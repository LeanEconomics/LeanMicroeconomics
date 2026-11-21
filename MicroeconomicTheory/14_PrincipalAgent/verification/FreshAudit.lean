import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import MWGClassicalDemand.UtilityMore
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import MWGAdverseSelection.ExercisesD1
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Necessity of the Kuhn-Tucker conditions for convex-like programs

MWG, footnote 7 (p. 484) and Section M.K: "the (Kuhn-Tucker) first-order conditions are both
necessary and sufficient" for a convex program. The programs of Chapter 14 are convex in the
manager's utility levels but are posed over compensation schemes, an infinite-dimensional set. The
multipliers nevertheless live in a finite-dimensional space (one per constraint), so the existence
of multipliers follows from separating two convex sets in `ℝ × ℝᵏ` (Mathlib's geometric
Hahn-Banach theorem), with no topology on the set of schemes.

* `kt_convexlike`: a minimization program over an arbitrary set `X` with finitely many inequality
  constraints `G i ≤ 0` that is *convex-like* (for any two points and `t ∈ [0, 1]` some point is at
  least as good as the `t`-mixture in the objective and every constraint) and satisfies Slater's
  condition: at every optimum there are multipliers `λ_i ≥ 0` with complementary slackness such that
  the optimum minimizes the Lagrangian over all of `X`.
* `kt_convexlike_eq`: the same with an additional equality constraint `H = 0` that is affine along
  the mixtures, under the qualification that `H` takes both signs at points satisfying the
  inequality constraints strictly; its multiplier has no sign restriction.
* `kt_sign`, `kt_le`: two elementary facts used for the signs of the multipliers.
-/

namespace MWG.PrincipalAgent

/-- If `c - s a < d` for every `s > 0`, then `a ≥ 0`. -/
theorem kt_sign {a c d : ℝ} (h : ∀ s : ℝ, 0 < s → c - s * a ≤ d) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  have hs : 0 < (|d - c| + 1) / -a := div_pos (by positivity) (by linarith)
  have h1 := h _ hs
  have h2 : (|d - c| + 1) / -a * a = -(|d - c| + 1) := by
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
  rw [h2] at h1
  linarith [le_abs_self (d - c)]

/-- If `c - s a ≤ d` for every `s > 0`, then `c ≤ d`. -/
theorem kt_le {a c d : ℝ} (h : ∀ s : ℝ, 0 < s → c - s * a ≤ d) : c ≤ d := by
  by_contra hcd
  push Not at hcd
  have hs : 0 < (c - d) / (2 * (|a| + 1)) := div_pos (by linarith) (by positivity)
  have h1 := h _ hs
  have h2 : (c - d) / (2 * (|a| + 1)) * a ≤ (c - d) / (2 * (|a| + 1)) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) hs.le
  have h3 : (c - d) / (2 * (|a| + 1)) * |a| < c - d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg a]
  linarith

/-- **Footnote 7 and Section M.K** (MWG, p. 484), abstract form. A program
`min J(x)` over `x ∈ X` subject to `G i x ≤ 0` (finitely many `i`). Suppose it is convex-like
(`hconv`), Slater's condition holds, and `xs` is optimal. Then there are multipliers `λ_i ≥ 0`
with complementary slackness `λ_i G_i(xs) = 0` such that `xs` minimizes the Lagrangian
`J + Σ λ_i G_i` over all of `X`. -/
theorem kt_convexlike {X ι : Type*} [Fintype ι] (J : X → ℝ) (G : ι → X → ℝ) (xs : X)
    (hfeas : ∀ i, G i xs ≤ 0) (hopt : ∀ x, (∀ i, G i x ≤ 0) → J xs ≤ J x)
    (hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x, J x ≤ (1 - t) * J x0 + t * J x1 ∧
      ∀ i, G i x ≤ (1 - t) * G i x0 + t * G i x1)
    (hslater : ∃ x, ∀ i, G i x < 0) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i xs = 0) ∧
      ∀ x, J xs ≤ J x + ∑ i, lam i * G i x := by
  classical
  let S : Set (ℝ × (ι → ℝ)) := {y | ∃ x, J x ≤ y.1 ∧ ∀ i, G i x ≤ y.2 i}
  let T : Set (ℝ × (ι → ℝ)) := {y | y.1 < J xs} ∩ ⋂ i, {y | y.2 i < 0}
  have hTo : IsOpen T := by
    refine (isOpen_lt continuous_fst continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const
  have hTc : Convex ℝ T := by
    intro y hy z hz a b ha hb hab
    simp only [T, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter] at hy hz ⊢
    refine ⟨?_, fun i => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hm := lt_min (sub_pos.2 hy.1) (sub_pos.2 hz.1)
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (J xs - y.1) (J xs - z.1)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (J xs - y.1) (J xs - z.1)) hb
      have h3 : a * min (J xs - y.1) (J xs - z.1) + b * min (J xs - y.1) (J xs - z.1) =
          min (J xs - y.1) (J xs - z.1) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.1 + b * z.1 = J xs - (a * (J xs - y.1) + b * (J xs - z.1)) := by
        linear_combination J xs * hab
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hm := lt_min (neg_pos.2 (hy.2 i)) (neg_pos.2 (hz.2 i))
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (-y.2 i) (-z.2 i)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (-y.2 i) (-z.2 i)) hb
      have h3 : a * min (-y.2 i) (-z.2 i) + b * min (-y.2 i) (-z.2 i) =
          min (-y.2 i) (-z.2 i) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.2 i + b * z.2 i = -(a * -y.2 i + b * -z.2 i) := by ring
      rw [h4]; linarith
  have hSc : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    obtain ⟨x0, h0J, h0G⟩ := hy
    obtain ⟨x1, h1J, h1G⟩ := hz
    obtain ⟨x, hxJ, hxG⟩ := hconv x0 x1 b hb (by linarith)
    have ha' : 1 - b = a := by linarith
    rw [ha'] at hxJ hxG
    refine ⟨x, ?_, fun i => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h0J ha, mul_le_mul_of_nonneg_left h1J hb]
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (h0G i) ha, mul_le_mul_of_nonneg_left (h1G i) hb,
        hxG i]
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    rintro y ⟨hy1, hy2⟩ ⟨x, hxJ, hxG⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iInter] at hy1 hy2
    have := hopt x fun i => ((hxG i).trans (hy2 i).le)
    linarith
  obtain ⟨f, u, hfT, hfS⟩ := geometric_hahn_banach_open hTc hTo hSc hdisj
  -- coordinates of `f`
  let e0 : ℝ × (ι → ℝ) := ((1 : ℝ), (0 : ι → ℝ))
  let ek : ι → ℝ × (ι → ℝ) := fun k => ((0 : ℝ), (Pi.single k (1 : ℝ) : ι → ℝ))
  have hdec : ∀ y : ℝ × (ι → ℝ), f y = y.1 * f e0 + ∑ i, y.2 i * f (ek i) := by
    intro y
    have : y = y.1 • e0 + ∑ i, y.2 i • ek i := by
      refine Prod.ext ?_ ?_
      · simp [e0, ek, Prod.fst_sum]
      · funext j
        simp [e0, ek, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, smul_eq_mul]
  set a0 := f e0
  let p : ℝ × (ι → ℝ) := (J xs, 0)
  have hpS : p ∈ S := ⟨xs, le_rfl, hfeas⟩
  have hfp : f p = J xs * a0 := by rw [hdec]; simp [p]
  have hup : u ≤ J xs * a0 := hfp ▸ hfS p hpS
  let base : ℝ × (ι → ℝ) := (J xs - 1, fun _ => -1)
  have hmemT : ∀ y : ℝ × (ι → ℝ), y.1 < J xs → (∀ i, y.2 i < 0) → y ∈ T := by
    intro y h1 h2
    simp only [T, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨h1, h2⟩
  have ha0 : 0 ≤ a0 := by
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • e0 ∈ T := hmemT _ (by simp [base, e0]; linarith)
      (fun i => by simp [base, e0])
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hak : ∀ k, 0 ≤ f (ek k) := by
    intro k
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • ek k ∈ T := hmemT _ (by simp [base, ek]) (fun i => by
      simp only [base, ek, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      by_cases hik : i = k
      · subst hik; simp; linarith
      · simp [hik])
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hu : J xs * a0 ≤ u := by
    refine kt_le (a := f (e0 + ∑ i, ek i)) fun s hs => ?_
    have hm : p - s • (e0 + ∑ i, ek i) ∈ T := hmemT _ (by simp [p, e0, ek, Prod.fst_sum]; linarith)
      (fun i => by simp [p, e0, ek, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]; linarith)
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul, hfp] at this
    exact this.le
  -- the Lagrangian inequality with `a0` on the objective
  have hlag : ∀ x, J xs * a0 ≤ J x * a0 + ∑ i, G i x * f (ek i) := by
    intro x
    have := hfS (J x, fun i => G i x) ⟨x, le_rfl, fun i => le_rfl⟩
    rw [hdec] at this
    exact hu.trans this
  -- complementary slackness
  have hcs : ∀ i, G i xs * f (ek i) = 0 := by
    have h1 := hlag xs
    have hnp : ∀ i ∈ Finset.univ, G i xs * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hfeas i) (hak i)
    have h2 : ∑ i, G i xs * f (ek i) = 0 :=
      le_antisymm (Finset.sum_nonpos hnp) (by linarith)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h2 i (Finset.mem_univ i)
  -- Slater gives `a0 > 0`
  have ha0pos : 0 < a0 := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨xt, hxt⟩ := hslater
    have h1 := hlag xt
    rw [← h] at h1
    simp only [mul_zero, zero_add] at h1
    have hnp : ∀ i ∈ Finset.univ, G i xt * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hxt i).le (hak i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1
      (le_antisymm (Finset.sum_nonpos hnp) h1)
    have hz : ∀ i, f (ek i) = 0 := fun i => by
      have := h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (hxt i).ne
      · exact h'
    have hf0 : ∀ y, f y = 0 := fun y => by rw [hdec, ← h]; simp [hz]
    have hbT : base ∈ T := hmemT _ (by simp [base]) (fun i => by simp [base])
    have := hfT _ hbT
    have := hfS p hpS
    rw [hf0] at *
    linarith
  refine ⟨fun i => f (ek i) / a0, fun i => div_nonneg (hak i) ha0, fun i => ?_, fun x => ?_⟩
  · rw [div_mul_eq_mul_div, mul_comm, hcs i, zero_div]
  · have h1 := hlag x
    have : ∑ i, f (ek i) / a0 * G i x = (∑ i, G i x * f (ek i)) / a0 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h2 : J xs * a0 ≤ (J x + (∑ i, G i x * f (ek i)) / a0) * a0 := by
      rw [add_mul, div_mul_cancel₀ _ ha0pos.ne']; linarith
    exact le_of_mul_le_mul_right h2 ha0pos

/-- **(14.AA.2)-(14.AA.3)** (MWG, p. 504), abstract form: a convex-like program with inequality
constraints `G i ≤ 0` and one equality constraint `H = 0` that is affine along the mixtures. If
there are points `xp`, `xm` satisfying every inequality constraint strictly with
`H(xp) > 0 > H(xm)`, then at every optimum `xs` there are multipliers `λ_i ≥ 0` (with
complementary slackness) and `ν` (of either sign) such that `xs` minimizes
`J + Σ λ_i G_i + ν H` over all of `X`. -/
theorem kt_convexlike_eq {X ι : Type*} [Fintype ι] (J : X → ℝ) (G : ι → X → ℝ) (H : X → ℝ)
    (xs : X) (hfeas : ∀ i, G i xs ≤ 0) (hHs : H xs = 0)
    (hopt : ∀ x, (∀ i, G i x ≤ 0) → H x = 0 → J xs ≤ J x)
    (hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x, J x ≤ (1 - t) * J x0 + t * J x1 ∧
      (∀ i, G i x ≤ (1 - t) * G i x0 + t * G i x1) ∧ H x = (1 - t) * H x0 + t * H x1)
    {xp xm : X} (hGp : ∀ i, G i xp < 0) (hGm : ∀ i, G i xm < 0) (hHp : 0 < H xp)
    (hHm : H xm < 0) :
    ∃ (lam : ι → ℝ) (ν : ℝ), (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i xs = 0) ∧
      ∀ x, J xs ≤ J x + ∑ i, lam i * G i x + ν * H x := by
  classical
  let S : Set (ℝ × (ι → ℝ) × ℝ) := {y | ∃ x, J x ≤ y.1 ∧ (∀ i, G i x ≤ y.2.1 i) ∧ H x = y.2.2}
  let T : Set (ℝ × (ι → ℝ) × ℝ) := {y | y.1 < J xs ∧ (∀ i, y.2.1 i < 0) ∧ y.2.2 = 0}
  -- mixing `xm` and `xp` to hit a prescribed value of `H`
  have hmix : ∀ z, H xm ≤ z → z ≤ H xp → ∃ x, J x ≤ max (J xm) (J xp) ∧
      (∀ i, G i x ≤ max (G i xm) (G i xp)) ∧ H x = z := by
    intro z hz1 hz2
    have hd : 0 < H xp - H xm := by linarith
    set t := (z - H xm) / (H xp - H xm)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
    obtain ⟨x, hJ, hG, hH⟩ := hconv xm xp t ht0 ht1
    refine ⟨x, ?_, fun i => ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left (le_max_left (J xm) (J xp)) (by linarith : 0 ≤ 1 - t)
      have := mul_le_mul_of_nonneg_left (le_max_right (J xm) (J xp)) ht0
      nlinarith
    · have := mul_le_mul_of_nonneg_left (le_max_left (G i xm) (G i xp))
        (by linarith : 0 ≤ 1 - t)
      have := mul_le_mul_of_nonneg_left (le_max_right (G i xm) (G i xp)) ht0
      nlinarith [hG i]
    · rw [hH]
      simp only [t]
      field_simp
      ring
  have hSc : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    obtain ⟨x0, h0J, h0G, h0H⟩ := hy
    obtain ⟨x1, h1J, h1G, h1H⟩ := hz
    obtain ⟨x, hxJ, hxG, hxH⟩ := hconv x0 x1 b hb (by linarith)
    have ha' : 1 - b = a := by linarith
    rw [ha'] at hxJ hxG hxH
    refine ⟨x, ?_, fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h0J ha, mul_le_mul_of_nonneg_left h1J hb]
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (h0G i) ha, mul_le_mul_of_nonneg_left (h1G i) hb,
        hxG i]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hxH, h0H, h1H]
  have hTc : Convex ℝ T := by
    intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3⟩ := hy
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨?_, fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hm := lt_min (sub_pos.2 hy1) (sub_pos.2 hz1)
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (J xs - y.1) (J xs - z.1)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (J xs - y.1) (J xs - z.1)) hb
      have h3 : a * min (J xs - y.1) (J xs - z.1) + b * min (J xs - y.1) (J xs - z.1) =
          min (J xs - y.1) (J xs - z.1) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.1 + b * z.1 = J xs - (a * (J xs - y.1) + b * (J xs - z.1)) := by
        linear_combination J xs * hab
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have hm := lt_min (neg_pos.2 (hy2 i)) (neg_pos.2 (hz2 i))
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (-y.2.1 i) (-z.2.1 i)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (-y.2.1 i) (-z.2.1 i)) hb
      have h3 : a * min (-y.2.1 i) (-z.2.1 i) + b * min (-y.2.1 i) (-z.2.1 i) =
          min (-y.2.1 i) (-z.2.1 i) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.2.1 i + b * z.2.1 i = -(a * -y.2.1 i + b * -z.2.1 i) := by ring
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hy3, hz3]; ring
  -- an open box inside `S`
  let B : Set (ℝ × (ι → ℝ) × ℝ) := {y | max (J xm) (J xp) < y.1} ∩
    (⋂ i, {y | max (G i xm) (G i xp) < y.2.1 i}) ∩ ({y | H xm < y.2.2} ∩ {y | y.2.2 < H xp})
  have hBo : IsOpen B := by
    refine ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_iInter_of_finite fun i => ?_)).inter
      ((isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
        (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const))
    exact isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have hBS : B ⊆ S := by
    rintro y ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iInter] at h1 h2 h3 h4
    obtain ⟨x, hJ, hG, hH⟩ := hmix y.2.2 h3.le h4.le
    exact ⟨x, hJ.trans h1.le, fun i => (hG i).trans (h2 i).le, hH⟩
  have hint : (interior S).Nonempty := by
    refine ⟨(max (J xm) (J xp) + 1, fun i => max (G i xm) (G i xp) + 1, 0),
      interior_maximal hBS hBo ?_⟩
    simp only [B, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨⟨by linarith, fun i => by linarith⟩, hHm, hHp⟩
  have hdisj : Disjoint (interior S) T := by
    rw [Set.disjoint_left]
    rintro y hyS ⟨hy1, hy2, hy3⟩
    obtain ⟨x, hxJ, hxG, hxH⟩ := interior_subset hyS
    have := hopt x (fun i => (hxG i).trans (hy2 i).le) (hxH.trans hy3)
    linarith
  have hTne : T.Nonempty := ⟨(J xs - 1, fun _ => -1, 0), by
    refine ⟨by simp, fun i => by simp, rfl⟩⟩
  obtain ⟨f0, u0, hf0ne, hfS0, hfT0⟩ :=
    geometric_hahn_banach_of_nonempty_interior hSc hTc hdisj hint hTne
  set f := -f0
  set u := -u0
  have hfS : ∀ y ∈ S, u ≤ f y := fun y hy => by
    have := hfS0 y hy
    change -u0 ≤ -(f0 y)
    linarith
  have hfT : ∀ y ∈ T, f y ≤ u := fun y hy => by
    have := hfT0 y hy
    change -(f0 y) ≤ -u0
    linarith
  let e0 : ℝ × (ι → ℝ) × ℝ := ((1 : ℝ), (0 : ι → ℝ), (0 : ℝ))
  let ek : ι → ℝ × (ι → ℝ) × ℝ := fun k => ((0 : ℝ), (Pi.single k (1 : ℝ) : ι → ℝ), (0 : ℝ))
  let eH : ℝ × (ι → ℝ) × ℝ := ((0 : ℝ), (0 : ι → ℝ), (1 : ℝ))
  have hdec : ∀ y : ℝ × (ι → ℝ) × ℝ,
      f y = y.1 * f e0 + ∑ i, y.2.1 i * f (ek i) + y.2.2 * f eH := by
    intro y
    have : y = y.1 • e0 + ∑ i, y.2.1 i • ek i + y.2.2 • eH := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [e0, ek, eH, Prod.fst_sum]
      · funext j
        simp [e0, ek, eH, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [e0, ek, eH, Prod.snd_sum]
    conv_lhs => rw [this]
    simp [map_sum, smul_eq_mul]
  set a0 := f e0
  set b := f eH
  let p : ℝ × (ι → ℝ) × ℝ := (J xs, 0, 0)
  have hpS : p ∈ S := ⟨xs, le_rfl, hfeas, hHs⟩
  have hfp : f p = J xs * a0 := by rw [hdec]; simp [p]
  have hup : u ≤ J xs * a0 := hfp ▸ hfS p hpS
  let base : ℝ × (ι → ℝ) × ℝ := (J xs - 1, fun _ => -1, 0)
  have ha0 : 0 ≤ a0 := by
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • e0 ∈ T := ⟨by simp [base, e0]; linarith, fun i => by simp [base, e0],
      by simp [base, e0]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hak : ∀ k, 0 ≤ f (ek k) := by
    intro k
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • ek k ∈ T := ⟨by simp [base, ek], fun i => by
      simp only [base, ek, Prod.snd_sub, Prod.fst_sub, Prod.smul_snd, Prod.smul_fst,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hik : i = k
      · subst hik; simp; linarith
      · simp [hik], by simp [base, ek]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hu : J xs * a0 ≤ u := by
    refine kt_le (a := f (e0 + ∑ i, ek i)) fun s hs => ?_
    have hm : p - s • (e0 + ∑ i, ek i) ∈ T := ⟨by simp [p, e0, ek, Prod.fst_sum]; linarith,
      fun i => by
        simp [p, e0, ek, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        linarith,
      by simp [p, e0, ek, Prod.snd_sum]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul, hfp] at this
    exact this
  have hlag : ∀ x, J xs * a0 ≤ J x * a0 + ∑ i, G i x * f (ek i) + H x * b := by
    intro x
    have := hfS (J x, fun i => G i x, H x) ⟨x, le_rfl, fun i => le_rfl, rfl⟩
    rw [hdec] at this
    exact hu.trans this
  have hcs : ∀ i, G i xs * f (ek i) = 0 := by
    have h1 := hlag xs
    rw [hHs, zero_mul, add_zero] at h1
    have hnp : ∀ i ∈ Finset.univ, G i xs * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hfeas i) (hak i)
    have h2 : ∑ i, G i xs * f (ek i) = 0 :=
      le_antisymm (Finset.sum_nonpos hnp) (by linarith)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h2 i (Finset.mem_univ i)
  have ha0pos : 0 < a0 := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    exfalso
    -- a point with `H = 0` satisfying the inequality constraints strictly
    obtain ⟨x0, -, hG0, hH0⟩ := hmix 0 hHm.le hHp.le
    have h1 := hlag x0
    rw [← h, hH0] at h1
    simp only [mul_zero, zero_add, zero_mul, add_zero] at h1
    have hG0' : ∀ i, G i x0 < 0 := fun i => (hG0 i).trans_lt (max_lt (hGm i) (hGp i))
    have hnp : ∀ i ∈ Finset.univ, G i x0 * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hG0' i).le (hak i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1
      (le_antisymm (Finset.sum_nonpos hnp) h1)
    have hz : ∀ i, f (ek i) = 0 := fun i => by
      have := h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (hG0' i).ne
      · exact h'
    have hb0 : b = 0 := by
      have hp := hlag xp
      have hm := hlag xm
      rw [← h] at hp hm
      simp only [mul_zero, hz, Finset.sum_const_zero, zero_add] at hp hm
      nlinarith
    have hf0 : f = 0 := by
      refine ContinuousLinearMap.ext fun y => ?_
      rw [hdec, ← h, hb0]
      simp [hz]
    exact hf0ne (neg_eq_zero.1 hf0)
  refine ⟨fun i => f (ek i) / a0, b / a0, fun i => div_nonneg (hak i) ha0, fun i => ?_,
    fun x => ?_⟩
  · rw [div_mul_eq_mul_div, mul_comm, hcs i, zero_div]
  · have h1 := hlag x
    have : ∑ i, f (ek i) / a0 * G i x = (∑ i, G i x * f (ek i)) / a0 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h2 : J xs * a0 ≤ (J x + (∑ i, G i x * f (ek i)) / a0 + b / a0 * H x) * a0 := by
      rw [add_mul, add_mul, div_mul_cancel₀ _ ha0pos.ne', div_mul_eq_mul_div,
        div_mul_cancel₀ _ ha0pos.ne']
      linarith
    exact le_of_mul_le_mul_right h2 ha0pos

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The hidden-action model and the observable-effort benchmark

MWG, Section 14.B, pp. 478-483.

Profits `π` are distributed with density `f(π | e)` with respect to a measure `ν` on `ℝ`
(MWG: Lebesgue measure on `[π̲, π̄]`; any measure is allowed here, so that the discrete version of
footnote 6 is the case of a sum of Dirac masses). The manager has utility `v(w) - g(e)` with
`v' > 0` and `v` concave (`v'' ≤ 0`); the owner is risk neutral. A compensation scheme is a
measurable `w : ℝ → ℝ` for which all expected wages and utilities exist (`Adm`); wages may be
negative (footnote 6).

* `ha_cost_lower_bound`: any scheme giving the manager `ū` at effort `e` costs at least the fixed
  wage `w*_e` of (14.B.4) (Jensen).
* `ha_fixed_wage_costMin`, `ha_costMin_binds`, `ha_costMin_unique`: problem (14.B.2) is solved by
  the fixed wage, its constraint binds, and under strict risk aversion the solution is unique
  (`ν`-a.e., footnote 6).
* `ha_foc_constant`, `ha_riskNeutral_costMin`: condition (14.B.3) and the risk-neutral case.
* `proposition_14_B_1`, `proposition_14_B_1_unique`: Proposition 14.B.1.
* `ha_value_le_obs`: the owner never does better when effort is unobservable (p. 482).
* `proposition_14_B_2`, `proposition_14_B_2_every`: Proposition 14.B.2 ("selling the project").
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- **Section 14.B** (MWG, pp. 479-480). The hidden-action principal-agent model with effort set
`ε`: a reference measure `ν` on profits, densities `f e`, the manager's utility of income `v`
with derivative `dv`, his disutility of effort `g`, and his reservation utility `ubar`. -/
structure HAModel (ε : Type*) where
  ν : Measure ℝ
  f : ε → ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  g : ε → ℝ
  ubar : ℝ

namespace HAModel

variable {ε : Type*}

/-- **Section 14.B** (MWG, pp. 479-480). The standing assumptions: each `f e` is a measurable
density, positive at every profit level, with a finite mean; `v` is differentiable with `v' > 0`
and concave (`v'' ≤ 0`). -/
structure Standing (M : HAModel ε) : Prop where
  f_meas : ∀ e, Measurable (M.f e)
  f_pos : ∀ e x, 0 < M.f e x
  f_int : ∀ e, Integrable (M.f e) M.ν
  f_one : ∀ e, ∫ x, M.f e x ∂M.ν = 1
  x_int : ∀ e, Integrable (fun x => x * M.f e x) M.ν
  v_deriv : ∀ w, HasDerivAt M.v (M.dv w) w
  dv_pos : ∀ w, 0 < M.dv w
  v_conc : ConcaveOn ℝ univ M.v

/-- An admissible compensation scheme: measurable, with finite expected wage and utility under
every effort. -/
def Adm (M : HAModel ε) (w : ℝ → ℝ) : Prop :=
  Measurable w ∧ ∀ e, Integrable (fun x => w x * M.f e x) M.ν ∧
    Integrable (fun x => M.v (w x) * M.f e x) M.ν

/-- The expected wage `∫ w(π) f(π | e) dπ`. -/
noncomputable def EW (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ := ∫ x, w x * M.f e x ∂M.ν

/-- The expected utility of income `∫ v(w(π)) f(π | e) dπ`. -/
noncomputable def EV (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ :=
  ∫ x, M.v (w x) * M.f e x ∂M.ν

/-- The manager's expected utility `∫ v(w(π)) f(π | e) dπ - g(e)`. -/
noncomputable def EU (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ := M.EV e w - M.g e

/-- Expected gross profit `∫ π f(π | e) dπ`. -/
noncomputable def GP (M : HAModel ε) (e : ε) : ℝ := ∫ x, x * M.f e x ∂M.ν

/-- The owner's payoff `∫ (π - w(π)) f(π | e) dπ`, the objective of (14.B.1). -/
noncomputable def OP (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ :=
  ∫ x, (x - w x) * M.f e x ∂M.ν

/-- The constraint of (14.B.1)-(14.B.2): an admissible scheme giving the manager at least `ū`
when he takes effort `e`. -/
def ObsFeasible (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := M.Adm w ∧ M.ubar ≤ M.EU e w

/-- **(14.B.1)** (MWG, p. 480). An optimal contract `(e, w(π))` when effort is observable. -/
def IsObsOptimal (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.ObsFeasible e w ∧ ∀ e' w', M.ObsFeasible e' w' → M.OP e' w' ≤ M.OP e w

/-- **(14.B.2)** (MWG, p. 480). `w` minimizes the expected wage of implementing `e` when effort
is observable. -/
def IsCostMin (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.ObsFeasible e w ∧ ∀ w', M.ObsFeasible e w' → M.EW e w ≤ M.EW e w'

/-- **(14.B.9)(ii)** (MWG, p. 483). The incentive constraint: `e` maximizes the manager's
expected utility under `w`. -/
def IC (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := ∀ e', M.EU e' w ≤ M.EU e w

/-- The constraints of (14.B.9) (MWG, p. 483). -/
def HAFeasible (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := M.ObsFeasible e w ∧ M.IC e w

/-- **(14.B.9)** (MWG, p. 483). `w` is an optimal incentive scheme for implementing `e`. -/
def IsHACostMin (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.HAFeasible e w ∧ ∀ w', M.HAFeasible e w' → M.EW e w ≤ M.EW e w'

/-- An optimal contract when effort is not observable: the owner picks the effort to implement
and an incentive-compatible scheme (MWG, pp. 482-483). -/
def IsHAOptimal (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.HAFeasible e w ∧ ∀ e' w', M.HAFeasible e' w' → M.OP e' w' ≤ M.OP e w

/-- The owner's payoff is expected gross profit less the expected wage (MWG, p. 480). -/
theorem ha_OP_eq {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) (e : ε) :
    M.OP e w = M.GP e - M.EW e w := by
  unfold OP GP EW
  rw [← integral_sub (hM.x_int e) (hw.2 e).1]
  congr 1; funext x; ring

/-- Constant schemes are admissible. -/
theorem ha_const_adm {M : HAModel ε} (hM : M.Standing) (c : ℝ) : M.Adm (fun _ => c) :=
  ⟨measurable_const, fun e => ⟨(hM.f_int e).const_mul c, (hM.f_int e).const_mul _⟩⟩

/-- A fixed wage `c` costs `c`. -/
theorem ha_EW_const {M : HAModel ε} (hM : M.Standing) (e : ε) (c : ℝ) :
    M.EW e (fun _ => c) = c := by
  unfold EW; rw [integral_const_mul, hM.f_one, mul_one]

/-- A fixed wage `c` gives expected utility of income `v(c)`. -/
theorem ha_EV_const {M : HAModel ε} (hM : M.Standing) (e : ε) (c : ℝ) :
    M.EV e (fun _ => c) = M.v c := by
  unfold EV; rw [integral_const_mul, hM.f_one, mul_one]

/-- The manager's utility of income is strictly increasing (`v' > 0`). -/
theorem ha_v_strictMono {M : HAModel ε} (hM : M.Standing) : StrictMono M.v :=
  strictMono_of_hasDerivAt_pos hM.v_deriv hM.dv_pos

/-- Jensen's inequality in the model: `∫ v(w) f(· | e) ≤ v(∫ w f(· | e))`. -/
theorem ha_EV_le {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) (e : ε) :
    M.EV e w ≤ M.v (M.EW e w) :=
  tpa_jensen hM.v_conc hM.v_deriv (fun x => (hM.f_pos e x).le) (hM.f_int e) (hM.f_one e)
    (hw.2 e).1 (hw.2 e).2

/-- **(14.B.4)** (MWG, p. 481). Any admissible scheme giving the manager at least `ū` at effort
`e` costs at least the fixed wage `w*_e` with `v(w*_e) - g(e) = ū`. -/
theorem ha_cost_lower_bound {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.ObsFeasible e w) {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) :
    wbar ≤ M.EW e w := by
  have h1 := ha_EV_le hM hw.1 e
  have h2 := hw.2
  unfold EU at h2
  exact (ha_v_strictMono hM).le_iff_le.1 (by linarith)

/-- The fixed wage `w*_e` of (14.B.4) satisfies the participation constraint with equality. -/
theorem ha_fixed_wage_feasible {M : HAModel ε} (hM : M.Standing) {e : ε} {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) :
    M.ObsFeasible e (fun _ => wbar) ∧ M.EU e (fun _ => wbar) = M.ubar := by
  have : M.EU e (fun _ => wbar) = M.ubar := by
    unfold EU; rw [ha_EV_const hM, hwbar]; ring
  exact ⟨⟨ha_const_adm hM wbar, this.ge⟩, this⟩

/-- **(14.B.2)-(14.B.4)** (MWG, pp. 480-481). The fixed wage `w*_e` solves (14.B.2). -/
theorem ha_fixed_wage_costMin {M : HAModel ε} (hM : M.Standing) {e : ε} {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) : M.IsCostMin e (fun _ => wbar) := by
  refine ⟨(ha_fixed_wage_feasible hM hwbar).1, fun w' hw' => ?_⟩
  rw [ha_EW_const hM]
  exact ha_cost_lower_bound hM hw' hwbar

/-- **(14.B.2)** (MWG, p. 480): "the constraint always binds at a solution", and every solution
costs exactly `w*_e`. -/
theorem ha_costMin_binds {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsCostMin e w) {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) :
    M.EW e w = wbar ∧ M.EU e w = M.ubar := by
  have hle := ha_cost_lower_bound hM hw.1 hwbar
  have hge := hw.2 _ (ha_fixed_wage_feasible hM hwbar).1
  rw [ha_EW_const hM] at hge
  have heq : M.EW e w = wbar := le_antisymm hge hle
  refine ⟨heq, ?_⟩
  have h1 := ha_EV_le hM hw.1.1 e
  have h2 := hw.1.2
  unfold EU at h2 ⊢
  rw [heq, hwbar] at h1
  linarith

/-- **Proposition 14.B.1, uniqueness part; footnote 6** (MWG, p. 481). If `v'' < 0` (here: `v`
strictly concave), every solution of (14.B.2) is the fixed wage `w*_e` at a set of profit levels
of full measure. -/
theorem ha_costMin_unique {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {e : ε} {w : ℝ → ℝ} (hw : M.IsCostMin e w) {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) : ∀ᵐ x ∂M.ν, w x = wbar := by
  obtain ⟨hEW, hEU⟩ := ha_costMin_binds hM hw hwbar
  have heq : M.EV e w = M.v (M.EW e w) := by
    unfold EU at hEU; rw [hEW, hwbar]; linarith
  have := tpa_jensen_eq hsc hM.v_deriv (hM.f_pos e) (hM.f_int e) (hM.f_one e) (hw.1.1.2 e).1
    (hw.1.1.2 e).2 heq
  filter_upwards [this] with x hx
  rw [hx]; exact hEW

/-- **(14.B.3)** (MWG, p. 481): with strict risk aversion (`v'` strictly decreasing) a scheme
satisfying `1 / v'(w(π)) = γ` at every profit level is a fixed wage. -/
theorem ha_foc_constant {M : HAModel ε} (hda : StrictAnti M.dv) {w : ℝ → ℝ} {γ : ℝ}
    (hfoc : ∀ x, 1 / M.dv (w x) = γ) (x y : ℝ) : w x = w y := by
  have h : M.dv (w x) = M.dv (w y) := by
    have := (hfoc x).trans (hfoc y).symm
    simpa using this
  exact hda.injective h

/-- **(14.B.3), risk-neutral case** (MWG, p. 481). If `v(w) = w`, condition (14.B.3) holds for
every scheme (with `γ = 1`), and a scheme solves (14.B.2) iff it gives an expected wage of
`ū + g(e)`. -/
theorem ha_riskNeutral_costMin {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    (hdv : ∀ w, M.dv w = 1) {e : ε} {w : ℝ → ℝ} (hw : M.Adm w) :
    (∀ x, 1 / M.dv (w x) = 1) ∧
      (M.IsCostMin e w ↔ M.EW e w = M.ubar + M.g e) := by
  have hEV : M.EV e w = M.EW e w := by unfold EV EW; simp only [hv]
  refine ⟨fun x => by simp [hdv], ⟨fun h => ?_, fun h => ⟨⟨hw, ?_⟩, fun w' hw' => ?_⟩⟩⟩
  · exact (ha_costMin_binds hM h (hv _)).1
  · unfold EU; rw [hEV, h]; ring_nf; exact le_refl _
  · rw [h]; have := ha_cost_lower_bound hM hw' (hv (M.ubar + M.g e)); exact this

/-- Since `g(e_H) > g(e_L)`, the fixed wage is higher when the contract calls for `e_H`
(MWG, p. 481). -/
theorem ha_wage_higher {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hg : M.g eL < M.g eH)
    {wL wH : ℝ} (hL : M.v wL = M.ubar + M.g eL) (hH : M.v wH = M.ubar + M.g eH) : wL < wH :=
  (ha_v_strictMono hM).lt_iff_lt.1 (by rw [hL, hH]; linarith)

/-- **Proposition 14.B.1** (MWG, p. 481). Let `w*(e)` solve `v(w*(e)) = ū + g(e)` for every `e`.
If `e*` maximizes `∫ π f(π | e) dπ - v⁻¹(ū + g(e))`, the contract specifying `e*` and the fixed
wage `w*(e*)` is optimal when effort is observable. -/
theorem proposition_14_B_1 {M : HAModel ε} (hM : M.Standing) {wstar : ε → ℝ}
    (hws : ∀ e, M.v (wstar e) = M.ubar + M.g e) {estar : ε}
    (hmax : ∀ e, M.GP e - wstar e ≤ M.GP estar - wstar estar) :
    M.IsObsOptimal estar (fun _ => wstar estar) := by
  refine ⟨(ha_fixed_wage_feasible hM (hws estar)).1, fun e' w' hw' => ?_⟩
  rw [ha_OP_eq hM hw'.1, ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM]
  have := ha_cost_lower_bound hM hw' (hws e')
  linarith [hmax e']

/-- **Proposition 14.B.1, "uniquely optimal"** (MWG, p. 481). If `v` is strictly concave, every
optimal contract `(e, w)` specifies an effort maximizing `∫ π f(π | e) dπ - v⁻¹(ū + g(e))` and pays
the fixed wage `w*(e)` at a set of profit levels of full measure (footnote 6). -/
theorem proposition_14_B_1_unique {M : HAModel ε} (hM : M.Standing)
    (hsc : StrictConcaveOn ℝ univ M.v) {wstar : ε → ℝ}
    (hws : ∀ e, M.v (wstar e) = M.ubar + M.g e) {e : ε} {w : ℝ → ℝ}
    (hopt : M.IsObsOptimal e w) :
    (∀ e', M.GP e' - wstar e' ≤ M.GP e - wstar e) ∧ ∀ᵐ x ∂M.ν, w x = wstar e := by
  have hcost : M.IsCostMin e w := by
    refine ⟨hopt.1, fun w' hw' => ?_⟩
    have := hopt.2 e w' hw'
    rw [ha_OP_eq hM hw'.1, ha_OP_eq hM hopt.1.1] at this
    linarith
  have hEW := (ha_costMin_binds hM hcost (hws e)).1
  refine ⟨fun e' => ?_, ha_costMin_unique hM hsc hcost (hws e)⟩
  have := hopt.2 e' _ (ha_fixed_wage_feasible hM (hws e')).1
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, ha_OP_eq hM hopt.1.1, hEW] at this
  exact this

/-- The owner can never do better when effort is unobservable than when it is observable
(MWG, p. 482, proof of Proposition 14.B.2; p. 484). -/
theorem ha_value_le_obs {M : HAModel ε} {e : ε} {w : ℝ → ℝ} (h : M.HAFeasible e w) :
    M.ObsFeasible e w := h.1

/-- **(14.B.6)-(14.B.8), Proposition 14.B.2** (MWG, pp. 482-483). With a risk-neutral manager
(`v(w) = w`), let `e*` solve (14.B.6) and `α* = ∫ π f(π | e*) dπ - g(e*) - ū`. The scheme
`w(π) = π - α*` ("selling the project") is incentive compatible for `e*`, gives the manager
exactly `ū`, gives the owner `α*` (the value of (14.B.6)), and is an optimal contract when
effort is unobservable. -/
theorem proposition_14_B_2 {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    {estar : ε} (hmax : ∀ e, M.GP e - M.g e - M.ubar ≤ M.GP estar - M.g estar - M.ubar) :
    let α := M.GP estar - M.g estar - M.ubar
    M.IsHAOptimal estar (fun x => x - α) ∧ M.EU estar (fun x => x - α) = M.ubar ∧
      M.OP estar (fun x => x - α) = α := by
  intro α
  have hadm : M.Adm (fun x => x - α) := by
    refine ⟨measurable_id.sub_const _, fun e => ?_⟩
    have h1 : Integrable (fun x => (x - α) * M.f e x) M.ν := by
      have : (fun x => (x - α) * M.f e x) = fun x => x * M.f e x - α * M.f e x := by
        funext x; ring
      rw [this]; exact (hM.x_int e).sub ((hM.f_int e).const_mul α)
    exact ⟨h1, by simpa only [hv] using h1⟩
  have hEW : ∀ e, M.EW e (fun x => x - α) = M.GP e - α := by
    intro e
    unfold EW GP
    have : (fun x => (x - α) * M.f e x) = fun x => x * M.f e x - α * M.f e x := by
      funext x; ring
    rw [this, integral_sub (hM.x_int e) ((hM.f_int e).const_mul α), integral_const_mul,
      hM.f_one, mul_one]
  have hEU : ∀ e, M.EU e (fun x => x - α) = M.GP e - α - M.g e := by
    intro e; unfold EU; rw [← hEW e]; unfold EV EW; simp only [hv]
  have hEUs : M.EU estar (fun x => x - α) = M.ubar := by rw [hEU]; ring
  have hOP : M.OP estar (fun x => x - α) = α := by
    rw [ha_OP_eq hM hadm, hEW]; ring
  refine ⟨⟨⟨⟨hadm, hEUs.ge⟩, fun e' => ?_⟩, fun e' w' hw' => ?_⟩, hEUs, hOP⟩
  · rw [hEU, hEU]; linarith [hmax e']
  · rw [hOP, ha_OP_eq hM hw'.1.1]
    have := ha_cost_lower_bound hM hw'.1 (hv (M.ubar + M.g e'))
    linarith [hmax e']

/-- **Proposition 14.B.2, "an optimal contract generates the same effort choice and expected
utilities"** (MWG, p. 482). With a risk-neutral manager, every optimal contract under
unobservable effort gives the owner the value of (14.B.6) and the manager exactly `ū`, and
implements an effort level solving (14.B.6). -/
theorem proposition_14_B_2_every {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    {estar : ε} (hmax : ∀ e, M.GP e - M.g e - M.ubar ≤ M.GP estar - M.g estar - M.ubar)
    {e : ε} {w : ℝ → ℝ} (hopt : M.IsHAOptimal e w) :
    M.OP e w = M.GP estar - M.g estar - M.ubar ∧ M.EU e w = M.ubar ∧
      ∀ e', M.GP e' - M.g e' - M.ubar ≤ M.GP e - M.g e - M.ubar := by
  obtain ⟨hsell, -, hOPs⟩ := proposition_14_B_2 hM hv hmax
  have h1 := hopt.2 _ _ hsell.1
  have h2 := hsell.2 e w hopt.1
  rw [hOPs] at h1 h2
  have hEU : M.EU e w = M.EW e w - M.g e := by unfold EU EV EW; simp only [hv]
  have hp := hopt.1.1.2
  rw [ha_OP_eq hM hopt.1.1.1] at h1 h2
  have hm := hmax e
  refine ⟨by rw [ha_OP_eq hM hopt.1.1.1]; linarith, by linarith, fun e' => ?_⟩
  linarith [hmax e']

end HAModel

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A risk-averse manager and two effort levels

MWG, Section 14.B, pp. 483-487.

* `ha_implement_low`: implementing the least costly effort (`e_L`) with the observable-effort
  fixed wage (pp. 483-484).
* `ha_kt_sufficient`: footnote 7, the Kuhn-Tucker condition (14.B.10) with complementary slackness
  is sufficient for (14.B.9) with `e = e_H` (the reformulated problem is convex in utilities).
* `lemma_14_B_1`: Lemma 14.B.1, both multipliers are positive.
* `ha_shift`, `footnote_8`: the utility-shift argument of footnote 8; the participation constraint
  binds in every solution of (14.B.9), for every effort level, and in every optimal contract.
* `ha_wage_vs_what`, `ha_monotone_iff_mlrp`: the likelihood-ratio form of the optimal scheme and
  the monotone likelihood ratio property (p. 485).
* `ha_EW_gt_of_IC`, `proposition_14_B_3`: Proposition 14.B.3; `ha_welfare_loss`,
  `ha_no_upward_distortion`, `footnote_9`.

Departures: the strict first-order stochastic dominance of p. 479 is used in the weaker form
"`F(π | e_H) ≤ F(π | e_L)` everywhere and strictly at some `π`" (`FOSD`). The necessity of the
Kuhn-Tucker conditions (footnote 7) is proved in `HANecessity` (`ha_kt_necessary`); here results
that MWG derives from (14.B.10) are proved for every scheme satisfying it, and those that do not
need multipliers (footnote 8, Proposition 14.B.3) are proved directly.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

/-- The distribution function `F(π | e) = ∫_{π' ≤ π} f(π' | e) dπ'` (MWG, p. 479). -/
noncomputable def F (M : HAModel ε) (e : ε) (x : ℝ) : ℝ := ∫ y in Iic x, M.f e y ∂M.ν

/-- **Strict first-order stochastic dominance** (MWG, p. 479; Section 6.D): `F(π | e_H) ≤
F(π | e_L)` at every `π`, with strict inequality somewhere. -/
def FOSD (M : HAModel ε) (eH eL : ε) : Prop :=
  (∀ x, M.F eH x ≤ M.F eL x) ∧ ∃ x, M.F eH x < M.F eL x

/-- With exactly two effort levels, the incentive constraint (14.B.9)(ii) for `e_H` is
constraint (ii_H) of p. 484. -/
theorem ha_IC_two {M : HAModel ε} {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (w : ℝ → ℝ) :
    M.IC eH w ↔ M.EU eL w ≤ M.EU eH w := by
  refine ⟨fun h => h eL, fun h e => ?_⟩
  rcases hE e with rfl | rfl
  · exact h
  · exact le_rfl

/-- **Implementing `e_L`** (MWG, pp. 483-484). If `e` has the lowest disutility, the fixed wage
`w*_e` of the observable case solves (14.B.9). -/
theorem ha_implement_low {M : HAModel ε} (hM : M.Standing) {e : ε} (hlow : ∀ e', M.g e ≤ M.g e')
    {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) : M.IsHACostMin e (fun _ => wbar) := by
  refine ⟨⟨(ha_fixed_wage_feasible hM hwbar).1, fun e' => ?_⟩, fun w' hw' => ?_⟩
  · unfold EU; rw [ha_EV_const hM, ha_EV_const hM]; linarith [hlow e']
  · exact (ha_fixed_wage_costMin hM hwbar).2 w' hw'.1

/-- The difference of expected utilities of income under two schemes. -/
theorem ha_EV_sub {M : HAModel ε} {w w' : ℝ → ℝ} (hw : M.Adm w) (hw' : M.Adm w') (e : ε) :
    ∫ x, (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) ∂M.ν = M.EV e w' - M.EV e w :=
  integral_sub (hw'.2 e).2 (hw.2 e).2

/-- **Footnote 7 and (14.B.10)** (MWG, p. 484). Sufficiency of the Kuhn-Tucker conditions: if `w`
satisfies the participation constraint (i) and the incentive constraint (ii_H), and there are
multipliers `γ, μ ≥ 0` with complementary slackness such that
`1 / v'(w(π)) = γ + μ [1 - f(π | e_L) / f(π | e_H)]` at almost every `π`, then `w` solves (14.B.9)
for `e = e_H`. -/
theorem ha_kt_sufficient {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) {w : ℝ → ℝ} (hw : M.Adm w) {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hi : M.ubar ≤ M.EU eH w) (hii : M.EU eL w ≤ M.EU eH w)
    (hcs1 : γ * (M.EU eH w - M.ubar) = 0) (hcs2 : μ * (M.EU eH w - M.EU eL w) = 0) :
    M.IsHACostMin eH w := by
  refine ⟨⟨⟨hw, hi⟩, (ha_IC_two hE w).2 hii⟩, fun w' hw' => ?_⟩
  have hii' := (ha_IC_two hE w').1 hw'.2
  have hi' := hw'.1.2
  -- the pointwise inequality
  have hpt : ∀ᵐ x ∂M.ν, (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
      μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x) ≤
      w' x * M.f eH x - w x * M.f eH x := by
    filter_upwards [hfoc] with x hx
    have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hH := hM.f_pos eH x
    have hL := hM.f_pos eL x
    have key : (M.v (w' x) - M.v (w x)) * (1 / M.dv (w x)) ≤ w' x - w x := by
      rw [mul_one_div, div_le_iff₀ hd]; linarith
    rw [hx] at key
    have key2 := mul_le_mul_of_nonneg_right key hH.le
    have hr : M.f eL x / M.f eH x * M.f eH x = M.f eL x := div_mul_cancel₀ _ hH.ne'
    have : (M.v (w' x) - M.v (w x)) * (γ + μ * (1 - M.f eL x / M.f eH x)) * M.f eH x =
        (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
          μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x) := by
      have : (M.v (w' x) - M.v (w x)) * (γ + μ * (1 - M.f eL x / M.f eH x)) * M.f eH x =
          (M.v (w' x) - M.v (w x)) * (γ * M.f eH x + μ * M.f eH x -
            μ * (M.f eL x / M.f eH x * M.f eH x)) := by ring
      rw [this, hr]; ring
    linarith
  have hiH : Integrable (fun x => (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x))
      M.ν := ((hw'.1.1.2 eH).2.sub (hw.2 eH).2).const_mul (γ + μ)
  have hiL : Integrable (fun x => μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) M.ν :=
    ((hw'.1.1.2 eL).2.sub (hw.2 eL).2).const_mul μ
  have hint : ∫ x, ((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
      μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν ≤
      ∫ x, (w' x * M.f eH x - w x * M.f eH x) ∂M.ν :=
    integral_mono_ae (hiH.sub hiL) ((hw'.1.1.2 eH).1.sub (hw.2 eH).1) hpt
  rw [integral_sub hiH hiL, integral_const_mul, integral_const_mul, ha_EV_sub hw hw'.1.1,
    ha_EV_sub hw hw'.1.1, integral_sub (hw'.1.1.2 eH).1 (hw.2 eH).1] at hint
  change _ ≤ M.EW eH w' - M.EW eH w at hint
  unfold EU at hi hii hi' hii' hcs1 hcs2
  have h1 : 0 ≤ γ * (M.EV eH w' - M.g eH - M.ubar) := mul_nonneg hγ (by linarith)
  have h2 : 0 ≤ μ * (M.EV eH w' - M.g eH - (M.EV eL w' - M.g eL)) := mul_nonneg hμ (by linarith)
  nlinarith

/-- Strict first-order stochastic dominance makes `f(π | e_L) > f(π | e_H)` on a set of positive
measure (MWG, proof of Lemma 14.B.1, p. 484). -/
theorem ha_fosd_set {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL) :
    M.ν {x | M.f eH x < M.f eL x} ≠ 0 := by
  intro h0
  obtain ⟨x0, hx0⟩ := hfosd.2
  have hae : ∀ᵐ x ∂M.ν, M.f eL x ≤ M.f eH x := by
    rw [ae_iff]; simpa [not_le] using h0
  have := setIntegral_mono_ae (s := Iic x0) (hM.f_int eL).integrableOn (hM.f_int eH).integrableOn
    hae
  unfold F at hx0
  linarith

/-- The reference measure is not zero (each `f e` integrates to one). -/
theorem ha_nu_ne_zero {M : HAModel ε} (hM : M.Standing) (e : ε) : M.ν ≠ 0 := by
  intro h
  have := hM.f_one e
  rw [h, integral_zero_measure] at this
  exact zero_ne_one this

/-- **Lemma 14.B.1** (MWG, p. 484). Suppose `F(π | e_H)` strictly first-order stochastically
dominates `F(π | e_L)`, `g(e_H) > g(e_L)`, the manager is strictly risk averse (`v'` strictly
decreasing), and `w` satisfies the incentive constraint (ii_H). If multipliers `γ, μ ≥ 0` satisfy
(14.B.10) at almost every profit level, then `γ > 0` and `μ > 0`. -/
theorem lemma_14_B_1 {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL)
    (hg : M.g eL < M.g eH) (hda : StrictAnti M.dv) {w : ℝ → ℝ}
    (hii : M.EU eL w ≤ M.EU eH w) {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) :
    0 < γ ∧ 0 < μ := by
  constructor
  · by_contra hγ0
    have hγ' : γ = 0 := le_antisymm (not_lt.1 hγ0) hγ
    obtain ⟨x, hxS, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ha_fosd_set hM hfosd)
      (ae_restrict_of_ae hfoc)
    have hH := hM.f_pos eH x
    have hr : 1 < M.f eL x / M.f eH x := by rw [one_lt_div hH]; exact hxS
    have hpos : 0 < 1 / M.dv (w x) := one_div_pos.2 (hM.dv_pos _)
    rw [hx, hγ'] at hpos
    nlinarith
  · by_contra hμ0
    have hμ' : μ = 0 := le_antisymm (not_lt.1 hμ0) hμ
    have hne : (ae M.ν).NeBot := ae_neBot.2 (ha_nu_ne_zero hM eL)
    obtain ⟨x0, hx0⟩ := hfoc.exists
    have hconst : ∀ᵐ x ∂M.ν, w x = w x0 := by
      filter_upwards [hfoc] with x hx
      rw [hμ'] at hx hx0
      simp only [zero_mul, add_zero] at hx hx0
      have : M.dv (w x) = M.dv (w x0) := by
        have := hx.trans hx0.symm; simpa using this
      exact hda.injective this
    have hEV : ∀ e, M.EV e w = M.v (w x0) := by
      intro e
      have : M.EV e w = M.EV e (fun _ => w x0) := by
        unfold EV
        refine integral_congr_ae ?_
        filter_upwards [hconst] with x hx
        rw [hx]
      rw [this, ha_EV_const hM]
    unfold EU at hii
    rw [hEV, hEV] at hii
    linarith

/-- Concavity makes `v'` antitone. -/
theorem ha_dv_anti {M : HAModel ε} (hM : M.Standing) {x a : ℝ} (hxa : x ≤ a) :
    M.dv a ≤ M.dv x := by
  rcases hxa.lt_or_eq with hxa | rfl
  · have h1 := tpa_tangent_le hM.v_conc (mem_univ x) (mem_univ a) (hM.v_deriv x).hasDerivWithinAt
    have h2 := tpa_tangent_le hM.v_conc (mem_univ a) (mem_univ x) (hM.v_deriv a).hasDerivWithinAt
    nlinarith
  · exact le_rfl

/-- `v` is unbounded below and continuous, so every utility level below `v(a)` is attained at a
wage below `a` (used in footnote 8). -/
theorem ha_v_hits {M : HAModel ε} (hM : M.Standing) {a t : ℝ} (ht : t < M.v a) :
    ∃ y, y < a ∧ M.v y = t := by
  have hd := hM.dv_pos a
  set y0 := a - (M.v a - t) / M.dv a - 1
  have hy0 : M.v y0 < t := by
    have := tpa_tangent_le hM.v_conc (mem_univ a) (mem_univ y0) (hM.v_deriv a).hasDerivWithinAt
    have : M.dv a * (y0 - a) = -(M.v a - t) - M.dv a := by
      simp only [y0]; field_simp; ring
    linarith
  have hya : y0 ≤ a := by
    have : 0 ≤ (M.v a - t) / M.dv a := div_nonneg (by linarith) hd.le
    simp only [y0]; linarith
  have hcont : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  obtain ⟨y, hy, hyt⟩ := intermediate_value_Ioo hya hcont.continuousOn ⟨hy0, ht⟩
  exact ⟨y, hy.2, hyt⟩

/-- **Footnote 8** (MWG, p. 485). The scheme `ŵ` with `v(ŵ(π)) = v(w(π)) - Δ`. -/
noncomputable def shift (M : HAModel ε) (Δ : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  Classical.epsilon fun y => M.v y = M.v (w x) - Δ

/-- The defining property of the shifted scheme, for `Δ > 0`. -/
theorem ha_shift_spec {M : HAModel ε} (hM : M.Standing) {Δ : ℝ} (hΔ : 0 < Δ) (w : ℝ → ℝ)
    (x : ℝ) : M.v (M.shift Δ w x) = M.v (w x) - Δ := by
  obtain ⟨y, -, hy⟩ := ha_v_hits hM (by linarith : M.v (w x) - Δ < M.v (w x))
  exact Classical.epsilon_spec (p := fun y => M.v y = M.v (w x) - Δ) ⟨y, hy⟩

/-- **Footnote 8** (MWG, p. 485). Lowering the manager's utility by `Δ > 0` at every profit level:
the resulting scheme is admissible, lowers every expected utility by exactly `Δ`, and lowers the
expected wage strictly under every effort. -/
theorem ha_shift {M : HAModel ε} (hM : M.Standing) {Δ : ℝ} (hΔ : 0 < Δ) {w : ℝ → ℝ}
    (hw : M.Adm w) :
    M.Adm (M.shift Δ w) ∧ (∀ e, M.EU e (M.shift Δ w) = M.EU e w - Δ) ∧
      ∀ e, M.EW e (M.shift Δ w) < M.EW e w := by
  set w' := M.shift Δ w
  have hspec : ∀ x, M.v (w' x) = M.v (w x) - Δ := ha_shift_spec hM hΔ w
  have hmono := ha_v_strictMono hM
  have hcont : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hlt : ∀ x, w' x < w x := fun x => hmono.lt_iff_lt.1 (by rw [hspec]; linarith)
  have hmeas : Measurable w' := by
    refine measurable_of_Iio fun a => ?_
    have : w' ⁻¹' Iio a = {x | M.v (w x) - Δ < M.v a} := by
      ext x
      simp only [mem_preimage, mem_Iio]
      rw [← hmono.lt_iff_lt, hspec]
      rfl
    rw [this]
    exact measurableSet_lt ((hcont.measurable.comp hw.1).sub_const _) measurable_const
  obtain ⟨b, -, hb⟩ := ha_v_hits hM (by linarith : M.v 0 - Δ < M.v 0)
  set C := |b| + Δ / M.dv 0
  have hd0 := hM.dv_pos 0
  have hbound : ∀ x, |w' x| ≤ |w x| + C := by
    intro x
    have hlow : min b (w x - Δ / M.dv 0) ≤ w' x := by
      rcases le_or_gt 0 (w x) with h0 | h0
      · refine min_le_of_left_le (hmono.le_iff_le.1 ?_)
        rw [hb, hspec]; linarith [hmono.monotone h0]
      · refine min_le_of_right_le ?_
        have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
          (hM.v_deriv (w x)).hasDerivWithinAt
        rw [hspec] at htan
        have hdx := ha_dv_anti hM h0.le
        have hdpos := hM.dv_pos (w x)
        have h1 : M.dv (w x) * (w x - w' x) ≤ Δ := by linarith
        have h2 : w x - w' x ≤ Δ / M.dv 0 := by
          rw [le_div_iff₀ hd0]
          have : 0 ≤ w x - w' x := (sub_pos.2 (hlt x)).le
          nlinarith
        linarith
    have hC : 0 ≤ Δ / M.dv 0 := div_nonneg hΔ.le hd0.le
    rw [abs_le]
    constructor
    · refine le_trans (le_min ?_ ?_) hlow
      · have := neg_abs_le b; have := abs_nonneg (w x); simp only [C]; linarith
      · have := neg_abs_le (w x); have := abs_nonneg b; simp only [C]; linarith
    · have := le_abs_self (w x); have := abs_nonneg b; simp only [C]; linarith [hlt x]
  have hEV : ∀ e, M.EV e w' = M.EV e w - Δ := by
    intro e
    unfold EV
    simp only [hspec, sub_mul]
    rw [integral_sub (hw.2 e).2 ((hM.f_int e).const_mul Δ), integral_const_mul, hM.f_one,
      mul_one]
  have hint : ∀ e, Integrable (fun x => w' x * M.f e x) M.ν := by
    intro e
    refine Integrable.mono' (((hw.2 e).1.norm).add ((hM.f_int e).const_mul C))
      (hmeas.mul (hM.f_meas e)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hf := hM.f_pos e x
    change |w' x * M.f e x| ≤ ‖w x * M.f e x‖ + C * M.f e x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hf]
    nlinarith [hbound x]
  have hadm : M.Adm w' := by
    refine ⟨hmeas, fun e => ⟨hint e, ?_⟩⟩
    have : (fun x => M.v (w' x) * M.f e x) = fun x => M.v (w x) * M.f e x - Δ * M.f e x := by
      funext x; rw [hspec]; ring
    rw [this]; exact (hw.2 e).2.sub ((hM.f_int e).const_mul Δ)
  refine ⟨hadm, fun e => by unfold EU; rw [hEV]; ring, fun e => ?_⟩
  have hpos : 0 < ∫ x, (w x * M.f e x - w' x * M.f e x) ∂M.ν := by
    have hnn : 0 ≤ fun x => w x * M.f e x - w' x * M.f e x := fun x => by
      have := mul_lt_mul_of_pos_right (hlt x) (hM.f_pos e x)
      simp only [Pi.zero_apply]; linarith
    rw [integral_pos_iff_support_of_nonneg hnn ((hw.2 e).1.sub (hint e))]
    have hsupp : Function.support (fun x => w x * M.f e x - w' x * M.f e x) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      have := mul_lt_mul_of_pos_right (hlt x) (hM.f_pos e x)
      linarith
    rw [hsupp, pos_iff_ne_zero]
    intro h
    exact ha_nu_ne_zero hM e (Measure.measure_univ_eq_zero.1 h)
  rw [integral_sub (hw.2 e).1 (hint e)] at hpos
  unfold EW; linarith

/-- **Footnote 8** (MWG, p. 485). In any solution of (14.B.9) (for any effort level) the
participation constraint (i) binds. -/
theorem footnote_8 {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHACostMin e w) : M.EU e w = M.ubar := by
  by_contra hne
  have hΔ : 0 < M.EU e w - M.ubar := sub_pos.2 (lt_of_le_of_ne hw.1.1.2 (Ne.symm hne))
  obtain ⟨hadm, hEU, hEW⟩ := ha_shift hM hΔ hw.1.1.1
  have hfeas : M.HAFeasible e (M.shift (M.EU e w - M.ubar) w) := by
    refine ⟨⟨hadm, by rw [hEU]; linarith⟩, fun e' => ?_⟩
    rw [hEU, hEU]; linarith [hw.1.2 e']
  linarith [hw.2 _ hfeas, hEW e]

/-- In every optimal contract under unobservable effort the participation constraint binds
(footnote 8, applied to the owner's whole problem). -/
theorem ha_optimal_binds {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHAOptimal e w) : M.EU e w = M.ubar := by
  by_contra hne
  have hΔ : 0 < M.EU e w - M.ubar := sub_pos.2 (lt_of_le_of_ne hw.1.1.2 (Ne.symm hne))
  obtain ⟨hadm, hEU, hEW⟩ := ha_shift hM hΔ hw.1.1.1
  have hfeas : M.HAFeasible e (M.shift (M.EU e w - M.ubar) w) := by
    refine ⟨⟨hadm, by rw [hEU]; linarith⟩, fun e' => ?_⟩
    rw [hEU, hEU]; linarith [hw.1.2 e']
  have := hw.2 _ _ hfeas
  rw [ha_OP_eq hM hadm, ha_OP_eq hM hw.1.1.1] at this
  linarith [hEW e]

/-- **Footnote 9** (MWG, p. 487). The optimal contract under unobservable effort is a constrained
Pareto optimum: no contract satisfying the same incentive constraints makes the owner and the
manager both weakly better off and one of them strictly better off: any such contract gives
both parties exactly what they get under `w`. -/
theorem footnote_9 {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHAOptimal e w) {e' : ε} {w' : ℝ → ℝ} (hw' : M.HAFeasible e' w')
    (hO : M.OP e w ≤ M.OP e' w') :
    M.OP e' w' = M.OP e w ∧ M.EU e' w' = M.EU e w := by
  have h1 := hw.2 e' w' hw'
  have hOeq : M.OP e' w' = M.OP e w := le_antisymm h1 hO
  have hopt' : M.IsHAOptimal e' w' := ⟨hw', fun e'' w'' h => hOeq ▸ hw.2 e'' w'' h⟩
  exact ⟨hOeq, by rw [ha_optimal_binds hM hopt', ha_optimal_binds hM hw]⟩

/-- **The likelihood-ratio form of (14.B.10)** (MWG, p. 485). Let `ŵ` be the fixed wage with
`1 / v'(ŵ) = γ`. If `w` satisfies (14.B.10) at `π` with `μ > 0` and `v'` is strictly decreasing,
then `w(π) > ŵ` if `f(π | e_L) / f(π | e_H) < 1`, and `w(π) < ŵ` if the ratio exceeds `1`. -/
theorem ha_wage_vs_what {M : HAModel ε} (hda : StrictAnti M.dv) (hdv : ∀ w, 0 < M.dv w)
    {eL eH : ε} {w : ℝ → ℝ} {γ μ x what : ℝ} (hμ : 0 < μ)
    (hfoc : 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hwhat : 1 / M.dv what = γ) :
    (M.f eL x / M.f eH x < 1 → what < w x) ∧ (1 < M.f eL x / M.f eH x → w x < what) := by
  have key : ∀ a b, 1 / M.dv a < 1 / M.dv b → a < b := fun a b h => by
    have := (one_div_lt_one_div (hdv a) (hdv b)).1 h
    exact hda.lt_iff_gt.1 this
  constructor
  · intro hr
    exact key _ _ (by rw [hfoc, hwhat]; nlinarith)
  · intro hr
    exact key _ _ (by rw [hfoc, hwhat]; nlinarith)

/-- **The monotone likelihood ratio property** (MWG, p. 485). If `w` satisfies (14.B.10) at every
profit level with `μ > 0` and `v'` is strictly decreasing, then `w` is nondecreasing in `π` if and
only if the likelihood ratio `f(π | e_L) / f(π | e_H)` is nonincreasing in `π`. -/
theorem ha_monotone_iff_mlrp {M : HAModel ε} (hda : StrictAnti M.dv) (hdv : ∀ w, 0 < M.dv w)
    {eL eH : ε} {w : ℝ → ℝ} {γ μ : ℝ} (hμ : 0 < μ)
    (hfoc : ∀ x, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) :
    Monotone w ↔ Antitone fun x => M.f eL x / M.f eH x := by
  have key : ∀ x y, w x ≤ w y ↔ M.f eL y / M.f eH y ≤ M.f eL x / M.f eH x := by
    intro x y
    rw [← hda.le_iff_ge, ← one_div_le_one_div (hdv _) (hdv _), hfoc, hfoc]
    constructor <;> intro h <;> nlinarith
  exact ⟨fun h x y hxy => (key x y).1 (h hxy), fun h x y hxy => (key x y).2 (h hxy)⟩

/-- **p. 486; Proposition 14.B.3, "a larger expected wage payment"**. With a strictly concave `v`
and `g(e_H) > g(e_L)`, every scheme satisfying (i) and (ii_H) for `e_H` has expected wage strictly
above the observable-effort wage `w*_{e_H}` (Jensen's inequality). -/
theorem ha_EW_gt_of_IC {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hg : M.g eL < M.g eH) {w : ℝ → ℝ} (hw : M.ObsFeasible eH w)
    (hii : M.EU eL w ≤ M.EU eH w) {wH : ℝ} (hwH : M.v wH = M.ubar + M.g eH) :
    wH < M.EW eH w := by
  rcases (ha_cost_lower_bound hM hw hwH).lt_or_eq with h | h
  · exact h
  exfalso
  have h1 := ha_EV_le hM hw.1 eH
  have h2 := hw.2
  unfold EU at h2
  have heq : M.EV eH w = M.v (M.EW eH w) := by rw [← h, hwH] at h1 ⊢; linarith
  have hae := tpa_jensen_eq hsc hM.v_deriv (hM.f_pos eH) (hM.f_int eH) (hM.f_one eH)
    (hw.1.2 eH).1 (hw.1.2 eH).2 heq
  have hae' : ∀ᵐ x ∂M.ν, w x = M.EW eH w := hae
  have hEV : ∀ e, M.EV e w = M.v (M.EW eH w) := by
    intro e
    have : M.EV e w = M.EV e (fun _ => M.EW eH w) := by
      unfold EV
      refine integral_congr_ae ?_
      filter_upwards [hae'] with x hx
      rw [hx]
    rw [this, ha_EV_const hM]
  unfold EU at hii
  rw [hEV, hEV] at hii
  linarith

/-- **Proposition 14.B.3** (MWG, p. 487). Two effort levels, `g(e_L) < g(e_H)`, a strictly risk
averse manager (`v` strictly concave). (a) A scheme satisfying (14.B.10) with complementary
slackness implements `e_H` optimally; (b) every optimal scheme for `e_H` gives the manager exactly
`ū` and (c) has an expected wage strictly above the observable-effort wage `w*_{e_H}`; (d) the
optimal scheme for `e_L` is the observable-effort fixed wage. -/
theorem proposition_14_B_3 {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH) :
    (∀ w : ℝ → ℝ, M.Adm w → ∀ γ μ : ℝ, 0 ≤ γ → 0 ≤ μ →
      (∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) →
      M.ubar ≤ M.EU eH w → M.EU eL w ≤ M.EU eH w → γ * (M.EU eH w - M.ubar) = 0 →
      μ * (M.EU eH w - M.EU eL w) = 0 → M.IsHACostMin eH w) ∧
    (∀ w, M.IsHACostMin eH w → M.EU eH w = M.ubar ∧ wH < M.EW eH w) ∧
    M.IsHACostMin eL (fun _ => wL) := by
  refine ⟨fun w hw γ μ hγ hμ hfoc hi hii h1 h2 => ha_kt_sufficient hM hE hw hγ hμ hfoc hi hii h1 h2,
    fun w hw => ⟨footnote_8 hM hw, ha_EW_gt_of_IC hM hsc hg hw.1.1 (hw.1.2 eL) hwH⟩,
    ha_implement_low hM (fun e => ?_) hwL⟩
  rcases hE e with rfl | rfl
  · exact le_rfl
  · exact hg.le

/-- **Proposition 14.B.3, welfare loss** (MWG, p. 487). If with observable effort `e_H` is
strictly better than `e_L` (`∫ π f(π|e_H) - w*_{e_H} > ∫ π f(π|e_L) - w*_{e_L}`), then every
contract feasible under unobservable effort gives the owner strictly less than his
observable-effort payoff. (With a tie the claim fails: see `ha_no_loss_of_tie`.) -/
theorem ha_welfare_loss {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH)
    (hstrict : M.GP eL - wL < M.GP eH - wH) {e : ε} {w : ℝ → ℝ} (hw : M.HAFeasible e w) :
    M.OP e w < M.GP eH - wH := by
  rw [ha_OP_eq hM hw.1.1]
  rcases hE e with rfl | rfl
  · have := ha_cost_lower_bound hM hw.1 hwL; linarith
  · have := ha_EW_gt_of_IC hM hsc hg hw.1 (hw.2 eL) hwH; linarith

/-- With a tie between `e_L` and `e_H` under observability there is no welfare loss: the
observable-effort fixed wage for `e_L` is feasible under unobservable effort and attains the
observable-effort payoff (refining the wording of Proposition 14.B.3, see corrections). -/
theorem ha_no_loss_of_tie {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (htie : M.GP eL - wL = M.GP eH - wH) :
    M.HAFeasible eL (fun _ => wL) ∧ M.OP eL (fun _ => wL) = M.GP eH - wH := by
  have hlow : ∀ e', M.g eL ≤ M.g e' := fun e' => by
    rcases hE e' with rfl | rfl
    · exact le_rfl
    · exact hg.le
  refine ⟨(ha_implement_low hM hlow hwL).1, ?_⟩
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, htie]

/-- **Downward distortion only** (MWG, p. 487). If `e_L` is strictly optimal under observable
effort, every optimal contract under unobservable effort implements `e_L`. -/
theorem ha_no_upward_distortion {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH)
    (hstrict : M.GP eH - wH < M.GP eL - wL) {e : ε} {w : ℝ → ℝ} (hw : M.IsHAOptimal e w) :
    e = eL := by
  rcases hE e with rfl | rfl
  · rfl
  exfalso
  have hlow : ∀ e', M.g eL ≤ M.g e' := fun e' => by
    rcases hE e' with rfl | rfl
    · exact le_rfl
    · exact hg.le
  have h1 := hw.2 _ _ (ha_implement_low hM hlow hwL).1
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, ha_OP_eq hM hw.1.1.1] at h1
  have := ha_cost_lower_bound hM hw.1.1 hwH
  linarith

end HAModel

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finitely many profit levels

MWG, footnote 6 (p. 481): the discrete version of the hidden-action model, with finitely many
profit levels `π₁, …, π_N`. The reference measure is the counting measure on these levels,
`∑ᵢ δ_{πᵢ}`; integrals against it are finite sums. Used for the concrete instances of
Section 14.B and for Exercise 14.B.4.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- The counting measure on the profit levels `a 0, …, a (n - 1)` (MWG, footnote 6). -/
noncomputable def dmeas {n : ℕ} (a : Fin n → ℝ) : Measure ℝ := ∑ i, Measure.dirac (a i)

/-- Every function is integrable against the counting measure on finitely many points. -/
theorem dmeas_integrable {n : ℕ} (a : Fin n → ℝ) (F : ℝ → ℝ) : Integrable F (dmeas a) :=
  integrable_finsetSum_measure.2 fun i _ => integrable_dirac (by simp)

/-- Integrals against the counting measure are finite sums. -/
theorem dmeas_integral {n : ℕ} (a : Fin n → ℝ) (F : ℝ → ℝ) :
    ∫ x, F x ∂dmeas a = ∑ i, F (a i) := by
  unfold dmeas
  rw [integral_finsetSum_measure fun i _ => integrable_dirac (by simp)]
  simp [integral_dirac]

/-- Integrals over a measurable set are sums over the points in the set. -/
theorem dmeas_setIntegral {n : ℕ} (a : Fin n → ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (F : ℝ → ℝ) : ∫ x in s, F x ∂dmeas a = ∑ i, s.indicator F (a i) := by
  rw [← integral_indicator hs, dmeas_integral]

/-- A property holding at every point holds almost everywhere for the counting measure. -/
theorem dmeas_ae {n : ℕ} (a : Fin n → ℝ) {P : ℝ → Prop} (h : ∀ i, P (a i)) :
    ∀ᵐ x ∂dmeas a, P x := by
  rw [ae_iff]
  unfold dmeas
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply, indicator_of_notMem (by simpa using h i)]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concrete hidden-action models

MWG, Section 14.B, pp. 479-487: proved instances of the hypotheses of the results of
`HiddenAction` and `RiskAverse`, and the example behind Figure 14.B.1.

Three profit levels `0, 1, 2` (footnote 6), effort `true = e_H`, `false = e_L`, densities
`f(·|e_L) = (1/2, 1/4, 1/4)` and `f(·|e_H) = (1/4, 1/2, 1/4)`, and `v(w) = -exp(-w)`.

* `exA_standing`, `exA_fosd`: the standing assumptions and strict first-order stochastic
  dominance hold.
* `exA_not_mlrp`, `exA_optimal`, `exA_not_monotone`: **Figure 14.B.1** (p. 486): first-order
  stochastic dominance without the monotone likelihood ratio property, and the optimal incentive
  scheme for `e_H` (from footnote 7 with `γ = 2`, `μ = 1`) is not monotone in profits.
* `exA_lemma_14_B_1`, `exA_proposition_14_B_1`, `exA_welfare_loss`: instances of Lemma 14.B.1,
  Proposition 14.B.1 and the welfare loss of Proposition 14.B.3.
* `exA_tie`: with a tie under observability, `e_H` is an optimal observable effort and yet
  unobservability causes no loss (correction to the wording of Proposition 14.B.3).
* `exA_proposition_14_B_2`: an instance of Proposition 14.B.2 (risk-neutral manager).
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- The profit levels `0, 1, 2`. -/
def exPts : Fin 3 → ℝ := ![0, 1, 2]

/-- The densities: `f(·|e_L)` interpolates `(1/2, 1/4, 1/4)` and `f(·|e_H)` interpolates
`(1/4, 1/2, 1/4)` at the profit levels `0, 1, 2`, positively on all of `ℝ`. -/
noncomputable def exF (b : Bool) (x : ℝ) : ℝ :=
  if b then (1 + x ^ 2 * (2 - x) ^ 2) / 4 else (x ^ 2 - 3 * x + 4) / 8

/-- The family of example models: utility `v` with derivative `dv`, `g(e_L) = 0`, `g(e_H) = gH`
and reservation utility `u`. -/
noncomputable def exModel (v dv : ℝ → ℝ) (gH u : ℝ) : HAModel Bool where
  ν := dmeas exPts
  f := exF
  v := v
  dv := dv
  g := fun b => if b then gH else 0
  ubar := u

/-- Integrals in the example models are sums over the three profit levels. -/
theorem exA_integral (F : ℝ → ℝ) : ∫ x, F x ∂dmeas exPts = F 0 + F 1 + F 2 := by
  rw [dmeas_integral, Fin.sum_univ_three]; simp [exPts]

/-- The example models satisfy the standing assumptions whenever `v` does. -/
theorem exA_standing_of {v dv : ℝ → ℝ} (hv : ∀ w, HasDerivAt v (dv w) w) (hdv : ∀ w, 0 < dv w)
    (hc : ConcaveOn ℝ univ v) (gH u : ℝ) : (exModel v dv gH u).Standing where
  f_meas b := by
    cases b
    · change Measurable fun x => (x ^ 2 - 3 * x + 4) / 8
      fun_prop
    · change Measurable fun x : ℝ => (1 + x ^ 2 * (2 - x) ^ 2) / 4
      fun_prop
  f_pos b x := by
    cases b
    · change 0 < (x ^ 2 - 3 * x + 4) / 8
      nlinarith [sq_nonneg (x - 3 / 2)]
    · change 0 < (1 + x ^ 2 * (2 - x) ^ 2) / 4
      positivity
  f_int _ := dmeas_integrable _ _
  f_one b := by
    change ∫ x, exF b x ∂dmeas exPts = 1
    rw [exA_integral]; cases b <;> simp [exF] <;> norm_num
  x_int _ := dmeas_integrable _ _
  v_deriv := hv
  dv_pos := hdv
  v_conc := hc

/-- `v(w) = -exp(-w)` has derivative `exp(-w)`. -/
theorem exA_hasDeriv (w : ℝ) : HasDerivAt (fun w => -Real.exp (-w)) (Real.exp (-w)) w := by
  have := (hasDerivAt_neg w).exp.neg
  convert this using 1
  ring

/-- `v(w) = -exp(-w)` is strictly concave. -/
theorem exA_strictConcave : StrictConcaveOn ℝ univ fun w => -Real.exp (-w) := by
  have hd : deriv (fun w => -Real.exp (-w)) = fun w => Real.exp (-w) :=
    funext fun w => (exA_hasDeriv w).deriv
  refine StrictAnti.strictConcaveOn_univ_of_deriv (by fun_prop) ?_
  rw [hd]
  exact fun a b hab => Real.exp_lt_exp.2 (neg_lt_neg hab)

/-- The main example: `v(w) = -exp(-w)`, `g(e_H) = 3/20`, `ū = -29/40`. -/
noncomputable def exA : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (3 / 20) (-29 / 40)

/-- The standing assumptions hold in `exA`. -/
theorem exA_standing : exA.Standing :=
  exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _

/-- In `exA` the manager is strictly risk averse: `v'(w) = exp(-w)` is strictly decreasing. -/
theorem exA_dv_anti : StrictAnti exA.dv := fun _ _ hab => Real.exp_lt_exp.2 (neg_lt_neg hab)

/-- The two effort levels. -/
theorem exA_two (b : Bool) : b = false ∨ b = true := by cases b <;> simp

/-- Strict first-order stochastic dominance holds in the example models. -/
theorem exA_fosd (v dv : ℝ → ℝ) (gH u : ℝ) : (exModel v dv gH u).FOSD true false := by
  have hF : ∀ b x, (exModel v dv gH u).F b x = ∑ i, (Iic x).indicator (exF b) (exPts i) :=
    fun b x => dmeas_setIntegral _ measurableSet_Iic _
  refine ⟨fun x => ?_, 0, ?_⟩
  · rw [hF, hF]
    simp only [Fin.sum_univ_three, indicator, mem_Iic]
    simp only [exPts, exF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    split_ifs <;> norm_num <;> linarith
  · rw [hF, hF]
    simp only [Fin.sum_univ_three, indicator, mem_Iic]
    simp only [exPts, exF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num

/-- **Figure 14.B.1(a)-(b)** (MWG, pp. 485-486). First-order stochastic dominance does not imply
the monotone likelihood ratio property: `f(π|e_L) / f(π|e_H)` is `2, 1/2, 1` at `π = 0, 1, 2`. -/
theorem exA_not_mlrp : ¬ Antitone fun x => exA.f false x / exA.f true x := by
  intro h
  have := h (show (1 : ℝ) ≤ 2 by norm_num)
  change exF false 2 / exF true 2 ≤ exF false 1 / exF true 1 at this
  simp only [exF] at this
  norm_num at this

/-- The optimal incentive scheme for `e_H` in `exA`: `w = 0, log (5/2), log 2` at `π = 0, 1, 2`. -/
noncomputable def exW (x : ℝ) : ℝ :=
  if x < 1 / 2 then 0 else if x < 3 / 2 then Real.log (5 / 2) else Real.log 2

/-- `exW` is admissible. -/
theorem exW_adm : exA.Adm exW := by
  refine ⟨?_, fun _ => ⟨dmeas_integrable _ _, dmeas_integrable _ _⟩⟩
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      measurable_const)

theorem exW_zero : exW 0 = 0 := by norm_num [exW]

theorem exW_one : exW 1 = Real.log (5 / 2) := by norm_num [exW]

theorem exW_two : exW 2 = Real.log 2 := by norm_num [exW]

/-- The manager's expected utilities under `exW`: both equal `ū = -29/40`. -/
theorem exA_EU : exA.EU true exW = -29 / 40 ∧ exA.EU false exW = -29 / 40 := by
  have h1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hc : ∀ b : Bool, exA.EU b exW = ∫ x, -Real.exp (-exW x) * exF b x ∂dmeas exPts -
      (if b then 3 / 20 else 0) := fun _ => rfl
  rw [hc, hc, exA_integral, exA_integral, exW_zero, exW_one, exW_two, h1, h2]
  simp only [exF]
  norm_num

/-- (14.B.10) holds for `exW` with `γ = 2`, `μ = 1` at every profit level of `exA`. -/
theorem exA_foc : ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = 2 + 1 * (1 - exA.f false x / exA.f true x) := by
  refine dmeas_ae _ fun i => ?_
  change 1 / Real.exp (-exW (exPts i)) = 2 + 1 * (1 - exF false (exPts i) / exF true (exPts i))
  fin_cases i <;> simp only [exPts, exF] <;> norm_num [exW_zero, exW_one, exW_two, Real.exp_neg,
    Real.exp_log]

/-- **Figure 14.B.1(c)** (MWG, p. 486) and footnote 7. `exW` is the optimal incentive scheme for
implementing `e_H` in `exA`. -/
theorem exA_optimal : exA.IsHACostMin true exW := by
  obtain ⟨h1, h2⟩ := exA_EU
  refine HAModel.ha_kt_sufficient exA_standing exA_two exW_adm (by norm_num) (by norm_num)
    exA_foc ?_ ?_ ?_ ?_
  · rw [h1]; exact le_refl _
  · rw [h1, h2]
  · rw [h1]; change (2 : ℝ) * (-29 / 40 - -29 / 40) = 0; ring
  · rw [h1, h2]; ring

/-- **Figure 14.B.1(c)** (MWG, pp. 485-486). The optimal incentive scheme is not monotone in
profits: it pays more at `π = 1` than at `π = 2`. -/
theorem exA_not_monotone : ¬ Monotone exW := by
  intro h
  have := h (show (1 : ℝ) ≤ 2 by norm_num)
  rw [exW_one, exW_two] at this
  have := Real.log_lt_log (by norm_num) (show (2 : ℝ) < 5 / 2 by norm_num)
  linarith

/-- An instance of all the hypotheses of **Lemma 14.B.1** (MWG, p. 484). -/
theorem exA_lemma_14_B_1 : (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 := by
  obtain ⟨h1, h2⟩ := exA_EU
  exact HAModel.lemma_14_B_1 exA_standing (exA_fosd _ _ _ _) (by norm_num [exA, exModel])
    exA_dv_anti (by rw [h1, h2]) (by norm_num) (by norm_num) exA_foc

/-- The fixed wages of (14.B.4) in `exA`: `w*_{e_L} = -log (29/40)`, `w*_{e_H} = -log (23/40)`. -/
noncomputable def exWstar (b : Bool) : ℝ := if b then -Real.log (23 / 40) else -Real.log (29 / 40)

theorem exA_wstar (b : Bool) : exA.v (exWstar b) = exA.ubar + exA.g b := by
  change -Real.exp (-exWstar b) = -29 / 40 + (if b then 3 / 20 else 0)
  cases b <;> simp only [exWstar] <;> norm_num [Real.exp_log]

/-- Expected gross profits in the example models: `3/4` under `e_L` and `1` under `e_H`. -/
theorem exA_GP (v dv : ℝ → ℝ) (gH u : ℝ) (b : Bool) :
    (exModel v dv gH u).GP b = if b then 1 else 3 / 4 := by
  change ∫ x, x * exF b x ∂dmeas exPts = _
  rw [exA_integral]; cases b <;> simp [exF] <;> norm_num

/-- With observable effort, `e_H` is strictly better than `e_L` in `exA`:
`1 + log (23/40) > 3/4 + log (29/40)`. -/
theorem exA_fb_strict : exA.GP false - exWstar false < exA.GP true - exWstar true := by
  rw [exA, exA_GP, exA_GP]
  simp only [exWstar, Bool.false_eq_true, ↓reduceIte]
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hlog : Real.log (29 / 23) < 1 / 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith
  have : Real.log (29 / 40) - Real.log (23 / 40) = Real.log (29 / 23) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  linarith

/-- An instance of **Proposition 14.B.1** (MWG, p. 481): in `exA` the optimal contract with
observable effort specifies `e_H` and the fixed wage `-log (23/40)`. -/
theorem exA_proposition_14_B_1 : exA.IsObsOptimal true (fun _ => exWstar true) := by
  refine HAModel.proposition_14_B_1 exA_standing exA_wstar fun e => ?_
  rcases exA_two e with rfl | rfl
  · exact exA_fb_strict.le
  · exact le_rfl

/-- An instance of the **welfare loss in Proposition 14.B.3** (MWG, p. 487): in `exA` every
contract feasible under unobservable effort gives the owner strictly less than the observable
optimum. -/
theorem exA_welfare_loss {e : Bool} {w : ℝ → ℝ} (hw : exA.HAFeasible e w) :
    exA.OP e w < exA.GP true - exWstar true :=
  HAModel.ha_welfare_loss exA_standing exA_strictConcave exA_two (by norm_num [exA, exModel])
    (exA_wstar false) (exA_wstar true) exA_fb_strict hw

/-- The tie model: `g(e_H) = 1 - exp(-1/4)`, `ū = -1`, so `w*_{e_L} = 0` and `w*_{e_H} = 1/4`. -/
noncomputable def exTie : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (1 - Real.exp (-(1 / 4))) (-1)

/-- **Correction to Proposition 14.B.3** (MWG, p. 487). In `exTie` the effort `e_H` is optimal
when effort is observable (it ties with `e_L`), and still unobservability causes no welfare loss:
a contract feasible under unobservable effort attains the observable-effort optimum. -/
theorem exA_tie :
    exTie.IsObsOptimal true (fun _ => 1 / 4) ∧ ∃ e w, exTie.HAFeasible e w ∧
      exTie.OP e w = exTie.OP true (fun _ => 1 / 4) := by
  have hst : exTie.Standing :=
    exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _
  have hws : ∀ b, exTie.v (if b then 1 / 4 else 0) = exTie.ubar + exTie.g b := by
    intro b
    change -Real.exp (-(if b then (1 / 4 : ℝ) else 0)) = -1 + (if b then 1 - Real.exp (-(1 / 4))
      else 0)
    cases b
    · simp
    · simp only [↓reduceIte]; ring
  have hGP : ∀ b, exTie.GP b = if b then 1 else 3 / 4 := exA_GP _ _ _ _
  have hopt : exTie.IsObsOptimal true (fun _ => 1 / 4) := by
    have := HAModel.proposition_14_B_1 hst hws (estar := true) fun e => by
      rcases exA_two e with rfl | rfl
      · simp only [hGP]; norm_num
      · exact le_rfl
    simpa using this
  obtain ⟨hfeas, hOP⟩ := HAModel.ha_no_loss_of_tie hst exA_two
    (show exTie.g false < exTie.g true by
      change (0 : ℝ) < 1 - Real.exp (-(1 / 4))
      have := Real.exp_lt_one_iff.2 (show -(1 / 4 : ℝ) < 0 by norm_num); linarith)
    (wH := 1 / 4) (hws false) (by simp [hGP]; norm_num)
  refine ⟨hopt, false, _, hfeas, ?_⟩
  rw [hOP, HAModel.ha_OP_eq hst (HAModel.ha_const_adm hst _), HAModel.ha_EW_const hst]

/-- The risk-neutral example: `v(w) = w`, `g(e_H) = 1/10`, `ū = 0`. -/
noncomputable def exRN : HAModel Bool := exModel id (fun _ => 1) (1 / 10) 0

/-- An instance of **Proposition 14.B.2** (MWG, p. 482): in `exRN`, selling the project for
`α* = 9/10` implements `e_H` optimally. -/
theorem exA_proposition_14_B_2 :
    exRN.IsHAOptimal true (fun x => x - (exRN.GP true - exRN.g true - exRN.ubar)) := by
  have hst : exRN.Standing :=
    exA_standing_of (fun w => hasDerivAt_id w) (fun _ => one_pos) (concaveOn_id convex_univ) _ _
  have hGP : ∀ b, exRN.GP b = if b then 1 else 3 / 4 := exA_GP _ _ _ _
  refine (HAModel.proposition_14_B_2 hst (fun _ => rfl) fun e => ?_).1
  rcases exA_two e with rfl | rfl
  · rw [hGP, hGP]; simp [exRN, exModel]; norm_num
  · exact le_rfl

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# An additional signal of effort

MWG, Section 14.B (small type), pp. 487-488, condition (14.B.11).

A signal `y` with joint density `f(π, y | e)` is available. Condition (14.B.11) reads
`1 / v'(w(π, y)) = γ + μ [1 - f(π, y | e_L) / f(π, y | e_H)]`.

* `signal_ratio_indep`, `signal_ratio_suffstat`: if `f(π, y | e) = f₁(π | e) f₂(y)`, or more
  generally `f₁(π | e) f₂(y | π)` (`π` a sufficient statistic), the `f₂` terms cancel.
* `signal_foc_indep`: then a scheme satisfying (14.B.11) does not depend on `y`.
* `signal_depends`: conversely, where the likelihood ratio depends on `y`, so do wages.
* `signal_jensen`: the certain payment `w̃(π)` with `v(w̃(π)) = E[v(w(π, y)) | π]` costs at most
  `E[w(π, y) | π]`, strictly less unless `w(π, ·)` is constant.
* `signal_same_utility`, `signal_lower_cost`: integrating over `π` (Fubini), `w̃` gives the
  manager the same expected utility as `w` under every effort and costs the owner no more.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- **p. 487**: with `f(π, y | e) = f₁(π | e) f₂(y)` the likelihood ratio does not involve `y`. -/
theorem signal_ratio_indep (f1L f1H f2 : ℝ) (h2 : f2 ≠ 0) :
    f1L * f2 / (f1H * f2) = f1L / f1H := mul_div_mul_right _ _ h2

/-- **p. 488**: with `f(π, y | e) = f₁(π | e) f₂(y | π)` (`π` a sufficient statistic for `y` with
respect to `e`) the likelihood ratio does not involve `y`. -/
theorem signal_ratio_suffstat (f1 : ℝ → ℝ → ℝ) (f2 : ℝ → ℝ → ℝ) {eL eH x y : ℝ}
    (h2 : f2 y x ≠ 0) : f1 x eL * f2 y x / (f1 x eH * f2 y x) = f1 x eL / f1 x eH :=
  mul_div_mul_right _ _ h2

/-- **(14.B.11)** (MWG, p. 487). If the likelihood ratio at `(π, y)` and `(π, y')` coincides
(as in `signal_ratio_indep`, `signal_ratio_suffstat`) and `v'` is strictly decreasing, a scheme
satisfying (14.B.11) pays the same at `(π, y)` and `(π, y')`. -/
theorem signal_foc_indep {dv : ℝ → ℝ} (hda : StrictAnti dv) {w : ℝ × ℝ → ℝ}
    {r : ℝ × ℝ → ℝ} {γ μ : ℝ} (hfoc : ∀ z, 1 / dv (w z) = γ + μ * (1 - r z)) {x y y' : ℝ}
    (hr : r (x, y) = r (x, y')) : w (x, y) = w (x, y') := by
  have h := (hfoc (x, y)).trans ((hfoc (x, y')).trans (by rw [hr])).symm
  have : dv (w (x, y)) = dv (w (x, y')) := by simpa using h
  exact hda.injective this

/-- **p. 488, the converse direction** (Holmstrom 1979): where the likelihood ratio depends on `y`
and `μ ≠ 0`, a scheme satisfying (14.B.11) depends on `y`. -/
theorem signal_depends {dv : ℝ → ℝ} {w : ℝ × ℝ → ℝ} {r : ℝ × ℝ → ℝ} {γ μ : ℝ} (hμ : μ ≠ 0)
    (hfoc : ∀ z, 1 / dv (w z) = γ + μ * (1 - r z)) {x y y' : ℝ} (hr : r (x, y) ≠ r (x, y')) :
    w (x, y) ≠ w (x, y') := by
  intro h
  have := (hfoc (x, y)).symm.trans ((congrArg (fun t => 1 / dv t) h).trans (hfoc (x, y')))
  apply hr
  have : μ * (r (x, y') - r (x, y)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hμ
  · linarith

/-- **p. 487-488 (Jensen)**: for a fixed profit level, the certain payment `w̃` with
`v(w̃) = ∫ v(w(π, y)) f₂(y) dy` satisfies `w̃ ≤ ∫ w(π, y) f₂(y) dy`, with strict inequality if
`v` is strictly concave and `w(π, ·)` is not almost everywhere constant. -/
theorem signal_jensen {ν : Measure ℝ} {p u : ℝ → ℝ} {v dv : ℝ → ℝ}
    (hv : ConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m) (hmono : StrictMono v)
    (hp0 : ∀ y, 0 < p y) (hp : Integrable p ν) (hp1 : ∫ y, p y ∂ν = 1)
    (hu : Integrable (fun y => u y * p y) ν) (hvu : Integrable (fun y => v (u y) * p y) ν)
    {wt : ℝ} (hwt : v wt = ∫ y, v (u y) * p y ∂ν) :
    wt ≤ ∫ y, u y * p y ∂ν ∧
      (StrictConcaveOn ℝ univ v → ¬ (∀ᵐ y ∂ν, u y = ∫ y, u y * p y ∂ν) →
        wt < ∫ y, u y * p y ∂ν) := by
  have hJ := tpa_jensen hv hdv (fun y => (hp0 y).le) hp hp1 hu hvu
  refine ⟨hmono.le_iff_le.1 (hwt ▸ hJ), fun hsc hne => ?_⟩
  rcases (hmono.le_iff_le.1 (hwt ▸ hJ)).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    exact tpa_jensen_eq hsc hdv hp0 hp hp1 hu hvu (by rw [← hwt, h])

/-- **p. 488**: under `w̃`, defined profit level by profit level by
`v(w̃(π)) = ∫ v(w(π, y)) f₂(y) dy`, the manager's expected utility of income under any effort (with
profit density `f₁`) equals that under `w`. -/
theorem signal_same_utility {ν1 ν2 : Measure ℝ} [SFinite ν1] [SFinite ν2] {v : ℝ → ℝ}
    {w : ℝ × ℝ → ℝ} {wt f1 f2 : ℝ → ℝ}
    (hwt : ∀ x, v (wt x) = ∫ y, v (w (x, y)) * f2 y ∂ν2)
    (hint : Integrable (fun z : ℝ × ℝ => v (w z) * (f1 z.1 * f2 z.2)) (ν1.prod ν2)) :
    ∫ x, v (wt x) * f1 x ∂ν1 = ∫ z, v (w z) * (f1 z.1 * f2 z.2) ∂(ν1.prod ν2) := by
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hwt]
  rw [← integral_mul_const]
  congr 1; funext y; ring

/-- **p. 488**: the owner's expected wage under `w̃` is at most that under `w` (Jensen at each
profit level, then integration over profits). -/
theorem signal_lower_cost {ν1 ν2 : Measure ℝ} [SFinite ν1] [SFinite ν2] {v dv : ℝ → ℝ}
    (hv : ConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m) (hmono : StrictMono v)
    {w : ℝ × ℝ → ℝ} {wt f1 f2 : ℝ → ℝ} (hf1 : ∀ x, 0 ≤ f1 x) (hf2 : ∀ y, 0 < f2 y)
    (hf2i : Integrable f2 ν2) (hf21 : ∫ y, f2 y ∂ν2 = 1)
    (hu : ∀ x, Integrable (fun y => w (x, y) * f2 y) ν2)
    (hvu : ∀ x, Integrable (fun y => v (w (x, y)) * f2 y) ν2)
    (hwt : ∀ x, v (wt x) = ∫ y, v (w (x, y)) * f2 y ∂ν2)
    (hwti : Integrable (fun x => wt x * f1 x) ν1)
    (hint : Integrable (fun z : ℝ × ℝ => w z * (f1 z.1 * f2 z.2)) (ν1.prod ν2)) :
    ∫ x, wt x * f1 x ∂ν1 ≤ ∫ z, w z * (f1 z.1 * f2 z.2) ∂(ν1.prod ν2) := by
  rw [integral_prod _ hint]
  have hin : Integrable (fun x => ∫ y, w (x, y) * (f1 x * f2 y) ∂ν2) ν1 := hint.integral_prod_left
  refine integral_mono hwti hin fun x => ?_
  have hJ := (signal_jensen hv hdv hmono hf2 hf2i hf21 (hu x) (hvu x) (hwt x)).1
  have : ∫ y, w (x, y) * (f1 x * f2 y) ∂ν2 = (∫ y, w (x, y) * f2 y ∂ν2) * f1 x := by
    rw [← integral_mul_const]; congr 1; funext y; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hJ (hf1 x)

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix A: multiple effort levels in the hidden-action model

MWG, Appendix A, pp. 502-504.

Problem (14.AA.1) is `HAModel.IsHACostMin` for an arbitrary effort set `ε` (`HiddenAction`); with
`K` effort levels its incentive constraint is the `K - 1` inequalities `EU e' ≤ EU e`, `e' ≠ e`
(`aa_IC_iff`), and in the manager's utility levels it is linear (footnote 7, `ha_kt_sufficient`).

* `aa_not_implementable`: Figure 14.AA.1. If `f(·|e_M)` is a mixture `α f(·|e_L) + (1 - α) f(·|e_H)`
  and `g(e_M) > α g(e_L) + (1 - α) g(e_H)`, no scheme implements `e_M`.
* `aa_high_implementable`: with two effort levels, strict first-order stochastic dominance and a
  utility of income unbounded above, `e_H` can be implemented ("sufficiently high incentives").
* `aa_high_not_implementable`: correction: with a utility of income bounded above (`-exp(-w)`),
  `e_H` may be impossible to implement although the observable-effort contract for `e_H` exists.
* `foa_sufficient`: the first-order approach (14.AA.2)-(14.AA.3): a scheme satisfying (14.AA.3)
  with complementary slackness solves the relaxed program in which the incentive constraint is
  replaced by the manager's first-order condition.
* `foa_fails`: a solution of the relaxed program need not be incentive compatible: the manager's
  first-order condition holds at an effort level that is not optimal for him.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

/-- **(14.AA.1)(ii)** (MWG, p. 503): the incentive constraint consists of the constraints
`EU e' ≤ EU e` for the other effort levels `e' ≠ e`. -/
theorem aa_IC_iff (M : HAModel ε) (e : ε) (w : ℝ → ℝ) :
    M.IC e w ↔ ∀ e', e' ≠ e → M.EU e' w ≤ M.EU e w := by
  refine ⟨fun h e' _ => h e', fun h e' => ?_⟩
  by_cases he : e' = e
  · rw [he]
  · exact h e' he

/-- **Figure 14.AA.1** (MWG, p. 503). If the profit density under `e_M` is the mixture
`α f(·|e_L) + (1 - α) f(·|e_H)` and `g(e_M) > α g(e_L) + (1 - α) g(e_H)`, then under every scheme
the manager strictly prefers `e_L` or `e_H` to `e_M`: `e_M` cannot be implemented. -/
theorem aa_not_implementable {M : HAModel ε} {eL eM eH : ε} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmix : ∀ x, M.f eM x = α * M.f eL x + (1 - α) * M.f eH x)
    (hg : α * M.g eL + (1 - α) * M.g eH < M.g eM) {w : ℝ → ℝ} (hw : M.Adm w) :
    M.EU eM w < M.EU eL w ∨ M.EU eM w < M.EU eH w := by
  have hEV : M.EV eM w = α * M.EV eL w + (1 - α) * M.EV eH w := by
    unfold EV
    have : (fun x => M.v (w x) * M.f eM x) =
        fun x => α * (M.v (w x) * M.f eL x) + (1 - α) * (M.v (w x) * M.f eH x) := by
      funext x; rw [hmix]; ring
    rw [this, integral_add ((hw.2 eL).2.const_mul _) ((hw.2 eH).2.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold EU
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  rw [hEV] at hc
  nlinarith [hc.1, hc.2]

/-- The two-valued scheme paying `w₁` where `f(π|e_L) < f(π|e_H)` and `w₀` elsewhere. -/
noncomputable def twoVal (M : HAModel ε) (eL eH : ε) (w₀ w₁ : ℝ) (x : ℝ) : ℝ :=
  if M.f eL x < M.f eH x then w₁ else w₀

/-- **"`e_H` could always be induced"** (MWG, p. 503), corrected. With two effort levels, strict
first-order stochastic dominance, `g(e_L) < g(e_H)`, and a utility of income that is unbounded
above, some admissible scheme satisfies the participation and incentive constraints for `e_H`. -/
theorem aa_high_implementable {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (hunb : ∀ y, ∃ w, y ≤ M.v w) :
    ∃ w, M.HAFeasible eH w := by
  set A := {x | M.f eL x < M.f eH x}
  have hA : MeasurableSet A := measurableSet_lt (hM.f_meas eL) (hM.f_meas eH)
  set P : ε → ℝ := fun e => ∫ x in A, M.f e x ∂M.ν
  -- the probability of A is larger under e_H
  have hdiff : 0 < P eH - P eL := by
    have hB := ha_fosd_set hM hfosd
    have hcompl : ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν = P eH - P eL := by
      have h1 : ∫ x in A, (M.f eL x - M.f eH x) ∂M.ν + ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν =
          ∫ x, (M.f eL x - M.f eH x) ∂M.ν := integral_add_compl hA ((hM.f_int eL).sub (hM.f_int eH))
      rw [integral_sub (hM.f_int eL) (hM.f_int eH), hM.f_one, hM.f_one, sub_self,
        integral_sub (hM.f_int eL).integrableOn (hM.f_int eH).integrableOn] at h1
      simp only [P]; linarith
    rw [← hcompl]
    have hsub : {x | M.f eH x < M.f eL x} ⊆ Aᶜ := fun x hx => by
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt]; exact (mem_ofPred_eq ▸ hx).le
    have hnn : ∀ x ∈ Aᶜ, 0 ≤ M.f eL x - M.f eH x := fun x hx => by
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt] at hx; linarith
    have hpos : 0 < ∫ x in {x | M.f eH x < M.f eL x}, (M.f eL x - M.f eH x) ∂M.ν := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · have : Function.support (fun x => M.f eL x - M.f eH x) ∩ {x | M.f eH x < M.f eL x} =
            {x | M.f eH x < M.f eL x} := by
          ext x; simp only [mem_inter_iff, Function.mem_support, mem_ofPred_eq]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨by linarith, h⟩
        rw [this]; exact pos_iff_ne_zero.2 hB
      · filter_upwards [ae_restrict_mem (measurableSet_lt (hM.f_meas eH) (hM.f_meas eL))] with x hx
        simp only [Pi.zero_apply] at hx ⊢; linarith
      · exact ((hM.f_int eL).sub (hM.f_int eH)).integrableOn
    calc 0 < _ := hpos
      _ ≤ ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν :=
        setIntegral_mono_set ((hM.f_int eL).sub (hM.f_int eH)).integrableOn
          (ae_restrict_of_forall_mem hA.compl hnn) (Filter.Eventually.of_forall hsub)
  have hPH : 0 < P eH := by
    have : 0 ≤ P eL := setIntegral_nonneg hA fun x _ => (hM.f_pos eL x).le
    linarith
  -- choose the wages
  set u₀ := M.v 0
  set t := max (u₀ + (M.g eH - M.g eL) / (P eH - P eL)) (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  obtain ⟨w₁, hw₁⟩ := hunb t
  set w := M.twoVal eL eH 0 w₁
  have hEV : ∀ e, M.EV e w = u₀ + (M.v w₁ - u₀) * P e := by
    intro e
    unfold EV
    have hsplit := integral_add_compl hA (show Integrable (fun x => M.v (w x) * M.f e x) M.ν from
      by
        have : (fun x => M.v (w x) * M.f e x) =
            A.indicator (fun x => M.v w₁ * M.f e x) + Aᶜ.indicator (fun x => u₀ * M.f e x) := by
          funext x
          by_cases hx : x ∈ A
          · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
          · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
              not_false_eq_true, ↓reduceIte, zero_add]
            have hx' : ¬ M.f eL x < M.f eH x := hx
            simp only [hx', ↓reduceIte, u₀]
        rw [this]
        exact (((hM.f_int e).const_mul _).indicator hA).add
          (((hM.f_int e).const_mul _).indicator hA.compl))
    rw [← hsplit]
    have e1 : ∫ x in A, M.v (w x) * M.f e x ∂M.ν = M.v w₁ * P e := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hA fun x hx => ?_
      simp only [w, twoVal, show M.f eL x < M.f eH x from hx, ↓reduceIte]
    have e2 : ∫ x in Aᶜ, M.v (w x) * M.f e x ∂M.ν = u₀ * (1 - P e) := by
      have hc := integral_add_compl hA (hM.f_int e)
      rw [hM.f_one] at hc
      have : ∫ x in Aᶜ, M.f e x ∂M.ν = 1 - P e := by simp only [P]; linarith
      rw [← this, ← integral_const_mul]
      refine setIntegral_congr_fun hA.compl fun x hx => ?_
      have hx' : ¬ M.f eL x < M.f eH x := hx
      simp only [w, twoVal, hx', ↓reduceIte, u₀]
    rw [e1, e2]; ring
  have hadm : M.Adm w := by
    refine ⟨Measurable.ite hA measurable_const measurable_const, fun e => ⟨?_, ?_⟩⟩
    · have : (fun x => w x * M.f e x) =
          A.indicator (fun x => w₁ * M.f e x) + Aᶜ.indicator (fun x => 0 * M.f e x) := by
        funext x
        by_cases hx : x ∈ A
        · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
        · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
            not_false_eq_true, ↓reduceIte, zero_add]
          have hx' : ¬ M.f eL x < M.f eH x := hx
          simp only [hx', ↓reduceIte]
      rw [this]
      exact (((hM.f_int e).const_mul _).indicator hA).add
        (((hM.f_int e).const_mul _).indicator hA.compl)
    · have : (fun x => M.v (w x) * M.f e x) =
          A.indicator (fun x => M.v w₁ * M.f e x) + Aᶜ.indicator (fun x => u₀ * M.f e x) := by
        funext x
        by_cases hx : x ∈ A
        · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
        · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
            not_false_eq_true, ↓reduceIte, zero_add]
          have hx' : ¬ M.f eL x < M.f eH x := hx
          simp only [hx', ↓reduceIte, u₀]
      rw [this]
      exact (((hM.f_int e).const_mul _).indicator hA).add
        (((hM.f_int e).const_mul _).indicator hA.compl)
  have ht1 := le_max_left (u₀ + (M.g eH - M.g eL) / (P eH - P eL))
    (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  have ht2 := le_max_right (u₀ + (M.g eH - M.g eL) / (P eH - P eL))
    (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  refine ⟨w, ⟨hadm, ?_⟩, (ha_IC_two hE w).2 ?_⟩
  · unfold EU; rw [hEV]
    have : (M.ubar + M.g eH - u₀) / P eH ≤ M.v w₁ - u₀ := by linarith
    rw [div_le_iff₀ hPH] at this
    linarith
  · unfold EU; rw [hEV, hEV]
    have : (M.g eH - M.g eL) / (P eH - P eL) ≤ M.v w₁ - u₀ := by linarith
    rw [div_le_iff₀ hdiff] at this
    nlinarith

end HAModel

/-- The model of `aa_high_not_implementable`: `v(w) = -exp(-w)`, `g(e_H) = 1/2`, `ū = -1`. -/
noncomputable def exC : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (1 / 2) (-1)

/-- **Correction to p. 503** ("`e_H` could always be induced"). In `exC` (strict first-order
stochastic dominance, `v(w) = -exp(-w)` bounded above) the observable-effort contract for `e_H`
exists (`w = log 2`), but no scheme satisfies the participation and incentive constraints for
`e_H`. -/
theorem aa_high_not_implementable :
    exC.v (Real.log 2) = exC.ubar + exC.g true ∧ ¬ ∃ w, exC.HAFeasible true w := by
  refine ⟨?_, ?_⟩
  · change -Real.exp (-Real.log 2) = -1 + (if true then 1 / 2 else 0)
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  · rintro ⟨w, ⟨⟨hw, hpart⟩, hic⟩⟩
    have hEU : ∀ b : Bool, exC.EU b w = -Real.exp (-w 0) * exF b 0 + -Real.exp (-w 1) * exF b 1 +
        -Real.exp (-w 2) * exF b 2 - (if b then 1 / 2 else 0) := by
      intro b
      change (∫ x, -Real.exp (-w x) * exF b x ∂dmeas exPts) - _ = _
      rw [exA_integral]
      rfl
    have hic' := hic false
    rw [hEU, hEU] at hic'
    have hp := hpart
    change -1 ≤ exC.EU true w at hp
    rw [hEU] at hp
    simp only [exF, Bool.false_eq_true, ↓reduceIte] at hic' hp
    norm_num at hic' hp
    have h0 := Real.exp_pos (-w 0)
    have h1 := Real.exp_pos (-w 1)
    have h2 := Real.exp_pos (-w 2)
    nlinarith

/-- **The first-order approach** (MWG, p. 504, (14.AA.2)-(14.AA.3)). For one-dimensional effort the
incentive constraint is replaced by the manager's first-order condition
`∫ v(w(π)) f_e(π|e) dπ = g'(e)` (with `f_e` given by `fe`). If `w` satisfies this condition, and
`1 / v'(w(π)) = λ + μ f_e(π|e) / f(π|e)` at almost every `π`
with `λ ≥ 0` and complementary slackness (`μ` is unrestricted in sign since the constraint is an
equality), then `w` solves the relaxed program. -/
theorem foa_sufficient {ε : Type*} {M : HAModel ε} (hM : M.Standing) {e : ε} {fe : ℝ → ℝ} {dg : ℝ}
    (hfe : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * fe x) M.ν)
    {w : ℝ → ℝ} (hw : M.Adm w) {lam μ : ℝ} (hlam : 0 ≤ lam)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = lam + μ * (fe x / M.f e x))
    (hcs : lam * (M.EU e w - M.ubar) = 0)
    (hfoa : ∫ x, M.v (w x) * fe x ∂M.ν = dg) {w' : ℝ → ℝ} (hw' : M.Adm w')
    (hpart' : M.ubar ≤ M.EU e w') (hfoa' : ∫ x, M.v (w' x) * fe x ∂M.ν = dg) :
    M.EW e w ≤ M.EW e w' := by
  have hpt : ∀ᵐ x ∂M.ν, lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
      μ * (M.v (w' x) * fe x - M.v (w x) * fe x) ≤ w' x * M.f e x - w x * M.f e x := by
    filter_upwards [hfoc] with x hx
    have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hf := hM.f_pos e x
    have key : (M.v (w' x) - M.v (w x)) * (1 / M.dv (w x)) ≤ w' x - w x := by
      rw [mul_one_div, div_le_iff₀ hd]; linarith
    rw [hx] at key
    have key2 := mul_le_mul_of_nonneg_right key hf.le
    have hr : fe x / M.f e x * M.f e x = fe x := div_mul_cancel₀ _ hf.ne'
    have : (M.v (w' x) - M.v (w x)) * (lam + μ * (fe x / M.f e x)) * M.f e x =
        lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
          μ * (M.v (w' x) * fe x - M.v (w x) * fe x) := by
      have : (M.v (w' x) - M.v (w x)) * (lam + μ * (fe x / M.f e x)) * M.f e x =
          (M.v (w' x) - M.v (w x)) * (lam * M.f e x + μ * (fe x / M.f e x * M.f e x)) := by ring
      rw [this, hr]; ring
    linarith
  have hi1 : Integrable (fun x => lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x)) M.ν :=
    ((hw'.2 e).2.sub (hw.2 e).2).const_mul lam
  have hi2 : Integrable (fun x => μ * (M.v (w' x) * fe x - M.v (w x) * fe x)) M.ν :=
    ((hfe w' hw').sub (hfe w hw)).const_mul μ
  have hint : ∫ x, (lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
      μ * (M.v (w' x) * fe x - M.v (w x) * fe x)) ∂M.ν ≤
      ∫ x, (w' x * M.f e x - w x * M.f e x) ∂M.ν :=
    integral_mono_ae (hi1.add hi2) ((hw'.2 e).1.sub (hw.2 e).1) hpt
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_sub (hw'.2 e).2 (hw.2 e).2, integral_sub (hfe w' hw') (hfe w hw), hfoa, hfoa',
    integral_sub (hw'.2 e).1 (hw.2 e).1] at hint
  change lam * (M.EV e w' - M.EV e w) + μ * (dg - dg) ≤ M.EW e w' - M.EW e w at hint
  unfold HAModel.EU at hpart' hcs
  have : 0 ≤ lam * (M.EV e w' - M.g e - M.ubar) := mul_nonneg hlam (by linarith)
  nlinarith

/-- **The first-order approach can fail** (MWG, p. 504). Two outcomes, effort `e ∈ [0, 1]`,
`f(π_H | e) = (1 + e²)/3`, `g(e) = e/6`, a risk-neutral manager and `ū = 0`. For `e = 1/2` the
relaxed program (participation and the first-order condition `f'(π_H|e)(w_H - w_L) = g'(e)`) has the
unique solution `w_L = -1/8`, `w_H = 3/8`; but under it the manager strictly prefers `e = 1` to
`e = 1/2` (where his first-order condition holds at a minimum). -/
theorem foa_fails :
    let p : ℝ → ℝ := fun e => (1 + e ^ 2) / 3
    let U : ℝ → ℝ → ℝ → ℝ := fun wL wH e => wL + p e * (wH - wL) - e / 6
    (∀ wL wH, 0 ≤ U wL wH (1 / 2) → 2 * (1 / 2) / 3 * (wH - wL) = 1 / 6 →
      wL + p (1 / 2) * (wH - wL) ≥ -1 / 8 + p (1 / 2) * (3 / 8 - -1 / 8)) ∧
    U (-1 / 8) (3 / 8) (1 / 2) = 0 ∧ 2 * (1 / 2) / 3 * (3 / 8 - -1 / 8) = (1 / 6 : ℝ) ∧
    (∀ wL wH, 0 ≤ U wL wH (1 / 2) → 2 * (1 / 2) / 3 * (wH - wL) = 1 / 6 →
      wL + p (1 / 2) * (wH - wL) = -1 / 8 + p (1 / 2) * (3 / 8 - -1 / 8) →
      wL = -1 / 8 ∧ wH = 3 / 8) ∧
    U (-1 / 8) (3 / 8) (1 / 2) < U (-1 / 8) (3 / 8) 1 := by
  intro p U
  simp only [p, U]
  refine ⟨fun wL wH h1 h2 => by nlinarith, by norm_num, by norm_num,
    fun wL wH h1 h2 h3 => ⟨by nlinarith, by nlinarith⟩, by norm_num⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two-type screening program

MWG, Section 14.C, pp. 494-499, problems (14.C.8) and (14.C.10); Appendix B, problem (14.BB.1);
Exercise 14.BB.1.

The owner (or firm) offers wage-effort pairs `(w_H, e_H)`, `(w_L, e_L)` with `e ≥ 0`; type `θ_i`
(probability `λ` for `θ_H`) gets `w - g(e, θ_i)`, and must get at least `c` (`c = v⁻¹(ū)` in
(14.C.8) for the infinitely risk-averse manager, `c = ū` in (14.C.10)). The owner's profit in state
`θ_i` is `π_i(e) - w`. This module proves the structure of the program using only that
`D(e) = g(e, θ_L) - g(e, θ_H)` vanishes at `0` and is strictly increasing on `[0, ∞)` (the
single-crossing property), and that the full-information efforts `e*_i` are the unique maximizers
of `S_i(e) = π_i(e) - g(e, θ_i)`, with `e*_L ≤ e*_H`. Derivative versions are in `HiddenInfo`.

* `lemma_14_C_1`: constraint (ii) is implied by (i) and (iii).
* `screen_Pi_le`, `screen_Pi_bind`: every contract satisfying (i) and (iii) earns at most
  `R(e_H, e_L) = λ S_H(e_H) + (1 - λ) S_L(e_L) - λ D(e_L) - c`, with equality iff (i) and (iii)
  bind; the binding contract `bind e_H e_L` attains it.
* `lemma_14_C_2`, `screen_iii_binds`: (i) and (iii) bind at an optimum.
* `lemma_14_C_3`: `e_L ≤ e*_L` and `e_H = e*_H`.
* `screen_opt_iff`: the optimal contracts are exactly `bind e*_H e_L` with `e_L` maximizing
  `Q(e) = (1 - λ) S_L(e) - λ D(e)` on `[0, ∞)`.
* `screen_iv_slack`, `screen_H_rent`, `screen_loss`: only (iii) binds (p. 497); the `θ_H` manager
  gets a rent; the owner loses relative to full information (Proposition 14.C.3).
* `screen_fb_violates_iii`: the full-information contract violates (iii) (p. 495).
* `exercise_14_BB_1`: the relaxed program without (iv) has the same solutions.
-/

namespace MWG.PrincipalAgent

open Set

/-- **(14.C.8), (14.C.10)** (MWG, pp. 494, 500). The data of the two-type screening program:
the owner's profit functions in the two states, the disvalue of effort `g(e, θ)`, the two states,
the probability `λ` of `θ_H`, and the reservation level `c` of `w - g(e, θ)`. -/
structure Screen where
  pH : ℝ → ℝ
  pL : ℝ → ℝ
  g : ℝ → ℝ → ℝ
  θL : ℝ
  θH : ℝ
  lam : ℝ
  c : ℝ

/-- A contract (revelation mechanism) `[(w_H, e_H), (w_L, e_L)]`. -/
structure HIContract where
  wH : ℝ
  eH : ℝ
  wL : ℝ
  eL : ℝ

namespace Screen

/-- The owner's expected profit `λ[π_H(e_H) - w_H] + (1 - λ)[π_L(e_L) - w_L]`. -/
def Pi (P : Screen) (K : HIContract) : ℝ :=
  P.lam * (P.pH K.eH - K.wH) + (1 - P.lam) * (P.pL K.eL - K.wL)

/-- Constraint (i): reservation utility in state `θ_L`. -/
def C1 (P : Screen) (K : HIContract) : Prop := P.c ≤ K.wL - P.g K.eL P.θL

/-- Constraint (ii): reservation utility in state `θ_H`. -/
def C2 (P : Screen) (K : HIContract) : Prop := P.c ≤ K.wH - P.g K.eH P.θH

/-- Constraint (iii): truth-telling in state `θ_H`. -/
def C3 (P : Screen) (K : HIContract) : Prop :=
  K.wL - P.g K.eL P.θH ≤ K.wH - P.g K.eH P.θH

/-- Constraint (iv): truth-telling in state `θ_L`. -/
def C4 (P : Screen) (K : HIContract) : Prop :=
  K.wH - P.g K.eH P.θL ≤ K.wL - P.g K.eL P.θL

/-- The feasible set of (14.C.8). -/
def Feas (P : Screen) (K : HIContract) : Prop :=
  0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C2 K ∧ P.C3 K ∧ P.C4 K

/-- The feasible set of (14.BB.1): (14.C.8) without constraint (ii). -/
def Feas3 (P : Screen) (K : HIContract) : Prop := 0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C3 K ∧ P.C4 K

/-- The relaxed feasible set of Exercise 14.BB.1: (14.BB.1) without constraint (iv). -/
def FeasRelax (P : Screen) (K : HIContract) : Prop := 0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C3 K

/-- An optimal contract: a solution of (14.C.8). -/
def IsOpt (P : Screen) (K : HIContract) : Prop := P.Feas K ∧ ∀ K', P.Feas K' → P.Pi K' ≤ P.Pi K

/-- A solution of the relaxed program of Exercise 14.BB.1. -/
def IsOptRelax (P : Screen) (K : HIContract) : Prop :=
  P.FeasRelax K ∧ ∀ K', P.FeasRelax K' → P.Pi K' ≤ P.Pi K

/-- `D(e) = g(e, θ_L) - g(e, θ_H)`, the information rent per unit of `θ_L` effort. -/
def D (P : Screen) (e : ℝ) : ℝ := P.g e P.θL - P.g e P.θH

/-- The full-information surplus in state `θ_H`. -/
def SH (P : Screen) (e : ℝ) : ℝ := P.pH e - P.g e P.θH

/-- The full-information surplus in state `θ_L`. -/
def SL (P : Screen) (e : ℝ) : ℝ := P.pL e - P.g e P.θL

/-- The virtual surplus of the `θ_L` effort, `(1 - λ) S_L(e) - λ D(e)`. -/
def Q (P : Screen) (e : ℝ) : ℝ := (1 - P.lam) * P.SL e - P.lam * P.D e

/-- The profit bound `R(e_H, e_L) = λ S_H(e_H) + Q(e_L) - c`. -/
def R (P : Screen) (eH eL : ℝ) : ℝ := P.lam * P.SH eH + P.Q eL - P.c

/-- The contract in which (i) and (iii) bind. -/
def bind (P : Screen) (eH eL : ℝ) : HIContract :=
  ⟨P.c + P.D eL + P.g eH P.θH, eH, P.c + P.g eL P.θL, eL⟩

/-- Standing assumptions of the screening program: `0 < λ < 1`, and `D(0) = 0` with `D` strictly
increasing on `[0, ∞)` (the single-crossing property, p. 490). -/
structure Hyp (P : Screen) : Prop where
  lam_pos : 0 < P.lam
  lam_lt : P.lam < 1
  D_zero : P.D 0 = 0
  D_mono : StrictMonoOn P.D (Ici 0)

/-- `D(e) ≥ 0` for `e ≥ 0`, strictly for `e > 0`. -/
theorem screen_D_pos {P : Screen} (h : P.Hyp) {e : ℝ} (he : 0 < e) : 0 < P.D e := by
  have := h.D_mono (mem_Ici.2 le_rfl) (mem_Ici.2 he.le) he
  rwa [h.D_zero] at this

theorem screen_D_nonneg {P : Screen} (h : P.Hyp) {e : ℝ} (he : 0 ≤ e) : 0 ≤ P.D e := by
  rcases he.lt_or_eq with he | rfl
  · exact (screen_D_pos h he).le
  · rw [h.D_zero]

/-- **Lemma 14.C.1** (MWG, p. 495). Constraint (ii) can be ignored: a contract is feasible for
(14.C.8) iff it satisfies the other constraints. -/
theorem lemma_14_C_1 {P : Screen} (h : P.Hyp) (K : HIContract) : P.Feas K ↔ P.Feas3 K := by
  constructor
  · rintro ⟨h1, h2, h3, -, h5, h6⟩; exact ⟨h1, h2, h3, h5, h6⟩
  · rintro ⟨h1, h2, h3, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    have := screen_D_nonneg h h2
    unfold C1 at h3; unfold C3 at h5; unfold D at this; unfold C2
    linarith

/-- Feasibility (in fact (iii) and (iv)) forces `e_L ≤ e_H` (MWG, p. 497; Appendix B, Step 4). -/
theorem screen_eL_le_eH {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.Feas3 K) :
    K.eL ≤ K.eH := by
  obtain ⟨h1, h2, -, h5, h6⟩ := hK
  have : P.D K.eL ≤ P.D K.eH := by unfold C3 at h5; unfold C4 at h6; unfold D; linarith
  exact (h.D_mono.le_iff_le h2 h1).1 this

/-- Every contract satisfying (i) and (iii) earns at most `R(e_H, e_L)`. -/
theorem screen_Pi_le {P : Screen} (h : P.Hyp) {K : HIContract} (h1 : P.C1 K) (h3 : P.C3 K) :
    P.Pi K ≤ P.R K.eH K.eL := by
  unfold C1 at h1; unfold C3 at h3
  have hl := h.lam_pos; have hl' := h.lam_lt
  have a : 0 ≤ P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) :=
    mul_nonneg hl.le (by unfold D; linarith)
  have b : 0 ≤ (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) :=
    mul_nonneg (by linarith) (by linarith)
  unfold Pi R Q SH SL; nlinarith

/-- Equality in `screen_Pi_le` holds iff (i) and (iii) bind. -/
theorem screen_Pi_eq_iff {P : Screen} (h : P.Hyp) {K : HIContract} (h1 : P.C1 K)
    (h3 : P.C3 K) : P.Pi K = P.R K.eH K.eL ↔
      K.wL = P.c + P.g K.eL P.θL ∧ K.wH = P.c + P.D K.eL + P.g K.eH P.θH := by
  unfold C1 at h1; unfold C3 at h3
  have hl := h.lam_pos; have hl' := h.lam_lt
  constructor
  · intro heq
    have a : 0 ≤ P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) :=
      mul_nonneg hl.le (by unfold D; linarith)
    have b : 0 ≤ (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) :=
      mul_nonneg (by linarith) (by linarith)
    have hsum : P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) +
        (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) = 0 := by
      unfold Pi R Q SH SL at heq; linarith
    have ha : P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) = 0 := by linarith
    have hb : (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) = 0 := by linarith
    rcases mul_eq_zero.1 ha with ha | ha
    · linarith
    rcases mul_eq_zero.1 hb with hb | hb
    · linarith
    constructor <;> linarith
  · rintro ⟨hL, hH⟩
    unfold Pi R Q SH SL; rw [hL, hH]; ring

/-- The binding contract earns exactly `R(e_H, e_L)`. -/
theorem screen_Pi_bind (P : Screen) (eH eL : ℝ) : P.Pi (P.bind eH eL) = P.R eH eL := by
  unfold Pi R Q SH SL bind D; ring

/-- The binding contract is feasible when `0 ≤ e_L ≤ e_H`. -/
theorem screen_bind_feas {P : Screen} (h : P.Hyp) {eH eL : ℝ} (hL : 0 ≤ eL) (hLH : eL ≤ eH) :
    P.Feas (P.bind eH eL) := by
  have hle : P.D eL ≤ P.D eH := h.D_mono.monotoneOn hL (hL.trans hLH) hLH
  refine (lemma_14_C_1 h _).2 ⟨hL.trans hLH, hL, ?_, ?_, ?_⟩
  · unfold C1 bind; simp
  · unfold C3 bind D; simp only; linarith
  · unfold C4 bind D; unfold D at hle; simp only; linarith

/-- **Lemma 14.C.2** (MWG, p. 495) and the binding of (iii) (p. 497): at an optimal contract
constraints (i) and (iii) bind. -/
theorem lemma_14_C_2 {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K) :
    K.wL = P.c + P.g K.eL P.θL ∧ K.wH = P.c + P.D K.eL + P.g K.eH P.θH := by
  have h3 := (lemma_14_C_1 h K).1 hK.1
  have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
  have hge := hK.2 _ (screen_bind_feas h hK.1.2.1 (screen_eL_le_eH h h3))
  rw [screen_Pi_bind] at hge
  exact (screen_Pi_eq_iff h h3.2.2.1 h3.2.2.2.1).1 (le_antisymm hle hge)

/-- The full-information efforts: `e*` uniquely maximizes the surplus `S` on `[0, ∞)`. -/
def IsFB (S : ℝ → ℝ) (estar : ℝ) : Prop :=
  0 ≤ estar ∧ ∀ e, 0 ≤ e → e ≠ estar → S e < S estar

/-- Lowering `e_L` to `min e_L e*_L` raises the virtual surplus `Q`, strictly if `e_L > e*_L`. -/
theorem screen_Q_min {P : Screen} (h : P.Hyp) {eLs : ℝ} (hL : IsFB P.SL eLs) {e : ℝ}
    (he : 0 ≤ e) : P.Q e ≤ P.Q (min e eLs) ∧ (eLs < e → P.Q e < P.Q (min e eLs)) := by
  rcases le_or_gt e eLs with hle | hlt
  · rw [min_eq_left hle]; exact ⟨le_rfl, fun h' => absurd h' (not_lt.2 hle)⟩
  · rw [min_eq_right hlt.le]
    have hS := hL.2 e he hlt.ne'
    have hD := h.D_mono hL.1 he hlt
    have hl := h.lam_pos; have hl' := h.lam_lt
    have : P.Q e < P.Q eLs := by
      unfold Q; nlinarith [mul_lt_mul_of_pos_left hS (by linarith : (0:ℝ) < 1 - P.lam),
        mul_lt_mul_of_pos_left hD hl]
    exact ⟨this.le, fun _ => this⟩

/-- **Lemma 14.C.3** (MWG, p. 496). In any optimal contract (i) `e_L ≤ e*_L` and
(ii) `e_H = e*_H`. -/
theorem lemma_14_C_3 {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) {K : HIContract} (hK : P.IsOpt K) :
    K.eL ≤ eLs ∧ K.eH = eHs := by
  have h3 := (lemma_14_C_1 h K).1 hK.1
  have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
  set e' := min K.eL eLs
  have he' : 0 ≤ e' := le_min hK.1.2.1 hL.1
  have hfeas := screen_bind_feas h he' ((min_le_right _ _).trans hord)
  have hge := hK.2 _ hfeas
  rw [screen_Pi_bind] at hge
  obtain ⟨hQ, hQs⟩ := screen_Q_min h hL hK.1.2.1
  have hl := h.lam_pos
  have hSH : P.SH K.eH ≤ P.SH eHs := by
    rcases eq_or_ne K.eH eHs with heq | hne
    · rw [heq]
    · exact (hH.2 _ hK.1.1 hne).le
  unfold R at hle hge
  have hLle : K.eL ≤ eLs := by
    by_contra hc
    have := hQs (not_le.1 hc)
    nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
  refine ⟨hLle, ?_⟩
  by_contra hne
  have hlt := hH.2 _ hK.1.1 hne
  have hm : e' = K.eL := min_eq_left hLle
  rw [hm] at hge
  nlinarith [mul_lt_mul_of_pos_left hlt hl]

/-- **Lemma 14.C.3 and Appendix B** (MWG, pp. 496-499, 504-506): the optimal contracts are exactly
the binding contracts `bind e*_H e_L` where `e_L ≥ 0` maximizes the virtual surplus
`Q(e) = (1 - λ)[π_L(e) - g(e, θ_L)] - λ[g(e, θ_L) - g(e, θ_H)]` on `[0, ∞)`. -/
theorem screen_opt_iff {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) (K : HIContract) :
    P.IsOpt K ↔ 0 ≤ K.eL ∧ (∀ e, 0 ≤ e → P.Q e ≤ P.Q K.eL) ∧ K = P.bind eHs K.eL := by
  constructor
  · intro hK
    obtain ⟨hLle, hHe⟩ := lemma_14_C_3 h hH hL hord hK
    obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
    have hKb : K = P.bind eHs K.eL := by
      obtain ⟨wH, eH, wL, eL⟩ := K
      simp only at hHe hwL hwH
      subst hHe
      simp only [bind, hwL, hwH]
    refine ⟨hK.1.2.1, fun e he => ?_, hKb⟩
    obtain ⟨hQ, -⟩ := screen_Q_min h hL he
    have hfeas := screen_bind_feas h (le_min he hL.1) ((min_le_right e eLs).trans hord)
    have := hK.2 _ hfeas
    rw [screen_Pi_bind, hKb, screen_Pi_bind] at this
    unfold R at this
    linarith
  · rintro ⟨h0, hmax, hKb⟩
    have hLle : K.eL ≤ eLs := by
      by_contra hc
      have := (screen_Q_min h hL h0).2 (not_le.1 hc)
      have := hmax _ (le_min h0 hL.1)
      linarith
    refine ⟨hKb ▸ screen_bind_feas h h0 (hLle.trans hord), fun K' hK' => ?_⟩
    have h3 := (lemma_14_C_1 h K').1 hK'
    have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
    rw [hKb, screen_Pi_bind]
    have hSH : P.SH K'.eH ≤ P.SH eHs := by
      rcases eq_or_ne K'.eH eHs with heq | hne
      · rw [heq]
      · exact (hH.2 _ hK'.1 hne).le
    have := hmax _ hK'.2.1
    unfold R at hle ⊢
    nlinarith [mul_le_mul_of_nonneg_left hSH h.lam_pos.le]

/-- The truth-telling constraint (iv) is slack at an optimal contract with `e_L < e_H` (MWG,
p. 497: "only the truth-telling constraint for state `θ_H` is binding"). -/
theorem screen_iv_slack {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K)
    (hlt : K.eL < K.eH) : K.wH - P.g K.eH P.θL < K.wL - P.g K.eL P.θL := by
  obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
  have := h.D_mono hK.1.2.1 hK.1.1 hlt
  unfold D at this hwH; rw [hwL, hwH]; linarith

/-- **Proposition 14.C.3** (MWG, p. 499): at an optimal contract the manager gets exactly `c` in
state `θ_L` and the rent `c + D(e_L)` in state `θ_H`, which exceeds `c` when `e_L > 0`. -/
theorem screen_H_rent {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K) :
    K.wL - P.g K.eL P.θL = P.c ∧ K.wH - P.g K.eH P.θH = P.c + P.D K.eL ∧
      (0 < K.eL → P.c < K.wH - P.g K.eH P.θH) := by
  obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
  refine ⟨by rw [hwL]; ring, by rw [hwH]; ring, fun hpos => ?_⟩
  have := screen_D_pos h hpos
  rw [hwH]; linarith

/-- The full-information payoff of the owner with an infinitely risk-averse manager:
`λ S_H(e*_H) + (1 - λ) S_L(e*_L) - c`. -/
def FBval (P : Screen) (eHs eLs : ℝ) : ℝ := P.lam * P.SH eHs + (1 - P.lam) * P.SL eLs - P.c

/-- **Proposition 14.C.3, the owner's loss** (MWG, p. 499). If `e_L > 0` at an optimal contract,
the owner's expected payoff is strictly below its full-information value. -/
theorem screen_loss {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) {K : HIContract} (hK : P.IsOpt K)
    (hpos : 0 < K.eL) : P.Pi K < P.FBval eHs eLs := by
  obtain ⟨-, -, hKb⟩ := (screen_opt_iff h hH hL hord K).1 hK
  rw [hKb, screen_Pi_bind]
  have hS : P.SL K.eL ≤ P.SL eLs := by
    rcases eq_or_ne K.eL eLs with heq | hne
    · rw [heq]
    · exact (hL.2 _ hpos.le hne).le
  have hD := screen_D_pos h hpos
  have hl := h.lam_pos; have hl' := h.lam_lt
  unfold R Q FBval
  nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0:ℝ) ≤ 1 - P.lam),
    mul_pos hl hD]

/-- The full-information contract `w_i = c + g(e*_i, θ_i)` violates the truth-telling constraint
(iii) when `e*_L > 0` (MWG, pp. 492, 495). -/
theorem screen_fb_violates_iii {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hpos : 0 < eLs) :
    ¬ P.C3 ⟨P.c + P.g eHs P.θH, eHs, P.c + P.g eLs P.θL, eLs⟩ := by
  intro h3
  have := screen_D_pos h hpos
  unfold C3 at h3; unfold D at this; simp only at h3; linarith

/-- **Exercise 14.BB.1** (MWG, p. 510). The relaxed program ignoring (iv) (and (ii)) has exactly
the same solutions as (14.C.8): its solutions satisfy (iv). -/
theorem exercise_14_BB_1 {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) (K : HIContract) :
    P.IsOptRelax K ↔ P.IsOpt K := by
  rw [screen_opt_iff h hH hL hord]
  have hbound : ∀ K', P.FeasRelax K' → P.Pi K' ≤ P.R K'.eH K'.eL :=
    fun K' hK' => screen_Pi_le h hK'.2.2.1 hK'.2.2.2
  constructor
  · intro hK
    have h0 := hK.1.2.1
    have hle := hbound K hK.1
    have hSHmax : ∀ e', 0 ≤ e' → P.Q e' ≤ P.Q K.eL ∧ P.SH K.eH = P.SH eHs ∧
        P.Pi K = P.R K.eH K.eL := by
      intro e' he'
      have hrel : P.FeasRelax (P.bind eHs e') := by
        refine ⟨hH.1, he', ?_, ?_⟩
        · unfold C1 bind; simp
        · unfold C3 bind D; simp only; linarith
      have hge := hK.2 _ hrel
      rw [screen_Pi_bind] at hge
      have hSH : P.SH K.eH ≤ P.SH eHs := by
        rcases eq_or_ne K.eH eHs with heq | hne
        · rw [heq]
        · exact (hH.2 _ hK.1.1 hne).le
      have hrel0 : P.FeasRelax (P.bind eHs K.eL) := by
        refine ⟨hH.1, h0, ?_, ?_⟩
        · unfold C1 bind; simp
        · unfold C3 bind D; simp only; linarith
      have hge0 := hK.2 _ hrel0
      rw [screen_Pi_bind] at hge0
      have hl := h.lam_pos
      unfold R at hle hge hge0
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
      · by_contra hne
        have : P.SH K.eH < P.SH eHs := lt_of_le_of_ne hSH hne
        nlinarith [mul_lt_mul_of_pos_left this hl]
      · unfold R; nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
    have hHe : K.eH = eHs := by
      by_contra hne
      have := (hSHmax 0 le_rfl).2.1
      exact absurd this (hH.2 _ hK.1.1 hne).ne
    obtain ⟨hwL, hwH⟩ := (screen_Pi_eq_iff h hK.1.2.2.1 hK.1.2.2.2).1 (hSHmax 0 le_rfl).2.2
    refine ⟨h0, fun e he => (hSHmax e he).1, ?_⟩
    obtain ⟨wH, eH, wL, eL⟩ := K
    simp only at hHe hwL hwH
    subst hHe
    simp only [bind, hwL, hwH]
  · rintro ⟨h0, hmax, hKb⟩
    have hLle : K.eL ≤ eLs := by
      by_contra hc
      have := (screen_Q_min h hL h0).2 (not_le.1 hc)
      have := hmax _ (le_min h0 hL.1)
      linarith
    refine ⟨?_, fun K' hK' => ?_⟩
    · have := screen_bind_feas h h0 (hLle.trans hord)
      rw [← hKb] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2.1⟩
    · have hle := hbound K' hK'
      rw [hKb, screen_Pi_bind]
      have hSH : P.SH K'.eH ≤ P.SH eHs := by
        rcases eq_or_ne K'.eH eHs with heq | hne
        · rw [heq]
        · exact (hH.2 _ hK'.1 hne).le
      have := hmax _ hK'.2.1
      unfold R at hle ⊢
      nlinarith [mul_le_mul_of_nonneg_left hSH h.lam_pos.le]

end Screen

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The hidden-information model

MWG, Section 14.C, pp. 488-500, and Appendix B, pp. 504-506.

Effort `e ∈ [0, ∞)` is observable; profits are `π(e)` with `π(0) = 0`, `π' > 0`, `π'' < 0`; the
manager has utility `v(w - g(e, θ))` with `v' > 0`, `v'' < 0`, where `g(0, θ) = 0`,
`g_e(0, θ) = 0`, `g_ee > 0` and `g_eθ < 0` for `e > 0`; two states `θ_L < θ_H` with
`Prob(θ_H) = λ ∈ (0, 1)`. To cover Exercise 14.C.5 and the monopolistic screening model (14.C.10)
the owner's profit may depend on the state (`π_H`, `π_L` with `π'_H ≥ π'_L > 0`); the model of
Section 14.C is `π_H = π_L = π`. Derivatives are taken within `[0, ∞)`; `π'' < 0` and `g_ee > 0`
are used only through the strict concavity of `π` and strict convexity of `g(·, θ)` they imply,
and `g_eθ < 0` through `g_e(e, θ_H) < g_e(e, θ_L)` for `e > 0` (`hi_cross_of_deriv` derives this).

* `hi_g_theta_inconsistent`: MWG's `g_θ(e, θ) < 0` "for all `e`" contradicts `g(0, θ) = 0`; it
  is not used (correction).
* `hi_hyp`, `hi_fb_of_foc`, `hi_fb_order`: single crossing; the first-best efforts (14.C.7) and
  `e*_H > e*_L`.
* `proposition_14_C_1`, `hi_obs_foc`: Proposition 14.C.1 and the first-order conditions
  (14.C.2)-(14.C.6).
* `hi_H_prefers_L`: in state `θ_H` the manager would lie (p. 492).
* `hi_eL_pos`, `hi_foc_14_C_9`, `lemma_14_C_4`, `proposition_14_C_3`: Appendix B Step 3, (14.C.9)
  = (14.BB.7), Lemma 14.C.4, Proposition 14.C.3.
* `hi_eL_falls`: the optimal `e_L` falls as `λ / (1 - λ)` rises (p. 499).
* `footnote_17`: `e_L = 0` can be optimal only if `g_e(0, θ_L) > 0`.
* `appendix_B_steps`, `appendix_B_multipliers`: Steps 1-5 of Appendix B and the multipliers.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- A function with positive derivative within `[a, ∞)` at `a` exceeds `f a` somewhere to the
right of `a`. -/
theorem hi_exists_gt_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivWithinAt f d (Ici a) a)
    (hd : 0 < d) : ∃ y, a < y ∧ f a < f y := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.1 hf).eventually (lt_mem_nhds hd)
  have hset : Ici a \ {a} = Ioi a := by
    ext x; simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h; exact ⟨h.le, h.ne'⟩
  rw [hset] at ht
  obtain ⟨y, hy, hya⟩ := (ht.and self_mem_nhdsWithin).exists
  refine ⟨y, hya, ?_⟩
  rw [slope_def_field, lt_div_iff₀ (sub_pos.2 hya)] at hy
  linarith

/-- The derivative of a strictly concave function is strictly decreasing. -/
theorem hi_deriv_anti {S : Set ℝ} {h : ℝ → ℝ} (hc : StrictConcaveOn ℝ S h) {x y dx dy : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivWithinAt h dx S x)
    (hdy : HasDerivWithinAt h dy S y) : dy < dx := by
  have h1 := tpa_tangent_lt hc hx hy hxy.ne' hdx
  have h2 := tpa_tangent_lt hc hy hx hxy.ne hdy
  nlinarith

/-- The derivative of a strictly convex function is strictly increasing. -/
theorem hi_deriv_mono {S : Set ℝ} {h : ℝ → ℝ} (hc : StrictConvexOn ℝ S h) {x y dx dy : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivWithinAt h dx S x)
    (hdy : HasDerivWithinAt h dy S y) : dx < dy := by
  have := hi_deriv_anti hc.neg hx hy hxy hdx.neg hdy.neg
  linarith

/-- **Correction** (MWG, p. 489). The assumptions `g(0, θ) = 0` for all `θ` and `g_θ(e, θ) < 0`
"for all `e`" are inconsistent: at `e = 0` the function `θ ↦ g(0, θ)` is constant, so its
derivative vanishes. (Only `g_θ < 0` for `e > 0` is consistent; it is not needed here.) -/
theorem hi_g_theta_inconsistent (g gθ : ℝ → ℝ → ℝ) (hg0 : ∀ θ, g 0 θ = 0) (θ : ℝ)
    (hd : HasDerivAt (fun θ => g 0 θ) (gθ 0 θ) θ) : ¬ gθ 0 θ < 0 := by
  have hc : (fun θ => g 0 θ) = fun _ => 0 := funext hg0
  rw [hc] at hd
  rw [hd.unique (hasDerivAt_const θ 0)]
  exact lt_irrefl 0

/-- **The single-crossing assumption** (MWG, p. 489): `g_eθ < 0` for `e > 0` gives
`g_e(e, θ_H) < g_e(e, θ_L)` when `θ_L < θ_H`. -/
theorem hi_cross_of_deriv {ge geθ : ℝ → ℝ → ℝ} {e : ℝ}
    (hd : ∀ θ, HasDerivAt (fun θ => ge e θ) (geθ e θ) θ) (hneg : ∀ θ, geθ e θ < 0)
    {θL θH : ℝ} (hθ : θL < θH) : ge e θH < ge e θL :=
  strictAnti_of_hasDerivAt_neg hd hneg hθ

/-- **Section 14.C** (MWG, pp. 489-490). The hidden-information model with state-dependent profits
`π_H`, `π_L` (derivatives `dpH`, `dpL`), disutility `g(e, θ)` with `g_e = ge`, utility `v` with
`v' = dv`, the two states, `λ = Prob(θ_H)`, the reservation utility `ū`, and `c = v⁻¹(ū)`. -/
structure HIModel where
  pH : ℝ → ℝ
  pL : ℝ → ℝ
  dpH : ℝ → ℝ
  dpL : ℝ → ℝ
  g : ℝ → ℝ → ℝ
  ge : ℝ → ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  θL : ℝ
  θH : ℝ
  lam : ℝ
  ubar : ℝ
  c : ℝ

namespace HIModel

/-- **Section 14.C** (MWG, pp. 489-490). The standing assumptions. -/
structure Standing (M : HIModel) : Prop where
  pH_zero : M.pH 0 = 0
  pL_zero : M.pL 0 = 0
  pH_deriv : ∀ e, 0 ≤ e → HasDerivWithinAt M.pH (M.dpH e) (Ici 0) e
  pL_deriv : ∀ e, 0 ≤ e → HasDerivWithinAt M.pL (M.dpL e) (Ici 0) e
  dpL_pos : ∀ e, 0 ≤ e → 0 < M.dpL e
  dp_le : ∀ e, 0 ≤ e → M.dpL e ≤ M.dpH e
  pH_conc : StrictConcaveOn ℝ (Ici 0) M.pH
  pL_conc : StrictConcaveOn ℝ (Ici 0) M.pL
  g_zero : ∀ θ, M.g 0 θ = 0
  g_deriv : ∀ θ e, 0 ≤ e → HasDerivWithinAt (fun e => M.g e θ) (M.ge e θ) (Ici 0) e
  ge_zero : ∀ θ, M.ge 0 θ = 0
  g_conv : ∀ θ, StrictConvexOn ℝ (Ici 0) fun e => M.g e θ
  θ_lt : M.θL < M.θH
  ge_cross : ∀ e, 0 < e → M.ge e M.θH < M.ge e M.θL
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  v_deriv : ∀ w, HasDerivAt M.v (M.dv w) w
  dv_pos : ∀ w, 0 < M.dv w
  v_conc : StrictConcaveOn ℝ univ M.v
  v_c : M.v M.c = M.ubar

/-- The screening program (14.C.8) of the model (with `c = v⁻¹(ū)`). -/
def scr (M : HIModel) : Screen := ⟨M.pH, M.pL, M.g, M.θL, M.θH, M.lam, M.c⟩

/-- `v` is strictly increasing. -/
theorem hi_v_strictMono {M : HIModel} (hM : M.Standing) : StrictMono M.v :=
  strictMono_of_hasDerivAt_pos hM.v_deriv hM.dv_pos

/-- The derivative of `D(e) = g(e, θ_L) - g(e, θ_H)`. -/
theorem hi_D_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.D (M.ge e M.θL - M.ge e M.θH) (Ici 0) e :=
  (hM.g_deriv M.θL e he).sub (hM.g_deriv M.θH e he)

/-- **Single crossing** (MWG, p. 490): the standing assumptions give the hypotheses of the
screening program; in particular `D` is strictly increasing on `[0, ∞)`. -/
theorem hi_hyp {M : HIModel} (hM : M.Standing) : M.scr.Hyp := by
  refine ⟨hM.lam_pos, hM.lam_lt, ?_, ?_⟩
  · change M.g 0 M.θL - M.g 0 M.θH = 0
    rw [hM.g_zero, hM.g_zero, sub_self]
  · refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun e he => (hi_D_deriv hM he).continuousWithinAt) (f' := fun e => M.ge e M.θL - M.ge e M.θH)
      (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Ici] at he ⊢
      exact (hi_D_deriv hM (le_of_lt he)).mono Ioi_subset_Ici_self
    · rw [interior_Ici] at he
      exact sub_pos.2 (hM.ge_cross e he)

/-- The surplus `S_H(e) = π_H(e) - g(e, θ_H)` is strictly concave. -/
theorem hi_SH_conc {M : HIModel} (hM : M.Standing) : StrictConcaveOn ℝ (Ici 0) M.scr.SH :=
  hM.pH_conc.sub (hM.g_conv M.θH)

/-- The surplus `S_L(e) = π_L(e) - g(e, θ_L)` is strictly concave. -/
theorem hi_SL_conc {M : HIModel} (hM : M.Standing) : StrictConcaveOn ℝ (Ici 0) M.scr.SL :=
  hM.pL_conc.sub (hM.g_conv M.θL)

theorem hi_SH_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.SH (M.dpH e - M.ge e M.θH) (Ici 0) e :=
  (hM.pH_deriv e he).sub (hM.g_deriv M.θH e he)

theorem hi_SL_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.SL (M.dpL e - M.ge e M.θL) (Ici 0) e :=
  (hM.pL_deriv e he).sub (hM.g_deriv M.θL e he)

/-- A critical point of a strictly concave function on `[0, ∞)` is its unique maximizer. -/
theorem hi_isFB_of_crit {S : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) S) {e : ℝ} (he : 0 ≤ e)
    (hd : HasDerivWithinAt S 0 (Ici 0) e) : Screen.IsFB S e :=
  ⟨he, fun y hy hne => by
    have := tpa_tangent_lt hc (mem_Ici.2 he) (mem_Ici.2 hy) hne hd
    simpa using this⟩

/-- **(14.C.7)** (MWG, p. 491). If `π'_H(e*) = g_e(e*, θ_H)` then `e* > 0` and `e*` is the unique
maximizer of `π_H(e) - g(e, θ_H)` on `[0, ∞)` (the first-best effort in state `θ_H`). -/
theorem hi_fbH_of_foc {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e)
    (hfoc : M.dpH e = M.ge e M.θH) : 0 < e ∧ Screen.IsFB M.scr.SH e := by
  refine ⟨?_, hi_isFB_of_crit (hi_SH_conc hM) he (by simpa [hfoc] using hi_SH_deriv hM he)⟩
  rcases he.lt_or_eq with h | rfl
  · exact h
  · exfalso
    have := hM.dp_le 0 le_rfl
    have := hM.dpL_pos 0 le_rfl
    rw [hM.ge_zero] at hfoc
    linarith

/-- **(14.C.7)** (MWG, p. 491), state `θ_L`. -/
theorem hi_fbL_of_foc {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e)
    (hfoc : M.dpL e = M.ge e M.θL) : 0 < e ∧ Screen.IsFB M.scr.SL e := by
  refine ⟨?_, hi_isFB_of_crit (hi_SL_conc hM) he (by simpa [hfoc] using hi_SL_deriv hM he)⟩
  rcases he.lt_or_eq with h | rfl
  · exact h
  · exfalso
    have := hM.dpL_pos 0 le_rfl
    rw [hM.ge_zero] at hfoc
    linarith

/-- **`e*_H > e*_L`** (MWG, p. 492): from (14.C.7), `g_eθ < 0`, `π'' < 0`, `g_ee > 0` (and
`π'_H ≥ π'_L` when profits depend on the state, Exercise 14.C.5). -/
theorem hi_fb_order {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    eLs < eHs := by
  have hHpos := (hi_fbH_of_foc hM hH0 hHf).1
  by_contra hle
  rw [not_lt] at hle
  -- π'_L(e*_L) ≤ π'_L(e*_H) ≤ π'_H(e*_H) = g_e(e*_H, θ_H) < g_e(e*_H, θ_L) ≤ g_e(e*_L, θ_L)
  have h1 : M.dpL eLs ≤ M.dpL eHs := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_anti hM.pL_conc (mem_Ici.2 hH0) (mem_Ici.2 hL0) h (hM.pL_deriv _ hH0)
        (hM.pL_deriv _ hL0)).le
    · rw [h]
  have h2 := hM.dp_le eHs hH0
  have h3 := hM.ge_cross eHs hHpos
  have h4 : M.ge eHs M.θL ≤ M.ge eLs M.θL := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_mono (hM.g_conv M.θL) (mem_Ici.2 hH0) (mem_Ici.2 hL0) h
        (hM.g_deriv _ _ hH0) (hM.g_deriv _ _ hL0)).le
    · rw [h]
  linarith

/-- The feasible contracts of (14.C.1) (MWG, p. 490): nonnegative efforts and expected utility at
least `ū`. -/
def ObsFeas (M : HIModel) (K : HIContract) : Prop :=
  0 ≤ K.eH ∧ 0 ≤ K.eL ∧
    M.ubar ≤ M.lam * M.v (K.wH - M.g K.eH M.θH) + (1 - M.lam) * M.v (K.wL - M.g K.eL M.θL)

/-- A solution of (14.C.1). -/
def IsObsOpt (M : HIModel) (K : HIContract) : Prop :=
  M.ObsFeas K ∧ ∀ K', M.ObsFeas K' → M.scr.Pi K' ≤ M.scr.Pi K

/-- The full-information contract: `e*_i` and `w*_i` with `v(w*_i - g(e*_i, θ_i)) = ū`. -/
def fbK (M : HIModel) (eHs eLs : ℝ) : HIContract :=
  ⟨M.c + M.g eHs M.θH, eHs, M.c + M.g eLs M.θL, eLs⟩

/-- **Proposition 14.C.1** (MWG, p. 492). With an observable state, the optimal contract specifies
the efforts `e*_i` with `π'(e*_i) = g_e(e*_i, θ_i)` and fully insures the manager, paying `w*_i`
with `v(w*_i - g(e*_i, θ_i)) = ū`; it is the unique optimal contract. -/
theorem proposition_14_C_1 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    M.IsObsOpt (M.fbK eHs eLs) ∧ ∀ K, M.IsObsOpt K → K = M.fbK eHs eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hl := hM.lam_pos; have hl' := hM.lam_lt
  have hmono := hi_v_strictMono hM
  have hfeas : M.ObsFeas (M.fbK eHs eLs) := by
    refine ⟨hH0, hL0, ?_⟩
    simp only [fbK, add_sub_cancel_right, hM.v_c]; linarith
  have hPifb : M.scr.Pi (M.fbK eHs eLs) = M.lam * M.scr.SH eHs + (1 - M.lam) * M.scr.SL eLs -
      M.c := by
    simp only [Screen.Pi, Screen.SH, Screen.SL, fbK, scr]; ring
  -- the bound for every feasible contract
  have key : ∀ K, M.ObsFeas K → M.c ≤ M.lam * (K.wH - M.g K.eH M.θH) +
      (1 - M.lam) * (K.wL - M.g K.eL M.θL) := by
    intro K hK
    have hJ := tpa_jensen_two hM.v_conc.concaveOn hl.le hl'.le (K.wH - M.g K.eH M.θH)
      (K.wL - M.g K.eL M.θL)
    exact hmono.le_iff_le.1 (by rw [hM.v_c]; linarith [hK.2.2])
  have hPi : ∀ K, M.scr.Pi K = M.lam * M.scr.SH K.eH + (1 - M.lam) * M.scr.SL K.eL -
      (M.lam * (K.wH - M.g K.eH M.θH) + (1 - M.lam) * (K.wL - M.g K.eL M.θL)) := by
    intro K; simp only [Screen.Pi, Screen.SH, Screen.SL, scr]; ring
  have hSHle : ∀ e, 0 ≤ e → M.scr.SH e ≤ M.scr.SH eHs := fun e he => by
    rcases eq_or_ne e eHs with rfl | hne
    · exact le_rfl
    · exact (hH.2 e he hne).le
  have hSLle : ∀ e, 0 ≤ e → M.scr.SL e ≤ M.scr.SL eLs := fun e he => by
    rcases eq_or_ne e eLs with rfl | hne
    · exact le_rfl
    · exact (hL.2 e he hne).le
  have hopt : M.IsObsOpt (M.fbK eHs eLs) := by
    refine ⟨hfeas, fun K hK => ?_⟩
    rw [hPi K, hPifb]
    nlinarith [key K hK, mul_le_mul_of_nonneg_left (hSHle _ hK.1) hl.le,
      mul_le_mul_of_nonneg_left (hSLle _ hK.2.1) (by linarith : (0:ℝ) ≤ 1 - M.lam)]
  refine ⟨hopt, fun K hK => ?_⟩
  have heq : M.scr.Pi K = M.scr.Pi (M.fbK eHs eLs) := le_antisymm (hopt.2 K hK.1) (hK.2 _ hfeas)
  rw [hPi K, hPifb] at heq
  have hk := key K hK.1
  have a1 := mul_le_mul_of_nonneg_left (hSHle _ hK.1.1) hl.le
  have a2 := mul_le_mul_of_nonneg_left (hSLle _ hK.1.2.1) (by linarith : (0:ℝ) ≤ 1 - M.lam)
  have hHe : K.eH = eHs := by
    by_contra hne
    have := mul_lt_mul_of_pos_left (hH.2 _ hK.1.1 hne) hl
    linarith
  have hLe : K.eL = eLs := by
    by_contra hne
    have := mul_lt_mul_of_pos_left (hL.2 _ hK.1.2.1 hne) (by linarith : (0:ℝ) < 1 - M.lam)
    linarith
  have hsum : M.lam * (K.wH - M.g K.eH M.θH) + (1 - M.lam) * (K.wL - M.g K.eL M.θL) = M.c := by
    linarith
  have hxeq : K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θL := by
    by_contra hne
    have hJ := tpa_jensen_two_lt hM.v_conc hl hl' hne
    rw [hsum, hM.v_c] at hJ
    linarith [hK.1.2.2]
  have hx : K.wL - M.g K.eL M.θL = M.c := by
    rw [hxeq] at hsum; linarith
  obtain ⟨wH, eH, wL, eL⟩ := K
  simp only at hHe hLe hx hxeq
  subst hHe hLe
  have e1 : wH = M.c + M.g eH M.θH := by linarith
  have e2 : wL = M.c + M.g eL M.θL := by linarith
  simp only [fbK, e1, e2]

/-- **(14.C.2)-(14.C.6)** (MWG, pp. 490-491). At the full-information contract the first-order
conditions hold with the multiplier `γ = 1 / v'(v⁻¹(ū))`: marginal utilities of income are equal
across states (14.C.6) and the effort conditions hold with equality. -/
theorem hi_obs_foc {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ}
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    let K := M.fbK eHs eLs
    let γ := 1 / M.dv M.c
    (-M.lam + γ * M.lam * M.dv (K.wH - M.g K.eH M.θH) = 0 ∧
    -(1 - M.lam) + γ * (1 - M.lam) * M.dv (K.wL - M.g K.eL M.θL) = 0 ∧
    M.lam * M.dpH K.eH - γ * M.lam * M.dv (K.wH - M.g K.eH M.θH) * M.ge K.eH M.θH = 0 ∧
    (1 - M.lam) * M.dpL K.eL - γ * (1 - M.lam) * M.dv (K.wL - M.g K.eL M.θL) *
      M.ge K.eL M.θL = 0 ∧
    M.dv (K.wH - M.g K.eH M.θH) = M.dv (K.wL - M.g K.eL M.θL)) := by
  intro K γ
  have hd := (hM.dv_pos M.c).ne'
  simp only [K, γ, fbK, add_sub_cancel_right]
  refine ⟨by field_simp; ring, by field_simp; ring, ?_, ?_, trivial⟩
  · rw [hHf]; field_simp; ring
  · rw [hLf]; field_simp; ring

/-- The isoprofit curve `π(e) - w = Π` meets the vertical axis `e = 0` at `w = -Π`, since
`π(0) = 0` (MWG, pp. 491-492, Figure 14.C.1). -/
theorem hi_isoprofit_axis {M : HIModel} (hM : M.Standing) (P0 w : ℝ) :
    M.pH 0 - w = P0 ↔ w = -P0 := by
  rw [hM.pH_zero]; constructor <;> intro h <;> linarith

/-- **p. 492**: facing the full-information contract, the manager in state `θ_H` strictly prefers
the `θ_L` pair, and the misrepresentation lowers the owner's profit in that state. -/
theorem hi_H_prefers_L {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    (hπ : M.pH = M.pL) :
    let K := M.fbK eHs eLs
    K.wH - M.g K.eH M.θH < K.wL - M.g K.eL M.θH ∧ M.pH K.eL - K.wL < M.pH K.eH - K.wH := by
  intro K
  have hLpos := (hi_fbL_of_foc hM hL0 hLf).1
  have hD := Screen.screen_D_pos (hi_hyp hM) hLpos
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hne : eLs ≠ eHs := (hi_fb_order hM hH0 hHf hL0 hLf).ne
  have hS := hH.2 eLs hL0 hne
  simp only [K, fbK]
  change 0 < M.g eLs M.θL - M.g eLs M.θH at hD
  change M.pH eLs - M.g eLs M.θH < M.pH eHs - M.g eHs M.θH at hS
  constructor
  · linarith
  · rw [hπ] at hS ⊢; linarith

/-- The derivative of the virtual surplus `Q(e) = (1 - λ) S_L(e) - λ D(e)`. -/
theorem hi_Q_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.Q ((1 - M.lam) * (M.dpL e - M.ge e M.θL) -
      M.lam * (M.ge e M.θL - M.ge e M.θH)) (Ici 0) e :=
  ((hi_SL_deriv hM he).const_mul (1 - M.lam)).sub ((hi_D_deriv hM he).const_mul M.lam)

/-- **Appendix B, Step 3** (MWG, p. 505). At an optimal contract `e_L > 0`. -/
theorem hi_eL_pos {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) : 0 < K.eL := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  obtain ⟨h0, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL hord K).1 hK
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  have hd := hi_Q_deriv hM (le_refl (0 : ℝ))
  rw [hM.ge_zero, hM.ge_zero] at hd
  simp only [sub_zero, mul_zero] at hd
  have hpos : 0 < (1 - M.lam) * M.dpL 0 :=
    mul_pos (by linarith [hM.lam_lt]) (hM.dpL_pos 0 le_rfl)
  obtain ⟨y, hy, hgt⟩ := hi_exists_gt_of_deriv_pos hd hpos
  have := hmax y hy.le
  rw [← h] at this
  linarith

/-- An interior maximizer of `Q` on `[0, ∞)` is a critical point. -/
theorem hi_Q_crit {M : HIModel} (hM : M.Standing) {e : ℝ} (hpos : 0 < e)
    (hmax : ∀ e', 0 ≤ e' → M.scr.Q e' ≤ M.scr.Q e) :
    (1 - M.lam) * (M.dpL e - M.ge e M.θL) - M.lam * (M.ge e M.θL - M.ge e M.θH) = 0 := by
  have hd := (hi_Q_deriv hM hpos.le).hasDerivAt (Ici_mem_nhds hpos)
  have hloc : IsLocalMax M.scr.Q e :=
    Filter.mem_of_superset (Ici_mem_nhds hpos) fun y hy => hmax y hy
  exact hloc.hasDerivAt_eq_zero hd

/-- **(14.C.9) = (14.BB.7) and (14.BB.6)** (MWG, pp. 499, 506). At an optimal contract
`π'_H(e_H) = g_e(e_H, θ_H)` and
`[π'(e_L) - g_e(e_L, θ_L)] + λ/(1 - λ) [g_e(e_L, θ_H) - g_e(e_L, θ_L)] = 0`. -/
theorem hi_foc_14_C_9 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    M.dpH K.eH - M.ge K.eH M.θH = 0 ∧
      (M.dpL K.eL - M.ge K.eL M.θL) + M.lam / (1 - M.lam) * (M.ge K.eL M.θH - M.ge K.eL M.θL) =
        0 := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  obtain ⟨-, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL hord K).1 hK
  have hHe := (Screen.lemma_14_C_3 (hi_hyp hM) hH hL hord hK).2
  have hc := hi_Q_crit hM (hi_eL_pos hM hH0 hHf hL0 hLf hK) hmax
  have hl : (0:ℝ) < 1 - M.lam := by linarith [hM.lam_lt]
  refine ⟨by rw [hHe, hHf]; ring, ?_⟩
  field_simp
  linarith

/-- **Lemma 14.C.4** (MWG, p. 497). In any optimal contract `e_L < e*_L`. -/
theorem lemma_14_C_4 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) : K.eL < eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf)
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  have hle := (Screen.lemma_14_C_3 (hi_hyp hM) hH hL.2 hord hK).1
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨-, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL.2 hord K).1 hK
  have hc := hi_Q_crit hM (h ▸ hL.1) hmax
  rw [h, hLf, sub_self, mul_zero, zero_sub, neg_eq_zero] at hc
  have := mul_pos hM.lam_pos (sub_pos.2 (hM.ge_cross eLs hL.1))
  linarith

/-- **(14.C.9), the two terms** (MWG, p. 499): `π'(e) - g_e(e, θ_L)` is zero at `e*_L` and strictly
positive for `0 ≤ e < e*_L`; `g_e(e, θ_H) - g_e(e, θ_L)` is strictly negative for `e > 0`. -/
theorem hi_14_C_9_terms {M : HIModel} (hM : M.Standing) {eLs : ℝ} (hL0 : 0 ≤ eLs)
    (hLf : M.dpL eLs = M.ge eLs M.θL) :
    M.dpL eLs - M.ge eLs M.θL = 0 ∧
    (∀ e, 0 ≤ e → e < eLs → 0 < M.dpL e - M.ge e M.θL) ∧
    ∀ e, 0 < e → M.ge e M.θH - M.ge e M.θL < 0 := by
  refine ⟨by rw [hLf, sub_self], fun e he hlt => ?_, fun e he => sub_neg.2 (hM.ge_cross e he)⟩
  have := hi_deriv_anti (hi_SL_conc hM) (mem_Ici.2 he) (mem_Ici.2 hL0) hlt (hi_SL_deriv hM he)
    (hi_SL_deriv hM hL0)
  rw [hLf, sub_self] at this
  exact this

/-- **Proposition 14.C.3** (MWG, p. 499). With an infinitely risk-averse manager the optimal
contract sets `e_H = e*_H`, distorts `e_L` strictly below `e*_L` (with `e_L > 0`), gives the manager
exactly `ū` in state `θ_L` and strictly more than `ū` in state `θ_H`, and gives the owner a strictly
lower expected payoff than when `θ` is observable. -/
theorem proposition_14_C_3 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    K.eH = eHs ∧ 0 < K.eL ∧ K.eL < eLs ∧ M.v (K.wL - M.g K.eL M.θL) = M.ubar ∧
      M.ubar < M.v (K.wH - M.g K.eH M.θH) ∧ M.scr.Pi K < M.scr.FBval eHs eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  have hpos := hi_eL_pos hM hH0 hHf hL0 hLf hK
  obtain ⟨hU1, -, hU3⟩ := Screen.screen_H_rent (hi_hyp hM) hK
  refine ⟨(Screen.lemma_14_C_3 (hi_hyp hM) hH hL hord hK).2, hpos,
    lemma_14_C_4 hM hH0 hHf hL0 hLf hK, ?_, ?_, Screen.screen_loss (hi_hyp hM) hH hL hord hK hpos⟩
  · have : K.wL - M.g K.eL M.θL = M.c := hU1
    rw [this, hM.v_c]
  · rw [← hM.v_c]; exact hi_v_strictMono hM (hU3 hpos)

/-- **p. 499**: the optimal `e_L` falls as `λ / (1 - λ)` rises. If `e₁ > 0` maximizes the virtual
surplus for `λ₁` and `e₂ > 0` for `λ₂ > λ₁` (both in `(0, 1)`), then `e₂ < e₁`. -/
theorem hi_eL_falls {M : HIModel} (hM : M.Standing) {l1 l2 e1 e2 : ℝ} (hl1 : 0 < l1)
    (hl12 : l1 < l2) (hl2 : l2 < 1) (he1 : 0 < e1) (he2 : 0 < e2)
    (hm1 : ∀ e, 0 ≤ e → (1 - l1) * M.scr.SL e - l1 * M.scr.D e ≤
      (1 - l1) * M.scr.SL e1 - l1 * M.scr.D e1)
    (hm2 : ∀ e, 0 ≤ e → (1 - l2) * M.scr.SL e - l2 * M.scr.D e ≤
      (1 - l2) * M.scr.SL e2 - l2 * M.scr.D e2) : e2 < e1 := by
  have hyp := hi_hyp hM
  -- weak monotonicity from revealed preference
  have a := hm1 e2 he2.le
  have b := hm2 e1 he1.le
  have hle : e2 ≤ e1 := by
    by_contra hc
    rw [not_le] at hc
    have hD := hyp.D_mono he1.le he2.le hc
    -- divide by (1 - l): S_L - k D with k = l/(1-l); compare via cross-multiplication
    have h1 : (1 - l2) * ((1 - l1) * M.scr.SL e2 - l1 * M.scr.D e2) ≤
        (1 - l2) * ((1 - l1) * M.scr.SL e1 - l1 * M.scr.D e1) :=
      mul_le_mul_of_nonneg_left a (by linarith)
    have h2 : (1 - l1) * ((1 - l2) * M.scr.SL e1 - l2 * M.scr.D e1) ≤
        (1 - l1) * ((1 - l2) * M.scr.SL e2 - l2 * M.scr.D e2) :=
      mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  subst h
  -- both critical points coincide: contradiction with g_e(e, θ_H) < g_e(e, θ_L)
  have hd1 := ((hi_SL_deriv hM he2.le).const_mul (1 - l1)).sub ((hi_D_deriv hM he2.le).const_mul l1)
  have hd2 := ((hi_SL_deriv hM he2.le).const_mul (1 - l2)).sub ((hi_D_deriv hM he2.le).const_mul l2)
  have c1 := IsLocalMax.hasDerivAt_eq_zero
    (Filter.mem_of_superset (Ici_mem_nhds he2) fun y hy => hm1 y hy)
    (hd1.hasDerivAt (Ici_mem_nhds he2))
  have c2 := IsLocalMax.hasDerivAt_eq_zero
    (Filter.mem_of_superset (Ici_mem_nhds he2) fun y hy => hm2 y hy)
    (hd2.hasDerivAt (Ici_mem_nhds he2))
  have hx := sub_pos.2 (hM.ge_cross e2 he2)
  have : (l2 - l1) * ((M.dpL e2 - M.ge e2 M.θL) + (M.ge e2 M.θL - M.ge e2 M.θH)) = 0 := by
    linarith
  have hS : M.dpL e2 - M.ge e2 M.θL + (M.ge e2 M.θL - M.ge e2 M.θH) = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have : (1 - l1) * (M.dpL e2 - M.ge e2 M.θL) = l1 * (M.ge e2 M.θL - M.ge e2 M.θH) := by
    linarith
  nlinarith

/-- **Footnote 17** (MWG, p. 499). In a variant of the model where `g_e(0, θ)` may be positive
(with `g_e(0, θ_H) ≥ 0`), `e_L = 0` maximizes the virtual surplus only if `g_e(0, θ_L) > 0`. -/
theorem footnote_17 {Q dpL : ℝ → ℝ} {ge : ℝ → ℝ → ℝ} {lam θL θH : ℝ} (hl : lam < 1)
    (hd : HasDerivWithinAt Q ((1 - lam) * (dpL 0 - ge 0 θL) - lam * (ge 0 θL - ge 0 θH))
      (Ici 0) 0)
    (hdp : 0 < dpL 0) (hH : 0 ≤ ge 0 θH) (hl0 : 0 ≤ lam) (hmax : ∀ e, 0 ≤ e → Q e ≤ Q 0) :
    0 < ge 0 θL := by
  by_contra hc
  rw [not_lt] at hc
  have hpos : 0 < (1 - lam) * (dpL 0 - ge 0 θL) - lam * (ge 0 θL - ge 0 θH) := by
    have : 0 < (1 - lam) * (dpL 0 - ge 0 θL) := mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨y, hy, hgt⟩ := hi_exists_gt_of_deriv_pos hd hpos
  linarith [hmax y hy.le]

/-- **Appendix B, (14.BB.2)-(14.BB.5) and Steps 1-5** (MWG, pp. 505-506). If `K` is feasible and the
Kuhn-Tucker conditions hold with multipliers `(γ, φ_H, φ_L) ≥ 0` and complementary slackness, then
`φ_H > 0` and (iii) binds (Step 1), `γ = 1` and (i) binds (Step 2), `e_L, e_H > 0` (Step 3),
`φ_L = 0` (Step 4), and (14.BB.6)-(14.BB.7) hold (Step 5). -/
theorem appendix_B_steps {M : HIModel} (hM : M.Standing) {K : HIContract} (hK : M.scr.Feas K)
    {γ φH φL : ℝ} (hφL : 0 ≤ φL)
    (h2 : -M.lam + φH - φL = 0) (h3 : -(1 - M.lam) + γ - φH + φL = 0)
    (h4 : M.lam * M.dpH K.eH - φH * M.ge K.eH M.θH + φL * M.ge K.eH M.θL ≤ 0)
    (h4' : 0 < K.eH → M.lam * M.dpH K.eH - φH * M.ge K.eH M.θH + φL * M.ge K.eH M.θL = 0)
    (h5 : (1 - M.lam) * M.dpL K.eL - (γ + φL) * M.ge K.eL M.θL + φH * M.ge K.eL M.θH ≤ 0)
    (h5' : 0 < K.eL →
      (1 - M.lam) * M.dpL K.eL - (γ + φL) * M.ge K.eL M.θL + φH * M.ge K.eL M.θH = 0)
    (cs1 : γ * (K.wL - M.g K.eL M.θL - M.c) = 0)
    (cs3 : φH * (K.wH - M.g K.eH M.θH - (K.wL - M.g K.eL M.θH)) = 0)
    (cs4 : φL * (K.wL - M.g K.eL M.θL - (K.wH - M.g K.eH M.θL)) = 0) :
    0 < φH ∧ K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θH ∧ γ = 1 ∧
      K.wL - M.g K.eL M.θL = M.c ∧ 0 < K.eL ∧ 0 < K.eH ∧ φL = 0 ∧ φH = M.lam ∧
      M.dpH K.eH - M.ge K.eH M.θH = 0 ∧
      (M.dpL K.eL - M.ge K.eL M.θL) + M.lam / (1 - M.lam) * (M.ge K.eL M.θH - M.ge K.eL M.θL) =
        0 := by
  have hl := hM.lam_pos; have hl' := hM.lam_lt
  -- Step 1
  have hφHpos : 0 < φH := by linarith
  have hiii : K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θH := by
    rcases mul_eq_zero.1 cs3 with h | h
    · linarith
    · linarith
  -- Step 2
  have hγ1 : γ = 1 := by linarith
  have hi : K.wL - M.g K.eL M.θL = M.c := by
    rw [hγ1] at cs1; linarith
  -- Step 3
  have hpos : ∀ e : ℝ, 0 ≤ e → ¬ 0 < e → e = 0 := fun e he hne => le_antisymm (not_lt.1 hne) he
  have heL : 0 < K.eL := by
    by_contra hc
    have h0 := hpos _ hK.2.1 hc
    rw [h0, hM.ge_zero, hM.ge_zero] at h5
    have := hM.dpL_pos 0 le_rfl
    nlinarith
  have heH : 0 < K.eH := by
    by_contra hc
    have h0 := hpos _ hK.1 hc
    rw [h0, hM.ge_zero, hM.ge_zero] at h4
    have := hM.dp_le 0 le_rfl
    have := hM.dpL_pos 0 le_rfl
    nlinarith
  have e4 := h4' heH
  have e5 := h5' heL
  -- Step 4
  have hφL : φL = 0 := by
    by_contra hne
    have hφLpos : 0 < φL := lt_of_le_of_ne hφL (Ne.symm hne)
    have hφHv : φH = φL + M.lam := by linarith
    rw [hφHv] at e4 e5
    rw [hγ1] at e5
    have a4 : M.lam * (M.dpH K.eH - M.ge K.eH M.θH) +
        φL * (M.ge K.eH M.θL - M.ge K.eH M.θH) = 0 := by linarith
    have a5 : (1 - M.lam) * (M.dpL K.eL - M.ge K.eL M.θH) +
        (1 + φL) * (M.ge K.eL M.θH - M.ge K.eL M.θL) = 0 := by linarith
    -- (iv) binds since φL > 0
    have hiv : K.wL - M.g K.eL M.θL = K.wH - M.g K.eH M.θL := by
      rcases mul_eq_zero.1 cs4 with h | h
      · exact absurd h hne
      · linarith
    -- then D(e_H) = D(e_L), so e_H = e_L
    have hDeq : M.scr.D K.eH = M.scr.D K.eL := by
      change M.g K.eH M.θL - M.g K.eH M.θH = M.g K.eL M.θL - M.g K.eL M.θH; linarith
    have heq : K.eH = K.eL := (hi_hyp hM).D_mono.injOn hK.1 hK.2.1 hDeq
    have hcH := hM.ge_cross K.eH heH
    -- with e_H = e_L =: e, (14.BB.4) and (14.BB.5) are incompatible
    rw [heq] at a4 hcH
    have hp := hM.dp_le K.eL heL.le
    have hlpos : 0 < M.ge K.eL M.θL - M.ge K.eL M.θH := by linarith
    -- a4: λ (π'_H - g_eH) = -φL (g_eL - g_eH) < 0; a5: (1 - λ)(π'_L - g_eH) > 0
    have b4 : M.dpH K.eL - M.ge K.eL M.θH < 0 := by nlinarith
    have b5 : 0 < M.dpL K.eL - M.ge K.eL M.θH := by nlinarith
    linarith
  -- Step 5
  have hφHl : φH = M.lam := by linarith
  rw [hφL, hφHl] at e4 e5
  rw [hγ1] at e5
  refine ⟨hφHpos, hiii, hγ1, hi, heL, heH, hφL, hφHl, ?_, ?_⟩
  · have : M.lam * (M.dpH K.eH - M.ge K.eH M.θH) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · have hl1 : (0:ℝ) < 1 - M.lam := by linarith
    field_simp
    linarith

/-- **Appendix B** (MWG, p. 505): at every optimal contract the Kuhn-Tucker conditions
(14.BB.2)-(14.BB.5) hold, with multipliers `γ = 1`, `φ_H = λ`, `φ_L = 0`. -/
theorem appendix_B_multipliers {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    -M.lam + M.lam - 0 = 0 ∧ -(1 - M.lam) + 1 - M.lam + 0 = 0 ∧
    M.lam * M.dpH K.eH - M.lam * M.ge K.eH M.θH + 0 * M.ge K.eH M.θL = 0 ∧
    (1 - M.lam) * M.dpL K.eL - (1 + 0) * M.ge K.eL M.θL + M.lam * M.ge K.eL M.θH = 0 ∧
    1 * (K.wL - M.g K.eL M.θL - M.c) = 0 ∧
    M.lam * (K.wH - M.g K.eH M.θH - (K.wL - M.g K.eL M.θH)) = 0 := by
  obtain ⟨hf1, hf2⟩ := hi_foc_14_C_9 hM hH0 hHf hL0 hLf hK
  obtain ⟨hwL, hwH⟩ := Screen.lemma_14_C_2 (hi_hyp hM) hK
  have hl1 : (0:ℝ) < 1 - M.lam := by linarith [hM.lam_lt]
  refine ⟨by ring, by ring, by linear_combination M.lam * hf1, ?_, ?_, ?_⟩
  · field_simp at hf2; linear_combination hf2
  · have e1 : K.wL = M.c + M.g K.eL M.θL := hwL
    rw [e1]; ring
  · have e1 : K.wL = M.c + M.g K.eL M.θL := hwL
    have e2 : K.wH = M.c + (M.g K.eL M.θL - M.g K.eL M.θH) + M.g K.eH M.θH := hwH
    rw [e1, e2]; ring

end HIModel

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A concrete hidden-information model

MWG, Section 14.C, pp. 489-499: a proved instance of the standing assumptions of `HiddenInfo`
in which the optimal contract of (14.C.8) exists and is computed.

`π(e) = log (1 + e)`, `g(e, θ) = e² exp(-θ) / 2`, `θ_L = log 2`, `θ_H = log 6`, `λ = 5/7`,
`v(w) = -exp(-w)`, `ū = -1` (so `v⁻¹(ū) = 0`). Then `e*_L = 1`, `e*_H = 2` (14.C.7), and the
optimal contract under hidden information has `e_H = 2`, `e_L = 1/2`, `w_L = 1/16`,
`w_H = 1/24 + 1/3 = 3/8` (Proposition 14.C.3).

* `exB_standing`: the standing assumptions hold.
* `exB_opt`: the optimal contract; `exB_proposition_14_C_3`, `exB_proposition_14_C_1`: instances.
-/

namespace MWG.PrincipalAgent

open Set

/-- `g(e, θ) = e² exp(-θ) / 2` is strictly convex in `e ≥ 0`. -/
theorem exB_g_conv (θ : ℝ) : StrictConvexOn ℝ (Ici 0) fun e : ℝ => e ^ 2 * Real.exp (-θ) / 2 := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hk := Real.exp_pos (-θ)
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hd : 0 < (x - y) ^ 2 := by positivity
  simp only [smul_eq_mul]
  have : (a * x + (1 - a) * y) ^ 2 < a * x ^ 2 + (1 - a) * y ^ 2 := by
    nlinarith [mul_pos (mul_pos ha hb) hd]
  have := mul_lt_mul_of_pos_right this hk
  nlinarith

/-- `log (1 + e)` has derivative `1 / (1 + e)` for `e > -1`. -/
theorem exB_log_deriv {e : ℝ} (he : 0 ≤ e) :
    HasDerivAt (fun e : ℝ => Real.log (1 + e)) (1 / (1 + e)) e := by
  have := ((hasDerivAt_id e).const_add 1).log (by simp; linarith)
  simpa using this

/-- `log (1 + e)` is strictly concave on `[0, ∞)`. -/
theorem exB_log_conc : StrictConcaveOn ℝ (Ici 0) fun e : ℝ => Real.log (1 + e) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) ?_ ?_
  · intro e he
    exact (exB_log_deriv (mem_Ici.1 he)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(exB_log_deriv (le_of_lt hx)).deriv, (exB_log_deriv (le_of_lt hy)).deriv]
    have hx' : (0:ℝ) < 1 + x := by linarith [mem_Ioi.1 hx]
    exact one_div_lt_one_div_of_lt hx' (by linarith)

/-- The concrete hidden-information model. -/
noncomputable def exB : HIModel where
  pH := fun e => Real.log (1 + e)
  pL := fun e => Real.log (1 + e)
  dpH := fun e => 1 / (1 + e)
  dpL := fun e => 1 / (1 + e)
  g := fun e θ => e ^ 2 * Real.exp (-θ) / 2
  ge := fun e θ => e * Real.exp (-θ)
  v := fun w => -Real.exp (-w)
  dv := fun w => Real.exp (-w)
  θL := Real.log 2
  θH := Real.log 6
  lam := 5 / 7
  ubar := -1
  c := 0

theorem exB_expL : Real.exp (-exB.θL) = 1 / 2 := by
  change Real.exp (-Real.log 2) = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem exB_expH : Real.exp (-exB.θH) = 1 / 6 := by
  change Real.exp (-Real.log 6) = 1 / 6
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- The standing assumptions of Section 14.C hold in `exB`. -/
theorem exB_standing : exB.Standing where
  pH_zero := by simp [exB]
  pL_zero := by simp [exB]
  pH_deriv e he := (exB_log_deriv he).hasDerivWithinAt
  pL_deriv e he := (exB_log_deriv he).hasDerivWithinAt
  dpL_pos e he := by change 0 < 1 / (1 + e); positivity
  dp_le _ _ := le_rfl
  pH_conc := exB_log_conc
  pL_conc := exB_log_conc
  g_zero θ := by simp [exB]
  g_deriv θ e _ := by
    have := ((hasDerivAt_pow 2 e).mul_const (Real.exp (-θ))).div_const 2
    refine HasDerivWithinAt.congr_deriv this.hasDerivWithinAt ?_
    change _ = e * Real.exp (-θ)
    push_cast; ring
  ge_zero θ := by simp [exB]
  g_conv θ := exB_g_conv θ
  θ_lt := Real.log_lt_log (by norm_num) (by norm_num)
  ge_cross e he := by
    change e * Real.exp (-exB.θH) < e * Real.exp (-exB.θL)
    rw [exB_expL, exB_expH]; linarith
  lam_pos := by norm_num [exB]
  lam_lt := by norm_num [exB]
  v_deriv := exA_hasDeriv
  dv_pos _ := Real.exp_pos _
  v_conc := exA_strictConcave
  v_c := by simp [exB]

theorem exB_focH : exB.dpH 2 = exB.ge 2 exB.θH := by
  change 1 / (1 + 2 : ℝ) = 2 * Real.exp (-exB.θH)
  rw [exB_expH]; norm_num

theorem exB_focL : exB.dpL 1 = exB.ge 1 exB.θL := by
  change 1 / (1 + 1 : ℝ) = 1 * Real.exp (-exB.θL)
  rw [exB_expL]; norm_num

/-- The virtual surplus of `exB`: `Q(e) = (2/7) log (1 + e) - 4 e² / 21`. -/
theorem exB_Q (e : ℝ) : exB.scr.Q e = 2 / 7 * Real.log (1 + e) - 4 * e ^ 2 / 21 := by
  change (1 - 5 / 7) * (Real.log (1 + e) - e ^ 2 * Real.exp (-exB.θL) / 2) -
    5 / 7 * (e ^ 2 * Real.exp (-exB.θL) / 2 - e ^ 2 * Real.exp (-exB.θH) / 2) = _
  rw [exB_expL, exB_expH]; ring

/-- `e = 1/2` maximizes the virtual surplus of `exB` on `[0, ∞)`. -/
theorem exB_Q_max (e : ℝ) (he : 0 ≤ e) : exB.scr.Q e ≤ exB.scr.Q (1 / 2) := by
  rw [exB_Q, exB_Q]
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [this]
  nlinarith [sq_nonneg (2 * e - 1)]

/-- **The optimal contract of (14.C.8) in `exB`**: `e_H = e*_H = 2`, `e_L = 1/2`, with (i) and
(iii) binding. -/
theorem exB_opt : exB.scr.IsOpt (exB.scr.bind 2 (1 / 2)) := by
  have hH := (HIModel.hi_fbH_of_foc exB_standing (by norm_num) exB_focH).2
  have hL := (HIModel.hi_fbL_of_foc exB_standing (by norm_num) exB_focL).2
  refine (Screen.screen_opt_iff (HIModel.hi_hyp exB_standing) hH hL (by norm_num) _).2
    ⟨by change (0:ℝ) ≤ 1 / 2; norm_num, fun e he => exB_Q_max e he, rfl⟩

/-- An instance of **Proposition 14.C.3** (MWG, p. 499) in `exB`. -/
theorem exB_proposition_14_C_3 :
    (exB.scr.bind 2 (1 / 2)).eH = 2 ∧ 0 < (exB.scr.bind 2 (1 / 2)).eL ∧
      (exB.scr.bind 2 (1 / 2)).eL < 1 ∧
      exB.scr.Pi (exB.scr.bind 2 (1 / 2)) < exB.scr.FBval 2 1 := by
  obtain ⟨h1, h2, h3, -, -, h6⟩ := HIModel.proposition_14_C_3 exB_standing (by norm_num)
    exB_focH (by norm_num) exB_focL exB_opt
  exact ⟨h1, h2, h3, h6⟩

/-- An instance of **Proposition 14.C.1** (MWG, p. 492) in `exB`. -/
theorem exB_proposition_14_C_1 : exB.IsObsOpt (exB.fbK 2 1) :=
  (HIModel.proposition_14_C_1 exB_standing (by norm_num) exB_focH (by norm_num) exB_focL).1

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Infinite risk aversion

MWG, Section 14.C, p. 494 and footnote 15.

The manager's Bernoulli utility `u_ρ(v) = -v^ρ` (`ρ < 0`) applied to the utility levels
`v_H, v_L > 0` of the two states gives expected utility `EU = -[λ v_H^ρ + (1 - λ) v_L^ρ]`, ordered
by the certainty equivalent `(-EU)^{1/ρ}`; as `ρ → -∞` this tends to `min {v_H, v_L}`. The limit is
MWG's Exercise 3.C.6(c), imported from Chapter 3 (`MWG.ClassicalDemand.exercise_3_C_6c`).

* `footnote_15_order`: for `ρ < 0`, `(-EU)^{1/ρ}` orders contracts as `EU` does.
* `footnote_15`: `(λ v_H^ρ + (1 - λ) v_L^ρ)^{1/ρ} → min {v_H, v_L}` as `ρ → -∞`.
* `footnote_15_accept`, `footnote_15_reject`: a contract is accepted by the manager with the
  certain reservation utility `ū` for every `ρ < 0` if `min {v_H, v_L} ≥ ū`, and rejected for all
  sufficiently negative `ρ` if `min {v_H, v_L} < ū`.
* `infinite_ra_insure`: with an infinitely risk-averse manager, lowering the better state's
  utility to the worse one's keeps him equally well off and lowers the wage bill (p. 494).
-/

namespace MWG.PrincipalAgent

open Filter Topology

/-- The certainty equivalent `(λ v_H^ρ + (1 - λ) v_L^ρ)^{1/ρ}` of footnote 15. -/
noncomputable def ceRho (lam vH vL ρ : ℝ) : ℝ := (lam * vH ^ ρ + (1 - lam) * vL ^ ρ) ^ (1 / ρ)

/-- **Footnote 15** (MWG, p. 494): for `ρ < 0` the expected utility `-(λ v_H^ρ + (1 - λ) v_L^ρ)`
is ordered correctly by `(-EU)^{1/ρ}`. -/
theorem footnote_15_order {ρ X Y : ℝ} (hρ : ρ < 0) (hX : 0 < X) (hY : 0 < Y) :
    -X < -Y ↔ X ^ (1 / ρ) < Y ^ (1 / ρ) := by
  have hr : 1 / ρ < 0 := one_div_neg.2 hρ
  constructor
  · intro h; exact Real.rpow_lt_rpow_of_neg hY (by linarith) hr
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · have := Real.rpow_lt_rpow_of_neg hX (by linarith : X < Y) hr; linarith
    · have : X = Y := by linarith
      rw [this] at h; exact lt_irrefl _ h

/-- **Footnote 15** (MWG, p. 494, via Exercise 3.C.6): as `ρ → -∞` the certainty equivalent tends
to `min {v_H, v_L}`. -/
theorem footnote_15 {lam vH vL : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hH : 0 < vH) (hL : 0 < vL) :
    Tendsto (ceRho lam vH vL) atBot (𝓝 (min vH vL)) :=
  MWG.ClassicalDemand.exercise_3_C_6c hl0 (by linarith) hH hL

/-- The certainty equivalent is at least `min {v_H, v_L}` for every `ρ < 0`. -/
theorem ceRho_ge_min {lam vH vL ρ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hH : 0 < vH)
    (hL : 0 < vL) (hρ : ρ < 0) : min vH vL ≤ ceRho lam vH vL ρ := by
  set m := min vH vL
  have hm : 0 < m := lt_min hH hL
  have hHm : vH ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm (min_le_left _ _) hρ.le
  have hLm : vL ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm (min_le_right _ _) hρ.le
  have hS : lam * vH ^ ρ + (1 - lam) * vL ^ ρ ≤ m ^ ρ := by
    nlinarith [mul_le_mul_of_nonneg_left hHm hl0,
      mul_le_mul_of_nonneg_left hLm (by linarith : (0:ℝ) ≤ 1 - lam)]
  have hSpos : 0 < lam * vH ^ ρ + (1 - lam) * vL ^ ρ := by
    rcases hl0.lt_or_eq with h | h
    · have := Real.rpow_pos_of_pos hH ρ
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (Real.rpow_pos_of_pos hL ρ).le
      nlinarith
    · rw [← h]; simp only [zero_mul, zero_add, sub_zero, one_mul]
      exact Real.rpow_pos_of_pos hL ρ
  have := Real.rpow_le_rpow_of_nonpos hSpos hS (one_div_neg.2 hρ).le
  rw [← Real.rpow_mul hm.le, mul_one_div_cancel hρ.ne, Real.rpow_one] at this
  exact this

/-- **Footnote 15**: if `min {v_H, v_L} ≥ ū > 0`, the contract gives the manager an expected utility
at least that of his certain reservation utility `ū`, for every `ρ < 0`. -/
theorem footnote_15_accept {lam vH vL u ρ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hu : 0 < u)
    (hρ : ρ < 0) (hmin : u ≤ min vH vL) :
    -(u ^ ρ) ≤ -(lam * vH ^ ρ + (1 - lam) * vL ^ ρ) := by
  have h1 := Real.rpow_le_rpow_of_nonpos hu (hmin.trans (min_le_left _ _)) hρ.le
  have h2 := Real.rpow_le_rpow_of_nonpos hu (hmin.trans (min_le_right _ _)) hρ.le
  nlinarith [mul_le_mul_of_nonneg_left h1 hl0,
    mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Footnote 15**: if `min {v_H, v_L} < ū`, then for all sufficiently negative `ρ` the certainty
equivalent is below `ū` (the contract is rejected). -/
theorem footnote_15_reject {lam vH vL u : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hH : 0 < vH)
    (hL : 0 < vL) (hmin : min vH vL < u) : ∀ᶠ ρ in atBot, ceRho lam vH vL ρ < u :=
  (footnote_15 hl0 hl1 hH hL).eventually (gt_mem_nhds hmin)

/-- **p. 494**: for an infinitely risk-averse manager, whose utility is the lower of his two
state utilities `min {x_H, x_L}`, paying the minimum in both states leaves him as well off and
lowers the expected wage payment. -/
theorem infinite_ra_insure {lam xH xL : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    min (min xH xL) (min xH xL) = min xH xL ∧
      lam * min xH xL + (1 - lam) * min xH xL ≤ lam * xH + (1 - lam) * xL := by
  refine ⟨min_self _, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left xH xL) hl0,
    mul_le_mul_of_nonneg_left (min_le_right xH xL) (by linarith : (0:ℝ) ≤ 1 - lam)]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The revelation principle and hybrid models

MWG, Section 14.C, pp. 492-494 (Proposition 14.C.2), and Section 14.D, pp. 500-502.

* `proposition_14_C_2`: the revelation principle. For any contract (a set of messages or choices
  `Msg` for the manager and an outcome for each) and any optimal behaviour of the manager, the
  direct mechanism that assigns to each announced state the outcome the manager would have chosen
  in that state is truthful and yields the same outcome in every state.
* `revelation_example`: the example of p. 493: a compensation schedule `w(π)` with the effort left
  to the manager.
* `hybrid_revelation`: Section 14.D (Myerson 1982): mechanisms whose outcome after a message is a
  hidden-action contract can be replaced by truthful and obedient direct mechanisms.
* `hybrid_forcing`: Section 14.D, p. 502: with deterministic profits a "forcing" scheme implements
  any wage-effort pair (with a finite penalty instead of MWG's wage of `-∞`).
* `hybrid_change_of_variables`: p. 502: with forcing contracts the hybrid model is the hidden
  information model with effort variable `π`, disutility `g(ẽ(π), θ)` and profit function `π`.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Proposition 14.C.2 (the revelation principle)** (MWG, p. 493). Let the manager in state `θ`
choose `σ θ` optimally among the messages/choices `Msg` allowed by a contract with outcome `o`.
The direct revelation mechanism `d θ̂ = o (σ θ̂)` makes truthful announcement optimal in every
state and yields exactly the same outcome in every state. -/
theorem proposition_14_C_2 {Θ Msg Out : Type*} (o : Msg → Out) (U : Θ → Out → ℝ)
    (σ : Θ → Msg) (hσ : ∀ θ m, U θ (o m) ≤ U θ (o (σ θ))) :
    ∃ d : Θ → Out, (∀ θ θ', U θ (d θ') ≤ U θ (d θ)) ∧ ∀ θ, d θ = o (σ θ) :=
  ⟨fun θ => o (σ θ), fun θ θ' => hσ θ (σ θ'), fun _ => rfl⟩

/-- **Proposition 14.C.2, "without loss"** (MWG, p. 493): whatever the owner's payoff from an
outcome in a state, the truthful direct mechanism gives the owner the same payoff in every state as
the original contract. -/
theorem proposition_14_C_2_payoff {Θ Msg Out : Type*} (o : Msg → Out) (U : Θ → Out → ℝ)
    (V : Θ → Out → ℝ) (σ : Θ → Msg) (hσ : ∀ θ m, U θ (o m) ≤ U θ (o (σ θ))) :
    ∃ d : Θ → Out, (∀ θ θ', U θ (d θ') ≤ U θ (d θ)) ∧ ∀ θ, V θ (d θ) = V θ (o (σ θ)) := by
  obtain ⟨d, h1, h2⟩ := proposition_14_C_2 o U σ hσ
  exact ⟨d, h1, fun θ => by rw [h2]⟩

/-- **The example of p. 493.** The owner offers a compensation schedule `w(π)` and leaves the
effort to the manager; in state `θ` the manager chooses `e θ ≥ 0` maximizing
`v(w(π(e)) - g(e, θ))`. The revelation mechanism assigning `[w(π(e θ̂)), e θ̂]` to the announcement
`θ̂` is truthful. -/
theorem revelation_example {Θ : Type*} (w prof v : ℝ → ℝ) (g : ℝ → Θ → ℝ) (e : Θ → ℝ)
    (he : ∀ θ, 0 ≤ e θ)
    (hopt : ∀ θ e', 0 ≤ e' → v (w (prof e') - g e' θ) ≤ v (w (prof (e θ)) - g (e θ) θ)) :
    ∀ θ θ', v (w (prof (e θ')) - g (e θ') θ) ≤ v (w (prof (e θ)) - g (e θ) θ) :=
  fun θ θ' => hopt θ (e θ') (he θ')

/-- **Section 14.D, the revelation principle for hybrid models** (MWG, p. 501; Myerson 1982). In a
general mechanism the manager sends a message `m` and then takes a hidden action `a`, obtaining
utility `U θ m a`. If `(σ θ, α θ)` is optimal in state `θ`, the direct mechanism that, after the
announcement `θ̂`, offers the contract of message `σ θ̂` and recommends the action `α θ̂` makes the
manager willing to be truthful and obedient. -/
theorem hybrid_revelation {Θ Msg Act : Type*} (U : Θ → Msg → Act → ℝ) (σ : Θ → Msg)
    (α : Θ → Act) (hopt : ∀ θ m a, U θ m a ≤ U θ (σ θ) (α θ)) :
    ∀ θ θ' a, U θ (σ θ') a ≤ U θ (σ θ) (α θ) :=
  fun θ θ' a => hopt θ (σ θ') a

/-- **Forcing contracts** (MWG, Section 14.D, p. 502). With deterministic, strictly increasing
profits `π(e)`, strictly increasing `v`, and `g(e, θ) ≥ 0` for `e ≥ 0`, the scheme paying `ŵ` if
profits are `π(ê)` and `ŵ - K` otherwise (with `K` above `g(ê, θ)` for the states considered)
makes `ê` the unique optimal effort in each of these states. (MWG uses a wage of `-∞`; any
finite penalty `K > max g(ê, θ)` suffices.) -/
theorem hybrid_forcing {Θ : Type*} (prof v : ℝ → ℝ) (hprof : StrictMono prof) (hv : StrictMono v)
    (g : ℝ → Θ → ℝ) (hg : ∀ e θ, 0 ≤ e → 0 ≤ g e θ) (what ehat K : ℝ)
    (S : Set Θ) (hK : ∀ θ ∈ S, g ehat θ < K) :
    let w : ℝ → ℝ := fun x => if x = prof ehat then what else what - K
    ∀ θ ∈ S, ∀ e, 0 ≤ e → e ≠ ehat → v (w (prof e) - g e θ) < v (w (prof ehat) - g ehat θ) := by
  intro w θ hθ e he hne
  have hne' : prof e ≠ prof ehat := hprof.injective.ne hne
  simp only [w, hne', ↓reduceIte]
  apply hv
  linarith [hg e θ he, hK θ hθ]

/-- **The hybrid model as a hidden-information model** (MWG, Section 14.D, p. 502). Suppose
profits are a deterministic function `π(e)` with an inverse `ẽ` on the relevant profit levels.
Writing a contract in terms of wage-profit pairs, the hidden-information program with effort
variable `π`, disutility `g̃(π, θ) = g(ẽ(π), θ)` and profit function `π ↦ π` has the same owner's
payoff and the same constraints as the program in terms of wage-effort pairs. -/
theorem hybrid_change_of_variables (P : Screen) (prof etil : ℝ → ℝ) (hpH : P.pH = prof)
    (hpL : P.pL = prof) (hinv : ∀ e, 0 ≤ e → etil (prof e) = e)
    (hpos : ∀ e, 0 ≤ e ↔ 0 ≤ prof e) (K : HIContract) (hH : 0 ≤ K.eH) (hL : 0 ≤ K.eL) :
    let P' : Screen := ⟨id, id, fun x θ => P.g (etil x) θ, P.θL, P.θH, P.lam, P.c⟩
    let K' : HIContract := ⟨K.wH, prof K.eH, K.wL, prof K.eL⟩
    P'.Pi K' = P.Pi K ∧ (P'.Feas K' ↔ P.Feas K) := by
  intro P' K'
  have h1 : etil (prof K.eH) = K.eH := hinv _ hH
  have h2 : etil (prof K.eL) = K.eL := hinv _ hL
  refine ⟨by simp [P', K', Screen.Pi, hpH, hpL], ?_⟩
  simp only [Screen.Feas, Screen.C1, Screen.C2, Screen.C3, Screen.C4, P', K', h1, h2,
    ← hpos]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 14.C.2, 14.C.3, 14.C.5, 14.C.6

MWG, pp. 508-509.

* `exercise_14_C_2`: a risk-neutral manager; selling the project (`w(π) = π - α`) attains the
  observable-state payoff, and the revelation mechanism `(π(e*_i) - α, e*_i)` gives the same
  outcome.
* `exercise_14_C_3a`, `exercise_14_C_3a_suff`, `exercise_14_C_3b`: utility `v(w) - g(e, θ)`. Every
  optimal full-information contract pays the same wage in both states (so the manager's utility
  differs across states); the first-order conditions are sufficient; the full-information contract
  violates the truth-telling constraint of state `θ_H` when `e_L < e_H`.
* Exercise 14.C.5 is `HIModel` with `π_H ≠ π_L` (Section 14.C results hold when
  `π'_H ≥ π'_L > 0`); `exercise_14_C_5_reversal`: when `π'_H < π'_L` the first-best efforts can be
  reversed and the solution of the program without (iv) violates (iv).
* `exercise_14_C_6`, `exercise_14_C_6_instance`: the monopsony version of Exercise 13.D.1: the
  high type's task is efficient, the low type's is distorted down, below the competitive one.
-/

namespace MWG.PrincipalAgent

open Set

/-! ### Exercise 14.C.2 -/

/-- **Exercise 14.C.2** (MWG, p. 508). Hidden information with a risk-neutral manager
(`v(w) = w`). Let `e*_i` maximize `S_i(e) = π(e) - g(e, θ_i)` on `[0, ∞)` and
`α* = λ S_H(e*_H) + (1 - λ) S_L(e*_L) - ū`. Under `w(π) = π - α*` the manager in state `θ_i` chooses
`e*_i` (any optimal choice gives the full-information surplus), his expected utility is `ū`, and the
owner gets `α*`, which is the most he can get even when `θ` is observable. The revelation mechanism
`(π(e*_i) - α*, e*_i)` is truthful and gives the same outcome. -/
theorem exercise_14_C_2 (prof : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {θL θH lam ubar eHs eLs : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hH0 : 0 ≤ eHs) (hL0 : 0 ≤ eLs)
    (hH : ∀ e, 0 ≤ e → prof e - g e θH ≤ prof eHs - g eHs θH)
    (hL : ∀ e, 0 ≤ e → prof e - g e θL ≤ prof eLs - g eLs θL) :
    let α := lam * (prof eHs - g eHs θH) + (1 - lam) * (prof eLs - g eLs θL) - ubar
    -- the manager's choices under the sellout
    (∀ e, 0 ≤ e → prof e - α - g e θH ≤ prof eHs - α - g eHs θH) ∧
    (∀ e, 0 ≤ e → prof e - α - g e θL ≤ prof eLs - α - g eLs θL) ∧
    lam * (prof eHs - α - g eHs θH) + (1 - lam) * (prof eLs - α - g eLs θL) = ubar ∧
    -- the owner's payoff `α` is the observable-state optimum
    (∀ wH eH wL eL : ℝ, 0 ≤ eH → 0 ≤ eL →
      ubar ≤ lam * (wH - g eH θH) + (1 - lam) * (wL - g eL θL) →
      lam * (prof eH - wH) + (1 - lam) * (prof eL - wL) ≤ α) ∧
    -- the revelation mechanism
    (prof eHs - α - g eHs θH ≥ prof eLs - α - g eLs θH ∧
      prof eLs - α - g eLs θL ≥ prof eHs - α - g eHs θL) := by
  intro α
  refine ⟨fun e he => by linarith [hH e he], fun e he => by linarith [hL e he],
    by simp only [α]; ring, fun wH eH wL eL h1 h2 h3 => ?_, ?_, ?_⟩
  · have a := mul_le_mul_of_nonneg_left (hH eH h1) hl0
    have b := mul_le_mul_of_nonneg_left (hL eL h2) (by linarith : (0:ℝ) ≤ 1 - lam)
    simp only [α]; nlinarith
  · linarith [hH eLs hL0]
  · linarith [hL eHs hH0]

/-! ### Exercise 14.C.3 -/

/-- **Exercise 14.C.3(a)** (MWG, p. 509), full insurance. With utility `v(w) - g(e, θ)`, `v`
strictly concave and strictly increasing and continuous, every optimal full-information contract
pays the same wage in both states: otherwise paying the certainty equivalent `w̄` with
`v(w̄) = λ v(w_H) + (1 - λ) v(w_L)` in both states keeps the constraint and is cheaper. -/
theorem exercise_14_C_3a {v : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v) (hmono : StrictMono v)
    (hcont : Continuous v) (prof : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {θL θH lam ubar : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) {wH eH wL eL : ℝ}
    (hfeas : ubar ≤ lam * (v wH - g eH θH) + (1 - lam) * (v wL - g eL θL))
    (hopt : ∀ wH' wL', ubar ≤ lam * (v wH' - g eH θH) + (1 - lam) * (v wL' - g eL θL) →
      lam * (prof eH - wH') + (1 - lam) * (prof eL - wL') ≤
        lam * (prof eH - wH) + (1 - lam) * (prof eL - wL)) : wH = wL := by
  by_contra hne
  -- the certainty equivalent
  set t := lam * v wH + (1 - lam) * v wL
  have hJ := tpa_jensen_two_lt hv hl0 hl1 hne
  obtain ⟨wbar, hwbar⟩ : ∃ wbar, v wbar = t := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hlo : v wH ≤ t := by
        have := hmono h; simp only [t]; nlinarith
      have hhi : t ≤ v wL := by
        have := hmono h; simp only [t]; nlinarith
      obtain ⟨c, hc, hct⟩ := intermediate_value_Icc h.le hcont.continuousOn ⟨hlo, hhi⟩
      exact ⟨c, hct⟩
    · have hlo : v wL ≤ t := by
        have := hmono h; simp only [t]; nlinarith
      have hhi : t ≤ v wH := by
        have := hmono h; simp only [t]; nlinarith
      obtain ⟨c, hc, hct⟩ := intermediate_value_Icc h.le hcont.continuousOn ⟨hlo, hhi⟩
      exact ⟨c, hct⟩
  have hlt : wbar < lam * wH + (1 - lam) * wL := hmono.lt_iff_lt.1 (by rw [hwbar]; exact hJ)
  have := hopt wbar wbar (by rw [hwbar]; simp only [t] at *; nlinarith)
  nlinarith

/-- **Exercise 14.C.3(a)** (MWG, p. 509), sufficiency of the first-order conditions. With `π`
concave, `g(·, θ)` convex and `v` concave and increasing, a contract `(w̄, e_H, w̄, e_L)` with
binding constraint and `π'(e_i) v'(w̄) = g_e(e_i, θ_i)` is an optimal full-information contract. -/
theorem exercise_14_C_3a_suff {v dv prof dprof : ℝ → ℝ} {g ge : ℝ → ℝ → ℝ} {θL θH lam ubar : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hv : ConcaveOn ℝ univ v) (hdv : ∀ w, HasDerivAt v (dv w) w)
    (hdvpos : ∀ w, 0 < dv w) (hp : ConcaveOn ℝ (Ici 0) prof)
    (hdp : ∀ e, 0 ≤ e → HasDerivWithinAt prof (dprof e) (Ici 0) e)
    (hg : ∀ θ, ConvexOn ℝ (Ici 0) fun e => g e θ)
    (hdg : ∀ θ e, 0 ≤ e → HasDerivWithinAt (fun e => g e θ) (ge e θ) (Ici 0) e)
    {wbar eH eL : ℝ} (hH0 : 0 ≤ eH) (hL0 : 0 ≤ eL)
    (hbind : lam * (v wbar - g eH θH) + (1 - lam) * (v wbar - g eL θL) = ubar)
    (hfH : dprof eH * dv wbar = ge eH θH) (hfL : dprof eL * dv wbar = ge eL θL)
    {wH' eH' wL' eL' : ℝ} (hH0' : 0 ≤ eH') (hL0' : 0 ≤ eL')
    (hfeas : ubar ≤ lam * (v wH' - g eH' θH) + (1 - lam) * (v wL' - g eL' θL)) :
    lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL') ≤
      lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar) := by
  have hd := hdvpos wbar
  have tH := tpa_tangent_le hp (mem_Ici.2 hH0) (mem_Ici.2 hH0') (hdp eH hH0)
  have tL := tpa_tangent_le hp (mem_Ici.2 hL0) (mem_Ici.2 hL0') (hdp eL hL0)
  have gH := tpa_tangent_ge_convex (hg θH) (mem_Ici.2 hH0) (mem_Ici.2 hH0') (hdg θH eH hH0)
  have gL := tpa_tangent_ge_convex (hg θL) (mem_Ici.2 hL0) (mem_Ici.2 hL0') (hdg θL eL hL0)
  have vH := tpa_tangent_le hv (mem_univ wbar) (mem_univ wH') (hdv wbar).hasDerivWithinAt
  have vL := tpa_tangent_le hv (mem_univ wbar) (mem_univ wL') (hdv wbar).hasDerivWithinAt
  -- multiply the profit tangents by `v'(w̄) > 0`
  have key : dv wbar * (lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL')) ≤
      dv wbar * (lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar)) := by
    have a1 := mul_le_mul_of_nonneg_left tH (mul_nonneg hd.le hl0)
    have a2 := mul_le_mul_of_nonneg_left tL (mul_nonneg hd.le (by linarith : (0:ℝ) ≤ 1 - lam))
    have b1 := mul_le_mul_of_nonneg_left gH hl0
    have b2 := mul_le_mul_of_nonneg_left gL (by linarith : (0:ℝ) ≤ 1 - lam)
    have c1 := mul_le_mul_of_nonneg_left vH hl0
    have c2 := mul_le_mul_of_nonneg_left vL (by linarith : (0:ℝ) ≤ 1 - lam)
    have e1 : dv wbar * lam * (prof eH + dprof eH * (eH' - eH)) =
        dv wbar * lam * prof eH + lam * (ge eH θH * (eH' - eH)) := by rw [← hfH]; ring
    have e2 : dv wbar * (1 - lam) * (prof eL + dprof eL * (eL' - eL)) =
        dv wbar * (1 - lam) * prof eL + (1 - lam) * (ge eL θL * (eL' - eL)) := by rw [← hfL]; ring
    linarith
  exact le_of_mul_le_mul_left key hd

/-- **Exercise 14.C.3(b)** (MWG, p. 509). With `u = v(w) - g(e, θ)` and `g(·, θ_H)` strictly
increasing on `[0, ∞)`, a full-insurance contract `(w̄, e_H), (w̄, e_L)` with `0 ≤ e_L < e_H`
violates the truth-telling constraint of state `θ_H`: it is not feasible when `θ` is not
observable. -/
theorem exercise_14_C_3b {v : ℝ → ℝ} (g : ℝ → ℝ → ℝ) {θH wbar eH eL : ℝ}
    (hg : StrictMonoOn (fun e => g e θH) (Ici 0)) (hL0 : 0 ≤ eL) (hlt : eL < eH) :
    v wbar - g eH θH < v wbar - g eL θH := by
  have := hg (mem_Ici.2 hL0) (mem_Ici.2 (hL0.trans hlt.le)) hlt
  simp only at this; linarith

/-- **Exercise 14.C.3(b)**, the full-information efforts are ordered: if
`π'(e_i) v'(w̄) = g_e(e_i, θ_i)`, `π` is strictly concave, `g(·, θ_L)` convex, and
`g_e(e, θ_H) < g_e(e, θ_L)` for `e > 0`, then `e_L < e_H` whenever `e_H > 0`. -/
theorem exercise_14_C_3b_order {prof dprof : ℝ → ℝ} {g ge : ℝ → ℝ → ℝ} {θL θH a : ℝ}
    (hp : StrictConcaveOn ℝ (Ici 0) prof)
    (hdp : ∀ e, 0 ≤ e → HasDerivWithinAt prof (dprof e) (Ici 0) e)
    (hg : ConvexOn ℝ (Ici 0) fun e => g e θL)
    (hdg : ∀ e, 0 ≤ e → HasDerivWithinAt (fun e => g e θL) (ge e θL) (Ici 0) e)
    (hcross : ∀ e, 0 < e → ge e θH < ge e θL) (ha : 0 < a) {eH eL : ℝ} (hH0 : 0 < eH)
    (hL0 : 0 ≤ eL) (hfH : dprof eH * a = ge eH θH) (hfL : dprof eL * a = ge eL θL) :
    eL < eH := by
  by_contra hle
  rw [not_lt] at hle
  have h1 : dprof eL ≤ dprof eH := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_anti hp (mem_Ici.2 hH0.le) (mem_Ici.2 hL0) h (hdp _ hH0.le)
        (hdp _ hL0)).le
    · rw [h]
  have h4 : ge eH θL ≤ ge eL θL := by
    rcases hle.lt_or_eq with h | h
    · have t1 := tpa_tangent_ge_convex hg (mem_Ici.2 hH0.le) (mem_Ici.2 hL0) (hdg eH hH0.le)
      have t2 := tpa_tangent_ge_convex hg (mem_Ici.2 hL0) (mem_Ici.2 hH0.le) (hdg eL hL0)
      nlinarith
    · rw [h]
  have := hcross eH hH0
  nlinarith [mul_le_mul_of_nonneg_right h1 ha.le]

/-! ### Exercise 14.C.5 -/

/-- The relaxed program without (iv) is solved by the binding contract at a maximizer of `S_H` and
a maximizer of the virtual surplus `Q`, whatever their order. -/
theorem screen_relax_opt {P : Screen} (h : P.Hyp) {eH eL : ℝ} (hH0 : 0 ≤ eH)
    (hH : ∀ e, 0 ≤ e → P.SH e ≤ P.SH eH) (hL0 : 0 ≤ eL) (hQ : ∀ e, 0 ≤ e → P.Q e ≤ P.Q eL) :
    P.IsOptRelax (P.bind eH eL) := by
  refine ⟨⟨hH0, hL0, ?_, ?_⟩, fun K hK => ?_⟩
  · unfold Screen.C1 Screen.bind; simp
  · unfold Screen.C3 Screen.bind Screen.D; simp only; linarith
  · have := Screen.screen_Pi_le h hK.2.2.1 hK.2.2.2
    rw [Screen.screen_Pi_bind]
    unfold Screen.R at this ⊢
    nlinarith [mul_le_mul_of_nonneg_left (hH _ hK.1) h.lam_pos.le, hQ _ hK.2.1]

/-- The model of `exercise_14_C_5_reversal`: `π_H(e) = log (1 + e) / 8`, `π_L(e) = log (1 + e)`,
`g(e, θ_L) = e²/4`, `g(e, θ_H) = e²/12`, `λ = 7/19`, `c = 0`. -/
noncomputable def exRev : Screen :=
  ⟨fun e => Real.log (1 + e) / 8, fun e => Real.log (1 + e),
    fun e θ => if θ = 0 then e ^ 2 / 4 else e ^ 2 / 12, 0, 1, 7 / 19, 0⟩

/-- **Exercise 14.C.5, "what happens if this condition is not satisfied?"** (MWG, p. 509). In
`exRev` (`π'_H < π'_L`) the first-best efforts are reversed (`e*_H = 1/2 < e*_L = 1`), and the
solution of the program without constraint (iv), `e_H = 1/2`, `e_L = 4/5`, violates (iv): the
truth-telling constraint of state `θ_L` can no longer be ignored. -/
theorem exercise_14_C_5_reversal :
    (∀ e, 0 ≤ e → exRev.SH e ≤ exRev.SH (1 / 2)) ∧ (∀ e, 0 ≤ e → exRev.SL e ≤ exRev.SL 1) ∧
      exRev.IsOptRelax (exRev.bind (1 / 2) (4 / 5)) ∧ ¬ exRev.C4 (exRev.bind (1 / 2) (4 / 5)) := by
  have gL : ∀ e, exRev.g e exRev.θL = e ^ 2 / 4 := fun e => by simp [exRev]
  have gH : ∀ e, exRev.g e exRev.θH = e ^ 2 / 12 := fun e => by simp [exRev]
  have hSH : ∀ e, exRev.SH e = Real.log (1 + e) / 8 - e ^ 2 / 12 := fun e => by
    simp only [Screen.SH, gH]; rfl
  have hSL : ∀ e, exRev.SL e = Real.log (1 + e) - e ^ 2 / 4 := fun e => by
    simp only [Screen.SL, gL]; rfl
  have hD : ∀ e, exRev.D e = e ^ 2 / 6 := fun e => by
    simp only [Screen.D, gL, gH]; ring
  have hQ : ∀ e, exRev.Q e = 12 / 19 * Real.log (1 + e) - 25 / 114 * e ^ 2 := fun e => by
    simp only [Screen.Q, hSL, hD]; simp only [exRev]; ring
  have hyp : exRev.Hyp := by
    refine ⟨by norm_num [exRev], by norm_num [exRev], by rw [hD]; norm_num, ?_⟩
    intro a ha b hb hab
    simp only [hD]
    have : (0:ℝ) ≤ a := ha
    nlinarith
  have hSHmax : ∀ e, 0 ≤ e → exRev.SH e ≤ exRev.SH (1 / 2) := fun e he => by
    rw [hSH, hSH]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (2 * e - 1)]
  have hSLmax : ∀ e, 0 ≤ e → exRev.SL e ≤ exRev.SL 1 := fun e he => by
    rw [hSL, hSL]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / 2 by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 = 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (e - 1)]
  have hQmax : ∀ e, 0 ≤ e → exRev.Q e ≤ exRev.Q (4 / 5) := fun e he => by
    rw [hQ, hQ]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (9 / 5) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 4 / 5 = 9 / 5 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (5 * e - 4)]
  refine ⟨hSHmax, hSLmax, screen_relax_opt hyp (by norm_num) hSHmax (by norm_num) hQmax, ?_⟩
  intro h4
  unfold Screen.C4 Screen.bind at h4
  simp only at h4
  rw [gL, gL, hD, gH] at h4
  norm_num at h4
  linarith

/-! ### Exercise 14.C.6 -/

/-- The monopsony screening program of Exercise 14.C.6: Exercise 13.D.1's labor market (output
`θ(1 + μt)`, utility `w - c(t, θ)`, reservation utility `0`) with a single employer. -/
noncomputable def monopsony (M : AdverseSelection.SigModel) (μ : ℝ) : Screen :=
  ⟨fun t => M.θH * (1 + μ * t), fun t => M.θL * (1 + μ * t), M.c, M.θL, M.θH, M.lam, 0⟩

/-- The single-crossing assumption of Chapter 13 gives the hypotheses of the screening program. -/
theorem monopsony_hyp {M : AdverseSelection.SigModel} (hM : M.Valid) (μ : ℝ) :
    (monopsony M μ).Hyp := by
  refine ⟨hM.lam_pos, hM.lam_lt, ?_, ?_⟩
  · change M.c 0 M.θL - M.c 0 M.θH = 0
    rw [hM.c_zero, hM.c_zero, sub_self]
  · intro a ha b hb hab
    have := hM.sc a b ha hab
    change M.c a M.θL - M.c a M.θH < M.c b M.θL - M.c b M.θH
    linarith

/-- **Exercise 14.C.6** (MWG, p. 509). With a single employer, if `t*_H`, `t*_L` uniquely maximize
the types' surpluses `S_θ(t) = θ(1 + μt) - c(t, θ)` and `t*_L ≤ t*_H`, every optimal menu gives the
high type the efficient task `t*_H` and the low type a task `t_L ≤ t*_L` (with (i) and (iii)
binding). In every subgame perfect equilibrium of the competitive model of Exercise 13.D.1 the low
type's task is `t*_L`: the monopsonist's low task is no higher than the competitive one. -/
theorem exercise_14_C_6 {M : AdverseSelection.SigModel} (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ)
    {tHs tLs : ℝ} (hH : Screen.IsFB (monopsony M μ).SH tHs)
    (hL : Screen.IsFB (monopsony M μ).SL tLs) (hord : tLs ≤ tHs) {K : HIContract}
    (hK : (monopsony M μ).IsOpt K) :
    K.eH = tHs ∧ K.eL ≤ tLs ∧ K = (monopsony M μ).bind tHs K.eL ∧
      ∀ A₁ A₂, (M.prodGame μ).IsEq A₁ A₂ → ∃ kL, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
        kL.2 = tLs ∧ K.eL ≤ kL.2 := by
  have hyp := monopsony_hyp hM μ
  obtain ⟨hLle, hHe⟩ := Screen.lemma_14_C_3 hyp hH hL hord hK
  obtain ⟨-, -, hKb⟩ := (Screen.screen_opt_iff hyp hH hL hord K).1 hK
  refine ⟨hHe, hLle, hKb, fun A₁ A₂ hE => ?_⟩
  obtain ⟨kL, -, hkL, -, hkL0, -, -, -, hmax, -⟩ :=
    AdverseSelection.SigModel.exercise_13_D_1 hM hμ hE
  have hSL : ∀ t, (monopsony M μ).SL t = M.surplus μ false t := fun t => by
    simp only [Screen.SL, monopsony, AdverseSelection.SigModel.surplus,
      AdverseSelection.SigModel.θ_false]
  have heq : kL.2 = tLs := by
    by_contra hne
    have := hL.2 _ hkL0 hne
    rw [hSL, hSL] at this
    linarith [hmax tLs hL.1]
  exact ⟨kL, hkL, heq, heq ▸ hLle⟩

/-- **Exercise 14.C.6, an instance** (MWG, p. 509), with Chapter 13's `quadModel` (`θ_L = 1`,
`θ_H = 2`, `λ = 1/2`, `c(t, θ) = t²/θ`) and `μ = 4`: the optimal monopsony menu has tasks
`t_H = 8`, `t_L = 4/3`, while the competitive equilibrium tasks are `8` and `2`. -/
theorem exercise_14_C_6_instance :
    (monopsony AdverseSelection.SigModel.quadModel 4).IsOpt
      ((monopsony AdverseSelection.SigModel.quadModel 4).bind 8 (4 / 3)) := by
  set P := monopsony AdverseSelection.SigModel.quadModel 4
  have hyp := monopsony_hyp AdverseSelection.SigModel.quadModel_valid 4
  have hSH : ∀ t, P.SH t = 2 + 8 * t - t ^ 2 / 2 := fun t => by
    simp only [P, Screen.SH, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hSL : ∀ t, P.SL t = 1 + 4 * t - t ^ 2 := fun t => by
    simp only [P, Screen.SL, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hD : ∀ t, P.D t = t ^ 2 / 2 := fun t => by
    simp only [P, Screen.D, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hQ : ∀ t, P.Q t = (1 + 4 * t - t ^ 2) / 2 - t ^ 2 / 4 := fun t => by
    simp only [Screen.Q, hSL, hD]; simp only [P, monopsony, AdverseSelection.SigModel.quadModel]
    ring
  have hH : Screen.IsFB P.SH 8 := ⟨by norm_num, fun e _ hne => by
    rw [hSH, hSH]; have : 0 < (e - 8) ^ 2 := by positivity
    nlinarith⟩
  have hL : Screen.IsFB P.SL 2 := ⟨by norm_num, fun e _ hne => by
    rw [hSL, hSL]; have : 0 < (e - 2) ^ 2 := by positivity
    nlinarith⟩
  refine (Screen.screen_opt_iff hyp hH hL (by norm_num) _).2
    ⟨by change (0:ℝ) ≤ 4 / 3; norm_num, fun e _ => ?_, rfl⟩
  change P.Q e ≤ P.Q (4 / 3)
  rw [hQ, hQ]; nlinarith [sq_nonneg (e - 4 / 3)]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 14.AA.1 and 14.AA.2

MWG, p. 510.

* `exercise_14_AA_1`: the differential form of the monotone likelihood ratio property:
  `f_e(π|e) / f(π|e)` is nondecreasing in `π` for every `e ∈ [a, b]` iff
  `f(π|e'') / f(π|e')` is nondecreasing in `π` for all `e' < e''` in `[a, b]`.
  `exercise_14_AA_1_strict` gives the strict version of "only if"; `exercise_14_AA_1_strict_false`
  shows that the strict version of "if" is false (correction).
* `exercise_14_AA_2_valid`, `exercise_14_AA_2_contract`: two outcomes; if `f(π_H|e)` is concave in
  `e`, `g` convex and `v_H ≥ v_L`, the manager's first-order condition is sufficient (the
  first-order approach is valid); the optimal contract implementing an interior `e` has
  `v_H - v_L = g'(e) / f'(π_H|e)` and a binding participation constraint.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- A point of `[a, b]` (`a < b`) is a limit of other points of `[a, b]`. -/
theorem aa_neBot {a b e : ℝ} (hab : a < b) (he : e ∈ Icc a b) : (𝓝[Icc a b \ {e}] e).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  rcases he.2.lt_or_eq with h | h
  · have hsub : Ioo e b ⊆ Icc a b \ {e} := fun x hx => ⟨⟨he.1.trans hx.1.le, hx.2.le⟩, hx.1.ne'⟩
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨le_rfl, h.le⟩)
  · have hsub : Ioo a b ⊆ Icc a b \ {e} := fun x hx => ⟨⟨hx.1.le, hx.2.le⟩, by
      rw [h]; exact hx.2.ne⟩
    exact closure_mono hsub (by rw [closure_Ioo hab.ne]; rw [h]; exact ⟨hab.le, le_rfl⟩)

/-- A function with within-derivatives on `[a, b]` (`a < b`) is monotone there iff its derivative
is nonnegative at every point of `[a, b]`. -/
theorem aa_mono_iff {G G' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ e ∈ Icc a b, HasDerivWithinAt G (G' e) (Icc a b) e) :
    MonotoneOn G (Icc a b) ↔ ∀ e ∈ Icc a b, 0 ≤ G' e := by
  constructor
  · intro hm e he
    have ht := hasDerivWithinAt_iff_tendsto_slope.1 (hd e he)
    have := aa_neBot hab he
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hy.2 with h | h
    · exact div_nonneg_of_nonpos (by linarith [hm hy.1 he h.le]) (by linarith)
    · exact div_nonneg (by linarith [hm he hy.1 h.le]) (by linarith)
  · intro hpos
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := G') (convex_Icc a b)
      (fun e he => (hd e he).continuousWithinAt) (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Icc] at he ⊢
      exact (hd e (Ioo_subset_Icc_self he)).mono Ioo_subset_Icc_self
    · rw [interior_Icc] at he
      exact hpos e (Ioo_subset_Icc_self he)

/-- For positive numbers, `A/B ≤ C/D` iff `log A - log B ≤ log C - log D`. -/
theorem aa_ratio_log {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    A / B ≤ C / D ↔ Real.log A - Real.log B ≤ Real.log C - Real.log D := by
  rw [← Real.log_div hA.ne' hB.ne', ← Real.log_div hC.ne' hD.ne',
    Real.log_le_log_iff (div_pos hA hB) (div_pos hC hD)]

/-- The derivative of `e ↦ log f(π₂|e) - log f(π₁|e)`. -/
theorem aa_G_deriv {f fe : ℝ → ℝ → ℝ} {S : Set ℝ} (hf : ∀ x e, 0 < f x e) {e : ℝ}
    (hd : ∀ x, HasDerivWithinAt (fun e => f x e) (fe x e) S e) (x₁ x₂ : ℝ) :
    HasDerivWithinAt (fun e => Real.log (f x₂ e) - Real.log (f x₁ e))
      (fe x₂ e / f x₂ e - fe x₁ e / f x₁ e) S e :=
  ((hd x₂).log (hf x₂ e).ne').sub ((hd x₁).log (hf x₁ e).ne')

/-- **Exercise 14.AA.1** (MWG, p. 510). For positive `f(π|e)` differentiable in `e ∈ [a, b]`
(`a < b`), `f_e(π|e) / f(π|e)` is nondecreasing in `π` for every `e ∈ [a, b]` iff
`f(π|e'') / f(π|e')` is nondecreasing in `π` whenever `e' < e''` in `[a, b]`. -/
theorem exercise_14_AA_1 {f fe : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ∀ x e, 0 < f x e)
    (hd : ∀ x, ∀ e ∈ Icc a b, HasDerivWithinAt (fun e => f x e) (fe x e) (Icc a b) e) :
    (∀ e ∈ Icc a b, Monotone fun x => fe x e / f x e) ↔
      ∀ e' ∈ Icc a b, ∀ e'' ∈ Icc a b, e' < e'' → Monotone fun x => f x e'' / f x e' := by
  -- both sides say: for `x₁ ≤ x₂`, `G = log f(x₂|·) - log f(x₁|·)` is monotone on `[a, b]`
  have key : ∀ x₁ x₂, MonotoneOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) ↔
      ∀ e ∈ Icc a b, 0 ≤ fe x₂ e / f x₂ e - fe x₁ e / f x₁ e :=
    fun x₁ x₂ => aa_mono_iff hab fun e he => aa_G_deriv hf (fun x => hd x e he) x₁ x₂
  constructor
  · intro h e' he' e'' he'' hlt x₁ x₂ hx
    have hm := (key x₁ x₂).2 fun e he => sub_nonneg.2 (h e he hx)
    have := hm he' he'' hlt.le
    simp only at this
    rw [aa_ratio_log (hf _ _) (hf _ _) (hf _ _) (hf _ _)]
    linarith
  · intro h e he x₁ x₂ hx
    have hm : MonotoneOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) := by
      intro e' he' e'' he'' hle
      rcases hle.lt_or_eq with hlt | heq
      · have := (aa_ratio_log (hf _ _) (hf _ _) (hf _ _) (hf _ _)).1 (h e' he' e'' he'' hlt hx)
        simp only; linarith
      · rw [heq]
    exact sub_nonneg.1 ((key x₁ x₂).1 hm e he)

/-- **Exercise 14.AA.1, strict "only if"**: if `f_e/f` is strictly increasing in `π` for every
`e ∈ [a, b]`, then `f(π|e'')/f(π|e')` is strictly increasing in `π` for `e' < e''`. -/
theorem exercise_14_AA_1_strict {f fe : ℝ → ℝ → ℝ} {a b : ℝ} (hf : ∀ x e, 0 < f x e)
    (hd : ∀ x, ∀ e ∈ Icc a b, HasDerivWithinAt (fun e => f x e) (fe x e) (Icc a b) e)
    (h : ∀ e ∈ Icc a b, StrictMono fun x => fe x e / f x e) :
    ∀ e' ∈ Icc a b, ∀ e'' ∈ Icc a b, e' < e'' → StrictMono fun x => f x e'' / f x e' := by
  intro e' he' e'' he'' hlt x₁ x₂ hx
  have hm : StrictMonoOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := fun e => fe x₂ e / f x₂ e - fe x₁ e / f x₁ e) (convex_Icc a b)
      (fun e he => (aa_G_deriv hf (fun x => hd x e he) x₁ x₂).continuousWithinAt)
      (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Icc] at he ⊢
      exact (aa_G_deriv hf (fun x => hd x e (Ioo_subset_Icc_self he)) x₁ x₂).mono
        Ioo_subset_Icc_self
    · rw [interior_Icc] at he
      exact sub_pos.2 (h e (Ioo_subset_Icc_self he) hx)
  have := hm he' he'' hlt
  simp only at this
  have hA := hf x₁ e''; have hB := hf x₁ e'; have hC := hf x₂ e''; have hD := hf x₂ e'
  rw [div_lt_div_iff₀ hB hD, ← Real.log_lt_log_iff (mul_pos hA hD) (mul_pos hC hB),
    Real.log_mul hA.ne' hD.ne', Real.log_mul hC.ne' hB.ne']
  linarith

/-- **Exercise 14.AA.1, the strict "if" is false** (correction). For `f(π|e) = exp(e³ π)` on
`e ∈ [-1, 1]` the ratio `f(π|e'')/f(π|e') = exp((e''³ - e'³) π)` is strictly increasing in `π` for
every `e' < e''`, but `f_e/f = 3 e² π` is constant in `π` at `e = 0`. (Multiplying `f` by any
positive normalizing factor `c(e)` changes neither property.) -/
theorem exercise_14_AA_1_strict_false :
    (∀ e' e'' : ℝ, e' < e'' →
        StrictMono fun x : ℝ => Real.exp (e'' ^ 3 * x) / Real.exp (e' ^ 3 * x)) ∧
      (∀ x e : ℝ, HasDerivAt (fun e => Real.exp (e ^ 3 * x))
        (3 * e ^ 2 * x * Real.exp (e ^ 3 * x)) e)
      ∧ ¬ StrictMono fun x : ℝ => 3 * (0 : ℝ) ^ 2 * x * Real.exp (0 ^ 3 * x) /
        Real.exp (0 ^ 3 * x) := by
  refine ⟨fun e' e'' hlt x₁ x₂ hx => ?_, fun x e => ?_, fun h => ?_⟩
  · simp only [← Real.exp_sub]
    apply Real.exp_lt_exp.2
    have : e' ^ 3 < e'' ^ 3 := Odd.strictMono_pow (by decide) hlt
    nlinarith
  · have := ((hasDerivAt_pow 3 e).mul_const x).exp
    convert this using 1
    push_cast; ring
  · have := h (show (0 : ℝ) < 1 by norm_num)
    simp at this

/-- **Exercise 14.AA.2** (MWG, p. 510), validity of the first-order approach. Two outcomes; the
manager's utility from effort `e ∈ [0, ē]` under utility levels `v_H ≥ v_L` is
`v_L + f(π_H|e)(v_H - v_L) - g(e)`. If `f(π_H|·)` is concave and `g` convex, any `e` satisfying the
first-order condition `f'(π_H|e)(v_H - v_L) = g'(e)` maximizes it. -/
theorem exercise_14_AA_2_valid {p dp g dg : ℝ → ℝ} {ebar : ℝ}
    (hp : ConcaveOn ℝ (Icc 0 ebar) p) (hg : ConvexOn ℝ (Icc 0 ebar) g)
    (hdp : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt p (dp e) (Icc 0 ebar) e)
    (hdg : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt g (dg e) (Icc 0 ebar) e)
    {vL vH : ℝ} (hv : vL ≤ vH) {e : ℝ} (he : e ∈ Icc 0 ebar) (hfoc : dp e * (vH - vL) = dg e) :
    ∀ e' ∈ Icc 0 ebar, vL + p e' * (vH - vL) - g e' ≤ vL + p e * (vH - vL) - g e := by
  intro e' he'
  have t1 := tpa_tangent_le hp he he' (hdp e he)
  have t2 := tpa_tangent_ge_convex hg he he' (hdg e he)
  have := mul_le_mul_of_nonneg_right t1 (sub_nonneg.2 hv)
  have e1 : dp e * (e' - e) * (vH - vL) = dg e * (e' - e) := by rw [← hfoc]; ring
  nlinarith

/-- **Exercise 14.AA.2** (MWG, p. 510), the optimal contract. Under the conditions of
`exercise_14_AA_2_valid`, with `f'(π_H|e) > 0`, `g'(e) ≥ 0` and wages `φ(v)` increasing in the
utility level (`φ = v⁻¹`), the cheapest utility levels implementing an interior `e ∈ (0, ē)` with
expected utility at least `ū` are `v_H - v_L = g'(e)/f'(π_H|e)` with participation binding:
every implementing pair is weakly more expensive. -/
theorem exercise_14_AA_2_contract {p dp g dg φ : ℝ → ℝ} {ebar ubar : ℝ}
    (hp : ConcaveOn ℝ (Icc 0 ebar) p) (hg : ConvexOn ℝ (Icc 0 ebar) g)
    (hdp : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt p (dp e) (Icc 0 ebar) e)
    (hdg : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt g (dg e) (Icc 0 ebar) e)
    (hφ : Monotone φ) {e : ℝ} (he : e ∈ Ioo 0 ebar) (hp01 : 0 ≤ p e ∧ p e ≤ 1)
    (hdp0 : 0 < dp e) (hdg0 : 0 ≤ dg e) :
    let Δ := dg e / dp e
    let vL := ubar + g e - p e * Δ
    -- the contract implements `e` and gives exactly `ū`
    (∀ e' ∈ Icc 0 ebar, vL + p e' * Δ - g e' ≤ vL + p e * Δ - g e) ∧
      vL + p e * Δ - g e = ubar ∧
    -- every implementing pair costs at least as much
    ∀ uL uH : ℝ, (∀ e' ∈ Icc 0 ebar, uL + p e' * (uH - uL) - g e' ≤ uL + p e * (uH - uL) - g e) →
      ubar ≤ uL + p e * (uH - uL) - g e →
      p e * φ (vL + Δ) + (1 - p e) * φ vL ≤ p e * φ uH + (1 - p e) * φ uL := by
  intro Δ vL
  have hIcc : e ∈ Icc 0 ebar := Ioo_subset_Icc_self he
  have hΔ : 0 ≤ Δ := div_nonneg hdg0 hdp0.le
  have hfocΔ : dp e * Δ = dg e := by simp only [Δ]; field_simp
  refine ⟨fun e' he' => ?_, by simp only [vL]; ring, fun uL uH hIC hpart => ?_⟩
  · have := exercise_14_AA_2_valid hp hg hdp hdg (vL := vL) (vH := vL + Δ) (by linarith) hIcc
      (by rw [add_sub_cancel_left]; exact hfocΔ) e' he'
    simpa only [add_sub_cancel_left] using this
  · -- interior maximum: the first-order condition holds
    have hnhds : Icc 0 ebar ∈ 𝓝 e := Icc_mem_nhds he.1 he.2
    have hU : HasDerivAt (fun e => uL + p e * (uH - uL) - g e) (dp e * (uH - uL) - dg e) e :=
      ((((hdp e hIcc).hasDerivAt hnhds).mul_const (uH - uL)).const_add uL).sub
        ((hdg e hIcc).hasDerivAt hnhds)
    have hloc : IsLocalMax (fun e => uL + p e * (uH - uL) - g e) e :=
      Filter.mem_of_superset hnhds fun y hy => hIC y hy
    have hfoc := hloc.hasDerivAt_eq_zero hU
    have hdiff : uH - uL = Δ := by
      simp only [Δ]; field_simp; linarith
    have hLle : vL ≤ uL := by
      simp only [vL]; rw [hdiff] at hpart; linarith
    have hHle : vL + Δ ≤ uH := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (hφ hHle) hp01.1,
      mul_le_mul_of_nonneg_left (hφ hLle) (by linarith : (0:ℝ) ≤ 1 - p e)]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.B.4

MWG, Exercise 14.B.4, p. 507; Appendix A, pp. 503-504.

Three efforts `e₁, e₂, e₃` (indices `0, 1, 2`), profits `π_H = 10` and `π_L = 0`,
`f(π_H|e) = 2/3, 1/2, 1/3`, `g(e) = 5/3, 8/5, 4/3`, `v(w) = √w`, `ū = 0`. A contract is described
by the manager's utility levels `v_H, v_L ≥ 0` (wages `v_H²`, `v_L²`), as the hint suggests.

* `exercise_14_B_4a`: with observable effort the optimal contract implements `e₁` with the fixed
  wage `25/9`.
* `exercise_14_B_4b`, `exercise_14_B_4b_threshold`: `e₂` cannot be implemented; it can be
  implemented iff `g(e₂) ≤ 3/2`.
* `exercise_14_B_4c`: with unobservable effort the optimal contract implements `e₁` with
  `v_H = 2`, `v_L = 1` (wages `4` and `1`), uniquely.
* `exercise_14_B_4d_obs`, `exercise_14_B_4d_unobs`: with `g(e₁) = √8` and `f(π_H|e₁) = x`, the
  observable optimum implements `e₂` for every `x ∈ (0, 1)`, while for `x ≥ 99/100` every optimal
  unobservable contract implements `e₁`: the effort implemented is higher when effort is not
  observable (the upward distortion of p. 487 and Appendix A, which also features inefficient risk
  bearing).
-/

namespace MWG.PrincipalAgent

/-- The manager's expected utility from effort `i` under utility levels `(v_H, v_L)`. -/
def b4EU (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : ℝ := p i * vH + (1 - p i) * vL - g i

/-- The owner's expected profit when effort `i` is taken under `(v_H, v_L)` (wages `v²`). -/
def b4Profit (p : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : ℝ :=
  10 * p i - (p i * vH ^ 2 + (1 - p i) * vL ^ 2)

/-- A contract specifying effort `i` and acceptable to the manager (observable effort). -/
def b4Obs (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : Prop :=
  0 ≤ vH ∧ 0 ≤ vL ∧ 0 ≤ b4EU p g i vH vL

/-- A contract implementing effort `i` when effort is unobservable. -/
def b4Impl (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : Prop :=
  b4Obs p g i vH vL ∧ ∀ j, b4EU p g j vH vL ≤ b4EU p g i vH vL

/-- The data of the exercise. -/
noncomputable def b4p : Fin 3 → ℝ := ![2 / 3, 1 / 2, 1 / 3]

noncomputable def b4g : Fin 3 → ℝ := ![5 / 3, 8 / 5, 4 / 3]

/-- Jensen for `v ↦ v²`: the expected wage is at least the square of the expected utility. -/
theorem b4_jensen {q a b : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (q * a + (1 - q) * b) ^ 2 ≤ q * a ^ 2 + (1 - q) * b ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - q)) (sq_nonneg (a - b))]

/-- The observable-effort bound: profit from effort `i` is at most `10 f(π_H|e_i) - g(e_i)²`. -/
theorem b4_obs_bound {p g : Fin 3 → ℝ} {i : Fin 3} (hp0 : 0 ≤ p i) (hp1 : p i ≤ 1)
    (hg : 0 ≤ g i) {vH vL : ℝ} (h : b4Obs p g i vH vL) :
    b4Profit p i vH vL ≤ 10 * p i - g i ^ 2 := by
  have hJ := b4_jensen (a := vH) (b := vL) hp0 hp1
  have hE : g i ≤ p i * vH + (1 - p i) * vL := by have := h.2.2; unfold b4EU at this; linarith
  unfold b4Profit
  nlinarith

/-- **Exercise 14.B.4(a)** (MWG, p. 507). With observable effort the optimal contract specifies
`e₁` and the fixed wage `25/9` (`v = 5/3`), with profit `35/9`. -/
theorem exercise_14_B_4a :
    b4Obs b4p b4g 0 (5 / 3) (5 / 3) ∧ b4Profit b4p 0 (5 / 3) (5 / 3) = 35 / 9 ∧
      ∀ i vH vL, b4Obs b4p b4g i vH vL → b4Profit b4p i vH vL ≤ 35 / 9 := by
  refine ⟨⟨by norm_num, by norm_num, by simp [b4EU, b4p, b4g]; norm_num⟩,
    by simp [b4Profit, b4p]; norm_num, fun i vH vL h => ?_⟩
  have := b4_obs_bound (p := b4p) (g := b4g) (i := i) (by fin_cases i <;> norm_num [b4p])
    (by fin_cases i <;> norm_num [b4p]) (by fin_cases i <;> norm_num [b4g]) h
  fin_cases i <;> simp [b4p, b4g] at this ⊢ <;> linarith

/-- **Exercise 14.B.4(b)** (MWG, p. 507). Whatever the utility levels, the manager strictly
prefers `e₁` or `e₃` to `e₂`: `e₂` cannot be implemented. -/
theorem exercise_14_B_4b (vH vL : ℝ) :
    b4EU b4p b4g 1 vH vL < b4EU b4p b4g 0 vH vL ∨ b4EU b4p b4g 1 vH vL < b4EU b4p b4g 2 vH vL := by
  simp only [b4EU, b4p, b4g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  linarith [h.1, h.2]

/-- **Exercise 14.B.4(b)**, "for what levels of `g(e₂)` would `e₂` be implementable?" (with
`g(e₂) ≥ 0`): exactly when `g(e₂) ≤ 3/2`. -/
theorem exercise_14_B_4b_threshold {g2 : ℝ} (hg2 : 0 ≤ g2) :
    (∃ vH vL, b4Impl b4p ![5 / 3, g2, 4 / 3] 1 vH vL) ↔ g2 ≤ 3 / 2 := by
  constructor
  · rintro ⟨vH, vL, -, hic⟩
    have h0 := hic 0
    have h2 := hic 2
    simp only [b4EU, b4p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h2
    linarith
  · intro h
    refine ⟨g2 + 1, g2, ⟨by linarith, hg2, ?_⟩, fun j => ?_⟩
    · simp [b4EU, b4p]; linarith
    · fin_cases j <;> simp [b4EU, b4p] <;> linarith

/-- **Exercise 14.B.4(c)** (MWG, p. 507). With unobservable effort the optimal contract implements
`e₁` with `v_H = 2`, `v_L = 1` (wages `4` and `1`) and profit `11/3`; it is the unique contract
implementing `e₁` at least cost, implementing `e₃` yields at most `14/9`, and `e₂` cannot be
implemented. -/
theorem exercise_14_B_4c :
    b4Impl b4p b4g 0 2 1 ∧ b4Profit b4p 0 2 1 = 11 / 3 ∧
      (∀ vH vL, b4Impl b4p b4g 0 vH vL → b4Profit b4p 0 vH vL ≤ 11 / 3 ∧
        (b4Profit b4p 0 vH vL = 11 / 3 → vH = 2 ∧ vL = 1)) ∧
      (∀ vH vL, b4Impl b4p b4g 2 vH vL → b4Profit b4p 2 vH vL ≤ 14 / 9) ∧
      ∀ vH vL, ¬ b4Impl b4p b4g 1 vH vL := by
  refine ⟨⟨⟨by norm_num, by norm_num, by simp [b4EU, b4p, b4g]; norm_num⟩, fun j => ?_⟩,
    by simp [b4Profit, b4p]; norm_num, fun vH vL h => ?_, fun vH vL h => ?_, fun vH vL h => ?_⟩
  · fin_cases j <;> norm_num [b4EU, b4p, b4g]
  · obtain ⟨⟨-, -, hp⟩, hic⟩ := h
    have h2 := hic 2
    simp only [b4EU, b4p, b4g, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hp h2
    simp only [b4Profit, b4p, Matrix.cons_val_zero]
    constructor
    · nlinarith [sq_nonneg (vH - 2), sq_nonneg (vL - 1)]
    · intro heq
      constructor <;> nlinarith [sq_nonneg (vH - 2), sq_nonneg (vL - 1)]
  · have := b4_obs_bound (p := b4p) (g := b4g) (i := 2) (by norm_num [b4p])
      (by norm_num [b4p]) (by norm_num [b4g]) h.1
    simp [b4p, b4g] at this ⊢; linarith
  · rcases exercise_14_B_4b vH vL with h' | h'
    · linarith [h.2 0]
    · linarith [h.2 2]

/-- The data of part (d): `f(π_H|e₁) = x`, `g(e₁) = √8`. -/
noncomputable def b4pd (x : ℝ) : Fin 3 → ℝ := ![x, 1 / 2, 1 / 3]

noncomputable def b4gd : Fin 3 → ℝ := ![Real.sqrt 8, 8 / 5, 4 / 3]

theorem b4_sqrt8 : Real.sqrt 8 ^ 2 = 8 ∧ 2828 / 1000 < Real.sqrt 8 ∧ Real.sqrt 8 < 2829 / 1000 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)
  have hp := Real.sqrt_nonneg 8
  refine ⟨h, ?_, ?_⟩ <;> nlinarith

/-- **Exercise 14.B.4(d)**, observable effort (MWG, p. 507). For every `x ∈ (0, 1)` the observable
optimum implements `e₂` with the fixed wage `64/25` (profit `61/25`); every contract specifying
`e₁` or `e₃` earns strictly less. -/
theorem exercise_14_B_4d_obs {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    b4Obs (b4pd x) b4gd 1 (8 / 5) (8 / 5) ∧ b4Profit (b4pd x) 1 (8 / 5) (8 / 5) = 61 / 25 ∧
      ∀ i vH vL, i ≠ 1 → b4Obs (b4pd x) b4gd i vH vL → b4Profit (b4pd x) i vH vL < 61 / 25 := by
  obtain ⟨h8, -, -⟩ := b4_sqrt8
  refine ⟨⟨by norm_num, by norm_num, by norm_num [b4EU, b4pd, b4gd]⟩, by
    simp [b4Profit, b4pd]; norm_num, fun i vH vL hi h => ?_⟩
  have := b4_obs_bound (p := b4pd x) (g := b4gd) (i := i)
    (by fin_cases i <;> norm_num [b4pd, hx0.le])
    (by fin_cases i <;> norm_num [b4pd, hx1.le]) (by fin_cases i <;> norm_num [b4gd]) h
  fin_cases i
  · simp [b4pd, b4gd, h8] at this ⊢; linarith
  · exact absurd rfl hi
  · simp [b4pd, b4gd] at this ⊢; linarith

/-- **Exercise 14.B.4(d)**, unobservable effort (MWG, p. 507). For `x ∈ [99/100, 1)` the contract
`v_H = 13/5 + v_L`, `v_L = √8 - 13x/5` implements `e₁` with profit above `9/5`, while every contract
implementing `e₂` earns at most `9/5` and every contract implementing `e₃` at most `14/9`: every
optimal contract implements `e₁`, a higher effort than the observable optimum `e₂`. -/
theorem exercise_14_B_4d_unobs {x : ℝ} (hx0 : 99 / 100 ≤ x) (hx1 : x < 1) :
    b4Impl (b4pd x) b4gd 0 (Real.sqrt 8 - 13 * x / 5 + 13 / 5) (Real.sqrt 8 - 13 * x / 5) ∧
      9 / 5 < b4Profit (b4pd x) 0 (Real.sqrt 8 - 13 * x / 5 + 13 / 5) (Real.sqrt 8 - 13 * x / 5) ∧
      (∀ vH vL, b4Impl (b4pd x) b4gd 1 vH vL → b4Profit (b4pd x) 1 vH vL ≤ 9 / 5) ∧
      (∀ vH vL, b4Impl (b4pd x) b4gd 2 vH vL → b4Profit (b4pd x) 2 vH vL ≤ 14 / 9) := by
  obtain ⟨h8, hlo, hhi⟩ := b4_sqrt8
  set s := Real.sqrt 8
  refine ⟨⟨⟨by nlinarith, by nlinarith, ?_⟩, fun j => ?_⟩, ?_, fun vH vL h => ?_,
    fun vH vL h => ?_⟩
  · simp only [b4EU, b4pd, b4gd, Matrix.cons_val_zero]; nlinarith
  · fin_cases j <;> simp [b4EU, b4pd, b4gd, s] <;> nlinarith
  · simp only [b4Profit, b4pd, Matrix.cons_val_zero]; nlinarith
  · obtain ⟨⟨-, -, hp⟩, hic⟩ := h
    have h2 := hic 2
    simp [b4EU, b4pd, b4gd] at hp h2
    simp only [b4Profit, b4pd]
    norm_num
    nlinarith [sq_nonneg (vH + vL - 16 / 5), sq_nonneg (vH - vL - 8 / 5)]
  · have := b4_obs_bound (p := b4pd x) (g := b4gd) (i := 2) (by norm_num [b4pd])
      (by norm_num [b4pd]) (by norm_num [b4gd]) h.1
    simp [b4pd, b4gd] at this ⊢; linarith

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 14.B.2 and 14.B.3

MWG, p. 507.

* `exercise_14_B_2`: a strictly risk-averse owner with utility `U` of net profit. The first-order
  condition for the optimal scheme implementing `e_H` is
  `U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]`; with complementary slackness it is
  sufficient (the problem in utility levels is concave); its necessity is
  `exercise_14_B_2_necessary` (`HANecessity`).
* `exercise_14_B_3a`: with normally distributed profits (mean `e`, variance `σ²`) and a linear
  scheme `w = α + βπ`, the manager's mean-variance utility is `α + βe - φβ²σ² - g(e)`.
* `exercise_14_B_3b`: with observable effort the optimal linear contract has `β = 0`,
  `α = ū + g(e*)` and `g'(e*) = 1`.
* `exercise_14_B_3c`, `exercise_14_B_3c_beta`, `exercise_14_B_3c_sigma`: with unobservable effort
  the manager sets `g'(e) = β`; the owner's problem reduces to maximizing
  `e - g(e) - φσ² g'(e)² - ū`; at an interior optimum `β = 1/(1 + 2φσ² g''(e)) ∈ (0, 1)`; and a
  larger `σ²` gives a (weakly) smaller `β`.
-/

namespace MWG.PrincipalAgent

open MeasureTheory ProbabilityTheory Set

namespace HAModel

variable {ε : Type*}

/-- **Exercise 14.B.2** (MWG, p. 507). A risk-averse owner with a concave, nondecreasing,
differentiable utility `U` of net profit `π - w(π)`. If
`U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π` with `γ, μ ≥ 0` and
complementary slackness, then `w` maximizes the owner's expected utility among the schemes
implementing `e_H`. -/
theorem exercise_14_B_2 {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) {U dU : ℝ → ℝ} (hU : ConcaveOn ℝ univ U)
    (hdU : ∀ y, HasDerivAt U (dU y) y) (hdU0 : ∀ y, 0 ≤ dU y) {w : ℝ → ℝ} (hw : M.Adm w)
    {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, dU (x - w x) / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hcs1 : γ * (M.EU eH w - M.ubar) = 0) (hcs2 : μ * (M.EU eH w - M.EU eL w) = 0)
    (hUi : ∀ w', M.Adm w' → Integrable (fun x => U (x - w' x) * M.f eH x) M.ν)
    {w' : ℝ → ℝ} (hw' : M.HAFeasible eH w') :
    ∫ x, U (x - w' x) * M.f eH x ∂M.ν ≤ ∫ x, U (x - w x) * M.f eH x ∂M.ν := by
  have hii' := (ha_IC_two hE w').1 hw'.2
  have hi' := hw'.1.2
  have hpt : ∀ᵐ x ∂M.ν, U (x - w' x) * M.f eH x - U (x - w x) * M.f eH x ≤
      -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
        μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) := by
    filter_upwards [hfoc] with x hx
    have htanv := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have htanU := tpa_tangent_le hU (mem_univ (x - w x)) (mem_univ (x - w' x))
      (hdU (x - w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hH := hM.f_pos eH x
    have hr : M.f eL x / M.f eH x * M.f eH x = M.f eL x := div_mul_cancel₀ _ hH.ne'
    -- U(π - w') - U(π - w) ≤ U'(π - w)(w - w') ≤ -U'(π - w)(v(w') - v(w))/v'(w)
    have k1 : dU (x - w x) * (w x - w' x) ≤
        -(dU (x - w x) / M.dv (w x)) * (M.v (w' x) - M.v (w x)) := by
      have : M.v (w' x) - M.v (w x) ≤ M.dv (w x) * (w' x - w x) := by linarith
      have h2 : (M.v (w' x) - M.v (w x)) / M.dv (w x) ≤ w' x - w x := by
        rw [div_le_iff₀ hd]; linarith
      have h3 : dU (x - w x) / M.dv (w x) * (M.v (w' x) - M.v (w x)) ≤
          dU (x - w x) * (w' x - w x) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith [hdU0 (x - w x)]
      have e1 : dU (x - w x) * (w x - w' x) = -(dU (x - w x) * (w' x - w x)) := by ring
      have e2 : -(dU (x - w x) / M.dv (w x)) * (M.v (w' x) - M.v (w x)) =
          -(dU (x - w x) / M.dv (w x) * (M.v (w' x) - M.v (w x))) := by ring
      rw [e1, e2]; exact neg_le_neg h3
    rw [hx] at k1
    have k2 : U (x - w' x) - U (x - w x) ≤
        -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) := by
      have : (x - w' x) - (x - w x) = w x - w' x := by ring
      rw [this] at htanU; linarith
    have k3 := mul_le_mul_of_nonneg_right k2 hH.le
    have : -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) * M.f eH x =
        -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
          μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) := by
      have : -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) * M.f eH x =
          -((M.v (w' x) - M.v (w x)) * (γ * M.f eH x + μ * M.f eH x -
            μ * (M.f eL x / M.f eH x * M.f eH x))) := by ring
      rw [this, hr]; ring
    linarith
  have hiH : Integrable (fun x => (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x))
      M.ν := ((hw'.1.1.2 eH).2.sub (hw.2 eH).2).const_mul (γ + μ)
  have hiL : Integrable (fun x => μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) M.ν :=
    ((hw'.1.1.2 eL).2.sub (hw.2 eL).2).const_mul μ
  have hint : ∫ x, (U (x - w' x) * M.f eH x - U (x - w x) * M.f eH x) ∂M.ν ≤
      ∫ x, -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
        μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν :=
    integral_mono_ae ((hUi w' hw'.1.1).sub (hUi w hw)) (hiH.sub hiL).neg hpt
  rw [integral_neg, integral_sub hiH hiL, integral_const_mul, integral_const_mul,
    ha_EV_sub hw hw'.1.1, ha_EV_sub hw hw'.1.1, integral_sub (hUi w' hw'.1.1) (hUi w hw)] at hint
  unfold EU at hi' hii' hcs1 hcs2
  have h1 : 0 ≤ γ * (M.EV eH w' - M.g eH - M.ubar) := mul_nonneg hγ (by linarith)
  have h2 : 0 ≤ μ * (M.EV eH w' - M.g eH - (M.EV eL w' - M.g eL)) := mul_nonneg hμ (by linarith)
  nlinarith

end HAModel

/-- **Exercise 14.B.3(a)** (MWG, p. 507). If profits are normal with mean `e` and variance `σ²`,
the linear scheme `w = α + βπ` has mean `α + βe` and variance `β²σ²`, so the manager's utility
`E[w] - φ Var(w) - g(e)` is `α + βe - φβ²σ² - g(e)`. -/
theorem exercise_14_B_3a (α β e φ : ℝ) (σ2 : NNReal) (g : ℝ → ℝ) :
    (∫ x, (α + β * x) ∂gaussianReal e σ2) - φ * Var[fun x => α + β * x; gaussianReal e σ2] -
      g e = α + β * e - φ * β ^ 2 * σ2 - g e := by
  have hint : Integrable (fun x : ℝ => x) (gaussianReal e σ2) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [integral_add (integrable_const α) (hint.const_mul β), integral_const, integral_const_mul,
    integral_id_gaussianReal, variance_const_add (by fun_prop),
    variance_const_mul, variance_fun_id_gaussianReal]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Exercise 14.B.3(b)** (MWG, p. 507). With observable effort the owner maximizes
`e - (α + βe)` subject to `α + βe - φβ²σ² - g(e) ≥ ū` (`φσ² > 0`). If `g` is convex on `[0, ∞)` with
`g'(e*) = 1` at `e* ≥ 0`, the optimal contract is `e*`, `β = 0`, `α = ū + g(e*)`: every feasible
contract gives at most `e* - g(e*) - ū`, and only `β = 0` with a binding constraint and an effort
maximizing `e - g(e)` attains it. -/
theorem exercise_14_B_3b {g dg : ℝ → ℝ} (hg : ConvexOn ℝ (Ici 0) g)
    (hdg : ∀ e, 0 ≤ e → HasDerivWithinAt g (dg e) (Ici 0) e) {φσ2 ubar estar : ℝ}
    (hφ : 0 < φσ2) (hes : 0 ≤ estar) (hfoc : dg estar = 1) {e α β : ℝ} (he : 0 ≤ e)
    (hpart : ubar ≤ α + β * e - φσ2 * β ^ 2 - g e) :
    e - (α + β * e) ≤ estar - g estar - ubar ∧
      (e - (α + β * e) = estar - g estar - ubar → β = 0) := by
  have htan := tpa_tangent_ge_convex hg (mem_Ici.2 hes) (mem_Ici.2 he) (hdg estar hes)
  rw [hfoc] at htan
  have hb := sq_nonneg β
  refine ⟨by nlinarith, fun heq => ?_⟩
  have : φσ2 * β ^ 2 ≤ 0 := by nlinarith
  have : β ^ 2 = 0 := le_antisymm (by nlinarith) hb
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- **Exercise 14.B.3(c)** (MWG, p. 507), the manager's choice and the reduced problem. Under a
linear scheme with `β`, the manager's effort `e > 0` (maximizing `α + βe - φβ²σ² - g(e)`) satisfies
`g'(e) = β`; given this, the owner's profit with the participation constraint binding is
`e - g(e) - φσ² g'(e)² - ū`. -/
theorem exercise_14_B_3c {g dg : ℝ → ℝ} {φσ2 ubar α β e : ℝ} (he : 0 < e)
    (hdg : HasDerivAt g (dg e) e)
    (hopt : ∀ e', 0 ≤ e' → α + β * e' - φσ2 * β ^ 2 - g e' ≤ α + β * e - φσ2 * β ^ 2 - g e)
    (hbind : α + β * e - φσ2 * β ^ 2 - g e = ubar) :
    dg e = β ∧ e - (α + β * e) = e - g e - φσ2 * dg e ^ 2 - ubar := by
  have hloc : IsLocalMax (fun e' => α + β * e' - φσ2 * β ^ 2 - g e') e :=
    Filter.mem_of_superset (Ici_mem_nhds he) fun y hy => hopt y hy
  have hd : HasDerivAt (fun e' => α + β * e' - φσ2 * β ^ 2 - g e') (β * 1 - dg e) e :=
    ((((hasDerivAt_id e).const_mul β).const_add α).sub_const (φσ2 * β ^ 2)).sub hdg
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβ : dg e = β := by linarith
  refine ⟨hβ, ?_⟩
  rw [hβ]; linarith

/-- **Exercise 14.B.3(c)**, the optimal `β` (MWG, p. 507). If `e > 0` maximizes
`h(e) = e - g(e) - φσ² g'(e)² - ū` with `g'' > 0`, `g' ≥ 0` and `φσ² > 0`, then
`β = g'(e) = 1/(1 + 2φσ² g''(e))`, so `0 < β < 1` when `g''(e) > 0`. -/
theorem exercise_14_B_3c_beta {g dg d2g : ℝ → ℝ} {φσ2 ubar e : ℝ} (he : 0 < e) (hφ : 0 < φσ2)
    (hdg : HasDerivAt g (dg e) e) (hd2g : HasDerivAt dg (d2g e) e) (hd2 : 0 < d2g e)
    (hmax : ∀ e', 0 ≤ e' → e' - g e' - φσ2 * dg e' ^ 2 - ubar ≤ e - g e - φσ2 * dg e ^ 2 - ubar) :
    dg e = 1 / (1 + 2 * φσ2 * d2g e) ∧ 0 < dg e ∧ dg e < 1 := by
  have hloc : IsLocalMax (fun e' => e' - g e' - φσ2 * dg e' ^ 2 - ubar) e :=
    Filter.mem_of_superset (Ici_mem_nhds he) fun y hy => hmax y hy
  have hd : HasDerivAt (fun e' => e' - g e' - φσ2 * dg e' ^ 2 - ubar)
      (1 - dg e - φσ2 * (2 * dg e * d2g e)) e := by
    have h1 := ((hasDerivAt_id e).sub hdg).sub ((hd2g.pow 2).const_mul φσ2)
    have := h1.sub_const ubar
    convert this using 1
    all_goals norm_num
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hpos : 0 < 1 + 2 * φσ2 * d2g e := by positivity
  have heq : dg e = 1 / (1 + 2 * φσ2 * d2g e) := by
    rw [eq_div_iff hpos.ne']; linarith
  refine ⟨heq, by rw [heq]; positivity, ?_⟩
  rw [heq, div_lt_one hpos]; nlinarith

/-- **Exercise 14.B.3(c)**, the effect of `σ²` (MWG, p. 507). If `e₁` maximizes
`e - g(e) - φσ₁² g'(e)²` and `e₂` maximizes `e - g(e) - φσ₂² g'(e)²` with `σ₁² < σ₂²` and `g' ≥ 0`,
then the incentive intensities satisfy `β₂ = g'(e₂) ≤ β₁ = g'(e₁)`: more noise, weaker
incentives. -/
theorem exercise_14_B_3c_sigma {g dg : ℝ → ℝ} {k1 k2 e1 e2 : ℝ} (hk : k1 < k2)
    (hdg0 : ∀ e, 0 ≤ e → 0 ≤ dg e) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hm1 : ∀ e, 0 ≤ e → e - g e - k1 * dg e ^ 2 ≤ e1 - g e1 - k1 * dg e1 ^ 2)
    (hm2 : ∀ e, 0 ≤ e → e - g e - k2 * dg e ^ 2 ≤ e2 - g e2 - k2 * dg e2 ^ 2) :
    dg e2 ≤ dg e1 := by
  have a := hm1 e2 he2
  have b := hm2 e1 he1
  have hsq : dg e2 ^ 2 ≤ dg e1 ^ 2 := by nlinarith
  by_contra hc
  rw [not_le] at hc
  nlinarith [hdg0 e1 he1, hdg0 e2 he2]

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Necessity of the Kuhn-Tucker conditions in the hidden-action model

MWG, footnote 7 (p. 484), (14.B.10), Lemma 14.B.1, Exercise 14.B.2 (p. 507) and
(14.AA.2)-(14.AA.3) (p. 504).

Footnote 7 reformulates (14.B.9) as a convex program in the manager's utility levels
`v̂(π) = v(w(π))` and concludes that the Kuhn-Tucker conditions are necessary. Here this is proved
in the general model of `HiddenAction` (profits with a density with respect to an arbitrary
measure, measurable schemes with finite expected wage and utility):

* `ha_mix`: the scheme whose utility levels are the `t`-mixture of those of two schemes is
  admissible and pays at most the mixture of their wages (`v` concave): the program is
  convex-like in utility levels.
* `ha_piece_integral`, `ha_piece_adm`: changing a scheme to a constant on a measurable set.
* `ha_raise`: raising a scheme on a set of positive measure raises expected utilities strictly;
  with strict first-order stochastic dominance this gives a scheme satisfying (i) and (ii_H)
  strictly (`ha_slater`: Slater's condition).
* `ha_ae_min`: a scheme that cannot be improved by changing it to a constant on any measurable set
  minimizes the pointwise Lagrangian at almost every profit level.
* `ha_kt_general`: multipliers exist at every solution of a program with the constraints of
  (14.B.9) and any objective that is convex in utility levels (via `kt_convexlike`).
* `ha_kt_necessary`: **footnote 7**, the Kuhn-Tucker condition (14.B.10) with complementary
  slackness holds (almost everywhere) at every solution of (14.B.9) for `e = e_H`;
  `lemma_14_B_1_every`: in every solution both multipliers are positive.
* `exercise_14_B_2_necessary`: the same for a risk-averse owner.
* `foa_necessary`: **(14.AA.3)** holds at every solution of the relaxed program of the
  first-order approach (via `kt_convexlike_eq`).
* `inst_kt_necessary`, `inst_14_B_2_necessary`, `inst_foa_necessary`: proved instances.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

open Classical in
/-- Changing a function to the constant `q` on a measurable set `A`: integrability and the change
in the integral of `Ψ(π, w(π))`. -/
theorem ha_piece_integral {μ : Measure ℝ} {Ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (q : ℝ) (h1 : Integrable (fun x => Ψ x (w x)) μ)
    (h2 : Integrable (fun x => Ψ x q) μ) :
    Integrable (fun x => Ψ x (A.piecewise (fun _ => q) w x)) μ ∧
      ∫ x, Ψ x (A.piecewise (fun _ => q) w x) ∂μ - ∫ x, Ψ x (w x) ∂μ =
        ∫ x in A, (Ψ x q - Ψ x (w x)) ∂μ := by
  have heq : (fun x => Ψ x (A.piecewise (fun _ => q) w x)) =
      fun x => Ψ x (w x) + A.indicator (fun x => Ψ x q - Ψ x (w x)) x := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx]
  have hi : Integrable (fun x => A.indicator (fun x => Ψ x q - Ψ x (w x)) x) μ :=
    (h2.sub h1).indicator hA
  rw [heq]
  refine ⟨h1.add hi, ?_⟩
  rw [integral_add h1 hi, integral_indicator hA]
  ring

open Classical in
/-- A scheme changed to a constant on a measurable set is admissible. -/
theorem ha_piece_adm {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) {A : Set ℝ}
    (hA : MeasurableSet A) (q : ℝ) : M.Adm (A.piecewise (fun _ => q) w) :=
  ⟨Measurable.piecewise hA measurable_const hw.1, fun e =>
    ⟨(ha_piece_integral (Ψ := fun x c => c * M.f e x) hA q (hw.2 e).1
      ((hM.f_int e).const_mul q)).1,
     (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA q (hw.2 e).2
      ((hM.f_int e).const_mul _)).1⟩⟩

/-- **Footnote 7** (MWG, p. 484): the program is convex in utility levels. For admissible `w₀`,
`w₁` and `t ∈ [0, 1]` there is an admissible scheme `W` with
`v(W(π)) = (1 - t) v(w₀(π)) + t v(w₁(π))` at every `π`, and (as `v` is concave)
`W(π) ≤ (1 - t) w₀(π) + t w₁(π)`. -/
theorem ha_mix {M : HAModel ε} (hM : M.Standing) {w0 w1 : ℝ → ℝ} (hw0 : M.Adm w0)
    (hw1 : M.Adm w1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ W, M.Adm W ∧ (∀ x, M.v (W x) = (1 - t) * M.v (w0 x) + t * M.v (w1 x)) ∧
      ∀ x, W x ≤ (1 - t) * w0 x + t * w1 x := by
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hmono := ha_v_strictMono hM
  have hex : ∀ x, ∃ c, c ∈ Icc (min (w0 x) (w1 x)) (max (w0 x) (w1 x)) ∧
      M.v c = (1 - t) * M.v (w0 x) + t * M.v (w1 x) := by
    intro x
    have hmem : (1 - t) * M.v (w0 x) + t * M.v (w1 x) ∈
        Icc (M.v (min (w0 x) (w1 x))) (M.v (max (w0 x) (w1 x))) := by
      have a1 := hmono.monotone (min_le_left (w0 x) (w1 x))
      have a2 := hmono.monotone (min_le_right (w0 x) (w1 x))
      have a3 := hmono.monotone (le_max_left (w0 x) (w1 x))
      have a4 := hmono.monotone (le_max_right (w0 x) (w1 x))
      constructor <;> nlinarith
    exact intermediate_value_Icc min_le_max hvc.continuousOn hmem
  choose W hWI hWv using hex
  have hmixm : Measurable fun x => (1 - t) * M.v (w0 x) + t * M.v (w1 x) :=
    ((hvc.measurable.comp hw0.1).const_mul _).add ((hvc.measurable.comp hw1.1).const_mul _)
  have hWm : Measurable W := by
    refine measurable_of_Iic fun c => ?_
    have : W ⁻¹' Iic c = {x | (1 - t) * M.v (w0 x) + t * M.v (w1 x) ≤ M.v c} := by
      ext x
      change W x ≤ c ↔ (1 - t) * M.v (w0 x) + t * M.v (w1 x) ≤ M.v c
      rw [← hWv x]
      exact hmono.le_iff_le.symm
    rw [this]
    exact measurableSet_le hmixm measurable_const
  refine ⟨W, ⟨hWm, fun e => ⟨?_, ?_⟩⟩, hWv, fun x => ?_⟩
  · refine Integrable.mono' (((hw0.2 e).1.norm).add ((hw1.2 e).1.norm))
      (hWm.mul (hM.f_meas e)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hf := hM.f_pos e x
    change ‖W x * M.f e x‖ ≤ ‖w0 x * M.f e x‖ + ‖w1 x * M.f e x‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hf]
    have hb : |W x| ≤ |w0 x| + |w1 x| := by
      obtain ⟨h1, h2⟩ := hWI x
      rw [abs_le]
      constructor
      · exact le_trans (le_min (by linarith [neg_abs_le (w0 x), abs_nonneg (w1 x)])
          (by linarith [neg_abs_le (w1 x), abs_nonneg (w0 x)])) h1
      · exact h2.trans (max_le (by linarith [le_abs_self (w0 x), abs_nonneg (w1 x)])
          (by linarith [le_abs_self (w1 x), abs_nonneg (w0 x)]))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hb hf.le
  · have : (fun x => M.v (W x) * M.f e x) =
        fun x => (1 - t) * (M.v (w0 x) * M.f e x) + t * (M.v (w1 x) * M.f e x) := by
      funext x; rw [hWv x]; ring
    rw [this]
    exact ((hw0.2 e).2.const_mul _).add ((hw1.2 e).2.const_mul _)
  · have hc := hM.v_conc.2 (mem_univ (w0 x)) (mem_univ (w1 x)) (by linarith : 0 ≤ 1 - t) ht0
      (by ring)
    simp only [smul_eq_mul] at hc
    rw [← hWv x] at hc
    exact hmono.le_iff_le.1 hc

/-- Expected utilities of income are linear along the mixtures of `ha_mix`. -/
theorem ha_EV_mix {M : HAModel ε} {w0 w1 W : ℝ → ℝ} (hw0 : M.Adm w0) (hw1 : M.Adm w1) {t : ℝ}
    (hW : ∀ x, M.v (W x) = (1 - t) * M.v (w0 x) + t * M.v (w1 x)) (e : ε) :
    M.EV e W = (1 - t) * M.EV e w0 + t * M.EV e w1 := by
  unfold EV
  have : (fun x => M.v (W x) * M.f e x) =
      fun x => (1 - t) * (M.v (w0 x) * M.f e x) + t * (M.v (w1 x) * M.f e x) := by
    funext x; rw [hW x]; ring
  rw [this, integral_add ((hw0.2 e).2.const_mul _) ((hw1.2 e).2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- A set integral of a function positive on a set of positive measure is positive. -/
theorem ha_setIntegral_pos {μ : Measure ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hAμ : μ A ≠ 0)
    {k : ℝ → ℝ} (hk : IntegrableOn k A μ) (hpos : ∀ x ∈ A, 0 < k x) :
    0 < ∫ x in A, k x ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem hA fun x hx => (hpos x hx).le) hk]
  refine lt_of_lt_of_le (pos_iff_ne_zero.2 hAμ) (measure_mono fun x hx => ⟨?_, hx⟩)
  exact (hpos x hx).ne'

/-- Raising a scheme on a set `B` of positive measure. Given a weight `k` positive on `B`, there is
an admissible scheme with strictly higher expected utility of income under every effort and a
strictly higher `∫ v(w(π)) k(π) dπ`. -/
theorem ha_raise {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) {B : Set ℝ}
    (hB : MeasurableSet B) (hBν : M.ν B ≠ 0) {k : ℝ → ℝ}
    (hk : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * k x) M.ν)
    (hkpos : ∀ x ∈ B, 0 < k x) :
    ∃ w', M.Adm w' ∧ (∀ e, M.EV e w < M.EV e w') ∧
      ∫ x, M.v (w x) * k x ∂M.ν < ∫ x, M.v (w' x) * k x ∂M.ν := by
  have hU : B = ⋃ n : ℕ, B ∩ {x | w x ≤ n} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (w x)
      exact ⟨n, h, hn⟩
    · rintro ⟨n, h, -⟩
      exact h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M.ν (B ∩ {x | w x ≤ n}) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hBν (hU ▸ measure_iUnion_null hc)
  set A := B ∩ {x | w x ≤ n}
  have hA : MeasurableSet A := hB.inter (measurableSet_le hw.1 measurable_const)
  have hlt : ∀ x ∈ A, M.v (w x) < M.v ((n : ℝ) + 1) := fun x hx =>
    ha_v_strictMono hM (lt_of_le_of_lt hx.2 (by linarith))
  refine ⟨_, ha_piece_adm hM hw hA ((n : ℝ) + 1), fun e => ?_, ?_⟩
  · have h := (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA ((n : ℝ) + 1) (hw.2 e).2
      ((hM.f_int e).const_mul _)).2
    have hp : 0 < ∫ x in A, (M.v ((n : ℝ) + 1) * M.f e x - M.v (w x) * M.f e x) ∂M.ν :=
      ha_setIntegral_pos hA hn (((hM.f_int e).const_mul _).sub (hw.2 e).2).integrableOn
        fun x hx => by nlinarith [hlt x hx, hM.f_pos e x]
    unfold EV
    linarith
  · have h := (ha_piece_integral (Ψ := fun x c => M.v c * k x) hA ((n : ℝ) + 1)
      (hk w hw) (hk _ (ha_const_adm hM _))).2
    have hp : 0 < ∫ x in A, (M.v ((n : ℝ) + 1) * k x - M.v (w x) * k x) ∂M.ν :=
      ha_setIntegral_pos hA hn ((hk _ (ha_const_adm hM _)).sub (hk w hw)).integrableOn
        fun x hx => by nlinarith [hlt x hx, hkpos x hx.1]
    linarith

/-- **Slater's condition for (14.B.9)**. With strict first-order stochastic dominance, every
admissible scheme can be raised to one with strictly higher `EU(e_H)` and strictly higher
`EU(e_H) - EU(e_L)`; in particular, if (i) and (ii_H) hold, a scheme satisfying both strictly
exists. -/
theorem ha_slater {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL)
    {w : ℝ → ℝ} (hw : M.Adm w) :
    ∃ w', M.Adm w' ∧ M.EU eH w < M.EU eH w' ∧
      M.EU eH w - M.EU eL w < M.EU eH w' - M.EU eL w' := by
  have hpos : M.ν {x | M.f eL x < M.f eH x} ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂M.ν, 0 ≤ M.f eL x - M.f eH x := by
      rw [ae_iff]
      convert h0 using 2
      ext x
      simp [sub_nonneg, not_le]
    have hint : ∫ x, (M.f eL x - M.f eH x) ∂M.ν = 0 := by
      rw [integral_sub (hM.f_int eL) (hM.f_int eH), hM.f_one, hM.f_one, sub_self]
    have h0' := (integral_eq_zero_iff_of_nonneg_ae hae ((hM.f_int eL).sub (hM.f_int eH))).1 hint
    have h2 : ∀ᵐ x ∂M.ν, ¬ (M.f eH x < M.f eL x) := by
      filter_upwards [h0'] with x hx
      simp only [Pi.zero_apply] at hx
      linarith
    exact ha_fosd_set hM hfosd (by rw [ae_iff] at h2; simpa using h2)
  have hk : ∀ w', M.Adm w' →
      Integrable (fun x => M.v (w' x) * (M.f eH x - M.f eL x)) M.ν := fun w' hw' => by
    have := (hw'.2 eH).2.sub (hw'.2 eL).2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  obtain ⟨w', hw', hEV, hk'⟩ := ha_raise hM hw (measurableSet_lt (hM.f_meas eL) (hM.f_meas eH))
    hpos hk fun x hx => sub_pos.2 hx
  have hD : ∀ u, M.Adm u → ∫ x, M.v (u x) * (M.f eH x - M.f eL x) ∂M.ν = M.EV eH u - M.EV eL u :=
    fun u hu => by
      unfold EV
      rw [← integral_sub (hu.2 eH).2 (hu.2 eL).2]
      congr 1; funext x; ring
  rw [hD w hw, hD w' hw'] at hk'
  refine ⟨w', hw', ?_, ?_⟩ <;> unfold EU
  · linarith [hEV eH]
  · linarith

/-- A scheme `w` that cannot be improved, in the integral of a Lagrangian `ℓ(π, w(π))`, by changing
it to a constant on a measurable set minimizes `ℓ(π, ·)` at almost every `π`. -/
theorem ha_ae_min {μ : Measure ℝ} {ℓ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} (hc : ∀ x, Continuous (ℓ x))
    (hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) μ)
    (hA : ∀ A, MeasurableSet A → ∀ q, 0 ≤ ∫ x in A, (ℓ x q - ℓ x (w x)) ∂μ) :
    ∀ᵐ x ∂μ, ∀ c, ℓ x (w x) ≤ ℓ x c := by
  have h : ∀ q : ℚ, ∀ᵐ x ∂μ, 0 ≤ ℓ x q - ℓ x (w x) := fun q =>
    ae_nonneg_of_forall_setIntegral_nonneg (hint q) fun s hs _ => hA s hs q
  filter_upwards [ae_all_iff.2 h] with x hx c
  refine Rat.denseRange_cast.induction_on c (isClosed_le continuous_const (hc x)) fun q => ?_
  linarith [hx q]

/-- **Footnote 7** (MWG, p. 484), general form. Two effort levels with strict first-order
stochastic dominance; an objective `∫ φ(π, w(π)) dπ` that is convex in utility levels (`hφconv`).
At every `w` minimizing it subject to (i) and (ii_H) there are multipliers `γ, μ ≥ 0` with
complementary slackness such that, at almost every `π`, `w(π)` minimizes the pointwise Lagrangian
`c ↦ φ(π, c) - (γ + μ) v(c) f(π|e_H) + μ v(c) f(π|e_L)`. -/
theorem ha_kt_general {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (φ : ℝ → ℝ → ℝ)
    (hφi : ∀ w', M.Adm w' → Integrable (fun x => φ x (w' x)) M.ν)
    (hφc : ∀ x, Continuous (φ x))
    (hφconv : ∀ x a b c t, 0 ≤ t → t ≤ 1 → c ≤ (1 - t) * a + t * b →
      φ x c ≤ (1 - t) * φ x a + t * φ x b)
    {w : ℝ → ℝ} (hw : M.HAFeasible eH w)
    (hopt : ∀ w', M.HAFeasible eH w' → ∫ x, φ x (w x) ∂M.ν ≤ ∫ x, φ x (w' x) ∂M.ν) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, ∀ c, φ x (w x) - (γ + μ) * (M.v (w x) * M.f eH x) +
        μ * (M.v (w x) * M.f eL x) ≤
        φ x c - (γ + μ) * (M.v c * M.f eH x) + μ * (M.v c * M.f eL x) := by
  classical
  let X := {u : ℝ → ℝ // M.Adm u}
  let J : X → ℝ := fun u => ∫ x, φ x (u.1 x) ∂M.ν
  let G : Fin 2 → X → ℝ := ![fun u => M.ubar - M.EU eH u.1, fun u => M.EU eL u.1 - M.EU eH u.1]
  have hii := (ha_IC_two hE w).1 hw.2
  obtain ⟨lam, hlam, hcs, hlag⟩ := kt_convexlike J G ⟨w, hw.1.1⟩
    (Fin.forall_fin_two.2 ⟨by simp [G]; linarith [hw.1.2], by simp [G]; linarith⟩)
    (fun u hu => by
      have h0 := hu 0
      have h1 := hu 1
      simp only [G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
      exact hopt u.1 ⟨⟨u.2, by linarith⟩, (ha_IC_two hE u.1).2 (by linarith)⟩)
    (fun u0 u1 t ht0 ht1 => by
      obtain ⟨W, hW, hWv, hWle⟩ := ha_mix hM u0.2 u1.2 ht0 ht1
      refine ⟨⟨W, hW⟩, ?_, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · change ∫ x, φ x (W x) ∂M.ν ≤ (1 - t) * (∫ x, φ x (u0.1 x) ∂M.ν) +
          t * ∫ x, φ x (u1.1 x) ∂M.ν
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((hφi _ u0.2).const_mul _) ((hφi _ u1.2).const_mul _)]
        exact integral_mono (hφi _ hW)
          (((hφi _ u0.2).const_mul _).add ((hφi _ u1.2).const_mul _))
          fun x => hφconv x _ _ _ t ht0 ht1 (hWle x)
      · simp only [G, Matrix.cons_val_zero]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv]
        nlinarith
      · simp only [G, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv, ha_EV_mix u0.2 u1.2 hWv]
        nlinarith)
    (by
      obtain ⟨w', hw', h1, h2⟩ := ha_slater hM hfosd hw.1.1
      refine ⟨⟨w', hw'⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · simp only [G, Matrix.cons_val_zero]; linarith [hw.1.2]
      · simp only [G, Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith)
  set γ := lam 0
  set μ := lam 1
  have hcs0 : γ * (M.ubar - M.EU eH w) = 0 := hcs 0
  have hcs1 : μ * (M.EU eL w - M.EU eH w) = 0 := hcs 1
  have hlag' : ∀ u : ℝ → ℝ, M.Adm u → ∫ x, φ x (w x) ∂M.ν ≤ ∫ x, φ x (u x) ∂M.ν +
      γ * (M.ubar - M.EU eH u) + μ * (M.EU eL u - M.EU eH u) := by
    intro u hu
    have := hlag ⟨u, hu⟩
    simp only [Fin.sum_univ_two, G, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, J] at this
    linarith
  refine ⟨γ, μ, hlam 0, hlam 1, by linear_combination -hcs0, by linear_combination -hcs1, ?_⟩
  let ℓ : ℝ → ℝ → ℝ := fun x c =>
    φ x c - (γ + μ) * (M.v c * M.f eH x) + μ * (M.v c * M.f eL x)
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hVi : ∀ e q, Integrable (fun x => M.v q * M.f e x) M.ν := fun e q =>
    (hM.f_int e).const_mul _
  have hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) M.ν := by
    intro q
    exact ((((hφi _ (ha_const_adm hM q)).sub ((hVi eH q).const_mul _)).add
      ((hVi eL q).const_mul _)).sub (((hφi _ hw.1.1).sub ((hw.1.1.2 eH).2.const_mul _)).add
      ((hw.1.1.2 eL).2.const_mul _)))
  refine ha_ae_min (ℓ := ℓ) (fun x => ?_) hint fun A hA q => ?_
  · exact ((hφc x).sub (continuous_const.mul (hvc.mul continuous_const))).add
      (continuous_const.mul (hvc.mul continuous_const))
  · have hu := ha_piece_adm hM hw.1.1 hA q
    have h0 : ∫ x, φ x (A.piecewise (fun _ => q) w x) ∂M.ν - ∫ x, φ x (w x) ∂M.ν =
        ∫ x in A, (φ x q - φ x (w x)) ∂M.ν :=
      (ha_piece_integral hA q (hφi _ hw.1.1) (hφi _ (ha_const_adm hM q))).2
    have hH : M.EV eH (A.piecewise (fun _ => q) w) - M.EV eH w =
        ∫ x in A, (M.v q * M.f eH x - M.v (w x) * M.f eH x) ∂M.ν :=
      (ha_piece_integral (Ψ := fun x c => M.v c * M.f eH x) hA q (hw.1.1.2 eH).2 (hVi eH q)).2
    have hL : M.EV eL (A.piecewise (fun _ => q) w) - M.EV eL w =
        ∫ x in A, (M.v q * M.f eL x - M.v (w x) * M.f eL x) ∂M.ν :=
      (ha_piece_integral (Ψ := fun x c => M.v c * M.f eL x) hA q (hw.1.1.2 eL).2 (hVi eL q)).2
    have hl := hlag' _ hu
    have I1 : IntegrableOn (fun x => φ x q - φ x (w x)) A M.ν :=
      ((hφi _ (ha_const_adm hM q)).sub (hφi _ hw.1.1)).integrableOn
    have I2 : IntegrableOn (fun x => (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x))
        A M.ν := (((hVi eH q).sub (hw.1.1.2 eH).2).const_mul (γ + μ)).integrableOn
    have I3 : IntegrableOn (fun x => μ * (M.v q * M.f eL x - M.v (w x) * M.f eL x)) A M.ν :=
      (((hVi eL q).sub (hw.1.1.2 eL).2).const_mul μ).integrableOn
    have I12 : IntegrableOn (fun x => (φ x q - φ x (w x)) -
        (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x)) A M.ν := I1.sub I2
    have e1 : ∫ x in A, (ℓ x q - ℓ x (w x)) ∂M.ν =
        ∫ x in A, ((φ x q - φ x (w x)) -
          (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x) +
          μ * (M.v q * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν := by
      congr 1; funext x; simp only [ℓ]; ring
    rw [e1, integral_add I12 I3, integral_sub I1 I2, integral_const_mul,
      integral_const_mul, ← h0, ← hH, ← hL]
    unfold EU at hl hcs0 hcs1
    nlinarith

/-- **Footnote 7 and (14.B.10)** (MWG, p. 484): necessity of the Kuhn-Tucker conditions. Two
effort levels, `F(·|e_H)` strictly first-order stochastically dominates `F(·|e_L)`. At every
solution `w` of (14.B.9) for `e = e_H` there are multipliers `γ, μ ≥ 0` with complementary
slackness such that `1 / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π`. -/
theorem ha_kt_necessary {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) {w : ℝ → ℝ}
    (hw : M.IsHACostMin eH w) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  obtain ⟨γ, μ, hγ, hμ, h1, h2, hmin⟩ := ha_kt_general hM hE hfosd (fun x c => c * M.f eH x)
    (fun w' hw' => (hw'.2 eH).1) (fun x => continuous_id.mul continuous_const)
    (fun x a b c t _ _ hc => by nlinarith [hM.f_pos eH x]) hw.1 (fun w' hw' => hw.2 w' hw')
  refine ⟨γ, μ, hγ, hμ, h1, h2, ?_⟩
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => c * M.f eH x - (γ + μ) * (M.v c * M.f eH x) +
      μ * (M.v c * M.f eL x)) (1 * M.f eH x - (γ + μ) * (M.dv (w x) * M.f eH x) +
      μ * (M.dv (w x) * M.f eL x)) (w x) :=
    (((hasDerivAt_id' (w x)).mul_const _).sub (((hM.v_deriv _).mul_const _).const_mul _)).add
      (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos eH x
  field_simp
  linarith

/-- **Lemma 14.B.1** (MWG, p. 484), as stated: in *any* solution of (14.B.9) with `e = e_H` the
Kuhn-Tucker multipliers exist and both are positive (strict first-order stochastic dominance,
`g(e_H) > g(e_L)`, `v'` strictly decreasing). -/
theorem lemma_14_B_1_every {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (hg : M.g eL < M.g eH)
    (hda : StrictAnti M.dv) {w : ℝ → ℝ} (hw : M.IsHACostMin eH w) :
    ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  obtain ⟨γ, μ, hγ, hμ, -, -, hfoc⟩ := ha_kt_necessary hM hE hfosd hw
  obtain ⟨h1, h2⟩ := lemma_14_B_1 hM hfosd hg hda ((ha_IC_two hE w).1 hw.1.2) hγ hμ hfoc
  exact ⟨γ, μ, h1, h2, hfoc⟩

/-- **Exercise 14.B.2** (MWG, p. 507), necessity. A risk-averse owner with a concave,
nondecreasing, differentiable utility `U` of net profit (strict first-order stochastic dominance,
two efforts). At every scheme `w` maximizing the owner's expected utility
`∫ U(π - w(π)) f(π|e_H) dπ` subject to (i) and (ii_H), there are multipliers `γ, μ ≥ 0` with
complementary slackness such that
`U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π`. -/
theorem exercise_14_B_2_necessary {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) {U dU : ℝ → ℝ}
    (hU : ConcaveOn ℝ univ U) (hdU : ∀ y, HasDerivAt U (dU y) y) (hdU0 : ∀ y, 0 ≤ dU y)
    (hUi : ∀ w', M.Adm w' → Integrable (fun x => U (x - w' x) * M.f eH x) M.ν)
    {w : ℝ → ℝ} (hw : M.HAFeasible eH w)
    (hopt : ∀ w', M.HAFeasible eH w' →
      ∫ x, U (x - w' x) * M.f eH x ∂M.ν ≤ ∫ x, U (x - w x) * M.f eH x ∂M.ν) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, dU (x - w x) / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  have hUm : Monotone U := monotone_of_deriv_nonneg (fun y => (hdU y).differentiableAt)
    (fun y => (hdU y).deriv ▸ hdU0 y)
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun y => (hdU y).continuousAt
  obtain ⟨γ, μ, hγ, hμ, h1, h2, hmin⟩ := ha_kt_general hM hE hfosd
    (fun x c => -(U (x - c) * M.f eH x)) (fun w' hw' => (hUi w' hw').neg)
    (fun x => ((hUc.comp (continuous_const.sub continuous_id)).mul continuous_const).neg)
    (fun x a b c t ht0 ht1 hc => by
      have hf := hM.f_pos eH x
      have hmo : U (x - ((1 - t) * a + t * b)) ≤ U (x - c) := hUm (by linarith)
      have hcv := hU.2 (mem_univ (x - a)) (mem_univ (x - b)) (by linarith : 0 ≤ 1 - t) ht0
        (by ring)
      simp only [smul_eq_mul] at hcv
      have : (1 - t) * (x - a) + t * (x - b) = x - ((1 - t) * a + t * b) := by ring
      rw [this] at hcv
      nlinarith)
    hw (fun w' hw' => by
      rw [integral_neg, integral_neg]; linarith [hopt w' hw'])
  refine ⟨γ, μ, hγ, hμ, h1, h2, ?_⟩
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => -(U (x - c) * M.f eH x) - (γ + μ) * (M.v c * M.f eH x) +
      μ * (M.v c * M.f eL x)) (-(dU (x - w x) * -1 * M.f eH x) -
      (γ + μ) * (M.dv (w x) * M.f eH x) + μ * (M.dv (w x) * M.f eL x)) (w x) :=
    ((((hdU (x - w x)).comp (w x) ((hasDerivAt_id' (w x)).const_sub x)).mul_const _).neg.sub
      (((hM.v_deriv _).mul_const _).const_mul _)).add (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos eH x
  field_simp
  linarith

/-- **(14.AA.2)-(14.AA.3)** (MWG, p. 504), necessity. The relaxed program of the first-order
approach: minimize `∫ w f(·|e)` over admissible schemes subject to participation and the
manager's first-order condition `∫ v(w(π)) f_e(π|e) dπ = g'(e)`. Suppose `f_e` is measurable, the
integrals exist, and `f_e` is positive on a set of positive measure and negative on another (as for
the derivative of a family of densities that is not constant). Then at every solution there are
`λ ≥ 0` (with complementary slackness) and `μ` such that
`1 / v'(w(π)) = λ + μ f_e(π|e)/f(π|e)` at almost every `π`. -/
theorem foa_necessary {M : HAModel ε} (hM : M.Standing) {e : ε} {fe : ℝ → ℝ} {dg : ℝ}
    (hfem : Measurable fe)
    (hfe : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * fe x) M.ν)
    (hpos : M.ν {x | 0 < fe x} ≠ 0) (hneg : M.ν {x | fe x < 0} ≠ 0)
    {w : ℝ → ℝ} (hw : M.Adm w) (hpart : M.ubar ≤ M.EU e w)
    (hfoa : ∫ x, M.v (w x) * fe x ∂M.ν = dg)
    (hopt : ∀ w', M.Adm w' → M.ubar ≤ M.EU e w' → ∫ x, M.v (w' x) * fe x ∂M.ν = dg →
      M.EW e w ≤ M.EW e w') :
    ∃ lam μ : ℝ, 0 ≤ lam ∧ lam * (M.EU e w - M.ubar) = 0 ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = lam + μ * (fe x / M.f e x) := by
  classical
  let X := {u : ℝ → ℝ // M.Adm u}
  let J : X → ℝ := fun u => M.EW e u.1
  let G : Fin 1 → X → ℝ := fun _ u => M.ubar - M.EU e u.1
  let H : X → ℝ := fun u => ∫ x, M.v (u.1 x) * fe x ∂M.ν - dg
  obtain ⟨wp, hwp, hEVp, hHp⟩ :=
    ha_raise hM hw (measurableSet_lt measurable_const hfem) hpos hfe fun x hx => hx
  have hfe' : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * -fe x) M.ν :=
    fun w' hw' => by
      refine (hfe w' hw').neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]; ring
  obtain ⟨wm, hwm, hEVm, hHm⟩ :=
    ha_raise hM hw (measurableSet_lt hfem measurable_const) hneg (k := fun x => -fe x) hfe'
      fun x hx => neg_pos.2 hx
  simp only [mul_neg, integral_neg] at hHm
  have hmixH : ∀ u0 u1 : ℝ → ℝ, M.Adm u0 → M.Adm u1 → ∀ (W : ℝ → ℝ) (t : ℝ),
      (∀ x, M.v (W x) = (1 - t) * M.v (u0 x) + t * M.v (u1 x)) →
      ∫ x, M.v (W x) * fe x ∂M.ν =
        (1 - t) * ∫ x, M.v (u0 x) * fe x ∂M.ν + t * ∫ x, M.v (u1 x) * fe x ∂M.ν := by
    intro u0 u1 hu0 hu1 W t hW
    have : (fun x => M.v (W x) * fe x) =
        fun x => (1 - t) * (M.v (u0 x) * fe x) + t * (M.v (u1 x) * fe x) := by
      funext x; rw [hW x]; ring
    rw [this, integral_add ((hfe _ hu0).const_mul _) ((hfe _ hu1).const_mul _),
      integral_const_mul, integral_const_mul]
  obtain ⟨lam, ν0, hlam, hcs, hlag⟩ := kt_convexlike_eq J G H ⟨w, hw⟩
    (fun _ => by simp only [G]; linarith) (by simp only [H, hfoa, sub_self])
    (fun u hu hHu => hopt u.1 u.2 (by linarith [hu 0]) (by simp only [H] at hHu; linarith))
    (fun u0 u1 t ht0 ht1 => by
      obtain ⟨W, hW, hWv, hWle⟩ := ha_mix hM u0.2 u1.2 ht0 ht1
      refine ⟨⟨W, hW⟩, ?_, fun _ => ?_, ?_⟩
      · change M.EW e W ≤ (1 - t) * M.EW e u0.1 + t * M.EW e u1.1
        unfold EW
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add (((u0.2).2 e).1.const_mul _) (((u1.2).2 e).1.const_mul _)]
        refine integral_mono (hW.2 e).1 ((((u0.2).2 e).1.const_mul _).add
          (((u1.2).2 e).1.const_mul _)) fun x => ?_
        have hf := hM.f_pos e x
        have := mul_le_mul_of_nonneg_right (hWle x) hf.le
        simp only
        linarith
      · simp only [G]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv]
        nlinarith
      · simp only [H]
        rw [hmixH _ _ u0.2 u1.2 W t hWv]
        ring)
    (xp := ⟨wp, hwp⟩) (xm := ⟨wm, hwm⟩)
    (fun _ => by have h := hpart; simp only [G]; unfold EU at h ⊢; linarith [hEVp e])
    (fun _ => by have h := hpart; simp only [G]; unfold EU at h ⊢; linarith [hEVm e])
    (by simp only [H]; linarith) (by simp only [H]; linarith)
  set lam0 := lam 0
  have hcs0 : lam0 * (M.ubar - M.EU e w) = 0 := hcs 0
  have hlag' : ∀ u : ℝ → ℝ, M.Adm u → M.EW e w ≤ M.EW e u +
      lam0 * (M.ubar - M.EU e u) + ν0 * (∫ x, M.v (u x) * fe x ∂M.ν - dg) := by
    intro u hu
    have := hlag ⟨u, hu⟩
    simp only [Fin.sum_univ_one, J, G, H] at this
    linarith
  refine ⟨lam0, -ν0, hlam 0, by linear_combination -hcs0, ?_⟩
  let ℓ : ℝ → ℝ → ℝ := fun x c =>
    c * M.f e x - lam0 * (M.v c * M.f e x) + ν0 * (M.v c * fe x)
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hVi : ∀ q, Integrable (fun x => M.v q * M.f e x) M.ν := fun q =>
    (hM.f_int e).const_mul _
  have hWi : ∀ q, Integrable (fun x => q * M.f e x) M.ν := fun q => (hM.f_int e).const_mul _
  have hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) M.ν := by
    intro q
    exact ((((hWi q).sub ((hVi q).const_mul _)).add
      ((hfe _ (ha_const_adm hM q)).const_mul _)).sub
      ((((hw.2 e).1).sub (((hw.2 e).2).const_mul _)).add ((hfe w hw).const_mul _)))
  have hmin : ∀ᵐ x ∂M.ν, ∀ c, ℓ x (w x) ≤ ℓ x c := by
    refine ha_ae_min (ℓ := ℓ) (fun x => ?_) hint fun A hA q => ?_
    · exact ((continuous_id.mul continuous_const).sub
        (continuous_const.mul (hvc.mul continuous_const))).add
        (continuous_const.mul (hvc.mul continuous_const))
    · have hu := ha_piece_adm hM hw hA q
      have h0 : M.EW e (A.piecewise (fun _ => q) w) - M.EW e w =
          ∫ x in A, (q * M.f e x - w x * M.f e x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => c * M.f e x) hA q (hw.2 e).1 (hWi q)).2
      have hV : M.EV e (A.piecewise (fun _ => q) w) - M.EV e w =
          ∫ x in A, (M.v q * M.f e x - M.v (w x) * M.f e x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA q (hw.2 e).2 (hVi q)).2
      have hF : ∫ x, M.v (A.piecewise (fun _ => q) w x) * fe x ∂M.ν -
          ∫ x, M.v (w x) * fe x ∂M.ν = ∫ x in A, (M.v q * fe x - M.v (w x) * fe x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => M.v c * fe x) hA q (hfe w hw)
          (hfe _ (ha_const_adm hM q))).2
      have hl := hlag' _ hu
      have I1 : IntegrableOn (fun x => q * M.f e x - w x * M.f e x) A M.ν :=
        ((hWi q).sub (hw.2 e).1).integrableOn
      have I2 : IntegrableOn (fun x => lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x)) A M.ν :=
        (((hVi q).sub (hw.2 e).2).const_mul _).integrableOn
      have I3 : IntegrableOn (fun x => ν0 * (M.v q * fe x - M.v (w x) * fe x)) A M.ν :=
        (((hfe _ (ha_const_adm hM q)).sub (hfe w hw)).const_mul _).integrableOn
      have I12 : IntegrableOn (fun x => (q * M.f e x - w x * M.f e x) -
          lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x)) A M.ν := I1.sub I2
      have e1 : ∫ x in A, (ℓ x q - ℓ x (w x)) ∂M.ν =
          ∫ x in A, ((q * M.f e x - w x * M.f e x) -
            lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x) +
            ν0 * (M.v q * fe x - M.v (w x) * fe x)) ∂M.ν := by
        congr 1; funext x; simp only [ℓ]; ring
      rw [e1, integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul,
        ← h0, ← hV, ← hF, hfoa]
      unfold EU at hl hcs0
      nlinarith
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => c * M.f e x - lam0 * (M.v c * M.f e x) +
      ν0 * (M.v c * fe x)) (1 * M.f e x - lam0 * (M.dv (w x) * M.f e x) +
      ν0 * (M.dv (w x) * fe x)) (w x) :=
    (((hasDerivAt_id' (w x)).mul_const _).sub (((hM.v_deriv _).mul_const _).const_mul _)).add
      (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos e x
  field_simp
  linarith

end HAModel

/-- **Footnote 7, an instance** (MWG, p. 484). In `exA` the optimal scheme `exW` (Figure 14.B.1)
has Kuhn-Tucker multipliers, and they are positive (Lemma 14.B.1), by the necessity theorems. -/
theorem inst_kt_necessary :
    (∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (exA.EU true exW - exA.ubar) = 0 ∧
      μ * (exA.EU true exW - exA.EU false exW) = 0 ∧
      ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = γ + μ * (1 - exA.f false x / exA.f true x)) ∧
    ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
      ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = γ + μ * (1 - exA.f false x / exA.f true x) :=
  ⟨HAModel.ha_kt_necessary exA_standing exA_two (exA_fosd _ _ _ _) exA_optimal,
    HAModel.lemma_14_B_1_every exA_standing exA_two (exA_fosd _ _ _ _)
      (by norm_num [exA, exModel]) exA_dv_anti exA_optimal⟩

/-- **Exercise 14.B.2, an instance** (MWG, p. 507). In `exA`, with the owner's utility `U(y) = y`
(concave and nondecreasing), `exW` maximizes the owner's expected utility subject to (i) and
(ii_H), so the necessity theorem applies and yields the multipliers. -/
theorem inst_14_B_2_necessary :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (exA.EU true exW - exA.ubar) = 0 ∧
      μ * (exA.EU true exW - exA.EU false exW) = 0 ∧
      ∀ᵐ x ∂exA.ν, (fun _ => (1 : ℝ)) (x - exW x) / exA.dv (exW x) =
        γ + μ * (1 - exA.f false x / exA.f true x) := by
  refine HAModel.exercise_14_B_2_necessary exA_standing exA_two (exA_fosd _ _ _ _)
    (U := fun y => y) (concaveOn_id convex_univ) (fun y => hasDerivAt_id' y)
    (fun _ => zero_le_one) (fun _ _ => dmeas_integrable _ _) exA_optimal.1 fun w' hw' => ?_
  change exA.OP true w' ≤ exA.OP true exW
  rw [HAModel.ha_OP_eq exA_standing hw'.1.1, HAModel.ha_OP_eq exA_standing exW_adm]
  linarith [exA_optimal.2 w' hw']

/-- The model of the first-order-approach instance: profit levels `0, 1, 2` with
`f(·|e) = (1/4, 1/2, 1/4)`, `v(w) = -exp(-w)`, no disutility of effort and `ū = -7/12`. -/
noncomputable def exFOA : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) 0 (-7 / 12)

/-- The solution of the relaxed program in `exFOA`: `w = 0, log 2, log 3` at `π = 0, 1, 2`. -/
noncomputable def exWf (x : ℝ) : ℝ :=
  if x < 1 / 2 then 0 else if x < 3 / 2 then Real.log 2 else Real.log 3

/-- **(14.AA.3), an instance** (MWG, p. 504). In `exFOA` with `f_e(π|e) = (π - 1)/4` and
`g'(e) = 1/6`, the scheme `exWf` solves the relaxed program of the first-order approach (by
`foa_sufficient`, with `λ = 2`, `μ = 1`), and the necessity theorem applies to it. -/
theorem inst_foa_necessary :
    ∃ lam μ : ℝ, 0 ≤ lam ∧ lam * (exFOA.EU true exWf - exFOA.ubar) = 0 ∧
      ∀ᵐ x ∂exFOA.ν, 1 / exFOA.dv (exWf x) = lam + μ * ((x - 1) / 4 / exFOA.f true x) := by
  have hst : exFOA.Standing :=
    exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _
  have hadm : exFOA.Adm exWf := by
    refine ⟨?_, fun _ => ⟨dmeas_integrable _ _, dmeas_integrable _ _⟩⟩
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        measurable_const)
  have hfe : ∀ w', exFOA.Adm w' →
      Integrable (fun x => exFOA.v (w' x) * ((x - 1) / 4)) exFOA.ν :=
    fun _ _ => dmeas_integrable _ _
  have h0 : exWf 0 = 0 := by norm_num [exWf]
  have h1 : exWf 1 = Real.log 2 := by norm_num [exWf]
  have h2 : exWf 2 = Real.log 3 := by norm_num [exWf]
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e3 : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEU : exFOA.EU true exWf = -7 / 12 := by
    change (∫ x, -Real.exp (-exWf x) * exF true x ∂dmeas exPts) - (if true then (0 : ℝ) else 0)
      = -7 / 12
    rw [exA_integral, h0, h1, h2, e2, e3]
    simp only [exF]
    norm_num
  have hfoa : ∫ x, exFOA.v (exWf x) * ((x - 1) / 4) ∂exFOA.ν = 1 / 6 := by
    change ∫ x, -Real.exp (-exWf x) * ((x - 1) / 4) ∂dmeas exPts = 1 / 6
    rw [exA_integral, h0, h1, h2, e2, e3]
    norm_num
  have hfoc : ∀ᵐ x ∂exFOA.ν,
      1 / exFOA.dv (exWf x) = 2 + 1 * ((x - 1) / 4 / exFOA.f true x) := by
    refine dmeas_ae _ fun i => ?_
    change 1 / Real.exp (-exWf (exPts i)) = 2 + 1 * ((exPts i - 1) / 4 / exF true (exPts i))
    fin_cases i <;> simp only [exPts, exF] <;> norm_num [h0, h1, h2, Real.exp_neg,
      Real.exp_log]
  have hset : ∀ (P : ℝ → Prop) (i : Fin 3), MeasurableSet {x | P x} → P (exPts i) →
      exFOA.ν {x | P x} ≠ 0 := by
    intro P i hP hi h
    have hsum : exFOA.ν {x | P x} = ∑ j, Measure.dirac (exPts j) {x | P x} := by
      change (∑ j, Measure.dirac (exPts j)) {x | P x} = _
      rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hle := Finset.single_le_sum (f := fun j => Measure.dirac (exPts j) {x | P x})
      (fun j _ => zero_le) (Finset.mem_univ i)
    rw [← hsum, h, Measure.dirac_apply' _ hP, indicator_of_mem (by exact hi)] at hle
    simp at hle
  refine HAModel.foa_necessary hst (by fun_prop) hfe
    (hset _ 2 (measurableSet_lt measurable_const (by fun_prop)) (by norm_num [exPts]))
    (hset _ 0 (measurableSet_lt (by fun_prop) measurable_const) (by norm_num [exPts]))
    hadm (by rw [hEU]; exact le_refl _) hfoa fun w' hw' hp hf => ?_
  exact foa_sufficient hst hfe hadm (lam := 2) (μ := 1) (by norm_num) hfoc
    (by rw [hEU]; change (2 : ℝ) * (-7 / 12 - -7 / 12) = 0; ring) hfoa hw' hp hf

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 14.B.5 and 14.B.6

MWG, p. 508. Both exercises are formalized with finitely many profit (revenue) levels
`a 0 < a 1 < ⋯` (MWG, footnote 6); a scheme is `w : Fin n → ℝ`.

* Exercise 14.B.5: the manager can unobservably reduce profits. Facing `w`, he effectively
  receives `ŵ(i) = max_{j ≤ i} w(j)` (`effw`). `exercise_14_B_5`: `ŵ` is nondecreasing, gives the
  manager the same expected utility under every effort as `w` (so it implements the same effort),
  needs no disposal, and gives the owner at least as much as `w` with any optimal disposal: there is
  always an optimal scheme that is nondecreasing in observed profits.
* Exercise 14.B.6: revenue `R` and cost `C` independent given effort. (a) `exercise_14_B_6a`: under
  the monotone likelihood ratio property, a scheme satisfying the first-order condition for
  implementing `e_C` is nonincreasing in both `R` and `C`. (b) `exercise_14_B_6b`: if the manager
  can
  reduce revenues, such a scheme is effectively independent of `R`. (c) `exercise_14_B_6c`: if pay
  can depend only on revenues (and revenues can be reduced), `e_C` cannot be implemented
  (`mlrp_expect_mono`: a nondecreasing function has a higher expectation under `e_R`).
-/

namespace MWG.PrincipalAgent

open Finset

/-- The effective payment `max_{j ≤ i} w(j)` when the manager can reduce observed profits. -/
noncomputable def effw {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.filter (· ≤ i)).sup' (show (univ.filter (· ≤ i)).Nonempty from ⟨i, by simp⟩) w

theorem effw_ge {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : w i ≤ effw w i :=
  le_sup' w (by simp)

theorem effw_le_iff {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (c : ℝ) :
    effw w i ≤ c ↔ ∀ j, j ≤ i → w j ≤ c := by
  unfold effw
  rw [Finset.sup'_le_iff]
  simp

theorem effw_exists {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ∃ j, j ≤ i ∧ w j = effw w i := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_sup' (s := univ.filter (· ≤ i)) ⟨i, by simp⟩ w
  exact ⟨j, by simpa using hj, h.symm⟩

/-- The effective scheme is nondecreasing. -/
theorem effw_mono {n : ℕ} (w : Fin n → ℝ) : Monotone (effw w) := by
  intro i i' hii
  rw [effw_le_iff]
  intro j hj
  exact le_sup' w (by simp [hj.trans hii])

/-- A nondecreasing scheme is its own effective scheme. -/
theorem effw_of_mono {n : ℕ} {w : Fin n → ℝ} (hw : Monotone w) : effw w = w := by
  funext i
  exact le_antisymm ((effw_le_iff w i _).2 fun j hj => hw hj) (effw_ge w i)

/-- The effective scheme of the effective scheme is itself. -/
theorem effw_idem {n : ℕ} (w : Fin n → ℝ) : effw (effw w) = effw w :=
  effw_of_mono (effw_mono w)

/-- An optimal disposal rule for `w`: from profit level `i` report `d i ≤ i` with the highest
pay. -/
def IsDisp {n : ℕ} (w : Fin n → ℝ) (d : Fin n → Fin n) : Prop :=
  ∀ i, d i ≤ i ∧ w (d i) = effw w i

/-- **Exercise 14.B.5** (MWG, p. 508). Let profit levels `a` be increasing, effort `e` give
profit level `i` with probability `q e i ≥ 0`, and let the manager have utility
`Σᵢ q e i v(pay) - g e`. For any scheme `w` and any optimal disposal rule `d` for `w`, the
nondecreasing scheme `ŵ = effw w`: (i) gives the manager the same expected utility under every
effort (so implements the same effort and meets the same participation constraint); (ii) makes not
disposing optimal; (iii) gives the owner at least as much as `w` with disposal `d`. -/
theorem exercise_14_B_5 {n : ℕ} {E : Type*} (a : Fin n → ℝ) (ha : Monotone a)
    (q : E → Fin n → ℝ) (hq : ∀ e i, 0 ≤ q e i) (v : ℝ → ℝ) (g : E → ℝ) (w : Fin n → ℝ)
    (d : Fin n → Fin n) (hd : IsDisp w d) :
    Monotone (effw w) ∧
      (∀ e, ∑ i, q e i * v (effw (effw w) i) - g e = ∑ i, q e i * v (effw w i) - g e) ∧
      IsDisp (effw w) id ∧
      ∀ e, ∑ i, q e i * (a (d i) - w (d i)) ≤ ∑ i, q e i * (a i - effw w i) := by
  refine ⟨effw_mono w, fun e => by rw [effw_idem], fun i => ⟨le_rfl, by rw [effw_idem]; rfl⟩,
    fun e => ?_⟩
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hq e i)
  rw [(hd i).2]
  linarith [ha (hd i).1]

/-- **Exercise 14.B.6(a)** (MWG, p. 508). With `R` and `C` independent given effort, the likelihood
ratio for implementing `e_C` against `e_R` is `ℓ_R(R) ℓ_C(C)` with
`ℓ_R = f_R(·|e_R)/f_R(·|e_C)` and `ℓ_C = f_C(·|e_R)/f_C(·|e_C)` positive and (MLRP) nondecreasing.
A scheme satisfying `1 / v'(w(R, C)) = γ + μ [1 - ℓ_R(R) ℓ_C(C)]` with `μ > 0` and `v'` strictly
decreasing is nonincreasing in `R` and in `C`. -/
theorem exercise_14_B_6a {dv : ℝ → ℝ} (hda : StrictAnti dv) (hdv : ∀ w, 0 < dv w)
    {lR lC : ℝ → ℝ} (hR : Monotone lR) (hC : Monotone lC) (hR0 : ∀ r, 0 < lR r)
    (hC0 : ∀ c, 0 < lC c) {w : ℝ → ℝ → ℝ} {γ μ : ℝ} (hμ : 0 < μ)
    (hfoc : ∀ r c, 1 / dv (w r c) = γ + μ * (1 - lR r * lC c)) :
    (∀ c, Antitone fun r => w r c) ∧ ∀ r, Antitone fun c => w r c := by
  have key : ∀ r c r' c', lR r * lC c ≤ lR r' * lC c' → w r' c' ≤ w r c := by
    intro r c r' c' h
    have h1 : 1 / dv (w r' c') ≤ 1 / dv (w r c) := by
      rw [hfoc, hfoc]; nlinarith
    rw [one_div_le_one_div (hdv _) (hdv _)] at h1
    exact hda.le_iff_ge.1 h1
  refine ⟨fun c r r' hrr => key r c r' c ?_, fun r c c' hcc => key r c r c' ?_⟩
  · exact mul_le_mul_of_nonneg_right (hR hrr) (hC0 c).le
  · exact mul_le_mul_of_nonneg_left (hC hcc) (hR0 r).le

/-- **Exercise 14.B.6(b)** (MWG, p. 508). If the manager can reduce revenues, a scheme that is
nonincreasing in the revenue level (as in part (a)) pays effectively the same at every revenue
level: `ŵ(R, C) = w(R_min, C)`. -/
theorem exercise_14_B_6b {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : Antitone w) (i : Fin (n + 1)) :
    effw w i = w 0 := by
  refine le_antisymm ((effw_le_iff w i _).2 fun j _ => hw (Fin.zero_le j)) ?_
  exact (le_sup' w (by simp : (0 : Fin (n + 1)) ∈ univ.filter (· ≤ i)))

/-- **Monotone likelihood ratio and expectations** (used in Exercise 14.B.6(c)). If `q₁, q₀` are
positive probability vectors with `q₁ i / q₀ i` nondecreasing in `i`, every nondecreasing `φ` has
`Σ q₀ φ ≤ Σ q₁ φ`. -/
theorem mlrp_expect_mono {n : ℕ} {q1 q0 φ : Fin n → ℝ} (h1 : ∀ i, 0 < q1 i) (h0 : ∀ i, 0 < q0 i)
    (hs : ∑ i, q1 i = ∑ i, q0 i) (hl : Monotone fun i => q1 i / q0 i) (hφ : Monotone φ) :
    ∑ i, q0 i * φ i ≤ ∑ i, q1 i * φ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- a threshold index
  have hne : (univ.filter fun i : Fin n => 1 ≤ q1 i / q0 i).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hc
    have : ∑ i, q1 i < ∑ i, q0 i := by
      refine sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ fun i _ => ?_
      have := hc (mem_univ i)
      rw [not_le, div_lt_one (h0 i)] at this; exact this
    linarith
  set i0 := (univ.filter fun i : Fin n => 1 ≤ q1 i / q0 i).min' hne
  have hi0 : 1 ≤ q1 i0 / q0 i0 := (mem_filter.1 (min'_mem _ hne)).2
  set κ := φ i0
  have hterm : ∀ i, 0 ≤ (q1 i - q0 i) * (φ i - κ) := by
    intro i
    rcases le_or_gt i0 i with h | h
    · have hl' : 1 ≤ q1 i / q0 i := hi0.trans (hl h)
      rw [le_div_iff₀ (h0 i), one_mul] at hl'
      exact mul_nonneg (by linarith) (by linarith [hφ h])
    · have hl' : q1 i / q0 i < 1 := by
        by_contra hc
        have hmem : i ∈ univ.filter (fun i : Fin n => 1 ≤ q1 i / q0 i) :=
          mem_filter.2 ⟨mem_univ i, le_of_not_gt hc⟩
        have := min'_le _ i hmem
        exact absurd h (not_lt_of_ge this)
      rw [div_lt_one (h0 i)] at hl'
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hφ h.le])
  have hsum := sum_nonneg fun i (_ : i ∈ univ) => hterm i
  have : ∑ i, (q1 i - q0 i) * (φ i - κ) = ∑ i, q1 i * φ i - ∑ i, q0 i * φ i -
      κ * (∑ i, q1 i - ∑ i, q0 i) := by
    rw [mul_sub, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [this, hs, sub_self, mul_zero, sub_zero] at hsum
  linarith

/-- **Exercise 14.B.6(c)** (MWG, p. 508). If pay can depend only on revenues and the manager can
reduce revenues, the effective scheme is nondecreasing in revenue; under the monotone likelihood
ratio property for revenues the manager's expected utility of income is then at least as high
under `e_R` as under `e_C`, and since `g(e_C) > g(e_R)` he strictly prefers `e_R`: `e_C` cannot be
implemented. -/
theorem exercise_14_B_6c {n : ℕ} {qR qC : Fin n → ℝ} (hR : ∀ i, 0 < qR i) (hC : ∀ i, 0 < qC i)
    (hs : ∑ i, qR i = ∑ i, qC i) (hl : Monotone fun i => qR i / qC i) {v : ℝ → ℝ}
    (hv : Monotone v) {gR gC : ℝ} (hg : gR < gC) (w : Fin n → ℝ) :
    ∑ i, qC i * v (effw w i) - gC < ∑ i, qR i * v (effw w i) - gR := by
  have := mlrp_expect_mono hR hC hs hl (hv.comp (effw_mono w))
  simp only [Function.comp] at this
  linarith

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.B.6(b): the optimal scheme when revenues can be reduced

MWG, Exercise 14.B.6(b), p. 508. Finitely many revenue levels `R_0 < ⋯ < R_n` and cost levels
`C_0, …, C_{m-1}` (corrections 7); revenue and cost are independent given effort, with
probabilities `r_e(R)` and `c_e(C)`; the owner implements `e_C`. Because the manager can reduce
revenues, he effectively faces a scheme nondecreasing in `R` (Exercise 14.B.5, `effw`).

* `exercise_14_B_6b_opt`: for every scheme `w(R, C)` nondecreasing in `R` that satisfies the
  participation and incentive constraints for `e_C`, the scheme `ŵ(C)` that pays, at each cost
  level, the certainty equivalent of `w(·, C)` under `r_{e_C}` (independent of `R`) also satisfies
  both constraints and costs no more (Jensen; the monotone likelihood ratio property makes the
  `e_R`-deviation weakly less attractive). With strict risk aversion it is strictly cheaper unless
  `w` already ignores `R` at every cost level of positive probability. So the optimal scheme
  depends on costs only, and solves the problem of part (a) with revenues ignored, with first-order
  condition `1 / v'(w(C)) = γ + μ [1 - f_C(C|e_R)/f_C(C|e_C)]` (`exercise_14_B_6a` with
  `ℓ_R ≡ 1`).
* `exercise_14_B_6b_instance`: a proved instance of the hypotheses.
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- **Exercise 14.B.6(b)** (MWG, p. 508). Revenue-reduction-proof schemes (nondecreasing in `R`)
can be replaced by schemes depending on costs only, without violating the constraints for `e_C`
and without raising the expected wage; strictly so under strict risk aversion if `w` depends on
`R` at some cost level of positive probability. -/
theorem exercise_14_B_6b_opt {n m : ℕ} {v : ℝ → ℝ} (hv : ConcaveOn ℝ univ v)
    (hvc : Continuous v) (hvm : StrictMono v) {rC rR : Fin (n + 1) → ℝ} {cC cR : Fin m → ℝ}
    (hrC : ∀ i, 0 < rC i) (hrR : ∀ i, 0 < rR i) (hrC1 : ∑ i, rC i = 1) (hrR1 : ∑ i, rR i = 1)
    (hcC : ∀ j, 0 ≤ cC j) (hcR : ∀ j, 0 ≤ cR j) (hl : Monotone fun i => rR i / rC i)
    {gC gR ubar : ℝ} {w : Fin (n + 1) → Fin m → ℝ} (hw : ∀ j, Monotone fun i => w i j)
    (hIR : ubar ≤ ∑ i, ∑ j, rC i * cC j * v (w i j) - gC)
    (hIC : ∑ i, ∑ j, rR i * cR j * v (w i j) - gR ≤ ∑ i, ∑ j, rC i * cC j * v (w i j) - gC) :
    ∃ wh : Fin m → ℝ, (∀ j, v (wh j) = ∑ i, rC i * v (w i j)) ∧
      ubar ≤ ∑ j, cC j * v (wh j) - gC ∧
      ∑ j, cR j * v (wh j) - gR ≤ ∑ j, cC j * v (wh j) - gC ∧
      ∑ j, cC j * wh j ≤ ∑ i, ∑ j, rC i * cC j * w i j ∧
      (StrictConcaveOn ℝ univ v → (∃ j0, 0 < cC j0 ∧ ∃ i i', w i j0 ≠ w i' j0) →
        ∑ j, cC j * wh j < ∑ i, ∑ j, rC i * cC j * w i j) := by
  -- the certainty equivalents
  have hex : ∀ j, ∃ x, v x = ∑ i, rC i * v (w i j) := by
    intro j
    have hlo : v (w 0 j) ≤ ∑ i, rC i * v (w i j) := by
      calc v (w 0 j) = ∑ i, rC i * v (w 0 j) := by rw [← sum_mul, hrC1, one_mul]
        _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (hvm.monotone (hw j (Fin.zero_le i))) (hrC i).le
    have hhi : ∑ i, rC i * v (w i j) ≤ v (w (Fin.last n) j) := by
      calc ∑ i, rC i * v (w i j) ≤ ∑ i, rC i * v (w (Fin.last n) j) :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              (hvm.monotone (hw j (Fin.le_last i))) (hrC i).le
        _ = _ := by rw [← sum_mul, hrC1, one_mul]
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc (hw j (Fin.zero_le (Fin.last n)))
      hvc.continuousOn ⟨hlo, hhi⟩
    exact ⟨x, hx⟩
  choose wh hwh using hex
  -- expected utilities
  have hUC : ∑ i, ∑ j, rC i * cC j * v (w i j) = ∑ j, cC j * v (wh j) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [hwh j, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have hUR : ∑ j, cR j * v (wh j) ≤ ∑ i, ∑ j, rR i * cR j * v (w i j) := by
    rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [hwh j]
    have hm := mlrp_expect_mono hrR hrC (by rw [hrR1, hrC1]) hl
      (hvm.monotone.comp (hw j))
    simp only [Function.comp] at hm
    have : ∑ i, rR i * cR j * v (w i j) = cR j * ∑ i, rR i * v (w i j) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hm (hcR j)
  -- Jensen at each cost level
  have hJ : ∀ j, wh j ≤ ∑ i, rC i * w i j := by
    intro j
    have := hv.le_map_sum (t := univ) (w := rC) (p := fun i => w i j)
      (fun i _ => (hrC i).le) hrC1 (fun i _ => mem_univ _)
    simp only [smul_eq_mul] at this
    rw [← hwh j] at this
    exact hvm.le_iff_le.1 this
  have hcost : ∑ i, ∑ j, rC i * cC j * w i j = ∑ j, cC j * ∑ i, rC i * w i j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  refine ⟨wh, hwh, by linarith, by linarith, ?_, fun hsc ⟨j0, hj0, i, i', hii'⟩ => ?_⟩
  · rw [hcost]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hJ j) (hcC j)
  · rw [hcost]
    refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hJ j) (hcC j))
      ⟨j0, mem_univ _, mul_lt_mul_of_pos_left ?_ hj0⟩
    have := (hsc.lt_map_sum_iff_of_pos (t := univ) (w := rC) (p := fun i => w i j0)
      (fun i _ => hrC i) hrC1 (fun i _ => mem_univ _)).2 ⟨i, mem_univ _, i', mem_univ _, hii'⟩
    simp only [smul_eq_mul] at this
    rw [← hwh j0] at this
    exact hvm.lt_iff_lt.1 this

/-- **Exercise 14.B.6(b), an instance** (MWG, p. 508). Two revenue levels with
`r_{e_C} = (1/2, 1/2)` and `r_{e_R} = (1/4, 3/4)` (monotone likelihood ratio), two cost levels with
`c_{e_C} = (3/4, 1/4)` and `c_{e_R} = (1/4, 3/4)`, `v(w) = w`, `g(e_C) = 1`, `g(e_R) = 0`, `ū = 0`
and the scheme `w(R_i, C_0) = 2 + i/10`, `w(R_i, C_1) = 0`, nondecreasing in revenue: the
hypotheses of `exercise_14_B_6b_opt` hold. -/
theorem exercise_14_B_6b_instance :
    let rC : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    let rR : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let cC : Fin 2 → ℝ := ![3 / 4, 1 / 4]
    let cR : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let w : Fin 2 → Fin 2 → ℝ := fun i j => if j = 0 then 2 + (i : ℝ) / 10 else 0
    (∀ j, Monotone fun i => w i j) ∧ Monotone (fun i => rR i / rC i) ∧
      (0 : ℝ) ≤ ∑ i, ∑ j, rC i * cC j * w i j - 1 ∧
      ∑ i, ∑ j, rR i * cR j * w i j - 0 ≤ ∑ i, ∑ j, rC i * cC j * w i j - 1 := by
  intro rC rR cC cR w
  refine ⟨fun j i i' hii' => ?_, fun i i' hii' => ?_, ?_, ?_⟩
  · simp only [w]
    split_ifs
    · have : (i : ℝ) ≤ i' := by exact_mod_cast hii'
      linarith
    · exact le_rfl
  · fin_cases i <;> fin_cases i' <;> simp_all [rR, rC]
    norm_num
  · simp [Fin.sum_univ_two, rC, cC, w]
    norm_num
  · simp [Fin.sum_univ_two, rC, cC, rR, cR, w]
    norm_num

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.8 (Air Shangri-la)

MWG, Exercise 14.C.8, pp. 509-510.

A traveller of type `θ` (`θ_B` business, `θ_T` tourist, `0 < θ_B < θ_T`) buying a ticket at price
`P ≥ 0` a time `W ≥ 0` before the flight gets `v - θP - W` (`0` if he does not fly); a fraction
`λ` are tourists; each passenger costs `c`. The airline offers `(P_B, W_B)`, `(P_T, W_T)` to carry
both types (part (a), the formulation, is `C8Feas`; the indifference curves are graphical).

* `exercise_14_C_8_IRB`: the business traveller's participation constraint is implied.
* `exercise_14_C_8b`: at an optimum tourists are indifferent between flying and not.
* `exercise_14_C_8c`: business travellers buy at the last moment (`W_B = 0`) and are indifferent
  between this and the tourists' ticket.
* `exercise_14_C_8d`: the optimal scheme. With `κ = (1 - λ)/θ_B - 1/θ_T`, the profit of every
  feasible scheme is at most `(v - W)/θ_T + (1 - λ) W/θ_B - c` for some `W ∈ [0, v]`; if `κ < 0`
  the optimum is a single price `v/θ_T` with no advance purchase; if `κ > 0` it is `P_T = 0`,
  `W_T = v`, `P_B = v/θ_B`.
* `exercise_14_C_8e`: serving only business travellers is better when `κ ≥ 0`.
-/

namespace MWG.PrincipalAgent

/-- The feasible schemes carrying both types (MWG, Exercise 14.C.8(a)). -/
def C8Feas (v θB θT PB WB PT WT : ℝ) : Prop :=
  0 ≤ PB ∧ 0 ≤ WB ∧ 0 ≤ PT ∧ 0 ≤ WT ∧ 0 ≤ v - θB * PB - WB ∧ 0 ≤ v - θT * PT - WT ∧
    v - θB * PT - WT ≤ v - θB * PB - WB ∧ v - θT * PB - WB ≤ v - θT * PT - WT

/-- The airline's profit. -/
def C8Profit (lam c PB PT : ℝ) : ℝ := lam * (PT - c) + (1 - lam) * (PB - c)

/-- An optimal scheme carrying both types. -/
def C8Opt (v θB θT lam c PB WB PT WT : ℝ) : Prop :=
  C8Feas v θB θT PB WB PT WT ∧ ∀ PB' WB' PT' WT', C8Feas v θB θT PB' WB' PT' WT' →
    C8Profit lam c PB' PT' ≤ C8Profit lam c PB PT

/-- The business traveller's participation follows from the tourists' participation and the
business traveller's self-selection constraint. -/
theorem exercise_14_C_8_IRB {v θB θT PB WB PT WT : ℝ} (hθ : θB < θT) (hPT : 0 ≤ PT)
    (hT : 0 ≤ v - θT * PT - WT) (hB : v - θB * PT - WT ≤ v - θB * PB - WB) :
    0 ≤ v - θB * PB - WB := by nlinarith

/-- **Exercise 14.C.8(b)** (MWG, p. 510). At an optimal scheme tourists are indifferent between
buying a ticket and not going (raising both prices by the slack keeps all constraints). -/
theorem exercise_14_C_8b {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (h : C8Opt v θB θT lam c PB WB PT WT) :
    v - θT * PT - WT = 0 := by
  obtain ⟨⟨h1, h2, h3, h4, -, h6, h7, h8⟩, hopt⟩ := h
  by_contra hne
  have hs : 0 < v - θT * PT - WT := lt_of_le_of_ne h6 (Ne.symm hne)
  set δ := (v - θT * PT - WT) / θT
  have hθT : 0 < θT := hθB.trans hθ
  have hδ : 0 < δ := div_pos hs hθT
  have hδT : θT * δ = v - θT * PT - WT := by simp only [δ]; field_simp
  clear_value δ
  have hfeas : C8Feas v θB θT (PB + δ) WB (PT + δ) WT := by
    refine ⟨by linarith, h2, by linarith, h4, ?_, by nlinarith, by nlinarith, by nlinarith⟩
    exact exercise_14_C_8_IRB (PT := PT + δ) (WT := WT) hθ (by linarith) (by nlinarith)
      (by nlinarith)
  have := hopt _ _ _ _ hfeas
  unfold C8Profit at this
  nlinarith

/-- **Exercise 14.C.8(c)** (MWG, p. 510). At an optimal scheme business travellers never buy in
advance (`W_B = 0`) and are indifferent between their ticket and the tourists'. -/
theorem exercise_14_C_8c {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam < 1) (h : C8Opt v θB θT lam c PB WB PT WT) :
    WB = 0 ∧ v - θB * PB - WB = v - θB * PT - WT := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hopt⟩ := h
  constructor
  · by_contra hne
    have hW : 0 < WB := lt_of_le_of_ne h2 (Ne.symm hne)
    -- move the business ticket along the business indifference curve: `W_B ↦ 0`,
    -- `P_B ↦ P_B + W_B/θ_B`
    have hfeas : C8Feas v θB θT (PB + WB / θB) 0 PT WT := by
      have e1 : θB * (PB + WB / θB) = θB * PB + WB := by field_simp
      have hT : θT * (WB / θB) ≥ WB := by
        rw [ge_iff_le, ← mul_div_assoc, le_div_iff₀ hθB]; nlinarith
      refine ⟨by positivity, le_rfl, h3, h4, by rw [e1]; linarith, h6, by rw [e1]; linarith, ?_⟩
      nlinarith
    have := hopt _ _ _ _ hfeas
    unfold C8Profit at this
    have : 0 < (1 - lam) * (WB / θB) := mul_pos (by linarith) (div_pos hW hθB)
    linarith
  · by_contra hne
    have hs : 0 < (v - θB * PB - WB) - (v - θB * PT - WT) := by
      rcases lt_or_eq_of_le h7 with h | h
      · linarith
      · exact absurd h.symm hne
    set δ := ((v - θB * PB - WB) - (v - θB * PT - WT)) / θB
    have hδ : 0 < δ := div_pos hs hθB
    have hδB : θB * δ = (v - θB * PB - WB) - (v - θB * PT - WT) := by simp only [δ]; field_simp
    clear_value δ
    have hfeas : C8Feas v θB θT (PB + δ) WB PT WT := by
      refine ⟨by linarith, h2, h3, h4, ?_, h6, by nlinarith, by nlinarith⟩
      exact exercise_14_C_8_IRB (PT := PT) (WT := WT) hθ h3 h6 (by nlinarith)
    have := hopt _ _ _ _ hfeas
    unfold C8Profit at this
    nlinarith

/-- The tourists' and business tickets determined by `W_T = W`: `P_T = (v - W)/θ_T`, `W_B = 0`,
`P_B = P_T + W/θ_B`. -/
theorem exercise_14_C_8d_feas {v θB θT W : ℝ} (hθB : 0 < θB) (hθ : θB < θT) (hW : 0 ≤ W)
    (hWv : W ≤ v) :
    C8Feas v θB θT ((v - W) / θT + W / θB) 0 ((v - W) / θT) W := by
  have hθT : 0 < θT := hθB.trans hθ
  have eT : θT * ((v - W) / θT) = v - W := by field_simp
  have eB : θB * ((v - W) / θT + W / θB) = θB * ((v - W) / θT) + W := by field_simp
  have eTB : θT * ((v - W) / θT + W / θB) = v - W + θT * (W / θB) := by
    rw [mul_add, eT]
  have hTB : W ≤ θT * (W / θB) := by
    rw [← mul_div_assoc, le_div_iff₀ hθB]; nlinarith
  have hPT : 0 ≤ (v - W) / θT := div_nonneg (by linarith) hθT.le
  refine ⟨by positivity, le_rfl, hPT, hW, ?_, by rw [eT]; linarith, by rw [eB]; linarith,
    by rw [eTB, eT]; linarith⟩
  rw [eB]
  have : θB * ((v - W) / θT) ≤ v - W := by
    have := mul_le_mul_of_nonneg_right hθ.le hPT
    rwa [eT] at this
  linarith

/-- **Exercise 14.C.8(d)** (MWG, p. 510), the bound. Every feasible scheme earns at most
`(v - W_T)/θ_T + (1 - λ) W_T/θ_B - c`, attained by `exercise_14_C_8d_feas` with `W = W_T`. -/
theorem exercise_14_C_8d_bound {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam ≤ 1) (h : C8Feas v θB θT PB WB PT WT) :
    C8Profit lam c PB PT ≤ (v - WT) / θT + (1 - lam) * (WT / θB) - c ∧ WT ≤ v ∧
      C8Profit lam c ((v - WT) / θT + WT / θB) ((v - WT) / θT) =
        (v - WT) / θT + (1 - lam) * (WT / θB) - c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hθT : 0 < θT := hθB.trans hθ
  have hPT : PT ≤ (v - WT) / θT := by rw [le_div_iff₀ hθT]; linarith
  have hPB : PB ≤ PT + WT / θB := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hθB]; nlinarith
  refine ⟨?_, by nlinarith, by unfold C8Profit; ring⟩
  unfold C8Profit
  nlinarith [mul_le_mul_of_nonneg_left hPB (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Exercise 14.C.8(d)** (MWG, p. 510), the optimal scheme. With `κ = (1 - λ)/θ_B - 1/θ_T`:
if `κ < 0` the single price `v/θ_T` (`W = 0`) for both types is optimal; if `κ > 0` the scheme
`P_T = 0`, `W_T = v`, `P_B = v/θ_B`, `W_B = 0` is optimal. The cost `c` does not matter. -/
theorem exercise_14_C_8d {v θB θT lam c : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam ≤ 1) (hv : 0 ≤ v) :
    ((1 - lam) / θB - 1 / θT < 0 → C8Opt v θB θT lam c (v / θT) 0 (v / θT) 0) ∧
      (0 < (1 - lam) / θB - 1 / θT → C8Opt v θB θT lam c (v / θB) 0 0 v) := by
  have hθT : 0 < θT := hθB.trans hθ
  have key : ∀ W, (v - W) / θT + (1 - lam) * (W / θB) - c =
      v / θT - c + W * ((1 - lam) / θB - 1 / θT) := fun W => by ring
  constructor
  · intro hκ
    have hf := exercise_14_C_8d_feas hθB hθ le_rfl hv
    simp only [sub_zero, zero_div, add_zero] at hf
    refine ⟨hf, fun PB' WB' PT' WT' h' => ?_⟩
    obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h'
    rw [key] at hb
    have : C8Profit lam c (v / θT) (v / θT) = v / θT - c := by unfold C8Profit; ring
    rw [this]; nlinarith [h'.2.2.2.1]
  · intro hκ
    have hf := exercise_14_C_8d_feas hθB hθ hv le_rfl
    simp only [sub_self, zero_div, zero_add] at hf
    refine ⟨hf, fun PB' WB' PT' WT' h' => ?_⟩
    obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h'
    rw [key] at hb
    have : C8Profit lam c (v / θB) 0 = v / θT - c + v * ((1 - lam) / θB - 1 / θT) := by
      unfold C8Profit; ring
    rw [this]; nlinarith

/-- **Exercise 14.C.8(e)** (MWG, p. 510). Serving only business travellers (at `P = v/θ_B`,
`W = 0`) earns `(1 - λ)(v/θ_B - c)`. When `κ = (1 - λ)/θ_B - 1/θ_T ≥ 0` and `c > 0` this beats
every scheme carrying both types. (When `κ < 0` the best scheme carrying both types earns
`v/θ_T - c` by `exercise_14_C_8d`, so serving only business travellers is better iff
`(1 - λ)(v/θ_B - c) > v/θ_T - c`.) -/
theorem exercise_14_C_8e {v θB θT lam c : ℝ} (hθB : 0 < θB) (hθ : θB < θT) (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) (hc : 0 < c) (hκ : 0 ≤ (1 - lam) / θB - 1 / θT) :
    ∀ PB WB PT WT, C8Feas v θB θT PB WB PT WT →
      C8Profit lam c PB PT < (1 - lam) * (v / θB - c) := by
  intro PB WB PT WT h
  obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h
  have key : (v - WT) / θT + (1 - lam) * (WT / θB) - c =
      v / θT - c + WT * ((1 - lam) / θB - 1 / θT) := by ring
  rw [key] at hb
  have h2 : WT * ((1 - lam) / θB - 1 / θT) ≤ v * ((1 - lam) / θB - 1 / θT) :=
    mul_le_mul_of_nonneg_right hWv hκ
  have : v / θT + v * ((1 - lam) / θB - 1 / θT) = (1 - lam) * (v / θB) := by ring
  nlinarith

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.9 (monopoly insurance)

MWG, Exercise 14.C.9, p. 510.

Wealth `W`, loss `L` with probability `θ`; a contract `(c₁, c₂)` gives wealth `c₁` without and
`c₂` with the loss; the insurer's expected profit is `(1 - θ)(W - c₁) + θ(W - L - c₂)`; the
individual's alternative is no insurance.

* `exercise_14_C_9a`: with `θ` observable the optimal contract is full insurance at the certainty
  equivalent of the endowment, and it is the unique optimum.
* `exercise_14_C_9b`: with `θ ∈ {θ_L, θ_H}` unobservable, written in utility levels
  `x = u(c₁)`, `y = u(c₂)` with `c = φ(·)` (`φ = u⁻¹` convex), a menu satisfying the Kuhn-Tucker
  conditions (with the low-risk participation and high-risk self-selection constraints as the
  only active ones) is optimal; its first-order conditions give full insurance for the high-risk
  type and partial insurance (`c₂ < c₁`) for the low-risk type (`exercise_14_C_9b_shape`). At such
  a contract the low-risk individual is rationed: she would buy more insurance at fair odds
  (`exercise_14_C_9b_rationed`).
* `exercise_14_C_9b_instance`: `u = √c`, `W = 25`, `L = 24`, `θ_L = 1/4`, `θ_H = 1/2`,
  `λ = 1/2`: the optimal menu is `(9, 9)` for the high-risk and `(25, 1)` for the low-risk type.
* Part (c) (comparison with the competitive model of Exercise 13.D.2) is verbal.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Exercise 14.C.9(a)** (MWG, p. 510). With `θ` observable, `u` strictly concave and strictly
increasing, and `c*` the certainty equivalent of the endowment
(`u(c*) = (1 - θ) u(W) + θ u(W - L)`), every contract acceptable to the individual earns at most
`W - θL - c*`, and only full insurance at `c*` attains it. -/
theorem exercise_14_C_9a {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ univ u) (hmono : StrictMono u)
    {θ W L cstar : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hc : u cstar = (1 - θ) * u W + θ * u (W - L)) {c1 c2 : ℝ}
    (hIR : (1 - θ) * u W + θ * u (W - L) ≤ (1 - θ) * u c1 + θ * u c2) :
    (1 - θ) * (W - c1) + θ * (W - L - c2) ≤ W - θ * L - cstar ∧
      ((1 - θ) * (W - c1) + θ * (W - L - c2) = W - θ * L - cstar → c1 = cstar ∧ c2 = cstar) := by
  have hJ := tpa_jensen_two hu.concaveOn (by linarith : 0 ≤ 1 - θ) (by linarith) c1 c2
  have hle : cstar ≤ (1 - θ) * c1 + (1 - (1 - θ)) * c2 :=
    hmono.le_iff_le.1 (by rw [hc]; simp only [sub_sub_cancel] at hJ ⊢; linarith)
  refine ⟨by nlinarith, fun heq => ?_⟩
  have hsum : (1 - θ) * c1 + θ * c2 = cstar := by linarith
  have hc12 : c1 = c2 := by
    by_contra hne
    have hJs := tpa_jensen_two_lt hu (by linarith : 0 < 1 - θ) (by linarith) hne
    simp only [sub_sub_cancel] at hJs
    rw [hsum, hc] at hJs
    linarith
  subst hc12
  constructor <;> linarith

/-- The insurer's expected profit from a type-`θ` individual with utility levels `(x, y)`. -/
def c9Profit (φ : ℝ → ℝ) (W L θ x y : ℝ) : ℝ := W - θ * L - ((1 - θ) * φ x + θ * φ y)

/-- **Exercise 14.C.9(b)** (MWG, p. 510), sufficiency. In utility levels, with `φ` convex and
differentiable (wealth `φ(x)` gives utility `x`), consider menus `(x_L, y_L)`, `(x_H, y_H)` for the
low- and high-risk types (probabilities `λ`, `1 - λ`), subject to the low-risk participation
constraint `(1 - θ_L) x_L + θ_L y_L ≥ r_L` and the high-risk self-selection constraint. If the
candidate satisfies the first-order conditions `(1 - λ) φ'(x_H) = (1 - λ) φ'(y_H) = β`,
`λ (1 - θ_L) φ'(x_L) = α (1 - θ_L) - β (1 - θ_H)`, `λ θ_L φ'(y_L) = α θ_L - β θ_H` with
`α, β ≥ 0` and complementary slackness, then no menu satisfying these two constraints earns more;
in particular it is optimal among all menus satisfying all participation and self-selection
constraints. -/
theorem exercise_14_C_9b {φ dφ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hdφ : ∀ x, HasDerivAt φ (dφ x) x) {W L θL θH lam rL α β : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) {xL yL xH yH : ℝ}
    (fH1 : (1 - lam) * dφ xH = β) (fH2 : (1 - lam) * dφ yH = β)
    (fL1 : lam * ((1 - θL) * dφ xL) = α * (1 - θL) - β * (1 - θH))
    (fL2 : lam * (θL * dφ yL) = α * θL - β * θH)
    (cs1 : α * ((1 - θL) * xL + θL * yL - rL) = 0)
    (cs2 : β * ((1 - θH) * xH + θH * yH - ((1 - θH) * xL + θH * yL)) = 0)
    {xL' yL' xH' yH' : ℝ} (hIR : rL ≤ (1 - θL) * xL' + θL * yL')
    (hIC : (1 - θH) * xL' + θH * yL' ≤ (1 - θH) * xH' + θH * yH')
    (hθH0 : 0 ≤ θH) (hθH1 : θH ≤ 1) (hθL0 : 0 ≤ θL) (hθL1 : θL ≤ 1) :
    lam * c9Profit φ W L θL xL' yL' + (1 - lam) * c9Profit φ W L θH xH' yH' ≤
      lam * c9Profit φ W L θL xL yL + (1 - lam) * c9Profit φ W L θH xH yH := by
  have t1 := tpa_tangent_ge_convex hφ (mem_univ xL) (mem_univ xL') (hdφ xL).hasDerivWithinAt
  have t2 := tpa_tangent_ge_convex hφ (mem_univ yL) (mem_univ yL') (hdφ yL).hasDerivWithinAt
  have t3 := tpa_tangent_ge_convex hφ (mem_univ xH) (mem_univ xH') (hdφ xH).hasDerivWithinAt
  have t4 := tpa_tangent_ge_convex hφ (mem_univ yH) (mem_univ yH') (hdφ yH).hasDerivWithinAt
  have a1 := mul_le_mul_of_nonneg_left t1 (mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1 - θL))
  have a2 := mul_le_mul_of_nonneg_left t2 (mul_nonneg hl0 hθL0)
  have a3 := mul_le_mul_of_nonneg_left t3
    (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (by linarith : (0:ℝ) ≤ 1 - θH))
  have a4 := mul_le_mul_of_nonneg_left t4 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hθH0)
  have k1 : 0 ≤ α * ((1 - θL) * xL' + θL * yL' - ((1 - θL) * xL + θL * yL)) := by
    have : α * ((1 - θL) * xL' + θL * yL' - rL) ≥ 0 := mul_nonneg hα (by linarith)
    linarith
  have k2 : 0 ≤ β * ((1 - θH) * xH' + θH * yH' - ((1 - θH) * xL' + θH * yL') -
      ((1 - θH) * xH + θH * yH - ((1 - θH) * xL + θH * yL))) := by
    have : β * ((1 - θH) * xH' + θH * yH' - ((1 - θH) * xL' + θH * yL')) ≥ 0 :=
      mul_nonneg hβ (by linarith)
    linarith
  -- the first-order conditions turn the tangent terms into the constraint terms
  have e1 : lam * (1 - θL) * (dφ xL * (xL' - xL)) =
      (α * (1 - θL) - β * (1 - θH)) * (xL' - xL) := by
    rw [← fL1]; ring
  have e2 : lam * θL * (dφ yL * (yL' - yL)) = (α * θL - β * θH) * (yL' - yL) := by
    rw [← fL2]; ring
  have e3 : (1 - lam) * (1 - θH) * (dφ xH * (xH' - xH)) = β * (1 - θH) * (xH' - xH) := by
    rw [← fH1]; ring
  have e4 : (1 - lam) * θH * (dφ yH * (yH' - yH)) = β * θH * (yH' - yH) := by
    rw [← fH2]; ring
  unfold c9Profit
  linarith

/-- **Exercise 14.C.9(b)**, the shape of the solution: the first-order conditions give full
insurance for the high-risk type (`x_H = y_H` when `φ'` is injective) and, with `β > 0`,
`θ_L < θ_H`, `λ > 0` and `φ'` strictly increasing, partial insurance for the low-risk type
(`y_L < x_L`, i.e. `c₂ < c₁`). -/
theorem exercise_14_C_9b_shape {dφ : ℝ → ℝ} (hd : StrictMono dφ) {θL θH lam α β : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hβ : 0 < β) (hθL0 : 0 < θL) (hθ : θL < θH)
    (hθH1 : θH < 1) {xL yL xH yH : ℝ}
    (fH1 : (1 - lam) * dφ xH = β) (fH2 : (1 - lam) * dφ yH = β)
    (fL1 : lam * ((1 - θL) * dφ xL) = α * (1 - θL) - β * (1 - θH))
    (fL2 : lam * (θL * dφ yL) = α * θL - β * θH) : xH = yH ∧ yL < xL := by
  refine ⟨hd.injective (by nlinarith), ?_⟩
  have key : lam * θL * (1 - θL) * (dφ xL - dφ yL) = β * (θH - θL) := by
    linear_combination θL * fL1 - (1 - θL) * fL2
  have hpos : 0 < lam * θL * (1 - θL) := by
    have : 0 < 1 - θL := by linarith
    positivity
  have : dφ yL < dφ xL := by
    have : 0 < lam * θL * (1 - θL) * (dφ xL - dφ yL) := by
      rw [key]; exact mul_pos hβ (by linarith)
    have := (pos_iff_pos_of_mul_pos this).1 hpos
    linarith
  exact hd.lt_iff_lt.1 this

/-- **Exercise 14.C.9(b)**, rationing: at a partially insured contract (`c₂ < c₁`) a strictly
risk-averse individual with loss probability `θ` gains from more insurance at fair odds: moving
`t > 0` along the fair-odds line `(c₁ - θ t, c₂ + (1 - θ) t)` raises her expected utility at the
margin, since `u'(c₂) > u'(c₁)`. -/
theorem exercise_14_C_9b_rationed {u du : ℝ → ℝ} (hu : StrictConcaveOn ℝ univ u)
    (hdu : ∀ c, HasDerivAt u (du c) c) {θ c1 c2 : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hc : c2 < c1) :
    0 < (1 - θ) * (du c1 * (-θ)) + θ * (du c2 * (1 - θ)) := by
  have := hi_deriv_anti hu (mem_univ c2) (mem_univ c1) hc (hdu c2).hasDerivWithinAt
    (hdu c1).hasDerivWithinAt
  nlinarith [mul_pos h0 (by linarith : (0:ℝ) < 1 - θ)]

/-- **Exercise 14.C.9(b), an instance** (MWG, p. 510). `u(c) = √c` (`φ(x) = x²`), `W = 25`,
`L = 24`, `θ_L = 1/4`, `θ_H = 1/2`, `λ = 1/2`. The menu with utility levels `(5, 1)` for the
low-risk type (wealth `(25, 1)`: no insurance) and `(3, 3)` for the high-risk type (full insurance
at wealth `9`) satisfies all participation and self-selection constraints and is optimal; the
multipliers are `α = 7`, `β = 3`. -/
theorem exercise_14_C_9b_instance {xL' yL' xH' yH' : ℝ}
    (hIR : 4 ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL')
    (hIC : (1 - 1 / 2) * xL' + 1 / 2 * yL' ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH') :
    1 / 2 * c9Profit (fun x => x ^ 2) 25 24 (1 / 4) xL' yL' +
        (1 - 1 / 2) * c9Profit (fun x => x ^ 2) 25 24 (1 / 2) xH' yH' ≤
      1 / 2 * c9Profit (fun x => x ^ 2) 25 24 (1 / 4) 5 1 +
        (1 - 1 / 2) * c9Profit (fun x => x ^ 2) 25 24 (1 / 2) 3 3 ∧
    -- the candidate satisfies all the constraints (reservation utilities `4` and `3`)
    4 ≤ (1 - 1 / 4) * 5 + 1 / 4 * (1 : ℝ) ∧ 3 ≤ (1 - 1 / 2) * 3 + 1 / 2 * (3 : ℝ) ∧
    (1 - 1 / 2) * 5 + 1 / 2 * (1 : ℝ) ≤ (1 - 1 / 2) * 3 + 1 / 2 * 3 ∧
    (1 - 1 / 4) * 3 + 1 / 4 * (3 : ℝ) ≤ (1 - 1 / 4) * 5 + 1 / 4 * 1 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  refine exercise_14_C_9b (φ := fun x => x ^ 2) (dφ := fun x => 2 * x)
    (by exact (even_two.convexOn_pow (𝕜 := ℝ)))
    (fun x => by simpa using hasDerivAt_pow 2 x) (by norm_num) (by norm_num)
    (α := 7) (β := 3) (rL := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hIR hIC (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.9(b): the shape of every optimal menu

MWG, Exercise 14.C.9(b), p. 510.

The program of `ExerciseC9`, in utility levels `x = u(c₁)`, `y = u(c₂)` with wealth `φ(·)`
(`φ = u⁻¹`), with all four constraints: the participation constraints of both types (reservation
levels `r_L`, `r_H`) and both self-selection constraints. The program is convex, Slater's condition
holds when `θ_L < θ_H`, so by `kt_convexlike` the Kuhn-Tucker conditions are necessary.

* `kt_foc_1d`: a point minimizing `A φ(x + s) + B s` over `s` has `A φ'(x) + B = 0`.
* `exercise_14_C_9b_necessary`: at every optimal menu (when `r_H < r_L`, as for no-insurance
  reservation levels, `c9_r_order`) the high-risk type is fully insured (`x_H = y_H`), the
  low-risk type is partially insured (`y_L < x_L`), the low-risk participation constraint and the
  high-risk self-selection constraint bind. This closes the necessity part left open by the
  sufficiency theorem `exercise_14_C_9b`.
* `exercise_14_C_9b_necessary_instance`: `u = log`, `W = 2`, `L = 3/2`, `θ_L = 1/4`, `θ_H = 1/2`,
  `λ = 8/17`: the optimal menu gives the high-risk type full insurance at wealth `1` and leaves the
  low-risk type uninsured.
-/

namespace MWG.PrincipalAgent

open Set

/-- A point minimizing `s ↦ A φ(x + s) + B s` at `s = 0`, with `φ'(x) = d`, has `A d + B = 0`. -/
theorem kt_foc_1d {φ : ℝ → ℝ} {d x A B : ℝ} (hd : HasDerivAt φ d x)
    (h : ∀ s, A * φ x ≤ A * φ (x + s) + B * s) : A * d + B = 0 := by
  have h1 : HasDerivAt (fun s => φ (x + s)) d 0 :=
    HasDerivAt.comp_const_add x 0 (by simpa using hd)
  have hd' : HasDerivAt (fun s => A * φ (x + s) + B * s) (A * d + B * 1) 0 :=
    (h1.const_mul A).add ((hasDerivAt_id' 0).const_mul B)
  have := IsLocalMin.hasDerivAt_eq_zero
    (Filter.Eventually.of_forall fun s => by simpa using h s) hd'
  linarith

/-- With no insurance as the outside option (`u(W) > u(W - L)`), the low-risk type's reservation
level exceeds the high-risk type's. -/
theorem c9_r_order {a b θL θH : ℝ} (hab : b < a) (hθ : θL < θH) :
    (1 - θH) * a + θH * b < (1 - θL) * a + θL * b := by
  nlinarith

/-- **Exercise 14.C.9(b)** (MWG, p. 510), necessity. Utility levels `(x_L, y_L)`, `(x_H, y_H)`,
`φ` convex and differentiable with `φ'` positive and strictly increasing, `0 < λ < 1`,
`0 < θ_L < θ_H < 1` and `r_H < r_L`. Every menu maximizing the insurer's expected profit subject to
both participation and both self-selection constraints gives the high-risk type full insurance
(`x_H = y_H`) and the low-risk type partial insurance (`y_L < x_L`); the low-risk participation
constraint and the high-risk self-selection constraint bind. -/
theorem exercise_14_C_9b_necessary {φ dφ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hdφ : ∀ x, HasDerivAt φ (dφ x) x) (hd : StrictMono dφ) (hdpos : ∀ x, 0 < dφ x)
    {W L θL θH lam rL rH : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hθL0 : 0 < θL) (hθ : θL < θH)
    (hθH1 : θH < 1) (hr : rH < rL) {xL yL xH yH : ℝ}
    (hIRL : rL ≤ (1 - θL) * xL + θL * yL) (hIRH : rH ≤ (1 - θH) * xH + θH * yH)
    (hICH : (1 - θH) * xL + θH * yL ≤ (1 - θH) * xH + θH * yH)
    (hICL : (1 - θL) * xH + θL * yH ≤ (1 - θL) * xL + θL * yL)
    (hopt : ∀ xL' yL' xH' yH', rL ≤ (1 - θL) * xL' + θL * yL' →
      rH ≤ (1 - θH) * xH' + θH * yH' →
      (1 - θH) * xL' + θH * yL' ≤ (1 - θH) * xH' + θH * yH' →
      (1 - θL) * xH' + θL * yH' ≤ (1 - θL) * xL' + θL * yL' →
      lam * c9Profit φ W L θL xL' yL' + (1 - lam) * c9Profit φ W L θH xH' yH' ≤
        lam * c9Profit φ W L θL xL yL + (1 - lam) * c9Profit φ W L θH xH yH) :
    xH = yH ∧ yL < xL ∧ (1 - θL) * xL + θL * yL = rL ∧
      (1 - θH) * xL + θH * yL = (1 - θH) * xH + θH * yH := by
  let J : ℝ × ℝ × ℝ × ℝ → ℝ := fun z => lam * ((1 - θL) * φ z.1 + θL * φ z.2.1) +
    (1 - lam) * ((1 - θH) * φ z.2.2.1 + θH * φ z.2.2.2)
  let G : Fin 4 → ℝ × ℝ × ℝ × ℝ → ℝ := ![
    fun z => rL - ((1 - θL) * z.1 + θL * z.2.1),
    fun z => rH - ((1 - θH) * z.2.2.1 + θH * z.2.2.2),
    fun z => (1 - θH) * z.1 + θH * z.2.1 - ((1 - θH) * z.2.2.1 + θH * z.2.2.2),
    fun z => (1 - θL) * z.2.2.1 + θL * z.2.2.2 - ((1 - θL) * z.1 + θL * z.2.1)]
  have hG0 : ∀ z, G 0 z = rL - ((1 - θL) * z.1 + θL * z.2.1) := fun z => rfl
  have hG1 : ∀ z, G 1 z = rH - ((1 - θH) * z.2.2.1 + θH * z.2.2.2) := fun z => rfl
  have hG2 : ∀ z, G 2 z = (1 - θH) * z.1 + θH * z.2.1 - ((1 - θH) * z.2.2.1 + θH * z.2.2.2) :=
    fun z => rfl
  have hG3 : ∀ z, G 3 z = (1 - θL) * z.2.2.1 + θL * z.2.2.2 - ((1 - θL) * z.1 + θL * z.2.1) :=
    fun z => rfl
  have hall : ∀ (P : Fin 4 → Prop), P 0 → P 1 → P 2 → P 3 → ∀ i, P i := by
    intro P h0 h1 h2 h3 i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hconvφ : ∀ a b t : ℝ, 0 ≤ t → t ≤ 1 → φ ((1 - t) * a + t * b) ≤ (1 - t) * φ a + t * φ b :=
    fun a b t ht0 ht1 => by
      have := hφ.2 (mem_univ a) (mem_univ b) (by linarith : 0 ≤ 1 - t) ht0 (by ring)
      simpa [smul_eq_mul] using this
  obtain ⟨a, ha, hcs, hlag⟩ := kt_convexlike J G (xL, yL, xH, yH)
    (hall _ (by rw [hG0]; linarith) (by rw [hG1]; linarith) (by rw [hG2]; linarith)
      (by rw [hG3]; linarith))
    (fun z hz => by
      have h := hopt z.1 z.2.1 z.2.2.1 z.2.2.2 (by linarith [hG0 z ▸ hz 0])
        (by linarith [hG1 z ▸ hz 1]) (by linarith [hG2 z ▸ hz 2]) (by linarith [hG3 z ▸ hz 3])
      simp only [c9Profit] at h
      simp only [J]
      nlinarith)
    (fun z0 z1 t ht0 ht1 => by
      refine ⟨((1 - t) * z0.1 + t * z1.1, (1 - t) * z0.2.1 + t * z1.2.1,
        (1 - t) * z0.2.2.1 + t * z1.2.2.1, (1 - t) * z0.2.2.2 + t * z1.2.2.2), ?_,
        hall _ ?_ ?_ ?_ ?_⟩
      · simp only [J]
        have c1 := hconvφ z0.1 z1.1 t ht0 ht1
        have c2 := hconvφ z0.2.1 z1.2.1 t ht0 ht1
        have c3 := hconvφ z0.2.2.1 z1.2.2.1 t ht0 ht1
        have c4 := hconvφ z0.2.2.2 z1.2.2.2 t ht0 ht1
        have k1 : 0 ≤ lam * (1 - θL) := mul_nonneg hl0.le (by linarith)
        have k2 : 0 ≤ lam * θL := mul_nonneg hl0.le hθL0.le
        have k3 : 0 ≤ (1 - lam) * (1 - θH) := mul_nonneg (by linarith) (by linarith)
        have k4 : 0 ≤ (1 - lam) * θH := mul_nonneg (by linarith) (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left c1 k1, mul_le_mul_of_nonneg_left c2 k2,
          mul_le_mul_of_nonneg_left c3 k3, mul_le_mul_of_nonneg_left c4 k4]
      · rw [hG0, hG0, hG0]; apply le_of_eq; ring
      · rw [hG1, hG1, hG1]; apply le_of_eq; ring
      · rw [hG2, hG2, hG2]; apply le_of_eq; ring
      · rw [hG3, hG3, hG3]; apply le_of_eq; ring)
    ⟨(|rL| + |rH| + 1, |rL| + |rH| + 1, |rL| + |rH| + 1 - (θL + θH),
      |rL| + |rH| + 1 + 2 - θL - θH), hall _
      (by rw [hG0]; linarith [le_abs_self rL, abs_nonneg rH])
      (by rw [hG1]; nlinarith [le_abs_self rH, abs_nonneg rL])
      (by rw [hG2]; nlinarith) (by rw [hG3]; nlinarith)⟩
  -- the multipliers
  have hsum : ∀ z, ∑ i, a i * G i z = a 0 * G 0 z + a 1 * G 1 z + a 2 * G 2 z + a 3 * G 3 z :=
    fun z => Fin.sum_univ_four _
  have cs0 := hcs 0
  have cs1 := hcs 1
  have cs2 := hcs 2
  have cs3 := hcs 3
  rw [hG0] at cs0
  rw [hG1] at cs1
  rw [hG2] at cs2
  rw [hG3] at cs3
  simp only at cs0 cs1 cs2 cs3
  have hlag' : ∀ z : ℝ × ℝ × ℝ × ℝ, J (xL, yL, xH, yH) ≤ J z + (a 0 * G 0 z + a 1 * G 1 z +
      a 2 * G 2 z + a 3 * G 3 z) := fun z => by rw [← hsum]; exact hlag z
  -- first-order conditions
  have F1 : lam * (1 - θL) * dφ xL + (-(a 0) * (1 - θL) + a 2 * (1 - θH) - a 3 * (1 - θL)) = 0 :=
    kt_foc_1d (hdφ xL) fun s => by
      have h := hlag' (xL + s, yL, xH, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F2 : lam * θL * dφ yL + (-(a 0) * θL + a 2 * θH - a 3 * θL) = 0 :=
    kt_foc_1d (hdφ yL) fun s => by
      have h := hlag' (xL, yL + s, xH, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F3 : (1 - lam) * (1 - θH) * dφ xH + (-(a 1) * (1 - θH) - a 2 * (1 - θH) +
      a 3 * (1 - θL)) = 0 :=
    kt_foc_1d (hdφ xH) fun s => by
      have h := hlag' (xL, yL, xH + s, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F4 : (1 - lam) * θH * dφ yH + (-(a 1) * θH - a 2 * θH + a 3 * θL) = 0 :=
    kt_foc_1d (hdφ yH) fun s => by
      have h := hlag' (xL, yL, xH, yH + s)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hθL1 : 0 < 1 - θL := by linarith
  have hθH0 : 0 < θH := by linarith
  have hθH1' : 0 < 1 - θH := by linarith
  have hl1' : 0 < 1 - lam := by linarith
  -- the two key combinations
  have KL : lam * θL * (1 - θL) * (dφ xL - dφ yL) = a 2 * (θH - θL) := by
    linear_combination θL * F1 - (1 - θL) * F2
  have KH : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) = -(a 3 * (θH - θL)) := by
    linear_combination θH * F3 - (1 - θH) * F4
  have pL : 0 < lam * θL * (1 - θL) := by positivity
  have pH : 0 < (1 - lam) * θH * (1 - θH) := by positivity
  -- `β_H > 0`
  have ha2pos : 0 < a 2 := by
    rcases ha2.lt_or_eq with h | h
    · exact h
    exfalso
    have hxy : xL = yL := by
      rw [← h, zero_mul] at KL
      have : dφ xL = dφ yL := by
        have := (mul_eq_zero.1 KL).resolve_left pL.ne'
        linarith
      exact hd.injective this
    have hF3 := F3
    rw [← h] at hF3
    have k : a 1 * (1 - θH) = (1 - lam) * (1 - θH) * dφ xH + a 3 * (1 - θL) := by
      linear_combination -hF3
    have k' : 0 < a 1 * (1 - θH) := by
      rw [k]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hl1' hθH1') (hdpos xH))
        (mul_nonneg ha3 hθL1.le)
    have hα1 : 0 < a 1 := (pos_iff_pos_of_mul_pos k').2 hθH1'
    have hbind : (1 - θH) * xH + θH * yH = rH := by
      have := (mul_eq_zero.1 cs1).resolve_left hα1.ne'
      linarith
    subst hxy
    have e1 : (1 - θL) * xL + θL * xL = xL := by ring
    have e2 : (1 - θH) * xL + θH * xL = xL := by ring
    linarith
  have hdL : dφ yL < dφ xL := by
    have : 0 < lam * θL * (1 - θL) * (dφ xL - dφ yL) := by
      rw [KL]; exact mul_pos ha2pos (by linarith)
    have := (pos_iff_pos_of_mul_pos this).1 pL
    linarith
  -- `β_L = 0`
  have ha3z : a 3 = 0 := by
    rcases ha3.lt_or_eq with h | h
    · exfalso
      have b2 : (1 - θH) * xL + θH * yL - ((1 - θH) * xH + θH * yH) = 0 :=
        (mul_eq_zero.1 cs2).resolve_left ha2pos.ne'
      have b3 : (1 - θL) * xH + θL * yH - ((1 - θL) * xL + θL * yL) = 0 :=
        (mul_eq_zero.1 cs3).resolve_left h.ne'
      have k1 : (θH - θL) * ((yH - yL) - (xH - xL)) = 0 := by linear_combination -b3 - b2
      have hdd : yH - yL = xH - xL := by
        have := (mul_eq_zero.1 k1).resolve_left (by linarith)
        linarith
      have hx : xH - xL = 0 := by linear_combination -b2 - θH * hdd
      have hdH : dφ xH < dφ yH := by
        have : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) < 0 := by
          rw [KH]; exact neg_lt_zero.2 (mul_pos h (by linarith))
        have := neg_of_mul_neg_right this pH.le
        linarith
      have hxe : xH = xL := by linarith
      have hye : yH = yL := by linarith
      rw [hxe, hye] at hdH
      linarith
    · exact h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha3z] at KH
    have : dφ xH = dφ yH := by
      have := (mul_eq_zero.1 (by linarith : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) = 0))
      rcases this with h | h
      · exact absurd h pH.ne'
      · linarith
    exact hd.injective this
  · exact hd.lt_iff_lt.1 hdL
  · have hα0 : 0 < a 0 := by
      rw [ha3z] at F1
      have k : a 0 * (1 - θL) = lam * (1 - θL) * dφ xL + a 2 * (1 - θH) := by
        linear_combination -F1
      have k' : 0 < a 0 * (1 - θL) := by
        rw [k]
        exact add_pos (mul_pos (mul_pos hl0 hθL1) (hdpos xL)) (mul_pos ha2pos hθH1')
      exact (pos_iff_pos_of_mul_pos k').2 hθL1
    have := (mul_eq_zero.1 cs0).resolve_left hα0.ne'
    linarith
  · have := (mul_eq_zero.1 cs2).resolve_left ha2pos.ne'
    linarith

/-- **Exercise 14.C.9(b), an instance of the necessity theorem** (MWG, p. 510). `u = log`
(`φ = exp`), `W = 2`, `L = 3/2`, `θ_L = 1/4`, `θ_H = 1/2`, `λ = 8/17`: the reservation levels are
`r_L = (log 2)/2` and `r_H = 0`. The menu `(x_L, y_L) = (log 2, -log 2)` (no insurance) and
`(x_H, y_H) = (0, 0)` (full insurance at wealth `1`) is optimal (sufficiency, with `α = 22/17`,
`β = 9/17`), and the necessity theorem applies to it. -/
theorem exercise_14_C_9b_necessary_instance :
    (0 : ℝ) = 0 ∧ -Real.log 2 < Real.log 2 ∧
      (1 - 1 / 4) * Real.log 2 + 1 / 4 * -Real.log 2 = Real.log 2 / 2 ∧
      (1 - 1 / 2) * Real.log 2 + 1 / 2 * -Real.log 2 = (1 - 1 / 2) * 0 + 1 / 2 * (0 : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hopt : ∀ xL' yL' xH' yH' : ℝ, Real.log 2 / 2 ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL' →
      0 ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH' →
      (1 - 1 / 2) * xL' + 1 / 2 * yL' ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH' →
      (1 - 1 / 4) * xH' + 1 / 4 * yH' ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL' →
      8 / 17 * c9Profit Real.exp 2 (3 / 2) (1 / 4) xL' yL' +
          (1 - 8 / 17) * c9Profit Real.exp 2 (3 / 2) (1 / 2) xH' yH' ≤
        8 / 17 * c9Profit Real.exp 2 (3 / 2) (1 / 4) (Real.log 2) (-Real.log 2) +
          (1 - 8 / 17) * c9Profit Real.exp 2 (3 / 2) (1 / 2) 0 0 := by
    intro xL' yL' xH' yH' h1 _ h3 _
    have e1 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, e1]; norm_num
    refine exercise_14_C_9b (φ := Real.exp) (dφ := Real.exp) convexOn_exp
      (fun x => Real.hasDerivAt_exp x) (α := 22 / 17) (β := 9 / 17) (rL := Real.log 2 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ h1 h3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [Real.exp_zero]; norm_num
    · rw [Real.exp_zero]; norm_num
    · rw [e1]; norm_num
    · rw [e2]; norm_num
    · ring
    · ring
  have hn := exercise_14_C_9b_necessary (φ := Real.exp) (dφ := Real.exp) convexOn_exp
    (fun x => Real.hasDerivAt_exp x) Real.exp_strictMono Real.exp_pos (W := 2) (L := 3 / 2)
    (lam := 8 / 17) (rH := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (by ring_nf; exact le_refl _) (by norm_num)
    (by ring_nf; exact le_refl _) (by nlinarith) hopt
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.7 (J. Tirole)

MWG, Exercise 14.C.7, p. 509.

A type-`θ` consumer buying `x ∈ [0, 1]` units for a total payment `T` gets `θ v(x) - T` with
`v(x) = (1 - (1 - x)²)/2 = x - x²/2`; `θ_L < θ_H`, a fraction `λ` of consumers is of type `θ_L`;
unit cost `c > 0`.

* `c7_demand`: at a linear price `p ∈ [0, θ]` a type-`θ` consumer buys `1 - p/θ`;
  `c7_surplus`: his surplus is `(θ - p)²/(2θ)`.
* `exercise_14_C_7a_theta`, `exercise_14_C_7a_lambda`: (a) the nondiscriminating monopolist serves
  both types (charges `p < θ_L`) if `θ_L > (θ_H + c)/2`, or if `λ (θ_L - c)²/θ_L >
  (1 - λ)(θ_H - c)²/θ_H` (true for `λ` near `1`); `exercise_14_C_7a_price`: the optimal price among
  those serving both.
* `exercise_14_C_7b`: (b) third-degree discrimination: `p_i = (θ_i + c)/2`.
* `exercise_14_C_7c`: (c) the optimal two-part tariff serving both types (when its profit is
  concave in `p`) has `p = cA/B > c` with `F = (θ_L - p)²/(2θ_L)`.
* `exercise_14_C_7d`: (d) the optimal nonlinear tariff: `x_H = 1 - c/θ_H` (efficient),
  `x_L = 1 - λc/K` with `K = λθ_L - (1 - λ)(θ_H - θ_L)`; `exercise_14_C_7d_compare`: the high type
  buys more than in (b) and (c), the low type less than efficiently.
-/

namespace MWG.PrincipalAgent

/-- `v(x) = x - x²/2`. -/
noncomputable def c7v (x : ℝ) : ℝ := x - x ^ 2 / 2

/-- Demand at a linear price `p ∈ [0, θ]` (MWG, Exercise 14.C.7(a)). -/
theorem c7_demand {θ p : ℝ} (hθ : 0 < θ) (x : ℝ) :
    θ * c7v x - p * x ≤ θ * c7v (1 - p / θ) - p * (1 - p / θ) := by
  have : θ * c7v (1 - p / θ) - p * (1 - p / θ) - (θ * c7v x - p * x) =
      θ / 2 * (x - (1 - p / θ)) ^ 2 := by
    unfold c7v; field_simp; ring
  nlinarith [sq_nonneg (x - (1 - p / θ))]

/-- The consumer's surplus at the price `p`: `(θ - p)²/(2θ)`. -/
theorem c7_surplus {θ p : ℝ} (hθ : 0 < θ) :
    θ * c7v (1 - p / θ) - p * (1 - p / θ) = (θ - p) ^ 2 / (2 * θ) := by
  unfold c7v; field_simp; ring

/-- Demand of a type-`θ` consumer at price `p` (zero when `p ≥ θ`). -/
noncomputable def c7D (θ p : ℝ) : ℝ := if p < θ then 1 - p / θ else 0

/-- The nondiscriminating monopolist's profit at price `p`. -/
noncomputable def c7Pi (θL θH lam c p : ℝ) : ℝ := (p - c) * (lam * c7D θL p + (1 - lam) * c7D θH p)

/-- The profit from one type at a price below its valuation is at most `(θ - c)²/(4θ)`. -/
theorem c7_one_type {θ c p : ℝ} (hθ : 0 < θ) : (p - c) * (1 - p / θ) ≤ (θ - c) ^ 2 / (4 * θ) := by
  have : (θ - c) ^ 2 / (4 * θ) - (p - c) * (1 - p / θ) = (p - (θ + c) / 2) ^ 2 / θ := by
    field_simp; ring
  have : 0 ≤ (p - (θ + c) / 2) ^ 2 / θ := by positivity
  linarith

/-- At prices `p ≥ θ_L` only high types buy, so profit is at most `(1 - λ)(θ_H - c)²/(4θ_H)`. -/
theorem c7_bound_high {θL θH lam c p : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam ≤ 1) (hp : θL ≤ p) :
    c7Pi θL θH lam c p ≤ (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) := by
  have hH : 0 < θH := hL.trans hLH
  have hDL : c7D θL p = 0 := by simp [c7D, not_lt.2 hp]
  unfold c7Pi; rw [hDL]
  have hb : 0 ≤ (θH - c) ^ 2 / (4 * θH) := by positivity
  unfold c7D
  split_ifs with h
  · have := c7_one_type (c := c) (p := p) hH
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 1 - lam)]
  · simp only [mul_zero, add_zero]; nlinarith

/-- **Exercise 14.C.7(a)** (MWG, p. 509), "`θ_L` large enough": if `θ_L > (θ_H + c)/2` the price
`(θ_H + c)/2` (optimal when selling to high types only) also sells to low types and beats every
price `p ≥ θ_L`; so every optimal price serves both types. -/
theorem exercise_14_C_7a_theta {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hθ : (θH + c) / 2 < θL) (p : ℝ) (hp : θL ≤ p) :
    c7Pi θL θH lam c p < c7Pi θL θH lam c ((θH + c) / 2) := by
  have hH : 0 < θH := hL.trans hLH
  have hb := c7_bound_high (c := c) hL hLH hl1.le hp
  have hp0 : (θH + c) / 2 < θH := by linarith
  have e : c7Pi θL θH lam c ((θH + c) / 2) = lam * (((θH + c) / 2 - c) * (1 - (θH + c) / 2 / θL)) +
      (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) := by
    simp only [c7Pi, c7D, hθ, hp0, ↓reduceIte]
    field_simp; ring
  rw [e]
  have h1 : 0 < (θH + c) / 2 - c := by linarith
  have h2 : 0 < 1 - (θH + c) / 2 / θL := by rw [sub_pos, div_lt_one hL]; exact hθ
  nlinarith [mul_pos hl0 (mul_pos h1 h2)]

/-- **Exercise 14.C.7(a)** (MWG, p. 509), "`λ` large enough": if
`λ(θ_L - c)²/(4θ_L) > (1 - λ)(θ_H - c)²/(4θ_H)` (which holds for `λ` close to `1` when `c < θ_L`),
the price `(θ_L + c)/2` beats every price `p ≥ θ_L`. -/
theorem exercise_14_C_7a_lambda {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam ≤ 1) (hc' : c < θL)
    (hcond : (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) < lam * ((θL - c) ^ 2 / (4 * θL)))
    (p : ℝ) (hp : θL ≤ p) : c7Pi θL θH lam c p < c7Pi θL θH lam c ((θL + c) / 2) := by
  have hH : 0 < θH := hL.trans hLH
  have hb := c7_bound_high (c := c) hL hLH hl1 hp
  have hp1 : (θL + c) / 2 < θL := by linarith
  have hp2 : (θL + c) / 2 < θH := by linarith
  have e : c7Pi θL θH lam c ((θL + c) / 2) = lam * ((θL - c) ^ 2 / (4 * θL)) +
      (1 - lam) * (((θL + c) / 2 - c) * (1 - (θL + c) / 2 / θH)) := by
    simp only [c7Pi, c7D, hp1, hp2, ↓reduceIte]
    field_simp; ring
  rw [e]
  have h1 : 0 < (θL + c) / 2 - c := by linarith
  have h2 : 0 < 1 - (θL + c) / 2 / θH := by rw [sub_pos, div_lt_one hH]; exact hp2
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (mul_pos h1 h2).le]

/-- **Exercise 14.C.7(a)**, the price when both types are served (MWG, p. 509): among prices
`p ≤ θ_L` the profit is `(p - c)(1 - pA)` with `A = λ/θ_L + (1 - λ)/θ_H`, maximized at
`p* = (1/A + c)/2` (when `p* ≤ θ_L`). -/
theorem exercise_14_C_7a_price {A c p : ℝ} (hA : 0 < A) :
    (p - c) * (1 - p * A) ≤ ((1 / A + c) / 2 - c) * (1 - (1 / A + c) / 2 * A) := by
  have : ((1 / A + c) / 2 - c) * (1 - (1 / A + c) / 2 * A) - (p - c) * (1 - p * A) =
      A * (p - (1 / A + c) / 2) ^ 2 := by field_simp; ring
  nlinarith [mul_nonneg hA.le (sq_nonneg (p - (1 / A + c) / 2))]

/-- **Exercise 14.C.7(b)** (MWG, p. 509). Charging `θ_i`-consumers `p_i = (θ_i + c)/2` is optimal
for a monopolist who can tell the types apart (but charges linear prices). -/
theorem exercise_14_C_7b {θ c : ℝ} (hθ : 0 < θ) (p : ℝ) :
    (p - c) * (1 - p / θ) ≤ ((θ + c) / 2 - c) * (1 - (θ + c) / 2 / θ) := by
  have h := c7_one_type (c := c) (p := p) hθ
  have : ((θ + c) / 2 - c) * (1 - (θ + c) / 2 / θ) = (θ - c) ^ 2 / (4 * θ) := by
    field_simp; ring
  linarith

/-- **Exercise 14.C.7(c)** (MWG, p. 509). The two-part tariff `(F, p)` serving both types sets
`F = (θ_L - p)²/(2θ_L)` (the low type's surplus); its profit
`(θ_L - p)²/(2θ_L) + (p - c)(1 - pA)` is concave in `p` iff `B = 2A - 1/θ_L > 0`, and then it is
maximized at `p* = cA/B`, which exceeds marginal cost `c` (high types buy more, so the unit price
extracts some of their surplus). -/
theorem exercise_14_C_7c {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl1 : lam < 1)
    (hc : 0 < c) (hB : 0 < 2 * (lam / θL + (1 - lam) / θH) - 1 / θL) (p : ℝ) :
    let A := lam / θL + (1 - lam) / θH
    let B := 2 * A - 1 / θL
    (θL - p) ^ 2 / (2 * θL) + (p - c) * (1 - p * A) ≤
        (θL - c * A / B) ^ 2 / (2 * θL) + (c * A / B - c) * (1 - c * A / B * A) ∧
      c < c * A / B := by
  intro A B
  have hH : 0 < θH := hL.trans hLH
  have hf : ∀ q, (θL - q) ^ 2 / (2 * θL) + (q - c) * (1 - q * A) =
      θL / 2 - c - B / 2 * q ^ 2 + c * A * q := by
    intro q; simp only [B]; field_simp; ring
  have hAL : A < 1 / θL := by
    have h1 : (1 - lam) / θH < (1 - lam) / θL := div_lt_div_of_pos_left (by linarith) hL hLH
    have h2 : lam / θL + (1 - lam) / θL = 1 / θL := by field_simp; ring
    simp only [A]; linarith
  have hBA : B < A := by simp only [B]; linarith
  have hB' : 0 < B := hB
  clear_value A B
  refine ⟨?_, ?_⟩
  · rw [hf, hf]
    have : -(B / 2) * (c * A / B) ^ 2 + c * A * (c * A / B) - (-(B / 2) * p ^ 2 + c * A * p) =
        B / 2 * (p - c * A / B) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hB'.le (sq_nonneg (p - c * A / B))]
  · rw [lt_div_iff₀ hB']
    nlinarith

/-- The nonlinear tariff of part (d): quantities `x_H, x_L ∈ [0, 1]` and payments. -/
def C7Feas (θL θH xH TH xL TL : ℝ) : Prop :=
  0 ≤ xH ∧ xH ≤ 1 ∧ 0 ≤ xL ∧ xL ≤ 1 ∧ 0 ≤ θL * c7v xL - TL ∧ 0 ≤ θH * c7v xH - TH ∧
    θH * c7v xL - TL ≤ θH * c7v xH - TH ∧ θL * c7v xH - TH ≤ θL * c7v xL - TL

/-- The monopolist's profit from a nonlinear tariff. -/
def c7Profit (lam c xH TH xL TL : ℝ) : ℝ := lam * (TL - c * xL) + (1 - lam) * (TH - c * xH)

/-- **Exercise 14.C.7(d)** (MWG, p. 509). The fully optimal nonlinear tariff: with
`K = λθ_L - (1 - λ)(θ_H - θ_L) > λc` and `c ≤ θ_H`, the menu `x_H = 1 - c/θ_H`,
`x_L = 1 - λc/K`, `T_L = θ_L v(x_L)`, `T_H = θ_H v(x_H) - (θ_H - θ_L) v(x_L)` is feasible and earns
at least as much as every feasible menu. -/
theorem exercise_14_C_7d {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hc : 0 < c) (hcH : c ≤ θH)
    (hK : lam * c < lam * θL - (1 - lam) * (θH - θL)) :
    let K := lam * θL - (1 - lam) * (θH - θL)
    let xH := 1 - c / θH
    let xL := 1 - lam * c / K
    let TL := θL * c7v xL
    let TH := θH * c7v xH - (θH - θL) * c7v xL
    C7Feas θL θH xH TH xL TL ∧
      ∀ xH' TH' xL' TL', C7Feas θL θH xH' TH' xL' TL' →
        c7Profit lam c xH' TH' xL' TL' ≤ c7Profit lam c xH TH xL TL := by
  intro K xH xL TL TH
  have hH : 0 < θH := hL.trans hLH
  have hKpos : 0 < K := by
    have : 0 < lam * c := mul_pos hl0 hc
    simp only [K]; linarith
  have hxH0 : 0 ≤ xH := by simp only [xH]; rw [sub_nonneg, div_le_one hH]; exact hcH
  have hxH1 : xH ≤ 1 := by
    have : 0 ≤ c / θH := by positivity
    simp only [xH]; linarith
  have hxL0 : 0 ≤ xL := by
    simp only [xL]; rw [sub_nonneg, div_le_one hKpos]; exact hK.le
  have hxL1 : xL ≤ 1 := by
    have : 0 ≤ lam * c / K := by positivity
    simp only [xL]; linarith
  have hord : xL ≤ xH := by
    simp only [xL, xH]
    have : c / θH ≤ lam * c / K := by
      rw [div_le_div_iff₀ hH hKpos]
      have : K ≤ lam * θH := by simp only [K]; nlinarith
      nlinarith
    linarith
  have hvmono : c7v xL ≤ c7v xH := by unfold c7v; nlinarith
  refine ⟨⟨hxH0, hxH1, hxL0, hxL1, by simp only [TL]; linarith, ?_, ?_, ?_⟩, ?_⟩
  · simp only [TH]
    have : 0 ≤ c7v xL := by unfold c7v; nlinarith
    nlinarith
  · simp only [TH, TL]; nlinarith
  · simp only [TH, TL]; nlinarith
  · intro xH' TH' xL' TL' hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    -- the bound from (i) and (iii)
    have hTL : TL' ≤ θL * c7v xL' := by linarith
    have hTH : TH' ≤ θH * c7v xH' - (θH - θL) * c7v xL' := by linarith
    have bound : c7Profit lam c xH' TH' xL' TL' ≤
        (1 - lam) * (θH * c7v xH' - c * xH') +
          (lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL') := by
      unfold c7Profit
      nlinarith [mul_le_mul_of_nonneg_left hTL hl0.le,
        mul_le_mul_of_nonneg_left hTH (by linarith : (0:ℝ) ≤ 1 - lam)]
    have eqv : c7Profit lam c xH TH xL TL =
        (1 - lam) * (θH * c7v xH - c * xH) +
          (lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL) := by
      unfold c7Profit; simp only [TH, TL]; ring
    -- both pieces are maximized at the candidate (completing squares)
    have hSH : θH * c7v xH' - c * xH' ≤ θH * c7v xH - c * xH := by
      have : θH * c7v xH - c * xH - (θH * c7v xH' - c * xH') = θH / 2 * (xH' - xH) ^ 2 := by
        simp only [xH]; unfold c7v; field_simp; ring
      nlinarith [mul_nonneg hH.le (sq_nonneg (xH' - xH))]
    have hQ : lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL' ≤
        lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL := by
      have : lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL -
          (lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL') =
            K / 2 * (xL' - xL) ^ 2 := by
        have hK0 : K ≠ 0 := hKpos.ne'
        simp only [xL]; unfold c7v; field_simp; simp only [K]; ring
      nlinarith [mul_nonneg hKpos.le (sq_nonneg (xL' - xL))]
    rw [eqv]
    nlinarith [mul_le_mul_of_nonneg_left hSH (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Exercise 14.C.7(d)**, comparing quantities (MWG, p. 509). The high type's quantity
`1 - c/θ_H` under the optimal nonlinear tariff exceeds his quantity under third-degree
discrimination (`(θ_H - c)/(2θ_H)`) and is at least that under a two-part tariff with unit price
`p ≥ c`; the low type's quantity `1 - λc/K` is below the efficient `1 - c/θ_L`. -/
theorem exercise_14_C_7d_compare {θL θH lam c p : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam < 1) (hc : 0 < c) (hcH : c < θH) (hp : c ≤ p)
    (hK : 0 < lam * θL - (1 - lam) * (θH - θL)) :
    (θH - c) / (2 * θH) < 1 - c / θH ∧ 1 - p / θH ≤ 1 - c / θH ∧
      1 - lam * c / (lam * θL - (1 - lam) * (θH - θL)) < 1 - c / θL := by
  have hH : 0 < θH := hL.trans hLH
  refine ⟨?_, ?_, ?_⟩
  · have e : (θH - c) / (2 * θH) = 1 - c / θH - (θH - c) / (2 * θH) := by field_simp; ring
    have : 0 < (θH - c) / (2 * θH) := div_pos (by linarith) (by positivity)
    linarith
  · have := div_le_div_of_nonneg_right hp hH.le; linarith
  · have : c / θL < lam * c / (lam * θL - (1 - lam) * (θH - θL)) := by
      rw [div_lt_div_iff₀ hL hK]
      nlinarith [mul_pos (mul_pos hc (by linarith : (0:ℝ) < 1 - lam)) (sub_pos.2 hLH)]
    linarith

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.B.1

MWG, Exercise 14.B.1, p. 507: with a general utility `u(w, e)` (not of the form `v(w) - g(e)`),
must the reservation utility constraint bind in an optimal contract? No.

Two profit levels; `f(π_H | e_H) = 1/2 > f(π_H | e_L) = 5/16`; `u(w, e_L) = w` and
`u(w, e_H) = w - c(w)` with `c(w) = 1/8 + ((1 - w)⁺)³` (the disutility of effort falls with
income); `ū = 0`. Then `u_w > 0`, `u_ww ≤ 0` (`c` is convex and `C¹`; here
`c(w) = 1/8 + ((1 - w)³ + |1 - w|³)/2`), and `u(w, e_H) < u(w, e_L)`.

* `b1_c_deriv`, `b1_uw_pos`, `b1_c_convex`, `b1_uH_lt`: the model satisfies MWG's assumptions.
* `exercise_14_B_1`: the scheme `w(π_L) = 1/2`, `w(π_H) = 3/2` implements `e_H` at expected wage
  `1`; every scheme satisfying the incentive constraint costs at least `1`, with equality only for
  this scheme; and it gives the manager `13/16 > ū = 0`. So the unique optimal contract for `e_H`
  has a slack participation constraint (lowering wages would violate incentive compatibility).
-/

namespace MWG.PrincipalAgent

/-- The disutility of high effort in money terms, `c(w) = 1/8 + ((1 - w)⁺)³`. -/
noncomputable def b1c (w : ℝ) : ℝ := 1 / 8 + ((1 - w) ^ 3 + ((1 - w) ^ 2) ^ (3 / 2 : ℝ)) / 2

/-- Its derivative, `-3 ((1 - w)⁺)²`. -/
noncomputable def b1dc (w : ℝ) : ℝ := (-3 * (1 - w) ^ 2 - 3 * (1 - w) * |1 - w|) / 2

theorem b1_rpow32 (t : ℝ) : (t ^ 2) ^ (3 / 2 : ℝ) = |t| ^ 3 := by
  rw [← sq_abs t, ← Real.rpow_natCast |t| 2, ← Real.rpow_mul (abs_nonneg t)]
  norm_num

theorem b1_rpow12 (t : ℝ) : (t ^ 2) ^ (1 / 2 : ℝ) = |t| := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- `c(w) = 1/8 + ((1 - w)³ + |1 - w|³)/2`. -/
theorem b1c_eq (w : ℝ) : b1c w = 1 / 8 + ((1 - w) ^ 3 + |1 - w| ^ 3) / 2 := by
  rw [b1c, b1_rpow32]

/-- `c` is differentiable with derivative `b1dc`. -/
theorem b1_c_deriv (w : ℝ) : HasDerivAt b1c (b1dc w) w := by
  have h0 : HasDerivAt (fun w : ℝ => 1 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h1 := h0.pow 3
  have h2 := (h0.pow 2).rpow_const (p := 3 / 2) (Or.inr (by norm_num))
  have h : HasDerivAt b1c ((↑3 * (1 - w) ^ (3 - 1) * -1 + ↑2 * (1 - w) ^ (2 - 1) * -1 * (3 / 2) *
      ((1 - w) ^ 2) ^ ((3 : ℝ) / 2 - 1)) / 2) w := ((h1.add h2).div_const 2).const_add (1 / 8)
  refine h.congr_deriv ?_
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, b1_rpow12]
  unfold b1dc; push_cast; ring

/-- `c(w) ≥ 1/8`, so `u(w, e_H) < u(w, e_L)`. -/
theorem b1_c_ge (w : ℝ) : 1 / 8 ≤ b1c w := by
  rw [b1c_eq]
  have : -(1 - w) ^ 3 ≤ |1 - w| ^ 3 := by
    rcases le_total 0 (1 - w) with h | h
    · rw [abs_of_nonneg h]; nlinarith [pow_nonneg h 3]
    · rw [abs_of_nonpos h]; ring_nf; exact le_refl _
  linarith

theorem b1_uH_lt (w : ℝ) : w - b1c w < w := by have := b1_c_ge w; linarith

/-- `c' ≤ 0`, so `u_w(w, e_H) = 1 - c'(w) ≥ 1 > 0`. -/
theorem b1_uw_pos (w : ℝ) : 0 < 1 - b1dc w := by
  unfold b1dc
  have : -(1 - w) * |1 - w| ≤ (1 - w) ^ 2 := by
    rw [← sq_abs (1 - w), sq]
    nlinarith [neg_abs_le (1 - w), abs_nonneg (1 - w)]
  nlinarith [sq_nonneg (1 - w)]

/-- `c'` is nondecreasing, so `c` is convex and `u(·, e_H)` is concave (`u_ww ≤ 0`). -/
theorem b1_c_convex : ConvexOn ℝ Set.univ b1c := by
  have hd : deriv b1c = b1dc := funext fun w => (b1_c_deriv w).deriv
  refine Monotone.convexOn_univ_of_deriv (fun w => (b1_c_deriv w).differentiableAt) ?_
  rw [hd]
  intro a b hab
  unfold b1dc
  -- with `s = 1 - a ≥ t = 1 - b`, `s² + s|s| ≥ t² + t|t|`
  set s := 1 - a
  set t := 1 - b
  have hts : t ≤ s := by simp only [s, t]; linarith
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (ht.trans hts)]; nlinarith
  · rcases le_total 0 s with hs | hs
    · rw [abs_of_nonpos ht, abs_of_nonneg hs]; nlinarith
    · rw [abs_of_nonpos ht, abs_of_nonpos hs]; nlinarith

/-- The tangent line of `c` at `1/2`: `c(x) ≥ 1/4 - (3/4)(x - 1/2)`. -/
theorem b1_c_tangent (x : ℝ) : 1 / 4 - 3 / 4 * (x - 1 / 2) ≤ b1c x := by
  rw [b1c_eq]
  rcases le_total 0 (1 - x) with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg (sq_nonneg (1 - x - 1 / 2)) (by linarith : (0:ℝ) ≤ 1 - x + 1)]
  · rw [abs_of_nonpos h]
    nlinarith

theorem b1_c_half : b1c (1 / 2) = 1 / 4 := by rw [b1c_eq]; norm_num [abs_of_pos]

theorem b1_c_threehalf : b1c (3 / 2) = 1 / 8 := by rw [b1c_eq]; norm_num [abs_of_neg]

/-- **Exercise 14.B.1** (MWG, p. 507). In the model above (`u(w, e_H) = w - c(w)`, `u(w, e_L) = w`,
`f(π_H|e_H) = 1/2`, `f(π_H|e_L) = 5/16`, `ū = 0`), the scheme `(w_L, w_H) = (1/2, 3/2)` satisfies
the incentive constraint for `e_H` with expected wage `1`, every scheme satisfying the incentive
constraint has expected wage at least `1` with equality only for this scheme, and the manager's
expected utility under it is `13/16 > 0 = ū`: the reservation utility constraint does not bind in
the (unique) optimal contract. -/
theorem exercise_14_B_1 :
    let EUH : ℝ → ℝ → ℝ := fun w0 w1 => 1 / 2 * (w1 - b1c w1) + 1 / 2 * (w0 - b1c w0)
    let EUL : ℝ → ℝ → ℝ := fun w0 w1 => 5 / 16 * w1 + 11 / 16 * w0
    EUL (1 / 2) (3 / 2) ≤ EUH (1 / 2) (3 / 2) ∧ 1 / 2 * (1 / 2) + 1 / 2 * (3 / 2 : ℝ) = 1 ∧
      EUH (1 / 2) (3 / 2) = 13 / 16 ∧
      ∀ w0 w1, EUL w0 w1 ≤ EUH w0 w1 →
        1 ≤ 1 / 2 * w0 + 1 / 2 * w1 ∧
          (1 / 2 * w0 + 1 / 2 * w1 = 1 → w0 = 1 / 2 ∧ w1 = 3 / 2) := by
  intro EUH EUL
  simp only [EUH, EUL, b1_c_half, b1_c_threehalf]
  refine ⟨by norm_num, by norm_num, by norm_num, fun w0 w1 hIC => ?_⟩
  have t0 := b1_c_tangent w0
  have t1 := b1_c_ge w1
  refine ⟨by linarith, fun heq => ?_⟩
  -- equality forces equality in the tangent bound at `w₀`, hence `w₀ = 1/2`
  have he : b1c w0 = 1 / 4 - 3 / 4 * (w0 - 1 / 2) := by linarith
  have h0 : w0 = 1 / 2 := by
    rw [b1c_eq] at he
    rcases le_total 0 (1 - w0) with h | h
    · rw [abs_of_nonneg h] at he
      have : (1 - w0 - 1 / 2) ^ 2 * (1 - w0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h' | h'
      · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h']
      · linarith
    · rw [abs_of_nonpos h] at he
      nlinarith
  exact ⟨h0, by rw [h0] at heq; linarith⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.1 (finitely many states)

MWG, Exercise 14.C.1, p. 508, and footnote 16, p. 497.

States `θ₀ < θ₁ < ⋯ < θ_{N-1}` with probabilities `p_i`, an infinitely risk-averse manager with
reservation level `c = v⁻¹(ū)`, and contracts `(w_i, e_i)`, `e_i ≥ 0`. The single-crossing
property: for `i < j`, `e ↦ g(e, θ_i) - g(e, θ_j)` is strictly increasing on `[0, ∞)`, and
`g(0, θ) = 0`. Write `x_i = w_i - g(e_i, θ_i)` for the manager's utility (money) in state `θ_i`
and `D_k(e) = g(e, θ_k) - g(e, θ_{k+1})`.

* `exercise_14_C_1_mono`: incentive compatibility forces nondecreasing efforts.
* `exercise_14_C_1_IR`: the reservation constraint of the lowest state and the incentive
  constraints imply all reservation constraints (Lemma 14.C.1).
* `exercise_14_C_1_rent`: the local downward incentive constraints give the rent
  `x_i ≥ c + Σ_{k<i} D_k(e_k)`; `exercise_14_C_1_bound`: hence the owner earns at most
  `Σ_i p_i (π(e_i) - g(e_i, θ_i)) - c - Σ_i p_i Σ_{k<i} D_k(e_k)`.
* `exercise_14_C_1_local`: footnote 16: with nondecreasing efforts, if the local downward
  constraints bind, all the incentive constraints hold. So the bound is attained by the contract
  in which `x_0 = c` and the local downward constraints bind, and an optimal contract maximizes
  the virtual surplus over nondecreasing efforts; the top state's effort enters only its own term
  (no distortion at the top), and every other effort is weighed against its rent
  `(Σ_{i>k} p_i) D_k(e_k)` (downward distortion).
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- The incentive constraint: in state `θ_i` the manager prefers `(w_i, e_i)` to `(w_j, e_j)`. -/
def C1IC (g : ℝ → ℝ → ℝ) (θ w e : ℕ → ℝ) (i j : ℕ) : Prop :=
  w j - g (e j) (θ i) ≤ w i - g (e i) (θ i)

/-- **Exercise 14.C.1** (MWG, p. 508). With single crossing, the incentive constraints between
`i < j` force `e_i ≤ e_j`. -/
theorem exercise_14_C_1_mono {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {i j : ℕ}
    (hsc : StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (hei : 0 ≤ e i)
    (hej : 0 ≤ e j) (h1 : C1IC g θ w e i j) (h2 : C1IC g θ w e j i) : e i ≤ e j := by
  unfold C1IC at h1 h2
  have : g (e i) (θ i) - g (e i) (θ j) ≤ g (e j) (θ i) - g (e j) (θ j) := by linarith
  exact (hsc.le_iff_le hei hej).1 this

/-- **Exercise 14.C.1**, Lemma 14.C.1 for `N` states: the reservation constraint of the lowest
state and the incentive constraint of state `i` towards state `0` give state `i`'s reservation
constraint. -/
theorem exercise_14_C_1_IR {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ} {i : ℕ}
    (hsc : StrictMonoOn (fun x => g x (θ 0) - g x (θ i)) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (he0 : 0 ≤ e 0) (hIR : c ≤ w 0 - g (e 0) (θ 0)) (hIC : C1IC g θ w e i 0) :
    c ≤ w i - g (e i) (θ i) := by
  have hD : g 0 (θ 0) - g 0 (θ i) ≤ g (e 0) (θ 0) - g (e 0) (θ i) :=
    hsc.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 he0) he0
  rw [hg0, hg0] at hD
  unfold C1IC at hIC
  linarith

/-- `D_k(e) = g(e, θ_k) - g(e, θ_{k+1})`. -/
def c1D (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (k : ℕ) (e : ℝ) : ℝ := g e (θ k) - g e (θ (k + 1))

/-- **Exercise 14.C.1**, the rents: the local downward constraints and the lowest state's
reservation constraint give `x_i ≥ c + Σ_{k<i} D_k(e_k)`. -/
theorem exercise_14_C_1_rent {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ}
    (hIR : c ≤ w 0 - g (e 0) (θ 0)) (hloc : ∀ k, C1IC g θ w e (k + 1) k) :
    ∀ i, c + ∑ k ∈ range i, c1D g θ k (e k) ≤ w i - g (e i) (θ i) := by
  intro i
  induction i with
  | zero => simpa using hIR
  | succ n ih =>
    rw [sum_range_succ]
    have := hloc n
    have hD : c1D g θ n (e n) = g (e n) (θ n) - g (e n) (θ (n + 1)) := rfl
    unfold C1IC at this
    linarith

/-- **Exercise 14.C.1**, the bound on the owner's profit (MWG, p. 508): with probabilities
`p_i ≥ 0`, every contract satisfying the lowest reservation constraint and the local downward
incentive constraints earns at most
`Σ_{i<N} p_i [π(e_i) - g(e_i, θ_i)] - c Σ p_i - Σ_{i<N} p_i Σ_{k<i} D_k(e_k)`. -/
theorem exercise_14_C_1_bound {g : ℝ → ℝ → ℝ} {θ w e p : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ}
    {N : ℕ} (hp : ∀ i, 0 ≤ p i) (hIR : c ≤ w 0 - g (e 0) (θ 0))
    (hloc : ∀ k, C1IC g θ w e (k + 1) k) :
    ∑ i ∈ range N, p i * (prof (e i) - w i) ≤
      ∑ i ∈ range N, p i * (prof (e i) - g (e i) (θ i)) - c * ∑ i ∈ range N, p i -
        ∑ i ∈ range N, p i * ∑ k ∈ range i, c1D g θ k (e k) := by
  have hr := exercise_14_C_1_rent hIR hloc
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left (hr i) (hp i)
  nlinarith

/-- **Footnote 16 / Exercise 14.C.1**: with nondecreasing efforts and single crossing between
adjacent states, if every local downward incentive constraint binds then every incentive
constraint holds (downward and upward). -/
theorem exercise_14_C_1_local {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ}
    (hsc : ∀ k, MonotoneOn (c1D g θ k) (Ici 0)) (he : ∀ k, 0 ≤ e k) (hmono : Monotone e)
    (hbind : ∀ k, w (k + 1) - g (e (k + 1)) (θ (k + 1)) = w k - g (e k) (θ (k + 1))) :
    ∀ i j, C1IC g θ w e i j := by
  -- utilities: `x i = w i - g (e i) (θ i)`
  have step : ∀ k, (w (k + 1) - g (e (k + 1)) (θ (k + 1))) = (w k - g (e k) (θ k)) +
      c1D g θ k (e k) := fun k => by rw [hbind]; unfold c1D; ring
  -- downward: for `j ≤ i`, by induction on `i - j`
  have down : ∀ j d, C1IC g θ w e (j + d) j := by
    intro j d
    induction d with
    | zero => unfold C1IC; simp
    | succ d ih =>
      unfold C1IC at ih ⊢
      have hs := step (j + d)
      have hDm : c1D g θ (j + d) (e j) ≤ c1D g θ (j + d) (e (j + d)) :=
        hsc (j + d) (he j) (he _) (hmono (by omega))
      unfold c1D at hDm hs
      rw [show j + (d + 1) = j + d + 1 by omega]
      linarith
  -- upward: for `i ≤ j`
  have up : ∀ i d, C1IC g θ w e i (i + d) := by
    intro i d
    induction d with
    | zero => unfold C1IC; simp
    | succ d ih =>
      unfold C1IC at ih ⊢
      have hs := step (i + d)
      have hDm : c1D g θ (i + d) (e (i + d)) ≤ c1D g θ (i + d) (e (i + d + 1)) :=
        hsc (i + d) (he _) (he _) (hmono (by omega))
      -- single crossing between `i` and `i + d`: `g(·, θ_i) - g(·, θ_{i+d})` is nondecreasing
      have hcross : ∀ m, ∀ x y, 0 ≤ x → x ≤ y →
          g x (θ i) - g x (θ (i + m)) ≤ g y (θ i) - g y (θ (i + m)) := by
        intro m
        induction m with
        | zero => intro x y _ _; simp
        | succ m ihm =>
          intro x y hx hxy
          have h1 := ihm x y hx hxy
          have h2 : c1D g θ (i + m) x ≤ c1D g θ (i + m) y := hsc (i + m) hx (hx.trans hxy) hxy
          unfold c1D at h2
          rw [show i + (m + 1) = i + m + 1 by omega]
          linarith
      have hc := hcross d (e (i + d)) (e (i + d + 1)) (he _) (hmono (by omega))
      unfold c1D at hDm hs
      rw [show i + (d + 1) = i + d + 1 by omega]
      linarith
  intro i j
  rcases le_total j i with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact down j d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact up i d

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.1: the optimal contract with `N` states

MWG, Exercise 14.C.1, p. 508, with the model of `ExerciseC1` (an infinitely risk-averse manager,
reservation level `c`, states `θ₀, …, θ_{N-1}` with probabilities `p_i > 0`).

* `C1Feas`, `c1Prof`: feasible contracts (nonnegative efforts, all reservation and all incentive
  constraints among the `N` states) and the owner's expected profit.
* `c1Rent`, `c1Wage`, `c1VS`: the minimal rents `Σ_{k<i} D_k(e_k)`, the wages that pay exactly
  these rents, and the virtual surplus `Σ_i p_i [π(e_i) - g(e_i, θ_i) - c - Σ_{k<i} D_k(e_k)]`.
* `c1_prof_le_VS`: every feasible contract earns at most the virtual surplus of its efforts;
  `c1_wage_feasible`, `c1_prof_wage`: for nondecreasing efforts the minimal-rent wages are feasible
  and earn exactly the virtual surplus.
* `exercise_14_C_1_opt`: **the characterization**. In every optimal contract efforts are
  nondecreasing, the reservation constraint of the lowest state binds, every local downward
  incentive constraint binds, and the efforts maximize the virtual surplus among nondecreasing
  effort profiles; `exercise_14_C_1_suff` is the converse.
* `exercise_14_C_1_distortion`: if `e*_i` uniquely maximizes `π(e) - g(e, θ_i)` and the `e*_i` are
  nondecreasing, then every optimal contract has `e_i ≤ e*_i` (downward distortion) and
  `e_{N-1} = e*_{N-1}` (no distortion at the top).
* `exercise_14_C_1_instance`: two states, `π(e) = e`, `g(e, θ) = e²/(2θ)`, `θ_i = i + 1`,
  `p = (1/2, 1/2)`, `c = 0`: efforts `(2/3, 2)` against first-best efforts `(1, 2)`.
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- Feasible contracts with `N` states: nonnegative efforts and all reservation and incentive
constraints among states `0, …, N-1`. -/
def C1Feas (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (c : ℝ) (N : ℕ) (w e : ℕ → ℝ) : Prop :=
  (∀ i < N, 0 ≤ e i) ∧ (∀ i < N, c ≤ w i - g (e i) (θ i)) ∧
    ∀ i < N, ∀ j < N, C1IC g θ w e i j

/-- The owner's expected profit `Σ_i p_i (π(e_i) - w_i)`. -/
def c1Prof (p : ℕ → ℝ) (prof : ℝ → ℝ) (N : ℕ) (w e : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, p i * (prof (e i) - w i)

/-- The minimal rent of state `i`: `Σ_{k<i} D_k(e_k)`. -/
def c1Rent (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ range i, c1D g θ k (e k)

/-- The wages paying exactly the minimal rents: `w_i = g(e_i, θ_i) + c + Σ_{k<i} D_k(e_k)`. -/
def c1Wage (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (c : ℝ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  g (e i) (θ i) + c + c1Rent g θ e i

/-- The virtual surplus `Σ_i p_i [π(e_i) - g(e_i, θ_i) - c - Σ_{k<i} D_k(e_k)]`. -/
def c1VS (g : ℝ → ℝ → ℝ) (θ p : ℕ → ℝ) (prof : ℝ → ℝ) (c : ℝ) (N : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, p i * (prof (e i) - g (e i) (θ i) - c - c1Rent g θ e i)

/-- Single crossing gives `D_k(e) ≥ D_k(0) = 0` for `e ≥ 0`, and `D_k` nondecreasing. -/
theorem c1_D_mono {g : ℝ → ℝ → ℝ} {θ : ℕ → ℝ}
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (k : ℕ) :
    MonotoneOn (c1D g θ k) (Ici 0) :=
  (hsc k (k + 1) (Nat.lt_succ_self k)).monotoneOn

/-- `D_k(e) ≥ 0` for `e ≥ 0`. -/
theorem c1_D_nonneg {g : ℝ → ℝ → ℝ} {θ : ℕ → ℝ} (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ c1D g θ k x := by
  have := c1_D_mono hsc k (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simpa [c1D, hg0] using this

/-- The rents of a feasible contract: `x_i ≥ c + Σ_{k<i} D_k(e_k)` for `i < N`. -/
theorem c1_rent_le {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hf : C1Feas g θ c N w e) : ∀ i < N, c + c1Rent g θ e i ≤ w i - g (e i) (θ i) := by
  intro i
  induction i with
  | zero => intro h; simpa [c1Rent] using hf.2.1 0 h
  | succ n ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hf.2.2 (n + 1) h n (by omega)
    unfold C1IC at h2
    unfold c1Rent at h1 ⊢
    rw [sum_range_succ]
    simp only [c1D] at h1 ⊢
    linarith

/-- Every feasible contract earns at most the virtual surplus of its efforts. -/
theorem c1_prof_le_VS {g : ℝ → ℝ → ℝ} {θ p w e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hp : ∀ i < N, 0 < p i) (hf : C1Feas g θ c N w e) :
    c1Prof p prof N w e ≤ c1VS g θ p prof c N e := by
  unfold c1Prof c1VS
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  have := mul_le_mul_of_nonneg_left (c1_rent_le hf i hi') (hp i hi').le
  nlinarith

/-- The extension `e (min i (N - 1))` of an effort profile on `0, …, N-1`. -/
def c1Ext (N : ℕ) (e : ℕ → ℝ) (i : ℕ) : ℝ := e (min i (N - 1))

/-- **Exercise 14.C.1**: for nonnegative nondecreasing efforts on `0, …, N-1`, the minimal-rent
wages (for the extended profile) form a feasible contract. -/
theorem c1_wage_feasible {g : ℝ → ℝ → ℝ} {θ e : ℕ → ℝ} {c : ℝ} {N : ℕ} (hN : 0 < N)
    (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (he : ∀ i < N, 0 ≤ e i) (hmono : ∀ i j, i ≤ j → j < N → e i ≤ e j) :
    C1Feas g θ c N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) := by
  have hE : ∀ k, 0 ≤ c1Ext N e k := fun k => he _ (by omega)
  have hM : Monotone (c1Ext N e) := fun i j hij => hmono _ _ (by omega) (by omega)
  have hIC := exercise_14_C_1_local (w := c1Wage g θ c (c1Ext N e)) (c1_D_mono hsc) hE hM
    (fun k => by
      unfold c1Wage c1Rent
      rw [sum_range_succ]
      unfold c1D
      ring)
  refine ⟨fun i _ => hE i, fun i _ => ?_, fun i _ j _ => hIC i j⟩
  unfold c1Wage c1Rent
  have : 0 ≤ ∑ k ∈ range i, c1D g θ k (c1Ext N e k) :=
    sum_nonneg fun k _ => c1_D_nonneg hg0 hsc k (hE k)
  linarith

/-- The minimal-rent contract earns exactly the virtual surplus. -/
theorem c1_prof_wage {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ} :
    c1Prof p prof N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) =
      c1VS g θ p prof c N (c1Ext N e) := by
  unfold c1Prof c1VS c1Wage
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The virtual surplus depends only on the efforts in states `0, …, N-1`. -/
theorem c1_VS_ext {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ} :
    c1VS g θ p prof c N (c1Ext N e) = c1VS g θ p prof c N e := by
  unfold c1VS c1Rent
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have h1 : c1Ext N e i = e i := by unfold c1Ext; congr 1; omega
  have h2 : ∑ k ∈ range i, c1D g θ k (c1Ext N e k) = ∑ k ∈ range i, c1D g θ k (e k) :=
    sum_congr rfl fun k hk => by
      have := mem_range.1 hk
      unfold c1Ext; congr 2; omega
  rw [h1, h2]

/-- **Exercise 14.C.1** (MWG, p. 508), the optimal contract with `N` states. With single crossing,
`g(0, θ) = 0` and positive probabilities, every optimal contract `(w, e)` has: (i) nondecreasing
efforts; (ii) a binding reservation constraint in the lowest state; (iii) binding local downward
incentive constraints `w_{k+1} - g(e_{k+1}, θ_{k+1}) = w_k - g(e_k, θ_{k+1})`; (iv) efforts that
maximize the virtual surplus among nonnegative nondecreasing effort profiles. -/
theorem exercise_14_C_1_opt {g : ℝ → ℝ → ℝ} {θ p w e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e) :
    (∀ i j, i ≤ j → j < N → e i ≤ e j) ∧ w 0 - g (e 0) (θ 0) = c ∧
      (∀ k, k + 1 < N → w (k + 1) - g (e (k + 1)) (θ (k + 1)) = w k - g (e k) (θ (k + 1))) ∧
      ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
        c1VS g θ p prof c N e' ≤ c1VS g θ p prof c N e := by
  have hmono : ∀ i j, i ≤ j → j < N → e i ≤ e j := by
    intro i j hij hj
    rcases hij.lt_or_eq with h | rfl
    · exact exercise_14_C_1_mono (hsc i j h) (hf.1 i (by omega)) (hf.1 j hj)
        (hf.2.2 i (by omega) j hj) (hf.2.2 j hj i (by omega))
    · exact le_rfl
  have hVSle : ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
      c1VS g θ p prof c N e' ≤ c1Prof p prof N w e := by
    intro e' he' hm'
    have := hopt _ _ (c1_wage_feasible (c := c) hN hg0 hsc he' hm')
    rwa [c1_prof_wage, c1_VS_ext] at this
  have heq : c1Prof p prof N w e = c1VS g θ p prof c N e :=
    le_antisymm (c1_prof_le_VS hp hf) (hVSle e hf.1 hmono)
  -- every rent is minimal
  have hrent : ∀ i < N, w i - g (e i) (θ i) = c + c1Rent g θ e i := by
    have hterm : ∀ i ∈ range N, 0 ≤ p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) :=
      fun i hi => mul_nonneg (hp i (mem_range.1 hi)).le
        (by linarith [c1_rent_le hf i (mem_range.1 hi)])
    have hsum : ∑ i ∈ range N, p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) = 0 := by
      have : ∑ i ∈ range N, p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) =
          c1VS g θ p prof c N e - c1Prof p prof N w e := by
        unfold c1VS c1Prof
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      rw [this, heq, sub_self]
    intro i hi
    have := (sum_eq_zero_iff_of_nonneg hterm).1 hsum i (mem_range.2 hi)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hp i hi).ne'
    · linarith
  refine ⟨hmono, by simpa [c1Rent] using hrent 0 hN, fun k hk => ?_, fun e' he' hm' => ?_⟩
  · have h1 := hrent (k + 1) hk
    have h2 := hrent k (by omega)
    unfold c1Rent at h1 h2
    rw [sum_range_succ] at h1
    simp only [c1D] at h1 h2
    linarith
  · rw [← heq]; exact hVSle e' he' hm'

/-- **Exercise 14.C.1**, the converse: if `e` is nonnegative, nondecreasing and maximizes the
virtual surplus among such profiles, then the minimal-rent contract is optimal. -/
theorem exercise_14_C_1_suff {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (he : ∀ i < N, 0 ≤ e i) (hm : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hmax : ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
        c1VS g θ p prof c N e' ≤ c1VS g θ p prof c N e) :
    C1Feas g θ c N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) ∧
      ∀ w' e', C1Feas g θ c N w' e' →
        c1Prof p prof N w' e' ≤ c1Prof p prof N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) := by
  refine ⟨c1_wage_feasible hN hg0 hsc he hm, fun w' e' hf' => ?_⟩
  rw [c1_prof_wage, c1_VS_ext]
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    rcases hij.lt_or_eq with h | rfl
    · exact exercise_14_C_1_mono (hsc i j h) (hf'.1 i (by omega)) (hf'.1 j hj)
        (hf'.2.2 i (by omega) j hj) (hf'.2.2 j hj i (by omega))
    · exact le_rfl
  exact (c1_prof_le_VS hp hf').trans (hmax e' hf'.1 hm')

/-- **Exercise 14.C.1**, distortions. Suppose each `e*_i ≥ 0` is the unique maximizer of
`π(e) - g(e, θ_i)` on `[0, ∞)` and `e*` is nondecreasing. In every optimal contract
`e_i ≤ e*_i` for every state (downward distortion) and `e_{N-1} = e*_{N-1}` (no distortion at the
top). -/
theorem exercise_14_C_1_distortion {g : ℝ → ℝ → ℝ} {θ p w e estar : ℕ → ℝ} {prof : ℝ → ℝ}
    {c : ℝ} {N : ℕ} (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hs0 : ∀ i < N, 0 ≤ estar i)
    (hsmax : ∀ i < N, ∀ x, 0 ≤ x → x ≠ estar i →
      prof x - g x (θ i) < prof (estar i) - g (estar i) (θ i))
    (hsm : ∀ i j, i ≤ j → j < N → estar i ≤ estar j)
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e) :
    (∀ i < N, e i ≤ estar i) ∧ e (N - 1) = estar (N - 1) := by
  obtain ⟨hmono, -, -, hmax⟩ := exercise_14_C_1_opt hN hp hg0 hsc hf hopt
  have hD := c1_D_mono hsc
  -- downward distortion: compare with `min e e*`
  have hdown : ∀ i < N, e i ≤ estar i := by
    by_contra hc
    push Not at hc
    obtain ⟨i0, hi0, hlt⟩ := hc
    set e' : ℕ → ℝ := fun i => min (e i) (estar i)
    have he' : ∀ i < N, 0 ≤ e' i := fun i hi => le_min (hf.1 i hi) (hs0 i hi)
    have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := fun i j hij hj =>
      min_le_min (hmono i j hij hj) (hsm i j hij hj)
    have hgt : c1VS g θ p prof c N e < c1VS g θ p prof c N e' := by
      unfold c1VS
      have hS : ∀ i ∈ range N, prof (e i) - g (e i) (θ i) ≤ prof (e' i) - g (e' i) (θ i) := by
        intro i hi
        have hi' := mem_range.1 hi
        by_cases h : e i ≤ estar i
        · simp only [e', min_eq_left h]; exact le_rfl
        · push Not at h
          simp only [e', min_eq_right h.le]
          exact (hsmax i hi' (e i) (hf.1 i hi') h.ne').le
      have hR : ∀ i ∈ range N, c1Rent g θ e' i ≤ c1Rent g θ e i := by
        intro i hi
        unfold c1Rent
        refine sum_le_sum fun k hk => ?_
        have hk' : k < N := by have := mem_range.1 hk; have := mem_range.1 hi; omega
        exact hD k (mem_Ici.2 (he' k hk')) (mem_Ici.2 (hf.1 k hk')) (min_le_left _ _)
      refine sum_lt_sum (fun i hi => ?_) ⟨i0, mem_range.2 hi0, ?_⟩
      · have := hp i (mem_range.1 hi)
        nlinarith [hS i hi, hR i hi]
      · have h1 := hp i0 hi0
        have hS0 : prof (e i0) - g (e i0) (θ i0) < prof (e' i0) - g (e' i0) (θ i0) := by
          simp only [e', min_eq_right hlt.le]
          exact hsmax i0 hi0 (e i0) (hf.1 i0 hi0) hlt.ne'
        nlinarith [hR i0 (mem_range.2 hi0)]
    linarith [hmax e' he' hm']
  refine ⟨hdown, ?_⟩
  -- no distortion at the top
  by_contra hne
  have htop : N - 1 < N := by omega
  have hlt : e (N - 1) < estar (N - 1) := lt_of_le_of_ne (hdown _ htop) hne
  set e' : ℕ → ℝ := Function.update e (N - 1) (estar (N - 1))
  have he'N : ∀ i < N - 1, e' i = e i := fun i hi => Function.update_of_ne (by omega) _ _
  have he' : ∀ i < N, 0 ≤ e' i := by
    intro i hi
    by_cases h : i = N - 1
    · subst h; simp only [e', Function.update_self]; exact hs0 _ htop
    · rw [he'N i (by omega)]; exact hf.1 i hi
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    by_cases hjN : j = N - 1
    · subst hjN
      by_cases hiN : i = N - 1
      · subst hiN; exact le_rfl
      · rw [he'N i (by omega)]
        simp only [e', Function.update_self]
        exact (hmono i (N - 1) hij htop).trans hlt.le
    · rw [he'N i (by omega), he'N j (by omega)]
      exact hmono i j hij hj
  have hgt : c1VS g θ p prof c N e < c1VS g θ p prof c N e' := by
    unfold c1VS
    have hR : ∀ i ∈ range N, c1Rent g θ e' i = c1Rent g θ e i := by
      intro i hi
      unfold c1Rent
      refine sum_congr rfl fun k hk => ?_
      have : k < N - 1 := by have := mem_range.1 hk; have := mem_range.1 hi; omega
      rw [he'N k this]
    refine sum_lt_sum (fun i hi => ?_) ⟨N - 1, mem_range.2 htop, ?_⟩
    · rw [hR i hi]
      by_cases h : i = N - 1
      · subst h
        have := hp _ htop
        have h2 := hsmax _ htop (e (N - 1)) (hf.1 _ htop) hlt.ne
        simp only [e', Function.update_self]
        nlinarith
      · rw [he'N i (by have := mem_range.1 hi; omega)]
    · rw [hR _ (mem_range.2 htop)]
      have := hp _ htop
      have h2 := hsmax _ htop (e (N - 1)) (hf.1 _ htop) hlt.ne
      simp only [e', Function.update_self]
      nlinarith
  linarith [hmax e' he' hm']

/-- **Exercise 14.C.1, an instance** (MWG, p. 508). Two states, `π(e) = e`, `g(e, θ) = e²/(2θ)`
with `θ_i = i + 1`, `p = (1/2, 1/2)`, `c = 0`. The efforts `(2/3, 2)` maximize the virtual
surplus, so the minimal-rent contract is optimal; its efforts are `e_0 = 2/3 < e*_0 = 1` and
`e_1 = e*_1 = 2`, as `exercise_14_C_1_opt` and `exercise_14_C_1_distortion` require. -/
theorem exercise_14_C_1_instance :
    let g : ℝ → ℝ → ℝ := fun x t => x ^ 2 / (2 * t)
    let θ : ℕ → ℝ := fun i => (i : ℝ) + 1
    let e : ℕ → ℝ := fun i => if i = 0 then 2 / 3 else 2
    C1Feas g θ 0 2 (c1Wage g θ 0 (c1Ext 2 e)) (c1Ext 2 e) ∧
      (∀ w' e', C1Feas g θ 0 2 w' e' →
        c1Prof (fun _ => 1 / 2) id 2 w' e' ≤
          c1Prof (fun _ => 1 / 2) id 2 (c1Wage g θ 0 (c1Ext 2 e)) (c1Ext 2 e)) ∧
      c1Ext 2 e 0 = 2 / 3 ∧ c1Ext 2 e 1 = 2 := by
  intro g θ e
  have hg0 : ∀ t, g 0 t = 0 := fun t => by simp [g]
  have hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0) := by
    intro i j hij x hx y hy hxy
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [g, θ, Set.mem_Ici] at hx hy ⊢
    have hk : 1 / (2 * ((j : ℝ) + 1)) < 1 / (2 * ((i : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
    rw [div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (y ^ 2),
      div_eq_mul_one_div (y ^ 2)]
    nlinarith
  have hsuff := exercise_14_C_1_suff (prof := id) (p := fun _ => 1 / 2) (c := 0) (N := 2)
    (e := e) (by norm_num) (fun _ _ => by norm_num) hg0 hsc
    (fun i _ => by simp only [e]; split_ifs <;> norm_num)
    (fun i j hij hj => by
      simp only [e]
      split_ifs <;> try norm_num
      omega)
    (fun e' _ _ => by
      simp only [c1VS, c1Rent, c1D, sum_range_succ, sum_range_zero, g, θ, e, id]
      norm_num
      nlinarith [sq_nonneg (e' 0 - 2 / 3), sq_nonneg (e' 1 - 2)])
  exact ⟨hsuff.1, hsuff.2, by simp [c1Ext, e], by simp [c1Ext, e]⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.4: a risk-averse but not infinitely risk-averse manager

MWG, Exercise 14.C.4, p. 509, in the two-state hidden-information model of Section 14.C
(pp. 489-490): the manager's utility is `v(w - g(e, θ))` with `v` strictly concave, strictly
increasing and differentiable; he accepts the contract before learning `θ`, so the participation
constraint is in expected utility, `λ v(w_H - g(e_H, θ_H)) + (1 - λ) v(w_L - g(e_L, θ_L)) ≥ ū`
(instead of (i)-(ii) of (14.C.8)), and the self-selection constraints (iii)-(iv) are as in
(14.C.8). Write `c_i = w_i - g(e_i, θ_i)` and `D(e) = g(e, θ_L) - g(e, θ_H)` (strictly increasing
on `[0, ∞)`: single crossing, `g_eθ < 0`).

* `exercise_14_C_4`: **the characterization**. In every optimal contract the participation
  constraint and the high state's self-selection constraint (iii) bind; `e_L ≤ e_H`; there is no
  distortion at the top (`e_H = e*_H`) and a downward distortion `e_L ≤ e*_L`; and the manager
  bears risk: `c_H - c_L = D(e_L)`, which is positive when `e_L > 0` (unlike the infinitely
  risk-averse case, where `c_H = c_L` is not required but `c_L = v⁻¹(ū)`).
* `exercise_14_C_4_strict`: with differentiability (`D' > 0`), the distortion is strict:
  `e_L < e*_L` whenever `e*_L > 0`.
* `exercise_14_C_4_instance`: `λ = 1/2`, `v(c) = -exp(-c)`, `ū = -1`, `π(e) = e`,
  `D(e) = κ e²` with `κ = log(11/9)`: the optimal contract has `e_L = 1 < e*_L`, `e_H = e*_H`,
  `c_H = log(10/9) > c_L = log(10/11)`; its optimality is proved with a Lagrangian certificate
  and the two theorems apply to it.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- The constraints of Exercise 14.C.4: nonnegative efforts, expected-utility participation and
the self-selection constraints (iii)-(iv) of (14.C.8). -/
def C4Feas (v : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (θH θL lam ubar wH eH wL eL : ℝ) : Prop :=
  0 ≤ eH ∧ 0 ≤ eL ∧ ubar ≤ lam * v (wH - g eH θH) + (1 - lam) * v (wL - g eL θL) ∧
    wL - g eL θH ≤ wH - g eH θH ∧ wH - g eH θL ≤ wL - g eL θL

/-- The owner's expected profit `λ [π(e_H) - w_H] + (1 - λ) [π(e_L) - w_L]`. -/
def c4Prof (prof : ℝ → ℝ) (lam wH eH wL eL : ℝ) : ℝ :=
  lam * (prof eH - wH) + (1 - lam) * (prof eL - wL)

/-- A contract described by the certainty incomes `c_i` and efforts: feasibility. -/
theorem c4_mk {v : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam ubar cH eH cL eL : ℝ} (hH : 0 ≤ eH)
    (hL : 0 ≤ eL) (hIR : ubar ≤ lam * v cH + (1 - lam) * v cL)
    (hiii : cL + (g eL θL - g eL θH) ≤ cH) (hiv : cH - (g eH θL - g eH θH) ≤ cL) :
    C4Feas v g θH θL lam ubar (cH + g eH θH) eH (cL + g eL θL) eL := by
  refine ⟨hH, hL, by simpa using hIR, by linarith, by linarith⟩

/-- The profit of a contract described by certainty incomes. -/
theorem c4_prof_mk {prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam cH eH cL eL : ℝ} :
    c4Prof prof lam (cH + g eH θH) eH (cL + g eL θL) eL =
      lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) := by
  unfold c4Prof; ring

/-- Concavity makes the derivative antitone (strictly, under strict concavity). -/
theorem c4_dv_lt {v dv : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) {x y : ℝ} (hxy : x < y) : dv y < dv x := by
  have h1 := tpa_tangent_lt hv (mem_univ x) (mem_univ y) hxy.ne' (hdv x).hasDerivWithinAt
  have h2 := tpa_tangent_lt hv (mem_univ y) (mem_univ x) hxy.ne (hdv y).hasDerivWithinAt
  nlinarith

/-- Spreading utilities more than needed is costly: if `a < a' ≤ b' < b` and moving from
`(a, b)` to `(a', b')` keeps `λ v(b) + (1 - λ) v(a)`, then the expected income falls:
`(1 - λ)(a' - a) < λ (b - b')` (strict concavity). -/
theorem c4_spread {v dv : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x) {lam a b a' b' : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (ha : a < a') (hab : a' ≤ b') (hb : b' < b)
    (heq : (1 - lam) * (v a' - v a) = lam * (v b - v b')) :
    (1 - lam) * (a' - a) < lam * (b - b') := by
  have t1 := tpa_tangent_le hv.concaveOn (mem_univ a') (mem_univ a) (hdv a').hasDerivWithinAt
  have t2 := tpa_tangent_lt hv (mem_univ b') (mem_univ b) hb.ne' (hdv b').hasDerivWithinAt
  have hdd : dv b' ≤ dv a' := by
    rcases hab.lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hp := hdvpos b'
  have k1 : 0 ≤ (1 - lam) * (a' - a) := mul_nonneg (by linarith) (by linarith)
  have e1 : (1 - lam) * (a' - a) * dv b' ≤ (1 - lam) * (a' - a) * dv a' :=
    mul_le_mul_of_nonneg_left hdd k1
  have e2 : (1 - lam) * ((a' - a) * dv a') ≤ (1 - lam) * (v a' - v a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e3 : lam * (v b - v b') < lam * (dv b' * (b - b')) :=
    mul_lt_mul_of_pos_left (by linarith) hl0
  have : (1 - lam) * (a' - a) * dv b' < lam * (b - b') * dv b' := by
    have r1 : (1 - lam) * (a' - a) * dv a' = (1 - lam) * ((a' - a) * dv a') := by ring
    have r2 : lam * (dv b' * (b - b')) = lam * (b - b') * dv b' := by ring
    linarith
  exact lt_of_mul_lt_mul_right this hp.le

/-- The participation bound used for the strict distortion: moving from `(a, b)` to
`(x, y) = (a + κΔ, b - (1 - κ)Δ)` with `A ≤ v'(x)`, `v'(y) ≤ B` and
`κ ((1 - λ) A + λ B) = λ B` does not lower `λ v(b) + (1 - λ) v(a)`. -/
theorem c4_part {v dv : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) (hdv : ∀ x, HasDerivAt v (dv x) x)
    {lam a b x y A B κ Δ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hx : x = a + κ * Δ)
    (hy : b = y + (1 - κ) * Δ) (hΔ : 0 ≤ Δ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hA : A ≤ dv x)
    (hB : dv y ≤ B) (hκeq : κ * ((1 - lam) * A + lam * B) = lam * B) :
    lam * v b + (1 - lam) * v a ≤ lam * v y + (1 - lam) * v x := by
  subst hx hy
  have t1 := tpa_tangent_le hv (mem_univ (a + κ * Δ)) (mem_univ a)
    (hdv (a + κ * Δ)).hasDerivWithinAt
  have t2 := tpa_tangent_le hv (mem_univ y) (mem_univ (y + (1 - κ) * Δ))
    (hdv y).hasDerivWithinAt
  have k1 : A * (κ * Δ) ≤ dv (a + κ * Δ) * (κ * Δ) :=
    mul_le_mul_of_nonneg_right hA (mul_nonneg hκ0 hΔ)
  have k2 : dv y * ((1 - κ) * Δ) ≤ B * ((1 - κ) * Δ) :=
    mul_le_mul_of_nonneg_right hB (mul_nonneg (by linarith) hΔ)
  have h1 : v (a + κ * Δ) - v a ≥ A * (κ * Δ) := by nlinarith
  have h2 : v (y + (1 - κ) * Δ) - v y ≤ B * ((1 - κ) * Δ) := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - lam)
  have h4 := mul_le_mul_of_nonneg_left h2 hl0
  have h5 : lam * (B * ((1 - κ) * Δ)) - (1 - lam) * (A * (κ * Δ)) = 0 := by
    linear_combination (-Δ) * hκeq
  nlinarith

/-- **Exercise 14.C.4** (MWG, p. 509), the characterization. Assumptions: `0 < λ < 1`; `v` strictly
concave and differentiable with `v' > 0`; `D(e) = g(e, θ_L) - g(e, θ_H)` strictly increasing on
`[0, ∞)` with `g(0, θ) = 0`; `e*_i ≥ 0` the unique maximizer of `π(e) - g(e, θ_i)` on `[0, ∞)`,
with `e*_L ≤ e*_H`. Every optimal contract has (a) binding participation; (b) binding (iii):
`c_H = c_L + D(e_L)`; (c) `e_L ≤ e_H`; (d) `e_L ≤ e*_L`; (e) `e_H = e*_H`; (f) `c_L < c_H` when
`e_L > 0` (the manager bears risk). -/
theorem exercise_14_C_4 {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam ubar esH esL : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    (hD : StrictMonoOn (fun e => g e θL - g e θH) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (hsH0 : 0 ≤ esH) (hsL0 : 0 ≤ esL)
    (hsH : ∀ x, 0 ≤ x → x ≠ esH → prof x - g x θH < prof esH - g esH θH)
    (hsL : ∀ x, 0 ≤ x → x ≠ esL → prof x - g x θL < prof esL - g esL θL) (hord : esL ≤ esH)
    {wH eH wL eL : ℝ} (hf : C4Feas v g θH θL lam ubar wH eH wL eL)
    (hopt : ∀ wH' eH' wL' eL', C4Feas v g θH θL lam ubar wH' eH' wL' eL' →
      c4Prof prof lam wH' eH' wL' eL' ≤ c4Prof prof lam wH eH wL eL) :
    lam * v (wH - g eH θH) + (1 - lam) * v (wL - g eL θL) = ubar ∧
      wH - g eH θH = wL - g eL θL + (g eL θL - g eL θH) ∧ eL ≤ eH ∧ eL ≤ esL ∧ eH = esH ∧
      (0 < eL → wL - g eL θL < wH - g eH θH) := by
  obtain ⟨hH0, hL0, hIR, hiii, hiv⟩ := hf
  set cH := wH - g eH θH with hcH
  set cL := wL - g eL θL with hcL
  set D : ℝ → ℝ := fun e => g e θL - g e θH with hDdef
  have hvm : StrictMono v := by
    intro x y hxy
    have := tpa_tangent_lt hv (mem_univ y) (mem_univ x) hxy.ne (hdv y).hasDerivWithinAt
    nlinarith [hdvpos y]
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hdv x).continuousAt
  have hwH : wH = cH + g eH θH := by rw [hcH]; ring
  have hwL : wL = cL + g eL θL := by rw [hcL]; ring
  have hprof : c4Prof prof lam wH eH wL eL =
      lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) := by
    rw [hwH, hwL, c4_prof_mk]
  have hiii' : cL + D eL ≤ cH := by simp only [D, hcH, hcL]; linarith
  have hiv' : cH - D eH ≤ cL := by simp only [D, hcH, hcL]; linarith
  -- (c) `e_L ≤ e_H`
  have hLH : eL ≤ eH := (hD.le_iff_le (mem_Ici.2 hL0) (mem_Ici.2 hH0)).1 (by linarith)
  -- (a) participation binds
  have hbindIR : lam * v cH + (1 - lam) * v cL = ubar := by
    by_contra hne
    have hlt : ubar < lam * v cH + (1 - lam) * v cL := lt_of_le_of_ne hIR (Ne.symm hne)
    have hcont : Continuous fun ε : ℝ => lam * v (cH - ε) + (1 - lam) * v (cL - ε) := by
      fun_prop
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ubar < lam * v (cH - ε) + (1 - lam) * v (cL - ε) :=
      hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH - ε) (cL := cL - ε) hH0 hL0 hε.le (by simp only [D] at hiii'; linarith)
      (by simp only [D] at hiv'; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have hεpos' : (0 : ℝ) < ε := hεpos
    have e : lam * (prof eH - g eH θH - (cH - ε)) + (1 - lam) * (prof eL - g eL θL - (cL - ε)) =
        lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) + ε := by ring
    linarith
  -- (b) (iii) binds
  have hbind : cH = cL + D eL := by
    by_contra hne
    have hslack : cL + D eL < cH := lt_of_le_of_ne hiii' (Ne.symm hne)
    set U := lam * v cH + (1 - lam) * v cL
    have hc : Continuous fun s : ℝ => lam * v (s + D eL) + (1 - lam) * v s := by fun_prop
    have hlo : lam * v (cL + D eL) + (1 - lam) * v cL ≤ U := by
      have := hvm.monotone hslack.le
      nlinarith
    have hhi : U ≤ lam * v (cH - D eL + D eL) + (1 - lam) * v (cH - D eL) := by
      have := hvm.monotone (show cL ≤ cH - D eL by linarith)
      simp only [sub_add_cancel]
      nlinarith
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := intermediate_value_Icc (show cL ≤ cH - D eL by linarith)
      hc.continuousOn ⟨hlo, hhi⟩
    simp only at hs
    -- the new contract `(s + D(e_L), s)` is cheaper
    have ha : cL < s := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · subst h
        have := mul_lt_mul_of_pos_left (hvm (show cL + D eL < cH from hslack)) hl0
        simp only [U] at hs
        linarith
    have hb : s + D eL < cH := by
      rcases hs2.lt_or_eq with h | h
      · linarith
      · have := mul_lt_mul_of_pos_left (hvm (show cL < s from ha)) (by linarith : 0 < 1 - lam)
        rw [h] at hs this
        simp only [sub_add_cancel, U] at hs
        linarith
    have hDnn : 0 ≤ D eL := by
      have := hD.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hL0) hL0
      simpa [D, hg0] using this
    have key : (1 - lam) * (s - cL) < lam * (cH - (s + D eL)) :=
      c4_spread hv hdv hdvpos hl0 hl1 ha (by linarith) hb (by simp only [U] at hs; linarith)
    have hDLH := hD.monotoneOn (mem_Ici.2 hL0) (mem_Ici.2 hH0) hLH
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := s + D eL) (cL := s) hH0 hL0 (by simp only [U] at hs; linarith)
      (by simp only [D]; linarith) (by simp only [D] at hiv' hDLH ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    linarith
  -- (d) `e_L ≤ e*_L`
  have hLs : eL ≤ esL := by
    by_contra hlt
    push Not at hlt
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH) (cL := cL) (eL := esL) hH0 hsL0 hIR
      (by have := hD.monotoneOn (mem_Ici.2 hsL0) (mem_Ici.2 hL0) hlt.le
          simp only [D] at hiii' this ⊢; linarith)
      (by simp only [D] at hiv' ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have := hsL eL hL0 hlt.ne'
    nlinarith
  -- (e) `e_H = e*_H`
  have hHs : eH = esH := by
    by_contra hne
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH) (cL := cL) (eH := esH) hsH0 hL0 hIR (by simp only [D] at hiii' ⊢; linarith)
      (by
        have := hD.monotoneOn (mem_Ici.2 hL0) (mem_Ici.2 hsH0) (hLs.trans hord)
        simp only [D] at hbind this ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have := hsH eH hH0 hne
    nlinarith
  refine ⟨hbindIR, hbind, hLH, hLs, hHs, fun hpos => ?_⟩
  have := hD (mem_Ici.2 le_rfl) (mem_Ici.2 hL0) hpos
  have hD0 : D 0 = 0 := by simp [D, hg0]
  linarith

/-- A function with negative derivative at `x` is larger than at `x` just to the left of `x`. -/
theorem c4_left_gt {ψ : ℝ → ℝ} {d x : ℝ} (hψ : HasDerivAt ψ d x) (hd : d < 0) :
    ∀ᶠ y in 𝓝[<] x, ψ x < ψ y := by
  have h := hasDerivAt_iff_tendsto_slope.1 hψ
  have h' := h.mono_left (nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy))
  filter_upwards [h'.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with y hy hyx
  rw [slope_def_field] at hy
  have hyx' : y - x < 0 := by simp only [mem_Iio] at hyx; linarith
  have := (div_neg_iff.1 hy)
  rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith
  · linarith

/-- **Exercise 14.C.4** (MWG, p. 509), strict downward distortion. In addition to the assumptions
of `exercise_14_C_4`, let `π(e) - g(e, θ_L)` be differentiable at `e*_L > 0` and `D` differentiable
at `e*_L` with `D'(e*_L) > 0` (as `g_eθ < 0`). Then every optimal contract has `e_L < e*_L`. -/
theorem exercise_14_C_4_strict {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    {θH θL lam ubar esH esL sL dD : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    (hD : StrictMonoOn (fun e => g e θL - g e θH) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (hsH0 : 0 ≤ esH) (hsLpos : 0 < esL)
    (hsH : ∀ x, 0 ≤ x → x ≠ esH → prof x - g x θH < prof esH - g esH θH)
    (hsL : ∀ x, 0 ≤ x → x ≠ esL → prof x - g x θL < prof esL - g esL θL) (hord : esL ≤ esH)
    (hSd : HasDerivAt (fun e => prof e - g e θL) sL esL)
    (hDd : HasDerivAt (fun e => g e θL - g e θH) dD esL) (hdD : 0 < dD)
    {wH eH wL eL : ℝ} (hf : C4Feas v g θH θL lam ubar wH eH wL eL)
    (hopt : ∀ wH' eH' wL' eL', C4Feas v g θH θL lam ubar wH' eH' wL' eL' →
      c4Prof prof lam wH' eH' wL' eL' ≤ c4Prof prof lam wH eH wL eL) :
    eL < esL := by
  obtain ⟨hbIR, hbind, hLH, hLs, hHs, hrisk⟩ := exercise_14_C_4 hl0 hl1 hv hdv hdvpos hD hg0
    hsH0 hsLpos.le hsH hsL hord hf hopt
  rcases hLs.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨hH0, hL0, hIR, hiii, hiv⟩ := hf
  subst h
  set D : ℝ → ℝ := fun e => g e θL - g e θH with hDdef
  set S : ℝ → ℝ := fun e => prof e - g e θL with hSdef
  set cH := wH - g eH θH with hcH
  set cL := wL - g eL θL with hcL
  have hsL0 : sL = 0 := by
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hSd
    filter_upwards [Ioi_mem_nhds hsLpos] with x hx
    rcases eq_or_ne x eL with rfl | hne
    · exact le_rfl
    · exact (hsL x (le_of_lt hx) hne).le
  have hgap : cL < cH := hrisk hsLpos
  set m1 := cL + (cH - cL) / 3
  set m2 := cL + 2 * (cH - cL) / 3
  have hA := hdvpos m1
  have hB := hdvpos m2
  have hAB : dv m2 < dv m1 := c4_dv_lt hv hdv (by simp only [m1, m2]; linarith)
  set κ := lam * dv m2 / ((1 - lam) * dv m1 + lam * dv m2)
  have hden : 0 < (1 - lam) * dv m1 + lam * dv m2 := by nlinarith
  have hκ0 : 0 ≤ κ := div_nonneg (by positivity) hden.le
  have hκl : κ < lam := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (mul_pos hl0 (by linarith : (0 : ℝ) < 1 - lam)) (sub_pos.2 hAB)]
  have hκ1 : κ ≤ 1 := hκl.le.trans hl1.le
  have hκeq : κ * ((1 - lam) * dv m1 + lam * dv m2) = lam * dv m2 := div_mul_cancel₀ _ hden.ne'
  -- choosing the new effort `y < e*_L`
  have hψ : HasDerivAt (fun e => (1 - lam) * S e - (lam - κ) * D e)
      ((1 - lam) * sL - (lam - κ) * dD) eL := (hSd.const_mul _).sub (hDd.const_mul _)
  have hneg : (1 - lam) * sL - (lam - κ) * dD < 0 := by
    rw [hsL0]; nlinarith [mul_pos (sub_pos.2 hκl) hdD]
  have hDc : Tendsto D (𝓝[<] eL) (𝓝 (D eL)) :=
    hDd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgap3 : 0 < (cH - cL) / 3 := by linarith
  obtain ⟨y, ⟨hy1, hy2⟩, hy4⟩ := (((c4_left_gt hψ hneg).and
    (hDc.eventually (Metric.ball_mem_nhds (D eL) hgap3))).and
    (Ioo_mem_nhdsLT hsLpos)).exists
  rw [Real.dist_eq] at hy2
  have hy0 : 0 < y := hy4.1
  have hyL : y < eL := hy4.2
  have hDy : D y < D eL := hD (mem_Ici.2 hy0.le) (mem_Ici.2 hL0) hyL
  set Δ := D eL - D y
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have hΔ3 : Δ < (cH - cL) / 3 := by
    rw [abs_sub_comm] at hy2
    simp only [Δ]
    linarith [le_abs_self (D eL - D y)]
  set t := κ * Δ
  have ht0 : 0 ≤ t := mul_nonneg hκ0 hΔ.le
  have htΔ : t ≤ Δ := by simp only [t]; nlinarith
  have hcHb : cH = cL + D eL := by simp only [D]; linarith [hbind]
  -- participation for the new contract `(c_L + t + D(y), c_L + t)`
  have d1 : dv m1 ≤ dv (cL + t) := by
    rcases (show cL + t ≤ m1 by simp only [m1]; linarith).lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hm2 : m2 ≤ cL + t + D y := by
    have : D y = D eL - Δ := by simp only [Δ]; ring
    rw [this]; simp only [m2]; rw [hcHb] at hΔ3 ⊢; linarith
  have d2 : dv (cL + t + D y) ≤ dv m2 := by
    rcases hm2.lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hpart : lam * v cH + (1 - lam) * v cL ≤
      lam * v (cL + t + D y) + (1 - lam) * v (cL + t) :=
    c4_part hv.concaveOn hdv hl0.le hl1.le rfl (by simp only [t, Δ]; rw [hcHb]; ring) hΔ.le
      hκ0 hκ1 d1 d2 hκeq
  have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
    (cH := cL + t + D y) (cL := cL + t) (eH := eH) (eL := y) hH0 hy0.le (hIR.trans
      (by simpa [hcH, hcL] using hpart)) (by simp only [D]; linarith)
    (by
      have := hD.monotoneOn (mem_Ici.2 hy0.le) (mem_Ici.2 hH0) (hyL.le.trans hLH)
      simp only [D] at this ⊢; linarith)
  have hp := hopt _ _ _ _ hfeas
  have hwH : wH = cH + g eH θH := by rw [hcH]; ring
  have hwL : wL = cL + g eL θL := by rw [hcL]; ring
  rw [c4_prof_mk, hwH, hwL, c4_prof_mk] at hp
  have e : lam * (prof eH - g eH θH - (cL + t + D y)) + (1 - lam) * (prof y - g y θL - (cL + t)) -
      (lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL)) =
      ((1 - lam) * S y - (lam - κ) * D y) - ((1 - lam) * S eL - (lam - κ) * D eL) := by
    simp only [t, Δ, S]; rw [hcHb]; ring
  linarith

/-- The exponential bound behind the instance: with `e^{-L} = q > 0`,
`-k c - e^{-c}/2 ≤ -k L - k` when `k = q/2`. -/
theorem c4_exp_bound {c L q : ℝ} (hL : Real.exp (-L) = q) (hq : 0 < q) :
    -(q / 2) * c - Real.exp (-c) / 2 ≤ -(q / 2) * L - q / 2 := by
  have h1 := Real.add_one_le_exp (-(c - L))
  have h2 : Real.exp (-c) = Real.exp (-L) * Real.exp (-(c - L)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, hL]
  nlinarith

/-- The instance of Exercise 14.C.4: `κ = log(10/9) - log(10/11)` (`= log(11/9)`). -/
noncomputable def c4κ : ℝ := Real.log (10 / 9) - Real.log (10 / 11)

/-- The instance: `a = 1 - 11κ/5`. -/
noncomputable def c4a : ℝ := 1 - 11 * c4κ / 5

/-- The instance: `g(e, θ) = a e²/2 + κ (1 - θ) e²` (`θ_L = 0`, `θ_H = 1`). -/
noncomputable def c4g (e θ : ℝ) : ℝ := c4a * e ^ 2 / 2 + c4κ * (1 - θ) * e ^ 2

/-- The instance: the wage in state `θ_H`, `log(10/9) + g(1/a, θ_H)`. -/
noncomputable def c4wH : ℝ := Real.log (10 / 9) + c4g (1 / c4a) 1

/-- The instance: the wage in state `θ_L`, `log(10/11) + g(1, θ_L)`. -/
noncomputable def c4wL : ℝ := Real.log (10 / 11) + c4g 1 0

/-- **Exercise 14.C.4, an instance** (MWG, p. 509). `λ = 1/2`, `v(c) = -exp(-c)`, `ū = -1`,
`π(e) = e`, `θ_L = 0`, `θ_H = 1`, `c4g(e, θ) = c4a e²/2 + c4κ (1 - θ) e²` with
`c4κ = log(10/9) - log(10/11)` (`= log(11/9)`) and `c4a = 1 - 11κ/5`, so that `D(e) = c4κ e²`,
`e*_H = 1/c4a` and `e*_L = 1/(1 - c4κ/5)`. The contract `e_H = 1/c4a`, `e_L = 1`,
`c_H = log(10/9)`, `c_L = log(10/11)` is optimal (Lagrangian certificate with multipliers `1` on
participation and `1/20` on (iii)); for it the characterization holds and `e_L = 1 < e*_L`. -/
theorem exercise_14_C_4_instance :
    C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) c4wH (1 / c4a) c4wL 1 ∧
      (∀ wH' eH' wL' eL', C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) wH' eH' wL' eL' →
        c4Prof id (1 / 2) wH' eH' wL' eL' ≤ c4Prof id (1 / 2) c4wH (1 / c4a) c4wL 1) ∧
      (1 : ℝ) < 1 / (1 - c4κ / 5) ∧ c4wL - c4g 1 0 < c4wH - c4g (1 / c4a) 1 := by
  have hL1 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have hL1' : Real.log (10 / 9) < 1 / 9 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 9) (by norm_num)
    linarith
  have hL2 : Real.log (10 / 11) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hL2' : -(1 / 10) < Real.log (10 / 11) := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10) (by norm_num)
    have e : Real.log (10 / 11) = -Real.log (11 / 10) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have hκ0 : 0 < c4κ := by simp only [c4κ]; linarith
  have hκ1 : c4κ < 1 / 4 := by simp only [c4κ]; linarith
  have ha0 : 0 < c4a := by simp only [c4a]; linarith
  have ha1 : c4a < 1 := by simp only [c4a]; linarith
  have hb0 : 0 < 1 - c4κ / 5 := by linarith
  have e9 : Real.exp (-Real.log (10 / 9)) = 9 / 10 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e11 : Real.exp (-Real.log (10 / 11)) = 11 / 10 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hgH : ∀ e, c4g e 1 = c4a * e ^ 2 / 2 := fun e => by simp only [c4g]; ring
  have hgL : ∀ e, c4g e 0 = c4a * e ^ 2 / 2 + c4κ * e ^ 2 := fun e => by simp only [c4g]; ring
  have hcH : c4wH - c4g (1 / c4a) 1 = Real.log (10 / 9) := by simp only [c4wH]; ring
  have hcL : c4wL - c4g 1 0 = Real.log (10 / 11) := by simp only [c4wL]; ring
  have hinv : c4a * (1 / c4a) = 1 := by field_simp
  have hfeas : C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) c4wH (1 / c4a) c4wL 1 := by
    refine ⟨by positivity, by norm_num, ?_, ?_, ?_⟩
    · rw [hcH, hcL]; simp only [e9, e11]; norm_num
    · have : c4wL - c4g 1 1 = Real.log (10 / 11) + c4κ := by
        simp only [c4wL, hgH, hgL]; ring
      rw [this, hcH]; simp only [c4κ]; linarith
    · have h1 : 1 ≤ 1 / c4a := by rw [le_div_iff₀ ha0]; linarith
      have h2 : 1 ≤ (1 / c4a) ^ 2 := by nlinarith
      have : c4wH - c4g (1 / c4a) 0 = Real.log (10 / 9) - c4κ * (1 / c4a) ^ 2 := by
        simp only [c4wH, hgH, hgL]; ring
      rw [this, hcL]
      simp only [c4κ] at hκ0 ⊢
      nlinarith
  refine ⟨hfeas, fun wH' eH' wL' eL' hf => ?_, ?_, ?_⟩
  · obtain ⟨hH0, hL0, hIR, hiii, _⟩ := hf
    set cH := wH' - c4g eH' 1
    set cL := wL' - c4g eL' 0
    have hiii' : cL + c4κ * eL' ^ 2 ≤ cH := by
      have : wL' - c4g eL' 1 = cL + c4κ * eL' ^ 2 := by simp only [cL, hgH, hgL]; ring
      linarith
    have hprof : c4Prof id (1 / 2) wH' eH' wL' eL' =
        1 / 2 * (eH' - c4a * eH' ^ 2 / 2 - cH) +
          1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2) - cL) := by
      simp only [c4Prof, id, cH, cL, hgH, hgL]; ring
    have hprof0 : c4Prof id (1 / 2) c4wH (1 / c4a) c4wL 1 =
        1 / 2 * (1 / c4a - c4a * (1 / c4a) ^ 2 / 2 - Real.log (10 / 9)) +
          1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2) - Real.log (10 / 11)) := by
      simp only [c4Prof, id, ← hcH, ← hcL, hgH, hgL]; ring
    rw [hprof, hprof0]
    have b1 := c4_exp_bound (c := cH) e9 (by norm_num)
    have b2 := c4_exp_bound (c := cL) e11 (by norm_num)
    have hIR' : -1 ≤ 1 / 2 * -Real.exp (-cH) + (1 - 1 / 2) * -Real.exp (-cL) := hIR
    have s1 : eH' - c4a * eH' ^ 2 / 2 ≤ 1 / c4a - c4a * (1 / c4a) ^ 2 / 2 := by
      have : 1 / c4a - c4a * (1 / c4a) ^ 2 / 2 - (eH' - c4a * eH' ^ 2 / 2) =
          c4a / 2 * (eH' - 1 / c4a) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg (eH' - 1 / c4a)]
    have s2 : 1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2)) - 1 / 20 * (c4κ * eL' ^ 2) ≤
        1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2)) - 1 / 20 * c4κ := by
      have : 1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2)) - 1 / 20 * c4κ -
          (1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2)) - 1 / 20 * (c4κ * eL' ^ 2)) =
          1 / 4 * (eL' - 1) ^ 2 := by simp only [c4a]; ring
      nlinarith [sq_nonneg (eL' - 1)]
    have hκdef : c4κ = Real.log (10 / 9) - Real.log (10 / 11) := rfl
    linarith
  · rw [lt_div_iff₀ hb0]; linarith
  · rw [hcH, hcL]; linarith

/-- **Exercise 14.C.4, the theorems applied to the instance**: in the instance the participation
constraint and (iii) bind, `e_H = e*_H`, and the distortion `e_L = 1 < e*_L` is strict. -/
theorem exercise_14_C_4_instance_applied :
    1 / 2 * -Real.exp (-(c4wH - c4g (1 / c4a) 1)) +
      (1 - 1 / 2) * -Real.exp (-(c4wL - c4g 1 0)) = -1 ∧ (1 : ℝ) < 1 / (1 - c4κ / 5) ∧
      c4wH - c4g (1 / c4a) 1 = c4wL - c4g 1 0 + (c4g 1 0 - c4g 1 1) := by
  obtain ⟨hf, hopt, -, -⟩ := exercise_14_C_4_instance
  have hκ0 : 0 < c4κ := by
    have : Real.log (10 / 11) < Real.log (10 / 9) := Real.log_lt_log (by norm_num) (by norm_num)
    simp only [c4κ]; linarith
  have hκ1 : c4κ < 1 / 4 := by
    have h1 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 9) (by norm_num)
    have h2 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10) (by norm_num)
    have e : Real.log (10 / 11) = -Real.log (11 / 10) := by rw [← Real.log_inv]; norm_num
    simp only [c4κ]; linarith
  have ha0 : 0 < c4a := by simp only [c4a]; linarith
  have hb0 : 0 < 1 - c4κ / 5 := by linarith
  have hgD : ∀ e, c4g e 0 - c4g e 1 = c4κ * e ^ 2 := fun e => by simp only [c4g]; ring
  have hD : StrictMonoOn (fun e => c4g e 0 - c4g e 1) (Ici 0) := by
    intro x hx y hy hxy
    simp only [hgD]
    simp only [mem_Ici] at hx hy
    exact mul_lt_mul_of_pos_left (by nlinarith) hκ0
  have hS : ∀ (c x : ℝ), 0 < c → 0 ≤ x → x ≠ 1 / c →
      x - c * x ^ 2 / 2 < 1 / c - c * (1 / c) ^ 2 / 2 := by
    intro c x hc _ hne
    have : 1 / c - c * (1 / c) ^ 2 / 2 - (x - c * x ^ 2 / 2) = c / 2 * (x - 1 / c) ^ 2 := by
      field_simp; ring
    have := mul_pos (half_pos hc) (pow_pos (abs_pos.2 (sub_ne_zero.2 hne)) 2)
    rw [sq_abs] at this
    linarith
  have hgL : ∀ e, c4g e 0 = (1 - c4κ / 5) * e ^ 2 / 2 := fun e => by simp only [c4g, c4a]; ring
  have hgH : ∀ e, c4g e 1 = c4a * e ^ 2 / 2 := fun e => by simp only [c4g]; ring
  have hstrict := exercise_14_C_4_strict (v := fun c => -Real.exp (-c))
    (dv := fun c => Real.exp (-c)) (prof := id)
    (g := c4g) (θH := 1) (θL := 0) (lam := 1 / 2) (ubar := -1) (esH := 1 / c4a)
    (esL := 1 / (1 - c4κ / 5)) (sL := 1 - (1 - c4κ / 5) * (1 / (1 - c4κ / 5)))
    (dD := 2 * c4κ * (1 / (1 - c4κ / 5))) (by norm_num) (by norm_num) exA_strictConcave
    exA_hasDeriv (fun _ => Real.exp_pos _) hD (fun t => by simp [c4g]) (by positivity)
    (by positivity)
    (fun x hx hne => by simp only [id, hgH]; exact hS c4a x ha0 hx hne)
    (fun x hx hne => by simp only [id, hgL]; exact hS _ x hb0 hx hne)
    (one_div_le_one_div_of_le ha0 (by simp only [c4a]; linarith))
    (by
      have := ((hasDerivAt_id' (1 / (1 - c4κ / 5))).sub
        (((hasDerivAt_pow 2 (1 / (1 - c4κ / 5))).const_mul (1 - c4κ / 5)).div_const 2))
      simp only [id, hgL]
      convert this using 1; ring)
    (by
      have := (hasDerivAt_pow 2 (1 / (1 - c4κ / 5))).const_mul c4κ
      simp only [hgD]
      convert this using 1; ring)
    (by positivity) hf hopt
  have hchar := exercise_14_C_4 (v := fun c => -Real.exp (-c))
    (dv := fun c => Real.exp (-c)) (prof := id)
    (g := c4g) (θH := 1) (θL := 0) (lam := 1 / 2) (ubar := -1) (esH := 1 / c4a)
    (esL := 1 / (1 - c4κ / 5)) (by norm_num) (by norm_num) exA_strictConcave
    exA_hasDeriv (fun _ => Real.exp_pos _) hD (fun t => by simp [c4g]) (by positivity)
    (by positivity)
    (fun x hx hne => by simp only [id, hgH]; exact hS c4a x ha0 hx hne)
    (fun x hx hne => by simp only [id, hgL]; exact hS _ x hb0 hx hne)
    (one_div_le_one_div_of_le ha0 (by simp only [c4a]; linarith)) hf hopt
  exact ⟨hchar.1, hstrict, hchar.2.1⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.1: strict downward distortion with `N` states

MWG, Exercise 14.C.1, p. 508 (model of `ExerciseC1` and `ExerciseC1Opt`).

* `c1_VS_update`: changing the effort of state `k` changes the virtual surplus by
  `p_k [S_k(y) - S_k(e_k)] - (Σ_{i>k} p_i) [D_k(y) - D_k(e_k)]`.
* `exercise_14_C_1_strict`: if the first-best efforts are strictly increasing, `e*_k > 0`,
  `π - g(·, θ_k)` and `D_k` are differentiable at `e*_k` with `D_k'(e*_k) > 0`, then every optimal
  contract has `e_k < e*_k` for every state below the top: the distortion is strict.
* `exercise_14_C_1_strict_instance`: the instance of `exercise_14_C_1_instance`.
-/

namespace MWG.PrincipalAgent

open Finset Set Filter Topology

/-- Changing the effort of one state `k < N` changes the virtual surplus by
`p_k [S_k(y) - S_k(e_k)] - (Σ_{k<i<N} p_i) [D_k(y) - D_k(e_k)]`. -/
theorem c1_VS_update {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N k : ℕ}
    (hk : k < N) (y : ℝ) :
    c1VS g θ p prof c N (Function.update e k y) - c1VS g θ p prof c N e =
      p k * ((prof y - g y (θ k)) - (prof (e k) - g (e k) (θ k))) -
        (∑ i ∈ (range N).filter (k < ·), p i) * (c1D g θ k y - c1D g θ k (e k)) := by
  unfold c1VS
  rw [← sum_sub_distrib]
  have hterm : ∀ i ∈ range N,
      p i * (prof (Function.update e k y i) - g (Function.update e k y i) (θ i) - c -
        c1Rent g θ (Function.update e k y) i) -
        p i * (prof (e i) - g (e i) (θ i) - c - c1Rent g θ e i) =
      (if i = k then p k * ((prof y - g y (θ k)) - (prof (e k) - g (e k) (θ k))) else 0) -
        (if k < i then p i * (c1D g θ k y - c1D g θ k (e k)) else 0) := by
    intro i hi
    have hR : c1Rent g θ (Function.update e k y) i - c1Rent g θ e i =
        if k < i then c1D g θ k y - c1D g θ k (e k) else 0 := by
      unfold c1Rent
      rw [← sum_sub_distrib]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte]
        rw [← sum_erase_add _ _ (mem_range.2 hki)]
        rw [sum_eq_zero fun j hj => by
          rw [Function.update_of_ne (ne_of_mem_erase hj)]; ring]
        simp
      · simp only [hki, ↓reduceIte]
        refine sum_eq_zero fun j hj => ?_
        have : j ≠ k := by have := mem_range.1 hj; omega
        rw [Function.update_of_ne this]; ring
    by_cases hik : i = k
    · subst hik
      have hR' := hR
      simp only [lt_irrefl, ↓reduceIte] at hR'
      simp only [Function.update_self, ↓reduceIte, lt_irrefl]
      linear_combination (-p i) * hR'
    · simp only [Function.update_of_ne hik, hik, ↓reduceIte]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte] at hR ⊢
        linear_combination (-p i) * hR
      · simp only [hki, ↓reduceIte] at hR ⊢
        linear_combination (-p i) * hR
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq' (range N) k]
  simp only [mem_range.2 hk, ↓reduceIte]
  rw [← sum_filter, sum_mul]

/-- **Exercise 14.C.1** (MWG, p. 508), strict downward distortion. In addition to the assumptions
of `exercise_14_C_1_distortion`, let the first-best efforts be strictly increasing, and for a
state `k` below the top (`k + 1 < N`) let `e*_k > 0`, `π - g(·, θ_k)` be differentiable at `e*_k`
and `D_k` differentiable at `e*_k` with `D_k'(e*_k) > 0`. Then every optimal contract has
`e_k < e*_k`. -/
theorem exercise_14_C_1_strict {g : ℝ → ℝ → ℝ} {θ p w e estar : ℕ → ℝ} {prof : ℝ → ℝ}
    {c : ℝ} {N : ℕ} (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hs0 : ∀ i < N, 0 ≤ estar i)
    (hsmax : ∀ i < N, ∀ x, 0 ≤ x → x ≠ estar i →
      prof x - g x (θ i) < prof (estar i) - g (estar i) (θ i))
    (hss : ∀ i j, i < j → j < N → estar i < estar j)
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e)
    {k : ℕ} {sk dD : ℝ} (hk : k + 1 < N) (hpos : 0 < estar k)
    (hSd : HasDerivAt (fun x => prof x - g x (θ k)) sk (estar k))
    (hDd : HasDerivAt (c1D g θ k) dD (estar k)) (hdD : 0 < dD) : e k < estar k := by
  have hsm : ∀ i j, i ≤ j → j < N → estar i ≤ estar j := fun i j hij hj => by
    rcases hij.lt_or_eq with h | h
    · exact (hss i j h hj).le
    · rw [h]
  obtain ⟨hdown, -⟩ := exercise_14_C_1_distortion hN hp hg0 hsc hs0 hsmax hsm hf hopt
  obtain ⟨hmono, -, -, hmax⟩ := exercise_14_C_1_opt hN hp hg0 hsc hf hopt
  rcases (hdown k (by omega)).lt_or_eq with h | h
  · exact h
  exfalso
  have hsk : sk = 0 := by
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hSd
    filter_upwards [Ioi_mem_nhds hpos] with x hx
    rcases eq_or_ne x (estar k) with rfl | hne
    · exact le_rfl
    · exact (hsmax k (by omega) x (le_of_lt hx) hne).le
  set P := ∑ i ∈ (range N).filter (k < ·), p i
  have hP : 0 < P := by
    have hmem : k + 1 ∈ (range N).filter (k < ·) := mem_filter.2 ⟨mem_range.2 hk, by omega⟩
    have := single_le_sum (f := p) (fun i hi => (hp i (mem_range.1 (mem_filter.1 hi).1)).le)
      hmem
    linarith [hp (k + 1) hk]
  have hψ : HasDerivAt (fun x => p k * (prof x - g x (θ k)) - P * c1D g θ k x)
      (p k * sk - P * dD) (estar k) := (hSd.const_mul _).sub (hDd.const_mul _)
  have hneg : p k * sk - P * dD < 0 := by rw [hsk]; nlinarith
  set L : ℝ := if k = 0 then 0 else max 0 (e (k - 1))
  have hL0 : 0 ≤ L := by simp only [L]; split_ifs <;> simp
  have hL : L < estar k := by
    simp only [L]
    split_ifs with hk0
    · exact hpos
    · exact max_lt hpos (lt_of_le_of_lt (hdown (k - 1) (by omega)) (hss _ _ (by omega) (by omega)))
  obtain ⟨y, hy1, hy2⟩ := ((c4_left_gt hψ hneg).and (Ioo_mem_nhdsLT hL)).exists
  set e' := Function.update e k y
  have he' : ∀ i < N, 0 ≤ e' i := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simp only [e', Function.update_self]; linarith [hy2.1]
    · simp only [e', Function.update_of_ne hik]; exact hf.1 i hi
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    by_cases hik : i = k
    · subst hik
      by_cases hjk : j = i
      · subst hjk; exact le_rfl
      · simp only [e', Function.update_self, Function.update_of_ne hjk]
        rw [← h] at hy2
        exact hy2.2.le.trans (hmono _ _ hij hj)
    · by_cases hjk : j = k
      · subst hjk
        simp only [e', Function.update_self, Function.update_of_ne hik]
        have hj0 : j ≠ 0 := by omega
        have h1 : e i ≤ e (j - 1) := hmono _ _ (by omega) (by omega)
        have h2 : e (j - 1) ≤ L := by simp only [L, hj0, ↓reduceIte]; exact le_max_right _ _
        linarith [hy2.1]
      · simp only [e', Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hmono i j hij hj
  have hup := c1_VS_update (g := g) (θ := θ) (p := p) (e := e) (prof := prof) (c := c)
    (show k < N by omega) y
  have hle := hmax e' he' hm'
  rw [← h] at hy1
  linarith

/-- **Exercise 14.C.1, strict distortion in the instance** (MWG, p. 508): in the instance of
`exercise_14_C_1_instance` (`e*_i = i + 1`), the theorem gives `e_0 < e*_0 = 1` for the optimal
contract (whose effort is `2/3`). -/
theorem exercise_14_C_1_strict_instance :
    let e : ℕ → ℝ := fun i => if i = 0 then 2 / 3 else 2
    c1Ext 2 e 0 < (fun i : ℕ => (i : ℝ) + 1) 0 := by
  intro e
  obtain ⟨hf, hopt, -, -⟩ := exercise_14_C_1_instance
  set g : ℝ → ℝ → ℝ := fun x t => x ^ 2 / (2 * t)
  set θ : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hg0 : ∀ t, g 0 t = 0 := fun t => by simp [g]
  have hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0) := by
    intro i j hij x hx y hy hxy
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [g, θ, Set.mem_Ici] at hx hy ⊢
    have hk : 1 / (2 * ((j : ℝ) + 1)) < 1 / (2 * ((i : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
    rw [div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (y ^ 2),
      div_eq_mul_one_div (y ^ 2)]
    nlinarith
  have hsmax : ∀ i < 2, ∀ x : ℝ, 0 ≤ x → x ≠ (fun i : ℕ => (i : ℝ) + 1) i →
      id x - g x (θ i) < id ((fun i : ℕ => (i : ℝ) + 1) i) -
        g ((fun i : ℕ => (i : ℝ) + 1) i) (θ i) := by
    intro i _ x _ hne
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    simp only [id, g, θ]
    have : ((i : ℝ) + 1) - ((i : ℝ) + 1) ^ 2 / (2 * ((i : ℝ) + 1)) -
        (x - x ^ 2 / (2 * ((i : ℝ) + 1))) = (x - ((i : ℝ) + 1)) ^ 2 / (2 * ((i : ℝ) + 1)) := by
      field_simp; ring
    have h2 : 0 < (x - ((i : ℝ) + 1)) ^ 2 / (2 * ((i : ℝ) + 1)) :=
      div_pos (by positivity) (by positivity)
    linarith
  refine exercise_14_C_1_strict (g := g) (θ := θ) (p := fun _ => 1 / 2) (prof := id) (c := 0)
    (N := 2) (k := 0) (sk := 1 - 1) (dD := 1 / 2) (by norm_num) (fun _ _ => by norm_num) hg0
    hsc (fun i _ => by positivity) hsmax (fun i j hij _ => by
      have : (i : ℝ) < j := by exact_mod_cast hij
      change (i : ℝ) + 1 < (j : ℝ) + 1
      linarith) hf hopt (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
  · have hfun : (fun x => id x - g x (θ 0)) = fun x : ℝ => x - x ^ 2 / 2 := by
      funext x; simp [g, θ]
    rw [hfun]
    have h := (hasDerivAt_id' (1 : ℝ)).sub ((hasDerivAt_pow 2 (1 : ℝ)).div_const 2)
    convert h using 1 <;> norm_num
  · have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 4
    have hfun : c1D g θ 0 = fun x : ℝ => x ^ 2 / 4 := by
      funext x; simp only [c1D, g, θ]; norm_num; ring
    rw [hfun]
    convert this using 1 <;> norm_num

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.B.7: two periods

MWG, Exercise 14.B.7, p. 508. Two repetitions of the two-effort hidden-action model, no
discounting; the manager's utility is the sum of the two periods' `v(w) - g(e)`, with `v' > 0`,
`v'' < 0`. A contract pays `w₁(π₁)` in period 1 and `w₂(π₁, π₂)` in period 2; the manager chooses
`e₁` and, after observing `π₁`, `e₂(π₁)`. Profits take finitely many values (footnote 6;
corrections 7), with probabilities `f(π | e) > 0`.

* `b7U`, `B7Feas`, `b7Cost`: the manager's expected utility of a plan, the constraints for
  implementing `e_H` in both periods (participation and incentive compatibility against every
  plan `(e₁, e₂(·))`), and the owner's expected wage bill.
* `b7_local_inv`: a local inverse of `v`, with derivative `1/v'`.
* `b7_shift`: moving utility between the periods after a given `π₁` (period-1 utility down by
  `Δ`, period-2 utility up by `Δ` at every `π₂`) leaves the manager's payoff from every plan
  unchanged.
* `b7_improve`: **the "inverse Euler" condition**. If a feasible contract violates
  `1 / v'(w₁(π₁)) = Σ_{π₂} f(π₂|e_H) / v'(w₂(π₁, π₂))` at some `π₁`, a feasible contract with a
  strictly lower expected wage exists. So every optimal contract satisfies it at every `π₁`.
* `exercise_14_B_7`: **the answer: yes.** If `g(e_H) > g(e_L)` and `v` is strictly concave, no
  feasible contract whose period-2 wages do not depend on period-1 profits is optimal: the
  inverse Euler condition would make `w₁` constant, and then the manager would choose `e_L` in
  period 1.
* `exercise_14_B_7_instance`: repeating the optimal one-period scheme of Figure 14.B.1
  (`exA`, `exW`) in both periods is feasible and memoryless, hence not optimal.
-/

namespace MWG.PrincipalAgent

open Finset Filter Topology

/-- The manager's expected utility over the two periods from the plan `(e₁, e₂(·))`. -/
noncomputable def b7U {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (v : ℝ → ℝ) (g : ε → ℝ)
    (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) (e1 : ε) (e2 : Fin n → ε) : ℝ :=
  ∑ i, f e1 i * (v (w1 i) - g e1 + (∑ j, f (e2 i) j * v (w2 i j) - g (e2 i)))

/-- The constraints for implementing `e_H` in both periods: participation (two-period reservation
utility `ū`) and incentive compatibility against every plan. -/
def B7Feas {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (v : ℝ → ℝ) (g : ε → ℝ) (ubar : ℝ) (eH : ε)
    (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) : Prop :=
  ubar ≤ b7U f v g w1 w2 eH (fun _ => eH) ∧
    ∀ e1 e2, b7U f v g w1 w2 e1 e2 ≤ b7U f v g w1 w2 eH (fun _ => eH)

/-- The owner's expected wage bill when `e_H` is chosen in both periods. -/
noncomputable def b7Cost {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (eH : ε) (w1 : Fin n → ℝ)
    (w2 : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, f eH i * (w1 i + ∑ j, f eH j * w2 i j)

/-- A local inverse of `v` at `v(x₀)` (`v' > 0`), with derivative `1 / v'(x₀)`. -/
theorem b7_local_inv {v dv : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (dv x) x) (hdv : ∀ x, 0 < dv x)
    (x0 : ℝ) : ∃ G : ℝ → ℝ, G (v x0) = x0 ∧ (∀ᶠ y in 𝓝 (v x0), v (G y) = y) ∧
      HasDerivAt G (dv x0)⁻¹ (v x0) := by
  classical
  have hmono : StrictMono v := strictMono_of_hasDerivAt_pos hv hdv
  have hc : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  set a := v (x0 - 1)
  set b := v (x0 + 1)
  have hex : ∀ y ∈ Set.Ioo a b, ∃ x ∈ Set.Ioo (x0 - 1) (x0 + 1), v x = y := fun y hy =>
    intermediate_value_Ioo (by linarith) hc.continuousOn hy
  let G : ℝ → ℝ := fun y => if h : y ∈ Set.Ioo a b then Classical.choose (hex y h) else x0
  have hG : ∀ y (h : y ∈ Set.Ioo a b), G y ∈ Set.Ioo (x0 - 1) (x0 + 1) ∧ v (G y) = y := by
    intro y h
    simp only [G, h, ↓reduceDIte]
    exact Classical.choose_spec (hex y h)
  have hmem : v x0 ∈ Set.Ioo a b := ⟨hmono (by linarith), hmono (by linarith)⟩
  have hGx0 : G (v x0) = x0 := hmono.injective (hG _ hmem).2
  have hnhds : Set.Ioo a b ∈ 𝓝 (v x0) := Ioo_mem_nhds hmem.1 hmem.2
  have hev : ∀ᶠ y in 𝓝 (v x0), v (G y) = y := by
    filter_upwards [hnhds] with y hy
    exact (hG y hy).2
  have hcont : ContinuousAt G (v x0) := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Set.Ioo a b) ?_ hnhds ?_
    · intro y hy y' hy' hyy'
      exact hmono.le_iff_le.1 (by rw [(hG y hy).2, (hG y' hy').2]; exact hyy')
    · rw [hGx0]
      refine mem_of_superset (Ioo_mem_nhds (show x0 - 1 < x0 by linarith)
        (show x0 < x0 + 1 by linarith)) fun x hx => ?_
      have hy : v x ∈ Set.Ioo a b := ⟨hmono hx.1, hmono hx.2⟩
      exact ⟨v x, hy, hmono.injective (hG _ hy).2⟩
  refine ⟨G, hGx0, hev, ?_⟩
  exact HasDerivAt.of_local_left_inverse hcont (by rw [hGx0]; exact hv x0) (hdv x0).ne' hev

/-- Moving utility between the periods after `π₁ = i₀` leaves the manager's payoff from every plan
unchanged. -/
theorem b7_shift {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v : ℝ → ℝ} {g : ε → ℝ}
    (hsum : ∀ e, ∑ j, f e j = 1) (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) (i0 : Fin n)
    {x Δ : ℝ} {W : Fin n → ℝ} (hx : v x = v (w1 i0) - Δ) (hW : ∀ j, v (W j) = v (w2 i0 j) + Δ)
    (e1 : ε) (e2 : Fin n → ε) :
    b7U f v g (Function.update w1 i0 x) (Function.update w2 i0 W) e1 e2 =
      b7U f v g w1 w2 e1 e2 := by
  unfold b7U
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i = i0
  · subst hi
    simp only [Function.update_self, hx, hW]
    have : ∑ j, f (e2 i) j * (v (w2 i j) + Δ) = ∑ j, f (e2 i) j * v (w2 i j) + Δ := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hsum, one_mul]
    rw [this]; ring
  · simp only [Function.update_of_ne hi]

/-- **Exercise 14.B.7** (MWG, p. 508), the inverse Euler condition. With `v` differentiable,
`v' > 0` and positive probabilities, if a feasible contract violates
`1 / v'(w₁(i₀)) = Σ_j f(j|e_H) / v'(w₂(i₀, j))` at some `i₀`, then shifting utility between the
periods after `i₀` gives a feasible contract with a strictly lower expected wage. -/
theorem b7_improve {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ}
    {ubar : ℝ} {eH : ε} (hv : ∀ x, HasDerivAt v (dv x) x) (hdv : ∀ x, 0 < dv x)
    (hf : ∀ e i, 0 < f e i) (hsum : ∀ e, ∑ j, f e j = 1) {w1 : Fin n → ℝ}
    {w2 : Fin n → Fin n → ℝ} (hfeas : B7Feas f v g ubar eH w1 w2) {i0 : Fin n}
    (hne : 1 / dv (w1 i0) ≠ ∑ j, f eH j / dv (w2 i0 j)) :
    ∃ w1' w2', B7Feas f v g ubar eH w1' w2' ∧ b7Cost f eH w1' w2' < b7Cost f eH w1 w2 := by
  obtain ⟨G1, hG1, hev1, hd1⟩ := b7_local_inv hv hdv (w1 i0)
  have hj : ∀ j, ∃ G : ℝ → ℝ, G (v (w2 i0 j)) = w2 i0 j ∧
      (∀ᶠ y in 𝓝 (v (w2 i0 j)), v (G y) = y) ∧ HasDerivAt G (dv (w2 i0 j))⁻¹ (v (w2 i0 j)) :=
    fun j => b7_local_inv hv hdv (w2 i0 j)
  choose G2 hG2 hev2 hd2 using hj
  let C : ℝ → ℝ := fun Δ => (G1 (v (w1 i0) - Δ) - w1 i0) +
    ∑ j, f eH j * (G2 j (v (w2 i0 j) + Δ) - w2 i0 j)
  have hC0 : C 0 = 0 := by simp [C, hG1, hG2]
  have hdC : HasDerivAt C (-(dv (w1 i0))⁻¹ + ∑ j, f eH j * (dv (w2 i0 j))⁻¹) 0 := by
    have h1 : HasDerivAt (fun Δ => G1 (v (w1 i0) - Δ)) (-(dv (w1 i0))⁻¹) 0 :=
      HasDerivAt.comp_const_sub (v (w1 i0)) 0 (by simpa using hd1)
    have h2 : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt
        (fun Δ => f eH j * (G2 j (v (w2 i0 j) + Δ) - w2 i0 j)) (f eH j * (dv (w2 i0 j))⁻¹) 0 :=
      fun j _ => ((HasDerivAt.comp_const_add (v (w2 i0 j)) 0
        (by simpa using hd2 j)).sub_const _).const_mul _
    exact (h1.sub_const _).add (HasDerivAt.fun_sum h2)
  have hD : -(dv (w1 i0))⁻¹ + ∑ j, f eH j * (dv (w2 i0 j))⁻¹ ≠ 0 := by
    intro h
    apply hne
    have : ∑ j, f eH j / dv (w2 i0 j) = ∑ j, f eH j * (dv (w2 i0 j))⁻¹ :=
      sum_congr rfl fun j _ => div_eq_mul_inv _ _
    rw [this, one_div]
    linarith
  have hfreq : ∃ᶠ Δ in 𝓝 (0 : ℝ), C Δ < 0 := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    have hmin : IsLocalMin C 0 := by
      filter_upwards [hcon] with Δ hΔ
      rw [hC0]; exact not_lt.1 hΔ
    exact hD (hmin.hasDerivAt_eq_zero hdC)
  have hE1 : ∀ᶠ Δ in 𝓝 (0 : ℝ), v (G1 (v (w1 i0) - Δ)) = v (w1 i0) - Δ := by
    have ht : Tendsto (fun Δ : ℝ => v (w1 i0) - Δ) (𝓝 0) (𝓝 (v (w1 i0))) :=
      (continuous_const.sub continuous_id).tendsto' 0 _ (by simp)
    exact ht.eventually hev1
  have hE2 : ∀ᶠ Δ in 𝓝 (0 : ℝ), ∀ j, v (G2 j (v (w2 i0 j) + Δ)) = v (w2 i0 j) + Δ := by
    rw [Filter.eventually_all]
    intro j
    have ht : Tendsto (fun Δ : ℝ => v (w2 i0 j) + Δ) (𝓝 0) (𝓝 (v (w2 i0 j))) :=
      (continuous_const.add continuous_id).tendsto' 0 _ (by simp)
    exact ht.eventually (hev2 j)
  obtain ⟨Δ, hCΔ, h1, h2⟩ := (hfreq.and_eventually (hE1.and hE2)).exists
  refine ⟨Function.update w1 i0 (G1 (v (w1 i0) - Δ)),
    Function.update w2 i0 (fun j => G2 j (v (w2 i0 j) + Δ)), ⟨?_, fun e1 e2 => ?_⟩, ?_⟩
  · rw [b7_shift hsum w1 w2 i0 h1 h2]; exact hfeas.1
  · rw [b7_shift hsum w1 w2 i0 h1 h2, b7_shift hsum w1 w2 i0 h1 h2]; exact hfeas.2 e1 e2
  · unfold b7Cost
    have hCd : C Δ = (G1 (v (w1 i0) - Δ) + ∑ j, f eH j * G2 j (v (w2 i0 j) + Δ)) -
        (w1 i0 + ∑ j, f eH j * w2 i0 j) := by
      simp only [C, mul_sub, sum_sub_distrib]; ring
    have key : ∀ i, f eH i * (Function.update w1 i0 (G1 (v (w1 i0) - Δ)) i +
        ∑ j, f eH j * Function.update w2 i0 (fun j => G2 j (v (w2 i0 j) + Δ)) i j) =
        f eH i * (w1 i + ∑ j, f eH j * w2 i j) + if i = i0 then f eH i0 * C Δ else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi
        simp only [Function.update_self, ↓reduceIte, hCd]
        ring
      · simp only [Function.update_of_ne hi, hi, ↓reduceIte, add_zero]
    rw [sum_congr rfl fun i _ => key i, sum_add_distrib, sum_ite_eq' univ i0]
    simp only [mem_univ, ↓reduceIte]
    have := mul_lt_mul_of_pos_left (show C Δ < 0 from hCΔ) (hf eH i0)
    linarith

/-- **Exercise 14.B.7** (MWG, p. 508): **yes, period-2 wages depend on period-1 profits in the
optimal contract.** Suppose `g(e_L) < g(e_H)`, `v` is strictly concave and differentiable with
`v' > 0`, and all probabilities are positive. If a feasible contract (implementing `e_H` in both
periods) has period-2 wages `w₂(π₁, π₂) = h(π₂)` independent of `π₁`, then a feasible contract
with a strictly lower expected wage exists. (Otherwise the inverse Euler condition `b7_improve`
would hold at every `π₁`, forcing `w₁` to be constant, and then the manager would choose `e_L` in
period 1.) -/
theorem exercise_14_B_7 {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ}
    {ubar : ℝ} {eL eH : ε} (hv : StrictConcaveOn ℝ Set.univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x) (hf : ∀ e i, 0 < f e i)
    (hsum : ∀ e, ∑ j, f e j = 1) (hg : g eL < g eH) {w1 : Fin n → ℝ}
    {w2 : Fin n → Fin n → ℝ} (hfeas : B7Feas f v g ubar eH w1 w2)
    (hmem : ∃ h : Fin n → ℝ, ∀ i j, w2 i j = h j) :
    ∃ w1' w2', B7Feas f v g ubar eH w1' w2' ∧ b7Cost f eH w1' w2' < b7Cost f eH w1 w2 := by
  by_cases hIE : ∀ i, 1 / dv (w1 i) = ∑ j, f eH j / dv (w2 i j)
  · exfalso
    obtain ⟨h, hh⟩ := hmem
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; have := hsum eH; simp at this
      · exact h0
    set i0 : Fin n := ⟨0, hn⟩
    have hw1 : ∀ i, w1 i = w1 i0 := by
      intro i
      have h1 := hIE i
      have h2 := hIE i0
      simp only [hh] at h1 h2
      have hd : dv (w1 i) = dv (w1 i0) := by
        rw [← h2, one_div, one_div] at h1
        exact inv_injective h1
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (c4_dv_lt hv hdv hlt).ne' hd
      · exact (c4_dv_lt hv hdv hlt).ne hd
    have hU : ∀ e, b7U f v g w1 w2 e (fun _ => eH) =
        v (w1 i0) - g e + (∑ j, f eH j * v (h j) - g eH) := by
      intro e
      unfold b7U
      simp only [hw1, hh]
      rw [← sum_mul, hsum, one_mul]
    have := hfeas.2 eL (fun _ => eH)
    rw [hU, hU] at this
    linarith
  · push Not at hIE
    obtain ⟨i0, hne⟩ := hIE
    exact b7_improve hdv hdvpos hf hsum hfeas hne

/-- The probabilities of the instance: `f(·|e_L) = (1/2, 1/4, 1/4)`, `f(·|e_H) = (1/4, 1/2, 1/4)`
(those of `exA`). -/
noncomputable def b7f (b : Bool) : Fin 3 → ℝ :=
  if b then ![1 / 4, 1 / 2, 1 / 4] else ![1 / 2, 1 / 4, 1 / 4]

/-- The period-1 scheme of the instance: the optimal one-period scheme `exW` of Figure 14.B.1,
`(0, log (5/2), log 2)`. -/
noncomputable def b7w : Fin 3 → ℝ := ![0, Real.log (5 / 2), Real.log 2]

/-- **Exercise 14.B.7, an instance** (MWG, p. 508). Repeating the optimal one-period scheme of
Figure 14.B.1 in both periods (`v(w) = -exp(-w)`, `g(e_H) = 3/20`, `g(e_L) = 0`, two-period
reservation utility `2 · (-29/40)`) is feasible and memoryless; by `exercise_14_B_7` a strictly
cheaper feasible contract exists. -/
theorem exercise_14_B_7_instance :
    B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) (-29 / 20) true
      b7w (fun _ j => b7w j) ∧
    ∃ w1' w2', B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 20) true w1' w2' ∧
      b7Cost b7f true w1' w2' < b7Cost b7f true b7w (fun _ j => b7w j) := by
  have hsum : ∀ e, ∑ j, b7f e j = 1 := by
    intro e; cases e <;> simp [b7f, Fin.sum_univ_three] <;> norm_num
  have hf : ∀ e i, 0 < b7f e i := by
    intro e i; cases e <;> fin_cases i <;> simp [b7f]
  have e1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hinner : ∀ e : Bool, ∑ j, b7f e j * -Real.exp (-b7w j) - (if e then 3 / 20 else 0) =
      -29 / 40 := by
    intro e
    cases e <;> simp [b7f, b7w, Fin.sum_univ_three, e1, e2] <;> norm_num
  have hU : ∀ e1 e2, b7U b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) b7w
      (fun _ j => b7w j) e1 e2 = -29 / 20 := by
    intro e1 e2
    unfold b7U
    have : ∀ i, b7f e1 i * (-Real.exp (-b7w i) - (if e1 then 3 / 20 else 0) +
        (∑ j, b7f (e2 i) j * -Real.exp (-b7w j) - (if e2 i then 3 / 20 else 0))) =
        b7f e1 i * -Real.exp (-b7w i) - b7f e1 i * (if e1 then 3 / 20 else 0) +
          b7f e1 i * (-29 / 40) := fun i => by rw [hinner]; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, hsum, one_mul]
    have := hinner e1
    linarith
  have hfeas : B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 20) true b7w (fun _ j => b7w j) :=
    ⟨by rw [hU], fun e1 e2 => by rw [hU, hU]⟩
  refine ⟨hfeas, exercise_14_B_7 (eL := false) exA_strictConcave exA_hasDeriv
    (fun _ => Real.exp_pos _) hf hsum (by norm_num) hfeas ⟨b7w, fun _ _ => rfl⟩⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.B.8: costly investigation

MWG, Exercise 14.B.8, p. 508. Profits `π` and a signal `y` have a joint distribution
`f(π, y | e) > 0`; here both take finitely many values (footnote 6; corrections 7), `f(π|e)` is
the marginal of `π`. After observing `π` the owner investigates with probability `p(π)` at cost
`c`; the contract pays `w(π)` without investigation and `w(π, y)` after one. The manager has
utility `v(w) - g(e)`, two effort levels, reservation utility `ū`.

* `b8EV`, `b8Cost`, `B8Feas`: expected utility of income, the owner's expected cost (wages and
  investigation), and the constraints for implementing `e_H`.
* `b8_persp`: the program is convex in the variables `((1 - p) v(w), p, p v(w(·, y)))` (a
  perspective argument): mixtures of contracts can be matched in utility at no higher cost.
* `b8_lag`: the Lagrangian separates across profit levels:
  `Σ_π [(1 - p(π)) A_π(w(π)) + p(π) B_π(w(π, ·))]`, with `A_π`, `B_π` the pointwise Lagrangians
  without and with investigation (`B_π` includes the cost `c f(π|e_H)`).
* `exercise_14_B_8`: **the characterization.** At every optimal contract for implementing `e_H`
  there are multipliers `γ, μ ≥ 0` with complementary slackness such that, at every profit level:
  without investigation (`p < 1`) `1/v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]`; after
  investigation (`p > 0`) `1/v'(w(π, y)) = γ + μ [1 - f(π, y|e_L)/f(π, y|e_H)]`; the owner does not
  investigate (`p < 1`) only if `A_π(w(π)) ≤ B_π(w')` for every `w'`, and investigates (`p > 0`)
  only if `B_π(w(π, ·)) ≤ A_π(w')` for every `w'`: investigation happens exactly where its
  Lagrangian saving exceeds its cost, and randomization only under indifference.
* `exercise_14_B_8_instance`: with an uninformative signal and `c ≥ 0`, never investigating and
  paying the scheme of Figure 14.B.1 is optimal; the theorem applies to it.
-/

namespace MWG.PrincipalAgent

open Finset Set

variable {ε : Type*} {n m : ℕ}

/-- The marginal probability `f(π_i | e) = Σ_y f(π_i, y | e)`. -/
noncomputable def b8F (fq : ε → Fin n → Fin m → ℝ) (e : ε) (i : Fin n) : ℝ := ∑ k, fq e i k

/-- Expected utility of income under effort `e`:
`Σ_π [(1 - p(π)) f(π|e) v(w(π)) + p(π) Σ_y f(π, y|e) v(w(π, y))]`. -/
noncomputable def b8EV (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (e : ε) (p w0 : Fin n → ℝ)
    (w1 : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ((1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))

/-- The owner's expected cost when `e_H` is chosen: wages plus `c` per investigation. -/
noncomputable def b8Cost (fq : ε → Fin n → Fin m → ℝ) (c : ℝ) (eH : ε) (p w0 : Fin n → ℝ)
    (w1 : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ((1 - p i) * b8F fq eH i * w0 i + p i * (∑ k, fq eH i k * w1 i k + c * b8F fq eH i))

/-- The constraints for implementing `e_H` (two effort levels): probabilities in `[0, 1]`,
participation and incentive compatibility. -/
def B8Feas (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (g : ε → ℝ) (ubar : ℝ) (eL eH : ε)
    (p w0 : Fin n → ℝ) (w1 : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ubar ≤ b8EV fq v eH p w0 w1 - g eH ∧
    b8EV fq v eL p w0 w1 - g eL ≤ b8EV fq v eH p w0 w1 - g eH

/-- The pointwise Lagrangian without investigation at profit level `i`. -/
noncomputable def b8A (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (eL eH : ε) (γ μ : ℝ)
    (i : Fin n) (x : ℝ) : ℝ :=
  b8F fq eH i * x - (γ + μ) * (b8F fq eH i * v x) + μ * (b8F fq eL i * v x)

/-- The pointwise Lagrangian with investigation at profit level `i` (including its cost). -/
noncomputable def b8B (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (c : ℝ) (eL eH : ε) (γ μ : ℝ)
    (i : Fin n) (z : Fin m → ℝ) : ℝ :=
  ∑ k, (fq eH i k * z k - (γ + μ) * (fq eH i k * v (z k)) + μ * (fq eL i k * v (z k))) +
    c * b8F fq eH i

/-- **The perspective step** (Exercise 14.B.8). For weights `s₀, s₁ ≥ 0` and wages `a, b`, some
wage `x` has `(s₀ + s₁) v(x) = s₀ v(a) + s₁ v(b)` and `(s₀ + s₁) x ≤ s₀ a + s₁ b` (`v` concave,
continuous and strictly increasing). -/
theorem b8_persp {v : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) (hvc : Continuous v)
    (hvm : StrictMono v) {s0 s1 : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (a b : ℝ) :
    ∃ x, (s0 + s1) * v x = s0 * v a + s1 * v b ∧ (s0 + s1) * x ≤ s0 * a + s1 * b := by
  rcases (add_nonneg h0 h1).lt_or_eq with hs | hs
  · set α := s0 / (s0 + s1)
    set β := s1 / (s0 + s1)
    have hα : 0 ≤ α := div_nonneg h0 hs.le
    have hβ : 0 ≤ β := div_nonneg h1 hs.le
    have hαβ : α + β = 1 := by simp only [α, β]; field_simp
    have hmem : α * v a + β * v b ∈ Icc (v (min a b)) (v (max a b)) := by
      have a1 := hvm.monotone (min_le_left a b)
      have a2 := hvm.monotone (min_le_right a b)
      have a3 := hvm.monotone (le_max_left a b)
      have a4 := hvm.monotone (le_max_right a b)
      have e1 : v (min a b) = α * v (min a b) + β * v (min a b) := by
        rw [← add_mul, hαβ, one_mul]
      have e2 : v (max a b) = α * v (max a b) + β * v (max a b) := by
        rw [← add_mul, hαβ, one_mul]
      constructor
      · linarith [mul_le_mul_of_nonneg_left a1 hα, mul_le_mul_of_nonneg_left a2 hβ]
      · linarith [mul_le_mul_of_nonneg_left a3 hα, mul_le_mul_of_nonneg_left a4 hβ]
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc min_le_max hvc.continuousOn hmem
    refine ⟨x, ?_, ?_⟩
    · rw [hx]; simp only [α, β]; field_simp
    · have hc := hv.2 (mem_univ a) (mem_univ b) hα hβ hαβ
      simp only [smul_eq_mul] at hc
      rw [← hx] at hc
      have hle := hvm.le_iff_le.1 hc
      have : (s0 + s1) * (α * a + β * b) = s0 * a + s1 * b := by
        simp only [α, β]; field_simp
      nlinarith
  · have hs0 : s0 = 0 := by linarith
    have hs1 : s1 = 0 := by linarith
    exact ⟨0, by rw [hs0, hs1]; ring, by rw [hs0, hs1]; simp⟩

/-- **The Lagrangian separates** across profit levels. -/
theorem b8_lag (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (c : ℝ) (eL eH : ε) (γ μ : ℝ)
    (p w0 : Fin n → ℝ) (w1 : Fin n → Fin m → ℝ) :
    b8Cost fq c eH p w0 w1 - (γ + μ) * b8EV fq v eH p w0 w1 + μ * b8EV fq v eL p w0 w1 =
      ∑ i, ((1 - p i) * b8A fq v eL eH γ μ i (w0 i) + p i * b8B fq v c eL eH γ μ i (w1 i)) := by
  unfold b8Cost b8EV b8A b8B
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  ring

/-- Changing a sum at one index. -/
theorem b8_upd {k : ℕ} (T T' : Fin k → ℝ) (i0 : Fin k) (h : ∀ i, i ≠ i0 → T' i = T i) :
    ∑ i, T' i = ∑ i, T i + (T' i0 - T i0) := by
  have : ∀ i, T' i = T i + if i = i0 then T' i0 - T i0 else 0 := by
    intro i
    by_cases hi : i = i0
    · subst hi; simp
    · simp [hi, h i hi]
  rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_ite_eq' univ i0]
  simp

/-- A minimizer of `x ↦ P x - K (Q v(x))` type expressions: if `x ↦ a x - b v(x)` is minimized
at `x₀` with `a > 0` and `v'(x₀) > 0`, then `1 / v'(x₀) = b / a`. -/
theorem b8_foc {v dv : ℝ → ℝ} (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    {a b x0 : ℝ} (ha : 0 < a) (hmin : ∀ x, a * x0 - b * v x0 ≤ a * x - b * v x) :
    1 / dv x0 = b / a := by
  have hd : HasDerivAt (fun x => a * x - b * v x) (a * 1 - b * dv x0) x0 :=
    ((hasDerivAt_id' x0).const_mul a).sub ((hdv x0).const_mul b)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmin) hd
  have := hdvpos x0
  field_simp
  linarith

/-- **Exercise 14.B.8** (MWG, p. 508), the characterization of the optimal contract for
implementing `e_H` with costly investigation. Assumptions: `v` concave and differentiable with
`v' > 0`; positive joint probabilities; the profit distributions under `e_L` and `e_H` differ
(`f(π|e_L) < f(π|e_H)` at some `π`). At every optimal contract there are multipliers
`γ, μ ≥ 0` with complementary slackness such that at every profit level `π_i`:
(a) if `p_i < 1`, `1/v'(w(π_i)) = γ + μ [1 - f(π_i|e_L)/f(π_i|e_H)]`;
(b) if `p_i > 0`, `1/v'(w(π_i, y)) = γ + μ [1 - f(π_i, y|e_L)/f(π_i, y|e_H)]` for every `y`;
(c) if `p_i < 1`, not investigating is optimal: `A_i(w(π_i)) ≤ B_i(z)` for every wage schedule `z`
after investigation; (d) if `p_i > 0`, investigating is optimal: `B_i(w(π_i, ·)) ≤ A_i(x)` for
every wage `x`. -/
theorem exercise_14_B_8 {fq : ε → Fin n → Fin m → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ} {c ubar : ℝ}
    {eL eH : ε} (hv : ConcaveOn ℝ univ v) (hdv : ∀ x, HasDerivAt v (dv x) x)
    (hdvpos : ∀ x, 0 < dv x) (hfq : ∀ e i k, 0 < fq e i k)
    (hdiff : ∃ i, b8F fq eL i < b8F fq eH i) {p w0 : Fin n → ℝ} {w1 : Fin n → Fin m → ℝ}
    (hf : B8Feas fq v g ubar eL eH p w0 w1)
    (hopt : ∀ p' w0' w1', B8Feas fq v g ubar eL eH p' w0' w1' →
      b8Cost fq c eH p w0 w1 ≤ b8Cost fq c eH p' w0' w1') :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (b8EV fq v eH p w0 w1 - g eH - ubar) = 0 ∧
      μ * ((b8EV fq v eH p w0 w1 - g eH) - (b8EV fq v eL p w0 w1 - g eL)) = 0 ∧
      ∀ i, (p i < 1 → 1 / dv (w0 i) = γ + μ * (1 - b8F fq eL i / b8F fq eH i)) ∧
        (0 < p i → ∀ k, 1 / dv (w1 i k) = γ + μ * (1 - fq eL i k / fq eH i k)) ∧
        (p i < 1 → ∀ z, b8A fq v eL eH γ μ i (w0 i) ≤ b8B fq v c eL eH γ μ i z) ∧
        (0 < p i → ∀ x, b8B fq v c eL eH γ μ i (w1 i) ≤ b8A fq v eL eH γ μ i x) := by
  classical
  have hvm : StrictMono v := strictMono_of_hasDerivAt_pos hdv hdvpos
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hdv x).continuousAt
  obtain ⟨id0, hid0⟩ := hdiff
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [b8F] at hid0
    · exact h
  have hF : ∀ e i, 0 < b8F fq e i := fun e i =>
    sum_pos (fun k _ => hfq e i k) ⟨⟨0, hm⟩, mem_univ _⟩
  let X := {x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin m → ℝ) // ∀ i, 0 ≤ x.1 i ∧ x.1 i ≤ 1}
  let EV : ε → X → ℝ := fun e x => b8EV fq v e x.1.1 x.1.2.1 x.1.2.2
  let J : X → ℝ := fun x => b8Cost fq c eH x.1.1 x.1.2.1 x.1.2.2
  let G : Fin 2 → X → ℝ := ![fun x => ubar - (EV eH x - g eH),
    fun x => (EV eL x - g eL) - (EV eH x - g eH)]
  have hG0 : ∀ x, G 0 x = ubar - (EV eH x - g eH) := fun x => rfl
  have hG1 : ∀ x, G 1 x = (EV eL x - g eL) - (EV eH x - g eH) := fun x => rfl
  let xs : X := ⟨(p, w0, w1), hf.1⟩
  -- the convex-like property
  have hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x : X,
      J x ≤ (1 - t) * J x0 + t * J x1 ∧ ∀ e, EV e x = (1 - t) * EV e x0 + t * EV e x1 := by
    intro x0 x1 t ht0 ht1
    obtain ⟨⟨p0, a0, b0⟩, hp0⟩ := x0
    obtain ⟨⟨p1, a1, b1⟩, hp1⟩ := x1
    have hA : ∀ i, ∃ x, ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * v x =
        (1 - t) * (1 - p0 i) * v (a0 i) + t * (1 - p1 i) * v (a1 i) ∧
        ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * x ≤
          (1 - t) * (1 - p0 i) * a0 i + t * (1 - p1 i) * a1 i := fun i =>
      b8_persp hv hvc hvm (mul_nonneg (by linarith) (by linarith [(hp0 i).2]))
        (mul_nonneg ht0 (by linarith [(hp1 i).2])) _ _
    have hB : ∀ i k, ∃ x, ((1 - t) * p0 i + t * p1 i) * v x =
        (1 - t) * p0 i * v (b0 i k) + t * p1 i * v (b1 i k) ∧
        ((1 - t) * p0 i + t * p1 i) * x ≤ (1 - t) * p0 i * b0 i k + t * p1 i * b1 i k :=
      fun i k => b8_persp hv hvc hvm (mul_nonneg (by linarith) (hp0 i).1)
        (mul_nonneg ht0 (hp1 i).1) _ _
    choose a hav hac using hA
    choose b hbv hbc using hB
    have hpm : ∀ i, 0 ≤ (1 - t) * p0 i + t * p1 i ∧ (1 - t) * p0 i + t * p1 i ≤ 1 := fun i =>
      ⟨by nlinarith [(hp0 i).1, (hp1 i).1], by nlinarith [(hp0 i).2, (hp1 i).2]⟩
    refine ⟨⟨(fun i => (1 - t) * p0 i + t * p1 i, a, b), hpm⟩, ?_, fun e => ?_⟩
    · simp only [J, b8Cost]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      have e1 : 1 - ((1 - t) * p0 i + t * p1 i) = (1 - t) * (1 - p0 i) + t * (1 - p1 i) := by
        ring
      rw [e1]
      have h1 := mul_le_mul_of_nonneg_left (hac i) (hF eH i).le
      have h2 : ∑ k, fq eH i k * b i k * ((1 - t) * p0 i + t * p1 i) ≤
          ∑ k, fq eH i k * ((1 - t) * p0 i * b0 i k + t * p1 i * b1 i k) :=
        sum_le_sum fun k _ => by
          have := mul_le_mul_of_nonneg_left (hbc i k) (hfq eH i k).le
          linarith
      have h3 : ((1 - t) * p0 i + t * p1 i) * ∑ k, fq eH i k * b i k =
          ∑ k, fq eH i k * b i k * ((1 - t) * p0 i + t * p1 i) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      have h4 : ∑ k, fq eH i k * ((1 - t) * p0 i * b0 i k + t * p1 i * b1 i k) =
          (1 - t) * p0 i * ∑ k, fq eH i k * b0 i k + t * p1 i * ∑ k, fq eH i k * b1 i k := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
      nlinarith
    · simp only [EV, b8EV]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      have e1 : 1 - ((1 - t) * p0 i + t * p1 i) = (1 - t) * (1 - p0 i) + t * (1 - p1 i) := by
        ring
      rw [e1]
      have h1 : ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * b8F fq e i * v (a i) =
          b8F fq e i * (((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * v (a i)) := by ring
      have h2 : ((1 - t) * p0 i + t * p1 i) * ∑ k, fq e i k * v (b i k) =
          ∑ k, fq e i k * (((1 - t) * p0 i + t * p1 i) * v (b i k)) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      rw [h1, h2, hav i]
      simp only [hbv]
      have h3 : ∑ k, fq e i k * ((1 - t) * p0 i * v (b0 i k) + t * p1 i * v (b1 i k)) =
          (1 - t) * p0 i * ∑ k, fq e i k * v (b0 i k) + t * p1 i * ∑ k, fq e i k * v (b1 i k) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
      rw [h3]
      ring
  -- Slater's condition
  have hslater : ∃ x : X, ∀ i, G i x < 0 := by
    have hG0s : ubar - (b8EV fq v eH p w0 w1 - g eH) ≤ 0 := by linarith [hf.2.1]
    have hG1s : (b8EV fq v eL p w0 w1 - g eL) - (b8EV fq v eH p w0 w1 - g eH) ≤ 0 := by
      linarith [hf.2.2]
    have hΔv : ∀ y, 0 < v (y + 1) - v y := fun y => sub_pos.2 (hvm (by linarith))
    by_cases hp1 : p id0 < 1
    · have hEV : ∀ e, b8EV fq v e p (Function.update w0 id0 (w0 id0 + 1)) w1 =
          b8EV fq v e p w0 w1 + (1 - p id0) * b8F fq e id0 * (v (w0 id0 + 1) - v (w0 id0)) := by
        intro e
        unfold b8EV
        rw [b8_upd (fun i => (1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))
          (fun i => (1 - p i) * b8F fq e i * v (Function.update w0 id0 (w0 id0 + 1) i) +
            p i * ∑ k, fq e i k * v (w1 i k)) id0
          (fun i hi => by simp only [Function.update_of_ne hi])]
        simp only [Function.update_self]
        ring
      refine ⟨⟨(p, Function.update w0 id0 (w0 id0 + 1), w1), hf.1⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0]; simp only [EV]; rw [hEV]
        have := mul_pos (mul_pos (sub_pos.2 hp1) (hF eH id0)) (hΔv (w0 id0))
        linarith
      · rw [hG1]; simp only [EV]; rw [hEV, hEV]
        have := mul_pos (mul_pos (sub_pos.2 hp1) (sub_pos.2 hid0)) (hΔv (w0 id0))
        nlinarith
    · have hp1' : p id0 = 1 := le_antisymm (hf.1 id0).2 (not_lt.1 hp1)
      obtain ⟨k0, hk0⟩ : ∃ k, fq eL id0 k < fq eH id0 k := by
        by_contra hc
        push Not at hc
        have : b8F fq eH id0 ≤ b8F fq eL id0 := sum_le_sum fun k _ => hc k
        linarith
      set z := Function.update (w1 id0) k0 (w1 id0 k0 + 1)
      have hEV : ∀ e, b8EV fq v e p w0 (Function.update w1 id0 z) =
          b8EV fq v e p w0 w1 + p id0 * (fq e id0 k0 * (v (w1 id0 k0 + 1) - v (w1 id0 k0))) := by
        intro e
        unfold b8EV
        rw [b8_upd (fun i => (1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))
          (fun i => (1 - p i) * b8F fq e i * v (w0 i) +
            p i * ∑ k, fq e i k * v (Function.update w1 id0 z i k)) id0
          (fun i hi => by simp only [Function.update_of_ne hi])]
        simp only [Function.update_self]
        rw [b8_upd (fun k => fq e id0 k * v (w1 id0 k)) (fun k => fq e id0 k * v (z k)) k0
          (fun k hk => by simp only [z, Function.update_of_ne hk])]
        simp only [z, Function.update_self]
        ring
      refine ⟨⟨(p, w0, Function.update w1 id0 z), hf.1⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0]; simp only [EV]; rw [hEV, hp1']
        have := mul_pos (hfq eH id0 k0) (hΔv (w1 id0 k0))
        linarith
      · rw [hG1]; simp only [EV]; rw [hEV, hEV, hp1']
        have := mul_pos (sub_pos.2 hk0) (hΔv (w1 id0 k0))
        nlinarith
  obtain ⟨lam, hlam, hcs, hlag⟩ := kt_convexlike J G xs
    (Fin.forall_fin_two.2 ⟨by rw [hG0]; simp only [EV, xs]; linarith [hf.2.1],
      by rw [hG1]; simp only [EV, xs]; linarith [hf.2.2]⟩)
    (fun x hx => hopt x.1.1 x.1.2.1 x.1.2.2 ⟨x.2, by linarith [hG0 x ▸ hx 0],
      by linarith [hG1 x ▸ hx 1]⟩)
    (fun x0 x1 t ht0 ht1 => by
      obtain ⟨x, hJ, hEVx⟩ := hconv x0 x1 t ht0 ht1
      refine ⟨x, hJ, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0, hG0, hG0, hEVx]; apply le_of_eq; ring
      · rw [hG1, hG1, hG1, hEVx, hEVx]; apply le_of_eq; ring)
    hslater
  set γ := lam 0
  set μ := lam 1
  have hcs0 : γ * (ubar - (EV eH xs - g eH)) = 0 := hcs 0
  have hcs1 : μ * ((EV eL xs - g eL) - (EV eH xs - g eH)) = 0 := hcs 1
  -- the Lagrangian is minimized at the optimum
  let ℓ : Fin n → ℝ → ℝ → (Fin m → ℝ) → ℝ := fun i q x z =>
    (1 - q) * b8A fq v eL eH γ μ i x + q * b8B fq v c eL eH γ μ i z
  have hsep : ∀ x : X, ∑ i, ℓ i (p i) (w0 i) (w1 i) ≤
      ∑ i, ℓ i (x.1.1 i) (x.1.2.1 i) (x.1.2.2 i) := by
    intro x
    have h1 := hlag x
    rw [Fin.sum_univ_two, hG0, hG1] at h1
    have l1 := b8_lag fq v c eL eH γ μ p w0 w1
    have l2 := b8_lag fq v c eL eH γ μ x.1.1 x.1.2.1 x.1.2.2
    simp only [ℓ]
    rw [← l1, ← l2]
    simp only [J, EV, xs] at h1 hcs0 hcs1
    nlinarith
  have hloc : ∀ i0 q x z, 0 ≤ q → q ≤ 1 → ℓ i0 (p i0) (w0 i0) (w1 i0) ≤ ℓ i0 q x z := by
    intro i0 q x z hq0 hq1
    have hX : ∀ j, 0 ≤ Function.update p i0 q j ∧ Function.update p i0 q j ≤ 1 := by
      intro j
      by_cases hj : j = i0
      · subst hj; simp only [Function.update_self]; exact ⟨hq0, hq1⟩
      · simp only [Function.update_of_ne hj]; exact hf.1 j
    have h := hsep ⟨(Function.update p i0 q, Function.update w0 i0 x, Function.update w1 i0 z), hX⟩
    simp only at h
    rw [b8_upd (fun i => ℓ i (p i) (w0 i) (w1 i)) (fun i => ℓ i (Function.update p i0 q i)
      (Function.update w0 i0 x i) (Function.update w1 i0 z i)) i0
      (fun i hi => by simp only [Function.update_of_ne hi])] at h
    simp only [Function.update_self] at h
    linarith
  refine ⟨γ, μ, hlam 0, hlam 1, ?_, ?_, fun i => ⟨fun hp => ?_, fun hp k => ?_, fun hp z => ?_,
    fun hp x => ?_⟩⟩
  · simp only [EV, xs] at hcs0; linear_combination -hcs0
  · simp only [EV, xs] at hcs1; linear_combination -hcs1
  · -- first-order condition without investigation
    have hmin : ∀ x, b8F fq eH i * w0 i - ((γ + μ) * b8F fq eH i - μ * b8F fq eL i) * v (w0 i) ≤
        b8F fq eH i * x - ((γ + μ) * b8F fq eH i - μ * b8F fq eL i) * v x := by
      intro x
      have h := hloc i (p i) x (w1 i) (hf.1 i).1 (hf.1 i).2
      simp only [ℓ, b8A] at h
      have h' : (1 - p i) * (b8F fq eH i * w0 i - (γ + μ) * (b8F fq eH i * v (w0 i)) +
          μ * (b8F fq eL i * v (w0 i))) ≤ (1 - p i) * (b8F fq eH i * x -
          (γ + μ) * (b8F fq eH i * v x) + μ * (b8F fq eL i * v x)) := by linarith
      have := le_of_mul_le_mul_left h' (sub_pos.2 hp)
      linarith
    rw [b8_foc hdv hdvpos (hF eH i) hmin]
    have := (hF eH i).ne'
    field_simp
    ring
  · -- first-order condition after investigation
    have hmin : ∀ y, fq eH i k * w1 i k - ((γ + μ) * fq eH i k - μ * fq eL i k) * v (w1 i k) ≤
        fq eH i k * y - ((γ + μ) * fq eH i k - μ * fq eL i k) * v y := by
      intro y
      have h := hloc i (p i) (w0 i) (Function.update (w1 i) k y) (hf.1 i).1 (hf.1 i).2
      simp only [ℓ, b8B] at h
      rw [b8_upd (fun k => fq eH i k * w1 i k - (γ + μ) * (fq eH i k * v (w1 i k)) +
          μ * (fq eL i k * v (w1 i k)))
        (fun k' => fq eH i k' * Function.update (w1 i) k y k' -
          (γ + μ) * (fq eH i k' * v (Function.update (w1 i) k y k')) +
          μ * (fq eL i k' * v (Function.update (w1 i) k y k'))) k
        (fun k' hk => by simp only [Function.update_of_ne hk])] at h
      simp only [Function.update_self] at h
      have h' : p i * (fq eH i k * w1 i k - (γ + μ) * (fq eH i k * v (w1 i k)) +
          μ * (fq eL i k * v (w1 i k))) ≤ p i * (fq eH i k * y - (γ + μ) * (fq eH i k * v y) +
          μ * (fq eL i k * v y)) := by linarith
      have := le_of_mul_le_mul_left h' hp
      linarith
    rw [b8_foc hdv hdvpos (hfq eH i k) hmin]
    have := (hfq eH i k).ne'
    field_simp
    ring
  · -- not investigating is optimal
    have h1 := hloc i 1 (w0 i) z zero_le_one le_rfl
    have h2 := hloc i 1 (w0 i) (w1 i) zero_le_one le_rfl
    simp only [ℓ] at h1 h2
    rcases (hf.1 i).1.lt_or_eq with hp0 | hp0
    · have : b8A fq v eL eH γ μ i (w0 i) ≤ b8B fq v c eL eH γ μ i (w1 i) := by
        have h3 : (1 - p i) * b8A fq v eL eH γ μ i (w0 i) ≤
            (1 - p i) * b8B fq v c eL eH γ μ i (w1 i) := by linarith
        exact le_of_mul_le_mul_left h3 (sub_pos.2 hp)
      nlinarith
    · rw [← hp0] at h1; linarith
  · -- investigating is optimal
    have h1 := hloc i 0 x (w1 i) le_rfl zero_le_one
    have h2 := hloc i 0 (w0 i) (w1 i) le_rfl zero_le_one
    simp only [ℓ] at h1 h2
    rcases (hf.1 i).2.lt_or_eq with hp1 | hp1
    · have : b8B fq v c eL eH γ μ i (w1 i) ≤ b8A fq v eL eH γ μ i (w0 i) := by
        have h3 : p i * b8B fq v c eL eH γ μ i (w1 i) ≤ p i * b8A fq v eL eH γ μ i (w0 i) := by
          linarith
        exact le_of_mul_le_mul_left h3 hp
      nlinarith
    · rw [hp1] at h1; linarith

/-- The exponential bound for the instance: if `K e^{-w*} = F`, then
`F x + K e^{-x} ≥ F w* + K e^{-w*}` (`e^t ≥ 1 + t`). -/
theorem b8_exp_bound {F K x ws : ℝ} (hK : 0 ≤ K) (hws : K * Real.exp (-ws) = F) :
    F * ws + K * Real.exp (-ws) ≤ F * x + K * Real.exp (-x) := by
  have h1 := Real.add_one_le_exp (-(x - ws))
  have h2 : Real.exp (-x) = Real.exp (-ws) * Real.exp (-(x - ws)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : K * Real.exp (-ws) * (-(x - ws) + 1) ≤ K * Real.exp (-ws) * Real.exp (-(x - ws)) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (Real.exp_pos _).le)
  rw [h2, ← mul_assoc]
  rw [hws] at h3 ⊢
  nlinarith

/-- The joint distribution of the instance: profits as in Figure 14.B.1 (`b7f`) and an
independent, uninformative signal taking two values with probability `1/2` each. -/
noncomputable def b8fq (e : Bool) (i : Fin 3) (_k : Fin 2) : ℝ := b7f e i / 2

/-- **Exercise 14.B.8, an instance** (MWG, p. 508). With an uninformative signal, investigation
cost `c ≥ 0`, `v(w) = -exp(-w)`, `g(e_H) = 3/20`, `g(e_L) = 0` and `ū = -29/40`, never
investigating and paying the scheme `(0, log (5/2), log 2)` of Figure 14.B.1 is optimal (a
Lagrangian certificate with `γ = 2`, `μ = 1`), and `exercise_14_B_8` applies to it. -/
theorem exercise_14_B_8_instance {c : ℝ} (hc : 0 ≤ c) :
    B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) (-29 / 40) false
      true (fun _ => 0) b7w (fun _ _ => 0) ∧
    (∀ p' w0' w1', B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 40) false true p' w0' w1' →
      b8Cost b8fq c true (fun _ => 0) b7w (fun _ _ => 0) ≤ b8Cost b8fq c true p' w0' w1') := by
  have hF : ∀ e i, b8F b8fq e i = b7f e i := fun e i => by
    simp only [b8F, b8fq, Fin.sum_univ_two]; ring
  have e1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEV : ∀ e, b8EV b8fq (fun w => -Real.exp (-w)) e (fun _ => 0) b7w (fun _ _ => 0) =
      ∑ i, b7f e i * -Real.exp (-b7w i) := fun e => by
    simp only [b8EV, hF, sub_zero, one_mul, zero_mul, add_zero]
  have hEVL : ∑ i, b7f false i * -Real.exp (-b7w i) = -29 / 40 := by
    simp [b7f, b7w, Fin.sum_univ_three, e1, e2]; norm_num
  have hEVH : ∑ i, b7f true i * -Real.exp (-b7w i) = -23 / 40 := by
    simp [b7f, b7w, Fin.sum_univ_three, e1, e2]; norm_num
  have hfeas : B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 40) false true (fun _ => 0) b7w (fun _ _ => 0) := by
    refine ⟨fun _ => ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;> simp only [hEV, hEVL, hEVH] <;> norm_num
  refine ⟨hfeas, fun p' w0' w1' hf' => ?_⟩
  -- the pointwise bound `A_i(x) ≥ A_i(w*_i)`
  have hA : ∀ i x, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) ≤
      b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i x := by
    intro i x
    have hform : ∀ y, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i y =
        b7f true i * y + (3 * b7f true i - b7f false i) * Real.exp (-y) := fun y => by
      simp only [b8A, hF]; ring
    rw [hform, hform]
    refine b8_exp_bound ?_ ?_
    · fin_cases i <;> simp [b7f] <;> norm_num
    · fin_cases i <;> simp [b7f, b7w, e1, e2] <;> norm_num
  have hB : ∀ i z, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) ≤
      b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i z := by
    intro i z
    have hform : b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i z =
        (b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (z 0) +
          b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (z 1)) / 2 +
          c * b8F b8fq true i := by
      simp only [b8B, b8A, hF, b8fq, Fin.sum_univ_two]; ring
    rw [hform]
    have := hA i (z 0)
    have := hA i (z 1)
    have : 0 ≤ c * b8F b8fq true i := mul_nonneg hc (by rw [hF]; fin_cases i <;> norm_num [b7f])
    linarith
  have hl' := b8_lag b8fq (fun w => -Real.exp (-w)) c false true 2 1 p' w0' w1'
  have hl0 := b8_lag b8fq (fun w => -Real.exp (-w)) c false true 2 1 (fun _ => 0) b7w
    (fun _ _ => 0)
  have hsum : ∑ i, ((1 - (fun _ => (0 : ℝ)) i) *
      b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) +
      (fun _ => (0 : ℝ)) i * b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i
        ((fun _ _ => (0 : ℝ)) i)) ≤
      ∑ i, ((1 - p' i) * b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (w0' i) +
        p' i * b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i (w1' i)) := by
    refine sum_le_sum fun i _ => ?_
    have h1 := hA i (w0' i)
    have h2 := hB i (w1' i)
    have hp0 := (hf'.1 i).1
    have hp1 := (hf'.1 i).2
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    nlinarith
  rw [← hl', ← hl0, hEV, hEV, hEVL, hEVH] at hsum
  obtain ⟨_, hIR, hIC⟩ := hf'
  simp only [Bool.false_eq_true, ↓reduceIte] at hIR hIC
  nlinarith

/-- **Exercise 14.B.8, the theorem applied to the instance**: the multipliers exist and the
characterization holds for the contract of `exercise_14_B_8_instance` (with `c = 1/10`). -/
theorem exercise_14_B_8_instance_applied :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ ∀ i, ((fun _ => (0 : ℝ)) i < 1 → 1 / Real.exp (-b7w i) =
      γ + μ * (1 - b8F b8fq false i / b8F b8fq true i)) := by
  obtain ⟨hf, hopt⟩ := exercise_14_B_8_instance (c := 1 / 10) (by norm_num)
  have hF : ∀ e i, b8F b8fq e i = b7f e i := fun e i => by
    simp only [b8F, b8fq, Fin.sum_univ_two]; ring
  obtain ⟨γ, μ, hγ, hμ, -, -, h⟩ := exercise_14_B_8 (c := 1 / 10) exA_strictConcave.concaveOn
    exA_hasDeriv (fun _ => Real.exp_pos _)
    (fun e i k => by unfold b8fq; cases e <;> fin_cases i <;> norm_num [b7f])
    ⟨1, by rw [hF, hF]; norm_num [b7f]⟩ hf hopt
  exact ⟨γ, μ, hγ, hμ, fun i => (h i).1⟩

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 14.C.3(a): necessity of the first-order conditions

MWG, Exercise 14.C.3(a), p. 509. With utility `v(w) - g(e, θ)` the optimal full-information
contract pays the same wage `w̄` in both states (`exercise_14_C_3a`), the participation constraint
binds, and `exercise_14_C_3a_sufficient` shows that the first-order conditions
`π'(e_i) v'(w̄) = g_e(e_i, θ_i)` are sufficient.

* `exercise_14_C_3a_necessary`: at an optimal contract `(w̄, e_H), (w̄, e_L)` with interior efforts
  the first-order conditions hold. The proof raises the effort in one state and pays the wage
  that keeps that state's utility (a local inverse of `v`, `b7_local_inv`); the change is
  feasible and the owner's payoff has a local maximum at the optimum.
* `exercise_14_C_3a_necessary_instance`: a proved instance.
-/

namespace MWG.PrincipalAgent

open Filter Topology

/-- One state of Exercise 14.C.3(a): if raising the effort from `e > 0` to `e + s` and paying a
wage `w'` that keeps the state's utility, `v(w') - g(e + s) = v(w̄) - g(e)`, never yields more than
`π(e) - w̄`, then `π'(e) v'(w̄) = g_e(e)`. -/
theorem c3_foc_state {v dv prof : ℝ → ℝ} {gθ : ℝ → ℝ} {dp ge wbar e : ℝ}
    (hdv : ∀ w, HasDerivAt v (dv w) w) (hdvpos : ∀ w, 0 < dv w) (he : 0 < e)
    (hdp : HasDerivAt prof dp e) (hg : HasDerivAt gθ ge e)
    (hopt : ∀ w' s, 0 ≤ e + s → v w' - gθ (e + s) = v wbar - gθ e →
      prof (e + s) - w' ≤ prof e - wbar) :
    dp * dv wbar = ge := by
  obtain ⟨G, hG0, hev, hdG⟩ := b7_local_inv hdv hdvpos wbar
  have hg1 : HasDerivAt (fun s => gθ (e + s)) ge 0 := HasDerivAt.comp_const_add e 0 (by simpa)
  have hp1 : HasDerivAt (fun s => prof (e + s)) dp 0 := HasDerivAt.comp_const_add e 0 (by simpa)
  have hdy : HasDerivAt (fun s => v wbar + (gθ (e + s) - gθ e)) ge 0 :=
    (hg1.sub_const (gθ e)).const_add (v wbar)
  have hy0 : v wbar + (gθ (e + 0) - gθ e) = v wbar := by simp
  have hψ : HasDerivAt (fun s => prof (e + s) - G (v wbar + (gθ (e + s) - gθ e)))
      (dp - (dv wbar)⁻¹ * ge) 0 :=
    hp1.sub (HasDerivAt.comp_of_eq 0 hdG hdy hy0.symm)
  have ht : Tendsto (fun s => v wbar + (gθ (e + s) - gθ e)) (𝓝 0) (𝓝 (v wbar)) := by
    have := hdy.continuousAt.tendsto
    rwa [hy0] at this
  have hmax : IsLocalMax (fun s => prof (e + s) - G (v wbar + (gθ (e + s) - gθ e))) 0 := by
    filter_upwards [ht.eventually hev, Ioo_mem_nhds (show -e < 0 by linarith) he] with s hs hs2
    have h := hopt (G (v wbar + (gθ (e + s) - gθ e))) s (by linarith [hs2.1]) (by rw [hs]; ring)
    simp only [add_zero, sub_self, hG0]
    exact h
  have h0 := hmax.hasDerivAt_eq_zero hψ
  have := hdvpos wbar
  field_simp at h0
  linarith

/-- **Exercise 14.C.3(a)** (MWG, p. 509), necessity of the first-order conditions. Let
`(w̄, e_H), (w̄, e_L)` with `e_H, e_L > 0` be an optimal full-information contract (by
`exercise_14_C_3a` every optimum pays a single wage) with binding participation constraint, and let
`π` and `g(·, θ_i)` be differentiable at `e_i`. Then `π'(e_i) v'(w̄) = g_e(e_i, θ_i)` in both
states. -/
theorem exercise_14_C_3a_necessary {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    {dpH dpL geH geL θL θH lam ubar wbar eH eL : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hdv : ∀ w, HasDerivAt v (dv w) w) (hdvpos : ∀ w, 0 < dv w) (hH : 0 < eH) (hL : 0 < eL)
    (hdpH : HasDerivAt prof dpH eH) (hdpL : HasDerivAt prof dpL eL)
    (hgH : HasDerivAt (fun e => g e θH) geH eH) (hgL : HasDerivAt (fun e => g e θL) geL eL)
    (hbind : lam * (v wbar - g eH θH) + (1 - lam) * (v wbar - g eL θL) = ubar)
    (hopt : ∀ wH' eH' wL' eL', 0 ≤ eH' → 0 ≤ eL' →
      ubar ≤ lam * (v wH' - g eH' θH) + (1 - lam) * (v wL' - g eL' θL) →
      lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL') ≤
        lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar)) :
    dpH * dv wbar = geH ∧ dpL * dv wbar = geL := by
  refine ⟨c3_foc_state (gθ := fun e => g e θH) hdv hdvpos hH hdpH hgH fun w' s hs hu => ?_,
    c3_foc_state (gθ := fun e => g e θL) hdv hdvpos hL hdpL hgL fun w' s hs hu => ?_⟩
  · have hu' : v w' - g (eH + s) θH = v wbar - g eH θH := hu
    have h := hopt w' (eH + s) wbar eL hs hL.le (le_of_eq (by rw [← hbind, hu']))
    have := le_of_mul_le_mul_left (show lam * (prof (eH + s) - w') ≤ lam * (prof eH - wbar) by
      linarith) hl0
    exact this
  · have hu' : v w' - g (eL + s) θL = v wbar - g eL θL := hu
    have h := hopt wbar eH w' (eL + s) hH.le hs (le_of_eq (by rw [← hbind, hu']))
    exact le_of_mul_le_mul_left (show (1 - lam) * (prof (eL + s) - w') ≤
      (1 - lam) * (prof eL - wbar) by linarith) (by linarith)

/-- **Exercise 14.C.3(a), an instance** (MWG, p. 509). `v(w) = -exp(-w)`, `π(e) = e`,
`g(e, θ) = e²/(2θ²)`, `θ_H = 2`, `θ_L = 1`, `λ = 1/2`, `ū = -9/4`: the contract `w̄ = 0`,
`e_H = 4`, `e_L = 1` is optimal (`exercise_14_C_3a_suff`) and satisfies the first-order
conditions, as `exercise_14_C_3a_necessary` requires. -/
theorem exercise_14_C_3a_necessary_instance :
    (1 : ℝ) * Real.exp (-0) = 4 / 2 ^ 2 ∧ (1 : ℝ) * Real.exp (-0) = 1 / 1 ^ 2 := by
  have hconv : ∀ θ : ℝ, ConvexOn ℝ (Set.Ici 0) fun e : ℝ => e ^ 2 / (2 * θ ^ 2) := by
    intro θ
    have : (fun e : ℝ => e ^ 2 / (2 * θ ^ 2)) = fun e => (1 / (2 * θ ^ 2)) • e ^ 2 := by
      funext e; simp only [smul_eq_mul]; ring
    rw [this]
    exact (even_two.convexOn_pow.subset (Set.subset_univ _) (convex_Ici 0)).smul (by positivity)
  have hdg : ∀ θ e : ℝ, HasDerivAt (fun e : ℝ => e ^ 2 / (2 * θ ^ 2)) (e / θ ^ 2) e := by
    intro θ e
    have := (hasDerivAt_pow 2 e).div_const (2 * θ ^ 2)
    convert this using 1
    rcases eq_or_ne θ 0 with h | h
    · subst h; simp
    · field_simp; ring
  have hopt := fun (wH' eH' wL' eL' : ℝ) (h1 : (0 : ℝ) ≤ eH') (h2 : (0 : ℝ) ≤ eL')
      (h3 : -9 / 4 ≤ 1 / 2 * (-Real.exp (-wH') - eH' ^ 2 / (2 * 2 ^ 2)) +
        (1 - 1 / 2) * (-Real.exp (-wL') - eL' ^ 2 / (2 * 1 ^ 2))) =>
    exercise_14_C_3a_suff (v := fun w => -Real.exp (-w)) (dv := fun w => Real.exp (-w))
      (prof := id) (dprof := fun _ => 1) (g := fun e θ => e ^ 2 / (2 * θ ^ 2))
      (ge := fun e θ => e / θ ^ 2) (θL := 1) (θH := 2) (lam := 1 / 2) (ubar := -9 / 4)
      (wbar := 0) (eH := 4) (eL := 1) (by norm_num) (by norm_num)
      exA_strictConcave.concaveOn exA_hasDeriv (fun _ => Real.exp_pos _)
      (concaveOn_id (convex_Ici 0)) (fun e _ => (hasDerivAt_id e).hasDerivWithinAt) hconv
      (fun θ e _ => (hdg θ e).hasDerivWithinAt) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
  exact exercise_14_C_3a_necessary (v := fun w => -Real.exp (-w)) (dv := fun w => Real.exp (-w))
    (prof := id) (g := fun e θ => e ^ 2 / (2 * θ ^ 2)) (θL := 1) (θH := 2) (lam := 1 / 2)
    (ubar := -9 / 4) (wbar := 0) (by norm_num) (by norm_num) exA_hasDeriv
    (fun _ => Real.exp_pos _) (by norm_num) (by norm_num) (hasDerivAt_id 4) (hasDerivAt_id 1)
    (hdg 2 4) (hdg 1 1) (by norm_num) hopt

end MWG.PrincipalAgent

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Instances of the hypotheses of the main results

Proved concrete instances (non-vacuity checks) for results of MWG Chapter 14 whose hypotheses are
not already instantiated in `ExampleHA`, `ExampleHI` or the exercise modules.

* Section 14.B: `inst_footnote_8`, `inst_EW_gt` (Proposition 14.B.3), `inst_high_implementable`
  (Appendix A) in the examples of `ExampleHA`.
* Section 14.C: `inst_lemmas_14_C`, `inst_appendix_B_steps`, `inst_eL_falls` in `exB`.
* Exercises: `inst_14_B_3b`, `inst_14_B_3c` (`g(e) = e³/3`), `inst_14_AA_2`.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Footnote 8** in `exA`: the optimal scheme `exW` for `e_H` gives exactly `ū`. -/
theorem inst_footnote_8 : exA.EU true exW = exA.ubar :=
  HAModel.footnote_8 exA_standing exA_optimal

/-- **Proposition 14.B.3** in `exA`: the optimal scheme for `e_H` costs strictly more than the
observable-effort wage `-log (23/40)`. -/
theorem inst_EW_gt : exWstar true < exA.EW true exW :=
  HAModel.ha_EW_gt_of_IC exA_standing exA_strictConcave (by norm_num [exA, exModel])
    exA_optimal.1.1 (exA_optimal.1.2 false) (exA_wstar true)

/-- **Appendix A** ("`e_H` can be induced") in the risk-neutral example `exRN` (`v(w) = w` is
unbounded above). -/
theorem inst_high_implementable : ∃ w, exRN.HAFeasible true w := by
  have hst : exRN.Standing :=
    exA_standing_of (fun w => hasDerivAt_id w) (fun _ => one_pos) (concaveOn_id convex_univ) _ _
  exact HAModel.aa_high_implementable hst exA_two (exA_fosd _ _ _ _) fun y => ⟨y, le_refl _⟩

/-- **Lemmas 14.C.2-14.C.4** in `exB`: at the optimal contract `(i)` and `(iii)` bind, `e_H = e*_H`,
and `e_L < e*_L`. -/
theorem inst_lemmas_14_C :
    let K := exB.scr.bind 2 (1 / 2)
    (K.wL = exB.scr.c + exB.scr.g K.eL exB.scr.θL ∧
      K.wH = exB.scr.c + exB.scr.D K.eL + exB.scr.g K.eH exB.scr.θH) ∧
    (K.eL ≤ 1 ∧ K.eH = 2) ∧ K.eL < 1 := by
  intro K
  have hH := (HIModel.hi_fbH_of_foc exB_standing (by norm_num) exB_focH).2
  have hL := (HIModel.hi_fbL_of_foc exB_standing (by norm_num) exB_focL).2
  exact ⟨Screen.lemma_14_C_2 (HIModel.hi_hyp exB_standing) exB_opt,
    Screen.lemma_14_C_3 (HIModel.hi_hyp exB_standing) hH hL (by norm_num) exB_opt,
    HIModel.lemma_14_C_4 exB_standing (by norm_num) exB_focH (by norm_num) exB_focL exB_opt⟩

/-- **Appendix B, Steps 1-5** in `exB`, with the multipliers `γ = 1`, `φ_H = λ`, `φ_L = 0`. -/
theorem inst_appendix_B_steps :
    0 < exB.lam ∧ (exB.scr.bind 2 (1 / 2)).eL = 1 / 2 := by
  obtain ⟨h2, h3, h4, h5, cs1, cs3⟩ := HIModel.appendix_B_multipliers exB_standing (by norm_num)
    exB_focH (by norm_num) exB_focL exB_opt
  have := HIModel.appendix_B_steps exB_standing exB_opt.1 (γ := 1) (φH := exB.lam) (φL := 0)
    le_rfl h2 h3 (le_of_eq h4) (fun _ => h4) (by linarith [h5]) (fun _ => by linarith [h5])
    cs1 cs3 (by simp)
  exact ⟨this.1, rfl⟩

/-- **p. 499** ("`e_L` falls as `λ/(1 - λ)` rises") in `exB`: for `λ = 5/7` the optimal `e_L` is
`1/2`, for `λ = 81/91` it is `1/4`. -/
theorem inst_eL_falls : (1 / 4 : ℝ) < 1 / 2 := by
  have hSL : ∀ e, exB.scr.SL e = Real.log (1 + e) - e ^ 2 / 4 := fun e => by
    change Real.log (1 + e) - e ^ 2 * Real.exp (-exB.θL) / 2 = _
    rw [exB_expL]; ring
  have hD : ∀ e, exB.scr.D e = e ^ 2 / 6 := fun e => by
    change e ^ 2 * Real.exp (-exB.θL) / 2 - e ^ 2 * Real.exp (-exB.θH) / 2 = _
    rw [exB_expL, exB_expH]; ring
  refine HIModel.hi_eL_falls exB_standing (l1 := 5 / 7) (l2 := 81 / 91) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun e he => ?_) (fun e he => ?_)
  · rw [hSL, hSL, hD, hD]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (2 * e - 1)]
  · rw [hSL, hSL, hD, hD]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (5 / 4) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (4 * e - 1)]

/-- **Exercise 14.B.3(b)**, an instance: `g(e) = e³/3` (`g'(0) = 0`, `g', g'', g''' > 0` for
`e > 0`), `e* = 1`, `φσ² = 3/2`, `ū = 0`: the contract `e = 1`, `α = 1/3`, `β = 0` earns `2/3`. -/
theorem inst_14_B_3b {e α β : ℝ} (he : 0 ≤ e)
    (hpart : 0 ≤ α + β * e - 3 / 2 * β ^ 2 - e ^ 3 / 3) :
    e - (α + β * e) ≤ 1 - 1 ^ 3 / 3 - 0 := by
  have hconv : ConvexOn ℝ (Ici 0) fun e : ℝ => e ^ 3 / 3 := by
    have := (convexOn_pow 3).smul (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    refine this.congr fun x _ => ?_
    simp only [smul_eq_mul]; ring
  refine (exercise_14_B_3b (g := fun e => e ^ 3 / 3) (dg := fun e => e ^ 2) hconv
    (fun e _ => ?_) (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num) (by norm_num) he hpart).1
  have := ((hasDerivAt_pow 3 e).div_const 3).hasDerivWithinAt (s := Ici 0)
  convert this using 1; push_cast; ring

/-- **Exercise 14.B.3(c)**, an instance: `g(e) = e³/3`, `φσ² = 3/2`: `e = 1/2` maximizes
`e - g(e) - φσ² g'(e)²`, and `β = g'(1/2) = 1/4 = 1/(1 + 2φσ² g''(1/2))`. -/
theorem inst_14_B_3c : (fun e : ℝ => e ^ 2) (1 / 2) = 1 / (1 + 2 * (3 / 2) * (2 * (1 / 2))) ∧
    0 < (fun e : ℝ => e ^ 2) (1 / 2) ∧ (fun e : ℝ => e ^ 2) (1 / 2) < 1 := by
  refine exercise_14_B_3c_beta (g := fun e => e ^ 3 / 3) (dg := fun e => e ^ 2)
    (d2g := fun e => 2 * e) (ubar := 0) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_
  · have := (hasDerivAt_pow 3 (1 / 2 : ℝ)).div_const 3
    convert this using 1; push_cast; ring
  · have := hasDerivAt_pow 2 (1 / 2 : ℝ)
    convert this using 1; push_cast; ring
  · intro e he
    nlinarith [sq_nonneg (e - 1 / 2), mul_nonneg he (sq_nonneg (e - 1 / 2)),
      mul_nonneg (mul_nonneg he he) (sq_nonneg (e - 1 / 2))]

/-- **Exercise 14.AA.2**, an instance: `f(π_H|e) = (1 + e)/3` on `[0, 1]`, `g(e) = e²/2`,
`v_L = 0`, `v_H = 3/2`: the first-order condition holds at `e = 1/2`, which maximizes
`v_L + f(π_H|e)(v_H - v_L) - g(e)`. -/
theorem inst_14_AA_2 : ∀ e' ∈ Icc (0 : ℝ) 1,
    0 + (1 + e') / 3 * (3 / 2 - 0) - e' ^ 2 / 2 ≤
      0 + (1 + 1 / 2) / 3 * (3 / 2 - 0) - (1 / 2) ^ 2 / 2 := by
  refine exercise_14_AA_2_valid (p := fun e => (1 + e) / 3) (dp := fun _ => 1 / 3)
    (g := fun e => e ^ 2 / 2) (dg := fun e => e) ?_ ?_ (fun e _ => ?_) (fun e _ => ?_)
    (by norm_num) (by norm_num) (by norm_num)
  · refine ⟨convex_Icc 0 1, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul]
    linarith
  · have := (convexOn_pow 2).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine (this.subset (Icc_subset_Ici_self) (convex_Icc 0 1)).congr fun x _ => ?_
    simp only [smul_eq_mul]; ring
  · exact (((hasDerivAt_id e).const_add 1).div_const 3).hasDerivWithinAt
  · have := ((hasDerivAt_pow 2 e).div_const 2).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; push_cast; ring

end MWG.PrincipalAgent

set_option linter.style.longLine false
#print axioms MWG.PrincipalAgent.tpa_tangent_le
#print axioms MWG.PrincipalAgent.tpa_tangent_lt
#print axioms MWG.PrincipalAgent.tpa_tangent_ge_convex
#print axioms MWG.PrincipalAgent.tpa_tangent_gt_convex
#print axioms MWG.PrincipalAgent.tpa_tangent_integrable
#print axioms MWG.PrincipalAgent.tpa_tangent_integral
#print axioms MWG.PrincipalAgent.tpa_jensen
#print axioms MWG.PrincipalAgent.tpa_jensen_eq
#print axioms MWG.PrincipalAgent.tpa_jensen_two
#print axioms MWG.PrincipalAgent.tpa_jensen_two_lt
#print axioms MWG.PrincipalAgent.kt_sign
#print axioms MWG.PrincipalAgent.kt_le
#print axioms MWG.PrincipalAgent.kt_convexlike
#print axioms MWG.PrincipalAgent.kt_convexlike_eq
#print axioms MWG.PrincipalAgent.HAModel
#print axioms MWG.PrincipalAgent.HAModel.mk
#print axioms MWG.PrincipalAgent.HAModel.ν
#print axioms MWG.PrincipalAgent.HAModel.f
#print axioms MWG.PrincipalAgent.HAModel.v
#print axioms MWG.PrincipalAgent.HAModel.dv
#print axioms MWG.PrincipalAgent.HAModel.g
#print axioms MWG.PrincipalAgent.HAModel.ubar
#print axioms MWG.PrincipalAgent.HAModel.Standing
#print axioms MWG.PrincipalAgent.HAModel.Standing.mk
#print axioms MWG.PrincipalAgent.HAModel.Standing.f_meas
#print axioms MWG.PrincipalAgent.HAModel.Standing.f_pos
#print axioms MWG.PrincipalAgent.HAModel.Standing.f_int
#print axioms MWG.PrincipalAgent.HAModel.Standing.f_one
#print axioms MWG.PrincipalAgent.HAModel.Standing.x_int
#print axioms MWG.PrincipalAgent.HAModel.Standing.v_deriv
#print axioms MWG.PrincipalAgent.HAModel.Standing.dv_pos
#print axioms MWG.PrincipalAgent.HAModel.Standing.v_conc
#print axioms MWG.PrincipalAgent.HAModel.Adm
#print axioms MWG.PrincipalAgent.HAModel.EW
#print axioms MWG.PrincipalAgent.HAModel.EV
#print axioms MWG.PrincipalAgent.HAModel.EU
#print axioms MWG.PrincipalAgent.HAModel.GP
#print axioms MWG.PrincipalAgent.HAModel.OP
#print axioms MWG.PrincipalAgent.HAModel.ObsFeasible
#print axioms MWG.PrincipalAgent.HAModel.IsObsOptimal
#print axioms MWG.PrincipalAgent.HAModel.IsCostMin
#print axioms MWG.PrincipalAgent.HAModel.IC
#print axioms MWG.PrincipalAgent.HAModel.HAFeasible
#print axioms MWG.PrincipalAgent.HAModel.IsHACostMin
#print axioms MWG.PrincipalAgent.HAModel.IsHAOptimal
#print axioms MWG.PrincipalAgent.HAModel.ha_OP_eq
#print axioms MWG.PrincipalAgent.HAModel.ha_const_adm
#print axioms MWG.PrincipalAgent.HAModel.ha_EW_const
#print axioms MWG.PrincipalAgent.HAModel.ha_EV_const
#print axioms MWG.PrincipalAgent.HAModel.ha_v_strictMono
#print axioms MWG.PrincipalAgent.HAModel.ha_EV_le
#print axioms MWG.PrincipalAgent.HAModel.ha_cost_lower_bound
#print axioms MWG.PrincipalAgent.HAModel.ha_fixed_wage_feasible
#print axioms MWG.PrincipalAgent.HAModel.ha_fixed_wage_costMin
#print axioms MWG.PrincipalAgent.HAModel.ha_costMin_binds
#print axioms MWG.PrincipalAgent.HAModel.ha_costMin_unique
#print axioms MWG.PrincipalAgent.HAModel.ha_foc_constant
#print axioms MWG.PrincipalAgent.HAModel.ha_riskNeutral_costMin
#print axioms MWG.PrincipalAgent.HAModel.ha_wage_higher
#print axioms MWG.PrincipalAgent.HAModel.proposition_14_B_1
#print axioms MWG.PrincipalAgent.HAModel.proposition_14_B_1_unique
#print axioms MWG.PrincipalAgent.HAModel.ha_value_le_obs
#print axioms MWG.PrincipalAgent.HAModel.proposition_14_B_2
#print axioms MWG.PrincipalAgent.HAModel.proposition_14_B_2_every
#print axioms MWG.PrincipalAgent.HAModel.F
#print axioms MWG.PrincipalAgent.HAModel.FOSD
#print axioms MWG.PrincipalAgent.HAModel.ha_IC_two
#print axioms MWG.PrincipalAgent.HAModel.ha_implement_low
#print axioms MWG.PrincipalAgent.HAModel.ha_EV_sub
#print axioms MWG.PrincipalAgent.HAModel.ha_kt_sufficient
#print axioms MWG.PrincipalAgent.HAModel.ha_fosd_set
#print axioms MWG.PrincipalAgent.HAModel.ha_nu_ne_zero
#print axioms MWG.PrincipalAgent.HAModel.lemma_14_B_1
#print axioms MWG.PrincipalAgent.HAModel.ha_dv_anti
#print axioms MWG.PrincipalAgent.HAModel.ha_v_hits
#print axioms MWG.PrincipalAgent.HAModel.shift
#print axioms MWG.PrincipalAgent.HAModel.ha_shift_spec
#print axioms MWG.PrincipalAgent.HAModel.ha_shift
#print axioms MWG.PrincipalAgent.HAModel.footnote_8
#print axioms MWG.PrincipalAgent.HAModel.ha_optimal_binds
#print axioms MWG.PrincipalAgent.HAModel.footnote_9
#print axioms MWG.PrincipalAgent.HAModel.ha_wage_vs_what
#print axioms MWG.PrincipalAgent.HAModel.ha_monotone_iff_mlrp
#print axioms MWG.PrincipalAgent.HAModel.ha_EW_gt_of_IC
#print axioms MWG.PrincipalAgent.HAModel.proposition_14_B_3
#print axioms MWG.PrincipalAgent.HAModel.ha_welfare_loss
#print axioms MWG.PrincipalAgent.HAModel.ha_no_loss_of_tie
#print axioms MWG.PrincipalAgent.HAModel.ha_no_upward_distortion
#print axioms MWG.PrincipalAgent.dmeas
#print axioms MWG.PrincipalAgent.dmeas_integrable
#print axioms MWG.PrincipalAgent.dmeas_integral
#print axioms MWG.PrincipalAgent.dmeas_setIntegral
#print axioms MWG.PrincipalAgent.dmeas_ae
#print axioms MWG.PrincipalAgent.exPts
#print axioms MWG.PrincipalAgent.exF
#print axioms MWG.PrincipalAgent.exModel
#print axioms MWG.PrincipalAgent.exA_integral
#print axioms MWG.PrincipalAgent.exA_standing_of
#print axioms MWG.PrincipalAgent.exA_hasDeriv
#print axioms MWG.PrincipalAgent.exA_strictConcave
#print axioms MWG.PrincipalAgent.exA
#print axioms MWG.PrincipalAgent.exA_standing
#print axioms MWG.PrincipalAgent.exA_dv_anti
#print axioms MWG.PrincipalAgent.exA_two
#print axioms MWG.PrincipalAgent.exA_fosd
#print axioms MWG.PrincipalAgent.exA_not_mlrp
#print axioms MWG.PrincipalAgent.exW
#print axioms MWG.PrincipalAgent.exW_adm
#print axioms MWG.PrincipalAgent.exW_zero
#print axioms MWG.PrincipalAgent.exW_one
#print axioms MWG.PrincipalAgent.exW_two
#print axioms MWG.PrincipalAgent.exA_EU
#print axioms MWG.PrincipalAgent.exA_foc
#print axioms MWG.PrincipalAgent.exA_optimal
#print axioms MWG.PrincipalAgent.exA_not_monotone
#print axioms MWG.PrincipalAgent.exA_lemma_14_B_1
#print axioms MWG.PrincipalAgent.exWstar
#print axioms MWG.PrincipalAgent.exA_wstar
#print axioms MWG.PrincipalAgent.exA_GP
#print axioms MWG.PrincipalAgent.exA_fb_strict
#print axioms MWG.PrincipalAgent.exA_proposition_14_B_1
#print axioms MWG.PrincipalAgent.exA_welfare_loss
#print axioms MWG.PrincipalAgent.exTie
#print axioms MWG.PrincipalAgent.exA_tie
#print axioms MWG.PrincipalAgent.exRN
#print axioms MWG.PrincipalAgent.exA_proposition_14_B_2
#print axioms MWG.PrincipalAgent.signal_ratio_indep
#print axioms MWG.PrincipalAgent.signal_ratio_suffstat
#print axioms MWG.PrincipalAgent.signal_foc_indep
#print axioms MWG.PrincipalAgent.signal_depends
#print axioms MWG.PrincipalAgent.signal_jensen
#print axioms MWG.PrincipalAgent.signal_same_utility
#print axioms MWG.PrincipalAgent.signal_lower_cost
#print axioms MWG.PrincipalAgent.HAModel.aa_IC_iff
#print axioms MWG.PrincipalAgent.HAModel.aa_not_implementable
#print axioms MWG.PrincipalAgent.HAModel.twoVal
#print axioms MWG.PrincipalAgent.HAModel.aa_high_implementable
#print axioms MWG.PrincipalAgent.exC
#print axioms MWG.PrincipalAgent.aa_high_not_implementable
#print axioms MWG.PrincipalAgent.foa_sufficient
#print axioms MWG.PrincipalAgent.foa_fails
#print axioms MWG.PrincipalAgent.Screen
#print axioms MWG.PrincipalAgent.Screen.mk
#print axioms MWG.PrincipalAgent.Screen.pH
#print axioms MWG.PrincipalAgent.Screen.pL
#print axioms MWG.PrincipalAgent.Screen.g
#print axioms MWG.PrincipalAgent.Screen.θL
#print axioms MWG.PrincipalAgent.Screen.θH
#print axioms MWG.PrincipalAgent.Screen.lam
#print axioms MWG.PrincipalAgent.Screen.c
#print axioms MWG.PrincipalAgent.HIContract
#print axioms MWG.PrincipalAgent.HIContract.mk
#print axioms MWG.PrincipalAgent.HIContract.wH
#print axioms MWG.PrincipalAgent.HIContract.eH
#print axioms MWG.PrincipalAgent.HIContract.wL
#print axioms MWG.PrincipalAgent.HIContract.eL
#print axioms MWG.PrincipalAgent.Screen.Pi
#print axioms MWG.PrincipalAgent.Screen.C1
#print axioms MWG.PrincipalAgent.Screen.C2
#print axioms MWG.PrincipalAgent.Screen.C3
#print axioms MWG.PrincipalAgent.Screen.C4
#print axioms MWG.PrincipalAgent.Screen.Feas
#print axioms MWG.PrincipalAgent.Screen.Feas3
#print axioms MWG.PrincipalAgent.Screen.FeasRelax
#print axioms MWG.PrincipalAgent.Screen.IsOpt
#print axioms MWG.PrincipalAgent.Screen.IsOptRelax
#print axioms MWG.PrincipalAgent.Screen.D
#print axioms MWG.PrincipalAgent.Screen.SH
#print axioms MWG.PrincipalAgent.Screen.SL
#print axioms MWG.PrincipalAgent.Screen.Q
#print axioms MWG.PrincipalAgent.Screen.R
#print axioms MWG.PrincipalAgent.Screen.bind
#print axioms MWG.PrincipalAgent.Screen.Hyp
#print axioms MWG.PrincipalAgent.Screen.Hyp.mk
#print axioms MWG.PrincipalAgent.Screen.Hyp.lam_pos
#print axioms MWG.PrincipalAgent.Screen.Hyp.lam_lt
#print axioms MWG.PrincipalAgent.Screen.Hyp.D_zero
#print axioms MWG.PrincipalAgent.Screen.Hyp.D_mono
#print axioms MWG.PrincipalAgent.Screen.screen_D_pos
#print axioms MWG.PrincipalAgent.Screen.screen_D_nonneg
#print axioms MWG.PrincipalAgent.Screen.lemma_14_C_1
#print axioms MWG.PrincipalAgent.Screen.screen_eL_le_eH
#print axioms MWG.PrincipalAgent.Screen.screen_Pi_le
#print axioms MWG.PrincipalAgent.Screen.screen_Pi_eq_iff
#print axioms MWG.PrincipalAgent.Screen.screen_Pi_bind
#print axioms MWG.PrincipalAgent.Screen.screen_bind_feas
#print axioms MWG.PrincipalAgent.Screen.lemma_14_C_2
#print axioms MWG.PrincipalAgent.Screen.IsFB
#print axioms MWG.PrincipalAgent.Screen.screen_Q_min
#print axioms MWG.PrincipalAgent.Screen.lemma_14_C_3
#print axioms MWG.PrincipalAgent.Screen.screen_opt_iff
#print axioms MWG.PrincipalAgent.Screen.screen_iv_slack
#print axioms MWG.PrincipalAgent.Screen.screen_H_rent
#print axioms MWG.PrincipalAgent.Screen.FBval
#print axioms MWG.PrincipalAgent.Screen.screen_loss
#print axioms MWG.PrincipalAgent.Screen.screen_fb_violates_iii
#print axioms MWG.PrincipalAgent.Screen.exercise_14_BB_1
#print axioms MWG.PrincipalAgent.hi_exists_gt_of_deriv_pos
#print axioms MWG.PrincipalAgent.hi_deriv_anti
#print axioms MWG.PrincipalAgent.hi_deriv_mono
#print axioms MWG.PrincipalAgent.hi_g_theta_inconsistent
#print axioms MWG.PrincipalAgent.hi_cross_of_deriv
#print axioms MWG.PrincipalAgent.HIModel
#print axioms MWG.PrincipalAgent.HIModel.mk
#print axioms MWG.PrincipalAgent.HIModel.pH
#print axioms MWG.PrincipalAgent.HIModel.pL
#print axioms MWG.PrincipalAgent.HIModel.dpH
#print axioms MWG.PrincipalAgent.HIModel.dpL
#print axioms MWG.PrincipalAgent.HIModel.g
#print axioms MWG.PrincipalAgent.HIModel.ge
#print axioms MWG.PrincipalAgent.HIModel.v
#print axioms MWG.PrincipalAgent.HIModel.dv
#print axioms MWG.PrincipalAgent.HIModel.θL
#print axioms MWG.PrincipalAgent.HIModel.θH
#print axioms MWG.PrincipalAgent.HIModel.lam
#print axioms MWG.PrincipalAgent.HIModel.ubar
#print axioms MWG.PrincipalAgent.HIModel.c
#print axioms MWG.PrincipalAgent.HIModel.Standing
#print axioms MWG.PrincipalAgent.HIModel.Standing.mk
#print axioms MWG.PrincipalAgent.HIModel.Standing.pH_zero
#print axioms MWG.PrincipalAgent.HIModel.Standing.pL_zero
#print axioms MWG.PrincipalAgent.HIModel.Standing.pH_deriv
#print axioms MWG.PrincipalAgent.HIModel.Standing.pL_deriv
#print axioms MWG.PrincipalAgent.HIModel.Standing.dpL_pos
#print axioms MWG.PrincipalAgent.HIModel.Standing.dp_le
#print axioms MWG.PrincipalAgent.HIModel.Standing.pH_conc
#print axioms MWG.PrincipalAgent.HIModel.Standing.pL_conc
#print axioms MWG.PrincipalAgent.HIModel.Standing.g_zero
#print axioms MWG.PrincipalAgent.HIModel.Standing.g_deriv
#print axioms MWG.PrincipalAgent.HIModel.Standing.ge_zero
#print axioms MWG.PrincipalAgent.HIModel.Standing.g_conv
#print axioms MWG.PrincipalAgent.HIModel.Standing.θ_lt
#print axioms MWG.PrincipalAgent.HIModel.Standing.ge_cross
#print axioms MWG.PrincipalAgent.HIModel.Standing.lam_pos
#print axioms MWG.PrincipalAgent.HIModel.Standing.lam_lt
#print axioms MWG.PrincipalAgent.HIModel.Standing.v_deriv
#print axioms MWG.PrincipalAgent.HIModel.Standing.dv_pos
#print axioms MWG.PrincipalAgent.HIModel.Standing.v_conc
#print axioms MWG.PrincipalAgent.HIModel.Standing.v_c
#print axioms MWG.PrincipalAgent.HIModel.scr
#print axioms MWG.PrincipalAgent.HIModel.hi_v_strictMono
#print axioms MWG.PrincipalAgent.HIModel.hi_D_deriv
#print axioms MWG.PrincipalAgent.HIModel.hi_hyp
#print axioms MWG.PrincipalAgent.HIModel.hi_SH_conc
#print axioms MWG.PrincipalAgent.HIModel.hi_SL_conc
#print axioms MWG.PrincipalAgent.HIModel.hi_SH_deriv
#print axioms MWG.PrincipalAgent.HIModel.hi_SL_deriv
#print axioms MWG.PrincipalAgent.HIModel.hi_isFB_of_crit
#print axioms MWG.PrincipalAgent.HIModel.hi_fbH_of_foc
#print axioms MWG.PrincipalAgent.HIModel.hi_fbL_of_foc
#print axioms MWG.PrincipalAgent.HIModel.hi_fb_order
#print axioms MWG.PrincipalAgent.HIModel.ObsFeas
#print axioms MWG.PrincipalAgent.HIModel.IsObsOpt
#print axioms MWG.PrincipalAgent.HIModel.fbK
#print axioms MWG.PrincipalAgent.HIModel.proposition_14_C_1
#print axioms MWG.PrincipalAgent.HIModel.hi_obs_foc
#print axioms MWG.PrincipalAgent.HIModel.hi_isoprofit_axis
#print axioms MWG.PrincipalAgent.HIModel.hi_H_prefers_L
#print axioms MWG.PrincipalAgent.HIModel.hi_Q_deriv
#print axioms MWG.PrincipalAgent.HIModel.hi_eL_pos
#print axioms MWG.PrincipalAgent.HIModel.hi_Q_crit
#print axioms MWG.PrincipalAgent.HIModel.hi_foc_14_C_9
#print axioms MWG.PrincipalAgent.HIModel.lemma_14_C_4
#print axioms MWG.PrincipalAgent.HIModel.hi_14_C_9_terms
#print axioms MWG.PrincipalAgent.HIModel.proposition_14_C_3
#print axioms MWG.PrincipalAgent.HIModel.hi_eL_falls
#print axioms MWG.PrincipalAgent.HIModel.footnote_17
#print axioms MWG.PrincipalAgent.HIModel.appendix_B_steps
#print axioms MWG.PrincipalAgent.HIModel.appendix_B_multipliers
#print axioms MWG.PrincipalAgent.exB_g_conv
#print axioms MWG.PrincipalAgent.exB_log_deriv
#print axioms MWG.PrincipalAgent.exB_log_conc
#print axioms MWG.PrincipalAgent.exB
#print axioms MWG.PrincipalAgent.exB_expL
#print axioms MWG.PrincipalAgent.exB_expH
#print axioms MWG.PrincipalAgent.exB_standing
#print axioms MWG.PrincipalAgent.exB_focH
#print axioms MWG.PrincipalAgent.exB_focL
#print axioms MWG.PrincipalAgent.exB_Q
#print axioms MWG.PrincipalAgent.exB_Q_max
#print axioms MWG.PrincipalAgent.exB_opt
#print axioms MWG.PrincipalAgent.exB_proposition_14_C_3
#print axioms MWG.PrincipalAgent.exB_proposition_14_C_1
#print axioms MWG.PrincipalAgent.ceRho
#print axioms MWG.PrincipalAgent.footnote_15_order
#print axioms MWG.PrincipalAgent.footnote_15
#print axioms MWG.PrincipalAgent.ceRho_ge_min
#print axioms MWG.PrincipalAgent.footnote_15_accept
#print axioms MWG.PrincipalAgent.footnote_15_reject
#print axioms MWG.PrincipalAgent.infinite_ra_insure
#print axioms MWG.PrincipalAgent.proposition_14_C_2
#print axioms MWG.PrincipalAgent.proposition_14_C_2_payoff
#print axioms MWG.PrincipalAgent.revelation_example
#print axioms MWG.PrincipalAgent.hybrid_revelation
#print axioms MWG.PrincipalAgent.hybrid_forcing
#print axioms MWG.PrincipalAgent.hybrid_change_of_variables
#print axioms MWG.PrincipalAgent.footnote_21_misprint
#print axioms MWG.PrincipalAgent.footnote_21_corrected
#print axioms MWG.PrincipalAgent.footnote_21_limit
#print axioms MWG.PrincipalAgent.maskin_riley
#print axioms MWG.PrincipalAgent.baron_myerson
#print axioms MWG.PrincipalAgent.exercise_14_C_2
#print axioms MWG.PrincipalAgent.exercise_14_C_3a
#print axioms MWG.PrincipalAgent.exercise_14_C_3a_suff
#print axioms MWG.PrincipalAgent.exercise_14_C_3b
#print axioms MWG.PrincipalAgent.exercise_14_C_3b_order
#print axioms MWG.PrincipalAgent.screen_relax_opt
#print axioms MWG.PrincipalAgent.exRev
#print axioms MWG.PrincipalAgent.exercise_14_C_5_reversal
#print axioms MWG.PrincipalAgent.monopsony
#print axioms MWG.PrincipalAgent.monopsony_hyp
#print axioms MWG.PrincipalAgent.exercise_14_C_6
#print axioms MWG.PrincipalAgent.exercise_14_C_6_instance
#print axioms MWG.PrincipalAgent.aa_neBot
#print axioms MWG.PrincipalAgent.aa_mono_iff
#print axioms MWG.PrincipalAgent.aa_ratio_log
#print axioms MWG.PrincipalAgent.aa_G_deriv
#print axioms MWG.PrincipalAgent.exercise_14_AA_1
#print axioms MWG.PrincipalAgent.exercise_14_AA_1_strict
#print axioms MWG.PrincipalAgent.exercise_14_AA_1_strict_false
#print axioms MWG.PrincipalAgent.exercise_14_AA_2_valid
#print axioms MWG.PrincipalAgent.exercise_14_AA_2_contract
#print axioms MWG.PrincipalAgent.b4EU
#print axioms MWG.PrincipalAgent.b4Profit
#print axioms MWG.PrincipalAgent.b4Obs
#print axioms MWG.PrincipalAgent.b4Impl
#print axioms MWG.PrincipalAgent.b4p
#print axioms MWG.PrincipalAgent.b4g
#print axioms MWG.PrincipalAgent.b4_jensen
#print axioms MWG.PrincipalAgent.b4_obs_bound
#print axioms MWG.PrincipalAgent.exercise_14_B_4a
#print axioms MWG.PrincipalAgent.exercise_14_B_4b
#print axioms MWG.PrincipalAgent.exercise_14_B_4b_threshold
#print axioms MWG.PrincipalAgent.exercise_14_B_4c
#print axioms MWG.PrincipalAgent.b4pd
#print axioms MWG.PrincipalAgent.b4gd
#print axioms MWG.PrincipalAgent.b4_sqrt8
#print axioms MWG.PrincipalAgent.exercise_14_B_4d_obs
#print axioms MWG.PrincipalAgent.exercise_14_B_4d_unobs
#print axioms MWG.PrincipalAgent.HAModel.exercise_14_B_2
#print axioms MWG.PrincipalAgent.exercise_14_B_3a
#print axioms MWG.PrincipalAgent.exercise_14_B_3b
#print axioms MWG.PrincipalAgent.exercise_14_B_3c
#print axioms MWG.PrincipalAgent.exercise_14_B_3c_beta
#print axioms MWG.PrincipalAgent.exercise_14_B_3c_sigma
#print axioms MWG.PrincipalAgent.HAModel.ha_piece_integral
#print axioms MWG.PrincipalAgent.HAModel.ha_piece_adm
#print axioms MWG.PrincipalAgent.HAModel.ha_mix
#print axioms MWG.PrincipalAgent.HAModel.ha_EV_mix
#print axioms MWG.PrincipalAgent.HAModel.ha_setIntegral_pos
#print axioms MWG.PrincipalAgent.HAModel.ha_raise
#print axioms MWG.PrincipalAgent.HAModel.ha_slater
#print axioms MWG.PrincipalAgent.HAModel.ha_ae_min
#print axioms MWG.PrincipalAgent.HAModel.ha_kt_general
#print axioms MWG.PrincipalAgent.HAModel.ha_kt_necessary
#print axioms MWG.PrincipalAgent.HAModel.lemma_14_B_1_every
#print axioms MWG.PrincipalAgent.HAModel.exercise_14_B_2_necessary
#print axioms MWG.PrincipalAgent.HAModel.foa_necessary
#print axioms MWG.PrincipalAgent.inst_kt_necessary
#print axioms MWG.PrincipalAgent.inst_14_B_2_necessary
#print axioms MWG.PrincipalAgent.exFOA
#print axioms MWG.PrincipalAgent.exWf
#print axioms MWG.PrincipalAgent.inst_foa_necessary
#print axioms MWG.PrincipalAgent.effw
#print axioms MWG.PrincipalAgent.effw_ge
#print axioms MWG.PrincipalAgent.effw_le_iff
#print axioms MWG.PrincipalAgent.effw_exists
#print axioms MWG.PrincipalAgent.effw_mono
#print axioms MWG.PrincipalAgent.effw_of_mono
#print axioms MWG.PrincipalAgent.effw_idem
#print axioms MWG.PrincipalAgent.IsDisp
#print axioms MWG.PrincipalAgent.exercise_14_B_5
#print axioms MWG.PrincipalAgent.exercise_14_B_6a
#print axioms MWG.PrincipalAgent.exercise_14_B_6b
#print axioms MWG.PrincipalAgent.mlrp_expect_mono
#print axioms MWG.PrincipalAgent.exercise_14_B_6c
#print axioms MWG.PrincipalAgent.exercise_14_B_6b_opt
#print axioms MWG.PrincipalAgent.exercise_14_B_6b_instance
#print axioms MWG.PrincipalAgent.C8Feas
#print axioms MWG.PrincipalAgent.C8Profit
#print axioms MWG.PrincipalAgent.C8Opt
#print axioms MWG.PrincipalAgent.exercise_14_C_8_IRB
#print axioms MWG.PrincipalAgent.exercise_14_C_8b
#print axioms MWG.PrincipalAgent.exercise_14_C_8c
#print axioms MWG.PrincipalAgent.exercise_14_C_8d_feas
#print axioms MWG.PrincipalAgent.exercise_14_C_8d_bound
#print axioms MWG.PrincipalAgent.exercise_14_C_8d
#print axioms MWG.PrincipalAgent.exercise_14_C_8e
#print axioms MWG.PrincipalAgent.exercise_14_C_9a
#print axioms MWG.PrincipalAgent.c9Profit
#print axioms MWG.PrincipalAgent.exercise_14_C_9b
#print axioms MWG.PrincipalAgent.exercise_14_C_9b_shape
#print axioms MWG.PrincipalAgent.exercise_14_C_9b_rationed
#print axioms MWG.PrincipalAgent.exercise_14_C_9b_instance
#print axioms MWG.PrincipalAgent.kt_foc_1d
#print axioms MWG.PrincipalAgent.c9_r_order
#print axioms MWG.PrincipalAgent.exercise_14_C_9b_necessary
#print axioms MWG.PrincipalAgent.exercise_14_C_9b_necessary_instance
#print axioms MWG.PrincipalAgent.c7v
#print axioms MWG.PrincipalAgent.c7_demand
#print axioms MWG.PrincipalAgent.c7_surplus
#print axioms MWG.PrincipalAgent.c7D
#print axioms MWG.PrincipalAgent.c7Pi
#print axioms MWG.PrincipalAgent.c7_one_type
#print axioms MWG.PrincipalAgent.c7_bound_high
#print axioms MWG.PrincipalAgent.exercise_14_C_7a_theta
#print axioms MWG.PrincipalAgent.exercise_14_C_7a_lambda
#print axioms MWG.PrincipalAgent.exercise_14_C_7a_price
#print axioms MWG.PrincipalAgent.exercise_14_C_7b
#print axioms MWG.PrincipalAgent.exercise_14_C_7c
#print axioms MWG.PrincipalAgent.C7Feas
#print axioms MWG.PrincipalAgent.c7Profit
#print axioms MWG.PrincipalAgent.exercise_14_C_7d
#print axioms MWG.PrincipalAgent.exercise_14_C_7d_compare
#print axioms MWG.PrincipalAgent.b1c
#print axioms MWG.PrincipalAgent.b1dc
#print axioms MWG.PrincipalAgent.b1_rpow32
#print axioms MWG.PrincipalAgent.b1_rpow12
#print axioms MWG.PrincipalAgent.b1c_eq
#print axioms MWG.PrincipalAgent.b1_c_deriv
#print axioms MWG.PrincipalAgent.b1_c_ge
#print axioms MWG.PrincipalAgent.b1_uH_lt
#print axioms MWG.PrincipalAgent.b1_uw_pos
#print axioms MWG.PrincipalAgent.b1_c_convex
#print axioms MWG.PrincipalAgent.b1_c_tangent
#print axioms MWG.PrincipalAgent.b1_c_half
#print axioms MWG.PrincipalAgent.b1_c_threehalf
#print axioms MWG.PrincipalAgent.exercise_14_B_1
#print axioms MWG.PrincipalAgent.C1IC
#print axioms MWG.PrincipalAgent.exercise_14_C_1_mono
#print axioms MWG.PrincipalAgent.exercise_14_C_1_IR
#print axioms MWG.PrincipalAgent.c1D
#print axioms MWG.PrincipalAgent.exercise_14_C_1_rent
#print axioms MWG.PrincipalAgent.exercise_14_C_1_bound
#print axioms MWG.PrincipalAgent.exercise_14_C_1_local
#print axioms MWG.PrincipalAgent.C1Feas
#print axioms MWG.PrincipalAgent.c1Prof
#print axioms MWG.PrincipalAgent.c1Rent
#print axioms MWG.PrincipalAgent.c1Wage
#print axioms MWG.PrincipalAgent.c1VS
#print axioms MWG.PrincipalAgent.c1_D_mono
#print axioms MWG.PrincipalAgent.c1_D_nonneg
#print axioms MWG.PrincipalAgent.c1_rent_le
#print axioms MWG.PrincipalAgent.c1_prof_le_VS
#print axioms MWG.PrincipalAgent.c1Ext
#print axioms MWG.PrincipalAgent.c1_wage_feasible
#print axioms MWG.PrincipalAgent.c1_prof_wage
#print axioms MWG.PrincipalAgent.c1_VS_ext
#print axioms MWG.PrincipalAgent.exercise_14_C_1_opt
#print axioms MWG.PrincipalAgent.exercise_14_C_1_suff
#print axioms MWG.PrincipalAgent.exercise_14_C_1_distortion
#print axioms MWG.PrincipalAgent.exercise_14_C_1_instance
#print axioms MWG.PrincipalAgent.C4Feas
#print axioms MWG.PrincipalAgent.c4Prof
#print axioms MWG.PrincipalAgent.c4_mk
#print axioms MWG.PrincipalAgent.c4_prof_mk
#print axioms MWG.PrincipalAgent.c4_dv_lt
#print axioms MWG.PrincipalAgent.c4_spread
#print axioms MWG.PrincipalAgent.c4_part
#print axioms MWG.PrincipalAgent.exercise_14_C_4
#print axioms MWG.PrincipalAgent.c4_left_gt
#print axioms MWG.PrincipalAgent.exercise_14_C_4_strict
#print axioms MWG.PrincipalAgent.c4_exp_bound
#print axioms MWG.PrincipalAgent.c4κ
#print axioms MWG.PrincipalAgent.c4a
#print axioms MWG.PrincipalAgent.c4g
#print axioms MWG.PrincipalAgent.c4wH
#print axioms MWG.PrincipalAgent.c4wL
#print axioms MWG.PrincipalAgent.exercise_14_C_4_instance
#print axioms MWG.PrincipalAgent.exercise_14_C_4_instance_applied
#print axioms MWG.PrincipalAgent.c1_VS_update
#print axioms MWG.PrincipalAgent.exercise_14_C_1_strict
#print axioms MWG.PrincipalAgent.exercise_14_C_1_strict_instance
#print axioms MWG.PrincipalAgent.b7U
#print axioms MWG.PrincipalAgent.B7Feas
#print axioms MWG.PrincipalAgent.b7Cost
#print axioms MWG.PrincipalAgent.b7_local_inv
#print axioms MWG.PrincipalAgent.b7_shift
#print axioms MWG.PrincipalAgent.b7_improve
#print axioms MWG.PrincipalAgent.exercise_14_B_7
#print axioms MWG.PrincipalAgent.b7f
#print axioms MWG.PrincipalAgent.b7w
#print axioms MWG.PrincipalAgent.exercise_14_B_7_instance
#print axioms MWG.PrincipalAgent.b8F
#print axioms MWG.PrincipalAgent.b8EV
#print axioms MWG.PrincipalAgent.b8Cost
#print axioms MWG.PrincipalAgent.B8Feas
#print axioms MWG.PrincipalAgent.b8A
#print axioms MWG.PrincipalAgent.b8B
#print axioms MWG.PrincipalAgent.b8_persp
#print axioms MWG.PrincipalAgent.b8_lag
#print axioms MWG.PrincipalAgent.b8_upd
#print axioms MWG.PrincipalAgent.b8_foc
#print axioms MWG.PrincipalAgent.exercise_14_B_8
#print axioms MWG.PrincipalAgent.b8_exp_bound
#print axioms MWG.PrincipalAgent.b8fq
#print axioms MWG.PrincipalAgent.exercise_14_B_8_instance
#print axioms MWG.PrincipalAgent.exercise_14_B_8_instance_applied
#print axioms MWG.PrincipalAgent.c3_foc_state
#print axioms MWG.PrincipalAgent.exercise_14_C_3a_necessary
#print axioms MWG.PrincipalAgent.exercise_14_C_3a_necessary_instance
#print axioms MWG.PrincipalAgent.inst_footnote_8
#print axioms MWG.PrincipalAgent.inst_EW_gt
#print axioms MWG.PrincipalAgent.inst_high_implementable
#print axioms MWG.PrincipalAgent.inst_lemmas_14_C
#print axioms MWG.PrincipalAgent.inst_appendix_B_steps
#print axioms MWG.PrincipalAgent.inst_eL_falls
#print axioms MWG.PrincipalAgent.inst_14_B_3b
#print axioms MWG.PrincipalAgent.inst_14_B_3c
#print axioms MWG.PrincipalAgent.inst_14_AA_2
