/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExercisesC4

/-!
# Exercise 6.C.15: a riskless and a risky asset

MWG, p. 212. Wealth `1` is split between a riskless asset paying `1` and a risky asset paying
`a` with probability `π` and `b` with probability `1 - π`; with `x₂` in the risky asset, final
wealth is `1 + x₂(a - 1)` or `1 + x₂(b - 1)`. Parts (a)-(b) give necessary conditions for
positive demands, (c) the first-order condition, (d) `dx₁/da ≤ 0` (indeed `< 0`) when `a < 1`,
and (e)-(f) the conjecture `dx₁/dπ ≥ 0` (indeed `> 0`) and its proof, by implicit
differentiation of the first-order condition along a differentiable demand.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- Expected utility from holding `x₂` of the risky asset (and `1 - x₂` of the riskless one). -/
def twoAssetEU (u : ℝ → ℝ) (π a b x₂ : ℝ) : ℝ :=
  π * u (1 + x₂ * (a - 1)) + (1 - π) * u (1 + x₂ * (b - 1))

/-- **Exercise 6.C.15(a)** (MWG, p. 212). If the demand for the riskless asset is strictly
positive (`x₂ < 1`) at an optimum of a strictly increasing utility, then `a < 1` or `b < 1`
(or both returns equal `1`). -/
theorem exercise_6_C_15a {u : ℝ → ℝ} (hi : StrictMono u) {π a b x₂ : ℝ} (hπ : π ∈ Ioo 0 1)
    (hx : x₂ ∈ Ico 0 1) (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    a < 1 ∨ b < 1 ∨ (a = 1 ∧ b = 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb, hab⟩ := hcon
  have h1 := hopt 1 ⟨zero_le_one, le_rfl⟩
  unfold twoAssetEU at h1
  have hx1 : 0 < 1 - x₂ := by linarith [hx.2]
  have ea : u (1 + x₂ * (a - 1)) ≤ u (1 + 1 * (a - 1)) := hi.monotone (by nlinarith)
  have eb : u (1 + x₂ * (b - 1)) ≤ u (1 + 1 * (b - 1)) := hi.monotone (by nlinarith)
  rcases lt_or_eq_of_le ha with ha' | ha'
  · have : u (1 + x₂ * (a - 1)) < u (1 + 1 * (a - 1)) := hi (by nlinarith)
    nlinarith [hπ.1, hπ.2]
  · have hb' : 1 < b := lt_of_le_of_ne hb (fun h => hab ha'.symm h.symm)
    have : u (1 + x₂ * (b - 1)) < u (1 + 1 * (b - 1)) := hi (by nlinarith)
    nlinarith [hπ.1, hπ.2]

/-- **Exercise 6.C.15(b)** (MWG, p. 212). For a strictly risk-averse, increasing utility and
`a ≠ b`, a strictly positive demand for the risky asset requires `πa + (1 - π)b > 1`. -/
theorem exercise_6_C_15b {u : ℝ → ℝ} (hc : StrictConcaveOn ℝ univ u) (hm : Monotone u)
    {π a b x₂ : ℝ} (hπ : π ∈ Ioo 0 1) (hab : a ≠ b) (hx : x₂ ∈ Ioc 0 1)
    (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    1 < π * a + (1 - π) * b := by
  by_contra hle
  have hle : π * a + (1 - π) * b ≤ 1 := not_lt.mp hle
  have hne : 1 + x₂ * (a - 1) ≠ 1 + x₂ * (b - 1) := by
    intro h; apply hab
    have : x₂ * (a - b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith [hx.1]
    · linarith
  have hs := hc.2 (mem_univ _) (mem_univ _) hne hπ.1 (show 0 < 1 - π by linarith [hπ.2])
    (by ring)
  simp only [smul_eq_mul] at hs
  have hmean : π * (1 + x₂ * (a - 1)) + (1 - π) * (1 + x₂ * (b - 1)) ≤ 1 := by nlinarith [hx.1]
  have := hopt 0 ⟨le_rfl, zero_le_one⟩
  unfold twoAssetEU at this
  simp only [zero_mul, add_zero] at this
  have hu1 := hm hmean
  have h1 : π * u 1 + (1 - π) * u 1 = u 1 := by ring
  linarith

/-- The marginal expected utility `φ(x₂) = π(a-1)u'(1 + x₂(a-1)) + (1-π)(b-1)u'(1 + x₂(b-1))`. -/
noncomputable def twoAssetFOC (u : ℝ → ℝ) (π a b x₂ : ℝ) : ℝ :=
  π * (a - 1) * deriv u (1 + x₂ * (a - 1)) + (1 - π) * (b - 1) * deriv u (1 + x₂ * (b - 1))

/-- **Exercise 6.C.15(c)** (MWG, p. 212). At an interior optimum `0 < x₂ < 1` the first-order
condition `φ(x₂) = 0` holds. -/
theorem exercise_6_C_15c {u : ℝ → ℝ} (hd : Differentiable ℝ u) {π a b x₂ : ℝ}
    (hx : x₂ ∈ Ioo 0 1)
    (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    twoAssetFOC u π a b x₂ = 0 := by
  have h1 : HasDerivAt (fun y => u (1 + y * (a - 1))) (deriv u (1 + x₂ * (a - 1)) * (a - 1)) x₂ :=
    (hd _).hasDerivAt.comp x₂ (by simpa using ((hasDerivAt_id x₂).mul_const (a - 1)).const_add 1)
  have h2 : HasDerivAt (fun y => u (1 + y * (b - 1))) (deriv u (1 + x₂ * (b - 1)) * (b - 1)) x₂ :=
    (hd _).hasDerivAt.comp x₂ (by simpa using ((hasDerivAt_id x₂).mul_const (b - 1)).const_add 1)
  have hD : HasDerivAt (twoAssetEU u π a b) (twoAssetFOC u π a b x₂) x₂ := by
    convert (h1.const_mul π).add (h2.const_mul (1 - π)) using 1
    · funext y; rfl
    · unfold twoAssetFOC; ring
  have hloc : IsLocalMax (twoAssetEU u π a b) x₂ := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hopt y ⟨hy.1.le, hy.2.le⟩
  exact hloc.hasDerivAt_eq_zero hD

/-- The derivative of the first-order condition along a demand `x₂ = X(a)`. -/
theorem foc_along_a {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (π b : ℝ) {X : ℝ → ℝ} {X' a₀ : ℝ} (hX : HasDerivAt X X' a₀) :
    HasDerivAt (fun a => twoAssetFOC u π a b (X a))
      (X' * (π * (a₀ - 1) ^ 2 * deriv (deriv u) (1 + X a₀ * (a₀ - 1)) +
          (1 - π) * (b - 1) ^ 2 * deriv (deriv u) (1 + X a₀ * (b - 1))) +
        (π * deriv u (1 + X a₀ * (a₀ - 1)) +
          π * (a₀ - 1) * X a₀ * deriv (deriv u) (1 + X a₀ * (a₀ - 1)))) a₀ := by
  have hWa : HasDerivAt (fun a => 1 + X a * (a - 1)) (X' * (a₀ - 1) + X a₀ * 1) a₀ := by
    simpa using (hX.mul ((hasDerivAt_id a₀).sub_const 1)).const_add 1
  have hWb : HasDerivAt (fun a => 1 + X a * (b - 1)) (X' * (b - 1)) a₀ := by
    simpa using (hX.mul_const (b - 1)).const_add 1
  have t1 := ((hasDerivAt_id a₀).sub_const 1).const_mul π |>.mul
    ((hd2 _).hasDerivAt.comp a₀ hWa)
  have t2 := ((hd2 _).hasDerivAt.comp a₀ hWb).const_mul ((1 - π) * (b - 1))
  unfold twoAssetFOC
  convert t1.add t2 using 1
  · funext a; simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id]
  · simp only [Function.comp_apply, id]; ring

/-- **Exercise 6.C.15(d)** (MWG, p. 212). With `a < 1`, implicit differentiation of the
first-order condition along a differentiable demand `x₂(a) ≥ 0` (for a strictly increasing,
strictly concave `u`) gives `dx₂/da > 0`, i.e. `dx₁/da = -dx₂/da < 0`. -/
theorem exercise_6_C_15d {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (hpos : ∀ t, 0 < deriv u t) (hneg : ∀ t, deriv (deriv u) t < 0) {π b a₀ : ℝ}
    (hπ : π ∈ Ioo 0 1) (ha : a₀ < 1) {X : ℝ → ℝ} {X' : ℝ} (hX : HasDerivAt X X' a₀)
    (hX0 : 0 ≤ X a₀) (hfoc : ∀ᶠ a in 𝓝 a₀, twoAssetFOC u π a b (X a) = 0) :
    -X' < 0 := by
  have hD := foc_along_a hd2 π b hX
  have hzero : HasDerivAt (fun a => twoAssetFOC u π a b (X a)) 0 a₀ :=
    (hasDerivAt_const a₀ (0 : ℝ)).congr_of_eventuallyEq hfoc
  have he := hD.unique hzero
  set Pa := deriv (deriv u) (1 + X a₀ * (a₀ - 1))
  set Pb := deriv (deriv u) (1 + X a₀ * (b - 1))
  have hPa : Pa < 0 := hneg _
  have hPb : Pb < 0 := hneg _
  have hφx : π * (a₀ - 1) ^ 2 * Pa + (1 - π) * (b - 1) ^ 2 * Pb < 0 := by
    have h1 : 0 < π * (a₀ - 1) ^ 2 := mul_pos hπ.1 (by nlinarith)
    have h2 : 0 ≤ (1 - π) * (b - 1) ^ 2 := mul_nonneg (by linarith [hπ.2]) (sq_nonneg _)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hPb.le]
  have hφa : 0 < π * deriv u (1 + X a₀ * (a₀ - 1)) + π * (a₀ - 1) * X a₀ * Pa := by
    have h1 := mul_pos hπ.1 (hpos (1 + X a₀ * (a₀ - 1)))
    have h2 : 0 ≤ π * (a₀ - 1) * X a₀ * Pa := by
      have : π * (a₀ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hπ.1.le (by linarith)
      have : π * (a₀ - 1) * X a₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this hX0
      nlinarith
    linarith
  nlinarith

/-- The derivative of the first-order condition along a demand `x₂ = X(π)`. -/
theorem foc_along_π {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u)) (a b : ℝ) {X : ℝ → ℝ}
    {X' π₀ : ℝ} (hX : HasDerivAt X X' π₀) :
    HasDerivAt (fun π => twoAssetFOC u π a b (X π))
      (X' * (π₀ * (a - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (a - 1)) +
          (1 - π₀) * (b - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (b - 1))) +
        ((a - 1) * deriv u (1 + X π₀ * (a - 1)) - (b - 1) * deriv u (1 + X π₀ * (b - 1)))) π₀ := by
  have hWa : HasDerivAt (fun π => 1 + X π * (a - 1)) (X' * (a - 1)) π₀ := by
    simpa using (hX.mul_const (a - 1)).const_add 1
  have hWb : HasDerivAt (fun π => 1 + X π * (b - 1)) (X' * (b - 1)) π₀ := by
    simpa using (hX.mul_const (b - 1)).const_add 1
  have ga := (hd2 _).hasDerivAt.comp π₀ hWa
  have gb := (hd2 _).hasDerivAt.comp π₀ hWb
  have t1 := ((hasDerivAt_id π₀).mul_const (a - 1)).mul ga
  have t2 := (((hasDerivAt_const π₀ (1 : ℝ)).sub (hasDerivAt_id π₀)).mul_const (b - 1)).mul gb
  unfold twoAssetFOC
  convert t1.add t2 using 1
  · funext π; simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, id]
  · simp only [Function.comp_apply, id, Pi.sub_apply]; ring

/-- **Exercise 6.C.15(e)-(f)** (MWG, p. 212). Conjecture and proof: when `a < 1 < b`, a higher
probability `π` of the low return lowers the demand for the risky asset, `dx₂/dπ < 0`, so
`dx₁/dπ > 0` (by implicit differentiation of the first-order condition). -/
theorem exercise_6_C_15f {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (hpos : ∀ t, 0 < deriv u t) (hneg : ∀ t, deriv (deriv u) t < 0) {a b π₀ : ℝ}
    (hπ : π₀ ∈ Ioo 0 1) (ha : a < 1) (hb : 1 < b) {X : ℝ → ℝ} {X' : ℝ}
    (hX : HasDerivAt X X' π₀) (hfoc : ∀ᶠ π in 𝓝 π₀, twoAssetFOC u π a b (X π) = 0) :
    0 < -X' := by
  have hD := foc_along_π hd2 a b hX
  have hzero : HasDerivAt (fun π => twoAssetFOC u π a b (X π)) 0 π₀ :=
    (hasDerivAt_const π₀ (0 : ℝ)).congr_of_eventuallyEq hfoc
  have he := hD.unique hzero
  have hPa := hneg (1 + X π₀ * (a - 1))
  have hPb := hneg (1 + X π₀ * (b - 1))
  have hφx : π₀ * (a - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (a - 1)) +
      (1 - π₀) * (b - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (b - 1)) < 0 := by
    have h1 : 0 < π₀ * (a - 1) ^ 2 := mul_pos hπ.1 (by nlinarith)
    have h2 : 0 < (1 - π₀) * (b - 1) ^ 2 := mul_pos (by linarith [hπ.2]) (by nlinarith)
    nlinarith
  have hφπ : (a - 1) * deriv u (1 + X π₀ * (a - 1)) -
      (b - 1) * deriv u (1 + X π₀ * (b - 1)) < 0 := by
    have h1 := hpos (1 + X π₀ * (a - 1))
    have h2 := hpos (1 + X π₀ * (b - 1))
    nlinarith
  nlinarith

end MWG.ChoiceUnderUncertainty
