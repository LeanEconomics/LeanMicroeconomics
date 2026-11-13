/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.HardHalkin
import MWGClassicalDemand.CloserAppendixMK

/-!
# Second-order necessary conditions for equality-constrained maximization

MWG, Section M.K, p. 958: "Suppose that at `x̄` the constraint qualification is satisfied and
that there are Lagrange multipliers satisfying (M.K.3). If `x̄` is a local maximizer, then
`D²_x L(x̄, λ)` is negative semidefinite on the subspace `{z : ∇g_m(x̄)·z = 0 for all m}`."

The book's formula `D²f(x̄) - ∑ λ_m ∇g_m(x̄)` is read as `D²f(x̄) - ∑ λ_m D²g_m(x̄)`, the second
derivative of the Lagrangian (first-pass correction E6). We assume, as in the first-pass
sufficiency theorem `theorem_M_K_second_order_sufficient`, that the Lagrangian is differentiable
near `x̄` with a derivative that is differentiable at `x̄` (second derivative `D2`); the
constraints need only be differentiable at `x̄` and continuous near it.

Instead of a `C²` feasible curve with prescribed tangent (which needs `C²` constraints), the proof
uses the feasible points `x̄ + t z + A v_t` with `‖v_t‖ ≤ η t` given by Halkin's lemma
(`hardHalkin_feasible`, Brouwer's theorem): first-order accuracy of the feasible points suffices
because `∇L(x̄) = 0`. Along them `L = f ≤ f(x̄)`, and the second-order expansion of `L`
(`closerMK_second_order_estimate` applied to `-L`) gives `D2 z z ≤ η K` for every small `η > 0`
(`hardSO_bound`), hence `D2 z z ≤ 0` (`theorem_M_K_second_order_necessary`); in matrix form, the
Hessian of the Lagrangian is negative semidefinite on the tangent subspace
(`theorem_M_K_second_order_necessary_matrix`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N M : ℕ}

/-- The key estimate for the second-order necessary conditions (MWG, p. 958): under the
hypotheses of `theorem_M_K_second_order_necessary`, for every tangent direction `z` and every
`0 < η ≤ 1`, `D2 z z ≤ η K` for a constant `K` depending only on `‖z‖`, `‖A‖` and `‖D2‖`. -/
theorem hardSO_bound {f : (Fin N → ℝ) → ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {b lam : Fin M → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hgc : ∀ m, ∀ᶠ y in 𝓝 x, ContinuousAt (g m) y)
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => lagrangian f g b y lam) y)
    (hgrad : fderiv ℝ (fun y => lagrangian f g b y lam) x = 0)
    (h2 : HasFDerivAt (fderiv ℝ (fun y => lagrangian f g b y lam)) D2 x)
    {A : (Fin M → ℝ) →L[ℝ] (Fin N → ℝ)} (hA : ∀ v, ContinuousLinearMap.pi g' (A v) = v)
    {z : Fin N → ℝ} (hz : ∀ m, g' m z = 0) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    D2 z z ≤ η * ((‖z‖ + ‖A‖) ^ 2 + 2 * ‖D2‖ * ‖z‖ * ‖A‖ + ‖D2‖ * ‖A‖ ^ 2) := by
  set F := fun y => lagrangian f g b y lam with hF
  have hFeq : ∀ y, y ∈ eqConstraintSet g b → F y = f y := by
    intro y hy
    simp [hF, lagrangian, show ∀ m, g m y = b m from hy]
  -- the second-order expansion of `-L`
  have hdiffn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => -F y) y :=
    hdiff.mono fun y hy => hy.neg
  have hfd : fderiv ℝ (fun y => -F y) = fun y => -fderiv ℝ F y := funext fun y => fderiv_neg
  have hgradn : fderiv ℝ (fun y => -F y) x = 0 := by rw [hfd]; simp only [hgrad, neg_zero]
  have h2n : HasFDerivAt (fderiv ℝ (fun y => -F y)) (-D2) x := by rw [hfd]; exact h2.neg
  have hest := closerMK_second_order_estimate hdiffn hgradn h2n hη
  -- feasible points
  set G : (Fin N → ℝ) → Fin M → ℝ := fun y m => g m y with hGdef
  have hG : HasFDerivAt G (ContinuousLinearMap.pi g') x := hasFDerivAt_pi.mpr hg
  have hGc : ∀ᶠ y in 𝓝 x, ContinuousAt G y :=
    (eventually_all.mpr hgc).mono fun y hy => continuousAt_pi.mpr hy
  obtain ⟨δ, hδ, hfeas⟩ := hardHalkin_feasible hG hGc hA z hη
  have hmax' : ∀ᶠ y in 𝓝 x, y ∈ eqConstraintSet g b → f y ≤ f x :=
    eventually_nhdsWithin_iff.mp hmax
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hest.and hmax')
  set C := ‖z‖ + ‖A‖ + 1 with hC
  have hC0 : 0 < C := by positivity
  set t := min (δ / 2) (ρ / (2 * C)) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htρ : C * t ≤ ρ / 2 := by
    have := min_le_right (δ / 2) (ρ / (2 * C))
    rw [← ht] at this
    calc C * t ≤ C * (ρ / (2 * C)) := mul_le_mul_of_nonneg_left this hC0.le
      _ = ρ / 2 := by field_simp
  obtain ⟨v, hv, hGv⟩ := hfeas t ht0 htδ
  set w := A v with hw
  set y := x + t • z + w with hy
  have hyx : y - x = t • z + w := by rw [hy]; abel
  have hwn : ‖w‖ ≤ ‖A‖ * η * t := by
    have := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    rw [hw]
    linarith [this, show ‖A‖ * (η * t) = ‖A‖ * η * t by ring]
  have hwn' : ‖w‖ ≤ ‖A‖ * t := by
    refine hwn.trans ?_
    have := mul_le_mul_of_nonneg_left hη1 (norm_nonneg A)
    nlinarith [ht0]
  have htz : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have hhn : ‖y - x‖ ≤ (‖z‖ + ‖A‖) * t := by
    rw [hyx]
    calc ‖t • z + w‖ ≤ ‖t • z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ (‖z‖ + ‖A‖) * t := by rw [htz]; linarith
  have hyball : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (‖z‖ + ‖A‖) * t ≤ C * t := mul_le_mul_of_nonneg_right (by linarith) ht0.le
    linarith
  have hyC : y ∈ eqConstraintSet g b := by
    intro m
    have := congrFun hGv m
    simp only [hGdef, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.pi_apply, hz,
      smul_zero, add_zero] at this
    rw [this]
    exact hx m
  obtain ⟨hesty, hmaxy⟩ := hball y hyball
  have hFle : -F x ≤ -F y := by
    rw [hFeq y hyC, hFeq x hx]
    linarith [hmaxy hyC]
  have hq := hesty hFle
  -- `D2 (y - x) (y - x) ≤ η ‖y - x‖²`
  have hq' : D2 (y - x) (y - x) ≤ η * ‖y - x‖ ^ 2 := by
    have : (-D2) (y - x) (y - x) = -(D2 (y - x) (y - x)) := rfl
    rw [this] at hq
    linarith
  have hexp : D2 (y - x) (y - x) =
      t ^ 2 * D2 z z + t * D2 z w + t * D2 w z + D2 w w := by
    rw [hyx]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hb1 : |D2 z w| ≤ ‖D2‖ * ‖z‖ * (‖A‖ * η * t) := by
    rw [← Real.norm_eq_abs]
    refine (D2.le_opNorm₂ z w).trans ?_
    exact mul_le_mul_of_nonneg_left hwn (mul_nonneg D2.opNorm_nonneg (norm_nonneg _))
  have hb2 : |D2 w z| ≤ ‖D2‖ * (‖A‖ * η * t) * ‖z‖ := by
    rw [← Real.norm_eq_abs]
    refine (D2.le_opNorm₂ w z).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwn D2.opNorm_nonneg)
      (norm_nonneg _)
  have hb3 : |D2 w w| ≤ ‖D2‖ * (‖A‖ * η * t) * (‖A‖ * t) := by
    rw [← Real.norm_eq_abs]
    refine (D2.le_opNorm₂ w w).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hwn D2.opNorm_nonneg) hwn' (norm_nonneg _)
      (mul_nonneg D2.opNorm_nonneg (by positivity))
  have hb4 : η * ‖y - x‖ ^ 2 ≤ η * ((‖z‖ + ‖A‖) * t) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhn 2) hη.le
  have hsum : t ^ 2 * D2 z z ≤
      t ^ 2 * (η * ((‖z‖ + ‖A‖) ^ 2 + 2 * ‖D2‖ * ‖z‖ * ‖A‖ + ‖D2‖ * ‖A‖ ^ 2)) := by
    have e1 := (abs_le.mp hb1).1
    have e2 := (abs_le.mp hb2).1
    have e3 := (abs_le.mp hb3).1
    have : t ^ 2 * D2 z z ≤ η * ((‖z‖ + ‖A‖) * t) ^ 2 - t * D2 z w - t * D2 w z - D2 w w := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_of_neg_le e1) ht0.le,
      mul_le_mul_of_nonneg_left (neg_le_of_neg_le e2) ht0.le]
  exact le_of_mul_le_mul_left hsum (by positivity)

/-- **Section M.K** (MWG, p. 958), second-order necessary conditions. Let `x̄ ∈ C` be a local
constrained maximizer of (M.K.1) at which the constraint qualification holds, the `g_m`
differentiable at `x̄` and continuous near it, and let `λ` be Lagrange multipliers satisfying
(M.K.3), i.e. the Lagrangian `L(·, λ)` is stationary at `x̄`. If `L(·, λ)` is differentiable near
`x̄` and its derivative has derivative `D2` at `x̄` (the second derivative `D²_x L(x̄, λ)`), then
`D2` is negative semidefinite on `{z : ∇g_m(x̄)·z = 0 for all m}`. -/
theorem theorem_M_K_second_order_necessary {f : (Fin N → ℝ) → ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {b lam : Fin M → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hgc : ∀ m, ∀ᶠ y in 𝓝 x, ContinuousAt (g m) y)
    (hCQ : LinearIndependent ℝ g')
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => lagrangian f g b y lam) y)
    (hgrad : fderiv ℝ (fun y => lagrangian f g b y lam) x = 0)
    (h2 : HasFDerivAt (fderiv ℝ (fun y => lagrangian f g b y lam)) D2 x)
    (z : Fin N → ℝ) (hz : ∀ m, g' m z = 0) : D2 z z ≤ 0 := by
  obtain ⟨A, hA⟩ := (ContinuousLinearMap.pi g').exists_rightInverse_of_surjective
    (mk_range_pi_eq_top hCQ)
  have hA' : ∀ v, ContinuousLinearMap.pi g' (A v) = v := fun v => by
    have := congrArg (fun T : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) => T v) hA
    simpa using this
  set K := (‖z‖ + ‖A‖) ^ 2 + 2 * ‖D2‖ * ‖z‖ * ‖A‖ + ‖D2‖ * ‖A‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  by_contra hpos
  push Not at hpos
  set η := min 1 (D2 z z / (2 * (K + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hb := hardSO_bound hx hmax hg hgc hdiff hgrad h2 hA' hz hη (min_le_left _ _)
  have h1 : η * K ≤ D2 z z / (2 * (K + 1)) * K :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hK0
  have h2' : D2 z z / (2 * (K + 1)) * K < D2 z z := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Section M.K** (MWG, p. 958), second-order necessary conditions in matrix form: the Hessian
matrix of the Lagrangian, `D²_x L(x̄, λ)`, satisfies `z·D²_x L z ≤ 0` for every `z` with
`∇g_m(x̄)·z = 0` for all `m`. -/
theorem theorem_M_K_second_order_necessary_matrix {f : (Fin N → ℝ) → ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {b lam : Fin M → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hgc : ∀ m, ∀ᶠ y in 𝓝 x, ContinuousAt (g m) y)
    (hCQ : LinearIndependent ℝ g')
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => lagrangian f g b y lam) y)
    (hgrad : fderiv ℝ (fun y => lagrangian f g b y lam) x = 0)
    (h2 : HasFDerivAt (fderiv ℝ (fun y => lagrangian f g b y lam)) D2 x)
    (z : Fin N → ℝ) (hz : ∀ m, gradientVec (g' m) ⬝ᵥ z = 0) :
    z ⬝ᵥ (hessianMatrix D2).mulVec z ≤ 0 := by
  rw [hessianMatrix_quad]
  refine theorem_M_K_second_order_necessary hx hmax hg hgc hCQ hdiff hgrad h2 z fun m => ?_
  rw [fderiv_apply_eq_gradient_dot]
  exact hz m

end MWG.ClassicalDemand
