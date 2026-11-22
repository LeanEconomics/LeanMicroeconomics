/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityPDE
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Integrability with two commodities: the ordinary differential equation (3.H.1)

MWG, Section 3.H, pp. 78-80, the case `L = 2` with `p₂ = 1`.

* Local existence of a solution of (3.H.1), `e'(p₁) = x₁(p₁, 1, e(p₁))`, `e(p₁⁰) = w⁰`, for a
  demand that is continuously differentiable near `(p₁⁰, w⁰)`, via footnote 18: (3.H.1) is the
  autonomous system `(p₁, e)' = (1, x₁(p₁, e))` in the `(p₁, e)` plane, to which the
  Picard-Lindelöf theorem applies (`equation_3_H_1_local_exists`).
* Properties of a solution claimed on p. 79: nondecreasing because `x₁ ≥ 0`
  (`equation_3_H_1_monotone`); `e'' = s₁₁ ≤ 0`, so concave (`equation_3_H_1_concave`).
* From (3.H.1) to (3.H.2): `E(p) = p₂ e(p₁/p₂)` solves (3.H.2) by homogeneity of degree zero and
  Walras' law (`twoGoodsLift_solvesPDE`).
* The conclusion of p. 80 for `L = 2`: if a family of global solutions `e(·, u)`, strictly
  increasing, continuous and onto in the initial value, exists, then every differentiable demand
  satisfying the weak axiom, homogeneity of degree zero and Walras' law is rationalized by
  preferences (`integrability_two_goods`). The Slutsky matrix is then automatically symmetric
  (MWG Chapter 2's `exercise_2_F_11`). The global existence and the monotone continuous
  dependence on the initial value are OPEN (see the source map).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

/-- **Equation (3.H.1) and footnote 18** (MWG, pp. 78-79), local existence. If `x₁(p₁, w)` (the
demand for good 1 at prices `(p₁, 1)`) is continuously differentiable near `(p₁⁰, w⁰)`, then
(3.H.1) has a solution `e` with `e(p₁⁰) = w⁰` on an open interval around `p₁⁰`. -/
theorem equation_3_H_1_local_exists {x₁ : ℝ → ℝ → ℝ} {p₀ w₀ : ℝ}
    (hx : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => x₁ z.1 z.2) (p₀, w₀)) :
    ∃ ε > (0 : ℝ), ∃ e : ℝ → ℝ, e p₀ = w₀ ∧
      ∀ t ∈ Set.Ioo (p₀ - ε) (p₀ + ε), HasDerivAt e (x₁ t (e t)) t := by
  set V : ℝ × ℝ → ℝ × ℝ := fun z => (1, x₁ z.1 z.2) with hV
  have hVc : ContDiffAt ℝ 1 V (p₀, w₀) := contDiffAt_const.prodMk hx
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hVc.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ p₀
  have hfst : ∀ t ∈ Set.Ioo (p₀ - ε) (p₀ + ε), HasDerivAt (fun s => (α s).1) 1 t :=
    fun t ht => (hα t ht).fst
  -- the first coordinate of the integral curve is the time variable
  have hid : ∀ t ∈ Set.Ioo (p₀ - ε) (p₀ + ε), (α t).1 = t := by
    have hc : ∀ t ∈ Set.Ioo (p₀ - ε) (p₀ + ε), HasDerivAt (fun s => (α s).1 - s) 0 t :=
      fun t ht => by
        have := (hfst t ht).sub (hasDerivAt_id' t)
        rw [sub_self] at this
        exact this
    have hp₀ : p₀ ∈ Set.Ioo (p₀ - ε) (p₀ + ε) := ⟨by linarith, by linarith⟩
    intro t ht
    have h0 : (α p₀).1 - p₀ = 0 := by rw [hα0]; simp
    rcases lt_trichotomy t p₀ with h | h | h
    · obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope (fun s => (α s).1 - s) (fun _ => 0) h
        (fun s hs => (hc s ⟨by linarith [ht.1, hs.1], by linarith [hp₀.2, hs.2]⟩
          ).continuousAt.continuousWithinAt)
        (fun s hs => hc s ⟨by linarith [ht.1, hs.1], by linarith [hp₀.2, hs.2]⟩)
      rw [eq_comm, div_eq_zero_iff] at hcd
      rcases hcd with hcd | hcd
      · linarith
      · linarith
    · subst h
      linarith
    · obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope (fun s => (α s).1 - s) (fun _ => 0) h
        (fun s hs => (hc s ⟨by linarith [hp₀.1, hs.1], by linarith [ht.2, hs.2]⟩
          ).continuousAt.continuousWithinAt)
        (fun s hs => hc s ⟨by linarith [hp₀.1, hs.1], by linarith [ht.2, hs.2]⟩)
      rw [eq_comm, div_eq_zero_iff] at hcd
      rcases hcd with hcd | hcd
      · linarith
      · linarith
  refine ⟨ε, hε, fun s => (α s).2, by simp [hα0], fun t ht => ?_⟩
  have := (hα t ht).snd
  simp only [hV] at this
  rwa [hid t ht] at this

/-- **Section 3.H** (MWG, p. 79). A solution of (3.H.1) on an interval is nondecreasing when
demand for good 1 is nonnegative. -/
theorem equation_3_H_1_monotone {x₁ : ℝ → ℝ → ℝ} {e : ℝ → ℝ} {a b : ℝ}
    (he : ∀ t ∈ Set.Ioo a b, HasDerivAt e (x₁ t (e t)) t)
    (hnn : ∀ t ∈ Set.Ioo a b, 0 ≤ x₁ t (e t)) : MonotoneOn e (Set.Ioo a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo a b)
    (fun t ht => (he t ht).continuousAt.continuousWithinAt)
  · intro t ht
    rw [interior_Ioo] at ht
    exact (he t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(he t ht).deriv]
    exact hnn t ht

/-- **Section 3.H** (MWG, p. 79). Differentiating (3.H.1): if `x₁` is differentiable at
`(p₁, e(p₁))` with derivative `D`, then `e'' = ∂x₁/∂p₁ + (∂x₁/∂w) x₁ = s₁₁`; if `s₁₁ ≤ 0` along
the solution, `e` is concave. -/
theorem equation_3_H_1_concave {x₁ : ℝ → ℝ → ℝ} {e : ℝ → ℝ} {a b : ℝ}
    {D : ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (he : ∀ t ∈ Set.Ioo a b, HasDerivAt e (x₁ t (e t)) t)
    (hD : ∀ t ∈ Set.Ioo a b, HasFDerivAt (fun z : ℝ × ℝ => x₁ z.1 z.2) (D t) (t, e t))
    (hs : ∀ t ∈ Set.Ioo a b, D t (1, 0) + D t (0, 1) * x₁ t (e t) ≤ 0) :
    ConcaveOn ℝ (Set.Ioo a b) e := by
  have hk : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun s => x₁ s (e s))
      (D t (1, 0) + D t (0, 1) * x₁ t (e t)) t := by
    intro t ht
    have hpath : HasDerivAt (fun s => ((s, e s) : ℝ × ℝ)) (1, x₁ t (e t)) t :=
      (hasDerivAt_id t).prodMk (he t ht)
    have := (hD t ht).comp_hasDerivAt t hpath
    have hsplit : ((1, x₁ t (e t)) : ℝ × ℝ) = (1, 0) + x₁ t (e t) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, smul_eq_mul, mul_comm] at this
    exact this
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioo a b)
    (fun t ht => (he t ht).continuousAt.continuousWithinAt)
  · intro t ht
    rw [interior_Ioo] at ht
    exact (he t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    have hanti : AntitoneOn (fun s => x₁ s (e s)) (Set.Ioo a b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioo a b)
        (fun t ht => (hk t ht).continuousAt.continuousWithinAt)
      · intro t ht
        rw [interior_Ioo] at ht
        exact (hk t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ioo] at ht
        rw [(hk t ht).deriv]
        exact hs t ht
    intro s hs' t ht hst
    rw [(he s hs').deriv, (he t ht).deriv]
    exact hanti hs' ht hst

/-- The homogeneous extension `E(p) = p₂ e(p₁/p₂)` of a function of the relative price. -/
noncomputable def twoGoodsLift (e : ℝ → ℝ) (q : Fin 2 → ℝ) : ℝ := q 1 * e (q 0 / q 1)

/-- **Section 3.H** (MWG, pp. 78-79). For `L = 2`, if `e` solves (3.H.1) at `r = p₁/p₂ > 0`
(with `p₂ = 1`, `e(r) > 0`) and `x` is homogeneous of degree zero and satisfies Walras' law, then
`E(p) = p₂ e(p₁/p₂)` satisfies both equations of (3.H.2) at `p`:
`∂E/∂p₁ = x₁(p, E(p))` and `∂E/∂p₂ = x₂(p, E(p))`. -/
theorem twoGoodsLift_hasFDerivAt {x : DemandFunction 2} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {e : ℝ → ℝ} {q : Fin 2 → ℝ} (hq : StrictlyPositive q)
    (hepos : 0 < e (q 0 / q 1))
    (hode : HasDerivAt e (x ![q 0 / q 1, 1] (e (q 0 / q 1)) 0) (q 0 / q 1)) :
    HasFDerivAt (twoGoodsLift e) (dualityDotCLM (x q (twoGoodsLift e q))) q := by
  set r := q 0 / q 1 with hr
  have hq1 := hq 1
  have hr0 : 0 < r := div_pos (hq 0) hq1
  -- the demand at `(q, E(q))` is the demand at `((r, 1), e(r))`
  have hscale : q 1 • (![r, 1] : Fin 2 → ℝ) = q := by
    funext i
    fin_cases i
    · simp [hr]
      field_simp
    · simp
  have hxq : x q (twoGoodsLift e q) = x ![r, 1] (e r) := by
    have := hH ![r, 1] (e r) (q 1) ⟨fun i => by fin_cases i <;> simp [hr0], hepos⟩ hq1
    rw [hscale] at this
    exact this
  have hwal := hW ![r, 1] (e r) ⟨fun i => by fin_cases i <;> simp [hr0], hepos⟩
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul] at hwal
  -- the derivative of `q ↦ q₂ e(q₁ q₂⁻¹)`
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) q
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q
  have hinv := (hasDerivAt_inv hq1.ne').comp_hasFDerivAt q h1
  have hrat := h0.mul hinv
  have hode' : HasDerivAt e (x ![r, 1] (e r) 0) (q 0 * (q 1)⁻¹) := by
    rw [← div_eq_mul_inv]
    exact hode
  have hcomp := hode'.comp_hasFDerivAt q hrat
  have hE := h1.mul hcomp
  have hfun : twoGoodsLift e = fun q : Fin 2 → ℝ => q 1 * (e ∘ fun q => q 0 * (q 1)⁻¹) q := by
    funext q
    simp [twoGoodsLift, div_eq_mul_inv]
  rw [hxq, hfun]
  refine hE.congr_fderiv ?_
  have hrq : ((fun f : Fin 2 → ℝ => f 0) * (fun y : ℝ => y⁻¹) ∘ fun f : Fin 2 → ℝ => f 1) q =
      r := by simp [hr, div_eq_mul_inv]
  have hx1 : x ![r, 1] (e r) 1 = e r - r * x ![r, 1] (e r) 0 := by linarith
  ext v
  rw [dualityDotCLM_apply]
  simp only [Fin.isValue, neg_smul, smul_neg, Function.comp_apply, smul_add, hrq, add_apply,
    neg_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct,
    Fin.sum_univ_two, hx1]
  rw [hr]
  field_simp
  ring

/-- **Section 3.H** (MWG, pp. 78-80). For `L = 2`: a solution of (3.H.1) on all relative prices
`r > 0` gives a solution `E(p) = p₂ e(p₁/p₂)` of (3.H.2) on `p ≫ 0`. -/
theorem twoGoodsLift_solvesPDE {x : DemandFunction 2} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {e : ℝ → ℝ} (hepos : ∀ r, 0 < r → 0 < e r)
    (hode : ∀ r, 0 < r → HasDerivAt e (x ![r, 1] (e r) 0) r) :
    SolvesPDE x (twoGoodsLift e) := fun _ hq =>
  twoGoodsLift_hasFDerivAt hH hW hq (hepos _ (div_pos (hq 0) (hq 1)))
    (hode _ (div_pos (hq 0) (hq 1)))

/-- **Section 3.H** (MWG, p. 80), the case `L = 2`, given the solutions of (3.H.1). Let
`x(p, w)` be a nonnegative demand function on `ℝ²` that is homogeneous of degree zero, satisfies
Walras' law and the weak axiom, and is differentiable on `p ≫ 0, w > 0`. Suppose that for every
utility index `u` the function `e(·, u)` is a positive solution of (3.H.1) on `r > 0`, and that
`e(r, ·)` is strictly increasing, continuous and onto `(0, ∞)`. Then the preference recovered from
`E(p, u) = p₂ e(p₁/p₂, u)` rationalizes `x`: its Walrasian demand at `(p, w)` is `{x(p, w)}`.
(Negative semidefiniteness comes from the weak axiom, MWG Proposition 2.F.2.) -/
theorem integrability_two_goods {x : DemandFunction 2} {e : ℝ → ℝ → ℝ}
    {Dx : (Fin 2 → ℝ) → ℝ → ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hH : HomogeneousZero x) (hW : WalrasLaw x) (hWA : WeakAxiom x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant 2)
    (hD : ∀ q w, StrictlyPositive q → 0 < w → HasFDerivAt (Function.uncurry x) (Dx q w) (q, w))
    (hode : ∀ u r, 0 < r → HasDerivAt (fun s => e s u) (x ![r, 1] (e r u) 0) r)
    (hepos : ∀ u r, 0 < r → 0 < e r u) (hmono : ∀ r, 0 < r → StrictMono (e r))
    (hcont : ∀ r, 0 < r → Continuous (e r)) (hsurj : ∀ r, 0 < r → ∀ w, 0 < w → ∃ u, e r u = w)
    {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    walrasianDemandPref (recoveredPref fun q u => twoGoodsLift (fun s => e s u) q) p w =
      {x p w} := by
  have hr : ∀ q : Fin 2 → ℝ, StrictlyPositive q → 0 < q 0 / q 1 :=
    fun q hq => div_pos (hq 0) (hq 1)
  refine integrability_of_pde hnn hW hD
    (fun q w hq hw' => fun v => proposition_2_F_2 hW hWA ⟨hq, hw'⟩ (hD q w hq hw') v)
    (fun u => twoGoodsLift_solvesPDE hH hW (hepos u) (hode u))
    (fun q u hq => mul_pos (hq 1) (hepos u _ (hr q hq)))
    (fun q hq => fun a b hab => mul_lt_mul_of_pos_left (hmono _ (hr q hq) hab) (hq 1))
    (fun q hq => continuous_const.mul (hcont _ (hr q hq)))
    (fun q hq w' hw' => ?_) hp hw
  obtain ⟨u, hu⟩ := hsurj _ (hr q hq) (w' / q 1) (div_pos hw' (hq 1))
  refine ⟨u, ?_⟩
  simp only [twoGoodsLift, hu]
  exact mul_div_cancel₀ _ (hq 1).ne'

end MWG.ClassicalDemand
