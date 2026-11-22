/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.LawOfDemand
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The Mitiushin-Polterovich theorem

MWG, Section 4.C, Proposition 4.C.3 (p. 112), and Exercises 4.C.5, 4.C.6 (p. 124).

`u` is twice differentiable with gradient `∇u(x) = G(x)` and Hessian `D²u(x) = C(x)`
(symmetric, negative semidefinite: `u` concave), `x·∇u(x) > 0`, and the Mitiushin-Polterovich
bound `-x·D²u(x) x / x·∇u(x) < 4` holds. The proof follows the hint of Exercise 4.C.5.

* `interior_demand_gradient`: at an interior Walrasian demand `x = x(p, w)`, `∇u(x) = λ p` with
  `λ = x·∇u(x)/w`; hence the indirect demand `g(x) = ∇u(x)/(x·∇u(x))` satisfies
  `g(x(p, w)) = p/w`.
* `demand_variational`: with corners, the first-order condition is `∇u(x)·(y - x) ≤ 0` on the
  budget set; it gives `w g(x(p, w))·y ≤ p·y` for every `y ≥ 0`, which replaces the
  self-duality `g(x(p, w)) = p/w` of the hint.
* `mp_quadratic`: the quadratic-form inequality behind `v·Dg(x) v ≤ 0` (with `< 0` when
  `∇u(x)·v ≠ 0`), from `v·Cv - x·Cv = (v - x/2)·C(v - x/2) - x·Cx/4`.
* `mp_uld_on`: the ULD for a single-valued demand whose values lie in a convex set `K` on which
  the hypotheses hold, via the monotonicity `(g(y) - g(x))·(y - x) < 0` of the indirect demand
  along segments.
* `proposition_4_C_3` (Exercise 4.C.5): the book's statement on `X = ℝ^L_+`, boundary demands
  included (`K = ℝ^L_+ \ {0}`); `proposition_4_C_3_interior`: the hypotheses only on `ℝ^L_{++}`
  when every demand is interior.
* `exercise_4_C_6`: a utility homogeneous of degree one has `D²u(x) x = 0`, so `σ(x) = 0 < 4`.

The hypotheses are satisfied by the quasilinear utilities of Exercise 4.C.11 on
`{x ≥ 0 : x₂ > 0}` (`ql_uld` in `QuasilinearSlutsky`), whose demands have corners.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L : ℕ}

/-- **Exercise 4.C.5** (MWG, p. 124), first-order step. If `x ≫ 0` is a Walrasian demand at
`(p, w)` with `p·x = w > 0` and `u` is differentiable at `x` with gradient `G(x)`, then
`G(x) = (x·G(x)/w) p`. -/
theorem interior_demand_gradient {u : (Fin L → ℝ) → ℝ} {Gx : Fin L → ℝ} {p x : Fin L → ℝ}
    {w : ℝ} (hw : 0 < w) (hx : x ∈ walrasianDemand u p w) (hxpos : StrictlyPositive x)
    (hpx : p ⬝ᵥ x = w) (hu : HasFDerivAt u (dualityDotCLM Gx) x) :
    Gx = ((x ⬝ᵥ Gx) / w) • p := by
  -- directional derivatives along the budget hyperplane vanish
  have hzero : ∀ v : Fin L → ℝ, p ⬝ᵥ v = 0 → Gx ⬝ᵥ v = 0 := by
    intro v hv
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hcomp : HasDerivAt (fun t : ℝ => u (x + t • v)) (Gx ⬝ᵥ v) 0 := by
      have := hu.comp_hasDerivAt_of_eq 0 hline (by simp)
      simpa [Function.comp_def, dualityDotCLM_apply] using this
    have hmax : IsLocalMax (fun t : ℝ => u (x + t • v)) 0 := by
      have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      filter_upwards [this.eventually (relations_eventually_strictlyPositive hxpos)] with t ht
      simp only [zero_smul, add_zero]
      refine hx.2 _ ⟨fun l => (ht l).le, ?_⟩
      rw [dotProduct_add, dotProduct_smul, hv, smul_zero, add_zero, hpx]
    exact hmax.hasDerivAt_eq_zero hcomp
  funext l
  have hv : p ⬝ᵥ (Pi.single l 1 - (p l / w) • x) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hpx, dotProduct_single, smul_eq_mul]
    field_simp
    ring
  have := hzero _ hv
  rw [dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one,
    dotProduct_comm] at this
  have h2 : Gx l = p l / w * (x ⬝ᵥ Gx) := by linarith
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  ring

/-- **Exercise 4.C.5** (MWG, p. 124), the hint's inequality. Let `C` be symmetric and negative
semidefinite, `q = ∇u(x)` with `A = x·q > 0` and `-x·Cx < 4A` (`σ(x) < 4`). For a direction
`v` with `s = q·v`, `N = A (v·Cv) - s² - s (x·Cv)` (the numerator of `v·Dg(x) v` times
`(x·q)²`) satisfies `N ≤ 0`, and `N < 0` if `s ≠ 0`. -/
theorem mp_quadratic {C : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hsymm : ∀ v z, v ⬝ᵥ C z = z ⬝ᵥ C v)
    (hnsd : ∀ z, z ⬝ᵥ C z ≤ 0) {x q v : Fin L → ℝ} (hA : 0 < x ⬝ᵥ q)
    (hσ : -(x ⬝ᵥ C x) < 4 * (x ⬝ᵥ q)) :
    (x ⬝ᵥ q) * (v ⬝ᵥ C v) - (q ⬝ᵥ v) ^ 2 - (q ⬝ᵥ v) * (x ⬝ᵥ C v) ≤ 0 ∧
      (q ⬝ᵥ v ≠ 0 →
        (x ⬝ᵥ q) * (v ⬝ᵥ C v) - (q ⬝ᵥ v) ^ 2 - (q ⬝ᵥ v) * (x ⬝ᵥ C v) < 0) := by
  set A := x ⬝ᵥ q
  set s := q ⬝ᵥ v
  set P := v ⬝ᵥ C v
  set Q := x ⬝ᵥ C v
  set R := x ⬝ᵥ C x
  -- `(A v - (s/2) x)·C(A v - (s/2) x) = A² P - A s Q + s² R/4 ≤ 0`
  have hE : A ^ 2 * P - A * s * Q + s ^ 2 * R / 4 ≤ 0 := by
    have h := hnsd (A • v - (s / 2) • x)
    have hvx : v ⬝ᵥ C x = Q := hsymm v x
    simp only [map_sub, map_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hvx] at h
    have : A * (A * P) - A * (s / 2 * Q) - (s / 2 * (A * Q) - s / 2 * (s / 2 * R)) =
        A ^ 2 * P - A * s * Q + s ^ 2 * R / 4 := by ring
    linarith
  have hkey : A * (A * P - s ^ 2 - s * Q) = (A ^ 2 * P - A * s * Q + s ^ 2 * R / 4) -
      s ^ 2 * (R / 4 + A) := by ring
  have hRA : 0 < R / 4 + A := by linarith
  constructor
  · have : A * (A * P - s ^ 2 - s * Q) ≤ 0 := by
      rw [hkey]
      nlinarith [sq_nonneg s]
    by_contra hc
    push Not at hc
    nlinarith
  · intro hs
    have hs2 : 0 < s ^ 2 := by positivity
    have : A * (A * P - s ^ 2 - s * Q) < 0 := by
      rw [hkey]
      nlinarith
    by_contra hc
    push Not at hc
    nlinarith

/-- **Exercise 4.C.5** (MWG, p. 124), first-order condition with corners. If `x` is a Walrasian
demand at `(p, w)` and `u` is differentiable at `x` with gradient `G`, then `G·(y - x) ≤ 0` for
every `y ∈ B_{p,w}` (the budget set is convex and `x` maximizes `u` on it). At an interior `x`
this gives `G = λ p`; at a corner it gives the Kuhn-Tucker inequalities. -/
theorem demand_variational {u : (Fin L → ℝ) → ℝ} {G p x y : Fin L → ℝ} {w : ℝ}
    (hx : x ∈ walrasianDemand u p w) (hu : HasFDerivAt u (dualityDotCLM G) x)
    (hy : y ∈ budgetSet p w) : G ⬝ᵥ (y - x) ≤ 0 := by
  have hmax : IsLocalMaxOn u (budgetSet p w) x := IsMaxOn.isLocalMaxOn fun z hz => hx.2 z hz
  have hcone : y - x ∈ posTangentConeAt (budgetSet p w) x :=
    sub_mem_posTangentConeAt_of_segment_subset ((convex_budgetSet p w).segment_subset hx.1 hy)
  have := hmax.hasFDerivWithinAt_nonpos hu.hasFDerivWithinAt hcone
  simpa [dualityDotCLM_apply] using this

/-- A nonnegative bundle with `p'·y = w > 0` has `p·y > 0` for every `p ≫ 0`. -/
theorem mp_dot_pos {p p' y : Fin L → ℝ} {w : ℝ} (hp : StrictlyPositive p)
    (hy : y ∈ nonnegOrthant L) (hw : 0 < w) (hpy : p' ⬝ᵥ y = w) : 0 < p ⬝ᵥ y := by
  rcases (Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hy l) :
      (0 : ℝ) ≤ p ⬝ᵥ y).eq_or_lt with h | h
  · have h0 : ∀ l, y l = 0 := by
      intro l
      have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hp k).le (hy k)).mp
        h.symm l (Finset.mem_univ l)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (hp l).ne'
      · exact h1
    have : p' ⬝ᵥ y = 0 := by simp [dotProduct, h0]
    linarith
  · exact h

/-- **Proposition 4.C.3** (MWG, p. 112; proof as in Exercise 4.C.5, p. 124), on a convex set of
bundles. Let `K` be convex and contain every demanded bundle. Suppose that on `K`, `u` is
differentiable with gradient `G`, `G` is differentiable with symmetric negative semidefinite
derivative `C` (concavity), `x·∇u(x) > 0`, and `-x·D²u(x) x/(x·∇u(x)) < 4`. If the Walrasian
demand is single-valued, `x(p, w)` is a selection satisfying Walras' law, then it satisfies the
ULD. Corners are allowed: the first-order condition used is `demand_variational`, and the
indirect demand `g(x) = ∇u(x)/(x·∇u(x))` satisfies `g(x(p, w)) ≤ p/w` in the sense
`w g(x(p, w))·y ≤ p·y` for `y ≥ 0`. -/
theorem mp_uld_on {K : Set (Fin L → ℝ)} (hK : Convex ℝ K) {u : (Fin L → ℝ) → ℝ}
    {G : (Fin L → ℝ) → Fin L → ℝ} {C : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hu : ∀ x ∈ K, HasFDerivAt u (dualityDotCLM (G x)) x)
    (hG : ∀ x ∈ K, HasFDerivAt G (C x) x)
    (hsymm : ∀ x ∈ K, ∀ v z, v ⬝ᵥ C x z = z ⬝ᵥ C x v)
    (hnsd : ∀ x ∈ K, ∀ z, z ⬝ᵥ C x z ≤ 0)
    (hpos : ∀ x ∈ K, 0 < x ⬝ᵥ G x)
    (hσ : ∀ x ∈ K, -(x ⬝ᵥ C x x) < 4 * (x ⬝ᵥ G x))
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    (hxK : ∀ p w, PWDomain p w → xf p w ∈ K)
    (huniq : ∀ p w, PWDomain p w → (walrasianDemand u p w).Subsingleton)
    (hW : WalrasLaw xf) : UncompensatedLawOfDemand xf := by
  intro p p' w hd hp'
  have hd' : PWDomain p' w := ⟨hp', hd.2⟩
  set x := xf p w with hxdef
  set y := xf p' w with hydef
  set v := y - x with hv
  have hx := hxK p w hd
  have hy := hxK p' w hd'
  -- the segment `x + t v` stays in `K` for `t ∈ [0, 1]`
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • v ∈ K := by
    intro t ht
    have e : x + t • v = (1 - t) • x + t • y := by
      simp only [hv, smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    exact hK hx hy (by linarith [ht.2]) ht.1 (by ring)
  -- derivatives along the segment
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hGt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => G (x + t • v)) (C (x + t • v) v) t :=
    fun t ht => (hG _ (hseg t ht)).comp_hasDerivAt t (hline t)
  set a : ℝ → ℝ := fun t => G (x + t • v) ⬝ᵥ v with ha
  set b : ℝ → ℝ := fun t => (x + t • v) ⬝ᵥ G (x + t • v) with hb
  have hadr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt a (v ⬝ᵥ C (x + t • v) v) t := by
    intro t ht
    have := (dualityDotCLM v).hasFDerivAt.comp_hasDerivAt t (hGt t ht)
    convert this using 1
    · funext s; simp [a, dualityDotCLM_apply, dotProduct_comm]
    · simp [dualityDotCLM_apply]
  have hbdr : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt b
      (v ⬝ᵥ G (x + t • v) + (x + t • v) ⬝ᵥ C (x + t • v) v) t := by
    intro t ht
    have h1 := hasDerivAt_pi.mp (hline t)
    have h2 := hasDerivAt_pi.mp (hGt t ht)
    have := HasDerivAt.sum (u := Finset.univ) fun l _ => (h1 l).mul (h2 l)
    convert this using 1
    · funext s
      simp only [b, dotProduct, Finset.sum_apply, Pi.mul_apply]
    · simp only [dotProduct, Finset.sum_add_distrib]
  have hbpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < b t := fun t ht => hpos _ (hseg t ht)
  set φ : ℝ → ℝ := fun t => a t / b t with hφ
  have hφdr : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ
      ((v ⬝ᵥ C (x + t • v) v * b t - a t *
        (v ⬝ᵥ G (x + t • v) + (x + t • v) ⬝ᵥ C (x + t • v) v)) / b t ^ 2) t :=
    fun t ht => (hadr t ht).div (hbdr t ht) (hbpos t ht).ne'
  -- the numerator is `N ≤ 0`, negative where `a ≠ 0`
  have hN : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (v ⬝ᵥ C (x + t • v) v * b t - a t *
        (v ⬝ᵥ G (x + t • v) + (x + t • v) ⬝ᵥ C (x + t • v) v)) ≤ 0 ∧
      (a t ≠ 0 → (v ⬝ᵥ C (x + t • v) v * b t - a t *
        (v ⬝ᵥ G (x + t • v) + (x + t • v) ⬝ᵥ C (x + t • v) v)) < 0) := by
    intro t ht
    have hq := mp_quadratic (hsymm _ (hseg t ht)) (hnsd _ (hseg t ht)) (v := v)
      (hpos _ (hseg t ht)) (hσ _ (hseg t ht))
    have e1 : a t = G (x + t • v) ⬝ᵥ v := rfl
    have e2 : v ⬝ᵥ G (x + t • v) = G (x + t • v) ⬝ᵥ v := dotProduct_comm _ _
    have e : v ⬝ᵥ C (x + t • v) v * b t - a t *
        (v ⬝ᵥ G (x + t • v) + (x + t • v) ⬝ᵥ C (x + t • v) v) =
        (x + t • v) ⬝ᵥ G (x + t • v) * (v ⬝ᵥ C (x + t • v) v) - (G (x + t • v) ⬝ᵥ v) ^ 2 -
          (G (x + t • v) ⬝ᵥ v) * ((x + t • v) ⬝ᵥ C (x + t • v) v) := by
      rw [e1, e2]; simp only [b]; ring
    rw [e]
    exact ⟨hq.1, fun h => hq.2 (by rwa [e1] at h)⟩
  have hφ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧ d ≤ 0 ∧ (a t ≠ 0 → d < 0) :=
    fun t ht => ⟨_, hφdr t ht, div_nonpos_of_nonpos_of_nonneg (hN t ht).1 (sq_nonneg _),
      fun h => div_neg_of_neg_of_pos ((hN t ht).2 h) (pow_pos (hbpos t ht) 2)⟩
  have hφc : ContinuousOn φ (Set.Icc 0 1) :=
    fun t ht => (hφdr t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hφc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφdr t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, hd0, -⟩ := hφ' t (Set.Ioo_subset_Icc_self ht)
      rw [hd.deriv]
      exact hd0
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- first-order conditions with corners
  have hxD := hxf p w hd
  have hyD := hxf p' w hd'
  have hWx : p ⬝ᵥ x = w := hW p w hd
  have hWy : p' ⬝ᵥ y = w := hW p' w hd'
  have hA : 0 < x ⬝ᵥ G x := hpos x hx
  have hB : 0 < y ⬝ᵥ G y := hpos y hy
  have hpy : 0 < p ⬝ᵥ y := mp_dot_pos hd.1 hyD.1.1 hd.2 hWy
  have hp'x : 0 < p' ⬝ᵥ x := mp_dot_pos hp' hxD.1.1 hd.2 hWx
  -- `w (G(x)·y) ≤ (x·G(x)) (p·y)`
  have hcx : w * (G x ⬝ᵥ y) ≤ (x ⬝ᵥ G x) * (p ⬝ᵥ y) := by
    have hz : (w / (p ⬝ᵥ y)) • y ∈ budgetSet p w := by
      refine ⟨fun l => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (div_nonneg hd.2.le hpy.le) (hyD.1.1 l)
      · rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hpy.ne']
    have := demand_variational hxD (hu x hx) hz
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm (G x) x] at this
    have h2 : w / (p ⬝ᵥ y) * (G x ⬝ᵥ y) * (p ⬝ᵥ y) = w * (G x ⬝ᵥ y) := by
      field_simp
    nlinarith
  -- `w (G(y)·x) ≤ (y·G(y)) (p'·x)`
  have hcy : w * (G y ⬝ᵥ x) ≤ (y ⬝ᵥ G y) * (p' ⬝ᵥ x) := by
    have hz : (w / (p' ⬝ᵥ x)) • x ∈ budgetSet p' w := by
      refine ⟨fun l => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (div_nonneg hd.2.le hp'x.le) (hxD.1.1 l)
      · rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hp'x.ne']
    have := demand_variational hyD (hu y hy) hz
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm (G y) y] at this
    have h2 : w / (p' ⬝ᵥ x) * (G y ⬝ᵥ x) * (p' ⬝ᵥ x) = w * (G y ⬝ᵥ x) := by
      field_simp
    nlinarith
  have hφ0 : φ 0 = (G x ⬝ᵥ y - x ⬝ᵥ G x) / (x ⬝ᵥ G x) := by
    simp only [φ, a, b, zero_smul, add_zero, hv, dotProduct_sub, dotProduct_comm (G x) x]
  have hφ1 : φ 1 = (y ⬝ᵥ G y - G y ⬝ᵥ x) / (y ⬝ᵥ G y) := by
    simp only [φ, a, b, one_smul, hv, add_sub_cancel, dotProduct_sub, dotProduct_comm (G y) y]
  -- `(p' - p)·(y - x) ≤ w (φ(1) - φ(0))`
  have hle1 : w - p' ⬝ᵥ x ≤ w * φ 1 := by
    rw [hφ1, mul_div_assoc', le_div_iff₀ hB]
    nlinarith
  have hle0 : w * φ 0 ≤ p ⬝ᵥ y - w := by
    rw [hφ0, mul_div_assoc', div_le_iff₀ hA]
    nlinarith
  have hexp : (p' - p) ⬝ᵥ (y - x) = 2 * w - p' ⬝ᵥ x - p ⬝ᵥ y := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hWx, hWy]
    ring
  have hle : φ 1 ≤ φ 0 := hanti h0mem h1mem zero_le_one
  have hmain : (p' - p) ⬝ᵥ (y - x) ≤ w * (φ 1 - φ 0) := by
    rw [hexp]; nlinarith
  refine ⟨hmain.trans (mul_nonpos_of_nonneg_of_nonpos hd.2.le (by linarith)), fun hne => ?_⟩
  by_contra hge
  push Not at hge
  have heq : φ 1 = φ 0 := by
    apply le_antisymm hle
    by_contra hlt
    push Not at hlt
    have : w * (φ 1 - φ 0) < 0 := mul_neg_of_pos_of_neg hd.2 (by linarith)
    linarith
  -- `φ` is constant on `[0, 1]`, so `a = 0` on `(0, 1)`
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t = φ 0 := by
    intro t ht
    exact le_antisymm (hanti h0mem ht ht.1) (heq ▸ hanti ht h1mem ht.2)
  have ha0 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t = 0 := by
    intro t ht
    by_contra hat
    obtain ⟨d, hdt, -, hdneg⟩ := hφ' t (Set.Ioo_subset_Icc_self ht)
    have hloc : φ =ᶠ[𝓝 t] fun _ => φ 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hconst s (Set.Ioo_subset_Icc_self hs)
    have := hdt.unique ((hasDerivAt_const t (φ 0)).congr_of_eventuallyEq hloc)
    linarith [hdneg hat]
  -- hence `a(0) = 0` by continuity, so `φ(0) = φ(1) = 0`
  have ha00 : a 0 = 0 := by
    have hlim : Tendsto a (𝓝[>] 0) (𝓝 (a 0)) :=
      ((hadr 0 h0mem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (ha0 t ht).symm
  have hφ00 : φ 0 = 0 := by simp only [φ, ha00, zero_div]
  -- `p·y ≤ w`
  have hpyw : p ⬝ᵥ y ≤ w := by
    have : w - p' ⬝ᵥ x ≤ 0 := by rw [heq, hφ00, mul_zero] at hle1; exact hle1
    rw [hexp] at hge
    linarith
  -- `t ↦ u(x + t v)` has derivative `a(t) = 0`, so `u(y) = u(x)`
  have hud : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => u (x + t • v)) (a t) t := by
    intro t ht
    have := (hu _ (hseg t ht)).comp_hasDerivAt t (hline t)
    simpa [Function.comp_def, dualityDotCLM_apply, a] using this
  have huc : ContinuousOn (fun t : ℝ => u (x + t • v)) (Set.Icc 0 1) :=
    fun t ht => (hud t ht).continuousAt.continuousWithinAt
  have huconst := constant_of_has_deriv_right_zero huc (fun t ht => by
    have hmem : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      have := (hud 0 hmem).hasDerivWithinAt (s := Set.Ici 0)
      rwa [ha00] at this
    · have := (hud t hmem).hasDerivWithinAt (s := Set.Ici t)
      rwa [ha0 t ⟨h0, ht.2⟩] at this) 1 h1mem
  simp only [one_smul, zero_smul, add_zero, hv, add_sub_cancel] at huconst
  -- so `y` is affordable at `(p, w)` and as good as `x`: it is demanded there
  have hyB : y ∈ budgetSet p w := ⟨hyD.1.1, hpyw⟩
  have hymem : y ∈ walrasianDemand u p w :=
    ⟨hyB, fun z hz => (hxD.2 z hz).trans huconst.ge⟩
  exact hne (huniq p w hd hymem hxD)

/-- **Proposition 4.C.3** (MWG, p. 112; proof as in Exercise 4.C.5, p. 124). Suppose that on the
consumption set `ℝ^L_+` (at every `x ≥ 0`, `x ≠ 0`, where the quotient `σ(x)` is defined) `u`
is twice differentiable with gradient `G` and symmetric negative semidefinite Hessian `C`
(concavity), `x·∇u(x) > 0`, and `-x·D²u(x) x/(x·∇u(x)) < 4`. If the Walrasian demand is
single-valued and `x(p, w)` is a selection satisfying Walras' law, then `x(p, w)` satisfies the
ULD. Demands on the boundary of `ℝ^L_+` are allowed. (Differentiability at a boundary point is
in the sense of a function on `ℝ^L`, the usual reading of "twice continuously differentiable on
`ℝ^L_+`".) -/
theorem proposition_4_C_3 {u : (Fin L → ℝ) → ℝ} {G : (Fin L → ℝ) → Fin L → ℝ}
    {C : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hu : ∀ x ∈ nonnegOrthant L, x ≠ 0 → HasFDerivAt u (dualityDotCLM (G x)) x)
    (hG : ∀ x ∈ nonnegOrthant L, x ≠ 0 → HasFDerivAt G (C x) x)
    (hsymm : ∀ x ∈ nonnegOrthant L, x ≠ 0 → ∀ v z, v ⬝ᵥ C x z = z ⬝ᵥ C x v)
    (hnsd : ∀ x ∈ nonnegOrthant L, x ≠ 0 → ∀ z, z ⬝ᵥ C x z ≤ 0)
    (hpos : ∀ x ∈ nonnegOrthant L, x ≠ 0 → 0 < x ⬝ᵥ G x)
    (hσ : ∀ x ∈ nonnegOrthant L, x ≠ 0 → -(x ⬝ᵥ C x x) < 4 * (x ⬝ᵥ G x))
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    (huniq : ∀ p w, PWDomain p w → (walrasianDemand u p w).Subsingleton)
    (hW : WalrasLaw xf) : UncompensatedLawOfDemand xf := by
  have hK : Convex ℝ {x : Fin L → ℝ | x ∈ nonnegOrthant L ∧ x ≠ 0} := by
    intro x hx y hy a b ha hb hab
    refine ⟨convex_nonnegOrthant L hx.1 hy.1 ha hb hab, fun h0 => ?_⟩
    -- a nonzero nonnegative bundle has a positive coordinate
    obtain ⟨l, hl⟩ : ∃ l, x l ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx.2 (funext hc)
    have hxl : 0 < x l := lt_of_le_of_ne (hx.1 l) (Ne.symm hl)
    have := congrFun h0 l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hyl := hy.1 l
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0, zero_add] at hab
      rw [← ha0, hab] at this
      obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hy.2 (funext hc)
      have hyk : 0 < y k := lt_of_le_of_ne (hy.1 k) (Ne.symm hk)
      have := congrFun h0 k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← ha0, hab] at this
      linarith
    · nlinarith [mul_pos ha0 hxl, mul_nonneg hb hyl]
  refine mp_uld_on hK (fun x hx => hu x hx.1 hx.2) (fun x hx => hG x hx.1 hx.2)
    (fun x hx => hsymm x hx.1 hx.2) (fun x hx => hnsd x hx.1 hx.2) (fun x hx => hpos x hx.1 hx.2)
    (fun x hx => hσ x hx.1 hx.2) hxf (fun p w hd => ⟨(hxf p w hd).1.1, fun h0 => ?_⟩) huniq hW
  have := hW p w hd
  rw [h0, dotProduct_zero] at this
  exact hd.2.ne this

/-- **Proposition 4.C.3** (MWG, p. 112): a proved instance of the hypotheses of
`proposition_4_C_3` (one good, `u(x) = x`, `D²u = 0`, `σ = 0`); the instance with corners is the
quasilinear pair of Exercise 4.C.11 (`ql_uld`). -/
theorem proposition_4_C_3_instance :
    UncompensatedLawOfDemand (fun p w => (fun _ => w / p 0 : Fin 1 → ℝ)) := by
  have hdem : ∀ p w, PWDomain p w →
      walrasianDemand (fun x : Fin 1 → ℝ => x 0) p w = {fun _ => w / p 0} := by
    intro p w hd
    have hp := hd.1 0
    have hdot : ∀ y : Fin 1 → ℝ, p ⬝ᵥ y = p 0 * y 0 := fun y => by simp [dotProduct]
    have hmem : (fun _ => w / p 0 : Fin 1 → ℝ) ∈ budgetSet p w :=
      ⟨fun _ => div_nonneg hd.2.le hp.le, by rw [hdot]; field_simp; rfl⟩
    have hle : ∀ y ∈ budgetSet p w, y 0 ≤ w / p 0 := fun y hy => by
      rw [le_div_iff₀ hp, mul_comm, ← hdot]; exact hy.2
    ext z
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · funext l
      fin_cases l
      exact le_antisymm (hle z hz.1) (hz.2 _ hmem)
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨hmem, fun y hy => hle y hy⟩
  refine proposition_4_C_3 (u := fun x : Fin 1 → ℝ => x 0) (G := fun _ => fun _ => 1)
    (C := fun _ => 0) (fun x _ _ => ?_) (fun x _ _ => hasFDerivAt_const _ _)
    (fun _ _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun x hx hx0 => ?_)
    (fun x hx hx0 => ?_) (fun p w hd => by rw [hdem p w hd]; rfl)
    (fun p w hd => by rw [hdem p w hd]; exact Set.subsingleton_singleton)
    (fun p w hd => by simp [dotProduct]; field_simp [(hd.1 0).ne'])
  · have := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x
    refine this.congr_fderiv ?_
    ext v
    simp [dualityDotCLM_apply, dotProduct]
  · have h0 : x 0 ≠ 0 := fun h => hx0 (funext fun l => by fin_cases l; exact h)
    have : 0 < x 0 := lt_of_le_of_ne (hx 0) (Ne.symm h0)
    simpa [dotProduct] using this
  · have h0 : x 0 ≠ 0 := fun h => hx0 (funext fun l => by fin_cases l; exact h)
    have : 0 < x 0 := lt_of_le_of_ne (hx 0) (Ne.symm h0)
    simp [dotProduct]
    linarith

/-- **Proposition 4.C.3** (MWG, p. 112), for interior demands: the hypotheses on `u` are needed
only on `ℝ^L_{++}` when every demand is interior. -/
theorem proposition_4_C_3_interior {u : (Fin L → ℝ) → ℝ} {G : (Fin L → ℝ) → Fin L → ℝ}
    {C : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hu : ∀ x, StrictlyPositive x → HasFDerivAt u (dualityDotCLM (G x)) x)
    (hG : ∀ x, StrictlyPositive x → HasFDerivAt G (C x) x)
    (hsymm : ∀ x, StrictlyPositive x → ∀ v z, v ⬝ᵥ C x z = z ⬝ᵥ C x v)
    (hnsd : ∀ x, StrictlyPositive x → ∀ z, z ⬝ᵥ C x z ≤ 0)
    (hpos : ∀ x, StrictlyPositive x → 0 < x ⬝ᵥ G x)
    (hσ : ∀ x, StrictlyPositive x → -(x ⬝ᵥ C x x) < 4 * (x ⬝ᵥ G x))
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    (hint : ∀ p w, PWDomain p w → StrictlyPositive (xf p w))
    (huniq : ∀ p w, PWDomain p w → (walrasianDemand u p w).Subsingleton)
    (hW : WalrasLaw xf) : UncompensatedLawOfDemand xf := by
  have hK : Convex ℝ {x : Fin L → ℝ | StrictlyPositive x} := by
    intro x hx y hy a b ha hb hab l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0, zero_add] at hab
      rw [← ha0, hab]
      simpa using hy l
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 (hx l)) (mul_nonneg hb (hy l).le)
  exact mp_uld_on hK hu hG hsymm hnsd hpos hσ hxf hint huniq hW

/-- **Exercise 4.C.6** (MWG, p. 124). If `u` is homogeneous of degree one on `ℝ^L_{++}` with
gradient `G` (homogeneous of degree zero) and Hessian `C`, then `C(x) x = 0`, so
`σ(x) = -x·D²u(x) x/(x·∇u(x)) = 0` for every `x ≫ 0`; homothetic preferences fit
Proposition 4.C.3. -/
theorem exercise_4_C_6 {G : (Fin L → ℝ) → Fin L → ℝ}
    {C : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hG0 : ∀ x, StrictlyPositive x → ∀ t : ℝ, 0 < t → G (t • x) = G x)
    (hG : ∀ x, StrictlyPositive x → HasFDerivAt G (C x) x) {x : Fin L → ℝ}
    (hx : StrictlyPositive x) : C x x = 0 ∧ x ⬝ᵥ C x x = 0 := by
  have hpath : HasDerivAt (fun t : ℝ => G ((1 + t) • x)) (C x x) 0 := by
    have hl : HasDerivAt (fun t : ℝ => (1 + t) • x) x 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
    have := (hG x hx).comp_hasDerivAt_of_eq 0 hl (by simp)
    simpa [Function.comp_def] using this
  have hev : (fun t : ℝ => G ((1 + t) • x)) =ᶠ[𝓝 0] fun _ => G x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos] with t ht
    exact hG0 x hx _ (by linarith [ht.1])
  have h := hpath.unique ((hasDerivAt_const (0 : ℝ) (G x)).congr_of_eventuallyEq hev)
  exact ⟨h, by rw [h, dotProduct_zero]⟩

end MWG.AggregateDemand
