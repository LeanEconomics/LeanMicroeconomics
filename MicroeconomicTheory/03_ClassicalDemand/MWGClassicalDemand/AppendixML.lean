/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.DualitySupport
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The envelope theorem

MWG, Mathematical Appendix, Section M.L, pp. 964-966.

* `envelope_tangency` (Figure M.L.1, p. 965): if `f(x̄; ·) ≤ v` near `q̄` with equality at `q̄`
  and both are differentiable at `q̄`, their derivatives agree. This gives the envelope theorem
  whenever `x̄` stays feasible as `q` moves (e.g. parameters in the objective only;
  `envelope_objective_only`, the setting of Proof 3 of Proposition 3.G.1 and footnote 16).
* (M.L.2)-(M.L.3): along a differentiable maximizer path with `∂f/∂x = 0`, `dv/dq = ∂f/∂q`
  (`equation_M_L_3`).
* **Theorem M.L.1** (M.L.4)-(M.L.5): for the problem `max f(x; q)` s.t. `g_m(x; q) = b̄_m`, along a
  maximizer path `x(·)` differentiable at `q̄` and feasible near `q̄`, with multipliers `λ` in
  the first-order conditions (M.K.2), `∇v(q̄) = ∇_q f - ∑ λ_m ∇_q g_m` (`theorem_M_L_1`). This is
  the book's proof; the book's statement assumes only that `v` is differentiable, and that
  general constrained case (it needs feasible curves through `x̄` built under a constraint
  qualification) is left OPEN.
-/

namespace MWG.ClassicalDemand

open Filter Topology

/-- **Section M.L** (MWG, p. 965; Figure M.L.1). If `g ≤ v` near `q̄`, `g(q̄) = v(q̄)`, and both
are differentiable at `q̄`, then `g'(q̄) = v'(q̄)`: the two graphs are tangent at `q̄`. -/
theorem envelope_tangency {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g v : E → ℝ}
    {q : E} {g' v' : E →L[ℝ] ℝ} (hle : ∀ᶠ q' in 𝓝 q, g q' ≤ v q') (heq : g q = v q)
    (hg : HasFDerivAt g g' q) (hv : HasFDerivAt v v' q) : g' = v' := by
  have hmin : IsLocalMin (fun q' => v q' - g q') q := by
    filter_upwards [hle] with q' hq'
    rw [heq, sub_self]
    linarith
  have := hmin.hasFDerivAt_eq_zero (hv.sub hg)
  exact (sub_eq_zero.mp this).symm

/-- **Section M.L** (MWG, pp. 964-965): the envelope theorem when the parameter enters only the
objective. If `x̄` maximizes `f(·; q̄)` over a constraint set `C` that does not depend on `q`,
`v(q) = sup_{x ∈ C} f(x; q)` is at least `f(x̄; q)`, and `v` and `f(x̄; ·)` are differentiable at
`q̄`, then `∇v(q̄) = ∇_q f(x̄; q̄)`. -/
theorem envelope_objective_only {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set X} {f : X → E → ℝ} {v : E → ℝ} {x : X} {q : E} {fq v' : E →L[ℝ] ℝ}
    (hx : x ∈ C) (hv : ∀ q', ∀ y ∈ C, f y q' ≤ v q') (hvq : v q = f x q)
    (hf : HasFDerivAt (f x) fq q) (hvd : HasFDerivAt v v' q) : v' = fq :=
  (envelope_tangency (Eventually.of_forall fun q' => hv q' x hx) hvq.symm hf hvd).symm

/-- **Equations (M.L.2)-(M.L.3)** (MWG, pp. 964-965). If `v(q) = f(x(q); q)` with `x(·)`
differentiable at `q̄` and the first-order condition `∂f(x(q̄); q̄)/∂x = 0` holds, then
`∇v(q̄) = ∇_q f(x(q̄); q̄)`: only the direct effect matters. -/
theorem equation_M_L_3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F × E → ℝ} {xq : E → F} {q : E}
    {f' : F × E →L[ℝ] ℝ} {x' : E →L[ℝ] F} (hf : HasFDerivAt f f' (xq q, q))
    (hx : HasFDerivAt xq x' q) (hfoc : f'.comp (ContinuousLinearMap.inl ℝ F E) = 0) :
    HasFDerivAt (fun q' => f (xq q', q')) (f'.comp (ContinuousLinearMap.inr ℝ F E)) q := by
  have hφ : HasFDerivAt (fun q' => (xq q', q')) (x'.prod (ContinuousLinearMap.id ℝ E)) q :=
    hx.prodMk (hasFDerivAt_id q)
  have := HasFDerivAt.comp (f := fun q' => (xq q', q')) q hf hφ
  refine this.congr_fderiv ?_
  ext e
  have h1 := congrArg (fun T : F →L[ℝ] ℝ => T (x' e)) hfoc
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    zero_apply] at h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  have : ((x' e, e) : F × E) = (x' e, 0) + (0, e) := by simp
  rw [this, map_add, h1, zero_add]

/-- **Theorem M.L.1 (envelope theorem)** (MWG, pp. 965-966), equations (M.L.4)-(M.L.5), along
a maximizer path. Consider `max f(x; q)` s.t. `g_m(x; q) = b̄_m`, `m = 1, ..., M`. Let `x(·)` be
differentiable at `q̄`, feasible near `q̄` (`g(x(q); q) = b̄`), with `v(q) = f(x(q); q)` near `q̄`,
and let `λ` satisfy the first-order conditions (M.K.2) at `x(q̄)`:
`∇_x f = ∑ λ_m ∇_x g_m`. Then `∇v(q̄) = ∇_q f(x(q̄); q̄) - ∑ λ_m ∇_q g_m(x(q̄); q̄)`. -/
theorem theorem_M_L_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M : ℕ} {f : F × E → ℝ}
    {g : Fin M → F × E → ℝ} {b : Fin M → ℝ} {v : E → ℝ} {xq : E → F} {q : E}
    {f' : F × E →L[ℝ] ℝ} {g' : Fin M → F × E →L[ℝ] ℝ} {x' : E →L[ℝ] F} {lam : Fin M → ℝ}
    (hf : HasFDerivAt f f' (xq q, q)) (hg : ∀ m, HasFDerivAt (g m) (g' m) (xq q, q))
    (hx : HasFDerivAt xq x' q) (hfeas : ∀ᶠ q' in 𝓝 q, ∀ m, g m (xq q', q') = b m)
    (hv : ∀ᶠ q' in 𝓝 q, v q' = f (xq q', q'))
    (hfoc : f'.comp (ContinuousLinearMap.inl ℝ F E) =
      ∑ m, lam m • (g' m).comp (ContinuousLinearMap.inl ℝ F E)) :
    HasFDerivAt v (f'.comp (ContinuousLinearMap.inr ℝ F E) -
      ∑ m, lam m • (g' m).comp (ContinuousLinearMap.inr ℝ F E)) q := by
  have hφ : HasFDerivAt (fun q' => (xq q', q')) (x'.prod (ContinuousLinearMap.id ℝ E)) q :=
    hx.prodMk (hasFDerivAt_id q)
  have hfc := HasFDerivAt.comp (f := fun q' => (xq q', q')) q hf hφ
  -- each constraint is constant along the path, so its total derivative vanishes
  have hgc : ∀ m, (g' m).comp (x'.prod (ContinuousLinearMap.id ℝ E)) = 0 := by
    intro m
    have h1 := HasFDerivAt.comp (f := fun q' => (xq q', q')) q (hg m) hφ
    have h2 : HasFDerivAt (fun q' => g m (xq q', q')) (0 : E →L[ℝ] ℝ) q :=
      (hasFDerivAt_const (b m) q).congr_of_eventuallyEq
        (hfeas.mono fun q' h => h m)
    exact h1.unique h2
  apply (hfc.congr_of_eventuallyEq hv).congr_fderiv
  ext e
  have hsplit : ((x' e, e) : F × E) = (x' e, 0) + (0, e) := by simp
  have hf1 := congrArg (fun T : F →L[ℝ] ℝ => T (x' e)) hfoc
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hf1
  have hg1 : ∀ m, g' m (x' e, 0) = -(g' m (0, e)) := by
    intro m
    have := congrArg (fun T : E →L[ℝ] ℝ => T e) (hgc m)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] at this
    rw [hsplit, map_add] at this
    linarith
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, sub_apply, ContinuousLinearMap.inr_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [hsplit, map_add, hf1]
  simp only [hg1, mul_neg, Finset.sum_neg_distrib]
  ring

end MWG.ClassicalDemand
