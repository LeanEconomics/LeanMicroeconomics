/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.Basic
import MWGConsumerChoice.AppendixMA
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Duality: a mathematical introduction

MWG, Section 3.F, pp. 63-67. Half-spaces and hyperplanes, the support function
`μ_K(p) = inf {p·x : x ∈ K}` (Definition 3.F.1) and the duality theorem (Proposition 3.F.1).

* The book lets `μ_K(p) = -∞`. `supportFnE` is that extended-real function; `supportFn` is its
  real-valued version (Lean's `sInf` of an unbounded set is `0`), equal to `supportFnE` where
  `p·x` is bounded below on `K` (`supportFnE_eq_coe`, `supportFnE_eq_bot`).
* A closed convex set is the intersection of the half-spaces containing it, and for any `K`
  that intersection is the closed convex hull (`exercise_3_F_1`, `halfspace_inter_eq_closure`).
  A nonconvex closed set has a point outside it that cannot be separated (`exercise_3_F_2`).
* `μ_K` is homogeneous of degree one and concave (`supportFn_smul`, `supportFn_concaveOn`).
* The duality theorem. "Differentiable at `p̄`" for the extended-real `μ_K` means finite near
  `p̄` and differentiable there (`SupportDifferentiableAt`). For a nonempty closed **convex**
  `K`, a unique minimizer `x̄` at `p̄` exists iff `μ_K` is differentiable at `p̄`, and then
  `∇μ_K(p̄) = x̄` (`proposition_3_F_1`). The direction "differentiable ⇒ unique minimizer" holds
  for every nonempty closed `K` (`duality_unique_of_differentiable`), as does footnote 14. The
  converse is false for nonconvex closed sets, although the book states the theorem for all
  closed sets (`proposition_3_F_1_nonconvex_counterexample`; correction B1).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Section 3.F** (MWG, p. 64). The half-space `{x ∈ ℝ^L : p·x ≥ c}` with normal `p`. -/
def halfSpace (p : Fin L → ℝ) (c : ℝ) : Set (Fin L → ℝ) := {x | c ≤ p ⬝ᵥ x}

/-- **Section 3.F** (MWG, p. 64). The hyperplane `{x ∈ ℝ^L : p·x = c}`, the boundary of
`halfSpace p c`. -/
def hyperplane (p : Fin L → ℝ) (c : ℝ) : Set (Fin L → ℝ) := {x | p ⬝ᵥ x = c}

/-- **Section 3.F** (MWG, p. 64). The normal `p` is orthogonal to the hyperplane:
`p·x = p·x' = c` implies `p·(x - x') = 0`. -/
theorem hyperplane_normal {p x x' : Fin L → ℝ} {c : ℝ} (hx : x ∈ hyperplane p c)
    (hx' : x' ∈ hyperplane p c) : p ⬝ᵥ (x - x') = 0 := by
  simp only [hyperplane, Set.mem_ofPred_eq] at hx hx'
  rw [dotProduct_sub, hx, hx', sub_self]

/-- **Section 3.F** (MWG, p. 64). Half-spaces are convex. -/
theorem convex_halfSpace (p : Fin L → ℝ) (c : ℝ) : Convex ℝ (halfSpace p c) := by
  intro x hx y hy a b ha hb hab
  simp only [halfSpace, Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at *
  have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- **Section 3.F** (MWG, p. 64). Hyperplanes are convex. -/
theorem convex_hyperplane (p : Fin L → ℝ) (c : ℝ) : Convex ℝ (hyperplane p c) := by
  intro x hx y hy a b _ _ hab
  simp only [hyperplane, Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at *
  rw [hx, hy, ← add_mul, hab, one_mul]

/-- **Section 3.F** (MWG, p. 64). Half-spaces are closed. -/
theorem isClosed_halfSpace (p : Fin L → ℝ) (c : ℝ) : IsClosed (halfSpace p c) :=
  isClosed_le continuous_const (by fun_prop)

/-- **Section 3.F** (MWG, p. 63). The intersection of two convex sets is convex. -/
theorem convex_inter_section_3_F {K K' : Set (Fin L → ℝ)} (hK : Convex ℝ K)
    (hK' : Convex ℝ K') : Convex ℝ (K ∩ K') := hK.inter hK'

/-- The continuous linear functional `q ↦ g·q`, whose gradient is `g`. -/
def dualityDotCLM (g : Fin L → ℝ) : (Fin L → ℝ) →L[ℝ] ℝ :=
  ∑ l, g l • ContinuousLinearMap.proj l

/-- `dualityDotCLM g q = g·q`. -/
theorem dualityDotCLM_apply (g q : Fin L → ℝ) : dualityDotCLM g q = g ⬝ᵥ q := by
  simp [dualityDotCLM, dotProduct]

/-- The gradient of `q ↦ g·q` is `g`. -/
theorem gradientVec_dualityDotCLM (g : Fin L → ℝ) : gradientVec (dualityDotCLM g) = g := by
  funext l
  simp [gradientVec, dualityDotCLM_apply, dotProduct, Pi.single_apply]

/-- A continuous linear functional is `q ↦ g·q` for its gradient `g`. -/
theorem dualityDotCLM_gradientVec (f : (Fin L → ℝ) →L[ℝ] ℝ) :
    dualityDotCLM (gradientVec f) = f := by
  ext q
  rw [dualityDotCLM_apply, ← fderiv_apply_eq_gradient_dot]

/-- `q ↦ g·q` determines `g`. -/
theorem dualityDotCLM_injective {g g' : Fin L → ℝ} (h : dualityDotCLM g = dualityDotCLM g') :
    g = g' := by
  rw [← gradientVec_dualityDotCLM g, h, gradientVec_dualityDotCLM]

/-- `q ↦ g·q` has derivative `q ↦ g·q`. -/
theorem duality_hasFDerivAt_dot_left (g p : Fin L → ℝ) :
    HasFDerivAt (fun q => q ⬝ᵥ g) (dualityDotCLM g) p := by
  have : (fun q => q ⬝ᵥ g) = dualityDotCLM g := by
    funext q
    rw [dualityDotCLM_apply, dotProduct_comm]
  rw [this]
  exact (dualityDotCLM g).hasFDerivAt

/-- The dot product is bounded by `L` times the product of the sup norms. -/
theorem duality_abs_dotProduct_le (a b : Fin L → ℝ) : |a ⬝ᵥ b| ≤ L * (‖a‖ * ‖b‖) := by
  unfold dotProduct
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin L, ‖a‖ * ‖b‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have h1 := norm_le_pi_norm a i
        have h2 := norm_le_pi_norm b i
        rw [Real.norm_eq_abs] at h1 h2
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = L * (‖a‖ * ‖b‖) := by simp

/-- A continuous linear functional on `ℝ^L` is `x ↦ p·x` for some `p`. -/
theorem duality_exists_dot_of_clm (f : (Fin L → ℝ) →L[ℝ] ℝ) : ∃ p : Fin L → ℝ, ∀ x, f x = p ⬝ᵥ x :=
  ⟨gradientVec f, fun x => fderiv_apply_eq_gradient_dot f x⟩

/-- **Section 3.F** (MWG, p. 64), the separating hyperplane theorem in the form used there:
for a closed convex `K` and `x̄ ∉ K` there are `p` and `c` with `p·x̄ < c ≤ p·x` on `K`. -/
theorem separation_section_3_F {K : Set (Fin L → ℝ)} (hK : IsClosed K) (hKc : Convex ℝ K)
    {x : Fin L → ℝ} (hx : x ∉ K) : ∃ p : Fin L → ℝ, ∃ c : ℝ, p ⬝ᵥ x < c ∧ ∀ y ∈ K, c ≤ p ⬝ᵥ y := by
  obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed hKc hK hx
  obtain ⟨p, hp⟩ := duality_exists_dot_of_clm f
  exact ⟨p, u, by rw [← hp]; exact hfx, fun y hy => by rw [← hp]; exact (hfK y hy).le⟩

/-- **Definition 3.F.1** (MWG, p. 64). The support function `μ_K(p) = inf {p·x : x ∈ K}`,
real-valued: it agrees with the book's extended-real `supportFnE` wherever `p·x` is bounded
below on `K`. -/
noncomputable def supportFn (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) : ℝ :=
  sInf ((fun x => p ⬝ᵥ x) '' K)

/-- **Definition 3.F.1** (MWG, pp. 64-65). The support function with values in `[-∞, ∞]`:
`μ_K(p) = -∞` when `p·x` is unbounded below on `K` (p. 65). -/
noncomputable def supportFnE (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) : EReal :=
  ⨅ x ∈ K, ((p ⬝ᵥ x : ℝ) : EReal)

/-- The minimizing set `{x ∈ K : p·x ≤ p·y for all y ∈ K}`. -/
def supportArgmin (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ K ∧ ∀ y ∈ K, p ⬝ᵥ x ≤ p ⬝ᵥ y}

/-- Where `p·x` is bounded below on a nonempty `K`, the two support functions agree. -/
theorem supportFnE_eq_coe {K : Set (Fin L → ℝ)} (hne : K.Nonempty) {p : Fin L → ℝ}
    (hb : BddBelow ((fun x => p ⬝ᵥ x) '' K)) : supportFnE K p = (supportFn K p : EReal) := by
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    have hr1' : supportFn K p < r := EReal.coe_lt_coe_iff.mp hr1
    have : r ≤ supportFn K p := by
      apply le_csInf (hne.image _)
      rintro _ ⟨x, hx, rfl⟩
      have h3 : (r : EReal) < (p ⬝ᵥ x : ℝ) := hr2.trans_le (iInf₂_le x hx)
      exact (EReal.coe_lt_coe_iff.mp h3).le
    linarith
  · refine le_iInf₂ fun x hx => ?_
    exact EReal.coe_le_coe_iff.mpr (csInf_le hb ⟨x, hx, rfl⟩)

/-- **Section 3.F** (MWG, p. 65). Where `p·x` is unbounded below on `K`, `μ_K(p) = -∞`. -/
theorem supportFnE_eq_bot {K : Set (Fin L → ℝ)} {p : Fin L → ℝ}
    (hb : ¬ BddBelow ((fun x => p ⬝ᵥ x) '' K)) : supportFnE K p = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  rw [not_bddBelow_iff] at hb
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hb r
  exact (iInf₂_le x hx).trans_lt (EReal.coe_lt_coe_iff.mpr hlt)

/-- `p·x̄ = μ_K(p)` (extended-real) with `x̄ ∈ K` exactly when `x̄` is a minimizer. -/
theorem eq_supportFnE_iff {K : Set (Fin L → ℝ)} {p x : Fin L → ℝ} (hx : x ∈ K) :
    ((p ⬝ᵥ x : ℝ) : EReal) = supportFnE K p ↔ x ∈ supportArgmin K p := by
  constructor
  · intro h
    refine ⟨hx, fun y hy => ?_⟩
    have : ((p ⬝ᵥ x : ℝ) : EReal) ≤ (p ⬝ᵥ y : ℝ) := h ▸ iInf₂_le y hy
    exact EReal.coe_le_coe_iff.mp this
  · rintro ⟨-, hmin⟩
    exact le_antisymm (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.mpr (hmin y hy))
      (iInf₂_le x hx)

/-- A minimizer gives the value of the real support function. -/
theorem supportFn_eq_of_mem_argmin {K : Set (Fin L → ℝ)} {p x : Fin L → ℝ}
    (hx : x ∈ supportArgmin K p) : supportFn K p = p ⬝ᵥ x := by
  apply IsLeast.csInf_eq
  exact ⟨⟨x, hx.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hx.2 y hy⟩

/-- `μ_K(p) ≤ p·x` for `x ∈ K` when `p·x` is bounded below on `K`. -/
theorem supportFn_le {K : Set (Fin L → ℝ)} {p x : Fin L → ℝ}
    (hb : BddBelow ((fun x => p ⬝ᵥ x) '' K)) (hx : x ∈ K) : supportFn K p ≤ p ⬝ᵥ x :=
  csInf_le hb ⟨x, hx, rfl⟩

/-- A lower bound on `K` bounds the support function. -/
theorem le_supportFn {K : Set (Fin L → ℝ)} (hne : K.Nonempty) {p : Fin L → ℝ} {c : ℝ}
    (h : ∀ x ∈ K, c ≤ p ⬝ᵥ x) : c ≤ supportFn K p := by
  apply le_csInf (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

open scoped Pointwise in
/-- **Section 3.F** (MWG, p. 65). `μ_K` is homogeneous of degree one:
`μ_K(αp) = α μ_K(p)` for `α ≥ 0`. -/
theorem supportFn_smul (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    supportFn K (α • p) = α * supportFn K p := by
  unfold supportFn
  have h : (fun x => (α • p) ⬝ᵥ x) '' K = α • ((fun x => p ⬝ᵥ x) '' K) := by
    rw [← Set.image_smul, Set.image_image]
    simp only [smul_dotProduct]
  rw [h, Real.sInf_smul_of_nonneg hα, smul_eq_mul]

/-- The set of `p` at which `μ_K(p)` is finite is convex. -/
theorem convex_supportDomain (K : Set (Fin L → ℝ)) :
    Convex ℝ {p : Fin L → ℝ | BddBelow ((fun x => p ⬝ᵥ x) '' K)} := by
  intro p hp p' hp' a b ha hb hab
  obtain ⟨m, hm⟩ := hp
  obtain ⟨m', hm'⟩ := hp'
  refine ⟨a * m + b * m', ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hm ⟨x, hx, rfl⟩
  have h2 := hm' ⟨x, hx, rfl⟩
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **Section 3.F** (MWG, p. 65; Figure 3.F.3). The support function of a nonempty set is
concave on the convex set where it is finite: it is the lower envelope of the linear functions
`p ↦ p·x`, `x ∈ K`. (The book assumes the infimum attained; this is not needed.) -/
theorem supportFn_concaveOn {K : Set (Fin L → ℝ)} (hne : K.Nonempty) :
    ConcaveOn ℝ {p : Fin L → ℝ | BddBelow ((fun x => p ⬝ᵥ x) '' K)} (supportFn K) := by
  refine ⟨convex_supportDomain K, fun p hp p' hp' a b ha hb hab => ?_⟩
  apply le_supportFn hne
  intro x hx
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (supportFn_le hp hx) ha)
    (mul_le_mul_of_nonneg_left (supportFn_le hp' hx) hb)

/-- **Section 3.F** (MWG, p. 65). For every `p`, `{x : p·x ≥ μ_K(p)}` contains `K`. -/
theorem subset_supportHalfSpace (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    K ⊆ {x | supportFnE K p ≤ ((p ⬝ᵥ x : ℝ) : EReal)} :=
  fun x hx => show supportFnE K p ≤ _ from iInf₂_le x hx

/-- **Section 3.F** (MWG, pp. 64-65). For any `K ⊆ ℝ^L`, the intersection of the half-spaces
`{x : p·x ≥ μ_K(p)}` over all `p` is the closed convex hull of `K`, the smallest closed convex
set containing `K`. -/
theorem halfspace_inter_eq_closure (K : Set (Fin L → ℝ)) :
    {x | ∀ p, supportFnE K p ≤ ((p ⬝ᵥ x : ℝ) : EReal)} = closure (convexHull ℝ K) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxK
    obtain ⟨p, c, hpx, hc⟩ := separation_section_3_F isClosed_closure
      (convex_convexHull ℝ K).closure hxK
    have h1 : (c : EReal) ≤ supportFnE K p :=
      le_iInf₂ fun y hy => EReal.coe_le_coe_iff.mpr
        (hc y (subset_closure (subset_convexHull ℝ K hy)))
    have h2 := h1.trans (hx p)
    exact absurd (EReal.coe_le_coe_iff.mp h2) (not_le.mpr hpx)
  · have hclosed : IsClosed {x : Fin L → ℝ | ∀ p, supportFnE K p ≤ ((p ⬝ᵥ x : ℝ) : EReal)} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun p => ?_
      exact isClosed_le continuous_const
        (continuous_coe_real_ereal.comp (continuous_const.dotProduct continuous_id))
    have hconv : Convex ℝ {x : Fin L → ℝ | ∀ p, supportFnE K p ≤ ((p ⬝ᵥ x : ℝ) : EReal)} := by
      intro x hx y hy a b ha hb hab p
      have hx' := hx p
      have hy' := hy p
      change supportFnE K p ≤ _
      rcases K.eq_empty_or_nonempty with hK | hne
      · simp [supportFnE, hK] at hx'
      by_cases hbd : BddBelow ((fun x => p ⬝ᵥ x) '' K)
      · rw [supportFnE_eq_coe hne hbd] at hx' hy' ⊢
        have h1 := EReal.coe_le_coe_iff.mp hx'
        have h2 := EReal.coe_le_coe_iff.mp hy'
        apply EReal.coe_le_coe_iff.mpr
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        have hc : supportFn K p = a * supportFn K p + b * supportFn K p := by
          rw [← add_mul, hab, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
      · rw [supportFnE_eq_bot hbd]
        exact bot_le
    refine closure_minimal ?_ hclosed
    exact convexHull_min (fun x hx p => subset_supportHalfSpace K p hx) hconv

/-- **Exercise 3.F.1** (MWG, pp. 65, 99). A closed convex set `K ⊆ ℝ^L` equals the
intersection of the half-spaces that contain it: `K = {x : p·x ≥ μ_K(p) for every p}`. -/
theorem exercise_3_F_1 {K : Set (Fin L → ℝ)} (hK : IsClosed K) (hKc : Convex ℝ K) :
    K = {x | ∀ p, supportFnE K p ≤ ((p ⬝ᵥ x : ℝ) : EReal)} := by
  rw [halfspace_inter_eq_closure, hKc.convexHull_eq, hK.closure_eq]

/-- **Exercise 3.F.1** (MWG, p. 99), in terms of half-spaces: for `L ≥ 1`, a closed convex
`K ⊆ ℝ^L` is the intersection of all half-spaces `{x : p·x ≥ c}`, `p ≠ 0`, that contain it.
(For `L = 0` there is no `p ≠ 0` and `K = ∅` is not such an intersection.) -/
theorem exercise_3_F_1_halfspaces (hL : 0 < L) {K : Set (Fin L → ℝ)} (hK : IsClosed K)
    (hKc : Convex ℝ K) : K = ⋂₀ {H | ∃ p c, p ≠ 0 ∧ H = halfSpace p c ∧ K ⊆ H} := by
  apply Set.Subset.antisymm
  · intro x hx H ⟨p, c, _, hH, hKH⟩
    exact hKH hx
  · intro x hx
    by_contra hxK
    obtain ⟨p, c, hpx, hc⟩ := separation_section_3_F hK hKc hxK
    rcases K.eq_empty_or_nonempty with hK0 | ⟨y, hy⟩
    · subst hK0
      set e : Fin L → ℝ := Pi.single ⟨0, hL⟩ 1 with he_def
      have he : e ≠ 0 := by
        intro h
        have := congrFun h ⟨0, hL⟩
        simp [e] at this
      have := hx (halfSpace e (e ⬝ᵥ x + 1)) ⟨e, _, he, rfl, Set.empty_subset _⟩
      simp only [halfSpace, Set.mem_ofPred_eq] at this
      linarith
    · have hp : p ≠ 0 := by
        rintro rfl
        have := hc y hy
        simp only [zero_dotProduct] at this hpx
        linarith
      have := hx (halfSpace p c) ⟨p, c, hp, rfl, fun y hy => hc y hy⟩
      exact absurd (show c ≤ p ⬝ᵥ x from this) (not_le.mpr hpx)

/-- **Exercise 3.F.2** (MWG, p. 99). If `K` is not convex (closed or not), some `x ∉ K`
cannot be separated from `K`: every half-space `{p·y ≥ c}` containing `K` also contains `x`. -/
theorem exercise_3_F_2 {K : Set (Fin L → ℝ)} (hKc : ¬ Convex ℝ K) :
    ∃ x ∉ K, ¬ ∃ p : Fin L → ℝ, ∃ c : ℝ, p ⬝ᵥ x < c ∧ ∀ y ∈ K, c ≤ p ⬝ᵥ y := by
  have hsub : K ⊆ closure (convexHull ℝ K) := subset_closure.trans' (subset_convexHull ℝ K)
  have hne : ¬ closure (convexHull ℝ K) ⊆ K := by
    intro h
    exact hKc ((Set.Subset.antisymm h hsub) ▸ (convex_convexHull ℝ K).closure)
  obtain ⟨x, hxC, hxK⟩ := Set.not_subset.mp hne
  refine ⟨x, hxK, ?_⟩
  rintro ⟨p, c, hpx, hc⟩
  rw [← halfspace_inter_eq_closure] at hxC
  have h1 : (c : EReal) ≤ supportFnE K p :=
    le_iInf₂ fun y hy => EReal.coe_le_coe_iff.mpr (hc y hy)
  exact absurd (EReal.coe_le_coe_iff.mp (h1.trans (hxC p))) (not_le.mpr hpx)

/-- **Exercise 3.F.2** (MWG, p. 99), the graphic example: the separating hyperplane theorem
fails for the nonconvex closed set `K = {0, 2}` in `ℝ`: `1 ∉ K` cannot be separated. -/
theorem exercise_3_F_2_example :
    (1 : Fin 1 → ℝ) ∉ ({0, 2} : Set (Fin 1 → ℝ)) ∧
      ¬ ∃ p : Fin 1 → ℝ, ∃ c : ℝ, p ⬝ᵥ 1 < c ∧ ∀ y ∈ ({0, 2} : Set (Fin 1 → ℝ)),
        c ≤ p ⬝ᵥ y := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with h | h
    · have := congrFun h 0
      simp at this
    · have := congrFun (show (1 : Fin 1 → ℝ) = 2 from h) 0
      norm_num at this
  · rintro ⟨p, c, hp, hc⟩
    have h0 := hc 0 (by simp)
    have h2 := hc 2 (by simp)
    simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Pi.one_apply, mul_one, Pi.zero_apply, mul_zero] at hp h0 h2
    have : (2 : Fin 1 → ℝ) 0 = 2 := rfl
    rw [this] at h2
    linarith

/-- **Proposition 3.F.1** (MWG, p. 66): the meaning of "`μ_K` is differentiable at `p̄`" for
the extended-real support function: it is finite near `p̄` and its real version is
differentiable at `p̄`. -/
def SupportDifferentiableAt (K : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Prop :=
  (∀ᶠ q in 𝓝 p, BddBelow ((fun x => q ⬝ᵥ x) '' K)) ∧ DifferentiableAt ℝ (supportFn K) p

/-- **Footnote 14** and the argument on p. 66 (MWG). If `μ_K` is finite near `p̄`, has
derivative `f'` at `p̄`, and `x̄` is a minimizer at `p̄`, then `f'` is `p ↦ x̄·p`, i.e.
`∇μ_K(p̄) = x̄`: `ξ(p) = p·x̄ - μ_K(p) ≥ 0` has a minimum at `p̄`. -/
theorem footnote_3_F_14 {K : Set (Fin L → ℝ)} {p x : Fin L → ℝ}
    (hb : ∀ᶠ q in 𝓝 p, BddBelow ((fun x => q ⬝ᵥ x) '' K)) {f' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt (supportFn K) f' p) (hx : x ∈ supportArgmin K p) :
    f' = dualityDotCLM x := by
  have hmin : IsLocalMin (fun q => q ⬝ᵥ x - supportFn K q) p := by
    filter_upwards [hb] with q hq
    rw [supportFn_eq_of_mem_argmin hx, dotProduct_comm, sub_self]
    exact sub_nonneg.mpr (supportFn_le hq hx.1)
  have hd := (duality_hasFDerivAt_dot_left x p).sub hf
  have := hmin.hasFDerivAt_eq_zero hd
  exact (sub_eq_zero.mp this).symm

/-- If `μ_K` is finite near `p̄`, the near-minimizers of `p̄·x` on `K` are bounded. -/
theorem supportFn_bounded_sublevel {K : Set (Fin L → ℝ)}
    {p : Fin L → ℝ} (hb : ∀ᶠ q in 𝓝 p, BddBelow ((fun x => q ⬝ᵥ x) '' K)) (c : ℝ) :
    ∃ R : ℝ, ∀ y ∈ K, p ⬝ᵥ y ≤ c → ∀ l, |y l| ≤ R := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hb
  set d := δ / 2 with hd
  have hd0 : 0 < d := by positivity
  have hmem : ∀ (l : Fin L) (s : ℝ), |s| = 1 →
      BddBelow ((fun x => (p + (s * d) • Pi.single l 1) ⬝ᵥ x) '' K) := by
    intro l s hs
    apply hball
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_mul, Real.norm_eq_abs, hs,
      Real.norm_eq_abs, abs_of_pos hd0]
    have : ‖(Pi.single l 1 : Fin L → ℝ)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      by_cases h : i = l
      · subst h; simp
      · simp [h]
    calc 1 * d * ‖(Pi.single l 1 : Fin L → ℝ)‖ ≤ 1 * d * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ < δ := by rw [hd]; linarith
  choose m hm using fun (l : Fin L) (s : {s : ℝ // |s| = 1}) => hmem l s.1 s.2
  have hm' : ∀ l (s : {s : ℝ // |s| = 1}) y, y ∈ K →
      m l s ≤ p ⬝ᵥ y + s.1 * d * y l := by
    intro l s y hy
    have := hm l s ⟨y, hy, rfl⟩
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul] at this
    linarith
  let M : ℝ := ∑ l, (|m l ⟨1, by simp⟩| + |m l ⟨-1, by simp⟩|)
  refine ⟨(M + |c|) / d, fun y hy hyc l => ?_⟩
  have hsum := Finset.single_le_sum
    (f := fun l => |m l ⟨1, by simp⟩| + |m l ⟨-1, by simp⟩|)
    (fun _ _ => by positivity) (Finset.mem_univ l)
  have hM1 : |m l ⟨1, by simp⟩| ≤ M := by
    have h2 := abs_nonneg (m l ⟨-1, by simp⟩)
    linarith
  have hM2 : |m l ⟨-1, by simp⟩| ≤ M := by
    have h2 := abs_nonneg (m l ⟨1, by simp⟩)
    linarith
  have h1 := hm' l ⟨1, by simp⟩ y hy
  have h2 := hm' l ⟨-1, by simp⟩ y hy
  have hc1 := le_abs_self c
  have hm1 := neg_abs_le (m l ⟨1, by simp⟩)
  have hm2 := neg_abs_le (m l ⟨-1, by simp⟩)
  rw [le_div_iff₀ hd0]
  rcases abs_cases (y l) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> push_cast at h1 h2 <;> nlinarith

/-- **Proposition 3.F.1** (MWG, p. 66), "if" part of the uniqueness claim read in the
direction proved for every closed set: if `μ_K` is differentiable at `p̄` (finite nearby),
there is a unique minimizer `x̄ ∈ K` with `p̄·x̄ = μ_K(p̄)`, and `∇μ_K(p̄) = x̄`. -/
theorem duality_unique_of_differentiable {K : Set (Fin L → ℝ)} (hK : IsClosed K)
    (hne : K.Nonempty) {p : Fin L → ℝ} (hd : SupportDifferentiableAt K p) :
    ∃ x, x ∈ supportArgmin K p ∧ (∀ y ∈ supportArgmin K p, y = x) ∧
      fderiv ℝ (supportFn K) p = dualityDotCLM x := by
  obtain ⟨hb, hdiff⟩ := hd
  have hb0 : BddBelow ((fun x => p ⬝ᵥ x) '' K) := hb.self_of_nhds
  set c := supportFn K p + 1
  obtain ⟨R, hR⟩ := supportFn_bounded_sublevel hb c
  set S := K ∩ {y | p ⬝ᵥ y ≤ c}
  have hSc : IsCompact S := by
    apply (isCompact_closedBall (0 : Fin L → ℝ) (max R 0)).of_isClosed_subset
    · exact hK.inter (isClosed_le (by fun_prop) continuous_const)
    · intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      intro l
      rw [Real.norm_eq_abs]
      exact (hR y hy.1 hy.2 l).trans (le_max_left _ _)
  have hSne : S.Nonempty := by
    have hlt : supportFn K p < c := by linarith
    obtain ⟨_, ⟨y, hy, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt (hne.image _) hlt
    exact ⟨y, hy, hlt'.le⟩
  obtain ⟨x, hxS, hxmin⟩ :=
    hSc.exists_isMinOn hSne (by fun_prop : Continuous fun y => p ⬝ᵥ y).continuousOn
  have hxarg : x ∈ supportArgmin K p := by
    refine ⟨hxS.1, fun y hy => ?_⟩
    by_cases hyc : p ⬝ᵥ y ≤ c
    · exact hxmin ⟨hy, hyc⟩
    · exact hxS.2.trans (not_le.mp hyc).le
  have hgrad : ∀ y ∈ supportArgmin K p, fderiv ℝ (supportFn K) p = dualityDotCLM y :=
    fun y hy => footnote_3_F_14 hb hdiff.hasFDerivAt hy
  refine ⟨x, hxarg, fun y hy => ?_, hgrad x hxarg⟩
  exact dualityDotCLM_injective ((hgrad y hy).symm.trans (hgrad x hxarg))

/-- The key estimate for the converse of the duality theorem: if `x̄` is the unique minimizer
of `p̄·x` on a closed convex `K`, then for every `ε > 0` and `p` near `p̄`,
`p·y ≥ p·x̄ - ε‖p - p̄‖` on `K`. -/
theorem duality_key_estimate {K : Set (Fin L → ℝ)} (hK : IsClosed K) (hKc : Convex ℝ K)
    {p₀ x : Fin L → ℝ} (hx : x ∈ K) (huniq : ∀ y ∈ K, y ≠ x → p₀ ⬝ᵥ x < p₀ ⬝ᵥ y) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, p ⬝ᵥ x - ε * ‖p - p₀‖ ≤ p ⬝ᵥ y := by
  set c := ε / (L + 1) with hc
  have hc0 : 0 < c := by positivity
  have hLc : (L : ℝ) * c ≤ ε := by
    rw [hc, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set S := K ∩ Metric.sphere x c
  have hSc : IsCompact S := (isCompact_sphere x c).inter_left hK
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ S, m ≤ p₀ ⬝ᵥ (z - x) := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨1, one_pos, fun z hz => by rw [hS] at hz; exact absurd hz (Set.notMem_empty z)⟩
    obtain ⟨z0, hz0, hzmin⟩ := hSc.exists_isMinOn hS
      (by fun_prop : Continuous fun z => p₀ ⬝ᵥ (z - x)).continuousOn
    have hne : z0 ≠ x := by
      intro h
      have := hz0.2
      rw [h, Metric.mem_sphere, dist_self] at this
      exact hc0.ne this
    refine ⟨p₀ ⬝ᵥ (z0 - x), ?_, fun z hz => hzmin hz⟩
    rw [dotProduct_sub, sub_pos]
    exact huniq z0 hz0.1 hne
  set δ := m / (L * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [Metric.ball_mem_nhds p₀ hδ0] with p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp
  intro y hy
  have hsplit : p ⬝ᵥ (y - x) = p₀ ⬝ᵥ (y - x) + (p - p₀) ⬝ᵥ (y - x) := by
    rw [sub_dotProduct]; ring
  have hbound := duality_abs_dotProduct_le (p - p₀) (y - x)
  have hnp := norm_nonneg (p - p₀)
  suffices h : -(ε * ‖p - p₀‖) ≤ p ⬝ᵥ (y - x) by
    rw [dotProduct_sub] at h; linarith
  by_cases hyx : ‖y - x‖ ≤ c
  · have h0 : 0 ≤ p₀ ⬝ᵥ (y - x) := by
      by_cases hyx' : y = x
      · subst hyx'; simp
      · rw [dotProduct_sub, sub_nonneg]; exact (huniq y hy hyx').le
    have : (L : ℝ) * (‖p - p₀‖ * ‖y - x‖) ≤ ε * ‖p - p₀‖ := by
      calc (L : ℝ) * (‖p - p₀‖ * ‖y - x‖) ≤ L * (‖p - p₀‖ * c) := by
            gcongr
        _ = (L * c) * ‖p - p₀‖ := by ring
        _ ≤ ε * ‖p - p₀‖ := mul_le_mul_of_nonneg_right hLc hnp
    have := neg_abs_le ((p - p₀) ⬝ᵥ (y - x))
    linarith
  · rw [not_le] at hyx
    have hn0 : 0 < ‖y - x‖ := hc0.trans hyx
    set t := c / ‖y - x‖ with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hn0]; exact hyx.le
    have hz : x + t • (y - x) ∈ S := by
      refine ⟨hKc.add_smul_sub_mem hx hy ⟨ht0.le, ht1⟩, ?_⟩
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, ht, div_mul_cancel₀ _ hn0.ne']
    have hmz := hm _ hz
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at hmz
    have hyx_eq : ‖y - x‖ = c / t := by rw [ht, div_div_cancel₀ hc0.ne']
    -- p₀·(y - x) ≥ m / t and |(p - p₀)·(y - x)| ≤ L ‖p - p₀‖ c / t < m / t
    have h1 : m ≤ t * (p₀ ⬝ᵥ (y - x)) := hmz
    have h2 : t * |(p - p₀) ⬝ᵥ (y - x)| ≤ L * ‖p - p₀‖ * c := by
      calc t * |(p - p₀) ⬝ᵥ (y - x)| ≤ t * (L * (‖p - p₀‖ * ‖y - x‖)) :=
            mul_le_mul_of_nonneg_left hbound ht0.le
        _ = L * ‖p - p₀‖ * (t * ‖y - x‖) := by ring
        _ = L * ‖p - p₀‖ * c := by rw [hyx_eq, mul_div_cancel₀ _ ht0.ne']
    have h3 : (L : ℝ) * ‖p - p₀‖ * c < m := by
      have : (L : ℝ) * c * ‖p - p₀‖ ≤ (L * c) * δ :=
        mul_le_mul_of_nonneg_left hp.le (by positivity)
      have h4 : (L : ℝ) * c * δ < m := by
        rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have h5 : 0 ≤ t * (p ⬝ᵥ (y - x)) := by
      rw [hsplit, mul_add]
      have := neg_abs_le ((p - p₀) ⬝ᵥ (y - x))
      nlinarith
    have h6 : 0 ≤ p ⬝ᵥ (y - x) := nonneg_of_mul_nonneg_right (by linarith) ht0
    have : 0 ≤ ε * ‖p - p₀‖ := mul_nonneg hε.le hnp
    linarith

/-- **Proposition 3.F.1** (MWG, p. 66), "only if" part for a closed convex set: if `x̄` is the
unique minimizer at `p̄`, then `μ_K` is finite near `p̄` and differentiable at `p̄` with
`∇μ_K(p̄) = x̄`. -/
theorem duality_differentiable_of_unique {K : Set (Fin L → ℝ)} (hK : IsClosed K)
    (hKc : Convex ℝ K) {p₀ x : Fin L → ℝ} (hx : x ∈ supportArgmin K p₀)
    (huniq : ∀ y ∈ supportArgmin K p₀, y = x) :
    (∀ᶠ q in 𝓝 p₀, BddBelow ((fun x => q ⬝ᵥ x) '' K)) ∧
      HasFDerivAt (supportFn K) (dualityDotCLM x) p₀ := by
  have hstrict : ∀ y ∈ K, y ≠ x → p₀ ⬝ᵥ x < p₀ ⬝ᵥ y := by
    intro y hy hyx
    rcases (hx.2 y hy).lt_or_eq with h | h
    · exact h
    · exact absurd (huniq y ⟨hy, fun z hz => h ▸ hx.2 z hz⟩) hyx
  have hb : ∀ᶠ q in 𝓝 p₀, BddBelow ((fun x => q ⬝ᵥ x) '' K) := by
    filter_upwards [duality_key_estimate hK hKc hx.1 hstrict one_pos] with q hq
    exact ⟨q ⬝ᵥ x - 1 * ‖q - p₀‖, by rintro _ ⟨y, hy, rfl⟩; exact hq y hy⟩
  refine ⟨hb, ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [duality_key_estimate hK hKc hx.1 hstrict hε, hb] with q hq hqb
  have hlo : q ⬝ᵥ x - ε * ‖q - p₀‖ ≤ supportFn K q := le_supportFn ⟨x, hx.1⟩ hq
  have hhi : supportFn K q ≤ q ⬝ᵥ x := supportFn_le hqb hx.1
  rw [supportFn_eq_of_mem_argmin hx, dualityDotCLM_apply, Real.norm_eq_abs, abs_le]
  have : x ⬝ᵥ (q - p₀) = q ⬝ᵥ x - p₀ ⬝ᵥ x := by
    rw [dotProduct_sub, dotProduct_comm x q, dotProduct_comm x p₀]
  rw [this]
  have := mul_nonneg hε.le (norm_nonneg (q - p₀))
  constructor <;> linarith

/-- **Proposition 3.F.1 (the duality theorem)** (MWG, p. 66), for a nonempty closed convex
`K ⊆ ℝ^L`: there is a unique `x̄ ∈ K` with `p̄·x̄ = μ_K(p̄)` if and only if `μ_K` is
differentiable at `p̄`; in that case `∇μ_K(p̄) = x̄`. -/
theorem proposition_3_F_1 {K : Set (Fin L → ℝ)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hne : K.Nonempty) (p₀ : Fin L → ℝ) :
    ((∃! x, x ∈ K ∧ ((p₀ ⬝ᵥ x : ℝ) : EReal) = supportFnE K p₀) ↔
        SupportDifferentiableAt K p₀) ∧
      ∀ x, x ∈ K → ((p₀ ⬝ᵥ x : ℝ) : EReal) = supportFnE K p₀ →
        SupportDifferentiableAt K p₀ → gradientVec (fderiv ℝ (supportFn K) p₀) = x := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨x, ⟨hxK, hx⟩, huniq⟩
    rw [eq_supportFnE_iff hxK] at hx
    obtain ⟨hb, hd⟩ := duality_differentiable_of_unique hK hKc hx fun y hy =>
      huniq y ⟨hy.1, (eq_supportFnE_iff hy.1).mpr hy⟩
    exact ⟨hb, hd.differentiableAt⟩
  · intro hd
    obtain ⟨x, hx, huniq, -⟩ := duality_unique_of_differentiable hK hne hd
    refine ⟨x, ⟨hx.1, (eq_supportFnE_iff hx.1).mpr hx⟩, fun y hy => ?_⟩
    exact huniq y ((eq_supportFnE_iff hy.1).mp hy.2)
  · intro x hxK hx hd
    rw [eq_supportFnE_iff hxK] at hx
    rw [footnote_3_F_14 hd.1 hd.2.hasFDerivAt hx, gradientVec_dualityDotCLM]

/-- The nonconvex closed set `{0} ∪ {x : x₂ = 1}` in `ℝ²` used in correction B1. -/
def dualityCounterexampleSet : Set (Fin 2 → ℝ) := {0} ∪ {x | x 1 = 1}

/-- **Proposition 3.F.1** (MWG, p. 66) fails for nonconvex closed sets (correction B1):
`K = {0} ∪ {x : x₂ = 1}` is nonempty and closed, `0` is the unique minimizer of `p̄·x` for
`p̄ = (0, 1)`, but `μ_K(p) = -∞` at `p = (δ, 1)` for every `δ > 0`, so `μ_K` is not
differentiable at `p̄`. -/
theorem proposition_3_F_1_nonconvex_counterexample :
    IsClosed dualityCounterexampleSet ∧ dualityCounterexampleSet.Nonempty ∧
      ¬ Convex ℝ dualityCounterexampleSet ∧
      (∃! x, x ∈ dualityCounterexampleSet ∧
        ((![0, 1] ⬝ᵥ x : ℝ) : EReal) = supportFnE dualityCounterexampleSet ![0, 1]) ∧
      ¬ SupportDifferentiableAt dualityCounterexampleSet ![0, 1] := by
  have hclosed : IsClosed dualityCounterexampleSet :=
    isClosed_singleton.union (isClosed_eq (continuous_apply 1) continuous_const)
  have hmem0 : (0 : Fin 2 → ℝ) ∈ dualityCounterexampleSet := Or.inl rfl
  have hval : ∀ x : Fin 2 → ℝ, (![0, 1] : Fin 2 → ℝ) ⬝ᵥ x = x 1 := by
    intro x; simp [dotProduct, Fin.sum_univ_two]
  have harg : ∀ x, x ∈ supportArgmin dualityCounterexampleSet ![0, 1] ↔ x = 0 := by
    intro x
    constructor
    · rintro ⟨hx, hmin⟩
      have := hmin 0 hmem0
      rw [hval, hval] at this
      rcases hx with hx | hx
      · exact hx
      · simp only [Set.mem_ofPred_eq] at hx
        simp at this; linarith
    · rintro rfl
      refine ⟨hmem0, fun y hy => ?_⟩
      rw [hval, hval]
      rcases hy with hy | hy
      · rw [Set.mem_singleton_iff] at hy; simp [hy]
      · simp only [Set.mem_ofPred_eq] at hy; simp [hy]
  refine ⟨hclosed, ⟨0, hmem0⟩, ?_, ?_, ?_⟩
  · intro hconv
    have h1 : (![0, 1] : Fin 2 → ℝ) ∈ dualityCounterexampleSet := Or.inr (by simp)
    have := hconv hmem0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    rcases this with h | h
    · have := congrFun h 1; simp at this
    · simp only [Set.mem_ofPred_eq] at h; simp at h
  · refine ⟨0, ⟨hmem0, (eq_supportFnE_iff hmem0).mpr ((harg 0).mpr rfl)⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    exact (harg y).mp ((eq_supportFnE_iff hy).mp hy')
  · rintro ⟨hb, -⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hb
    have hp : dist (![δ / 2, 1] : Fin 2 → ℝ) ![0, 1] < δ := by
      rw [dist_pi_lt_iff hδ]
      intro i
      fin_cases i
      · simp [abs_of_pos hδ]; linarith
      · simpa using hδ
    obtain ⟨b, hb'⟩ := hball hp
    have hmem : (![(b - 2) / (δ / 2), 1] : Fin 2 → ℝ) ∈ dualityCounterexampleSet :=
      Or.inr (by simp)
    have := hb' ⟨_, hmem, rfl⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [mul_div_cancel₀ _ (by positivity)] at this
    linarith

end MWG.ClassicalDemand
