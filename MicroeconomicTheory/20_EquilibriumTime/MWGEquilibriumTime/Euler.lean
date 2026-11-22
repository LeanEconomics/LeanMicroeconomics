/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Tools
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Euler equations, the policy function and the value function (MWG Section 20.D, pp. 749-754)

MWG, Chapter 20, the computation of equilibrium in the `(N+1)`-sector model, pp. 749-754:
(20.D.8)-(20.D.12), Proposition 20.D.7, and Exercises 20.D.6, 20.D.8, 20.D.9 (p. 784).

The capital space is a real normed space `K` (`ℝ^N` in MWG), the admissible region is
`A ⊆ K × K`, `u : K × K → ℝ`, and a path `k : ℕ → K` is admissible from `k̄₀` if `k₀ = k̄₀` and
`(k_t, k_{t+1}) ∈ A` (`Admissible`). The objective used here is
`W(k) = ∑_{t ≥ 0} δ^t u(k_t, k_{t+1})` (`reducedObjective`); MWG's (20.D.8),
`∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)`, is `δ W(k)` (`objective_20_D_8`), so the two problems have the same
solutions. The Euler equations (20.D.9) at the date `t + 1` read
`D₂u(k_t, k_{t+1}) + δ D₁u(k_{t+1}, k_{t+2}) = 0` (`EulerEq`).

* Necessity of the Euler equations at an interior optimum: `euler_of_optimal`.
* **Exercise 20.D.6**: for a concave `u` and an interior path, the Euler equations are necessary
  and sufficient for short-run optimality (`exercise_20_D_6`).
* **Proposition 20.D.7**: a bounded, strictly interior path satisfying the Euler equations is
  optimal (`proposition_20_D_7`).
* Uniqueness of the optimal path under strict concavity (`optimal_unique`).
* (20.D.10): tails of optimal paths are optimal and `k_{t+1} = ψ(k_t)` (`optimal_tail`,
  `policy_20_D_10`).
* (20.D.11): the Bellman equation for `V = sup W` (`bellman_20_D_11`); as printed, for the value
  of (20.D.8), it is off by the factor `δ` (`bellman_20_D_11_printed_false`).
* **Exercise 20.D.8** (`exercise_20_D_8_i`, `exercise_20_D_8_ii`) and **Exercise 20.D.9**
  (`exercise_20_D_9_first`, `exercise_20_D_9_second`).

The gradient inequality for concave functions on a normed space (`concave_le_fderiv_normed`)
reduces to Chapter 15's one-dimensional `MWG.GeneralEquilibriumExamples.concave_le_tangent`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- **The gradient inequality** for a concave function on a convex subset of a real normed
space: `f y ≤ f x + f'(y - x)`. -/
theorem concave_le_fderiv_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x y : E} (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt f f' x) : f y ≤ f x + f' (y - x) := by
  set g : ℝ → ℝ := fun s => f (AffineMap.lineMap x y s) with hg
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap x y) ⁻¹' S := fun s hs =>
    hf.1.lineMap_mem hx hy hs
  have hconc : ConcaveOn ℝ (Set.Icc 0 1) g :=
    (hf.comp_affineMap (AffineMap.lineMap x y)).subset hsub (convex_Icc 0 1)
  have hderiv : HasDerivAt g (f' (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ → E) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f f' (AffineMap.lineMap x y (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]; exact hd
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := MWG.GeneralEquilibriumExamples.concave_le_tangent hconc
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) hderiv
  simpa [hg, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using this

/-- Changing a real sequence at finitely many indices preserves summability. -/
theorem summable_of_eq_off {a a' : ℕ → ℝ} (s : Finset ℕ) (h : ∀ t ∉ s, a' t = a t)
    (ha : Summable a) : Summable a' := by
  have hfin : Summable fun t => if t ∈ s then a' t - a t else 0 :=
    summable_of_ne_finset_zero (s := s) (fun t ht => by simp [ht])
  refine (ha.add hfin).congr fun t => ?_
  by_cases ht : t ∈ s
  · simp [ht]
  · simp [ht, h t ht]

/-- Changing a summable real sequence at finitely many indices changes its sum by the finite
sum of the changes. -/
theorem tsum_sub_eq_of_eq_off {a a' : ℕ → ℝ} (s : Finset ℕ) (h : ∀ t ∉ s, a' t = a t)
    (ha : Summable a) : ∑' t, a' t - ∑' t, a t = ∑ t ∈ s, (a' t - a t) := by
  rw [← (summable_of_eq_off s h ha).tsum_sub ha]
  exact tsum_eq_sum fun t ht => by rw [h t ht, sub_self]

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A capital path is **admissible** from `k̄₀` for the region `A` (MWG, (20.D.8)). -/
def Admissible (A : Set (K × K)) (k₀ : K) (k : ℕ → K) : Prop :=
  k 0 = k₀ ∧ ∀ t, (k t, k (t + 1)) ∈ A

/-- The objective `W(k) = ∑_{t ≥ 0} δ^t u(k_t, k_{t+1})`. -/
noncomputable def reducedObjective (δ : ℝ) (u : K × K → ℝ) (k : ℕ → K) : ℝ :=
  ∑' t, δ ^ t * u (k t, k (t + 1))

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- MWG's objective (20.D.8), `∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)` (with `u(k_{-1}, k₀) = 0`, footnote
12), is `δ W(k)`. -/
theorem objective_20_D_8 (δ : ℝ) (u : K × K → ℝ) (k : ℕ → K) :
    ∑' t, δ ^ (t + 1) * u (k t, k (t + 1)) = δ * reducedObjective δ u k := by
  unfold reducedObjective
  rw [← tsum_mul_left]
  exact tsum_congr fun t => by ring

/-- `k` **solves the planning problem (20.D.8)** from `k̄₀`: it is admissible with a convergent
objective, and no admissible path with a convergent objective does better. -/
def OptimalFrom (A : Set (K × K)) (δ : ℝ) (u : K × K → ℝ) (k₀ : K) (k : ℕ → K) : Prop :=
  Admissible A k₀ k ∧ Summable (fun t => δ ^ t * u (k t, k (t + 1))) ∧
    ∀ k', Admissible A k₀ k' → Summable (fun t => δ ^ t * u (k' t, k' (t + 1))) →
      reducedObjective δ u k' ≤ reducedObjective δ u k

/-- **The Euler equations (20.D.9)** (MWG, p. 750), with `Du t` the derivative of `u` at
`(k_t, k_{t+1})`: `D₂u(k_t, k_{t+1}) + δ D₁u(k_{t+1}, k_{t+2}) = 0` for every `t ≥ 0`. -/
def EulerEq (δ : ℝ) (Du : ℕ → K × K →L[ℝ] ℝ) : Prop :=
  ∀ t v, Du t (0, v) + δ * Du (t + 1) (v, 0) = 0

/-- **Necessity of the Euler equations** (MWG, p. 750), in the short-run form: if no admissible
path that differs from `k` at finitely many dates does better, `k` passes through the interior of
`A`, `δ > 0` and `u` is differentiable along `k`, then (20.D.9) holds. -/
theorem euler_of_shortRun {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hadm : Admissible A k₀ k) (hsum0 : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    (hshort : ∀ k', Admissible A k₀ k' → {t | k' t ≠ k t}.Finite →
      reducedObjective δ u k' ≤ reducedObjective δ u k)
    (hint : ∀ t, (k t, k (t + 1)) ∈ interior A)
    {Du : ℕ → K × K →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du := by
  intro t v
  set φ : ℝ → ℝ := fun θ => δ ^ t * u (k t, k (t + 1) + θ • v)
    + δ ^ (t + 1) * u (k (t + 1) + θ • v, k (t + 2)) with hφ
  have hd : HasDerivAt φ (δ ^ t * Du t (0, v) + δ ^ (t + 1) * Du (t + 1) (v, 0)) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => (k t, k (t + 1) + θ • v)) ((0 : K), v) 0 := by
      refine HasDerivAt.prodMk (hasDerivAt_const _ _) ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (k (t + 1))
    have h2 : HasDerivAt (fun θ : ℝ => (k (t + 1) + θ • v, k (t + 2))) (v, (0 : K)) 0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (k (t + 1))
    have g1 := (hDu t).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    have g2 := (hDu (t + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
    exact (g1.const_mul _).add (g2.const_mul _)
  have hloc : IsLocalMax φ 0 := by
    have c1 : Continuous fun θ : ℝ => (k t, k (t + 1) + θ • v) := by fun_prop
    have c2 : Continuous fun θ : ℝ => (k (t + 1) + θ • v, k (t + 2)) := by fun_prop
    have n1 := c1.continuousAt.preimage_mem_nhds (x := 0) (isOpen_interior.mem_nhds (by
      simpa using hint t))
    have n2 := c2.continuousAt.preimage_mem_nhds (x := 0) (isOpen_interior.mem_nhds (by
      simpa using hint (t + 1)))
    filter_upwards [n1, n2] with θ h1 h2
    set k' : ℕ → K := Function.update k (t + 1) (k (t + 1) + θ • v) with hk'
    have hadm' : Admissible A k₀ k' := by
      refine ⟨by simp [hk', hadm.1], fun s => ?_⟩
      by_cases hs : s = t
      · subst hs; simpa [hk'] using interior_subset h1
      by_cases hs' : s = t + 1
      · subst hs'; simpa [hk', show t + 1 + 1 = t + 2 by omega] using interior_subset h2
      have : s + 1 ≠ t + 1 := fun h => hs (by omega)
      rw [hk', Function.update_of_ne hs', Function.update_of_ne this]
      exact hadm.2 s
    have hoff : ∀ s ∉ ({t, t + 1} : Finset ℕ), δ ^ s * u (k' s, k' (s + 1))
        = δ ^ s * u (k s, k (s + 1)) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      have h1' : s ≠ t + 1 := hs.2
      have h2' : s + 1 ≠ t + 1 := fun h => hs.1 (by omega)
      rw [hk', Function.update_of_ne h1', Function.update_of_ne h2']
    have hdiff := tsum_sub_eq_of_eq_off _ hoff hsum0
    rw [Finset.sum_pair (by omega)] at hdiff
    have hfin : {s | k' s ≠ k s}.Finite := (Set.finite_singleton (t + 1)).subset fun s hs => by
      by_contra h
      exact hs (by simp [hk', show s ≠ t + 1 from h])
    have hle := hshort k' hadm' hfin
    unfold reducedObjective at hle
    simp only [hk', Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega),
      Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)] at hdiff
    simp only [hφ, zero_smul, add_zero, show t + 1 + 1 = t + 2 by omega] at hdiff ⊢
    linarith
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hδt : 0 < δ ^ t := pow_pos hδ t
  have : δ ^ t * (Du t (0, v) + δ * Du (t + 1) (v, 0)) = 0 := by rw [pow_succ] at h0; linarith
  exact (mul_eq_zero.1 this).resolve_left hδt.ne'

/-- **Necessity of the Euler equations** (MWG, p. 750): an optimal path through the interior of
`A` (with `δ > 0` and `u` differentiable along it) satisfies (20.D.9). -/
theorem euler_of_optimal {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) (hint : ∀ t, (k t, k (t + 1)) ∈ interior A)
    {Du : ℕ → K × K →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du := by
  refine euler_of_shortRun hδ hopt.1 hopt.2.1 (fun k' hk' hfin => ?_) hint hDu
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hoff : ∀ s ∉ Finset.range (M + 1), δ ^ s * u (k' s, k' (s + 1))
      = δ ^ s * u (k s, k (s + 1)) := by
    intro s hs
    rw [Finset.mem_range, not_lt] at hs
    have e1 : k' s = k s := by by_contra h; have := hM h; omega
    have e2 : k' (s + 1) = k (s + 1) := by by_contra h; have := hM h; omega
    rw [e1, e2]
  exact hopt.2.2 k' hk' (summable_of_eq_off _ hoff hopt.2.1)

/-- The **telescoping identity** behind the sufficiency of the Euler equations:
`∑_{t ≤ T} δ^t Du_t(d_t, d_{t+1}) = Du_0(d_0, 0) + ∑_{t < T} δ^{t+1} (Euler expression at
t + 1, applied to d_{t+1}) + δ^T Du_T(0, d_{T+1})`. -/
theorem euler_telescope (δ : ℝ) (Du : ℕ → K × K →L[ℝ] ℝ) (d : ℕ → K) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), δ ^ t * Du t (d t, d (t + 1))
      = Du 0 (d 0, 0) + ∑ t ∈ Finset.range T,
          δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0))
        + δ ^ T * Du T (0, d (T + 1)) := by
  have hsplit : ∀ t (a b : K), Du t (a, b) = Du t (a, 0) + Du t (0, b) := by
    intro t a b
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  induction T with
  | zero => simp [hsplit 0 (d 0) (d 1)]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hsplit (T + 1) (d (T + 1))]
    ring

/-- **Exercise 20.D.6** (MWG, p. 784): for `u` concave on a convex `A`, an interior admissible
path along which `u` is differentiable, and `δ > 0`, the Euler equations hold if and only if no
admissible path that differs from `k` at finitely many dates does better (short-run
optimality). -/
theorem exercise_20_D_6 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ}
    (hconc : ConcaveOn ℝ A u) {k₀ : K} {k : ℕ → K} (hadm : Admissible A k₀ k)
    (hsum : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    (hint : ∀ t, (k t, k (t + 1)) ∈ interior A) {Du : ℕ → K × K →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du ↔ ∀ k', Admissible A k₀ k' → {t | k' t ≠ k t}.Finite →
      reducedObjective δ u k' ≤ reducedObjective δ u k := by
  constructor
  · intro heul k' hk' hfin
    obtain ⟨M, hM⟩ : ∃ M, ∀ t, M ≤ t → k' t = k t := by
      obtain ⟨M, hM⟩ := hfin.bddAbove
      exact ⟨M + 1, fun t ht => by by_contra h; have := hM h; omega⟩
    have hoff : ∀ s ∉ Finset.range (M + 1), δ ^ s * u (k' s, k' (s + 1))
        = δ ^ s * u (k s, k (s + 1)) := by
      intro s hs
      rw [Finset.mem_range, not_lt] at hs
      rw [hM s (by omega), hM (s + 1) (by omega)]
    have hdiff := tsum_sub_eq_of_eq_off _ hoff hsum
    -- termwise gradient inequality, then the telescoping identity
    set d : ℕ → K := fun t => k' t - k t
    have hterm : ∀ t, δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1))
        ≤ δ ^ t * Du t (d t, d (t + 1)) := by
      intro t
      have g := concave_le_fderiv_normed hconc (hadm.2 t) (hk'.2 t) (hDu t)
      have : (k' t, k' (t + 1)) - (k t, k (t + 1)) = (d t, d (t + 1)) := rfl
      rw [this] at g
      have hp := pow_nonneg hδ.le t
      nlinarith [mul_le_mul_of_nonneg_left g hp]
    have htel := euler_telescope δ Du d M
    have hd0 : d 0 = 0 := by simp [d, hk'.1, hadm.1]
    have hdM : d (M + 1) = 0 := by simp [d, hM (M + 1) (by omega)]
    have hmid : ∑ t ∈ Finset.range M,
        δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [heul t (d (t + 1)), mul_zero]
    rw [hd0, hdM, hmid] at htel
    simp only [Prod.mk_zero_zero, map_zero, mul_zero, add_zero] at htel
    unfold reducedObjective
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (M + 1)) => hterm t
    rw [Finset.sum_sub_distrib] at hdiff
    rw [Finset.sum_sub_distrib, htel] at this
    linarith
  · intro h
    exact euler_of_shortRun hδ hadm hsum h hint hDu

/-- A concave function bounded by `C` on the closed ball of radius `r` around `x`, and
differentiable at `x`, has derivative bounded by `2C / r` in operator norm. -/
theorem abs_fderiv_le_of_concave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ S f) {x : E} {r C : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ S) (hC : ∀ z ∈ Metric.closedBall x r, |f z| ≤ C)
    {f' : E →L[ℝ] ℝ} (hd : HasFDerivAt f f' x) (v : E) : |f' v| ≤ 2 * C / r * ‖v‖ := by
  have hx : x ∈ S := hball (Metric.mem_closedBall_self hr.le)
  -- first on the sphere of radius `r`
  have hw : ∀ w : E, ‖w‖ ≤ r → |f' w| ≤ 2 * C := by
    intro w hw
    have h1 : x + w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hw
    have h2 : x - w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hw
    have g1 := concave_le_fderiv_normed hf hx (hball h1) hd
    have g2 := concave_le_fderiv_normed hf hx (hball h2) hd
    rw [add_sub_cancel_left] at g1
    rw [sub_sub_cancel_left, map_neg] at g2
    have c0 := hC x (Metric.mem_closedBall_self hr.le)
    have c1 := hC _ h1
    have c2 := hC _ h2
    rw [abs_le] at c0 c1 c2 ⊢
    constructor <;> linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have := hw ((r / ‖v‖) • v) (by rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hvn), div_mul_cancel₀ _ hvn.ne'])
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (div_pos hr hvn)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    calc |f' v| * r = r / ‖v‖ * |f' v| * ‖v‖ := by field_simp
      _ ≤ 2 * C * ‖v‖ := mul_le_mul_of_nonneg_right this hvn.le

/-- **Proposition 20.D.7** (MWG, p. 751): a bounded, strictly interior admissible path satisfying
the Euler equations solves (20.D.8) among bounded admissible paths (all paths are bounded in MWG,
p. 744). Here `K` is finite-dimensional, `u` is concave on the convex region `A`, `0 < δ < 1`,
and strict interiority means `ball((k_t, k_{t+1}), ε) ⊆ A` for a fixed `ε > 0`. The proof uses
the gradient inequality and the telescoping identity: the gain of any competitor over the first
`T + 1` dates is at most `δ^T Du_T(0, k'_{T+1} - k_{T+1})`, which tends to `0` because strict
interiority bounds the derivatives (concave functions are continuous, hence bounded, on compact
subsets of the interior). -/
theorem proposition_20_D_7 [FiniteDimensional ℝ K] {A : Set (K × K)} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {u : K × K → ℝ} (hconc : ConcaveOn ℝ A u) {k₀ : K} {k : ℕ → K}
    (hadm : Admissible A k₀ k) (hsum : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    {R : ℝ} (hbdd : ∀ t, ‖k t‖ ≤ R) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ t, Metric.ball (k t, k (t + 1)) ε ⊆ A) {Du : ℕ → K × K →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) (heul : EulerEq δ Du)
    (k' : ℕ → K) (hk' : Admissible A k₀ k') {R' : ℝ} (hbdd' : ∀ t, ‖k' t‖ ≤ R')
    (hsum' : Summable fun t => δ ^ t * u (k' t, k' (t + 1))) :
    reducedObjective δ u k' ≤ reducedObjective δ u k := by
  set x : ℕ → K × K := fun t => (k t, k (t + 1)) with hx
  set U := ⋃ t, Metric.closedBall (x t) (ε / 2) with hU
  set S := closure U with hS
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hbdd 0)
  have hxR : ∀ t, ‖x t‖ ≤ R := fun t => by
    rw [hx, Prod.norm_def]; exact max_le (hbdd t) (hbdd (t + 1))
  have hSsub : S ⊆ interior A := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.1 hz (ε / 2) (by linarith)
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hw
    have hzt : z ∈ Metric.ball (x t) ε := by
      rw [Metric.mem_ball]
      have := dist_triangle z w (x t)
      rw [Metric.mem_closedBall] at ht
      linarith
    exact (Metric.isOpen_ball.subset_interior_iff.2 (hball t)) hzt
  have hScpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    refine (Metric.isBounded_closedBall (x := (0 : K × K)) (r := R + ε / 2)).subset ?_
    refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_insert' z (x t)
    linarith [hxR t]
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn
    (hconc.continuousOn_interior.mono hSsub)
  have hballS : ∀ t, Metric.closedBall (x t) (ε / 2) ⊆ S := fun t =>
    (Set.subset_iUnion (fun t => Metric.closedBall (x t) (ε / 2)) t).trans subset_closure
  have hDbound : ∀ t v, |Du t v| ≤ 2 * C / (ε / 2) * ‖v‖ := fun t v =>
    abs_fderiv_le_of_concave hconc (by linarith) ((hballS t).trans (hSsub.trans interior_subset))
      (fun z hz => by simpa [Real.norm_eq_abs] using hC z (hballS t hz)) (hDu t) v
  -- the gain over the first `T + 1` dates
  set d : ℕ → K := fun t => k' t - k t with hd
  have hdb : ∀ t, ‖d t‖ ≤ R' + R := fun t => by
    simp only [hd]; exact (norm_sub_le _ _).trans (add_le_add (hbdd' t) (hbdd t))
  have hgain : ∀ T, ∑ t ∈ Finset.range (T + 1),
      (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))
        ≤ δ ^ T * (2 * C / (ε / 2) * (R' + R)) := by
    intro T
    have hterm : ∀ t, δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1))
        ≤ δ ^ t * Du t (d t, d (t + 1)) := by
      intro t
      have g := concave_le_fderiv_normed hconc (hadm.2 t) (hk'.2 t) (hDu t)
      have : (k' t, k' (t + 1)) - (k t, k (t + 1)) = (d t, d (t + 1)) := rfl
      rw [this] at g
      have hp := pow_nonneg hδ0.le t
      nlinarith [mul_le_mul_of_nonneg_left g hp]
    have htel := euler_telescope δ Du d T
    have hd0 : d 0 = 0 := by simp [hd, hk'.1, hadm.1]
    have hmid : ∑ t ∈ Finset.range T,
        δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [heul t (d (t + 1)), mul_zero]
    rw [hd0, hmid] at htel
    simp only [Prod.mk_zero_zero, map_zero, zero_add] at htel
    have hlast : δ ^ T * Du T (0, d (T + 1)) ≤ δ ^ T * (2 * C / (ε / 2) * (R' + R)) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ0.le T)
      refine (le_abs_self _).trans ((hDbound T _).trans ?_)
      have hC0 : 0 ≤ 2 * C / (ε / 2) := by
        have := hC _ (hballS 0 (Metric.mem_closedBall_self (by linarith)))
        exact div_nonneg (by linarith [norm_nonneg (u (x 0))]) (by linarith)
      refine mul_le_mul_of_nonneg_left ?_ hC0
      rw [Prod.norm_def, norm_zero]
      exact max_le (by linarith [hdb 0, norm_nonneg (d 0)]) (hdb (T + 1))
    calc ∑ t ∈ Finset.range (T + 1), (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))
        ≤ ∑ t ∈ Finset.range (T + 1), δ ^ t * Du t (d t, d (t + 1)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = δ ^ T * Du T (0, d (T + 1)) := htel
      _ ≤ _ := hlast
  have hlim1 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1),
      (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))) atTop
      (𝓝 (reducedObjective δ u k' - reducedObjective δ u k)) := by
    have := ((hsum'.sub hsum).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    rw [hsum'.tsum_sub hsum] at this
    exact this
  have hlim2 : Tendsto (fun T : ℕ => δ ^ T * (2 * C / (ε / 2) * (R' + R))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).mul_const
      (2 * C / (ε / 2) * (R' + R))
  have := le_of_tendsto_of_tendsto hlim1 hlim2 (Eventually.of_forall hgain)
  linarith

/-! ### The policy function and the value function -/

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- The objective splits off its first term: `W(k) = u(k₀, k₁) + δ W(k¹)`. -/
theorem reducedObjective_succ {δ : ℝ} {u : K × K → ℝ} {k : ℕ → K}
    (hs : Summable fun t => δ ^ t * u (k t, k (t + 1))) :
    reducedObjective δ u k = u (k 0, k 1) + δ * reducedObjective δ u (fun t => k (t + 1)) := by
  unfold reducedObjective
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, zero_add]
  congr 1
  exact tsum_congr fun t => by ring

/-- Prepending an initial capital stock to a path. -/
def consPath (a : K) (k : ℕ → K) : ℕ → K
  | 0 => a
  | t + 1 => k t

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
@[simp] theorem consPath_zero (a : K) (k : ℕ → K) : consPath a k 0 = a := rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
@[simp] theorem consPath_succ (a : K) (k : ℕ → K) (t : ℕ) : consPath a k (t + 1) = k t := rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- The objective of a prepended path: `W(a, k) = u(a, k₀) + δ W(k)`. -/
theorem reducedObjective_consPath {δ : ℝ} {u : K × K → ℝ} (a : K) {k : ℕ → K}
    (hs : Summable fun t => δ ^ t * u (k t, k (t + 1))) :
    Summable (fun t => δ ^ t * u (consPath a k t, consPath a k (t + 1))) ∧
      reducedObjective δ u (consPath a k) = u (a, k 0) + δ * reducedObjective δ u k := by
  have hs' : Summable (fun t => δ ^ t * u (consPath a k t, consPath a k (t + 1))) := by
    refine (summable_nat_add_iff 1).1 ?_
    refine (hs.mul_left δ).congr fun t => ?_
    simp only [consPath_succ]; ring
  refine ⟨hs', ?_⟩
  rw [reducedObjective_succ hs']
  rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **The principle of optimality** behind (20.D.10) (MWG, p. 752): if `k` solves (20.D.8) from
`k̄₀` and `δ > 0`, the tail `(k₁, k₂, ...)` solves it from `k₁`. -/
theorem optimal_tail {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) :
    OptimalFrom A δ u (k 1) (fun t => k (t + 1)) := by
  obtain ⟨hadm, hs, hmax⟩ := hopt
  have hstail : Summable fun t => δ ^ t * u (k (t + 1), k (t + 1 + 1)) :=
    (((summable_nat_add_iff 1).2 hs).mul_left δ⁻¹).congr fun t => by
      rw [pow_succ]; field_simp
  refine ⟨⟨rfl, fun t => hadm.2 (t + 1)⟩, hstail, fun k' hk' hs' => ?_⟩
  obtain ⟨hs'', heq⟩ := reducedObjective_consPath (u := u) k₀ hs'
  have hadm'' : Admissible A k₀ (consPath k₀ k') := by
    refine ⟨rfl, fun t => ?_⟩
    cases t with
    | zero => simp only [consPath_zero, consPath_succ, hk'.1]; rw [← hadm.1]; exact hadm.2 0
    | succ t => exact hk'.2 t
  have h1 := hmax _ hadm'' hs''
  rw [heq, reducedObjective_succ hs, hk'.1, hadm.1] at h1
  have := le_of_mul_le_mul_left (by linarith : δ * reducedObjective δ u k'
    ≤ δ * reducedObjective δ u (fun t => k (t + 1))) hδ
  exact this

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **(20.D.10)** (MWG, p. 752): along an optimal path, `k_{t+1} = ψ(k_t)` for the policy
function `ψ`, the first-period choice of the optimal path from each initial condition. -/
theorem policy_20_D_10 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) {ψ : K → K}
    (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a) (t : ℕ) : k (t + 1) = ψ (k t) := by
  have htail : ∀ t, OptimalFrom A δ u (k t) (fun s => k (s + t)) := by
    intro t
    induction t with
    | zero => simpa [hopt.1.1] using hopt
    | succ t ih =>
      have := optimal_tail hδ ih
      simpa [add_assoc, add_comm 1 t] using this
  have := hψ _ _ (htail t)
  simpa [add_comm 1 t] using this

/-- **Uniqueness** of the solution of (20.D.8) (MWG, p. 750): if `A` is convex and `u` is strictly
concave and bounded above on `A`, and `0 < δ < 1`, two optimal paths from the same `k̄₀`
coincide. -/
theorem optimal_unique {A : Set (K × K)} (hA : Convex ℝ A) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : K × K → ℝ} (hu : StrictConcaveOn ℝ A u) {M : ℝ} (hM : ∀ x ∈ A, u x ≤ M) {k₀ : K}
    {k k' : ℕ → K} (h : OptimalFrom A δ u k₀ k) (h' : OptimalFrom A δ u k₀ k') : k = k' := by
  by_contra hne
  obtain ⟨t₀, ht₀⟩ : ∃ t, k t ≠ k' t := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  set m : ℕ → K := fun t => (1 / 2 : ℝ) • k t + (1 / 2 : ℝ) • k' t with hm
  have hpair : ∀ t, (m t, m (t + 1))
      = (1 / 2 : ℝ) • (k t, k (t + 1)) + (1 / 2 : ℝ) • (k' t, k' (t + 1)) := fun t => rfl
  have hadm : Admissible A k₀ m := by
    refine ⟨by simp [hm, h.1.1, h'.1.1, ← add_smul]; norm_num, fun t => ?_⟩
    rw [hpair]
    exact hA (h.1.2 t) (h'.1.2 t) (by norm_num) (by norm_num) (by norm_num)
  have hs := h.2.1
  have hs' := h'.2.1
  have hlow : ∀ t, (1 / 2 : ℝ) * (δ ^ t * u (k t, k (t + 1)))
      + (1 / 2 : ℝ) * (δ ^ t * u (k' t, k' (t + 1))) ≤ δ ^ t * u (m t, m (t + 1)) := by
    intro t
    have hc := (StrictConcaveOn.concaveOn hu).2 (h.1.2 t) (h'.1.2 t)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg hδ0.le t)]
  have hms : Summable fun t => δ ^ t * u (m t, m (t + 1)) := by
    have hlowsum := (hs.mul_left (1 / 2 : ℝ)).add (hs'.mul_left (1 / 2 : ℝ))
    have hg := (summable_geometric_of_lt_one hδ0.le hδ1).mul_right M
    have hup : ∀ t, δ ^ t * u (m t, m (t + 1)) ≤ δ ^ t * M := fun t =>
      mul_le_mul_of_nonneg_left (hM _ (hadm.2 t)) (pow_nonneg hδ0.le t)
    have hdiff : Summable fun t => δ ^ t * u (m t, m (t + 1))
        - ((1 / 2 : ℝ) * (δ ^ t * u (k t, k (t + 1)))
          + (1 / 2 : ℝ) * (δ ^ t * u (k' t, k' (t + 1)))) :=
      Summable.of_nonneg_of_le (fun t => sub_nonneg.2 (hlow t))
        (fun t => by have := hup t; linarith [hlow t])
        (hg.sub hlowsum)
    exact (hdiff.add hlowsum).congr fun t => by ring
  have hle := h.2.2 m hadm hms
  have heq : reducedObjective δ u k = reducedObjective δ u k' :=
    le_antisymm (h'.2.2 k h.1 hs) (h.2.2 k' h'.1 hs')
  -- strict inequality at a date where the pairs differ
  have hpair_ne : (k t₀, k (t₀ + 1)) ≠ (k' t₀, k' (t₀ + 1)) := fun he =>
    ht₀ (congrArg Prod.fst he)
  have hlt : (1 / 2 : ℝ) * reducedObjective δ u k + (1 / 2 : ℝ) * reducedObjective δ u k'
      < reducedObjective δ u m := by
    unfold reducedObjective
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    refine Summable.tsum_lt_tsum (i := t₀) hlow ?_ ((hs.mul_left _).add (hs'.mul_left _)) hms
    have hc := hu.2 (h.1.2 t₀) (h'.1.2 t₀) hpair_ne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_lt_mul_of_pos_left hc (pow_pos hδ0 t₀)]
  rw [heq] at hlt hle
  linarith

/-- `V` is the **value function** of (20.D.8) on a set `D` of initial conditions: from every
`k̄ ∈ D` an optimal path exists and `V(k̄)` is its value `W`. -/
def IsValueFn (A : Set (K × K)) (δ : ℝ) (u : K × K → ℝ) (D : Set K) (V : K → ℝ) : Prop :=
  ∀ a ∈ D, ∃ k, OptimalFrom A δ u a k ∧ reducedObjective δ u k = V a

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **(20.D.11)** (MWG, p. 753), the Bellman equation: if `V` is the value function on `D`, the
region keeps the capital stocks in `D` (`A ⊆ D × D`) and `δ > 0`, then for every `k ∈ D`,
`V(k) = max_{k' : (k, k') ∈ A} u(k, k') + δ V(k')`, attained at the first-period choice of the
optimal path. -/
theorem bellman_20_D_11 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {D : Set K}
    (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : K → ℝ} (hV : IsValueFn A δ u D V)
    {a : K} (ha : a ∈ D) :
    IsGreatest {r | ∃ b, (a, b) ∈ A ∧ r = u (a, b) + δ * V b} (V a) := by
  obtain ⟨k, hk, hkV⟩ := hV a ha
  constructor
  · refine ⟨k 1, by simpa [hk.1.1] using hk.1.2 0, ?_⟩
    have htail := optimal_tail hδ hk
    obtain ⟨k', hk', hk'V⟩ := hV (k 1) (hAD _ _ (by simpa [hk.1.1] using hk.1.2 0)).2
    have hval : reducedObjective δ u (fun t => k (t + 1)) = V (k 1) := by
      rw [← hk'V]
      exact le_antisymm (hk'.2.2 _ htail.1 htail.2.1) (htail.2.2 _ hk'.1 hk'.2.1)
    rw [← hkV, reducedObjective_succ hk.2.1, hval, hk.1.1]
  · rintro r ⟨b, hab, rfl⟩
    obtain ⟨k', hk', hk'V⟩ := hV b (hAD _ _ hab).2
    obtain ⟨hs'', heq⟩ := reducedObjective_consPath (u := u) a hk'.2.1
    have hadm : Admissible A a (consPath a k') := by
      refine ⟨rfl, fun t => ?_⟩
      cases t with
      | zero => simpa [hk'.1.1] using hab
      | succ t => exact hk'.1.2 t
    have := hk.2.2 _ hadm hs''
    rw [heq, hk'.1.1, hk'V, hkV] at this
    exact this

/-- **Correction to (20.D.11)** (MWG, p. 753): for the value `V₈` of the objective (20.D.8) as
printed, `∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)`, the printed equation `V₈ = max u + δ V₈` fails: with
`u ≡ 1` and `0 < δ < 1` every path has `V₈ = δ / (1 - δ)`, while `1 + δ V₈ ≠ V₈`; the normalized
value `V₈ / δ` does satisfy it. -/
theorem bellman_20_D_11_printed_false {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let V₈ := ∑' t : ℕ, δ ^ (t + 1) * (1 : ℝ)
    V₈ = δ / (1 - δ) ∧ V₈ ≠ 1 + δ * V₈ ∧ V₈ / δ = 1 + δ * (V₈ / δ) := by
  intro V₈
  have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
  have hV : V₈ = δ / (1 - δ) := by
    simp only [V₈, mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0.le hδ1]
    field_simp
  refine ⟨hV, fun h => ?_, ?_⟩
  · rw [hV] at h
    field_simp at h
    nlinarith
  · rw [hV]
    field_simp
    ring

/-- **Exercise 20.D.8(i)** (MWG, p. 784): the value function is concave, for `A` convex, `u`
concave and bounded above on `A`, `0 ≤ δ < 1`, and `D` convex. -/
theorem exercise_20_D_8_i {A : Set (K × K)} (hA : Convex ℝ A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) {u : K × K → ℝ} (hu : ConcaveOn ℝ A u) {M : ℝ} (hM : ∀ x ∈ A, u x ≤ M)
    {D : Set K} (hD : Convex ℝ D) {V : K → ℝ} (hV : IsValueFn A δ u D V) :
    ConcaveOn ℝ D V := by
  refine ⟨hD, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨k, hk, hkV⟩ := hV a ha
  obtain ⟨k', hk', hk'V⟩ := hV b hb
  obtain ⟨k'', hk'', hk''V⟩ := hV _ (hD ha hb hθ hφ hθφ)
  set m : ℕ → K := fun t => θ • k t + φ • k' t with hm
  have hpair : ∀ t, (m t, m (t + 1)) = θ • (k t, k (t + 1)) + φ • (k' t, k' (t + 1)) :=
    fun t => rfl
  have hadm : Admissible A (θ • a + φ • b) m :=
    ⟨by simp [hm, hk.1.1, hk'.1.1], fun t => by
      rw [hpair]; exact hA (hk.1.2 t) (hk'.1.2 t) hθ hφ hθφ⟩
  have hs := hk.2.1
  have hs' := hk'.2.1
  have hlow : ∀ t, θ * (δ ^ t * u (k t, k (t + 1))) + φ * (δ ^ t * u (k' t, k' (t + 1)))
      ≤ δ ^ t * u (m t, m (t + 1)) := by
    intro t
    have hc := hu.2 (hk.1.2 t) (hk'.1.2 t) hθ hφ hθφ
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg hδ0 t)]
  have hlowsum := (hs.mul_left θ).add (hs'.mul_left φ)
  have hms : Summable fun t => δ ^ t * u (m t, m (t + 1)) := by
    have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
    have hdiff : Summable fun t => δ ^ t * u (m t, m (t + 1))
        - (θ * (δ ^ t * u (k t, k (t + 1))) + φ * (δ ^ t * u (k' t, k' (t + 1)))) :=
      Summable.of_nonneg_of_le (fun t => sub_nonneg.2 (hlow t))
        (fun t => by
          have := mul_le_mul_of_nonneg_left (hM _ (hadm.2 t)) (pow_nonneg hδ0 t)
          linarith [hlow t])
        (hg.sub hlowsum)
    exact (hdiff.add hlowsum).congr fun t => by ring
  have h1 := hk''.2.2 m hadm hms
  have h2 : θ * reducedObjective δ u k + φ * reducedObjective δ u k' ≤ reducedObjective δ u m := by
    unfold reducedObjective
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    exact Summable.tsum_le_tsum hlow hlowsum hms
  rw [hkV, hk'V] at h2
  rw [hk''V] at h1
  simp only [smul_eq_mul]
  linarith

omit [NormedSpace ℝ K] in
/-- **Exercise 20.D.8(ii)** (MWG, p. 784), (20.D.12): for every perturbation `z` with
`(k + z, ψ(k)) ∈ A`, `V(k + z) ≥ u(k + z, ψ(k)) + δ V(ψ(k))`, with equality at `z = 0`. -/
theorem exercise_20_D_8_ii {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ}
    {D : Set K} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : K → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : K → K} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : K} (ha : a ∈ D) :
    (∀ z, (a + z, ψ a) ∈ A → u (a + z, ψ a) + δ * V (ψ a) ≤ V (a + z)) ∧
      V a = u (a, ψ a) + δ * V (ψ a) := by
  refine ⟨fun z hz => (bellman_20_D_11 hδ hAD hV (hAD _ _ hz).1).2 ⟨ψ a, hz, rfl⟩, ?_⟩
  obtain ⟨k, hk, hkV⟩ := hV a ha
  have h1 := hψ a k hk
  -- the Bellman maximum is attained at `ψ a`
  have htail := optimal_tail hδ hk
  obtain ⟨k', hk', hk'V⟩ := hV (k 1) (hAD _ _ (by simpa [hk.1.1] using hk.1.2 0)).2
  have hval : reducedObjective δ u (fun t => k (t + 1)) = V (k 1) := by
    rw [← hk'V]
    exact le_antisymm (hk'.2.2 _ htail.1 htail.2.1) (htail.2.2 _ hk'.1 hk'.2.1)
  rw [← hkV, reducedObjective_succ hk.2.1, hval, h1, hk.1.1]

/-- A **second-order condition at a local minimum**: if `g` has a local minimum at `a`, is
differentiable near `a` with derivative `g'`, and `g'` has derivative `D` at `a`, then `D ≥ 0`. -/
theorem second_deriv_nonneg_of_isLocalMin {g g' : ℝ → ℝ} {a D : ℝ} (hmin : IsLocalMin g a)
    (hd : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hd2 : HasDerivAt g' D a) : 0 ≤ D := by
  by_contra hneg
  push Not at hneg
  have hg'a : g' a = 0 := hmin.hasDerivAt_eq_zero hd.self_of_nhds
  -- `g' < 0` just to the right of `a`
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd2).mono_left (nhdsGT_le_nhdsNE a)
  have hneg' : ∀ᶠ x in 𝓝[>] a, g' x < 0 := by
    filter_upwards [hs.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with x hx hxa
    rw [slope_def_field, hg'a, sub_zero] at hx
    have hxa' : 0 < x - a := sub_pos.2 hxa
    exact (div_neg_iff.1 hx).elim (fun h => absurd h.2 (not_lt.2 hxa'.le)) (fun h => h.1)
  have h1 : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x := nhdsWithin_le_nhds hd
  have h2 : ∀ᶠ x in 𝓝[>] a, g a ≤ g x := nhdsWithin_le_nhds hmin
  have hall : ∀ᶠ x in 𝓝[>] a, g' x < 0 ∧ HasDerivAt g (g' x) x ∧ g a ≤ g x :=
    hneg'.and (h1.and h2)
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  have hab : a < b := hb
  set x := (a + b) / 2
  have hax : a < x := by simp only [x]; linarith
  have hxb : x < b := by simp only [x]; linarith
  have hcont : ContinuousOn g (Set.Icc a x) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hy1
    · exact hd.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hsub ⟨hy1, hy.2.trans_lt hxb⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hax hcont
    (fun y hy => (hsub ⟨hy.1, hy.2.trans hxb⟩).2.1)
  have hξneg := (hsub ⟨hξ.1, hξ.2.trans hxb⟩).1
  have hgx := (hsub ⟨hax, hxb⟩).2.2
  rw [hξeq] at hξneg
  have : g x - g a < 0 := by
    have := (div_neg_iff.1 hξneg).elim (fun h => absurd h.2 (not_lt.2 (sub_pos.2 hax).le))
      (fun h => h.1)
    exact this
  linarith

/-- **Exercise 20.D.9**, first consequence (MWG, p. 784): with one capital good, if `(k, ψ(k))` is
interior to `A`, `V` is differentiable at `k` and `u(·, ψ(k))` is differentiable at `k`, then
`V'(k) = ∇₁u(k, ψ(k))`. -/
theorem exercise_20_D_9_first {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ}
    {D : Set ℝ} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : ℝ → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : ℝ → ℝ} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : ℝ} (ha : a ∈ D) (hint : (a, ψ a) ∈ interior A) {V1 u1 : ℝ}
    (hV1 : HasDerivAt V V1 a) (hu1 : HasDerivAt (fun x => u (x, ψ a)) u1 a) : V1 = u1 := by
  obtain ⟨hge, heq⟩ := exercise_20_D_8_ii hδ hAD hV hψ ha
  have hmin : IsLocalMin (fun x => V x - u (x, ψ a) - δ * V (ψ a)) a := by
    have hc : Continuous fun x : ℝ => (x, ψ a) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)] with x hx
    have := hge (x - a) (by simpa using interior_subset hx)
    simp only [add_sub_cancel] at this
    linarith
  have := hmin.hasDerivAt_eq_zero ((hV1.sub hu1).sub_const _)
  linarith

/-- **Exercise 20.D.9**, second consequence (MWG, p. 784): with one capital good, `(k, ψ(k))`
interior to `A`, and `V`, `u(·, ψ(k))` twice differentiable at `k`, `V''(k) ≥ ∇²₁₁u(k, ψ(k))`. -/
theorem exercise_20_D_9_second {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ}
    {D : Set ℝ} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : ℝ → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : ℝ → ℝ} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : ℝ} (ha : a ∈ D) (hint : (a, ψ a) ∈ interior A) {V' u' : ℝ → ℝ} {V2 u11 : ℝ}
    (hV' : ∀ᶠ x in 𝓝 a, HasDerivAt V (V' x) x)
    (hu' : ∀ᶠ x in 𝓝 a, HasDerivAt (fun y => u (y, ψ a)) (u' x) x)
    (hV2 : HasDerivAt V' V2 a) (hu2 : HasDerivAt u' u11 a) : u11 ≤ V2 := by
  obtain ⟨hge, heq⟩ := exercise_20_D_8_ii hδ hAD hV hψ ha
  have hmin : IsLocalMin (fun x => V x - u (x, ψ a) - δ * V (ψ a)) a := by
    have hc : Continuous fun x : ℝ => (x, ψ a) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)] with x hx
    have := hge (x - a) (by simpa using interior_subset hx)
    simp only [add_sub_cancel] at this
    linarith
  have := second_deriv_nonneg_of_isLocalMin (g' := fun x => V' x - u' x) hmin
    (by filter_upwards [hV', hu'] with x h1 h2; exact (h1.sub h2).sub_const _) (hV2.sub hu2)
  linarith

end MWG.EquilibriumTime
