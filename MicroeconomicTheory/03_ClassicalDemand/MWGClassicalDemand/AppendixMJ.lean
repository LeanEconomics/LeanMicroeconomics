/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMC
import MWGConsumerChoice.AppendixMA
import MWGConsumerChoice.MatrixDefiniteness
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Mathematical Appendix M.J: unconstrained maximization

MWG, Section M.J, pp. 954-955. Functions are `f : ℝ^N → ℝ`; the Hessian quadratic form
`z·D²f(x)z` is `D2 z z` for the second derivative `D2 = D(∇f)(x)`, and the Hessian matrix
`hessianMatrix D2` has entries `∂²f/∂xₙ∂xₘ`.

* Definition M.J.1: local and global maximizers (Mathlib's `IsLocalMax`, `IsMaxOn`).
* Theorem M.J.1: first-order condition `∇f(x̄) = 0` at local maximizers and minimizers, and the
  saddle `x₁² - x₂²` showing the converse fails.
* Theorem M.J.2: (i) at a local maximizer `D²f(x̄)` is negative semidefinite; (ii) at a critical
  point a negative definite `D²f(x̄)` gives a (strict) local maximizer; with the minimizer
  versions. The printed hypothesis `f(x̄) = 0` is a misprint for `∇f(x̄) = 0`; part (ii) fails
  as printed (`theorem_M_J_2_printed_counterexample`). We assume `f` differentiable near `x̄`
  with `∇f` differentiable at `x̄` (weaker than `C²`). The cube `x³` shows that semidefiniteness
  does not suffice.
* Theorem M.J.3: a critical point of a concave function is a global maximizer (convex:
  global minimizer, footnote 21).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N : ℕ}

/-- **Definition M.J.1** (MWG, p. 954). `x̄` is a local maximizer of `f` iff there is an open
neighborhood `A` of `x̄` with `f(x̄) ≥ f(x)` on `A` (Mathlib's `IsLocalMax`). -/
theorem definition_M_J_1_local (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    IsLocalMax f x ↔ ∃ A : Set (Fin N → ℝ), IsOpen A ∧ x ∈ A ∧ ∀ y ∈ A, f y ≤ f x := by
  constructor
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    exact ⟨A, hAo, hxA, fun y hy => hA hy⟩
  · rintro ⟨A, hAo, hxA, h⟩
    exact Filter.mem_of_superset (hAo.mem_nhds hxA) fun y hy => h y hy

/-- **Definition M.J.1** (MWG, p. 954). `x̄` is a global maximizer of `f` iff `f(x̄) ≥ f(x)` for
every `x ∈ ℝ^N` (Mathlib's `IsMaxOn` on `univ`). -/
theorem definition_M_J_1_global (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    IsMaxOn f Set.univ x ↔ ∀ y, f y ≤ f x :=
  ⟨fun h y => h (Set.mem_univ y), fun h y _ => h y⟩

/-- **Theorem M.J.1** (MWG, p. 954). If `f` is differentiable at a local maximizer or local
minimizer `x̄`, then every partial derivative vanishes, `∂f(x̄)/∂xₙ = 0` (M.J.1), i.e.
`∇f(x̄) = 0` (M.J.2). -/
theorem theorem_M_J_1 {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    (hf : HasFDerivAt f f' x) (h : IsLocalMax f x ∨ IsLocalMin f x) :
    gradientVec f' = 0 ∧ ∀ n, f' (Pi.single n 1) = 0 := by
  have hz : f' = 0 := by
    rcases h with h | h
    · exact h.hasFDerivAt_eq_zero hf
    · exact h.hasFDerivAt_eq_zero hf
  subst hz
  exact ⟨rfl, fun _ => rfl⟩

/-- **Section M.J** (MWG, pp. 954-955). A critical point need not be a local extremum:
`f(x₁, x₂) = x₁² - x₂²` has `∇f(0) = 0`, but `0` is neither a local maximizer nor a local
minimizer. -/
theorem saddle_not_extremum :
    HasFDerivAt (fun x : Fin 2 → ℝ => x 0 * x 0 - x 1 * x 1) (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
      ¬ IsLocalMax (fun x : Fin 2 → ℝ => x 0 * x 0 - x 1 * x 1) 0 ∧
      ¬ IsLocalMin (fun x : Fin 2 → ℝ => x 0 * x 0 - x 1 * x 1) 0 := by
  have hd : HasFDerivAt (fun x : Fin 2 → ℝ => x 0 * x 0 - x 1 * x 1)
      (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
    have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)
    have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
    have := (h0.mul h0).sub (h1.mul h1)
    refine HasFDerivAt.congr_fderiv this ?_
    ext v
    simp
  have hline : ∀ v : Fin 2 → ℝ, Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    intro v
    have : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hex : ∀ v : Fin 2 → ℝ, ∀ P : (Fin 2 → ℝ) → Prop, (∀ᶠ y in 𝓝 0, P y) →
      ∃ t : ℝ, t ≠ 0 ∧ P (t • v) := by
    intro v P hP
    obtain ⟨t, ht, ht0⟩ := ((((hline v).eventually hP).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {t : ℝ | t ≠ 0} ∈ 𝓝[≠] (0 : ℝ))).exists
    exact ⟨t, ht0, ht⟩
  refine ⟨hd, fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, ht0, ht⟩ := hex ![1, 0] _ h
    have ht' : t * t ≤ 0 := by simpa using ht
    exact ht0 (mul_self_eq_zero.mp (le_antisymm ht' (mul_self_nonneg t)))
  · obtain ⟨t, ht0, ht⟩ := hex ![0, 1] _ h
    have ht' : t * t ≤ 0 := by simpa using ht
    exact ht0 (mul_self_eq_zero.mp (le_antisymm ht' (mul_self_nonneg t)))

/-- **Section M.J** (MWG, p. 955). The Hessian matrix `D²f(x)` of a second derivative
`D2 = D(∇f)(x)`: entries `∂²f/∂xₙ∂xₘ = D2 eₙ eₘ`. -/
def hessianMatrix (D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun n m => D2 (Pi.single n 1) (Pi.single m 1)

/-- The quadratic form of the Hessian matrix is `z·D²f(x)z = D2 z z`. -/
theorem hessianMatrix_quad (D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) (z : Fin N → ℝ) :
    z ⬝ᵥ (hessianMatrix D2).mulVec z = D2 z z := by
  have hz : z = ∑ n, z n • (Pi.single n 1 : Fin N → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_rhs => rw [hz]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    hessianMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Along the line `t ↦ x + tz`, the derivative of `t ↦ ∇f(x + tz)·z` at `0` is `D2 z z`. -/
theorem mj_line_second_deriv {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) D2 x) (z : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • z) z) (D2 z z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have h2' : HasFDerivAt (fderiv ℝ f) D2 (x + (0 : ℝ) • z) := by simpa using h2
  have hc := h2'.comp_hasDerivAt (0 : ℝ) h1
  have := hc.clm_apply (hasDerivAt_const (0 : ℝ) z)
  simpa using this

/-- If `f` is differentiable near `x`, then near `t = 0` the line restriction has derivative
`∇f(x + tz)·z`. -/
theorem mj_line_deriv_eventually {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (z : Fin N → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => f (x + s • z)) (fderiv ℝ f (x + t • z) z) t := by
  have hpath : Tendsto (fun t : ℝ => x + t • z) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun t : ℝ => x + t • z) := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [hpath.eventually hdiff] with t ht
  exact mc_line_hasDerivAt_at ht.hasFDerivAt

/-- **Theorem M.J.2(i)** (MWG, p. 955). If `x̄` is a local maximizer, `f` is differentiable
near `x̄` and `∇f` is differentiable at `x̄` with derivative `D2`, then `D²f(x̄)` is negative
semidefinite: `z·D²f(x̄)z ≤ 0` for all `z`. -/
theorem theorem_M_J_2_i {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    {x : Fin N → ℝ} (hmax : IsLocalMax f x) (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (h2 : HasFDerivAt (fderiv ℝ f) D2 x) : NegSemidef (hessianMatrix D2) := by
  intro z
  rw [hessianMatrix_quad]
  by_contra hpos
  push Not at hpos
  have hgrad : fderiv ℝ f x = 0 :=
    hmax.hasFDerivAt_eq_zero (hdiff.self_of_nhds).hasFDerivAt
  -- the directional derivative is positive just to the right of `0`
  have hψ := mj_line_second_deriv h2 z
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < fderiv ℝ f (x + t • z) z := by
    have hs := hψ.tendsto_slope_zero_right
    filter_upwards [hs.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, zero_smul, add_zero, hgrad, zero_apply, sub_zero,
      smul_eq_mul] at ht
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr ht0)).mp ht
  have hderiv := mj_line_deriv_eventually hdiff z
  have hmaxline : ∀ᶠ t in 𝓝 (0 : ℝ), f (x + t • z) ≤ f x := by
    have hpath : Tendsto (fun t : ℝ => x + t • z) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun t : ℝ => x + t • z) := by fun_prop
      simpa using this.tendsto 0
    exact hpath.eventually hmax
  obtain ⟨δ, hδ, hδset⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hright.and ((hderiv.and hmaxline).filter_mono nhdsWithin_le_nhds))
  obtain ⟨ε, hε, hεset⟩ := Metric.eventually_nhds_iff.mp (hderiv.and hmaxline)
  set t := min (δ / 2) (ε / 2) with ht
  have ht0 : 0 < t := lt_min (half_pos hδ) (half_pos hε)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have htε : |t| < ε := by rw [abs_of_pos ht0]; exact (min_le_right _ _).trans_lt (half_lt_self hε)
  have htε2 : t ≤ ε / 2 := min_le_right _ _
  have hcont : ContinuousOn (fun s : ℝ => f (x + s • z)) (Set.Icc 0 t) := by
    intro s hs
    have : |s| < ε := by rw [abs_of_nonneg hs.1]; linarith [hs.2]
    exact ((hεset (by simpa [Real.dist_eq] using this)).1).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (x + s • z))
    (fun s => fderiv ℝ f (x + s • z) z) ht0 hcont fun s hs =>
      (hδset ⟨hs.1, hs.2.trans htδ⟩).2.1
  have hcpos := (hδset ⟨hc.1, hc.2.trans htδ⟩).1
  rw [sub_zero] at hcs
  rw [hcs, lt_div_iff₀ ht0, zero_mul, sub_pos] at hcpos
  have := (hεset (by simpa [Real.dist_eq] using htε)).2
  simp only [zero_smul, add_zero] at hcpos
  linarith

/-- **Theorem M.J.2(i)**, minimizer version (MWG, p. 955): at a local minimizer `D²f(x̄)` is
positive semidefinite. -/
theorem theorem_M_J_2_i_min {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ} (hmin : IsLocalMin f x)
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (h2 : HasFDerivAt (fderiv ℝ f) D2 x) :
    PosSemidefMWG (hessianMatrix D2) := by
  have hneg : HasFDerivAt (fderiv ℝ (-f)) (-D2) x := by
    have heq : fderiv ℝ (-f) =ᶠ[𝓝 x] -fderiv ℝ f := by
      filter_upwards [hdiff] with y hy
      exact fderiv_neg
    exact h2.neg.congr_of_eventuallyEq heq
  have h := theorem_M_J_2_i (f := -f) hmin.neg (hdiff.mono fun y hy => hy.neg) hneg
  intro z
  have := h z
  rw [hessianMatrix_quad] at this ⊢
  simp only [neg_apply] at this
  linarith



/-- A negative definite Hessian is uniformly negative: `D2 z z ≤ -c ‖z‖²` for some `c > 0`. -/
theorem mj_negDef_uniform {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hnd : NegDef (hessianMatrix D2)) : ∃ c : ℝ, 0 < c ∧ ∀ z, D2 z z ≤ -c * ‖z‖ ^ 2 := by
  have hq : ∀ z, z ≠ 0 → D2 z z < 0 := fun z hz => by
    have := hnd z hz
    rwa [hessianMatrix_quad] at this
  have hcont : Continuous (fun z : Fin N → ℝ => D2 z z) := D2.continuous.clm_apply continuous_id
  by_cases hS : (Metric.sphere (0 : Fin N → ℝ) 1).Nonempty
  · obtain ⟨u0, hu0, hmax⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMaxOn hS
      hcont.continuousOn
    have hu0ne : u0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hu0
      exact zero_ne_one hu0
    refine ⟨-D2 u0 u0, by linarith [hq u0 hu0ne], fun z => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      obtain ⟨u, hu⟩ : ∃ u : Fin N → ℝ, u = ‖z‖⁻¹ • z := ⟨_, rfl⟩
      have hus : u ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hzn.ne']
      have hle : D2 u u ≤ D2 u0 u0 := hmax hus
      have hzu : z = ‖z‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hzn.ne', one_smul]
      have hexp : D2 (‖z‖ • u) (‖z‖ • u) = ‖z‖ ^ 2 * D2 u u := by
        rw [map_smul, map_smul]
        change ‖z‖ • (‖z‖ • D2 u u) = _
        rw [smul_eq_mul, smul_eq_mul]
        ring
      have : D2 z z = ‖z‖ ^ 2 * D2 u u := by rw [← hexp, ← hzu]
      rw [this]
      nlinarith [sq_nonneg ‖z‖]
  · refine ⟨1, one_pos, fun z => ?_⟩
    have hz : z = 0 := by
      by_contra hz
      apply hS
      refine ⟨‖z‖⁻¹ • z, ?_⟩
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.mpr hz).ne']
    simp [hz]

/-- **Theorem M.J.2(ii)** (MWG, p. 955). At a critical point `x̄` (`∇f(x̄) = 0`) of a function
differentiable near `x̄` whose gradient is differentiable at `x̄`, a negative definite `D²f(x̄)`
makes `x̄` a strict local maximizer. -/
theorem theorem_M_J_2_ii_strict {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hgrad : fderiv ℝ f x = 0)
    (h2 : HasFDerivAt (fderiv ℝ f) D2 x) (hnd : NegDef (hessianMatrix D2)) :
    ∀ᶠ y in 𝓝 x, y ≠ x → f y < f x := by
  obtain ⟨c, hc, hcq⟩ := mj_negDef_uniform hnd
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp h2).def (half_pos hc)
  rw [hgrad] at hlo
  obtain ⟨ρ1, hρ1, hset1⟩ := Metric.eventually_nhds_iff.mp hlo
  obtain ⟨ρ2, hρ2, hset2⟩ := Metric.eventually_nhds_iff.mp hdiff
  rw [Metric.eventually_nhds_iff]
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun y hy hne => ?_⟩
  set h := y - x with hh
  have hhne : h ≠ 0 := sub_ne_zero.mpr hne
  have hhn : ‖h‖ < min ρ1 ρ2 := by rwa [hh, ← dist_eq_norm]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t • h‖ < min ρ1 ρ2 := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hhn
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + t • h) h) t := by
    intro t ht
    have : dist (x + t • h) x < ρ2 := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact (hpt t ht).trans_le (min_le_right _ _)
    exact mc_line_hasDerivAt_at (hset2 this).hasFDerivAt
  obtain ⟨θ, hθ, hθeq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (x + s • h))
    (fun s => fderiv ℝ f (x + s • h) h) one_pos
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hθeq
  have hyx : y = x + h := by rw [hh, add_sub_cancel]
  rw [hyx, ← sub_neg, ← hθeq]
  -- bound the derivative at the intermediate point
  have hθh : dist (θ • h) 0 < ρ1 := by
    rw [dist_zero_right]
    exact (hpt θ ⟨hθ.1.le, hθ.2.le⟩).trans_le (min_le_left _ _)
  have hb := hset1 hθh
  simp only [sub_zero] at hb
  have hop : |(fderiv ℝ f (x + θ • h) - D2 (θ • h)) h| ≤ c / 2 * ‖θ • h‖ * ‖h‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ f (x + θ • h) - D2 (θ • h)).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg h))
  have hlin : D2 (θ • h) h = θ * D2 h h := by
    rw [map_smul]
    rfl
  have hnorm : ‖θ • h‖ = θ * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg hθ.1.le]
  have hsub : (fderiv ℝ f (x + θ • h) - D2 (θ • h)) h = fderiv ℝ f (x + θ • h) h -
      D2 (θ • h) h := rfl
  rw [hsub, hlin, hnorm] at hop
  have hq := hcq h
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hhne
  have h1 := (abs_le.mp hop).2
  have h2 := mul_le_mul_of_nonneg_left hq hθ.1.le
  have h3 : 0 < θ * (c * ‖h‖ ^ 2) := mul_pos hθ.1 (mul_pos hc (pow_pos hhpos 2))
  nlinarith

/-- **Theorem M.J.2(ii)** (MWG, p. 955), as stated: `x̄` is a local maximizer. -/
theorem theorem_M_J_2_ii {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    {x : Fin N → ℝ} (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hgrad : fderiv ℝ f x = 0)
    (h2 : HasFDerivAt (fderiv ℝ f) D2 x) (hnd : NegDef (hessianMatrix D2)) :
    IsLocalMax f x := by
  filter_upwards [theorem_M_J_2_ii_strict hdiff hgrad h2 hnd] with y hy
  rcases eq_or_ne y x with rfl | hne
  · exact le_rfl
  · exact (hy hne).le

/-- The function `f(x) = x - x²` on `ℝ¹` used against the printed hypothesis of Theorem M.J.2. -/
def mj2Counter (x : Fin 1 → ℝ) : ℝ := x 0 - x 0 * x 0

/-- **Theorem M.J.2** (MWG, p. 955) as printed assumes `f(x̄) = 0` instead of `∇f(x̄) = 0`; then
part (ii) fails. `f(x) = x - x²` has `f(0) = 0`, `f` is differentiable with `D²f(0) = -2`
negative definite, yet `0` is not a local maximizer. -/
theorem theorem_M_J_2_printed_counterexample :
    ∃ D2 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) →L[ℝ] ℝ, mj2Counter 0 = 0 ∧
      (∀ y, DifferentiableAt ℝ mj2Counter y) ∧ HasFDerivAt (fderiv ℝ mj2Counter) D2 0 ∧
      NegDef (hessianMatrix D2) ∧ ¬ IsLocalMax mj2Counter 0 := by
  set P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0 with hP
  have hf : ∀ y : Fin 1 → ℝ, HasFDerivAt mj2Counter ((1 - 2 * y 0) • P) y := by
    intro y
    have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) y
    have := h0.sub (h0.mul h0)
    refine HasFDerivAt.congr_fderiv this ?_
    ext v
    simp [hP]
    ring
  have hfd : fderiv ℝ mj2Counter = fun y => (1 - 2 * y 0) • P :=
    funext fun y => (hf y).fderiv
  have hc : HasFDerivAt (fun y : Fin 1 → ℝ => 1 - 2 * y 0) ((-2 : ℝ) • P) 0 := by
    have := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (0 : Fin 1 → ℝ)).const_mul 2).const_sub 1
    refine HasFDerivAt.congr_fderiv this ?_
    ext v
    simp [hP]
  refine ⟨((-2 : ℝ) • P).smulRight P, by simp [mj2Counter], fun y => (hf y).differentiableAt,
    ?_, ?_, ?_⟩
  · rw [hfd]
    exact hc.smul_const P
  · intro z hz
    have hz0 : z 0 ≠ 0 := by
      intro h
      apply hz
      funext i
      fin_cases i
      exact h
    simp [hessianMatrix, dotProduct, Matrix.mulVec, hP]
    nlinarith [sq_pos_of_ne_zero hz0]
  · intro h
    have hline : Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) := continuous_pi fun _ =>
        continuous_id
      exact (this.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := ((hline.eventually h).and ((Ioo_mem_nhdsGT
      (show (0 : ℝ) < 1 from one_pos)))).exists
    simp only [mj2Counter, Pi.zero_apply, mul_zero, sub_zero] at ht
    nlinarith [ht0.1, ht0.2]

/-- **Section M.J** (MWG, p. 955). Negative semidefiniteness is not sufficient: for
`f(x) = x³`, `f'(0) = 0` and `f''(0) = 0`, yet `0` is neither a local maximizer nor a local
minimizer. -/
theorem cube_semidefinite_not_extremum :
    deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧ deriv (deriv (fun x : ℝ => x ^ 3)) 0 = 0 ∧
      ¬ IsLocalMax (fun x : ℝ => x ^ 3) 0 ∧ ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0 := by
  have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 := by
    ext x
    simp
  refine ⟨by rw [hd]; simp, by rw [hd]; simp, fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, ht, ht0⟩ := (((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0))).exists
    have : 0 < t ^ 3 := pow_pos ht0 3
    simp at ht
    linarith
  · obtain ⟨t, ht, ht0⟩ := (((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Iio (0 : ℝ) ∈ 𝓝[<] 0))).exists
    have : t ^ 3 < 0 := Odd.pow_neg (by decide) ht0
    simp at ht
    linarith

/-- **Theorem M.J.3** (MWG, p. 955). Any critical point of a differentiable concave function is
a global maximizer. -/
theorem theorem_M_J_3 {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hc : ConcaveOn ℝ Set.univ f) {x : Fin N → ℝ}
    (hcrit : f' x = 0) : ∀ y, f y ≤ f x := by
  intro y
  have := theorem_M_C_1_necessity (z := y - x) (fun x _ => hf x) hc (Set.mem_univ x)
    (Set.mem_univ _)
  rw [add_sub_cancel, hcrit] at this
  simpa using this

/-- **Footnote 21** (MWG, p. 955). Any critical point of a differentiable convex function is a
global minimizer. -/
theorem theorem_M_J_3_convex {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hc : ConvexOn ℝ Set.univ f) {x : Fin N → ℝ}
    (hcrit : f' x = 0) : ∀ y, f x ≤ f y := by
  intro y
  have h := theorem_M_J_3 (f := -f) (f' := fun x => -f' x) (fun x => (hf x).neg)
    (neg_concaveOn_iff.mpr hc) (by rw [hcrit, neg_zero]) y
  simp only [Pi.neg_apply, neg_le_neg_iff] at h
  exact h

end MWG.ClassicalDemand
