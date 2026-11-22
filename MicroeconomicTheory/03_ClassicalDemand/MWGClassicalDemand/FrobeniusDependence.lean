/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Frobenius' theorem, step 1: differentiable dependence of an ODE solution on parameters

MWG, Section 3.H, pp. 79-80. The sufficiency half of Frobenius' theorem needs the derivative of
the solution of an ordinary differential equation with respect to a parameter. Mathlib v4.34.0
has existence, uniqueness, Gronwall bounds and Lipschitz dependence for ODEs, but no
differentiable dependence. This module proves the case needed:

* `frob_uniform_taylor`: a `C¹` map has a first-order Taylor remainder that is `o(‖b - a‖)`
  uniformly for `a, b` in a compact convex set (Heine-Cantor plus the mean value inequality).
* `frob_hasFDerivAt_endpoint`: let `y' = G(s, q, y)` with `G` of class `C¹` on `ℝ × E × ℝ`
  (`E` finite-dimensional, `q` a parameter), and let `Y q` solve it on `[0, 1]` from an initial
  value that does not depend on `q`, with the solutions bounded for `q` near `q₁`. If a family of
  linear maps `D s` solves the linearized (variational) equation
  `d/ds (D s k) = ∂_{(q, y)} G(s, q₁, Y q₁ s) (k, D s k)`, `D 0 = 0`, then `q ↦ Y q 1` is
  differentiable at `q₁` with derivative `D 1`. The proof bounds `Y q - Y q₁` by Gronwall's
  inequality (Lipschitz dependence), and then bounds `Y q - Y q₁ - D · (q - q₁)` by Gronwall's
  inequality again, with the uniform Taylor remainder as the forcing term.

The candidate `D` is supplied by the caller: for (3.H.2) it is explicit (see
`FrobeniusTheorem`), so no linear-ODE existence theorem is needed.
-/

namespace MWG.ClassicalDemand

open Filter Topology

/-- A `C¹` map has a uniform first-order Taylor remainder on a compact convex set: for every
`ε > 0` there is `ρ > 0` with `‖G b - G a - DG(a)(b - a)‖ ≤ ε ‖b - a‖` whenever `a, b ∈ K` and
`‖b - a‖ ≤ ρ`. -/
theorem frob_uniform_taylor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : V → ℝ} (hG : ContDiff ℝ 1 G) {K : Set V} (hK : IsCompact K) (hKc : Convex ℝ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a ∈ K, ∀ b ∈ K, ‖b - a‖ ≤ ρ →
      ‖G b - G a - fderiv ℝ G a (b - a)‖ ≤ ε * ‖b - a‖ := by
  have hc := hG.continuous_fderiv one_ne_zero
  obtain ⟨ρ, hρ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc.continuousOn) ε hε
  refine ⟨ρ / 2, half_pos hρ, fun a ha b hb hab => ?_⟩
  set φ : V → ℝ := fun c => G c - fderiv ℝ G a c with hφ
  have hd : ∀ c, HasFDerivAt φ (fderiv ℝ G c - fderiv ℝ G a) c := fun c =>
    ((hG.differentiable one_ne_zero c).hasFDerivAt).sub (fderiv ℝ G a).hasFDerivAt
  have hs : Convex ℝ (K ∩ Metric.closedBall a (ρ / 2)) := hKc.inter (convex_closedBall a _)
  have key := hs.norm_image_sub_le_of_norm_fderiv_le (f := φ) (C := ε)
    (fun c _ => (hd c).differentiableAt)
    (fun c hc' => by
      rw [(hd c).fderiv]
      have h1 := Metric.mem_closedBall.mp hc'.2
      have := hu c hc'.1 a ha (by linarith)
      rw [dist_eq_norm] at this
      exact this.le)
    ⟨ha, Metric.mem_closedBall_self (half_pos hρ).le⟩
    ⟨hb, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hab⟩
  simp only [hφ] at key
  rw [map_sub]
  convert key using 2
  ring

/-- **Differentiable dependence on a parameter** (used for Frobenius' theorem, MWG pp. 79-80).
Let `G : ℝ × E × ℝ → ℝ` be `C¹`, and for every parameter `q` let `Y q` solve `y' = G(s, q, y)` on
`[0, 1]` with `Y q 0 = Y q₁ 0`, the solutions being bounded by `B` for `‖q - q₁‖ ≤ 1`. If
`s ↦ D s k` solves the variational equation along `Y q₁` with `D 0 = 0`, then `q ↦ Y q 1` has
derivative `D 1` at `q₁`. -/
theorem frob_hasFDerivAt_endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {G : ℝ × E × ℝ → ℝ} (hG : ContDiff ℝ 1 G) {Y : E → ℝ → ℝ} {q₁ : E}
    {B : ℝ} (hY : ∀ q, ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y q) (G (s, q, Y q s)) s)
    (hY0 : ∀ q, Y q 0 = Y q₁ 0)
    (hB : ∀ q ∈ Metric.closedBall q₁ 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, |Y q s| ≤ B)
    {D : ℝ → E →L[ℝ] ℝ} (hD0 : D 0 = 0)
    (hD : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => D t k) (fderiv ℝ G (s, q₁, Y q₁ s) (0, k, D s k)) s) :
    HasFDerivAt (fun q => Y q 1) (D 1) q₁ := by
  set K : Set (ℝ × E × ℝ) := Set.Icc 0 1 ×ˢ (Metric.closedBall q₁ 1 ×ˢ Set.Icc (-B) B)
    with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hKv : Convex ℝ K :=
    (convex_Icc _ _).prod ((convex_closedBall _ _).prod (convex_Icc _ _))
  have hGd := hG.differentiable one_ne_zero
  obtain ⟨M₀, hM₀⟩ :=
    hKc.exists_bound_of_continuousOn (hG.continuous_fderiv one_ne_zero).continuousOn
  set M := max M₀ 0 + 1 with hM
  have hMpos : 0 < M := by positivity
  have hMb : ∀ X ∈ K, ‖fderiv ℝ G X‖ ≤ M := fun X hX =>
    (hM₀ X hX).trans (by linarith [le_max_left M₀ 0])
  have hlip : ∀ a ∈ K, ∀ b ∈ K, ‖G b - G a‖ ≤ M * ‖b - a‖ := fun a ha b hb =>
    hKv.norm_image_sub_le_of_norm_fderiv_le (fun X _ => hGd X) hMb ha hb
  have hmem : ∀ q ∈ Metric.closedBall q₁ 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, (s, q, Y q s) ∈ K :=
    fun q hq s hs => ⟨hs, hq, abs_le.mp (hB q hq s hs)⟩
  have hq₁ : q₁ ∈ Metric.closedBall q₁ 1 := Metric.mem_closedBall_self zero_le_one
  set C := Real.exp M - 1 with hC
  have hC0 : 0 ≤ C := by have := Real.add_one_le_exp M; linarith
  -- Lipschitz dependence on the parameter
  have hlipdep : ∀ q ∈ Metric.closedBall q₁ 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |Y q s - Y q₁ s| ≤ C * ‖q - q₁‖ := by
    intro q hq
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun s => Y q s - Y q₁ s)
      (f' := fun s => G (s, q, Y q s) - G (s, q₁, Y q₁ s)) (δ := 0) (K := M)
      (ε := M * ‖q - q₁‖) (a := 0) (b := 1)
      (fun s hs => ((hY q s hs).continuousAt.sub (hY q₁ s hs).continuousAt).continuousWithinAt)
      (fun s hs => ((hY q s (Set.Ico_subset_Icc_self hs)).sub
        (hY q₁ s (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (by simp [hY0 q])
      (fun s hs => by
        have hs' := Set.Ico_subset_Icc_self hs
        have h0 := hlip _ (hmem q₁ hq₁ s hs') _ (hmem q hq s hs')
        refine h0.trans ?_
        simp only [Prod.mk_sub_mk, Prod.norm_mk, sub_self, norm_zero]
        have h1 : max 0 (max ‖q - q₁‖ ‖Y q s - Y q₁ s‖) ≤ ‖Y q s - Y q₁ s‖ + ‖q - q₁‖ :=
          max_le (by positivity) (max_le (by linarith [norm_nonneg (Y q s - Y q₁ s)])
            (by linarith [norm_nonneg (q - q₁)]))
        calc M * max 0 (max ‖q - q₁‖ ‖Y q s - Y q₁ s‖)
            ≤ M * (‖Y q s - Y q₁ s‖ + ‖q - q₁‖) := mul_le_mul_of_nonneg_left h1 hMpos.le
          _ = M * ‖Y q s - Y q₁ s‖ + M * ‖q - q₁‖ := by ring)
    intro s hs
    have h2 := hgr s hs
    rw [gronwallBound_of_K_ne_0 hMpos.ne'] at h2
    simp only [zero_mul, zero_add, sub_zero, Real.norm_eq_abs] at h2
    refine h2.trans ?_
    have hexp : Real.exp (M * s) ≤ Real.exp M :=
      Real.exp_le_exp.mpr (by nlinarith [hs.2])
    rw [mul_div_cancel_left₀ _ hMpos.ne']
    nlinarith [norm_nonneg (q - q₁)]
  -- the first-order estimate
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  set c₁ := (Real.exp M - 1) / M with hc₁def
  have hc₁ : 0 ≤ c₁ := div_nonneg hC0 hMpos.le
  set ε' := ε / ((1 + C) * c₁ + 1) with hε'def
  have hden : 0 < (1 + C) * c₁ + 1 := by positivity
  have hε' : 0 < ε' := div_pos hε hden
  obtain ⟨ρ, hρ, hT⟩ := frob_uniform_taylor hG hKc hKv hε'
  have hball : Metric.ball (0 : E) (min 1 (ρ / (1 + C))) ∈ 𝓝 (0 : E) :=
    Metric.ball_mem_nhds _ (lt_min one_pos (div_pos hρ (by linarith)))
  filter_upwards [hball] with k hk
  rw [mem_ball_zero_iff, lt_min_iff] at hk
  have hq : q₁ + k ∈ Metric.closedBall q₁ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hk.1.le
  have hkρ : (1 + C) * ‖k‖ ≤ ρ := by
    have := hk.2
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => Y (q₁ + k) s - Y q₁ s - D s k)
    (f' := fun s => G (s, q₁ + k, Y (q₁ + k) s) - G (s, q₁, Y q₁ s) -
      fderiv ℝ G (s, q₁, Y q₁ s) (0, k, D s k)) (δ := 0) (K := M)
    (ε := ε' * ((1 + C) * ‖k‖)) (a := 0) (b := 1)
    (fun s hs => (((hY _ s hs).continuousAt.sub (hY q₁ s hs).continuousAt).sub
      (hD k s hs).continuousAt).continuousWithinAt)
    (fun s hs => (((hY _ s (Set.Ico_subset_Icc_self hs)).sub
      (hY q₁ s (Set.Ico_subset_Icc_self hs))).sub
        (hD k s (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (by simp [hY0 (q₁ + k), hD0])
    (fun s hs => by
      have hs' := Set.Ico_subset_Icc_self hs
      set a : ℝ × E × ℝ := (s, q₁, Y q₁ s) with ha
      set b : ℝ × E × ℝ := (s, q₁ + k, Y (q₁ + k) s) with hb
      set e := Y (q₁ + k) s - Y q₁ s - D s k with he
      have hba : b - a = (0, k, D s k) + (0, 0, e) := by
        simp only [ha, hb, he, Prod.mk_sub_mk, Prod.mk_add_mk, sub_self, add_zero,
          add_sub_cancel_left]
        congr 2
        ring
      have hsplit : G b - G a - fderiv ℝ G a (0, k, D s k) =
          (G b - G a - fderiv ℝ G a (b - a)) + fderiv ℝ G a (0, 0, e) := by
        rw [hba, map_add]
        ring
      have hnba : ‖b - a‖ ≤ (1 + C) * ‖k‖ := by
        have hd := hlipdep _ hq s hs'
        rw [add_sub_cancel_left] at hd
        simp only [ha, hb, Prod.mk_sub_mk, Prod.norm_mk, sub_self, norm_zero,
          add_sub_cancel_left, Real.norm_eq_abs]
        refine max_le (by positivity)
          (max_le (by nlinarith [norm_nonneg k]) (by linarith [norm_nonneg k]))
      have hTa := hT a (hmem q₁ hq₁ s hs') b (hmem _ hq s hs') (hnba.trans hkρ)
      have hlin : ‖fderiv ℝ G a (0, 0, e)‖ ≤ M * ‖e‖ := by
        refine ((fderiv ℝ G a).le_opNorm _).trans ?_
        have h3 : ‖((0 : ℝ), (0 : E), e)‖ = ‖e‖ := by
          simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg e)]
        rw [h3]
        exact mul_le_mul_of_nonneg_right (hMb a (hmem q₁ hq₁ s hs')) (norm_nonneg e)
      change ‖G b - G a - fderiv ℝ G a (0, k, D s k)‖ ≤ M * ‖e‖ + ε' * ((1 + C) * ‖k‖)
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h4 : ε' * ‖b - a‖ ≤ ε' * ((1 + C) * ‖k‖) := mul_le_mul_of_nonneg_left hnba hε'.le
      linarith)
  have h5 := hgr 1 ⟨zero_le_one, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hMpos.ne'] at h5
  simp only [zero_mul, zero_add, sub_zero, mul_one] at h5
  change ‖Y (q₁ + k) 1 - Y q₁ 1 - D 1 k‖ ≤ ε * ‖k‖
  refine h5.trans ?_
  have h6 : ε' * ((1 + C) * ‖k‖) / M * (Real.exp M - 1) = ε' * ((1 + C) * c₁) * ‖k‖ := by
    rw [hc₁def]
    field_simp
  rw [h6]
  have h7 : ε' * ((1 + C) * c₁) ≤ ε := by
    rw [hε'def, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hε.le, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + C) hc₁]
  exact mul_le_mul_of_nonneg_right h7 (norm_nonneg k)

end MWG.ClassicalDemand
