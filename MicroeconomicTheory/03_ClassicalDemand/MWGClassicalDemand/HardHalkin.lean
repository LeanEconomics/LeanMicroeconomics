/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMK
import LeanEconomics.FixedPoint.Brouwer
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Theorems M.K.1 and M.K.2 for merely differentiable functions (Halkin's argument)

MWG, Section M.K, pp. 956-960. The book assumes only that the objective and the constraint
functions are differentiable; the first pass (`theorem_M_K_1`, `theorem_M_K_2`) assumed strict
differentiability at `x̄`. Here the book's hypotheses suffice, by Halkin's argument (H. Halkin,
"Implicit functions and optimization problems without continuous differentiability of the
data", SIAM J. Control 12 (1974)) with Brouwer's fixed point theorem in place of the implicit
function theorem.

* `hardHalkin_feasible`: if `G : ℝ^N → ℝ^ι` is differentiable at `a` with a surjective derivative
  `G'` and continuous near `a`, `A` is a right inverse of `G'`, and `ε > 0`, then for all small
  `t > 0` there is `v` with `‖v‖ ≤ ε t` and `G(a + t z + A v) = G(a) + t G'z`. The point `v` is a
  fixed point of `v ↦ v - (G(a + t z + A v) - G(a) - t G'z)` on the ball of radius `ε t`
  (LeanEconomics' `brouwer`).
* `hardHalkin_cone`: at a local maximizer on a set `S` that contains the points with
  `G(y) = G(x̄) + t G'z`, `t > 0`, near `x̄`, the derivative of the objective satisfies
  `f'z ≤ 0`.
* `theorem_M_K_1_differentiable`, `theorem_M_K_1_book` (Theorem M.K.1) and
  `theorem_M_K_2_differentiable`, `theorem_M_K_2_book` (Theorem M.K.2): Lagrange and
  Kuhn-Tucker multipliers when `f` is differentiable at `x̄` and the constraints are
  differentiable at `x̄` and continuous near it (in the `_book` forms: all functions
  differentiable on `ℝ^N`, as the book states). The multipliers are then read off from the
  linearized problem by the first-pass theorems for linear functions.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N M : ℕ}

/-- **Halkin's lemma** (for Theorems M.K.1-M.K.2). Let `G : X → ℝ^ι` (`X` a normed space) be
differentiable at `a` with derivative `G'`, continuous near `a`, and let `A` be a right inverse
of `G'`. For every
direction `z` and `ε > 0` there is `δ > 0` such that for `0 < t < δ` some `v` with `‖v‖ ≤ ε t`
solves `G(a + t z + A v) = G(a) + t G'z` (Brouwer's fixed point theorem). -/
theorem hardHalkin_feasible {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] {G : X → ι → ℝ}
    {G' : X →L[ℝ] (ι → ℝ)} {a : X} (hG : HasFDerivAt G G' a)
    (hGc : ∀ᶠ y in 𝓝 a, ContinuousAt G y) {A : (ι → ℝ) →L[ℝ] X}
    (hA : ∀ v, G' (A v) = v) (z : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → ∃ v : ι → ℝ, ‖v‖ ≤ ε * t ∧
      G (a + t • z + A v) = G a + t • G' z := by
  set C := ‖z‖ + ‖A‖ * ε + 1 with hC
  have hC0 : 0 < C := by positivity
  have ho := hG.isLittleO.def (c := ε / C) (by positivity)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (ho.and hGc)
  refine ⟨ρ / C, by positivity, fun t ht0 htδ => ?_⟩
  set P : (ι → ℝ) → X := fun v => a + t • z + A v with hP
  have hPsub : ∀ v, P v - a = t • z + A v := fun v => by simp only [hP]; abel
  have hPa : ∀ v, ‖v‖ ≤ ε * t → ‖P v - a‖ ≤ C * t := by
    intro v hv
    rw [hPsub]
    have h1 : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
    have h2 : ‖A v‖ ≤ ‖A‖ * (ε * t) :=
      (A.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    calc ‖t • z + A v‖ ≤ ‖t • z‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ t * ‖z‖ + ‖A‖ * (ε * t) := by rw [h1]; linarith
      _ ≤ C * t := by rw [hC]; nlinarith [norm_nonneg z, norm_nonneg A]
  have hPball : ∀ v, ‖v‖ ≤ ε * t → P v ∈ Metric.ball a ρ := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm]
    have : C * t < ρ := by rwa [lt_div_iff₀ hC0, mul_comm] at htδ
    linarith [hPa v hv]
  set Φ : (ι → ℝ) → ι → ℝ := fun v => v - (G (P v) - G a - t • G' z) with hΦ
  have hΦeq : ∀ v, Φ v = -(G (P v) - G a - G' (P v - a)) := by
    intro v
    rw [hPsub, map_add, map_smul, hA]
    simp only [hΦ]
    abel
  set K := Metric.closedBall (0 : ι → ℝ) (ε * t) with hK
  have hmemK : ∀ v, v ∈ K ↔ ‖v‖ ≤ ε * t := fun v => by
    rw [hK, Metric.mem_closedBall, dist_zero_right]
  have hmaps : Set.MapsTo Φ K K := by
    intro v hv
    rw [hmemK] at hv ⊢
    rw [hΦeq, norm_neg]
    calc _ ≤ ε / C * ‖P v - a‖ := (hball _ (hPball v hv)).1
      _ ≤ ε / C * (C * t) := mul_le_mul_of_nonneg_left (hPa v hv) (by positivity)
      _ = ε * t := by field_simp
  have hcont : ContinuousOn Φ K := by
    intro v hv
    have hPc : Continuous P := by
      simp only [hP]
      exact continuous_const.add A.continuous
    have hGP : ContinuousAt G (P v) := (hball _ (hPball v ((hmemK v).mp hv))).2
    exact (continuousAt_id.sub (((hGP.comp hPc.continuousAt).sub continuousAt_const).sub
      continuousAt_const)).continuousWithinAt
  have hne : K.Nonempty := ⟨0, (hmemK 0).mpr (by simp only [norm_zero]; positivity)⟩
  obtain ⟨v, hvK, hv⟩ := LeanEconomics.FixedPoint.brouwer (isCompact_closedBall _ _)
    (convex_closedBall _ _) hne hcont hmaps
  refine ⟨v, (hmemK v).mp hvK, ?_⟩
  have h0 : G (P v) - G a - t • G' z = 0 := by
    have hv' : v - (G (P v) - G a - t • G' z) = v := hv
    rwa [sub_eq_self] at hv'
  have : G (P v) = G a + t • G' z := by
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  exact this

/-- **Halkin's cone lemma** (for Theorems M.K.1-M.K.2). Let `x̄` be a local maximizer of `f` on
`S`, `f` differentiable at `x̄`, and `G : X → ℝ^ι` differentiable at `x̄` with surjective
derivative `G'` and continuous near `x̄`. If, near `x̄`, every `y` with `G(y) = G(x̄) + t G'z` for
some `t > 0` lies in `S`, then `f'z ≤ 0`. -/
theorem hardHalkin_cone {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Finite ι] {f : X → ℝ}
    {f' : X →L[ℝ] ℝ} {G : X → ι → ℝ} {G' : X →L[ℝ] (ι → ℝ)}
    {S : Set X} {x z : X} (hmax : IsLocalMaxOn f S x)
    (hf : HasFDerivAt f f' x) (hG : HasFDerivAt G G' x) (hGc : ∀ᶠ y in 𝓝 x, ContinuousAt G y)
    (hsurj : G'.range = ⊤)
    (hS : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → G y = G x + t • G' z → y ∈ S) : f' z ≤ 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨A, hA⟩ := G'.exists_rightInverse_of_surjective hsurj
  have hA' : ∀ v, G' (A v) = v := fun v => by
    have := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) hA
    simpa using this
  by_contra hpos
  push Not at hpos
  set d := f' z with hd
  set ε := d / (4 * (‖f'‖ * ‖A‖ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set C := ‖z‖ + ‖A‖ * ε + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨δ, hδ, hfeas⟩ := hardHalkin_feasible hG hGc hA' z hε0
  have hmax' : ∀ᶠ y in 𝓝 x, y ∈ S → f y ≤ f x := eventually_nhdsWithin_iff.mp hmax
  have hfo := hf.isLittleO.def (c := d / (4 * C)) (by positivity)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((hmax'.and hfo).and hS)
  set t := min (δ / 2) (ρ / (2 * C)) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htρ : C * t ≤ ρ / 2 := by
    have := min_le_right (δ / 2) (ρ / (2 * C))
    rw [← ht] at this
    calc C * t ≤ C * (ρ / (2 * C)) := mul_le_mul_of_nonneg_left this hC0.le
      _ = ρ / 2 := by field_simp
  obtain ⟨v, hv, hGv⟩ := hfeas t ht0 htδ
  set P := x + t • z + A v with hP
  have hPx : P - x = t • z + A v := by rw [hP]; abel
  have hAv : ‖A v‖ ≤ ‖A‖ * (ε * t) :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hPnorm : ‖P - x‖ ≤ C * t := by
    rw [hPx]
    have h1 : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
    calc ‖t • z + A v‖ ≤ ‖t • z‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ t * ‖z‖ + ‖A‖ * (ε * t) := by rw [h1]; linarith
      _ ≤ C * t := by rw [hC]; nlinarith [norm_nonneg z, norm_nonneg A]
  have hPball : P ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  obtain ⟨⟨hmaxP, hfP⟩, hSP⟩ := hball P hPball
  have hfle := hmaxP (hSP t ht0 hGv)
  have h2 : f' (P - x) = t * d + f' (A v) := by
    rw [hPx, map_add, map_smul, smul_eq_mul]
  have h3 : |f' (A v)| ≤ ‖f'‖ * (‖A‖ * (ε * t)) := by
    rw [← Real.norm_eq_abs]
    exact (f'.le_opNorm _).trans (mul_le_mul_of_nonneg_left hAv (norm_nonneg _))
  have h4 : ‖f'‖ * ‖A‖ * ε ≤ d / 4 := by
    have hk : 0 ≤ ‖f'‖ * ‖A‖ := by positivity
    calc ‖f'‖ * ‖A‖ * ε = d / 4 * (‖f'‖ * ‖A‖ / (‖f'‖ * ‖A‖ + 1)) := by
          rw [hε]
          field_simp
      _ ≤ d / 4 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]
          linarith
      _ = d / 4 := mul_one _
  have h5 : ‖f P - f x - f' (P - x)‖ ≤ d / (4 * C) * (C * t) :=
    hfP.trans (mul_le_mul_of_nonneg_left hPnorm (by positivity))
  have h6 : d / (4 * C) * (C * t) = d / 4 * t := by field_simp
  rw [h6, Real.norm_eq_abs, abs_le] at h5
  have h7 : ‖f'‖ * (‖A‖ * (ε * t)) = ‖f'‖ * ‖A‖ * ε * t := by ring
  rw [h7] at h3
  have h8 := (abs_le.mp h3).1
  have h9 : ‖f'‖ * ‖A‖ * ε * t ≤ d / 4 * t := mul_le_mul_of_nonneg_right h4 ht0.le
  nlinarith [h5.1, h2, h8, h9]

/-- **Theorem M.K.1** (MWG, p. 956) for merely differentiable functions. Let `x̄ ∈ C` be a local
constrained maximizer of (M.K.1), `f` differentiable at `x̄`, every `g_m` differentiable at `x̄`
and continuous near `x̄`, and let the constraint qualification hold (the `∇g_m(x̄)` are linearly
independent). Then `∇f(x̄) = ∑ λ_m ∇g_m(x̄)` for some multipliers `λ_m`. -/
theorem theorem_M_K_1_differentiable {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hf : HasFDerivAt f f' x) (hg : ∀ m, HasFDerivAt (g m) (g' m) x)
    (hgc : ∀ m, ∀ᶠ y in 𝓝 x, ContinuousAt (g m) y) (hCQ : LinearIndependent ℝ g') :
    ∃ lam : Fin M → ℝ, f' = ∑ m, lam m • g' m := by
  set G : (Fin N → ℝ) → Fin M → ℝ := fun y m => g m y with hGdef
  have hG : HasFDerivAt G (ContinuousLinearMap.pi g') x := hasFDerivAt_pi.mpr hg
  have hGc : ∀ᶠ y in 𝓝 x, ContinuousAt G y :=
    (eventually_all.mpr hgc).mono fun y hy => continuousAt_pi.mpr hy
  have hsurj := mk_range_pi_eq_top hCQ
  have hle : ∀ z, (∀ m, g' m z = 0) → f' z ≤ 0 := by
    intro z hz
    refine hardHalkin_cone hmax hf hG hGc hsurj (Eventually.of_forall fun y t _ hy => ?_)
    intro m
    have := congrFun hy m
    simp only [hGdef, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.pi_apply, hz,
      smul_zero, add_zero] at this
    rw [this]
    exact hx m
  have hker : ∀ z, (∀ m, g' m z = 0) → f' z = 0 := by
    intro z hz
    have h1 := hle z hz
    have h2 := hle (-z) fun m => by rw [map_neg, hz m, neg_zero]
    rw [map_neg] at h2
    linarith
  have hlin : IsLocalMaxOn (⇑f') (eqConstraintSet (fun m => ⇑(g' m)) fun m => g' m x) x := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => ?_
    have := hker (y - x) fun m => by rw [map_sub]; exact sub_eq_zero.mpr (hy m)
    rw [map_sub, sub_eq_zero] at this
    exact this.le
  exact theorem_M_K_1 (fun m => rfl) hlin f'.hasStrictFDerivAt
    (fun m => (g' m).hasStrictFDerivAt) hCQ

/-- **Theorem M.K.1** (MWG, p. 956), as printed: `f` and the `g_m` are differentiable (on `ℝ^N`),
`x̄ ∈ C` is a local constrained maximizer and the constraint qualification holds. Then
`∇f(x̄) = ∑ λ_m ∇g_m(x̄)`. -/
theorem theorem_M_K_1_book {f : (Fin N → ℝ) → ℝ} {g : Fin M → (Fin N → ℝ) → ℝ}
    {b : Fin M → ℝ} {x : Fin N → ℝ} (hf : Differentiable ℝ f) (hg : ∀ m, Differentiable ℝ (g m))
    (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hCQ : LinearIndependent ℝ fun m => fderiv ℝ (g m) x) :
    ∃ lam : Fin M → ℝ, fderiv ℝ f x = ∑ m, lam m • fderiv ℝ (g m) x :=
  theorem_M_K_1_differentiable hx hmax (hf x).hasFDerivAt (fun m => (hg m x).hasFDerivAt)
    (fun m => Eventually.of_forall fun y => (hg m y).continuousAt) hCQ

/-- **Theorem M.K.2** (MWG, p. 959) for merely differentiable functions. Let `x̄` be a local
constrained maximizer of (M.K.4), `f` differentiable at `x̄`, every `g_m` and `h_k`
differentiable at `x̄` and continuous near `x̄`, and let the gradients of the equality and binding
inequality constraints be linearly independent. Then there are `λ_m` and `λ_k ≥ 0` with
`∇f(x̄) = ∑ λ_m ∇g_m(x̄) + ∑ λ_k ∇h_k(x̄)` and `λ_k (h_k(x̄) - c̄_k) = 0`. -/
theorem theorem_M_K_2_differentiable {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {h' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ} {c : Fin K → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ kktConstraintSet g b h c)
    (hmax : IsLocalMaxOn f (kktConstraintSet g b h c) x) (hf : HasFDerivAt f f' x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hh : ∀ k, HasFDerivAt (h k) (h' k) x)
    (hgc : ∀ m, ∀ᶠ y in 𝓝 x, ContinuousAt (g m) y)
    (hhc : ∀ k, ∀ᶠ y in 𝓝 x, ContinuousAt (h k) y)
    (hCQ : LinearIndependent ℝ (Sum.elim g' fun k : {k // h k x = c k} => h' k.1)) :
    ∃ lam : Fin M → ℝ, ∃ mu : Fin K → ℝ, (∀ k, 0 ≤ mu k) ∧
      f' = ∑ m, lam m • g' m + ∑ k, mu k • h' k ∧ ∀ k, mu k * (h k x - c k) = 0 := by
  classical
  set ι := Fin M ⊕ {k // h k x = c k}
  set φ : ι → (Fin N → ℝ) →L[ℝ] ℝ := Sum.elim g' fun k => h' k.1 with hφ
  set F : ι → (Fin N → ℝ) → ℝ := Sum.elim g fun k => h k.1 with hF
  set G : (Fin N → ℝ) → ι → ℝ := fun y i => F i y with hGdef
  have hG : HasFDerivAt G (ContinuousLinearMap.pi φ) x := by
    refine hasFDerivAt_pi.mpr ?_
    rintro (m | k)
    · exact hg m
    · exact hh k.1
  have hGc : ∀ᶠ y in 𝓝 x, ContinuousAt G y := by
    have hall : ∀ i, ∀ᶠ y in 𝓝 x, ContinuousAt (F i) y := by
      rintro (m | k)
      · exact hgc m
      · exact hhc k.1
    exact (eventually_all.mpr hall).mono fun y hy => continuousAt_pi.mpr hy
  have hsurj := mk_range_pi_eq_top hCQ
  -- inactive constraints stay slack near `x̄`
  have hslack : ∀ᶠ y in 𝓝 x, ∀ k, h k x < c k → h k y < c k := by
    rw [eventually_all]
    intro k
    by_cases hk : h k x < c k
    · exact ((hhc k).self_of_nhds.eventually (gt_mem_nhds hk)).mono fun y hy _ => hy
    · exact Eventually.of_forall fun y hk' => absurd hk' hk
  have hcone : ∀ z, (∀ m, g' m z = 0) → (∀ k, h k x = c k → h' k z ≤ 0) → f' z ≤ 0 := by
    intro z hz hzk
    refine hardHalkin_cone hmax hf hG hGc hsurj (hslack.mono fun y hy t ht hGy => ?_)
    refine ⟨fun m => ?_, fun k => ?_⟩
    · have := congrFun hGy (Sum.inl m)
      simp only [hGdef, hF, hφ, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
        ContinuousLinearMap.pi_apply, hz, smul_zero, add_zero] at this
      rw [this]
      exact hx.1 m
    · rcases (hx.2 k).lt_or_eq with hk | hk
      · exact (hy k hk).le
      · have := congrFun hGy (Sum.inr ⟨k, hk⟩)
        simp only [hGdef, hF, hφ, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
          ContinuousLinearMap.pi_apply, smul_eq_mul] at this
        rw [this, hk]
        have := hzk k hk
        nlinarith
  -- the linearized problem, with the same slacks
  set c' : Fin K → ℝ := fun k => h' k x + (c k - h k x) with hc'
  have hact : ∀ k, h' k x = c' k ↔ h k x = c k := fun k => by
    simp only [hc']
    constructor <;> intro H <;> linarith
  have hlin : IsLocalMaxOn (⇑f')
      (kktConstraintSet (fun m => ⇑(g' m)) (fun m => g' m x) (fun k => ⇑(h' k)) c') x := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => ?_
    have := hcone (y - x) (fun m => by rw [map_sub]; exact sub_eq_zero.mpr (hy.1 m))
      (fun k hk => by
        have := hy.2 k
        simp only [hc', hk, sub_self, add_zero] at this
        rw [map_sub]
        linarith)
    rw [map_sub] at this
    linarith
  have hxlin : x ∈ kktConstraintSet (fun m => ⇑(g' m)) (fun m => g' m x) (fun k => ⇑(h' k)) c' :=
    ⟨fun m => rfl, fun k => by simp only [hc']; linarith [hx.2 k]⟩
  have hCQ' : LinearIndependent ℝ (Sum.elim g' fun k : {k // h' k x = c' k} => h' k.1) := by
    have := hCQ.comp (Sum.map id fun k : {k // h' k x = c' k} =>
        (⟨k.1, (hact k.1).mp k.2⟩ : {k // h k x = c k}))
      (Sum.map_injective.mpr ⟨Function.injective_id,
        fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)⟩)
    convert this using 1
    funext i
    rcases i with m | k <;> rfl
  obtain ⟨lam, mu, hmu, hsum, hcs⟩ := theorem_M_K_2 hxlin hlin f'.hasStrictFDerivAt
    (fun m => (g' m).hasStrictFDerivAt) (fun k => (h' k).hasStrictFDerivAt) hCQ'
  refine ⟨lam, mu, hmu, hsum, fun k => ?_⟩
  have := hcs k
  have e : h' k x - c' k = h k x - c k := by simp only [hc']; ring
  rwa [e] at this

/-- **Theorem M.K.2** (MWG, p. 959), as printed: `f`, the `g_m` and the `h_k` are differentiable
(on `ℝ^N`), `x̄` is a local constrained maximizer of (M.K.4) and the constraint qualification
holds for the equality and binding inequality constraints. Then the Kuhn-Tucker conditions
(M.K.6)-(M.K.7) hold with `λ_k ≥ 0`. -/
theorem theorem_M_K_2_book {K : ℕ} {f : (Fin N → ℝ) → ℝ} {g : Fin M → (Fin N → ℝ) → ℝ}
    {b : Fin M → ℝ} {h : Fin K → (Fin N → ℝ) → ℝ} {c : Fin K → ℝ} {x : Fin N → ℝ}
    (hf : Differentiable ℝ f) (hg : ∀ m, Differentiable ℝ (g m)) (hh : ∀ k, Differentiable ℝ (h k))
    (hx : x ∈ kktConstraintSet g b h c) (hmax : IsLocalMaxOn f (kktConstraintSet g b h c) x)
    (hCQ : LinearIndependent ℝ
      (Sum.elim (fun m => fderiv ℝ (g m) x) fun k : {k // h k x = c k} => fderiv ℝ (h k.1) x)) :
    ∃ lam : Fin M → ℝ, ∃ mu : Fin K → ℝ, (∀ k, 0 ≤ mu k) ∧
      fderiv ℝ f x = ∑ m, lam m • fderiv ℝ (g m) x + ∑ k, mu k • fderiv ℝ (h k) x ∧
        ∀ k, mu k * (h k x - c k) = 0 :=
  theorem_M_K_2_differentiable hx hmax (hf x).hasFDerivAt (fun m => (hg m x).hasFDerivAt)
    (fun k => (hh k x).hasFDerivAt) (fun m => Eventually.of_forall fun y => (hg m y).continuousAt)
    (fun k => Eventually.of_forall fun y => (hh k y).continuousAt) hCQ

end MWG.ClassicalDemand
