/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMKSufficiency
import MWGClassicalDemand.AppendixMJ
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Mathematical Appendix M.K: shadow prices of inequality constraints, second-order sufficiency,
and the example on p. 964

MWG, Section M.K, pp. 958, 963-964.

* **Theorem M.K.5** with inequality constraints (`theorem_M_K_5_inequality`): at a solution
  `x̄` of (M.K.4) with Kuhn-Tucker multipliers `λ_m`, `λ_k` (complementary slackness), linearly
  independent gradients of the equality and binding inequality constraints, and a function `v`
  bounding the objective on nearby constraint sets with `v(b̄, c̄) = f(x̄)`, differentiability of
  `v` at `(b̄, c̄)` gives `∂v/∂b_m = λ_m` and `∂v/∂c_k = λ_k` for every `k` (for slack
  constraints both are `0`). As in `theorem_M_K_5`, no differentiability of the solution and no
  constancy of the binding set is needed.
* **Second-order sufficiency** (p. 958): if `x̄` is feasible, the Lagrangian `L` is stationary at
  `x̄`, twice differentiable there in the sense of Theorem M.J.2, and `D²L(x̄)` is negative
  definite on `{z : ∇g_m(x̄)·z = 0}`, then `x̄` is a strict local constrained maximizer
  (`theorem_M_K_second_order_sufficient`).
* **The example on p. 964**: maximize `x₁ + x₂` on `[0, 1]²` subject to `q₁x₁ + q₂x₂ ≤ q₁q₂`. For
  `q ∈ (0, 1)²` the maximizers are `(q₂, 0)`, `(0, q₁)` or the segment `x₁ + x₂ = q₁`
  (`example_M_K_964_argmax`); the maximizer correspondence has a closed graph on `(0, 1)²`
  (`example_M_K_964_closed_graph`) but is not lower hemicontinuous on the line `q₁ = q₂`
  (`example_M_K_964_not_lhc`); on `[0, 1]²` its graph is not closed at `0`, and the constraint
  correspondence is not lower hemicontinuous there (`example_M_K_964_boundary`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N M : ℕ}

/-- A linear functional on `ℝ^M × ℝ^K` is determined by its values on the unit vectors. -/
theorem closerMK_prod_decomp {K : ℕ} (v' : (Fin M → ℝ) × (Fin K → ℝ) →L[ℝ] ℝ)
    (a : Fin M → ℝ) (b : Fin K → ℝ) :
    v' (a, b) = ∑ m, a m * v' (Pi.single m 1, 0) + ∑ k, b k * v' (0, Pi.single k 1) := by
  have hab : (a, b) = ∑ m, a m • ((Pi.single m 1 : Fin M → ℝ), (0 : Fin K → ℝ)) +
      ∑ k, b k • ((0 : Fin M → ℝ), (Pi.single k 1 : Fin K → ℝ)) := by
    ext i
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hab, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- **Theorem M.K.5** (MWG, p. 963), with inequality constraints. Let `x̄` solve (M.K.4) at
`(b̄, c̄)`, with Kuhn-Tucker multipliers: `∇f(x̄) = ∑ λ_m ∇g_m(x̄) + ∑ μ_k ∇h_k(x̄)` and `μ_k = 0`
for slack constraints; let the gradients of the equality and binding inequality constraints be
linearly independent; and let `v(b, c)` bound `f` on the constraint set at `(b, c)` near
`(b̄, c̄)`, with `v(b̄, c̄) = f(x̄)` (e.g. the value function). If `v` is differentiable at
`(b̄, c̄)`, then `∂v/∂b_m = λ_m` and `∂v/∂c_k = μ_k` for all `m`, `k`. -/
theorem theorem_M_K_5_inequality {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {h' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {bbar : Fin M → ℝ} {cbar : Fin K → ℝ}
    {v : (Fin M → ℝ) × (Fin K → ℝ) → ℝ} {v' : (Fin M → ℝ) × (Fin K → ℝ) →L[ℝ] ℝ}
    (hxg : ∀ m, g m x = bbar m) (hxh : ∀ k, h k x ≤ cbar k) (hval : v (bbar, cbar) = f x)
    (hbound : ∀ᶠ q in 𝓝 (bbar, cbar), ∀ y, (∀ m, g m y = q.1 m) → (∀ k, h k y ≤ q.2 k) →
      f y ≤ v q)
    (hv : HasFDerivAt v v' (bbar, cbar)) (hf : HasFDerivAt f f' x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hh : ∀ k, HasFDerivAt (h k) (h' k) x)
    (hCQ : LinearIndependent ℝ (Sum.elim g' (fun k : {k // h k x = cbar k} => h' k)))
    {lam : Fin M → ℝ} {mu : Fin K → ℝ} (hslack : ∀ k, h k x < cbar k → mu k = 0)
    (hlam : f' = ∑ m, lam m • g' m + ∑ k, mu k • h' k) :
    (∀ m, v' (Pi.single m 1, 0) = lam m) ∧ ∀ k, v' (0, Pi.single k 1) = mu k := by
  classical
  -- slack constraints: moving `c_k` a little does not change feasibility of `x̄`
  have hnb : ∀ k, h k x < cbar k → v' (0, Pi.single k 1) = 0 := by
    intro k hk
    set γ : ℝ → (Fin M → ℝ) × (Fin K → ℝ) := fun t => (bbar, cbar + t • Pi.single k 1) with hγ
    have hγd : HasDerivAt γ ((0 : Fin M → ℝ), (Pi.single k 1 : Fin K → ℝ)) 0 := by
      have h2 : HasDerivAt (fun t : ℝ => cbar + t • (Pi.single k 1 : Fin K → ℝ))
          (Pi.single k 1) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ) : Fin K → ℝ)).const_add
          cbar
        simpa using this
      exact (hasDerivAt_const (0 : ℝ) bbar).prodMk h2
    have hγ0 : γ 0 = (bbar, cbar) := by simp [hγ]
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq 0 hv hγd hγ0.symm
    have hmin : IsLocalMin (v ∘ γ) 0 := by
      have hcont : Tendsto γ (𝓝 0) (𝓝 (bbar, cbar)) := by
        have := hγd.continuousAt.tendsto
        rwa [hγ0] at this
      have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), h k x - cbar k < t :=
        lt_mem_nhds (by linarith)
      filter_upwards [hcont.eventually hbound, hnear] with t ht htk
      simp only [Function.comp_apply, hγ0, hval]
      refine ht x hxg fun k' => ?_
      simp only [hγ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hkk : k' = k
      · subst hkk
        simp only [Pi.single_eq_same, mul_one]
        linarith
      · simp only [Pi.single_eq_of_ne hkk, mul_zero, add_zero]
        exact hxh k'
    exact hmin.hasDerivAt_eq_zero hcomp
  -- binding constraints and equality constraints
  set G : (Fin N → ℝ) → Fin M → ℝ := fun y m => g m y with hG
  set C : (Fin N → ℝ) → Fin K → ℝ := fun y k => if h k x = cbar k then h k y else cbar k with hC
  set C' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ := fun k => if h k x = cbar k then h' k else 0 with hC'
  have hGd : HasFDerivAt G (ContinuousLinearMap.pi g') x := hasFDerivAt_pi.mpr hg
  have hCd : HasFDerivAt C (ContinuousLinearMap.pi C') x := by
    refine hasFDerivAt_pi.mpr fun k => ?_
    by_cases hk : h k x = cbar k
    · simp only [hC', hk, ↓reduceIte]
      exact hh k
    · simp only [hC', hk, ↓reduceIte]
      exact hasFDerivAt_const _ _
  have hΦ : HasFDerivAt (fun y => (G y, C y))
      ((ContinuousLinearMap.pi g').prod (ContinuousLinearMap.pi C')) x := hGd.prodMk hCd
  have hΦx : (G x, C x) = (bbar, cbar) := by
    refine Prod.ext (funext hxg) (funext fun k => ?_)
    by_cases hk : h k x = cbar k
    · simp [hC, hk]
    · simp [hC, hk]
  have hψ : HasFDerivAt (fun y => v (G y, C y) - f y)
      (v'.comp ((ContinuousLinearMap.pi g').prod (ContinuousLinearMap.pi C')) - f') x :=
    (by
      have hv' : HasFDerivAt v v' (G x, C x) := by rw [hΦx]; exact hv
      exact (hv'.comp x hΦ).sub hf)
  have hmin : IsLocalMin (fun y => v (G y, C y) - f y) x := by
    have hcont : Tendsto (fun y => (G y, C y)) (𝓝 x) (𝓝 (bbar, cbar)) := by
      have := hΦ.continuousAt.tendsto
      rwa [hΦx] at this
    have hslackev : ∀ᶠ y in 𝓝 x, ∀ k, h k x < cbar k → h k y < cbar k := by
      rw [eventually_all]
      intro k
      by_cases hk : h k x < cbar k
      · filter_upwards [(hh k).continuousAt.eventually (gt_mem_nhds hk)] with y hy _ using hy
      · exact Eventually.of_forall fun y hk' => absurd hk' hk
    filter_upwards [hcont.eventually hbound, hslackev] with y hy hys
    have hfeas : f y ≤ v (G y, C y) := by
      refine hy y (fun m => rfl) fun k => ?_
      by_cases hk : h k x = cbar k
      · simp [hC, hk]
      · simp only [hC, hk, ↓reduceIte]
        exact (hys k (lt_of_le_of_ne (hxh k) hk)).le
    have h0 : v (G x, C x) - f x = 0 := by rw [hΦx, hval, sub_self]
    rw [h0]
    linarith
  have hzero := hmin.hasFDerivAt_eq_zero hψ
  -- coefficients of a vanishing combination
  have hcomb : ∀ w, ∑ m, (v' (Pi.single m 1, 0) - lam m) * g' m w +
      ∑ k : {k // h k x = cbar k}, (v' (0, Pi.single k.1 1) - mu k.1) * h' k.1 w = 0 := by
    intro w
    have h1 := congrArg (fun φ : (Fin N → ℝ) →L[ℝ] ℝ => φ w) hzero
    simp only [sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, zero_apply, ContinuousLinearMap.prod_apply] at h1
    rw [closerMK_prod_decomp, hlam] at h1
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.pi_apply] at h1
    have hsplit : ∀ F : Fin K → ℝ, ∑ k, F k =
        ∑ k : {k // h k x = cbar k}, F k.1 + ∑ k ∈ Finset.univ.filter (fun k => ¬ h k x = cbar k),
          F k := by
      intro F
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => h k x = cbar k),
        ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    have e1 := hsplit fun k => C' k w * v' (0, Pi.single k 1)
    have e2 := hsplit fun k => mu k * h' k w
    have z1 : ∑ k ∈ Finset.univ.filter (fun k => ¬ h k x = cbar k),
        C' k w * v' (0, Pi.single k 1) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        simp only [Finset.mem_filter] at hk
        simp [hC', hk.2]
    have z2 : ∑ k ∈ Finset.univ.filter (fun k => ¬ h k x = cbar k), mu k * h' k w = 0 :=
      Finset.sum_eq_zero fun k hk => by
        simp only [Finset.mem_filter] at hk
        rw [hslack k (lt_of_le_of_ne (hxh k) hk.2), zero_mul]
    have e3 : ∑ k : {k // h k x = cbar k}, C' k.1 w * v' (0, Pi.single k.1 1) =
        ∑ k : {k // h k x = cbar k}, h' k.1 w * v' (0, Pi.single k.1 1) :=
      Finset.sum_congr rfl fun k _ => by simp [hC', k.2]
    rw [e1, e2, z1, z2, e3, add_zero, add_zero] at h1
    have : ∑ m, (v' (Pi.single m 1, 0) - lam m) * g' m w +
        ∑ k : {k // h k x = cbar k}, (v' (0, Pi.single k.1 1) - mu k.1) * h' k.1 w =
        (∑ m, g' m w * v' (Pi.single m 1, 0) +
          ∑ k : {k // h k x = cbar k}, h' k.1 w * v' (0, Pi.single k.1 1)) -
        (∑ m, lam m * g' m w + ∑ k : {k // h k x = cbar k}, mu k.1 * h' k.1 w) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [show ∑ m, v' (Pi.single m 1, 0) * g' m w = ∑ m, g' m w * v' (Pi.single m 1, 0) from
        Finset.sum_congr rfl fun m _ => mul_comm _ _,
        show ∑ k : {k // h k x = cbar k}, v' (0, Pi.single k.1 1) * h' k.1 w =
          ∑ k : {k // h k x = cbar k}, h' k.1 w * v' (0, Pi.single k.1 1) from
        Finset.sum_congr rfl fun k _ => mul_comm _ _]
      ring
    rw [this]
    linarith
  set c : Fin M ⊕ {k // h k x = cbar k} → ℝ :=
    Sum.elim (fun m => v' (Pi.single m 1, 0) - lam m) (fun k => v' (0, Pi.single k.1 1) - mu k.1)
    with hc
  have hc0 : ∑ i, c i • Sum.elim g' (fun k : {k // h k x = cbar k} => h' k) i = 0 := by
    ext w
    rw [Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, add_apply,
      sum_apply, smul_apply, smul_eq_mul,
      zero_apply]
    exact hcomb w
  have hci := (Fintype.linearIndependent_iff.mp hCQ) c hc0
  refine ⟨fun m => ?_, fun k => ?_⟩
  · have := hci (Sum.inl m)
    simp only [hc, Sum.elim_inl] at this
    linarith
  · by_cases hk : h k x = cbar k
    · have := hci (Sum.inr ⟨k, hk⟩)
      simp only [hc, Sum.elim_inr] at this
      linarith
    · have hlt := lt_of_le_of_ne (hxh k) hk
      rw [hnb k hlt, hslack k hlt]


/-- **Section M.K** (MWG, p. 958), second-order sufficiency, the key estimate: if the
Lagrangian `L` is differentiable near `x̄`, stationary at `x̄`, and `∇L` has derivative `D2` at
`x̄`, then for every `ε > 0`, near `x̄`, `L(y) ≥ L(x̄)` forces `D2 h h ≥ -ε ‖h‖²`, `h = y - x̄`. -/
theorem closerMK_second_order_estimate {F : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y) (hgrad : fderiv ℝ F x = 0)
    (h2 : HasFDerivAt (fderiv ℝ F) D2 x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, F x ≤ F y → -ε * ‖y - x‖ ^ 2 ≤ D2 (y - x) (y - x) := by
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp h2).def hε
  rw [hgrad] at hlo
  obtain ⟨ρ1, hρ1, hset1⟩ := Metric.eventually_nhds_iff.mp hlo
  obtain ⟨ρ2, hρ2, hset2⟩ := Metric.eventually_nhds_iff.mp hdiff
  rw [Metric.eventually_nhds_iff]
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun y hy hFy => ?_⟩
  set h := y - x with hh
  rcases eq_or_ne h 0 with h0 | hhne
  · rw [h0]
    simp
  have hhn : ‖h‖ < min ρ1 ρ2 := by rwa [hh, ← dist_eq_norm]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t • h‖ < min ρ1 ρ2 := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hhn
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => F (x + s • h)) (fderiv ℝ F (x + t • h) h) t := by
    intro t ht
    have : dist (x + t • h) x < ρ2 := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact (hpt t ht).trans_le (min_le_right _ _)
    exact mc_line_hasDerivAt_at (hset2 this).hasFDerivAt
  obtain ⟨θ, hθ, hθeq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => F (x + s • h))
    (fun s => fderiv ℝ F (x + s • h) h) one_pos
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hθeq
  have hyx : y = x + h := by rw [hh, add_sub_cancel]
  have hθh : dist (θ • h) 0 < ρ1 := by
    rw [dist_zero_right]
    exact (hpt θ ⟨hθ.1.le, hθ.2.le⟩).trans_le (min_le_left _ _)
  have hb := hset1 hθh
  simp only [sub_zero] at hb
  have hop : |(fderiv ℝ F (x + θ • h) - D2 (θ • h)) h| ≤ ε * ‖θ • h‖ * ‖h‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ F (x + θ • h) - D2 (θ • h)).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg h))
  have hlin : D2 (θ • h) h = θ * D2 h h := by
    rw [map_smul]
    rfl
  have hnorm : ‖θ • h‖ = θ * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg hθ.1.le]
  have hsub : (fderiv ℝ F (x + θ • h) - D2 (θ • h)) h = fderiv ℝ F (x + θ • h) h -
      D2 (θ • h) h := rfl
  rw [hsub, hlin, hnorm] at hop
  have h1 := (abs_le.mp hop).2
  have hge : 0 ≤ fderiv ℝ F (x + θ • h) h := by
    rw [hθeq, ← hyx]
    linarith
  have h3 : 0 ≤ D2 h h + ε * ‖h‖ ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_pos_of_neg hθ.1 hc]
  linarith

/-- **Section M.K** (MWG, p. 958), second-order sufficient conditions. Let `x̄` be feasible
(`g_m(x̄) = b̄_m`), the constraints differentiable at `x̄`, and the Lagrangian
`L(x) = f(x) - ∑ λ_m (g_m(x) - b̄_m)` differentiable near `x̄`, stationary at `x̄` (the
first-order conditions (M.K.2)), with `∇L` differentiable at `x̄` with second derivative
`D²_x L`. If `D²_x L(x̄, λ)` is negative definite on `{z : ∇g_m(x̄)·z = 0 for all m}`, then `x̄`
is a strict local constrained maximizer. -/
theorem theorem_M_K_second_order_sufficient {f : (Fin N → ℝ) → ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {b lam : Fin M → ℝ} {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hxg : ∀ m, g m x = b m) (hg : ∀ m, HasFDerivAt (g m) (g' m) x)
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => lagrangian f g b y lam) y)
    (hgrad : fderiv ℝ (fun y => lagrangian f g b y lam) x = 0)
    (h2 : HasFDerivAt (fderiv ℝ (fun y => lagrangian f g b y lam)) D2 x)
    (hnd : ∀ z, z ≠ 0 → (∀ m, g' m z = 0) → D2 z z < 0) :
    ∀ᶠ y in 𝓝 x, (∀ m, g m y = b m) → y ≠ x → f y < f x := by
  set F := fun y => lagrangian f g b y lam with hF
  have hFeq : ∀ y, (∀ m, g m y = b m) → F y = f y := by
    intro y hy
    simp [hF, lagrangian, hy]
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hseq : ∀ n : ℕ, ∃ y, ((∀ m, g m y = b m) ∧ y ≠ x ∧ f x ≤ f y) ∧
      dist y x < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hy1, hy2⟩ := (hcon.and_eventually (Metric.ball_mem_nhds x
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))).exists
    push Not at hy1
    exact ⟨y, ⟨hy1.1, hy1.2.1, hy1.2.2⟩, hy2⟩
  choose y hy hyd using hseq
  have hyt : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hne : ∀ n, y n - x ≠ 0 := fun n => sub_ne_zero.2 (hy n).2.1
  set d : ℕ → Fin N → ℝ := fun n => ‖y n - x‖⁻¹ • (y n - x) with hd
  have hdn : ∀ n, d n ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    intro n
    rw [mem_sphere_iff_norm, sub_zero, hd, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hne n))]
  obtain ⟨d0, hd0, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).tendsto_subseq hdn
  have hd00 : d0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hd0
    exact zero_ne_one hd0
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 x) := hyt.comp hφ.tendsto_atTop
  have hscale : ∀ n, y n - x = ‖y n - x‖ • d n := by
    intro n
    rw [hd, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (hne n)), one_smul]
  -- the limit direction is tangent to the constraint set
  have htan : ∀ m, g' m d0 = 0 := by
    intro m
    have hlim' : Tendsto (fun n => g' m (d (φ n))) atTop (𝓝 (g' m d0)) :=
      ((g' m).continuous.tendsto d0).comp hlim
    have hsmall : ∀ ε > 0, ∀ᶠ n in atTop, |g' m (d (φ n))| ≤ ε := by
      intro ε hε
      have hev := hyφ.eventually ((hg m).isLittleO.def hε)
      filter_upwards [hev] with n hn
      simp only [Function.comp_apply, hxg m, (hy (φ n)).1 m, sub_self, zero_sub,
        norm_neg] at hn
      have hpos : 0 < ‖y (φ n) - x‖ := norm_pos_iff.2 (hne (φ n))
      have hdφ : d (φ n) = ‖y (φ n) - x‖⁻¹ • (y (φ n) - x) := rfl
      rw [hdφ, map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, ← Real.norm_eq_abs]
      rw [inv_mul_le_iff₀ hpos]
      linarith
    have : |g' m d0| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hlim') (hsmall ε hε)
    exact abs_nonpos_iff.1 this
  -- the second-order term is nonnegative in the limit
  have hquad : ∀ (r : ℝ) (u : Fin N → ℝ), D2 (r • u) (r • u) = r ^ 2 * D2 u u := by
    intro r u
    rw [map_smul, map_smul]
    change r • (r • D2 u u) = _
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have hq : 0 ≤ D2 d0 d0 := by
    have hcont : Tendsto (fun n => D2 (d (φ n)) (d (φ n))) atTop (𝓝 (D2 d0 d0)) :=
      ((D2.continuous.clm_apply continuous_id).tendsto d0).comp hlim
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev := hyφ.eventually (closerMK_second_order_estimate hdiff hgrad h2 hε)
    have hev' : ∀ᶠ n in atTop, -ε ≤ D2 (d (φ n)) (d (φ n)) := by
      filter_upwards [hev] with n hn
      have hFle : F x ≤ F (y (φ n)) := by
        rw [hFeq x hxg, hFeq _ (hy (φ n)).1]
        exact (hy (φ n)).2.2
      have := hn hFle
      simp only [Function.comp_apply] at this
      have hpos : 0 < ‖y (φ n) - x‖ := norm_pos_iff.2 (hne (φ n))
      have hq2 : D2 (y (φ n) - x) (y (φ n) - x) =
          ‖y (φ n) - x‖ ^ 2 * D2 (d (φ n)) (d (φ n)) := by
        have e := hscale (φ n)
        calc D2 (y (φ n) - x) (y (φ n) - x) =
            D2 (‖y (φ n) - x‖ • d (φ n)) (‖y (φ n) - x‖ • d (φ n)) := by rw [← e]
          _ = _ := hquad _ _
      rw [hq2] at this
      have h2pos : 0 < ‖y (φ n) - x‖ ^ 2 := by positivity
      nlinarith
    have := ge_of_tendsto hcont hev'
    linarith
  exact absurd (hnd d0 hd00 htan) (not_lt.2 hq)


/-- **Section M.K, small type** (MWG, p. 964). The constraint set
`{x ∈ [0, 1]² : q₁x₁ + q₂x₂ ≤ q₁q₂}`. -/
def mk964Constraint (q : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 ∧ q 0 * x 0 + q 1 * x 1 ≤ q 0 * q 1}

/-- **Section M.K, small type** (MWG, p. 964). The maximizers of `x₁ + x₂` on the constraint
set. -/
def mk964Argmax (q : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ mk964Constraint q ∧ ∀ y ∈ mk964Constraint q, y 0 + y 1 ≤ x 0 + x 1}

/-- For `q ∈ (0, 1)²` the maximizers are the feasible points with `x₁ + x₂ = max {q₁, q₂}`. -/
theorem mk964_argmax_iff {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h0' : q 0 < 1) (h1 : 0 < q 1)
    (h1' : q 1 < 1) (x : Fin 2 → ℝ) :
    x ∈ mk964Argmax q ↔ x ∈ mk964Constraint q ∧ x 0 + x 1 = max (q 0) (q 1) := by
  have hbound : ∀ y ∈ mk964Constraint q, y 0 + y 1 ≤ max (q 0) (q 1) := by
    rintro y ⟨hy0, -, hy1, -, hyq⟩
    rcases le_total (q 0) (q 1) with h | h
    · rw [max_eq_right h]
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right h hy1]
    · rw [max_eq_left h]
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right h hy0]
  obtain ⟨z, hz, hzv⟩ : ∃ z ∈ mk964Constraint q, z 0 + z 1 = max (q 0) (q 1) := by
    rcases le_total (q 0) (q 1) with h | h
    · refine ⟨![q 1, 0], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [max_eq_right h] <;> linarith
    · refine ⟨![0, q 0], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [max_eq_left h] <;> nlinarith
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (hbound x hx) (hzv ▸ hmax z hz)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun y hy => heq ▸ hbound y hy⟩

/-- **Section M.K, small type** (MWG, p. 964). For `q ∈ (0, 1)²`:
`x(q) = {(q₂, 0)}` if `q₁ < q₂`, `x(q) = {(0, q₁)}` if `q₂ < q₁`, and
`x(q) = {x ∈ [0, 1]² : x₁ + x₂ = q₁}` if `q₁ = q₂`. -/
theorem example_M_K_964_argmax {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h0' : q 0 < 1) (h1 : 0 < q 1)
    (h1' : q 1 < 1) :
    (q 0 < q 1 → mk964Argmax q = {![q 1, 0]}) ∧ (q 1 < q 0 → mk964Argmax q = {![0, q 0]}) ∧
      (q 0 = q 1 → mk964Argmax q =
        {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 ∧ x 0 + x 1 = q 0}) := by
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun heq => ?_⟩
  · ext x
    rw [mk964_argmax_iff h0 h0' h1 h1', max_eq_right hlt.le, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx0, hx0', hx1, hx1', hq⟩, hs⟩
      have hx1z : x 1 = 0 := by nlinarith
      funext j
      fin_cases j
      · simp; linarith
      · simpa using hx1z
    · rintro rfl
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp <;> linarith
  · ext x
    rw [mk964_argmax_iff h0 h0' h1 h1', max_eq_left hlt.le, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx0, hx0', hx1, hx1', hq⟩, hs⟩
      have hx0z : x 0 = 0 := by nlinarith
      funext j
      fin_cases j
      · simpa using hx0z
      · simp; linarith
    · rintro rfl
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp <;> nlinarith
  · ext x
    rw [mk964_argmax_iff h0 h0' h1 h1', ← heq, max_self]
    simp only [mk964Constraint, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx0, hx0', hx1, hx1', -⟩, hs⟩
      exact ⟨hx0, hx0', hx1, hx1', hs⟩
    · rintro ⟨hx0, hx0', hx1, hx1', hs⟩
      refine ⟨⟨hx0, hx0', hx1, hx1', ?_⟩, hs⟩
      rw [← heq]
      nlinarith

/-- **Section M.K, small type** (MWG, p. 964). On `Q = (0, 1)²` the maximizer correspondence
has a closed graph (with values in the compact `[0, 1]²`, so it is upper hemicontinuous, as
Theorem M.K.6 predicts). -/
theorem example_M_K_964_closed_graph {qs : ℕ → Fin 2 → ℝ} {xs : ℕ → Fin 2 → ℝ}
    {q x : Fin 2 → ℝ} (hq0 : 0 < q 0) (hq0' : q 0 < 1) (hq1 : 0 < q 1) (hq1' : q 1 < 1)
    (hQ : ∀ n, 0 < qs n 0 ∧ qs n 0 < 1 ∧ 0 < qs n 1 ∧ qs n 1 < 1)
    (hxs : ∀ n, xs n ∈ mk964Argmax (qs n)) (hqt : Tendsto qs atTop (𝓝 q))
    (hxt : Tendsto xs atTop (𝓝 x)) : x ∈ mk964Argmax q := by
  rw [mk964_argmax_iff hq0 hq0' hq1 hq1']
  have hc : ∀ n, xs n ∈ mk964Constraint (qs n) ∧ xs n 0 + xs n 1 = max (qs n 0) (qs n 1) :=
    fun n => (mk964_argmax_iff (hQ n).1 (hQ n).2.1 (hQ n).2.2.1 (hQ n).2.2.2 _).1 (hxs n)
  have tq : ∀ i, Tendsto (fun n => qs n i) atTop (𝓝 (q i)) := fun i =>
    (continuous_apply i).continuousAt.tendsto.comp hqt
  have tx : ∀ i, Tendsto (fun n => xs n i) atTop (𝓝 (x i)) := fun i =>
    (continuous_apply i).continuousAt.tendsto.comp hxt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ge_of_tendsto' (tx 0) fun n => (hc n).1.1
  · exact le_of_tendsto' (tx 0) fun n => (hc n).1.2.1
  · exact ge_of_tendsto' (tx 1) fun n => (hc n).1.2.2.1
  · exact le_of_tendsto' (tx 1) fun n => (hc n).1.2.2.2.1
  · exact le_of_tendsto_of_tendsto' (((tq 0).mul (tx 0)).add ((tq 1).mul (tx 1)))
      ((tq 0).mul (tq 1)) fun n => (hc n).1.2.2.2.2
  · exact tendsto_nhds_unique ((tx 0).add (tx 1))
      (((tq 0).max (tq 1)).congr fun n => ((hc n).2).symm)

/-- **Section M.K, small type** (MWG, p. 964). The maximizer correspondence is not continuous:
at `q̄ = (1/2, 1/2)` the point `(1/4, 1/4)` is a maximizer, but along `qⁿ = (1/2 - 1/(n+3), 1/2)`
the only maximizer is `(1/2, 0)`, so no maximizers at `qⁿ` approach `(1/4, 1/4)` (lower
hemicontinuity fails on the line `q₁ = q₂`). -/
theorem example_M_K_964_not_lhc :
    ![1 / 4, 1 / 4] ∈ mk964Argmax ![1 / 2, 1 / 2] ∧
      Tendsto (fun n : ℕ => ![1 / 2 - 1 / ((n : ℝ) + 3), 1 / 2]) atTop (𝓝 ![1 / 2, 1 / 2]) ∧
      ¬ ∃ xs : ℕ → Fin 2 → ℝ, (∀ n : ℕ, xs n ∈ mk964Argmax ![1 / 2 - 1 / ((n : ℝ) + 3), 1 / 2]) ∧
        Tendsto xs atTop (𝓝 ![1 / 4, 1 / 4]) := by
  have hn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 3) ∧ 1 / ((n : ℝ) + 3) < 1 / 2 := by
    intro n
    refine ⟨by positivity, ?_⟩
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [(example_M_K_964_argmax (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2
      (by norm_num)]
    simp only [Set.mem_ofPred_eq]
    norm_num
  · rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
        refine this.congr fun n => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
        ring_nf
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
    · simp
  · rintro ⟨xs, hxs, hlim⟩
    have hconst : ∀ n, xs n = ![1 / 2, 0] := by
      intro n
      obtain ⟨a, b⟩ := hn n
      rw [one_div] at a b
      have hm := (example_M_K_964_argmax (q := ![1 / 2 - 1 / ((n : ℝ) + 3), 1 / 2])
        (by simp; linarith) (by simp; linarith) (by norm_num) (by norm_num)).1
        (by simp; linarith)
      have := hxs n
      rw [hm] at this
      simpa using this
    have hxs' : xs = fun _ => ![1 / 2, 0] := funext hconst
    rw [hxs'] at hlim
    have := tendsto_nhds_unique hlim tendsto_const_nhds
    have h0 := congrFun this 0
    norm_num at h0

/-- **Section M.K, small type** (MWG, p. 964). On `Q = [0, 1]²` the conclusion of Theorem M.K.6
fails at `q = 0`: `x(0, 0) = {(1, 1)}` while `x(2ε, ε) = {(0, 2ε)}` for small `ε > 0`, so the
graph of `x(·)` is not closed; and the hypothesis fails too: `(1, 1)` is feasible at `q = 0`,
but at `q = (ε, ε)` every feasible `x` has `x₁ + x₂ ≤ ε`. -/
theorem example_M_K_964_boundary :
    mk964Argmax 0 = {![1, 1]} ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → mk964Argmax ![2 * ε, ε] = {![0, 2 * ε]}) ∧
      ![1, 1] ∈ mk964Constraint 0 ∧
      ∀ ε : ℝ, 0 < ε → ∀ y ∈ mk964Constraint ![ε, ε], y 0 + y 1 ≤ ε := by
  refine ⟨?_, fun ε hε hε' => ?_, ?_, fun ε hε y hy => ?_⟩
  · ext x
    simp only [mk964Argmax, mk964Constraint, Pi.zero_apply, zero_mul, add_zero, le_refl,
      and_true, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx0, hx0', hx1, hx1'⟩, hmax⟩
      have := hmax ![1, 1] ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      funext j
      fin_cases j
      · simp; linarith
      · simp; linarith
    · rintro rfl
      refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, fun y hy => ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [hy.2.1, hy.2.2.2]
  · have := (example_M_K_964_argmax (q := ![2 * ε, ε]) (by simp; linarith)
      (by simp; linarith) (by simpa using hε) (by simp; linarith)).2.1 (by simp; linarith)
    simpa using this
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
  · obtain ⟨-, -, -, -, hq⟩ := hy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hq
    by_contra hc
    push Not at hc
    nlinarith

end MWG.ClassicalDemand
