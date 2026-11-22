/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExerciseB7
import MWGPrincipalAgent.ExercisesC

/-!
# Exercise 14.C.3(a): necessity of the first-order conditions

MWG, Exercise 14.C.3(a), p. 509. With utility `v(w) - g(e, θ)` the optimal full-information
contract pays the same wage `w̄` in both states (`exercise_14_C_3a`), the participation constraint
binds, and `exercise_14_C_3a_sufficient` shows that the first-order conditions
`π'(e_i) v'(w̄) = g_e(e_i, θ_i)` are sufficient.

* `exercise_14_C_3a_necessary`: at an optimal contract `(w̄, e_H), (w̄, e_L)` with interior efforts
  the first-order conditions hold. The proof raises the effort in one state and pays the wage
  that keeps that state's utility (a local inverse of `v`, `b7_local_inv`); the change is
  feasible and the owner's payoff has a local maximum at the optimum.
* `exercise_14_C_3a_necessary_instance`: a proved instance.
-/

namespace MWG.PrincipalAgent

open Filter Topology

/-- One state of Exercise 14.C.3(a): if raising the effort from `e > 0` to `e + s` and paying a
wage `w'` that keeps the state's utility, `v(w') - g(e + s) = v(w̄) - g(e)`, never yields more than
`π(e) - w̄`, then `π'(e) v'(w̄) = g_e(e)`. -/
theorem c3_foc_state {v dv prof : ℝ → ℝ} {gθ : ℝ → ℝ} {dp ge wbar e : ℝ}
    (hdv : ∀ w, HasDerivAt v (dv w) w) (hdvpos : ∀ w, 0 < dv w) (he : 0 < e)
    (hdp : HasDerivAt prof dp e) (hg : HasDerivAt gθ ge e)
    (hopt : ∀ w' s, 0 ≤ e + s → v w' - gθ (e + s) = v wbar - gθ e →
      prof (e + s) - w' ≤ prof e - wbar) :
    dp * dv wbar = ge := by
  obtain ⟨G, hG0, hev, hdG⟩ := b7_local_inv hdv hdvpos wbar
  have hg1 : HasDerivAt (fun s => gθ (e + s)) ge 0 := HasDerivAt.comp_const_add e 0 (by simpa)
  have hp1 : HasDerivAt (fun s => prof (e + s)) dp 0 := HasDerivAt.comp_const_add e 0 (by simpa)
  have hdy : HasDerivAt (fun s => v wbar + (gθ (e + s) - gθ e)) ge 0 :=
    (hg1.sub_const (gθ e)).const_add (v wbar)
  have hy0 : v wbar + (gθ (e + 0) - gθ e) = v wbar := by simp
  have hψ : HasDerivAt (fun s => prof (e + s) - G (v wbar + (gθ (e + s) - gθ e)))
      (dp - (dv wbar)⁻¹ * ge) 0 :=
    hp1.sub (HasDerivAt.comp_of_eq 0 hdG hdy hy0.symm)
  have ht : Tendsto (fun s => v wbar + (gθ (e + s) - gθ e)) (𝓝 0) (𝓝 (v wbar)) := by
    have := hdy.continuousAt.tendsto
    rwa [hy0] at this
  have hmax : IsLocalMax (fun s => prof (e + s) - G (v wbar + (gθ (e + s) - gθ e))) 0 := by
    filter_upwards [ht.eventually hev, Ioo_mem_nhds (show -e < 0 by linarith) he] with s hs hs2
    have h := hopt (G (v wbar + (gθ (e + s) - gθ e))) s (by linarith [hs2.1]) (by rw [hs]; ring)
    simp only [add_zero, sub_self, hG0]
    exact h
  have h0 := hmax.hasDerivAt_eq_zero hψ
  have := hdvpos wbar
  field_simp at h0
  linarith

/-- **Exercise 14.C.3(a)** (MWG, p. 509), necessity of the first-order conditions. Let
`(w̄, e_H), (w̄, e_L)` with `e_H, e_L > 0` be an optimal full-information contract (by
`exercise_14_C_3a` every optimum pays a single wage) with binding participation constraint, and let
`π` and `g(·, θ_i)` be differentiable at `e_i`. Then `π'(e_i) v'(w̄) = g_e(e_i, θ_i)` in both
states. -/
theorem exercise_14_C_3a_necessary {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    {dpH dpL geH geL θL θH lam ubar wbar eH eL : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hdv : ∀ w, HasDerivAt v (dv w) w) (hdvpos : ∀ w, 0 < dv w) (hH : 0 < eH) (hL : 0 < eL)
    (hdpH : HasDerivAt prof dpH eH) (hdpL : HasDerivAt prof dpL eL)
    (hgH : HasDerivAt (fun e => g e θH) geH eH) (hgL : HasDerivAt (fun e => g e θL) geL eL)
    (hbind : lam * (v wbar - g eH θH) + (1 - lam) * (v wbar - g eL θL) = ubar)
    (hopt : ∀ wH' eH' wL' eL', 0 ≤ eH' → 0 ≤ eL' →
      ubar ≤ lam * (v wH' - g eH' θH) + (1 - lam) * (v wL' - g eL' θL) →
      lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL') ≤
        lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar)) :
    dpH * dv wbar = geH ∧ dpL * dv wbar = geL := by
  refine ⟨c3_foc_state (gθ := fun e => g e θH) hdv hdvpos hH hdpH hgH fun w' s hs hu => ?_,
    c3_foc_state (gθ := fun e => g e θL) hdv hdvpos hL hdpL hgL fun w' s hs hu => ?_⟩
  · have hu' : v w' - g (eH + s) θH = v wbar - g eH θH := hu
    have h := hopt w' (eH + s) wbar eL hs hL.le (le_of_eq (by rw [← hbind, hu']))
    have := le_of_mul_le_mul_left (show lam * (prof (eH + s) - w') ≤ lam * (prof eH - wbar) by
      linarith) hl0
    exact this
  · have hu' : v w' - g (eL + s) θL = v wbar - g eL θL := hu
    have h := hopt wbar eH w' (eL + s) hH.le hs (le_of_eq (by rw [← hbind, hu']))
    exact le_of_mul_le_mul_left (show (1 - lam) * (prof (eL + s) - w') ≤
      (1 - lam) * (prof eL - wbar) by linarith) (by linarith)

/-- **Exercise 14.C.3(a), an instance** (MWG, p. 509). `v(w) = -exp(-w)`, `π(e) = e`,
`g(e, θ) = e²/(2θ²)`, `θ_H = 2`, `θ_L = 1`, `λ = 1/2`, `ū = -9/4`: the contract `w̄ = 0`,
`e_H = 4`, `e_L = 1` is optimal (`exercise_14_C_3a_suff`) and satisfies the first-order
conditions, as `exercise_14_C_3a_necessary` requires. -/
theorem exercise_14_C_3a_necessary_instance :
    (1 : ℝ) * Real.exp (-0) = 4 / 2 ^ 2 ∧ (1 : ℝ) * Real.exp (-0) = 1 / 1 ^ 2 := by
  have hconv : ∀ θ : ℝ, ConvexOn ℝ (Set.Ici 0) fun e : ℝ => e ^ 2 / (2 * θ ^ 2) := by
    intro θ
    have : (fun e : ℝ => e ^ 2 / (2 * θ ^ 2)) = fun e => (1 / (2 * θ ^ 2)) • e ^ 2 := by
      funext e; simp only [smul_eq_mul]; ring
    rw [this]
    exact (even_two.convexOn_pow.subset (Set.subset_univ _) (convex_Ici 0)).smul (by positivity)
  have hdg : ∀ θ e : ℝ, HasDerivAt (fun e : ℝ => e ^ 2 / (2 * θ ^ 2)) (e / θ ^ 2) e := by
    intro θ e
    have := (hasDerivAt_pow 2 e).div_const (2 * θ ^ 2)
    convert this using 1
    rcases eq_or_ne θ 0 with h | h
    · subst h; simp
    · field_simp; ring
  have hopt := fun (wH' eH' wL' eL' : ℝ) (h1 : (0 : ℝ) ≤ eH') (h2 : (0 : ℝ) ≤ eL')
      (h3 : -9 / 4 ≤ 1 / 2 * (-Real.exp (-wH') - eH' ^ 2 / (2 * 2 ^ 2)) +
        (1 - 1 / 2) * (-Real.exp (-wL') - eL' ^ 2 / (2 * 1 ^ 2))) =>
    exercise_14_C_3a_suff (v := fun w => -Real.exp (-w)) (dv := fun w => Real.exp (-w))
      (prof := id) (dprof := fun _ => 1) (g := fun e θ => e ^ 2 / (2 * θ ^ 2))
      (ge := fun e θ => e / θ ^ 2) (θL := 1) (θH := 2) (lam := 1 / 2) (ubar := -9 / 4)
      (wbar := 0) (eH := 4) (eL := 1) (by norm_num) (by norm_num)
      exA_strictConcave.concaveOn exA_hasDeriv (fun _ => Real.exp_pos _)
      (concaveOn_id (convex_Ici 0)) (fun e _ => (hasDerivAt_id e).hasDerivWithinAt) hconv
      (fun θ e _ => (hdg θ e).hasDerivWithinAt) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
  exact exercise_14_C_3a_necessary (v := fun w => -Real.exp (-w)) (dv := fun w => Real.exp (-w))
    (prof := id) (g := fun e θ => e ^ 2 / (2 * θ ^ 2)) (θL := 1) (θH := 2) (lam := 1 / 2)
    (ubar := -9 / 4) (wbar := 0) (by norm_num) (by norm_num) exA_hasDeriv
    (fun _ => Real.exp_pos _) (by norm_num) (by norm_num) (hasDerivAt_id 4) (hasDerivAt_id 1)
    (hdg 2 4) (hdg 1 1) (by norm_num) hopt

end MWG.PrincipalAgent
