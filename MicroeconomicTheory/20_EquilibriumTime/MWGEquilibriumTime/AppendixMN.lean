/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Euler
import MWGEquilibriumTime.Utility
import LeanEconomics.DynamicProgramming.Optimality

/-!
# Dynamic programming (MWG Mathematical Appendix, Section M.N, pp. 968-970)

The problem (M.N.1): `max ∑_t δ^t u(x_t, x_{t+1})` over sequences in a nonempty compact
`A ⊆ ℝ^N` with `x₀ = z`, for `u` continuous on `A × A` and `0 < δ < 1`. Here `A` is a set
`K ⊆ Fin N → ℝ` with `CompactSpace K` and `Nonempty K`.

The problem is LeanEconomics' `DynamicProgram` with states and actions in `K`, the constant
feasible set `K` and the law of motion `(z, z') ↦ z'` (`mnProgram`); its value function is
`LeanEconomics.DynamicProgram.valueFunction`.

* The value function is attained by a maximizing sequence and is the value of (M.N.1)
  (`value_attained_M_N`); it is continuous (`value_continuous_M_N`) and concave when `A` is convex
  and `u` concave (`value_concave_M_N`).
* The Bellman equation (`bellman_M_N`).
* **Theorem M.N.1** (`theorem_M_N_1`): a continuous solution of the Bellman equation (M.N.2) is the
  value function.
* Value function iteration converges (`value_iteration_M_N`, pointwise
  `value_iteration_pointwise_M_N`).
* The Euler equations (M.N.4) at an interior optimum (`euler_M_N_4`).
-/

open Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace MWG.EquilibriumTime

variable {N : ℕ} {K : Set (Fin N → ℝ)} [CompactSpace K] [Nonempty K]

/-- The reward `u` restricted to `K × K` as a bounded continuous function. -/
noncomputable def mnReward (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hu : ContinuousOn u (K ×ˢ K)) :
    (K × K) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => u (x.1.1, x.2.1), hu.comp_continuous (by fun_prop) fun x => ⟨x.1.2, x.2.2⟩⟩

/-- **The dynamic program of (M.N.1)** (MWG, p. 968), as a LeanEconomics `DynamicProgram`: state
`z ∈ K`, action `z' ∈ K` (the whole of `K` is feasible), reward `u(z, z')`, next state `z'`. -/
noncomputable def mnProgram (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hu : ContinuousOn u (K ×ˢ K))
    (δ : ℝ≥0) (hδ : δ < 1) : LeanEconomics.DynamicProgram K K where
  feasible _ := Set.univ
  isCompact_feasible _ := isCompact_univ
  feasible_nonempty _ := Set.univ_nonempty
  upperHemicontinuous_feasible := LeanEconomics.upperHemicontinuous_const Set.univ
  lowerHemicontinuous_feasible := LeanEconomics.lowerHemicontinuous_const Set.univ
  reward := mnReward u hu
  transition := ⟨Prod.snd, continuous_snd⟩
  discount := δ
  discount_lt_one := hδ

/-- The objective of (M.N.1) along a sequence in `K`. -/
noncomputable def mnObjective (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (δ : ℝ) (x : ℕ → K) : ℝ :=
  ∑' t, δ ^ t * u ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ))

variable {u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {hu : ContinuousOn u (K ×ˢ K)} {δ : ℝ≥0}
  {hδ : δ < 1}

/-- A sequence of `K` as a plan of the dynamic program. -/
def mnPlan (x : ℕ → K) : (mnProgram u hu δ hδ).Plan (x 0) where
  state := x
  action := fun t => x (t + 1)
  state_zero := rfl
  action_mem := fun _ => Set.mem_univ _
  state_succ := fun _ => rfl

theorem mnPlan_value (x : ℕ → K) :
    (mnPlan (u := u) (hu := hu) (δ := δ) (hδ := hδ) x).value = mnObjective u δ x := rfl

/-- Every plan is the plan of its state sequence. -/
theorem plan_value_eq {z : K} (p : (mnProgram u hu δ hδ).Plan z) :
    p.value = mnObjective u δ p.state := by
  unfold LeanEconomics.DynamicProgram.Plan.value LeanEconomics.DynamicProgram.Plan.payoff
    mnObjective
  refine tsum_congr fun t => ?_
  have h := p.state_succ t
  simp only [mnProgram] at h
  rw [h]
  rfl

/-- **The value of (M.N.1) is attained** (MWG, p. 968): there is a maximizing sequence from `z`,
and the value function of the dynamic program is the maximum value `v(z)`. -/
theorem value_attained_M_N (z : K) :
    ∃ x : ℕ → K, x 0 = z ∧ mnObjective u δ x = (mnProgram u hu δ hδ).valueFunction z ∧
      ∀ x' : ℕ → K, x' 0 = z → mnObjective u δ x' ≤ (mnProgram u hu δ hδ).valueFunction z := by
  obtain ⟨⟨p, hp⟩, hmax⟩ := (mnProgram u hu δ hδ).isGreatest_planValue z
  refine ⟨p.state, p.state_zero, by rw [← plan_value_eq, hp], fun x' hx' => ?_⟩
  subst hx'
  exact hmax ⟨mnPlan x', rfl⟩

/-- **The value function is continuous** (MWG, p. 968). -/
theorem value_continuous_M_N : Continuous ((mnProgram u hu δ hδ).valueFunction) :=
  (mnProgram u hu δ hδ).valueFunction.continuous

/-- **The Bellman equation** (MWG, p. 969): `v(z) = max_{z' ∈ A} u(z, z') + δ v(z')`. -/
theorem bellman_M_N (z : K) :
    IsGreatest {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ))
      + δ * (mnProgram u hu δ hδ).valueFunction z'}
      ((mnProgram u hu δ hδ).valueFunction z) := by
  set D := mnProgram u hu δ hδ
  obtain ⟨a, -, ha⟩ := D.exists_optimal_policy z
  refine ⟨⟨a, by rw [ha]; rfl⟩, ?_⟩
  rintro r ⟨z', rfl⟩
  have h := D.le_bellmanFn (s := z) (a := z') D.valueFunction (Set.mem_univ _)
  have hfix : D.bellmanFn D.valueFunction z = D.valueFunction z := by
    conv_rhs => rw [← D.bellman_valueFunction]
    rfl
  rw [hfix] at h
  exact h

/-- **Theorem M.N.1** (MWG, p. 969): if `f : A → ℝ` is continuous and satisfies the Bellman
equation (M.N.2), `f(z) = max_{z' ∈ A} u(z, z') + δ f(z')` for every `z ∈ A`, then `f` is the value
function of (M.N.1). -/
theorem theorem_M_N_1 {f : K → ℝ} (hf : Continuous f)
    (hbell : ∀ z : K, IsGreatest {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ))
      + δ * f z'} (f z)) :
    ∀ z, f z = (mnProgram u hu δ hδ).valueFunction z := by
  set D := mnProgram u hu δ hδ
  set g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  have hfix : D.bellman g = g := by
    ext z
    rw [D.bellman_apply, LeanEconomics.maxValue]
    have : D.objective g z '' D.feasible z
        = {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ)) + δ * f z'} := by
      ext r
      constructor
      · rintro ⟨z', -, rfl⟩; exact ⟨z', rfl⟩
      · rintro ⟨z', rfl⟩; exact ⟨z', Set.mem_univ _, rfl⟩
    rw [this, (hbell z).csSup_eq]
    rfl
  intro z
  have := D.eq_valueFunction hfix
  exact congrFun (congrArg DFunLike.coe this) z

/-- **Value function iteration** (MWG, p. 969): from any continuous `f₀`, the iterates
`f_{r+1}(z) = max_{z'} u(z, z') + δ f_r(z')` converge (uniformly) to the value function. -/
theorem value_iteration_M_N (f₀ : K →ᵇ ℝ) :
    Tendsto (fun r => (mnProgram u hu δ hδ).bellman^[r] f₀) atTop
      (𝓝 (mnProgram u hu δ hδ).valueFunction) :=
  (mnProgram u hu δ hδ).tendsto_iterate_valueFunction f₀

/-- **Value function iteration**, pointwise form (MWG, p. 969): `f_r(z) → v(z)` for every `z`. -/
theorem value_iteration_pointwise_M_N (f₀ : K →ᵇ ℝ) (z : K) :
    Tendsto (fun r => ((mnProgram u hu δ hδ).bellman^[r] f₀) z) atTop
      (𝓝 ((mnProgram u hu δ hδ).valueFunction z)) := by
  have h := value_iteration_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) f₀
  rw [tendsto_iff_dist_tendsto_zero] at h ⊢
  exact squeeze_zero (fun r => dist_nonneg)
    (fun r => BoundedContinuousFunction.dist_coe_le_dist z) h

omit [Nonempty K] in
include hu in
/-- A bounded reward makes the objective summable. -/
theorem summable_mnObjective (x : ℕ → K) (hδ0 : (δ : ℝ) < 1) :
    Summable fun t => (δ : ℝ) ^ t * u ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ)) := by
  refine summable_discounted δ.coe_nonneg hδ0 (M := ‖mnReward u hu‖) fun t => ?_
  have := (mnReward u hu).norm_coe_le_norm (x t, x (t + 1))
  simpa [mnReward, Real.norm_eq_abs] using this

/-- **The value function is concave** (MWG, p. 968) when `A` is convex and `u` is concave on
`A × A`. -/
theorem value_concave_M_N (hKc : Convex ℝ K) (hconc : ConcaveOn ℝ (K ×ˢ K) u) {z₁ z₂ : K}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * (mnProgram u hu δ hδ).valueFunction z₁ + (1 - θ) * (mnProgram u hu δ hδ).valueFunction z₂
      ≤ (mnProgram u hu δ hδ).valueFunction
        ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
          hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩ := by
  obtain ⟨x₁, hx₁, hv₁, -⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z₁
  obtain ⟨x₂, hx₂, hv₂, -⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z₂
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  set m : ℕ → K := fun t => ⟨θ • (x₁ t : Fin N → ℝ) + (1 - θ) • (x₂ t : Fin N → ℝ),
    hKc (x₁ t).2 (x₂ t).2 hθ0 (by linarith) (by ring)⟩ with hm
  obtain ⟨_, _, _, hmax⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ)
    ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
      hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩
  have hm0 : m 0 = ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
      hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩ := by
    simp [hm, hx₁, hx₂]
  have hle := hmax m hm0
  have hs₁ := summable_mnObjective (u := u) (hu := hu) x₁ hδ1
  have hs₂ := summable_mnObjective (u := u) (hu := hu) x₂ hδ1
  have hsm := summable_mnObjective (u := u) (hu := hu) m hδ1
  have hterm : ∀ t, θ * ((δ : ℝ) ^ t * u ((x₁ t : Fin N → ℝ), (x₁ (t + 1) : Fin N → ℝ)))
      + (1 - θ) * ((δ : ℝ) ^ t * u ((x₂ t : Fin N → ℝ), (x₂ (t + 1) : Fin N → ℝ)))
      ≤ (δ : ℝ) ^ t * u ((m t : Fin N → ℝ), (m (t + 1) : Fin N → ℝ)) := by
    intro t
    have hc := hconc.2 (⟨(x₁ t).2, (x₁ (t + 1)).2⟩ : ((x₁ t : Fin N → ℝ),
      (x₁ (t + 1) : Fin N → ℝ)) ∈ K ×ˢ K) (⟨(x₂ t).2, (x₂ (t + 1)).2⟩ :
      ((x₂ t : Fin N → ℝ), (x₂ (t + 1) : Fin N → ℝ)) ∈ K ×ˢ K) hθ0 (by linarith : 0 ≤ 1 - θ)
      (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hc
    have hp := pow_nonneg δ.coe_nonneg t
    simp only [hm]
    nlinarith [mul_le_mul_of_nonneg_left hc hp]
  have hsum := Summable.tsum_le_tsum hterm ((hs₁.mul_left θ).add (hs₂.mul_left (1 - θ))) hsm
  rw [(hs₁.mul_left θ).tsum_add (hs₂.mul_left (1 - θ)), hs₁.tsum_mul_left,
    hs₂.tsum_mul_left] at hsum
  unfold mnObjective at hv₁ hv₂ hle
  rw [← hv₁, ← hv₂]
  exact hsum.trans hle

/-- **The Euler equations (M.N.4)** (MWG, p. 969): along a maximizing sequence of (M.N.1) whose
pairs `(x_t, x_{t+1})` are interior to `A × A`, with `u` differentiable there (derivative `Du t`),
`∇₂u(x_t, x_{t+1}) + δ ∇₁u(x_{t+1}, x_{t+2}) = 0` for all `t` (MWG's `t ≥ 1` with
`x_{t-1}, x_t`). -/
theorem euler_M_N_4 (hδ0 : 0 < (δ : ℝ)) {z : K} {x : ℕ → K} (hx0 : x 0 = z)
    (hopt : mnObjective u δ x = (mnProgram u hu δ hδ).valueFunction z)
    (hint : ∀ t, ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ)) ∈ interior (K ×ˢ K))
    {Du : ℕ → (Fin N → ℝ) × (Fin N → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ))) :
    EulerEq (δ : ℝ) Du := by
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  -- the sequence is optimal among admissible ambient paths
  have hopt' : OptimalFrom (K ×ˢ K) (δ : ℝ) u (z : Fin N → ℝ) (fun t => (x t : Fin N → ℝ)) := by
    refine ⟨⟨congrArg Subtype.val hx0, fun t => ⟨(x t).2, (x (t + 1)).2⟩⟩,
      summable_mnObjective (u := u) (hu := hu) x hδ1, fun k' hk' _ => ?_⟩
    -- a competitor stays in `K`
    have hkK : ∀ t, k' t ∈ K := fun t => (hk'.2 t).1
    set x' : ℕ → K := fun t => ⟨k' t, hkK t⟩
    have hx'0 : x' 0 = z := Subtype.ext hk'.1
    obtain ⟨_, _, _, hmax⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z
    have := hmax x' hx'0
    rw [← hopt] at this
    exact this
  exact euler_of_optimal hδ0 hopt' hint hDu

end MWG.EquilibriumTime
