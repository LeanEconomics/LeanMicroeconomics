/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.HardHalkin
import MWGClassicalDemand.AppendixML

/-!
# Theorem M.L.1 when only the value function is known to be differentiable

MWG, Section M.L, pp. 965-966. The book's Theorem M.L.1 assumes only that the value function
`v` is differentiable at `q̄` and that `λ` are Lagrange multipliers at the maximizer `x(q̄)`; its
proof differentiates along a maximizer path `x(·)`, which the first pass formalized
(`theorem_M_L_1`). Here the statement is proved without any maximizer path:

* `theorem_M_L_1_value`: let `f(x; q)` and `g_m(x; q)` be differentiable at `(x̄, q̄)`, the `g_m`
  continuous near it, `g(x̄; q̄) = b̄`, let the constraint qualification hold (the
  `∇_x g_m(x̄; q̄)` are linearly independent), let `λ` satisfy (M.K.2), and let `v` bound `f` on
  the constraint sets near `q̄` with `v(q̄) = f(x̄; q̄)` (e.g. the value function). If `v` is
  differentiable at `q̄`, then `∇v(q̄) = ∇_q f - ∑ λ_m ∇_q g_m` (M.L.4)-(M.L.5). The point
  `(x̄, q̄)` maximizes `f(x; q) - v(q)` on the joint constraint set `{(x, q) : g(x; q) = b̄}`, so
  Halkin's cone lemma (`hardHalkin_cone`, Brouwer's theorem) makes the derivative
  `f' - v' ∘ snd` vanish on the tangent space; evaluating it at the tangent vector `(w, e)` with
  `∇_x g·w = -∇_q g·e` gives the formula.
* `theorem_M_L_1_needs_CQ`: the constraint qualification (implicit in the book through the
  multipliers of Theorem M.K.1) cannot be dropped: for `max x³` s.t. `x³ - q = 0`, `v(q) = q`, but
  at `q̄ = 0`, `x̄ = 0` every `λ` satisfies (M.K.2) and (M.L.4) holds only for `λ = 1`.
-/

namespace MWG.ClassicalDemand

open Filter Topology

/-- Linearly independent functionals on a normed space give a surjective joint map. -/
theorem hardEnv_range_pi_eq_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {M : ℕ}
    {φ : Fin M → F →L[ℝ] ℝ} (hφ : LinearIndependent ℝ φ) :
    (ContinuousLinearMap.pi φ).range = ⊤ := by
  by_contra hne
  obtain ⟨ψ, hψ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hdecomp : ∀ y : Fin M → ℝ, ψ y = ∑ i, y i * ψ (Pi.single i 1) := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hcomb : ∑ i, ψ (Pi.single i 1) • φ i = 0 := by
    ext v
    have := hle ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hdecomp] at this
    simpa [mul_comm] using this
  have hzero := (Fintype.linearIndependent_iff.mp hφ) _ hcomb
  apply hψ
  refine LinearMap.ext fun y => ?_
  rw [hdecomp]
  simp [hzero]

/-- **Theorem M.L.1 (envelope theorem)** (MWG, p. 965), (M.L.4)-(M.L.5), with only `v`
differentiable. Consider `max f(x; q)` s.t. `g_m(x; q) = b̄_m`. Let `f` and the `g_m` be
differentiable at `(x̄, q̄)`, the `g_m` continuous near it, `g(x̄; q̄) = b̄`, the `∇_x g_m(x̄; q̄)`
linearly independent, and `λ` multipliers: `∇_x f = ∑ λ_m ∇_x g_m` (M.K.2). Let `v(q)` bound
`f(·; q)` on the constraint set at `q` for `q` near `q̄`, with `v(q̄) = f(x̄; q̄)`. If `v` is
differentiable at `q̄` with derivative `v'`, then `v' = ∇_q f - ∑ λ_m ∇_q g_m`. -/
theorem theorem_M_L_1_value {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M : ℕ} {f : F × E → ℝ}
    {g : Fin M → F × E → ℝ} {b : Fin M → ℝ} {v : E → ℝ} {x : F} {q : E}
    {f' : F × E →L[ℝ] ℝ} {g' : Fin M → F × E →L[ℝ] ℝ} {v' : E →L[ℝ] ℝ} {lam : Fin M → ℝ}
    (hf : HasFDerivAt f f' (x, q)) (hg : ∀ m, HasFDerivAt (g m) (g' m) (x, q))
    (hgc : ∀ m, ∀ᶠ z in 𝓝 (x, q), ContinuousAt (g m) z) (hx : ∀ m, g m (x, q) = b m)
    (hCQ : LinearIndependent ℝ fun m => (g' m).comp (ContinuousLinearMap.inl ℝ F E))
    (hvge : ∀ᶠ q' in 𝓝 q, ∀ y, (∀ m, g m (y, q') = b m) → f (y, q') ≤ v q')
    (hvq : v q = f (x, q)) (hv : HasFDerivAt v v' q)
    (hfoc : f'.comp (ContinuousLinearMap.inl ℝ F E) =
      ∑ m, lam m • (g' m).comp (ContinuousLinearMap.inl ℝ F E)) :
    v' = f'.comp (ContinuousLinearMap.inr ℝ F E) -
      ∑ m, lam m • (g' m).comp (ContinuousLinearMap.inr ℝ F E) := by
  set S : Set (F × E) := {z | ∀ m, g m z = b m} with hS
  set φ : F × E → ℝ := fun z => f z - v z.2 with hφdef
  set φ' : F × E →L[ℝ] ℝ := f' - v'.comp (ContinuousLinearMap.snd ℝ F E) with hφ'def
  have hφ : HasFDerivAt φ φ' (x, q) := hf.sub (hv.comp (x, q) hasFDerivAt_snd)
  -- `(x̄, q̄)` maximizes `f(x; q) - v(q)` on the joint constraint set
  have hmax : IsLocalMaxOn φ S (x, q) := by
    have hq' : ∀ᶠ z : F × E in 𝓝 (x, q),
        ∀ y, (∀ m, g m (y, z.2) = b m) → f (y, z.2) ≤ v z.2 :=
      (continuous_snd.tendsto (x, q)).eventually hvge
    refine eventually_nhdsWithin_iff.mpr (hq'.mono fun z hz hzS => ?_)
    have := hz z.1 hzS
    simp only [hφdef, hvq, sub_self]
    linarith
  set G : F × E → Fin M → ℝ := fun z m => g m z with hGdef
  have hG : HasFDerivAt G (ContinuousLinearMap.pi g') (x, q) := hasFDerivAt_pi.mpr hg
  have hGc : ∀ᶠ z in 𝓝 (x, q), ContinuousAt G z :=
    (eventually_all.mpr hgc).mono fun z hz => continuousAt_pi.mpr hz
  obtain ⟨A, hA⟩ := (ContinuousLinearMap.pi fun m => (g' m).comp
    (ContinuousLinearMap.inl ℝ F E)).exists_rightInverse_of_surjective
    (hardEnv_range_pi_eq_top hCQ)
  have hA' : ∀ u m, g' m (A u, 0) = u m := fun u m => by
    have := congrFun (congrArg (fun T : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) => T u) hA) m
    simpa using this
  have hsurj : (ContinuousLinearMap.pi g').range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro u
    exact ⟨(A u, 0), funext fun m => hA' u m⟩
  have hcone : ∀ ζ, (∀ m, g' m ζ = 0) → φ' ζ ≤ 0 := fun ζ hζ =>
    hardHalkin_cone hmax hφ hG hGc hsurj (Eventually.of_forall fun y t _ hy => by
      intro m
      have := congrFun hy m
      simp only [hGdef, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.pi_apply, hζ,
        smul_zero, add_zero] at this
      rw [this]
      exact hx m)
  ext e
  set w : F := -A (fun m => g' m (0, e)) with hw
  have hw0 : ∀ m, g' m (w, 0) = -g' m (0, e) := fun m => by
    have : ((w, 0) : F × E) = -((A fun m => g' m (0, e)), 0) := by simp [hw]
    rw [this, map_neg, hA']
  have hsplit : ∀ T : F × E →L[ℝ] ℝ, T (w, e) = T (w, 0) + T (0, e) := fun T => by
    rw [← map_add]
    simp
  have hζ : ∀ m, g' m (w, e) = 0 := fun m => by
    rw [hsplit, hw0]
    ring
  have h1 := hcone (w, e) hζ
  have h2 := hcone (-(w, e)) fun m => by rw [map_neg, hζ m, neg_zero]
  rw [map_neg] at h2
  have h0 : φ' (w, e) = 0 := by linarith
  have hf1 := congrArg (fun T : F →L[ℝ] ℝ => T w) hfoc
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul] at hf1
  simp only [hφ'def, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd'] at h0
  rw [hsplit, hf1] at h0
  simp only [hw0, mul_neg, Finset.sum_neg_distrib] at h0
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  linarith

/-- **Theorem M.L.1** (MWG, p. 965): the constraint qualification cannot be dropped. For
`max x³` s.t. `g(x; q) = x³ - q = 0` (`x, q ∈ ℝ`), the value function is `v(q) = q`, so
`v'(0) = 1`. At `q̄ = 0`, `x̄ = 0` we have `∂f/∂x = 0` and `∂g/∂x = 0`, so every `λ` satisfies
(M.K.2), while `∂f/∂q = 0` and `∂g/∂q = -1`: (M.L.4) reads `1 = λ`, which fails for `λ = 0`. -/
theorem theorem_M_L_1_needs_CQ :
    (∀ q : ℝ, sSup ((fun y : ℝ => y ^ 3) '' {y : ℝ | y ^ 3 - q = 0}) = q) ∧
    HasDerivAt (fun y : ℝ => y ^ 3) 0 0 ∧ HasDerivAt (fun y : ℝ => y ^ 3 - (0 : ℝ)) 0 0 ∧
    (∀ lam : ℝ, (0 : ℝ) = lam * 0) ∧ HasDerivAt (fun _ : ℝ => (0 : ℝ) ^ 3) 0 0 ∧
    HasDerivAt (fun q : ℝ => (0 : ℝ) ^ 3 - q) (-1) 0 ∧ (1 : ℝ) ≠ 0 - 0 * (-1) := by
  refine ⟨fun q => ?_, ?_, ?_, fun lam => by ring, hasDerivAt_const _ _, ?_, by norm_num⟩
  · -- a real cube root exists
    obtain ⟨y, -, hy⟩ : ∃ y ∈ Set.Icc (-(|q| + 1)) (|q| + 1), y ^ 3 = q := by
      have hab : -(|q| + 1) ≤ |q| + 1 := by linarith [abs_nonneg q]
      have hc : ContinuousOn (fun y : ℝ => y ^ 3) (Set.Icc (-(|q| + 1)) (|q| + 1)) :=
        (continuous_pow 3).continuousOn
      have hmem : q ∈ Set.Icc ((-(|q| + 1)) ^ 3) ((|q| + 1) ^ 3) := by
        have h1 : |q| + 1 ≤ (|q| + 1) ^ 3 :=
          le_self_pow₀ (by linarith [abs_nonneg q]) (by norm_num)
        constructor <;> nlinarith [abs_nonneg q, neg_abs_le q, le_abs_self q]
      exact intermediate_value_Icc hab hc hmem
    have hset : (fun y : ℝ => y ^ 3) '' {y : ℝ | y ^ 3 - q = 0} = {q} := by
      ext a
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y', hy', rfl⟩
        linarith
      · rintro rfl
        exact ⟨y, by rw [hy]; ring, hy⟩
    rw [hset, csSup_singleton]
  · simpa using hasDerivAt_pow 3 (0 : ℝ)
  · simpa using hasDerivAt_pow 3 (0 : ℝ)
  · exact (hasDerivAt_id (0 : ℝ)).const_sub ((0 : ℝ) ^ 3)

end MWG.ClassicalDemand
