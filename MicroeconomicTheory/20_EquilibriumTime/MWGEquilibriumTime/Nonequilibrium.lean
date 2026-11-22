/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Matrix.Mul

/-!
# Remarks on nonequilibrium dynamics (MWG Section 20.I, pp. 778-781)

MWG, Chapter 20, Section 20.I and Exercise 20.I.1 (p. 786).

* **Short-run equilibrium and permanent income**: with the marginal utilities of wealth `λ_i`
  fixed, (20.I.1) `δ^t ∇u_i(c_{it}) = λ_i p_t` defines short-run demands whose price derivative is
  `λ_i [D²u_i]⁻¹` (`shortRun_demand_derivative`), negative definite (`shortRun_negDef`), and so is
  the aggregate (`shortRun_aggregate_negDef`); an excess demand with negative definite derivative
  has at most one zero, so the short-run equilibrium is unique (`unique_zero_of_negDef`).
* **Exercise 20.I.1** (`exercise_20_I_1`): the identity relating the single-market law of demand
  in the overlapping generations model to the determinacy condition (20.H.3).
* **Learning**: by Walras' law (20.I.2) is (20.I.3) (`learning_walras`), and the adaptive dynamics
  reverse the equilibrium dynamics (`learning_reverses`, footnote 44).

OPEN: global tâtonnement stability of the short-run equilibrium, the effect of patience on `λ_i`
(heuristic), and the stability-determinacy correspondences (stated with "we neglect borderline
cases").
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- **The short-run price effects** (MWG, p. 778): if `C` is the derivative of the short-run
demand `c₀(p₀, λ)` defined by `∇u(c₀) = λ p₀` and `H = D²u(c₀)` is invertible, differentiating
gives `H C = λ I`, hence `C = λ H⁻¹`. -/
theorem shortRun_demand_derivative {H C : Matrix (Fin L) (Fin L) ℝ} {lam : ℝ}
    (hH : IsUnit H.det) (hdiff : H * C = lam • (1 : Matrix (Fin L) (Fin L) ℝ)) :
    C = lam • H⁻¹ := by
  have := congrArg (fun M => H⁻¹ * M) hdiff
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hH, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

/-- **The short-run price effects are negative definite** (MWG, p. 778): if `D²u` is negative
definite and `λ > 0`, then `λ (D²u)⁻¹` is negative definite. -/
theorem shortRun_negDef {H : Matrix (Fin L) (Fin L) ℝ} (hH : (-H).PosDef) {lam : ℝ}
    (hlam : 0 < lam) : (-(lam • H⁻¹)).PosDef := by
  have hu : IsUnit H.det := by
    have := hH.isUnit
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_neg] at this
    exact (IsUnit.mul_iff.1 this).2
  have hinv : (-H)⁻¹ = -H⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hu]
  have := hH.inv.smul hlam
  rw [hinv] at this
  rwa [smul_neg] at this

/-- **The aggregate short-run price effects are negative definite** (MWG, p. 778). -/
theorem shortRun_aggregate_negDef {ι : Type*} [Fintype ι] [Nonempty ι]
    {H : ι → Matrix (Fin L) (Fin L) ℝ} (hH : ∀ i, (-H i).PosDef) {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) : (-(∑ i, lam i • (H i)⁻¹)).PosDef := by
  classical
  rw [← Finset.sum_neg_distrib]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have h0 := shortRun_negDef (hH i₀) (hlam i₀)
  refine Finset.induction_on (Finset.univ.erase i₀) (by simpa using h0) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, ← add_assoc, add_comm (-(lam i₀ • (H i₀)⁻¹)), add_assoc]
  exact (shortRun_negDef (hH j) (hlam j)).add ih

/-- **Uniqueness of the short-run equilibrium** (MWG, p. 778): an excess demand function whose
derivative is negative definite on a convex set (`v · Dz(p) v < 0` for `v ≠ 0`) has at most one
zero there; indeed `(p - p') · (z(p) - z(p')) < 0` for `p ≠ p'`. -/
theorem unique_zero_of_negDef {S : Set (Fin L → ℝ)} (hS : Convex ℝ S)
    {z : (Fin L → ℝ) → Fin L → ℝ} {Dz : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hDz : ∀ x ∈ S, HasFDerivAt z (Dz x) x) (hneg : ∀ x ∈ S, ∀ v, v ≠ 0 → v ⬝ᵥ Dz x v < 0)
    {p p' : Fin L → ℝ} (hp : p ∈ S) (hp' : p' ∈ S) (hne : p ≠ p') :
    (p - p') ⬝ᵥ (z p - z p') < 0 := by
  set v := p - p' with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 hne
  set g : ℝ → ℝ := fun s => v ⬝ᵥ z (p' + s • v) with hg
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, p' + s • v ∈ S := by
    intro s hs
    have := hS hp' hp (by linarith [hs.2] : 0 ≤ 1 - s) hs.1 (by ring)
    convert this using 1
    simp only [hv]
    module
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (v ⬝ᵥ Dz (p' + s • v) v) s := by
    intro s hs
    have hl : HasDerivAt (fun s : ℝ => p' + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p'
    have h1 := (hDz _ (hseg s hs)).comp_hasDerivAt s hl
    have hcomp : ∀ i, HasDerivAt (fun s : ℝ => z (p' + s • v) i) ((Dz (p' + s • v) v) i) s :=
      fun i => hasDerivAt_pi.1 h1 i
    have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hcomp i).const_mul (v i))
    simp only [hg, dotProduct]
    convert this using 1
    funext s; simp
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g (fun s => v ⬝ᵥ Dz (p' + s • v) v)
    (zero_lt_one) (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hgd s (Set.Ioo_subset_Icc_self hs))
  have hlt := hneg _ (hseg c (Set.Ioo_subset_Icc_self hc)) v hv0
  rw [hceq] at hlt
  simp only [hg, zero_smul, add_zero, one_smul, hv, add_sub_cancel] at hlt
  rw [dotProduct_sub]
  linarith

/-- **Exercise 20.I.1** (MWG, p. 786): if the excess demands `z_b`, `z_a` of a generation are
homogeneous of degree zero in `(p_b, p_a)` and differentiable, then (with `∇₁`, `∇₂` the partial
derivatives)
`∇₂z_a(1/p, 1) + ∇₁z_b(1, p) = p ∇₂z_a(1, p) + ∇₁z_b(1, p) = -∇₁z_a(1, p) + ∇₁z_b(1, p)`. -/
theorem exercise_20_I_1 {za : ℝ × ℝ → ℝ} (hhom : ∀ c : ℝ, 0 < c → ∀ x, za (c • x) = za x)
    {p : ℝ} (hp : 0 < p) {D D' : ℝ × ℝ →L[ℝ] ℝ} (hD : HasFDerivAt za D (1, p))
    (hD' : HasFDerivAt za D' (1 / p, 1)) (zb1 : ℝ) :
    D' (0, 1) + zb1 = p * D (0, 1) + zb1 ∧ p * D (0, 1) + zb1 = -D (1, 0) + zb1 := by
  -- degree `-1` homogeneity of the derivative: `za(x) = za((1/p) • x)` near `(1, p)`
  have hscale : (1 / p) • ((1 : ℝ), p) = (1 / p, 1) := by
    ext <;> simp [hp.ne']
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => za ((1 / p) • x))
      (D'.comp ((1 / p) • ContinuousLinearMap.id ℝ (ℝ × ℝ))) (1, p) := by
    have hl : HasFDerivAt (fun x : ℝ × ℝ => (1 / p) • x)
        ((1 / p) • ContinuousLinearMap.id ℝ (ℝ × ℝ)) (1, p) :=
      (hasFDerivAt_id _).const_smul (1 / p)
    rw [← hscale] at hD'
    exact hD'.comp _ hl
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => za ((1 / p) • x)) D (1, p) := by
    refine hD.congr_of_eventuallyEq (Eventually.of_forall fun x => hhom (1 / p) (by positivity) x)
  have hEq := h2.unique h1
  have e1 : D (0, 1) = (1 / p) * D' (0, 1) := by
    rw [hEq]; simp
  -- Euler's theorem for degree zero: `D(1, p) = 0`
  have h3 : HasDerivAt (fun c : ℝ => za (c • ((1 : ℝ), p))) (D (1, p)) 1 := by
    have hl : HasDerivAt (fun c : ℝ => c • ((1 : ℝ), p)) ((1 : ℝ), p) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const ((1 : ℝ), p)
    exact hD.comp_hasDerivAt_of_eq (1 : ℝ) hl (by simp)
  have h4 : HasDerivAt (fun c : ℝ => za (c • ((1 : ℝ), p))) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (za ((1 : ℝ), p))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with c hc
    exact hhom c hc _
  have hEuler := h3.unique h4
  have hsplit : D (1, p) = D (1, 0) + p * D (0, 1) := by
    rw [show ((1 : ℝ), p) = (1, 0) + p • ((0 : ℝ), (1 : ℝ)) by ext <;> simp, map_add, map_smul,
      smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e1]; field_simp
  · linarith

/-- **(20.I.2) is (20.I.3)** (MWG, p. 780): by Walras' law for the young,
`p_t z_b + p^e z_a = 0` with expected price `p^e = p_{t-1}`, the condition `z_b = -M/p_t` is
equivalent to `z_a = M/p_{t-1}`. -/
theorem learning_walras {pt pe zb za M : ℝ} (hpt : 0 < pt) (hpe : 0 < pe)
    (hW : pt * zb + pe * za = 0) : zb = -(M / pt) ↔ za = M / pe := by
  constructor
  · intro h
    rw [h] at hW
    field_simp at hW ⊢
    linarith
  · intro h
    rw [h] at hW
    field_simp at hW ⊢
    linarith

/-- **Footnote 44** (MWG, p. 781): the learning dynamics exactly reverse the equilibrium
dynamics. If the realizations `p_t` satisfy the adaptive rule `z_b(p_t, p_{t-1}) = -M/p_t`
(20.I.2) for `1 ≤ t ≤ T`, then `p'_s = p_{T-s}` satisfies the perfect-foresight equilibrium
condition `z_b(p'_s, p'_{s+1}) = -M/p'_s` for `s < T`. -/
theorem learning_reverses {zb : ℝ → ℝ → ℝ} {M : ℝ} {p : ℕ → ℝ} {T : ℕ}
    (hlearn : ∀ t, 1 ≤ t → t ≤ T → zb (p t) (p (t - 1)) = -(M / p t)) :
    ∀ s, s < T → zb (p (T - s)) (p (T - (s + 1))) = -(M / p (T - s)) := by
  intro s hs
  have := hlearn (T - s) (by omega) (by omega)
  rwa [show T - s - 1 = T - (s + 1) by omega] at this

end MWG.EquilibriumTime
