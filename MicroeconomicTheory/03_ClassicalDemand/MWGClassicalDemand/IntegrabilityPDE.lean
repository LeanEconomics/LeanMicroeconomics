/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityUtility

/-!
# Integrability: the system of partial differential equations (3.H.2)

MWG, Section 3.H, pp. 79-80 ("Recovering the Expenditure Function from Demand").

`SolvesPDE x E` says that `E` solves (3.H.2), `∇E(p) = x(p, E(p))` for all `p ≫ 0`. For a
demand function `x(p, w)` differentiable at `(p, E(p))`:

* the Hessian of a solution is the Slutsky matrix, `D²E(p) = S(p, E(p))`
  (`pde_hessian_eq_slutsky`), so a solution can exist only if `S(p, E(p))` is symmetric
  (`pde_slutsky_symmetric`; the necessity half of Frobenius' theorem, p. 80);
* if `S` is negative semidefinite, a solution is concave (`pde_concave`); Walras' law makes it
  homogeneous of degree one (`pde_hd1`); nonnegative demand makes it nondecreasing
  (`pde_monotone`). These are the properties of an expenditure function claimed on p. 80;
* combined with `integrability_theorem`, a family of solutions of (3.H.2) that is strictly
  increasing, continuous and onto in the utility index rationalizes `x(p, w)`
  (`integrability_of_pde`).

The existence of solutions of (3.H.2) under symmetry (the sufficiency half of Frobenius'
theorem) is not proved for general `L`; see `IntegrabilityTwoGoods` for `L = 2` and the source
map's OPEN table.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Equation (3.H.2)** (MWG, p. 79). `E` solves the system of partial differential equations
`∂E(p)/∂p_l = x_l(p, E(p))`, `l = 1, ..., L`, on `p ≫ 0`. -/
def SolvesPDE (x : DemandFunction L) (E : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ q, StrictlyPositive q → HasFDerivAt E (dualityDotCLM (x q (E q))) q

/-- The derivative of `p ↦ x(p, E(p))` along a solution of (3.H.2) (chain rule). -/
theorem pde_chain {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ} (hE : SolvesPDE x E)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, E p)) :
    HasFDerivAt (fun q => x q (E q))
      (D.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (x p (E p))))) p := by
  have h1 : HasFDerivAt (fun q => (q, E q))
      ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (x p (E p)))) p :=
    (hasFDerivAt_id p).prodMk (hE p hp)
  exact hD.comp p h1

/-- The derivative matrix of `p ↦ x(p, E(p))` along a solution is the Slutsky matrix
`D_p x + D_w x xᵀ` (MWG, p. 79). -/
theorem pde_jacobian_eq_slutsky (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin L → ℝ) :
    jacobian (D.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM xv))) =
      slutskyMatrix D xv := by
  ext l k
  simp only [jacobian, Matrix.of_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, dualityDotCLM_apply,
    slutskyMatrix]
  rw [deriv_apply_eq]
  simp [Pi.single_apply, priceEffect, dotProduct_single]

/-- **Section 3.H** (MWG, p. 79). If `E` solves (3.H.2) and `x` is differentiable at
`(p, E(p))` with derivative `D`, then the Hessian of `E` at `p` is the Slutsky matrix:
`D²E(p) = D_p x(p, E(p)) + D_w x(p, E(p)) x(p, E(p))ᵀ = S(p, E(p))`. -/
theorem pde_hessian_eq_slutsky {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ}
    (hE : SolvesPDE x E) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, E p)) :
    MWG.ConsumerChoice.hessianMatrix E p = slutskyMatrix D (x p (E p)) := by
  have hchain := pde_chain hE hp hD
  have heq : (fun y => gradientVec (fderiv ℝ E y)) =ᶠ[𝓝 p] fun q => x q (E q) := by
    filter_upwards [relations_eventually_strictlyPositive hp] with q hq
    rw [(hE q hq).fderiv, gradientVec_dualityDotCLM]
  have h2 := hchain.congr_of_eventuallyEq heq
  rw [MWG.ConsumerChoice.hessianMatrix, h2.fderiv, pde_jacobian_eq_slutsky]

/-- **Section 3.H** (MWG, pp. 79-80), the necessity half of Frobenius' theorem. If (3.H.2) has
a solution `E` and `x` is differentiable at `(p, E(p))`, then `S(p, E(p))` is symmetric (the
Hessian of a twice differentiable function is symmetric). -/
theorem pde_slutsky_symmetric {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ}
    (hE : SolvesPDE x E) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, E p)) :
    ∀ i j, slutskyMatrix D (x p (E p)) i j = slutskyMatrix D (x p (E p)) j i := by
  have hchain := pde_chain hE hp hD
  set G := D.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (x p (E p))))
  have h1 : ∀ᶠ q in 𝓝 p, HasFDerivAt E (dualityDotLin (x q (E q))) q := by
    filter_upwards [relations_eventually_strictlyPositive hp] with q hq
    rw [dualityDotLin_apply]
    exact hE q hq
  have h2 : HasFDerivAt (fun q => dualityDotLin (x q (E q))) (dualityDotLin.comp G) p :=
    dualityDotLin.hasFDerivAt.comp p hchain
  intro i j
  have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
  simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
    dotProduct_single, mul_one] at this
  have h3 : jacobian G i j = jacobian G j i := this
  rw [← pde_jacobian_eq_slutsky]
  exact h3

/-- The one-dimensional step: if `g' = k` and `k' ≤ 0` on `[0, 1]`, then `g(1) ≤ g(0) + k(0)`. -/
theorem pde_line_le {g k k' : ℝ → ℝ} (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (k t) t)
    (hk : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt k (k' t) t)
    (hk' : ∀ t ∈ Set.Icc (0 : ℝ) 1, k' t ≤ 0) : g 1 ≤ g 0 + k 0 := by
  obtain ⟨c, hc, hgc⟩ := exists_hasDerivAt_eq_slope g k (zero_lt_one' ℝ)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hg t (Set.Ioo_subset_Icc_self ht))
  have hcI : Set.Icc 0 c ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc le_rfl hc.2.le
  obtain ⟨d, hd, hkd⟩ := exists_hasDerivAt_eq_slope k k' hc.1
    (fun t ht => (hk t (hcI ht)).continuousAt.continuousWithinAt)
    (fun t ht => hk t (hcI (Set.Ioo_subset_Icc_self ht)))
  have h1 : k c ≤ k 0 := by
    have := hk' d (hcI (Set.Ioo_subset_Icc_self hd))
    rw [hkd, div_nonpos_iff] at this
    rcases this with h | h
    · linarith [h.2, hc.1]
    · linarith [h.1]
  rw [sub_zero, div_one] at hgc
  linarith

/-- **Section 3.H** (MWG, p. 80). If `E` solves (3.H.2), `x` is differentiable at every
`(q, E(q))`, `q ≫ 0`, and the Slutsky matrix `S(q, E(q))` is negative semidefinite there, then
`E` is concave on `p ≫ 0`. -/
theorem pde_concave {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ} (hE : SolvesPDE x E)
    {Dx : (Fin L → ℝ) → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ q, StrictlyPositive q → HasFDerivAt (Function.uncurry x) (Dx q) (q, E q))
    (hnsd : ∀ q, StrictlyPositive q → NegSemidef (slutskyMatrix (Dx q) (x q (E q)))) :
    ConcaveOn ℝ (posPrices L) E := by
  apply theorem_M_C_1_sufficiency (exp_convex_strictlyPositive L)
    (f' := fun q => dualityDotCLM (x q (E q)))
  intro p hp z hpz
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictlyPositive (p + t • z) := by
    intro t ht
    have : p + t • z = (1 - t) • p + t • (p + z) := by module
    rw [this]
    exact exp_convex_strictlyPositive L hp hpz (by linarith [ht.2]) ht.1 (by ring)
  set γ : ℝ → Fin L → ℝ := fun t => p + t • z
  have hγ : ∀ t, HasDerivAt γ z t := fun t => by
    change HasDerivAt (fun t : ℝ => p + t • z) z t
    simpa using ((hasDerivAt_id t).smul_const z).const_add p
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => E (γ t))
      (z ⬝ᵥ x (γ t) (E (γ t))) t := by
    intro t ht
    have := (hE (γ t) (hseg t ht)).comp_hasDerivAt t (hγ t)
    rwa [dualityDotCLM_apply, dotProduct_comm] at this
  have hk : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => z ⬝ᵥ x (γ t) (E (γ t)))
      (z ⬝ᵥ (slutskyMatrix (Dx (γ t)) (x (γ t) (E (γ t)))).mulVec z) t := by
    intro t ht
    have hc := pde_chain hE (hseg t ht) (hD (γ t) (hseg t ht))
    have h1 := (hc.comp_hasDerivAt t (hγ t))
    have h2 := (dualityDotCLM z).hasFDerivAt.comp_hasDerivAt t h1
    simp only [Function.comp_def, dualityDotCLM_apply] at h2
    rw [← pde_jacobian_eq_slutsky, jacobian_mulVec]
    exact h2
  have := pde_line_le hg hk fun t ht => hnsd (γ t) (hseg t ht) z
  simp only [γ, zero_smul, add_zero, one_smul] at this
  rw [dualityDotCLM_apply, dotProduct_comm]
  exact this

/-- **Section 3.H** (MWG, p. 80). If `E` solves (3.H.2) and `x` satisfies Walras' law along the
solution, `q·x(q, E(q)) = E(q)`, then `E` is homogeneous of degree one on `p ≫ 0`. -/
theorem pde_hd1 {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ} (hE : SolvesPDE x E)
    (hwal : ∀ q, StrictlyPositive q → q ⬝ᵥ x q (E q) = E q) : HD1OnPos E := by
  intro p hp α hα
  have hpos : ∀ t : ℝ, 0 < t → StrictlyPositive (t • p) := fun t ht l => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos ht (hp l)
  -- `φ(t) = E(tp)/t` has zero derivative on `(0, ∞)`
  have hφ : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => E (s • p) / s) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => E (s • p)) (p ⬝ᵥ x (t • p) (E (t • p))) t := by
      have hl : HasDerivAt (fun s : ℝ => s • p) p t := by
        simpa using (hasDerivAt_id t).smul_const p
      have := (hE (t • p) (hpos t ht)).comp_hasDerivAt t hl
      rwa [dualityDotCLM_apply, dotProduct_comm] at this
    have h2 := h1.div (hasDerivAt_id' t) ht.ne'
    have hw := hwal (t • p) (hpos t ht)
    rw [smul_dotProduct, smul_eq_mul] at hw
    convert h2 using 1
    rw [eq_comm, div_eq_zero_iff]
    left
    linarith
  have key : ∀ a b : ℝ, 0 < a → a < b → E (b • p) / b = E (a • p) / a := by
    intro a b ha hab
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => E (s • p) / s) (fun _ => 0) hab
      (fun t ht => (hφ t (ha.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => hφ t (ha.trans ht.1))
    have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    rw [eq_comm, div_eq_zero_iff] at hcd
    rcases hcd with h | h
    · linarith
    · exact absurd h hne
  have h1 : E (α • p) / α = E ((1 : ℝ) • p) / 1 := by
    rcases lt_trichotomy α 1 with h | h | h
    · exact (key α 1 hα h).symm
    · rw [h]
    · exact key 1 α one_pos h
  rw [one_smul, div_one] at h1
  field_simp at h1
  linarith

/-- **Section 3.H** (MWG, p. 79). If `E` solves (3.H.2) and `x(q, E(q)) ≥ 0`, then `E` is
nondecreasing on `p ≫ 0`. -/
theorem pde_monotone {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ} (hE : SolvesPDE x E)
    (hnn : ∀ q, StrictlyPositive q → x q (E q) ∈ nonnegOrthant L) : MonotoneOnPos E := by
  intro p q hp hpq
  have hq := integ_strictlyPositive_of_le hp hpq
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictlyPositive (p + t • (q - p)) := by
    intro t ht
    have : p + t • (q - p) = (1 - t) • p + t • q := by module
    rw [this]
    exact exp_convex_strictlyPositive L hp hq (by linarith [ht.2]) ht.1 (by ring)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => E (p + t • (q - p)))
      ((q - p) ⬝ᵥ x (p + t • (q - p)) (E (p + t • (q - p)))) t := by
    intro t ht
    have hl : HasDerivAt (fun s : ℝ => p + s • (q - p)) (q - p) t := by
      simpa using ((hasDerivAt_id t).smul_const (q - p)).const_add p
    have := (hE _ (hseg t ht)).comp_hasDerivAt t hl
    rwa [dualityDotCLM_apply, dotProduct_comm] at this
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hd t (interior_subset ht)).deriv]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (sub_nonneg.mpr (hpq l))
        (hnn _ (hseg t (interior_subset ht)) l))
  have := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simpa using this

/-- **Section 3.H** (MWG, pp. 79-80), the integrability theorem from a solution of (3.H.2). Let
`x(p, w)` be a demand function, nonnegative, satisfying Walras' law, differentiable on
`p ≫ 0, w > 0`, with a negative semidefinite Slutsky matrix there. If for every utility level `u`,
`E(·, u)` solves (3.H.2) with `E(p, u) > 0`, and `E(p, ·)` is strictly increasing, continuous and
onto `(0, ∞)`, then `x(p, w)` is the Walrasian demand of the recovered preference. (By
`pde_slutsky_symmetric`, such a family exists only if `S` is symmetric.) -/
theorem integrability_of_pde {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ → ℝ}
    {Dx : (Fin L → ℝ) → ℝ → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hwal : WalrasLaw x)
    (hD : ∀ q w, StrictlyPositive q → 0 < w → HasFDerivAt (Function.uncurry x) (Dx q w) (q, w))
    (hnsd : ∀ q w, StrictlyPositive q → 0 < w → NegSemidef (slutskyMatrix (Dx q w) (x q w)))
    (hE : ∀ u, SolvesPDE x fun q => E q u) (hEpos : ∀ q u, StrictlyPositive q → 0 < E q u)
    (hmono : ∀ p, StrictlyPositive p → StrictMono (E p))
    (hcont : ∀ p, StrictlyPositive p → Continuous (E p))
    (hsurj : ∀ p, StrictlyPositive p → ∀ w, 0 < w → ∃ u, E p u = w)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    walrasianDemandPref (recoveredPref E) p w = {x p w} := by
  refine integrability_theorem (fun u => ?_) (fun u => ?_) (fun u => ?_) hmono hcont hsurj
    (fun q u hq _ => hE u q hq) hp hw
  · exact pde_concave (hE u) (fun q hq => hD q (E q u) hq (hEpos q u hq))
      fun q hq => hnsd q (E q u) hq (hEpos q u hq)
  · exact pde_hd1 (hE u) fun q hq => hwal q (E q u) ⟨hq, hEpos q u hq⟩
  · exact pde_monotone (hE u) fun q hq => hnn q (E q u) hq (hEpos q u hq)

end MWG.ClassicalDemand
