/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpBasic
import MWGConsumerChoice.Slutsky
import MWGConsumerChoice.MatrixDefiniteness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Relationships between demand, indirect utility and expenditure functions

MWG, Section 3.G, pp. 67-75. Throughout, `u` is continuous on `ℝ^L_+` and represents a
strictly convex `≿` (so it is strictly quasiconcave and the Hicksian demand is single-valued).

* **Proposition 3.G.1** (Shephard's lemma): `h(p, ū) = ∇_p e(p, ū)`, proved through the duality
  theorem (the book's Proof 1). Local nonsatiation is not needed.
* **Proposition 3.G.2**: if a Hicksian demand function `h(·, ū)` is differentiable at `p̄`
  (the book asks for continuous differentiability), then `D_p h = D²_p e`, it is negative
  semidefinite (from the compensated law of demand), symmetric (Schwarz's theorem for `e`) and
  `D_p h(p̄, ū) p̄ = 0`; every good has a weak substitute.
* **Proposition 3.G.3** (the Slutsky equation): if a Walrasian demand function is differentiable
  at `(p̄, w̄)`, the Hicksian demand at `ū = v(p̄, w̄)` is differentiable at `p̄` with derivative
  matrix `S(p̄, w̄) = D_p x + D_w x xᵀ` (MWG Chapter 2's `slutskyMatrix`). Hence `S` is negative
  semidefinite, symmetric and `S p̄ = 0`.
* **Proposition 3.G.4** (Roy's identity): `∇_p v + (∂v/∂w) x = 0`; dividing requires
  `∂v/∂w ≠ 0`, which the book omits (correction B4, `proposition_3_G_4_printed_counterexample`).
* Exercise 3.G.1 (Shephard's lemma from Roy's identity), Hicksian versus Slutsky compensation
  (p. 72).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- The set of strictly positive price vectors is open. -/
theorem relations_isOpen_strictlyPositive (L : ℕ) :
    IsOpen {p : Fin L → ℝ | StrictlyPositive p} := by
  have : {p : Fin L → ℝ | StrictlyPositive p} = ⋂ l, {p : Fin L → ℝ | 0 < p l} := by
    ext p; simp [StrictlyPositive]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)

/-- Strictly positive prices remain strictly positive nearby. -/
theorem relations_eventually_strictlyPositive {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    ∀ᶠ q in 𝓝 p, StrictlyPositive q :=
  (relations_isOpen_strictlyPositive L).mem_nhds hp

/-- A strictly quasiconcave utility has convex upper level sets, so the EMP constraint set is
convex. -/
theorem convex_empConstraintSet {u : (Fin L → ℝ) → ℝ}
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) (ub : ℝ) :
    Convex ℝ (empConstraintSet u ub) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hq.1 hx.1 hy.1 ha hb hab, ?_⟩
  by_cases hxy : x = y
  · subst hxy
    rw [← add_smul, hab, one_smul]
    exact hx.2
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have hb1 : b = 1 - a := by linarith
      have := hq.2 x hx.1 y hy.1 hxy a ha' (by linarith) ub hx.2 hy.2
      rw [hb1]
      exact this.le
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simpa using hx.2
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simpa using hy.2

/-- Shephard's lemma in terms of the utility: for `u` continuous and strictly quasiconcave on
`ℝ^L_+`, `p ≫ 0` and `x ∈ h(p, ū)`, `e(·, ū)` has derivative `q ↦ x·q` at `p`. -/
theorem shephard_lemma {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub : ℝ} {x : Fin L → ℝ} (hx : x ∈ hicksianDemand u p ub) :
    HasFDerivAt (fun q => expenditure u q ub) (dualityDotCLM x) p :=
  (duality_differentiable_of_unique (isClosed_empConstraintSet hu ub)
    (convex_empConstraintSet hq ub) hx
    fun _ hy => exercise_3_E_4_unique hu hq hp ub hy hx).2

/-- **Proposition 3.G.1** (MWG, p. 68; Shephard's lemma). Let `u` be continuous on `ℝ^L_+`,
representing a strictly convex `≿`, `p ≫ 0`, and `ū` attainable. Then `h(p, ū) = {x}` for a
single `x`, and `x = ∇_p e(p, ū)`: `h_l(p, ū) = ∂e(p, ū)/∂p_l` for every `l`. (Local nonsatiation
is not needed.) -/
theorem proposition_3_G_1 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub : ℝ} (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    ∃ x, hicksianDemand u p ub = {x} ∧
      HasFDerivAt (fun q => expenditure u q ub) (dualityDotCLM x) p ∧
      ∀ l, x l = gradientVec (fderiv ℝ (fun q => expenditure u q ub) p) l := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  obtain ⟨x, hx⟩ := exercise_3_E_3 hu hp hne
  have hd := shephard_lemma hu hq hp hx
  refine ⟨x, Set.eq_singleton_iff_unique_mem.mpr ⟨hx, fun _ hy =>
    exercise_3_E_4_unique hu hq hp ub hy hx⟩, hd, fun l => ?_⟩
  rw [hd.fderiv, gradientVec_dualityDotCLM]

/-- The linear map `g ↦ (q ↦ g·q)`. -/
noncomputable def dualityDotLin : (Fin L → ℝ) →L[ℝ] ((Fin L → ℝ) →L[ℝ] ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l).smulRight (ContinuousLinearMap.proj l)

/-- `dualityDotLin g = dualityDotCLM g`. -/
theorem dualityDotLin_apply (g : Fin L → ℝ) : dualityDotLin g = dualityDotCLM g := by
  ext q
  simp [dualityDotLin, dualityDotCLM]

/-- A Hicksian demand selection at `ū` (on `p ≫ 0`) is the gradient of `e(·, ū)` near any
`p̄ ≫ 0`. -/
theorem eventually_hasFDerivAt_expenditure {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u)
    {ub : ℝ} {hf : (Fin L → ℝ) → (Fin L → ℝ)}
    (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) :
    ∀ᶠ q in 𝓝 p, HasFDerivAt (fun q => expenditure u q ub) (dualityDotCLM (hf q)) q := by
  filter_upwards [relations_eventually_strictlyPositive hp] with q hq'
  exact shephard_lemma hu hq hq' (hhf q hq')

/-- **Proposition 3.G.2(i)** (MWG, p. 69). If a Hicksian demand function `h(·, ū)` (a selection
from `h(p, ū)` for all `p ≫ 0`) has derivative `D` at `p̄ ≫ 0`, then `D_p h(p̄, ū) = D²_p e(p̄, ū)`:
the Hessian of `e(·, ū)` at `p̄` is the derivative matrix of `h(·, ū)`. -/
theorem proposition_3_G_2_i {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ}
    {hf : (Fin L → ℝ) → (Fin L → ℝ)} (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt hf D p) :
    MWG.ConsumerChoice.hessianMatrix (fun q => expenditure u q ub) p = jacobian D := by
  have heq : (fun y => gradientVec (fderiv ℝ (fun q => expenditure u q ub) y)) =ᶠ[𝓝 p] hf := by
    filter_upwards [eventually_hasFDerivAt_expenditure hu hq hhf hp] with y hy
    rw [hy.fderiv, gradientVec_dualityDotCLM]
  rw [MWG.ConsumerChoice.hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]

/-- **Proposition 3.G.2(ii)** (MWG, pp. 69-70). The derivative matrix `D_p h(p̄, ū)` of a
Hicksian demand function is negative semidefinite: the differential form of the compensated law
of demand (3.E.5). -/
theorem proposition_3_G_2_ii (u : (Fin L → ℝ) → ℝ) {ub : ℝ}
    {hf : (Fin L → ℝ) → (Fin L → ℝ)} (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt hf D p) : NegSemidef (jacobian D) := by
  intro z
  rw [jacobian_mulVec]
  set γ : ℝ → Fin L → ℝ := fun t => p + t • z with hγ
  have hγd : HasDerivAt γ z 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => hf (γ t)) (D z) 0 := by
    rw [← hγ0] at hD
    exact hD.comp_hasDerivAt 0 hγd
  have hg : HasDerivAt (fun t => ∑ l, z l * hf (γ t) l) (∑ l, z l * D z l) 0 :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hcomp l).const_mul (z l)
  apply hasDerivAt_nonpos_of_right_le hg
  have hcont : Tendsto γ (𝓝[>] 0) (𝓝 p) := by
    rw [← hγ0]
    exact hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hcont.eventually (relations_eventually_strictlyPositive hp), self_mem_nhdsWithin]
    with t ht htpos
  have hlaw := proposition_3_E_4 u (hhf p hp) (hhf (γ t) ht)
  have hsub : γ t - p = t • z := by simp [γ]
  rw [hsub, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hlaw
  rw [hγ0]
  have : z ⬝ᵥ hf (γ t) - z ⬝ᵥ hf p ≤ 0 := by
    by_contra h
    rw [not_le] at h
    have := mul_pos (show (0 : ℝ) < t from htpos) h
    linarith
  simp only [dotProduct] at this
  linarith

/-- **Proposition 3.G.2(iii)** (MWG, pp. 69-70). The derivative matrix `D_p h(p̄, ū)` is
symmetric: it is the Hessian of `e(·, ū)`, whose cross-partials agree (Schwarz's theorem). -/
theorem proposition_3_G_2_iii {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ}
    {hf : (Fin L → ℝ) → (Fin L → ℝ)} (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt hf D p) : ∀ i j, jacobian D i j = jacobian D j i := by
  have h1 : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun q => expenditure u q ub)
      (dualityDotLin (hf q)) q := by
    filter_upwards [eventually_hasFDerivAt_expenditure hu hq hhf hp] with q hq'
    rwa [dualityDotLin_apply]
  have h2 : HasFDerivAt (fun q => dualityDotLin (hf q)) (dualityDotLin.comp D) p :=
    dualityDotLin.hasFDerivAt.comp p hD
  intro i j
  have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
  simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
    dotProduct_single, mul_one] at this
  simpa [jacobian] using this

/-- **Proposition 3.G.2(iv)** (MWG, pp. 69-70). `D_p h(p̄, ū) p̄ = 0`, from homogeneity of degree
zero of `h(·, ū)`. -/
theorem proposition_3_G_2_iv {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ}
    {hf : (Fin L → ℝ) → (Fin L → ℝ)} (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt hf D p) : D p = 0 := by
  set γ : ℝ → Fin L → ℝ := fun t => p + t • p with hγ
  have hγd : HasDerivAt γ p 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => hf (γ t)) (D p) 0 := by
    have hD' := hD
    rw [← hγ0] at hD'
    exact hD'.comp_hasDerivAt 0 hγd
  have hconst : (fun t => hf (γ t)) =ᶠ[𝓝 0] fun _ => hf p := by
    have : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := lt_mem_nhds (by norm_num)
    filter_upwards [this] with t ht
    have hpos : 0 < 1 + t := by linarith
    have hγt : γ t = (1 + t) • p := by simp [γ, add_smul]
    have hmem := hhf (γ t) (by rw [hγt]; exact fun l => mul_pos hpos (hp l))
    rw [hγt, proposition_3_E_3_i u p ub hpos] at hmem
    rw [hγt]
    exact exercise_3_E_4_unique hu hq hp ub hmem (hhf p hp)
  have h0 : HasDerivAt (fun t => hf (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (hf p)).congr_of_eventuallyEq hconst
  exact hcomp.unique h0

/-- **Section 3.G** (MWG, p. 70). Every good has at least one (weak) substitute: if
`D_p h(p̄, ū)` is negative semidefinite with `D_p h(p̄, ū) p̄ = 0`, `p̄ ≫ 0` and there is a good
`k₀ ≠ l`, then `∂h_l/∂p_k ≥ 0` for some `k ≠ l`. -/
theorem every_good_has_substitute {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (hnsd : NegSemidef (jacobian D)) (hDp : D p = 0) (l : Fin L)
    {k₀ : Fin L} (hk₀ : k₀ ≠ l) : ∃ k, k ≠ l ∧ 0 ≤ jacobian D l k := by
  by_contra h
  push Not at h
  have hdiag : jacobian D l l ≤ 0 := by
    have := hnsd (Pi.single l 1)
    simpa [jacobian_mulVec, jacobian] using this
  have hrow : ∑ k, jacobian D l k * p k = 0 := by
    have := congrFun (jacobian_mulVec D p) l
    rw [hDp] at this
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at hrow
  have hneg : ∑ k ∈ Finset.univ.erase l, jacobian D l k * p k < 0 :=
    Finset.sum_neg (fun k hk => mul_neg_of_neg_of_pos (h k (Finset.ne_of_mem_erase hk)) (hp k))
      ⟨k₀, Finset.mem_erase.mpr ⟨hk₀, Finset.mem_univ _⟩⟩
  have := mul_nonpos_of_nonpos_of_nonneg hdiag (hp l).le
  linarith

/-- The derivative of `q ↦ x(q, e(q, ū))` composed from `D_x` and Shephard's lemma has
derivative matrix equal to the Slutsky matrix `S = D_p x + D_w x xᵀ`. -/
theorem jacobian_slutsky_comp (Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (x : Fin L → ℝ) :
    jacobian (Dx.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM x))) =
      slutskyMatrix Dx x := by
  ext l k
  simp only [jacobian, slutskyMatrix, Matrix.of_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, dualityDotCLM_apply,
    dotProduct_single, mul_one, priceEffect, wealthEffect]
  have : ((Pi.single k 1 : Fin L → ℝ), x k) = (Pi.single k 1, 0) + x k • ((0 : Fin L → ℝ), 1) := by
    ext <;> simp
  rw [this, map_add, map_smul]
  simp [mul_comm]

/-- `v(p, w) > u(0)` at `p ≫ 0`, `w > 0` under local nonsatiation. -/
theorem relations_indirectUtility_gt_zero {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    u 0 < indirectUtility u p w :=
  (exp_indirectUtility_ge_zero hu hp le_rfl).trans_lt
    (proposition_3_D_3_ii_wealth hrep hu hlns hp le_rfl hw)

/-- **Proposition 3.G.3** (MWG, p. 71; the Slutsky equation). Let `u` be continuous on `ℝ^L_+`,
representing a locally nonsatiated, strictly convex `≿`; let `x(·, ·)` be a Walrasian demand
function (a selection from `x(p, w)` on `p ≫ 0`, `w > 0`) with derivative `D_x` at `(p̄, w̄)`,
and `ū = v(p̄, w̄)`. Then any Hicksian demand function `h(·, ū)` is differentiable at `p̄` with
derivative `q ↦ D_x(q, x(p̄, w̄)·q)`, whose matrix is the Slutsky matrix:
`∂h_l/∂p_k = ∂x_l/∂p_k + (∂x_l/∂w) x_k` (3.G.3)-(3.G.4). -/
theorem proposition_3_G_3 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    {p₀ : Fin L → ℝ} {w₀ : ℝ} (hpw : PWDomain p₀ w₀)
    {Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry xf) Dx (p₀, w₀))
    {hf : (Fin L → ℝ) → (Fin L → ℝ)}
    (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q (indirectUtility u p₀ w₀)) :
    HasFDerivAt hf
        (Dx.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (xf p₀ w₀)))) p₀ ∧
      jacobian (Dx.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod
        (dualityDotCLM (xf p₀ w₀)))) = slutskyMatrix Dx (xf p₀ w₀) := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  set ub := indirectUtility u p₀ w₀ with hub_def
  have hx₀ := hxf p₀ w₀ hpw
  have hub : u 0 < ub := relations_indirectUtility_gt_zero hrep hu hlns hpw.1 hpw.2
  have huxf : u (xf p₀ w₀) = ub := (indirectUtility_eq_of_mem hx₀).symm
  have hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x := ⟨xf p₀ w₀, hx₀.1.1, huxf.ge⟩
  have hepos : ∀ q, StrictlyPositive q → 0 < expenditure u q ub := by
    intro q hq'
    obtain ⟨y, hy⟩ := exercise_3_E_3 hu hq' hne
    have hy0 : y ≠ 0 := by
      rintro rfl
      linarith [hy.1.2]
    rw [expenditure_eq_of_mem hy]
    exact exp_dotProduct_pos hq' hy.1.1 hy0
  have hcomp : ∀ q, StrictlyPositive q → xf q (expenditure u q ub) ∈ hicksianDemand u q ub := by
    intro q hq'
    rw [equation_3_E_4_left hrep hu hlns hq' hub hne]
    exact hxf q _ ⟨hq', hepos q hq'⟩
  have he₀ : expenditure u p₀ ub = w₀ := by
    rw [hub_def]; exact equation_3_E_1_left hrep hu hlns hpw.1 hpw.2.le
  have hx₀h : xf p₀ w₀ ∈ hicksianDemand u p₀ ub := by
    have := hcomp p₀ hpw.1
    rwa [he₀] at this
  have hsh := shephard_lemma hu hq hpw.1 hx₀h
  have hφ : HasFDerivAt (fun q => (q, expenditure u q ub))
      ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (xf p₀ w₀))) p₀ :=
    (hasFDerivAt_id p₀).prodMk hsh
  have hD' : HasFDerivAt (Function.uncurry xf) Dx (p₀, expenditure u p₀ ub) := by
    rw [he₀]; exact hD
  have hchain := hD'.comp p₀ hφ
  refine ⟨?_, jacobian_slutsky_comp Dx _⟩
  apply hchain.congr_of_eventuallyEq
  filter_upwards [relations_eventually_strictlyPositive hpw.1] with q hq'
  exact exercise_3_E_4_unique hu hq hq' ub (hhf q hq') (hcomp q hq')

/-- **Section 3.G** (MWG, p. 72). When demand is generated by preference maximization, the
Slutsky matrix `S(p̄, w̄)` is negative semidefinite, symmetric and satisfies `S(p̄, w̄) p̄ = 0`. -/
theorem slutsky_matrix_properties {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    {p₀ : Fin L → ℝ} {w₀ : ℝ} (hpw : PWDomain p₀ w₀)
    {Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry xf) Dx (p₀, w₀)) :
    NegSemidef (slutskyMatrix Dx (xf p₀ w₀)) ∧
      (∀ i j, slutskyMatrix Dx (xf p₀ w₀) i j = slutskyMatrix Dx (xf p₀ w₀) j i) ∧
      (slutskyMatrix Dx (xf p₀ w₀)).mulVec p₀ = 0 := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  set ub := indirectUtility u p₀ w₀
  have hx₀ := hxf p₀ w₀ hpw
  have hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x :=
    ⟨xf p₀ w₀, hx₀.1.1, (indirectUtility_eq_of_mem hx₀).le⟩
  have hsel : ∀ q, ∃ y, StrictlyPositive q → y ∈ hicksianDemand u q ub := by
    intro q
    by_cases hq' : StrictlyPositive q
    · obtain ⟨y, hy⟩ := exercise_3_E_3 hu hq' hne
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hq'⟩
  choose hf hhf using hsel
  obtain ⟨hdiff, hjac⟩ := proposition_3_G_3 hrep hu hlns hsc hxf hpw hD hhf
  rw [← hjac]
  refine ⟨proposition_3_G_2_ii u hhf hpw.1 hdiff, proposition_3_G_2_iii hu hq hhf hpw.1 hdiff, ?_⟩
  rw [jacobian_mulVec]
  exact proposition_3_G_2_iv hu hq hhf hpw.1 hdiff

/-- **Section 3.G** (MWG, p. 73). It is impossible to find (continuous, locally nonsatiated,
strictly convex) preferences that rationalize a differentiable demand function whose Slutsky
matrix is not symmetric at some `(p̄, w̄)`. -/
theorem no_rationalization_of_asymmetric_slutsky {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {xf : DemandFunction L}
    {p₀ : Fin L → ℝ} {w₀ : ℝ} (hpw : PWDomain p₀ w₀)
    {Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry xf) Dx (p₀, w₀)) {i j : Fin L}
    (hasym : slutskyMatrix Dx (xf p₀ w₀) i j ≠ slutskyMatrix Dx (xf p₀ w₀) j i) :
    ¬ ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w :=
  fun hxf => hasym ((slutsky_matrix_properties hrep hu hlns hsc hxf hpw hD).2.1 i j)

/-- **Section 3.G** (MWG, p. 72; Figure 3.G.2). Hicksian versus Slutsky wealth compensation:
for `x̄ ∈ x(p̄, w̄)` and `ū = u(x̄)`, `Δw_Hicks = e(p', ū) - w̄ ≤ p'·x̄ - w̄ = Δw_Slutsky`. -/
theorem hicks_le_slutsky_compensation (u : (Fin L → ℝ) → ℝ) {p₀ p' : Fin L → ℝ} {w₀ : ℝ}
    (hp' : StrictlyPositive p') {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p₀ w₀) :
    expenditure u p' (u x) - w₀ ≤ p' ⬝ᵥ x - w₀ := by
  have := supportFn_le (exp_bddBelow hp' (u x)) (⟨hx.1.1, le_rfl⟩ : x ∈ empConstraintSet u (u x))
  change expenditure u p' (u x) ≤ _ at this
  linarith

/-- **Proposition 3.G.4** (MWG, p. 73; Roy's identity), in the form that holds without extra
assumptions: if `v` is differentiable at `(p̄, w̄) ≫ 0` with derivative `D_v`, then
`∂v/∂p_l + (∂v/∂w) x_l(p̄, w̄) = 0` for every `l`; if moreover `∂v/∂w ≠ 0`,
`x_l(p̄, w̄) = -(∂v/∂p_l)/(∂v/∂w)`. -/
theorem proposition_3_G_4 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {p₀ : Fin L → ℝ} {w₀ : ℝ} (hpw : PWDomain p₀ w₀)
    {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) Dv (p₀, w₀))
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p₀ w₀) :
    (∀ l, Dv (Pi.single l 1, 0) + Dv (0, 1) * x l = 0) ∧
      (Dv (0, 1) ≠ 0 → ∀ l, x l = -(Dv (Pi.single l 1, 0) / Dv (0, 1))) := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  set ub := indirectUtility u p₀ w₀ with hub_def
  have huxf : u x = ub := (indirectUtility_eq_of_mem hx).symm
  have hub : u 0 < ub := relations_indirectUtility_gt_zero hrep hu hlns hpw.1 hpw.2
  have hne : ∃ y ∈ nonnegOrthant L, ub ≤ u y := ⟨x, hx.1.1, huxf.ge⟩
  obtain ⟨hxh, he₀⟩ := proposition_3_E_1_i hrep hlns hx
  rw [huxf] at hxh he₀
  have hsh := shephard_lemma hu hq hpw.1 hxh
  have hφ : HasFDerivAt (fun q => (q, expenditure u q ub))
      ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM x)) p₀ :=
    (hasFDerivAt_id p₀).prodMk hsh
  have hD' : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) Dv
      (p₀, expenditure u p₀ ub) := by
    rw [he₀]; exact hD
  have hchain := hD'.comp p₀ hφ
  have hconst : (fun q => indirectUtility u q (expenditure u q ub)) =ᶠ[𝓝 p₀] fun _ => ub := by
    filter_upwards [relations_eventually_strictlyPositive hpw.1] with q hq'
    exact equation_3_E_1_right hu hq' hub hne
  have h0 : HasFDerivAt (fun q => indirectUtility u q (expenditure u q ub)) 0 p₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) ub p₀).congr_of_eventuallyEq hconst
  have heq := hchain.unique h0
  have key : ∀ l, Dv (Pi.single l 1, 0) + Dv (0, 1) * x l = 0 := by
    intro l
    have := congrArg (fun f : (Fin L → ℝ) →L[ℝ] ℝ => f (Pi.single l 1)) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, dualityDotCLM_apply, dotProduct_single, mul_one,
      zero_apply] at this
    have hsplit : ((Pi.single l 1 : Fin L → ℝ), x l) =
        (Pi.single l 1, 0) + x l • ((0 : Fin L → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, smul_eq_mul] at this
    linarith
  refine ⟨key, fun hw l => ?_⟩
  have := key l
  field_simp
  linarith

/-- The utility `(x₁ - 1)³` on `ℝ¹_+` of correction B4. -/
def royCounterexampleUtility (x : Fin 1 → ℝ) : ℝ := (x 0 - 1) ^ 3

/-- The cube is strictly increasing. -/
theorem relations_cube_strictMono : StrictMono fun t : ℝ => t ^ 3 :=
  Odd.strictMono_pow (by decide)

/-- For the utility `(x₁ - 1)³` on `ℝ¹_+`, `v(p, w) = (w/p - 1)³` and `x(p, w) = w/p`. -/
theorem royCounterexample_demand {p : Fin 1 → ℝ} (hp : 0 < p 0) {w : ℝ} (hw : 0 ≤ w) :
    (fun _ => w / p 0) ∈ walrasianDemand royCounterexampleUtility p w ∧
      indirectUtility royCounterexampleUtility p w = (w / p 0 - 1) ^ 3 := by
  have hdot : ∀ y : Fin 1 → ℝ, p ⬝ᵥ y = p 0 * y 0 := by intro y; simp [dotProduct]
  have hmem : (fun _ => w / p 0) ∈ walrasianDemand royCounterexampleUtility p w := by
    refine ⟨⟨fun _ => div_nonneg hw hp.le, ?_⟩, fun y hy => ?_⟩
    · rw [hdot, mul_div_cancel₀ _ hp.ne']
    · have h1 := hy.2
      rw [hdot] at h1
      have h2 : y 0 ≤ w / p 0 := by rw [le_div_iff₀ hp]; linarith
      exact relations_cube_strictMono.monotone (by linarith : y 0 - 1 ≤ w / p 0 - 1)
  exact ⟨hmem, (indirectUtility_eq_of_mem hmem).trans rfl⟩

/-- **Proposition 3.G.4** as printed (MWG, p. 73) is false when `∂v/∂w = 0` (correction B4).
For `L = 1` and `u(x) = (x - 1)³` (continuous, locally nonsatiated, strictly convex on `ℝ¹_+`),
`v(p, w) = (w/p - 1)³` is differentiable at `(1, 1)` with zero derivative, so
`-(∂v/∂p)/(∂v/∂w)` is `0/0` (in Lean, `0`), while `x(1, 1) = 1`. -/
theorem proposition_3_G_4_printed_counterexample :
    RepresentsOn (nonnegOrthant 1) royCounterexampleUtility (utilityPref royCounterexampleUtility) ∧
      ContinuousOn royCounterexampleUtility (nonnegOrthant 1) ∧
      LocallyNonsatiated (nonnegOrthant 1) (utilityPref royCounterexampleUtility) ∧
      PrefStrictlyConvex (nonnegOrthant 1) (utilityPref royCounterexampleUtility) ∧
      HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => indirectUtility royCounterexampleUtility q.1 q.2)
        (0 : ((Fin 1 → ℝ) × ℝ) →L[ℝ] ℝ) (1, 1) ∧
      walrasianDemand royCounterexampleUtility 1 1 = {1} ∧
      (1 : Fin 1 → ℝ) 0 ≠ -((0 : ((Fin 1 → ℝ) × ℝ) →L[ℝ] ℝ) (Pi.single 0 1, 0) /
        (0 : ((Fin 1 → ℝ) × ℝ) →L[ℝ] ℝ) (0, 1)) := by
  have hmono : ∀ a b : Fin 1 → ℝ, a 0 < b 0 →
      royCounterexampleUtility a < royCounterexampleUtility b := by
    intro a b h
    exact relations_cube_strictMono (by linarith : a 0 - 1 < b 0 - 1)
  have hle : ∀ a b : Fin 1 → ℝ, royCounterexampleUtility a ≤ royCounterexampleUtility b →
      a 0 ≤ b 0 := by
    intro a b h
    by_contra h'
    exact absurd h (not_le.mpr (hmono b a (not_le.mp h')))
  refine ⟨representsOn_utilityPref _ _, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · exact (by unfold royCounterexampleUtility; fun_prop :
      Continuous royCounterexampleUtility).continuousOn
  · intro x hx ε hε
    refine ⟨x + fun _ => ε, fun l => add_nonneg (hx l) hε.le, ?_, ?_⟩
    · rw [euclidDist_add_const]
      simp [abs_of_pos hε]
    · exact ⟨(hmono _ _ (by simp [hε])).le, not_le.mpr (hmono _ _ (by simp [hε]))⟩
  · intro x _ y _ z _ hy hz hyz α hα0 hα1
    have hy' := hle x y hy
    have hz' := hle x z hz
    have hyz' : y 0 ≠ z 0 := by
      intro h
      apply hyz
      funext i
      fin_cases i
      exact h
    have hmix : x 0 < (α • y + (1 - α) • z) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases lt_or_gt_of_ne hyz' with h | h
      · nlinarith
      · nlinarith
    exact ⟨(hmono _ _ hmix).le, not_le.mpr (hmono _ _ hmix)⟩
  · have hev : (fun q : (Fin 1 → ℝ) × ℝ => indirectUtility royCounterexampleUtility q.1 q.2)
        =ᶠ[𝓝 (1, 1)]
        fun q => (q.2 / q.1 0 - 1) ^ 3 := by
      have h1 : ∀ᶠ q : (Fin 1 → ℝ) × ℝ in 𝓝 (1, 1), 0 < q.1 0 :=
        (continuous_apply 0 |>.comp continuous_fst).continuousAt.eventually (lt_mem_nhds (by simp))
      have h2 : ∀ᶠ q : (Fin 1 → ℝ) × ℝ in 𝓝 (1, 1), 0 < q.2 :=
        continuous_snd.continuousAt.eventually (lt_mem_nhds (by simp))
      filter_upwards [h1, h2] with q hq1 hq2
      exact (royCounterexample_demand hq1 hq2.le).2
    apply HasFDerivAt.congr_of_eventuallyEq _ hev
    have hg : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × ℝ => q.2 / q.1 0 - 1) (1, 1) := by
      fun_prop (disch := simp)
    have := hg.hasFDerivAt.pow 3
    convert this using 1
    simp
  · have hone : (fun _ : Fin 1 => (1 : ℝ) / (1 : Fin 1 → ℝ) 0) = 1 := by
      funext; simp
    have := (royCounterexample_demand (p := 1) (by simp) zero_le_one).1
    rw [hone] at this
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨this, fun y hy => ?_⟩
    have h1 := hy.2 1 this.1
    have h2 := hy.1.2
    simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Pi.one_apply, one_mul,
      Finset.sum_singleton] at h2
    have h3 := hle _ _ h1
    funext i
    rw [Subsingleton.elim i 0]
    simp only [Pi.one_apply] at h3 ⊢
    linarith

/-- **Exercise 3.G.1** (MWG, p. 99). Proposition 3.G.1 follows from Roy's identity: if `v` is
differentiable at `(p̄, e(p̄))` with `∂v/∂w ≠ 0`, `e` is differentiable at `p̄`, `v(p, e(p)) = ū`
near `p̄`, and Roy's identity holds for `x̄ = x(p̄, e(p̄)) = h(p̄, ū)`, then `∇e(p̄) = x̄`. -/
theorem exercise_3_G_1 {E : (Fin L → ℝ) → ℝ} {V : (Fin L → ℝ) × ℝ → ℝ} {p₀ x : Fin L → ℝ}
    {ub : ℝ} {E' : (Fin L → ℝ) →L[ℝ] ℝ} {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hE : HasFDerivAt E E' p₀) (hV : HasFDerivAt V Dv (p₀, E p₀))
    (hid : ∀ᶠ q in 𝓝 p₀, V (q, E q) = ub) (hw : Dv (0, 1) ≠ 0)
    (hroy : ∀ l, x l = -(Dv (Pi.single l 1, 0) / Dv (0, 1))) : gradientVec E' = x := by
  have hφ : HasFDerivAt (fun q => (q, E q)) ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod E') p₀ :=
    (hasFDerivAt_id p₀).prodMk hE
  have hchain := hV.comp p₀ hφ
  have h0 : HasFDerivAt (fun q => V (q, E q)) 0 p₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) ub p₀).congr_of_eventuallyEq hid
  have heq := hchain.unique h0
  funext l
  have := congrArg (fun f : (Fin L → ℝ) →L[ℝ] ℝ => f (Pi.single l 1)) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at this
  have hsplit : ((Pi.single l 1 : Fin L → ℝ), E' (Pi.single l 1)) =
      (Pi.single l 1, 0) + E' (Pi.single l 1) • ((0 : Fin L → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at this
  rw [hroy l, gradientVec]
  field_simp
  linarith

end MWG.ClassicalDemand
