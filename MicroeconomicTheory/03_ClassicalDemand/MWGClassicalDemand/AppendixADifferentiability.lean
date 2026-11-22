/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixAContinuity
import MWGClassicalDemand.AppendixABordered
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MWGConsumerChoice.AppendixMDBasic

/-!
# Appendix A to Chapter 3: differentiability of Walrasian demand

MWG, Appendix A to Chapter 3, "Differentiability", pp. 94-95.

Standing assumptions of the passage: `u` is twice continuously differentiable (`ContDiff ℝ 2 u`)
and represents a locally nonsatiated preference on `ℝ^L_+`; demand is a function
(`x(p, w) = {s(p, w)}`, which strict quasiconcavity gives) with `x(p, w) ≫ 0` for `(p, w) ≫ 0`
(the assumption at the start of the appendix). The gradient map is `G(x) = ∇u(x)`.

* "The first-order conditions imply that `x(p, w) ≫ 0` is, for some `λ > 0`, a solution of
  `∇u(x) - λp = 0`, `p·x - w = 0`" (`appendixA_foc_of_demand`); the multiplier is
  `λ(p, w) = ∇u(x(p, w))·x(p, w) / w`.
* The Jacobian of this system with respect to `(x, λ)` is `[[D²u(x), -p], [pᵀ, 0]]`
  (`appendixAFocSystem_hasStrictFDerivAt`, the strict derivative of the system in all variables).
* **The implicit function theorem step** (Mathlib's `implicitFunctionOfProdDomain`): if the
  Jacobian is nonsingular at `x(p̄, w̄)`, demand is differentiable at `(p̄, w̄)`
  (`appendixA_demand_differentiableAt_of_jacobian`).
* The converse ("only if"), which the book also asserts: if demand is differentiable at
  `(p̄, w̄)` and `∇u ≠ 0` there, the Jacobian is nonsingular
  (`appendixA_jacobian_of_demand_differentiableAt`).
* "`x(p, w)` is differentiable iff the determinant of the bordered Hessian of `u` is nonzero at
  `x(p, w)`" (`appendixA_differentiable_iff_bordered`, and from the book's primitive assumptions
  `appendixA_differentiable_iff_bordered_primitive`, with the consistency witness
  `appendixA_oneGoodUtility_assumptions`).
* The fact stated without proof: if demand is differentiable at `(p, w)`, the Slutsky matrix has
  rank `L - 1` (`appendixA_slutsky_rank`, from the linearised first-order conditions
  `appendixA_linearized_foc`: `S v = λ M v` with `p·S v = 0` and `S v = 0 ⇒ v ∈ span p`).

Departure (correction C6): smoothness and strict quasiconcavity are assumed on `x ≫ 0` (with
continuity on `ℝ^L_+`), since a utility that is `C²` with nonzero gradient on all of `ℝ^L` and has
interior demand at every `(p, w) ≫ 0` is not what the book's examples satisfy.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology Matrix

variable {L : ℕ}

/-- The strictly positive orthant `{x : x ≫ 0}`, the interior of `ℝ^L_+`. -/
def appendixAPosOrthant (L : ℕ) : Set (Fin L → ℝ) := {x | ∀ l, 0 < x l}

/-- The strictly positive orthant is open. -/
theorem appendixA_isOpen_posOrthant (L : ℕ) : IsOpen (appendixAPosOrthant L) := by
  have : appendixAPosOrthant L = ⋂ l : Fin L, {x : Fin L → ℝ | 0 < x l} := by
    ext x
    simp [appendixAPosOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)

/-- The first-order system of the UMP as a function of the parameters `(p, w)` and the unknowns
`(x, λ)`: `((p, w), (x, λ)) ↦ (G(x) - λp, p·x - w)` (MWG, p. 94). -/
def appendixAFocSystem (G : (Fin L → ℝ) → (Fin L → ℝ))
    (v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ)) : (Fin L → ℝ) × ℝ :=
  (G v.2.1 - v.2.2 • v.1.1, v.1.1 ⬝ᵥ v.2.1 - v.1.2)

/-- **Appendix A** (MWG, pp. 94-95). If `G = ∇u` has strict derivative `G' = D²u(x̄)` at `x̄`, the
first-order system is strictly differentiable at `((p̄, w̄), (x̄, λ̄))`; its partial derivative in
`(x, λ)` is `(dx, dλ) ↦ (D²u(x̄) dx - dλ p̄, p̄·dx)` (the Jacobian `[[D²u(x), -p], [pᵀ, 0]]`) and
its partial derivative in `(p, w)` is `(dp, dw) ↦ (-λ̄ dp, dp·x̄ - dw)`. -/
theorem appendixAFocSystem_hasStrictFDerivAt {G : (Fin L → ℝ) → (Fin L → ℝ)}
    {G' : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} {xbar : Fin L → ℝ} (hG : HasStrictFDerivAt G G' xbar)
    (pbar : Fin L → ℝ) (wbar lbar : ℝ) :
    ∃ f' : (((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ)) →L[ℝ] ((Fin L → ℝ) × ℝ),
      HasStrictFDerivAt (appendixAFocSystem G) f' ((pbar, wbar), (xbar, lbar)) ∧
      (∀ dx dlam, f' (0, (dx, dlam)) = (G' dx - dlam • pbar, pbar ⬝ᵥ dx)) ∧
      (∀ dp dw, f' ((dp, dw), 0) = (-(lbar • dp), dp ⬝ᵥ xbar - dw)) := by
  set u : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) := ((pbar, wbar), (xbar, lbar)) with hu
  have hx : HasStrictFDerivAt (fun v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) => v.2.1) _ u :=
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := u)).fst
  have hl : HasStrictFDerivAt (fun v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) => v.2.2) _ u :=
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := u)).snd
  have hp : HasStrictFDerivAt (fun v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) => v.1.1) _ u :=
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := u)).fst
  have hw : HasStrictFDerivAt (fun v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) => v.1.2) _ u :=
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := u)).snd
  have h1 := (hG.comp u hx).sub (hl.smul hp)
  have hdot := HasStrictFDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((hasStrictFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin L => ℝ) i pbar).comp u hp).mul
      ((hasStrictFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin L => ℝ) i xbar).comp u hx))
  have h2 : HasStrictFDerivAt
      (fun v : ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) => v.1.1 ⬝ᵥ v.2.1 - v.1.2) _ u :=
    (hdot.sub hw).congr_of_eventuallyEq (Eventually.of_forall fun v => by simp [dotProduct])
  refine ⟨_, h1.prodMk h2, fun dx dlam => ?_, fun dp dw => ?_⟩
  · simp [hu, dotProduct]
  · simp [hu, dotProduct, mul_comm]

/-- The price-wealth domain `(p, w) ≫ 0` is open. -/
theorem appendixA_isOpen_pwDomainSet (L : ℕ) : IsOpen (pwDomainSet L) := by
  have : pwDomainSet L = (⋂ l : Fin L, {q : (Fin L → ℝ) × ℝ | 0 < q.1 l}) ∩ {q | 0 < q.2} := by
    ext q
    simp [pwDomainSet, PWDomain, StrictlyPositive]
  rw [this]
  exact (isOpen_iInter_of_finite fun l =>
    isOpen_lt continuous_const (by fun_prop : Continuous fun q : (Fin L → ℝ) × ℝ => q.1 l)).inter
    (isOpen_lt continuous_const continuous_snd)

/-- For a utility that is `C²` on `x ≫ 0`, the gradient map `x ↦ ∇u(x)` is `C¹` there, hence
strictly differentiable at every `x ≫ 0`, with derivative the Hessian. -/
theorem appendixA_gradient_hasStrictFDerivAt {u : (Fin L → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {x : Fin L → ℝ} (hx : x ∈ appendixAPosOrthant L) :
    HasStrictFDerivAt (fun y => gradientVec (fderiv ℝ u y))
      (fderiv ℝ (fun y => gradientVec (fderiv ℝ u y)) x) x := by
  let gv : ((Fin L → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin L → ℝ) :=
    ContinuousLinearMap.pi fun n => ContinuousLinearMap.apply ℝ ℝ (Pi.single n 1)
  have he : (fun y => gradientVec (fderiv ℝ u y)) = fun y => gv (fderiv ℝ u y) := rfl
  have hc : ContDiffOn ℝ 1 (fun y => gradientVec (fderiv ℝ u y)) (appendixAPosOrthant L) := by
    rw [he]
    exact gv.contDiff.comp_contDiffOn
      (hu.fderiv_of_isOpen (appendixA_isOpen_posOrthant L) (by norm_num))
  exact (hc.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).hasStrictFDerivAt
    (by norm_num)

/-- **Appendix A** (MWG, p. 94), with Section 3.D. At every `(p, w) ≫ 0` the interior demand
`x = x(p, w)` solves the first-order system with `λ = ∇u(x)·x / w`: `∇u(x) = λp` and
`p·x = w`. -/
theorem appendixA_foc_of_demand {u : (Fin L → ℝ) → ℝ}
    (hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) :
    gradientVec (fderiv ℝ u (s p w)) =
        ((gradientVec (fderiv ℝ u (s p w)) ⬝ᵥ s p w) / w) • p ∧ p ⬝ᵥ s p w = w := by
  have hmem : s p w ∈ walrasianDemand u p w := by rw [hs p w hd]; rfl
  have hW := proposition_3_D_2_ii hrep hlns hmem
  obtain ⟨lam, -, hkt⟩ := ump_kuhn_tucker hd.1 hmem
    (hdiff (s p w) (hint p w hd)).hasFDerivAt
  have hG : gradientVec (fderiv ℝ u (s p w)) = lam • p := by
    funext l
    rw [(hkt l).2 (hint p w hd l)]
    rfl
  refine ⟨?_, hW⟩
  rw [hG, smul_dotProduct, hW, smul_eq_mul, mul_div_assoc, div_self hd.2.ne',
    mul_one]

/-- The multiplier `λ(p, w) = ∇u(x(p, w))·x(p, w) / w`. -/
noncomputable def appendixADemandMultiplier (u : (Fin L → ℝ) → ℝ) (s : DemandFunction L)
    (q : (Fin L → ℝ) × ℝ) : ℝ :=
  gradientVec (fderiv ℝ u (s q.1 q.2)) ⬝ᵥ s q.1 q.2 / q.2

/-- **Appendix A** (MWG, pp. 94-95), the implicit function theorem step. Under the standing
assumptions, if the Jacobian of the first-order system with respect to `(x, λ)` is nonsingular
at `x(p̄, w̄)` (its linearisation `(dx, dλ) ↦ (D²u dx - dλ p̄, p̄·dx)` has trivial kernel), the
demand function is differentiable at `(p̄, w̄)`. -/
theorem appendixA_demand_differentiableAt_of_jacobian {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hd : PWDomain pbar wbar)
    (hJ : ∀ (dx : Fin L → ℝ) (dlam : ℝ),
      fderiv ℝ (fun y => gradientVec (fderiv ℝ u y)) (s pbar wbar) dx - dlam • pbar = 0 →
        pbar ⬝ᵥ dx = 0 → dx = 0 ∧ dlam = 0) :
    DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) := by
  classical
  set G : (Fin L → ℝ) → (Fin L → ℝ) := fun y => gradientVec (fderiv ℝ u y) with hGdef
  have hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).differentiableAt (by norm_num)
  set xbar := s pbar wbar with hxbar
  set lbar := appendixADemandMultiplier u s (pbar, wbar) with hlbar
  have hG := appendixA_gradient_hasStrictFDerivAt hu (x := xbar) (hint pbar wbar hd)
  obtain ⟨f', hf, hJf, -⟩ := appendixAFocSystem_hasStrictFDerivAt hG pbar wbar lbar
  -- the partial derivative in `(x, λ)` is invertible
  set J := f'.comp (ContinuousLinearMap.inr ℝ ((Fin L → ℝ) × ℝ) ((Fin L → ℝ) × ℝ)) with hJdef
  have hJinj : Function.Injective J := by
    rw [injective_iff_map_eq_zero J]
    rintro ⟨dx, dlam⟩ h0
    have := hJf dx dlam
    simp only [hJdef, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply] at h0
    rw [this] at h0
    obtain ⟨h1, h2⟩ := hJ dx dlam (congrArg Prod.fst h0) (congrArg Prod.snd h0)
    rw [h1, h2]
    rfl
  have hJsurj : Function.Surjective J :=
    LinearMap.injective_iff_surjective
      (f := (↑J : ((Fin L → ℝ) × ℝ) →ₗ[ℝ] ((Fin L → ℝ) × ℝ))).mp hJinj
  have hinv : J.IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective J (LinearMap.ker_eq_bot.mpr hJinj)
      (LinearMap.range_eq_top.mpr hJsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  -- the implicit function and the demand coincide near `(p̄, w̄)`
  have hiff := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  set ψ := hf.implicitFunctionOfProdDomain hinv with hψ
  have hψd : DifferentiableAt ℝ ψ (pbar, wbar) :=
    (hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).differentiableAt
  have hcont : ContinuousAt (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) := by
    have := proposition_3_AA_1_continuous hc hs
    exact this.continuousAt ((appendixA_isOpen_pwDomainSet L).mem_nhds hd)
  have hlamcont : ContinuousAt (appendixADemandMultiplier u s) (pbar, wbar) := by
    have hGc : ContinuousAt (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2)) (pbar, wbar) :=
      ContinuousAt.comp (g := G) (f := fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) hG.continuousAt
        hcont
    have hdot : ContinuousAt (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2) ⬝ᵥ s q.1 q.2)
        (pbar, wbar) := by
      simp only [dotProduct]
      exact tendsto_finsetSum _ fun l _ =>
        (((continuous_apply l).continuousAt.comp hGc).mul
          ((continuous_apply l).continuousAt.comp hcont)).tendsto
    exact hdot.div continuous_snd.continuousAt hd.2.ne'
  have hV : Tendsto (fun q : (Fin L → ℝ) × ℝ => (q, (s q.1 q.2, appendixADemandMultiplier u s q)))
      (𝓝 (pbar, wbar)) (𝓝 ((pbar, wbar), (xbar, lbar))) :=
    tendsto_id.prodMk_nhds (hcont.tendsto.prodMk_nhds hlamcont.tendsto)
  have hfoc : ∀ q ∈ pwDomainSet L,
      appendixAFocSystem G (q, (s q.1 q.2, appendixADemandMultiplier u s q)) = 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := appendixA_foc_of_demand hdiff hrep hlns hs hint hq
    simp only [appendixAFocSystem, appendixADemandMultiplier]
    rw [← h1, h2, sub_self, sub_self]
    rfl
  have hfu : appendixAFocSystem G ((pbar, wbar), (xbar, lbar)) = 0 := hfoc (pbar, wbar) hd
  have hev : ∀ᶠ q in 𝓝 (pbar, wbar), s q.1 q.2 = (ψ q).1 := by
    filter_upwards [hV.eventually hiff, (appendixA_isOpen_pwDomainSet L).mem_nhds hd] with q h1 h2
    have := h1.mp (by rw [hfoc q h2, hfu])
    rw [this]
  exact (hψd.fst).congr_of_eventuallyEq hev

/-- **Appendix A** (MWG, p. 95), the converse ("only if"). Under the standing assumptions and
`∇u(x̄) ≠ 0`, if the demand function is differentiable at `(p̄, w̄)`, the Jacobian of the
first-order system is nonsingular at `x(p̄, w̄)`. -/
theorem appendixA_jacobian_of_demand_differentiableAt {u : (Fin L → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hd : PWDomain pbar wbar) (hgrad : gradientVec (fderiv ℝ u (s pbar wbar)) ≠ 0)
    (hsd : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)) :
    ∀ (dx : Fin L → ℝ) (dlam : ℝ),
      fderiv ℝ (fun y => gradientVec (fderiv ℝ u y)) (s pbar wbar) dx - dlam • pbar = 0 →
        pbar ⬝ᵥ dx = 0 → dx = 0 ∧ dlam = 0 := by
  classical
  set G : (Fin L → ℝ) → (Fin L → ℝ) := fun y => gradientVec (fderiv ℝ u y) with hGdef
  have hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).differentiableAt (by norm_num)
  set xbar := s pbar wbar with hxbar
  set lbar := appendixADemandMultiplier u s (pbar, wbar) with hlbar
  have hG := appendixA_gradient_hasStrictFDerivAt hu (x := xbar) (hint pbar wbar hd)
  obtain ⟨f', hf, hJf, hAf⟩ := appendixAFocSystem_hasStrictFDerivAt hG pbar wbar lbar
  have hfoc : ∀ q ∈ pwDomainSet L,
      appendixAFocSystem G (q, (s q.1 q.2, appendixADemandMultiplier u s q)) = 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := appendixA_foc_of_demand hdiff hrep hlns hs hint hq
    simp only [appendixAFocSystem, appendixADemandMultiplier]
    rw [← h1, h2, sub_self, sub_self]
    rfl
  have hlbar0 : lbar ≠ 0 := by
    intro h0
    apply hgrad
    have := (appendixA_foc_of_demand hdiff hrep hlns hs hint hd).1
    rw [this]
    change lbar • pbar = 0
    rw [h0, zero_smul]
  -- the multiplier is differentiable at `(p̄, w̄)`
  have hGd : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2)) (pbar, wbar) :=
    DifferentiableAt.comp (f := fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)
      hG.differentiableAt hsd
  have hlamd : DifferentiableAt ℝ (appendixADemandMultiplier u s) (pbar, wbar) := by
    have hdot : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2) ⬝ᵥ s q.1 q.2)
        (pbar, wbar) := by
      simp only [dotProduct]
      exact DifferentiableAt.fun_sum fun l _ =>
        (differentiableAt_pi.mp hGd l).mul (differentiableAt_pi.mp hsd l)
    have hmul := hdot.mul (differentiableAt_snd.inv (by simpa using hd.2.ne'))
    convert hmul using 1
    funext q
    simp only [appendixADemandMultiplier, div_eq_mul_inv, hGdef, Pi.mul_apply, Pi.inv_apply]
  -- differentiate the identity `F((p, w), (x(p, w), λ(p, w))) = 0`
  set V : (Fin L → ℝ) × ℝ → ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) :=
    fun q => (q, (s q.1 q.2, appendixADemandMultiplier u s q)) with hVdef
  have hVd : HasFDerivAt V ((ContinuousLinearMap.id ℝ _).prod
      ((fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)).prod
        (fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar)))) (pbar, wbar) :=
    (hasFDerivAt_id _).prodMk (hsd.hasFDerivAt.prodMk hlamd.hasFDerivAt)
  have hcomp := hf.hasFDerivAt.comp (pbar, wbar) hVd
  have hzero : HasFDerivAt (𝕜 := ℝ) (appendixAFocSystem G ∘ V) 0 (pbar, wbar) := by
    apply (hasFDerivAt_const (0 : (Fin L → ℝ) × ℝ) (pbar, wbar)).congr_of_eventuallyEq
    filter_upwards [(appendixA_isOpen_pwDomainSet L).mem_nhds hd] with q hq
    exact hfoc q hq
  have huniq := hcomp.unique hzero
  -- hence `J` is surjective: `J (Dx dq, Dλ dq) = -A dq`, and `A` is onto since `λ̄ ≠ 0`
  set J := f'.comp (ContinuousLinearMap.inr ℝ ((Fin L → ℝ) × ℝ) ((Fin L → ℝ) × ℝ)) with hJdef
  have hJsurj : Function.Surjective J := by
    rintro ⟨a, b⟩
    set dq : (Fin L → ℝ) × ℝ := (lbar⁻¹ • a, b + (lbar⁻¹ • a) ⬝ᵥ xbar) with hdq
    have h0 := congrArg (fun T => T dq) huniq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_id', id_eq, _root_.zero_apply] at h0
    refine ⟨(fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) dq,
      fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) dq), ?_⟩
    have hsplit : f' (dq, (fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) dq,
        fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) dq)) =
        f' (dq, 0) + J (fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) dq,
          fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) dq) := by
      rw [hJdef, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inr_apply, ← map_add]
      simp
    rw [h0, hdq, hAf] at hsplit
    have hfst := congrArg Prod.fst hsplit
    have hsnd := congrArg Prod.snd hsplit
    simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add] at hfst hsnd
    rw [smul_smul, mul_inv_cancel₀ hlbar0, one_smul] at hfst
    ext
    · simp only at hfst ⊢
      rw [eq_neg_add_iff_add_eq] at hfst
      rw [← hfst, add_zero]
    · simp only at hsnd ⊢
      linarith
  have hJinj : Function.Injective J :=
    LinearMap.injective_iff_surjective
      (f := (↑J : ((Fin L → ℝ) × ℝ) →ₗ[ℝ] ((Fin L → ℝ) × ℝ))).mpr hJsurj
  intro dx dlam h1 h2
  have hJ0 : J (dx, dlam) = J 0 := by
    rw [map_zero, hJdef, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply, hJf, h1, h2]
    rfl
  have := hJinj hJ0
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **Appendix A** (MWG, p. 95). "We conclude that `x(p, w)` is differentiable if and only if
the determinant of the bordered Hessian of `u(·)` is nonzero at `x(p, w)`." Under the standing
assumptions and `∇u(x(p̄, w̄)) ≠ 0`, demand is differentiable at `(p̄, w̄)` iff
`det [[D²u(x̄), ∇u(x̄)], [∇u(x̄)ᵀ, 0]] ≠ 0` at `x̄ = x(p̄, w̄)`. -/
theorem appendixA_differentiable_iff_bordered {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hd : PWDomain pbar wbar) (hgrad : gradientVec (fderiv ℝ u (s pbar wbar)) ≠ 0) :
    DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) ↔
      (appendixABorderedHessian (MWG.ConsumerChoice.hessianMatrix u (s pbar wbar))
        (gradientVec (fderiv ℝ u (s pbar wbar)))).det ≠ 0 := by
  have hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).differentiableAt (by norm_num)
  obtain ⟨hfoc, -⟩ := appendixA_foc_of_demand hdiff hrep hlns hs hint hd
  set lbar := gradientVec (fderiv ℝ u (s pbar wbar)) ⬝ᵥ s pbar wbar / wbar with hlbar
  have hlbar0 : lbar ≠ 0 := by
    intro h0
    apply hgrad
    rw [hfoc, h0, zero_smul]
  rw [← appendixAFocJacobian_det_ne_zero_iff_bordered _ hfoc hlbar0,
    appendixAFocJacobian_det_ne_zero_iff]
  have hmv : ∀ dx, MWG.ConsumerChoice.hessianMatrix u (s pbar wbar) *ᵥ dx =
      fderiv ℝ (fun y => gradientVec (fderiv ℝ u y)) (s pbar wbar) dx := fun dx =>
    jacobian_mulVec _ dx
  simp only [hmv]
  exact ⟨appendixA_jacobian_of_demand_differentiableAt hu hrep hlns hs hint hd hgrad,
    appendixA_demand_differentiableAt_of_jacobian hc hu hrep hlns hs hint hd⟩

/-- **Appendix A** (MWG, p. 94): "if `u` is strictly quasiconcave, `x(p, w)` is a function". A
utility continuous on `ℝ^L_+` and strictly quasiconcave on `x ≫ 0`, whose demanded bundles are all
`≫ 0`, has a demand function `s` with `x(p, w) = {s(p, w)}` at every `(p, w) ≫ 0`
(Propositions 3.D.1 and 3.D.2(iii)). -/
theorem appendixA_exists_demandFunction_of_strictlyQuasiconcave {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hq : StrictlyQuasiconcaveOn (appendixAPosOrthant L) u)
    (hint : ∀ p w, PWDomain p w → ∀ x ∈ walrasianDemand u p w, ∀ l, 0 < x l) :
    ∃ s : DemandFunction L, ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w} := by
  classical
  have hex : ∀ p w, ∃ x : Fin L → ℝ, PWDomain p w → walrasianDemand u p w = {x} := by
    intro p w
    by_cases hd : PWDomain p w
    · obtain ⟨x, hx⟩ := proposition_3_D_1 hc hd.1 hd.2.le
      refine ⟨x, fun _ => Set.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => ?_⟩⟩
      by_contra hne
      have heq : u y = u x := le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
      have hmem : (1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x ∈ budgetSet p w :=
        convex_budgetSet p w hy.1 hx.1 (by norm_num) (by norm_num) (by norm_num)
      have hlt := hq.2 y (hint p w hd y hy) x (hint p w hd x hx) hne (1 / 2) (by norm_num)
        (by norm_num) (u y) le_rfl heq.le
      exact absurd (hy.2 _ hmem) (not_le.mpr hlt)
    · exact ⟨0, fun h => absurd h hd⟩
  choose s hs using hex
  exact ⟨s, hs⟩

/-- **Appendix A** (MWG, pp. 94-95), from the book's assumptions: `u` is continuous on `ℝ^L_+`,
`C²` and strictly quasiconcave on `x ≫ 0` with `∇u ≠ 0` there, represents a locally nonsatiated
preference, and every demanded bundle at `(p, w) ≫ 0` is `≫ 0`. Then demand is a function `s`,
and at every `(p̄, w̄) ≫ 0` it is differentiable iff the bordered Hessian determinant of `u` at
`x(p̄, w̄)` is nonzero. -/
theorem appendixA_differentiable_iff_bordered_primitive {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    (hq : StrictlyQuasiconcaveOn (appendixAPosOrthant L) u)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hint : ∀ p w, PWDomain p w → ∀ x ∈ walrasianDemand u p w, ∀ l, 0 < x l)
    (hgrad : ∀ x ∈ appendixAPosOrthant L, gradientVec (fderiv ℝ u x) ≠ 0) :
    ∃ s : DemandFunction L, (∀ p w, PWDomain p w → walrasianDemand u p w = {s p w}) ∧
      ∀ pbar wbar, PWDomain pbar wbar →
        (DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) ↔
          (appendixABorderedHessian (MWG.ConsumerChoice.hessianMatrix u (s pbar wbar))
            (gradientVec (fderiv ℝ u (s pbar wbar)))).det ≠ 0) := by
  obtain ⟨s, hs⟩ := appendixA_exists_demandFunction_of_strictlyQuasiconcave hc hq hint
  have hint' : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l := by
    intro p w hd
    exact hint p w hd (s p w) (by rw [hs p w hd]; rfl)
  exact ⟨s, hs, fun pbar wbar hd =>
    appendixA_differentiable_iff_bordered hc hu hrep hlns hs hint' hd
      (hgrad _ (hint' pbar wbar hd))⟩

/-- The one-good utility `u(x) = x₁`, a witness that the assumptions of
`appendixA_differentiable_iff_bordered_primitive` are consistent. -/
def appendixAOneGoodUtility (x : Fin 1 → ℝ) : ℝ := x 0

/-- **Appendix A**, consistency of the assumptions: `u(x) = x₁` with `L = 1` satisfies every
hypothesis of `appendixA_differentiable_iff_bordered_primitive`; its demand `w/p` is `≫ 0`. -/
theorem appendixA_oneGoodUtility_assumptions :
    ContinuousOn appendixAOneGoodUtility (nonnegOrthant 1) ∧
      ContDiffOn ℝ 2 appendixAOneGoodUtility (appendixAPosOrthant 1) ∧
      StrictlyQuasiconcaveOn (appendixAPosOrthant 1) appendixAOneGoodUtility ∧
      LocallyNonsatiated (nonnegOrthant 1) (utilityPref appendixAOneGoodUtility) ∧
      (∀ p w, PWDomain p w → ∀ x ∈ walrasianDemand appendixAOneGoodUtility p w, ∀ l, 0 < x l) ∧
      ∀ x ∈ appendixAPosOrthant 1, gradientVec (fderiv ℝ appendixAOneGoodUtility x) ≠ 0 := by
  have hd : ∀ x : Fin 1 → ℝ, HasFDerivAt appendixAOneGoodUtility
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := fun x =>
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0 x
  refine ⟨(continuous_apply 0).continuousOn, (contDiff_apply ℝ ℝ 0).contDiffOn, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx y hy a b ha hb hab l => ?_, fun x _ y _ hxy α hα0 hα1 t htx hty => ?_⟩
    · fin_cases l
      change 0 < a * x 0 + b * y 0
      have hx0 := hx 0
      have hy0 := hy 0
      have hm : 0 < min (x 0) (y 0) := lt_min hx0 hy0
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (x 0) (y 0)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (x 0) (y 0)) hb
      have h3 : a * min (x 0) (y 0) + b * min (x 0) (y 0) = min (x 0) (y 0) := by
        rw [← add_mul, hab, one_mul]
      linarith
    · have hne : x 0 ≠ y 0 := fun h => hxy (funext fun l => by fin_cases l; exact h)
      simp only [appendixAOneGoodUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at htx hty ⊢
      rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
  · intro x _ ε hε
    refine ⟨x + fun _ => ε, fun l => ?_, ?_, ?_⟩
    · have := ‹x ∈ nonnegOrthant 1› l
      simp only [Pi.add_apply]
      linarith
    · rw [euclidDist_add_const, abs_of_pos hε]
      simp
    · simp only [Kreps.PreferenceProperties.Strict, utilityPref, appendixAOneGoodUtility,
        Pi.add_apply]
      constructor <;> linarith
  · intro p w hdom x hx l
    fin_cases l
    have hopt := hx.2 (fun _ => w / p 0) ⟨fun _ => (div_pos hdom.2 (hdom.1 0)).le, by
      simp [dotProduct, mul_div_cancel₀ _ (hdom.1 0).ne']⟩
    simp only [appendixAOneGoodUtility] at hopt
    have := div_pos hdom.2 (hdom.1 0)
    simp only [Fin.zero_eta]
    linarith
  · intro x _ h
    have := congrFun h 0
    rw [(hd x).fderiv] at this
    simp [gradientVec] at this

/-- **Appendix A** (MWG, p. 95), the linearised first-order conditions. If the demand function
is differentiable at `(p̄, w̄)`, differentiating `∇u(x(p, w)) = λ(p, w)p`, `p·x(p, w) = w` gives,
for every direction `(dp, dw)`, `D²u(x̄) Dx(dp, dw) - Dλ(dp, dw) p̄ = λ̄ dp` and
`p̄·Dx(dp, dw) = dw - dp·x̄`. -/
theorem appendixA_linearized_foc {u : (Fin L → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hd : PWDomain pbar wbar)
    (hsd : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar))
    (dp : Fin L → ℝ) (dw : ℝ) :
    fderiv ℝ (fun y => gradientVec (fderiv ℝ u y)) (s pbar wbar)
        (fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) (dp, dw)) -
      fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) (dp, dw) • pbar =
        appendixADemandMultiplier u s (pbar, wbar) • dp ∧
    pbar ⬝ᵥ fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) (dp, dw) =
      dw - dp ⬝ᵥ s pbar wbar := by
  classical
  set G : (Fin L → ℝ) → (Fin L → ℝ) := fun y => gradientVec (fderiv ℝ u y) with hGdef
  have hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).differentiableAt (by norm_num)
  set xbar := s pbar wbar with hxbar
  set lbar := appendixADemandMultiplier u s (pbar, wbar) with hlbar
  have hG := appendixA_gradient_hasStrictFDerivAt hu (x := xbar) (hint pbar wbar hd)
  obtain ⟨f', hf, hJf, hAf⟩ := appendixAFocSystem_hasStrictFDerivAt hG pbar wbar lbar
  have hfoc : ∀ q ∈ pwDomainSet L,
      appendixAFocSystem G (q, (s q.1 q.2, appendixADemandMultiplier u s q)) = 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := appendixA_foc_of_demand hdiff hrep hlns hs hint hq
    simp only [appendixAFocSystem, appendixADemandMultiplier]
    rw [← h1, h2, sub_self, sub_self]
    rfl
  have hGd : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2)) (pbar, wbar) :=
    DifferentiableAt.comp (f := fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)
      hG.differentiableAt hsd
  have hlamd : DifferentiableAt ℝ (appendixADemandMultiplier u s) (pbar, wbar) := by
    have hdot : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => G (s q.1 q.2) ⬝ᵥ s q.1 q.2)
        (pbar, wbar) := by
      simp only [dotProduct]
      exact DifferentiableAt.fun_sum fun l _ =>
        (differentiableAt_pi.mp hGd l).mul (differentiableAt_pi.mp hsd l)
    have hmul := hdot.mul (differentiableAt_snd.inv (by simpa using hd.2.ne'))
    convert hmul using 1
    funext q
    simp only [appendixADemandMultiplier, div_eq_mul_inv, hGdef, Pi.mul_apply, Pi.inv_apply]
  set V : (Fin L → ℝ) × ℝ → ((Fin L → ℝ) × ℝ) × ((Fin L → ℝ) × ℝ) :=
    fun q => (q, (s q.1 q.2, appendixADemandMultiplier u s q)) with hVdef
  have hVd : HasFDerivAt V ((ContinuousLinearMap.id ℝ _).prod
      ((fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)).prod
        (fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar)))) (pbar, wbar) :=
    (hasFDerivAt_id _).prodMk (hsd.hasFDerivAt.prodMk hlamd.hasFDerivAt)
  have hcomp := hf.hasFDerivAt.comp (pbar, wbar) hVd
  have hzero : HasFDerivAt (𝕜 := ℝ) (appendixAFocSystem G ∘ V) 0 (pbar, wbar) := by
    apply (hasFDerivAt_const (0 : (Fin L → ℝ) × ℝ) (pbar, wbar)).congr_of_eventuallyEq
    filter_upwards [(appendixA_isOpen_pwDomainSet L).mem_nhds hd] with q hq
    exact hfoc q hq
  have huniq := hcomp.unique hzero
  have h0 := congrArg (fun T => T (dp, dw)) huniq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, _root_.zero_apply] at h0
  set a := fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar) (dp, dw) with ha
  set b := fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) (dp, dw) with hb
  have hsplit : f' ((dp, dw), (a, b)) = f' ((dp, dw), 0) + f' (0, (a, b)) := by
    rw [← map_add]
    simp
  rw [h0, hAf, hJf] at hsplit
  have hfst := congrArg Prod.fst hsplit
  have hsnd := congrArg Prod.snd hsplit
  simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add] at hfst hsnd
  refine ⟨?_, by linarith⟩
  rw [eq_comm, ← sub_eq_zero] at hfst
  rw [← sub_eq_zero]
  rw [← hfst]
  abel

/-- **Appendix A** (MWG, p. 95), the claim stated without proof: "if `x(p, w)` is differentiable
at `(p, w)`, then the Slutsky matrix `S(p, w)` has maximal possible rank, `L - 1`". Under the
standing assumptions (with `∇u(x(p̄, w̄)) ≠ 0`), `rank S(p̄, w̄) = L - 1`. -/
theorem appendixA_slutsky_rank {u : (Fin L → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u (appendixAPosOrthant L))
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w})
    (hint : ∀ p w, PWDomain p w → ∀ l, 0 < s p w l) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hd : PWDomain pbar wbar) (hgrad : gradientVec (fderiv ℝ u (s pbar wbar)) ≠ 0)
    (hsd : DifferentiableAt ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar)) :
    (slutskyMatrix (fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar))
      (s pbar wbar)).rank = L - 1 := by
  classical
  set Smat := slutskyMatrix (fderiv ℝ (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pbar, wbar))
    (s pbar wbar) with hSmat
  have hdiff : ∀ x ∈ appendixAPosOrthant L, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt ((appendixA_isOpen_posOrthant L).mem_nhds hx)).differentiableAt (by norm_num)
  set lbar := appendixADemandMultiplier u s (pbar, wbar) with hlbar
  have hlbar0 : lbar ≠ 0 := by
    intro h0
    apply hgrad
    have := (appendixA_foc_of_demand hdiff hrep hlns hs hint hd).1
    rw [this]
    change lbar • pbar = 0
    rw [h0, zero_smul]
  have hlin := appendixA_linearized_foc hu hrep hlns hs hint hd hsd
  have hp0 : ∀ v, pbar ⬝ᵥ (Smat *ᵥ v) = 0 := by
    intro v
    rw [hSmat, slutskyMatrix_mulVec, (hlin v _).2, dotProduct_comm, sub_self]
  have hker : ∀ v, Smat *ᵥ v = 0 → v ∈ Submodule.span ℝ {pbar} := by
    intro v hv
    have h1 := (hlin v (v ⬝ᵥ s pbar wbar)).1
    rw [hSmat, slutskyMatrix_mulVec] at hv
    rw [hv, map_zero, zero_sub] at h1
    rw [Submodule.mem_span_singleton]
    refine ⟨-(fderiv ℝ (appendixADemandMultiplier u s) (pbar, wbar) (v, v ⬝ᵥ s pbar wbar)) /
      lbar, ?_⟩
    rw [← hlbar] at h1
    rw [div_eq_inv_mul, mul_smul, neg_smul, h1, smul_smul, inv_mul_cancel₀ hlbar0, one_smul]
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have := Smat.rank_le_card_width
    simp at this
    simp [this]
  · have hpne : pbar ≠ 0 := fun h => by
      have := hd.1 ⟨0, hL⟩
      rw [h] at this
      exact lt_irrefl _ this
    let φ : (Fin L → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => pbar ⬝ᵥ y
        map_add' := dotProduct_add pbar
        map_smul' := fun c y => dotProduct_smul c pbar y }
    have hpp : 0 < pbar ⬝ᵥ pbar := MWG.ConsumerChoice.dotProduct_self_pos_of_ne_zero hpne
    have hφsurj : LinearMap.range φ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨(t / (pbar ⬝ᵥ pbar)) • pbar, ?_⟩
      change pbar ⬝ᵥ ((t / (pbar ⬝ᵥ pbar)) • pbar) = t
      rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hpp.ne']
    have hkerφ : Module.finrank ℝ (LinearMap.ker φ) = L - 1 := by
      have := LinearMap.finrank_range_add_finrank_ker φ
      rw [hφsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
      omega
    have hrange_le : LinearMap.range Smat.mulVecLin ≤ LinearMap.ker φ := by
      rintro y ⟨v, rfl⟩
      exact hp0 v
    have hker_le : LinearMap.ker Smat.mulVecLin ≤ Submodule.span ℝ {pbar} :=
      fun v hv => hker v hv
    have h1 : Module.finrank ℝ (LinearMap.range Smat.mulVecLin) ≤ L - 1 := by
      rw [← hkerφ]
      exact Submodule.finrank_mono hrange_le
    have h2 : Module.finrank ℝ (LinearMap.ker Smat.mulVecLin) ≤ 1 :=
      (Submodule.finrank_mono hker_le).trans (finrank_span_singleton hpne).le
    have h3 := LinearMap.finrank_range_add_finrank_ker Smat.mulVecLin
    rw [Module.finrank_fin_fun] at h3
    rw [Matrix.rank]
    omega

end MWG.ClassicalDemand
