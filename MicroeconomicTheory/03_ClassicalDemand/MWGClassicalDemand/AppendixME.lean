/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The implicit function theorem

MWG, Mathematical Appendix, Section M.E, pp. 940-943, the part on the implicit function theorem.

The book writes the system (M.E.1) as `f(x; q) = 0` with `N` endogenous variables `x` and `M`
parameters `q`. Here `f : X × Q → F` with `x` first, for Banach spaces `X`, `Q`, `F` (in the book
`X = F = ℝ^N`, `Q = ℝ^M`); the partial derivatives are `D_x f = f' ∘ inl` and
`D_q f = f' ∘ inr`, and the full-rank condition (M.E.2) is invertibility of `D_x f`.

* **Definition M.E.1**: `LocallySolvable` (neighbourhoods `A'`, `B'` and a unique implicit
  function `η : B' → A'`).
* **Theorem M.E.1** and (M.E.3): `theorem_M_E_1` (strictly differentiable `f`; continuous
  differentiability implies this) gives local solvability and
  `Dη(q̄) = -[D_x f]⁻¹ D_q f`; `theorem_M_E_1_contDiff` gives the book's continuously
  differentiable implicit function from a `C¹` system. Both are bridges to Mathlib's
  `HasStrictFDerivAt.implicitFunctionOfProdDomain` and `ContDiffAt.implicitFunction`.
* The one-variable formula `dη/dq = -(∂f/∂q)/(∂f/∂x)` and the inverse function theorem as the
  special case `f(x, q) = φ(x) - q`.
* **Definition M.E.2** (regular systems). **Theorem M.E.2** (transversality) needs Sard's
  theorem and is OPEN.
-/

namespace MWG.ClassicalDemand

open Filter Topology

variable {X Q F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Definition M.E.1** (MWG, p. 941). The system `f(x; q) = 0` can be locally solved at
`(x̄, q̄)` for `x` as a function of `q`: there are open balls `A'` around `x̄` and `B'` around `q̄`
and a function `η` with `η(q̄) = x̄` such that for each `q ∈ B'`, `η(q)` is the unique `x ∈ A'`
with `f(x; q) = 0`. -/
def LocallySolvable (f : X × Q → F) (x : X) (q : Q) (η : Q → X) : Prop :=
  η q = x ∧ ∃ ε > 0, ∃ δ > 0, ∀ q' ∈ Metric.ball q δ,
    η q' ∈ Metric.ball x ε ∧ f (η q', q') = 0 ∧
      ∀ x' ∈ Metric.ball x ε, f (x', q') = 0 → x' = η q'

/-- The swapped system `(q, x) ↦ f(x; q)`. -/
def swapSystem (f : X × Q → F) : Q × X → F := fun z => f (z.2, z.1)

omit [CompleteSpace X] [CompleteSpace Q] [CompleteSpace F] in
/-- The derivative of the swapped system. -/
theorem hasStrictFDerivAt_swapSystem {f : X × Q → F} {f' : X × Q →L[ℝ] F} {x : X} {q : Q}
    (hf : HasStrictFDerivAt f f' (x, q)) :
    HasStrictFDerivAt (swapSystem f)
      (f'.comp ((ContinuousLinearMap.snd ℝ Q X).prod (ContinuousLinearMap.fst ℝ Q X))) (q, x) :=
  HasStrictFDerivAt.comp (f := fun z : Q × X => (z.2, z.1)) (q, x) hf
    (hasStrictFDerivAt_snd.prodMk hasStrictFDerivAt_fst)

omit [NormedSpace ℝ X] [CompleteSpace X] [NormedSpace ℝ Q] [CompleteSpace Q] [NormedSpace ℝ F]
  [CompleteSpace F] in
/-- Local solvability from the eventual characterization `f(z) = 0 ⟺ η(z₂) = z₁` near
`(x̄, q̄)` and continuity of `η` at `q̄`. -/
theorem locallySolvable_of_eventually {f : X × Q → F} {x : X} {q : Q} {η : Q → X}
    (hη : η q = x) (hc : ContinuousAt η q)
    (hiff : ∀ᶠ z in 𝓝 (x, q), f z = 0 ↔ η z.2 = z.1) : LocallySolvable f x q η := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hiff
  have hcont : ∀ᶠ q' in 𝓝 q, η q' ∈ Metric.ball x r := by
    rw [← hη]
    exact hc.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨δ0, hδ0, hδb⟩ := Metric.eventually_nhds_iff.mp hcont
  refine ⟨hη, r, hr, min δ0 r, lt_min hδ0 hr, fun q' hq' => ?_⟩
  rw [Metric.mem_ball] at hq'
  have hq1 : dist q' q < δ0 := hq'.trans_le (min_le_left _ _)
  have hq2 : dist q' q < r := hq'.trans_le (min_le_right _ _)
  have hηq := hδb hq1
  refine ⟨hηq, ?_, fun x' hx' hfx => ?_⟩
  · have hz : dist (η q', q') (x, q) < r := by
      rw [Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp hηq) hq2
    exact (hball hz).mpr rfl
  · have hz : dist (x', q') (x, q) < r := by
      rw [Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp hx') hq2
    exact ((hball hz).mp hfx).symm

/-- **Theorem M.E.1 (implicit function theorem)** (MWG, p. 941) with (M.E.3) (p. 942). If `f`
is strictly differentiable at `(x̄, q̄)` (e.g. continuously differentiable), `f(x̄; q̄) = 0` and
`D_x f(x̄; q̄)` is invertible (M.E.2), then the system can be locally solved at `(x̄, q̄)` by an
implicit function `η` that is differentiable at `q̄` with
`Dη(q̄) = -[D_x f(x̄; q̄)]⁻¹ D_q f(x̄; q̄)`. -/
theorem theorem_M_E_1 {f : X × Q → F} {f' : X × Q →L[ℝ] F} {x : X} {q : Q}
    (hf : HasStrictFDerivAt f f' (x, q)) (h0 : f (x, q) = 0)
    (hinv : (f'.comp (ContinuousLinearMap.inl ℝ X Q)).IsInvertible) :
    ∃ η : Q → X, LocallySolvable f x q η ∧
      HasStrictFDerivAt η (-(f'.comp (ContinuousLinearMap.inl ℝ X Q)).inverse.comp
        (f'.comp (ContinuousLinearMap.inr ℝ X Q))) q := by
  have hg := hasStrictFDerivAt_swapSystem hf
  set g' := f'.comp ((ContinuousLinearMap.snd ℝ Q X).prod (ContinuousLinearMap.fst ℝ Q X))
  have hinr :
      g'.comp (ContinuousLinearMap.inr ℝ Q X) = f'.comp (ContinuousLinearMap.inl ℝ X Q) := by
    ext v; simp [g']
  have hinl :
      g'.comp (ContinuousLinearMap.inl ℝ Q X) = f'.comp (ContinuousLinearMap.inr ℝ X Q) := by
    ext v; simp [g']
  have hinv' : (g'.comp (ContinuousLinearMap.inr ℝ Q X)).IsInvertible := by rwa [hinr]
  set η := hg.implicitFunctionOfProdDomain hinv'
  have hd := hg.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv'
  rw [hinr, hinl] at hd
  have hηq : η q = x := eq_of_tendsto_nhds (hg.tendsto_implicitFunctionOfProdDomain hinv')
  refine ⟨η, locallySolvable_of_eventually hηq hd.continuousAt ?_, hd⟩
  have hiff := hg.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv'
  have hswap : Tendsto (fun z : X × Q => (z.2, z.1)) (𝓝 (x, q)) (𝓝 (q, x)) :=
    (continuous_snd.prodMk continuous_fst).tendsto (x, q)
  filter_upwards [hswap.eventually hiff] with z hz
  simpa [swapSystem, h0] using hz

/-- **Theorem M.E.1** (MWG, p. 941), continuously differentiable form: if `f` is `C¹` at
`(x̄, q̄)` (`C^n`, `n ≥ 1`), `f(x̄; q̄) = 0` and `D_x f` is invertible there, the system is locally
solvable by an implicit function that is itself `C^n` at `q̄`. -/
theorem theorem_M_E_1_contDiff {f : X × Q → F} {x : X} {q : Q} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f (x, q)) (hn : n ≠ 0) (h0 : f (x, q) = 0)
    (hinv : ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ X Q)).IsInvertible) :
    ∃ η : Q → X, LocallySolvable f x q η ∧ ContDiffAt ℝ n η q := by
  have hg : ContDiffAt ℝ n (swapSystem f) (q, x) :=
    hf.comp (q, x) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hstrict := hf.hasStrictFDerivAt hn
  have hgd := hasStrictFDerivAt_swapSystem hstrict
  have hfd : fderiv ℝ (swapSystem f) (q, x) =
      (fderiv ℝ f (x, q)).comp
        ((ContinuousLinearMap.snd ℝ Q X).prod (ContinuousLinearMap.fst ℝ Q X)) :=
    hgd.hasFDerivAt.fderiv
  have hinr : (fderiv ℝ (swapSystem f) (q, x)).comp (ContinuousLinearMap.inr ℝ Q X) =
      (fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ X Q) := by
    rw [hfd]; ext v; simp
  have hinv' : ((fderiv ℝ (swapSystem f) (q, x)).comp
      (ContinuousLinearMap.inr ℝ Q X)).IsInvertible := by rwa [hinr]
  set η := hg.implicitFunction hn hinv'
  have hηq : η q = x := hg.implicitFunction_apply_self hn hinv'
  have hcd : ContDiffAt ℝ n η q := hg.contDiffAt_implicitFunction hn hinv'
  refine ⟨η, locallySolvable_of_eventually hηq (hcd.continuousAt) ?_, hcd⟩
  have hiff := hg.eventually_apply_eq_iff_implicitFunction hn hinv'
  have hswap : Tendsto (fun z : X × Q => (z.2, z.1)) (𝓝 (x, q)) (𝓝 (q, x)) :=
    (continuous_snd.prodMk continuous_fst).tendsto (x, q)
  filter_upwards [hswap.eventually hiff] with z hz
  simpa [swapSystem, h0] using hz

/-- **Section M.E** (MWG, p. 942). With one endogenous variable and one parameter, (M.E.3)
reads `dη(q̄)/dq = -(∂f/∂q)/(∂f/∂x)`. -/
theorem implicit_function_one_variable {f : ℝ × ℝ → ℝ} {fx fq x q : ℝ}
    (hf : HasStrictFDerivAt f ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fq) (x, q)) (h0 : f (x, q) = 0)
    (hfx : fx ≠ 0) :
    ∃ η : ℝ → ℝ, LocallySolvable f x q η ∧ HasDerivAt η (-(fq / fx)) q := by
  set f' := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fq
  have hx : f'.comp (ContinuousLinearMap.inl ℝ ℝ ℝ) =
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) fx := by
    ext; simp [f']
  have hq : f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) fq := by
    ext; simp [f']
  set A := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) fx
  have hAeq : A = (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 fx hfx) :
      ℝ →L[ℝ] ℝ) := by
    ext; simp [A]
  have hinv : (f'.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)).IsInvertible := by
    rw [hx, hAeq]
    exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨η, hloc, hd⟩ := theorem_M_E_1 hf h0 hinv
  refine ⟨η, hloc, ?_⟩
  have hd' := hd.hasFDerivAt.hasDerivAt
  convert hd' using 1
  rw [hx, hq, hAeq, ContinuousLinearMap.inverse_equiv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply_symm,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul]
  field_simp

/-- **Section M.E** (MWG, p. 942): the inverse function theorem as the special case
`f(x, q) = φ(x) - q` with `M = N`. If `φ` is strictly differentiable at `x̄` with invertible
derivative `φ'`, there is a local inverse `η` near `q̄ = φ(x̄)` with `φ(η(q)) = q`, unique near
`x̄`, and `Dη(q̄) = φ'⁻¹`. -/
theorem inverse_function_theorem_M_E {φ : X → X} {φ' : X →L[ℝ] X} {x : X}
    (hφ : HasStrictFDerivAt φ φ' x) (hinv : φ'.IsInvertible) :
    ∃ η : X → X, LocallySolvable (fun z : X × X => φ z.1 - z.2) x (φ x) η ∧
      HasStrictFDerivAt η φ'.inverse (φ x) := by
  have hf : HasStrictFDerivAt (fun z : X × X => φ z.1 - z.2)
      (φ'.comp (ContinuousLinearMap.fst ℝ X X) - ContinuousLinearMap.snd ℝ X X) (x, φ x) :=
    (hφ.comp (x, φ x) hasStrictFDerivAt_fst).sub hasStrictFDerivAt_snd
  have hx : (φ'.comp (ContinuousLinearMap.fst ℝ X X) - ContinuousLinearMap.snd ℝ X X).comp
      (ContinuousLinearMap.inl ℝ X X) = φ' := by
    ext v; simp
  have hq : (φ'.comp (ContinuousLinearMap.fst ℝ X X) - ContinuousLinearMap.snd ℝ X X).comp
      (ContinuousLinearMap.inr ℝ X X) = -ContinuousLinearMap.id ℝ X := by
    ext v; simp
  obtain ⟨η, hloc, hd⟩ := theorem_M_E_1 hf (by simp) (by rwa [hx])
  refine ⟨η, hloc, ?_⟩
  rw [hx, hq] at hd
  convert hd using 1
  ext v
  simp

/-- **Definition M.E.2** (MWG, p. 943). The system `f(·; q̄) = 0` is regular at `q̄` if
(M.E.2) holds at every solution: `f(x; q̄) = 0` implies that `D_x f(x; q̄)` is invertible. -/
def RegularSystemAt (f : X × Q → F) (q : Q) : Prop :=
  ∀ x, f (x, q) = 0 → ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ X Q)).IsInvertible

end MWG.ClassicalDemand
