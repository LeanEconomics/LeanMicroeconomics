/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix notation for derivatives

MWG, Mathematical Appendix, Section M.A, pp. 926–927.

Vectors of `ℝ^N` are columns (`Fin N → ℝ`); the inner product is `x·y = ∑ xₙyₙ = xᵀy`, and
`x·A` means `xᵀA`. For a differentiable `f : ℝ^N → ℝ^M` the derivative at `x` is a continuous
linear map `f'`; its matrix `Df(x)` has `mn` entry `∂fₘ/∂xₙ` (`jacobian`). For `M = 1` the
gradient is `∇f(x) = [Df(x)]ᵀ`. Partial derivative matrices `D_x f(x, y)` restrict the
derivative to the `x`-variables. The Hessian is the derivative matrix of the gradient.

Proved: the chain rule (M.A.1) in matrix form, and the product rules (M.A.2)–(M.A.5), including
that (M.A.4) is a special case of (M.A.5) and that `g(x) Dh(x)` has rank at most one.
-/

namespace MWG.ConsumerChoice

/-- **Section M.A** (MWG, p. 926). The inner product is `x·y = xᵀy`, the single entry of the
`1 × 1` matrix `xᵀ y`. -/
theorem dotProduct_eq_transpose_mul {N : ℕ} (x y : Fin N → ℝ) :
    x ⬝ᵥ y =
      (Matrix.transpose (Matrix.replicateCol Unit x) * Matrix.replicateCol Unit y) () () := by
  simp [Matrix.mul_apply, dotProduct]

/-- **Section M.A** (MWG, p. 926). `x·A` is `xᵀA`. -/
theorem vecMul_eq_transpose_mul {N M : ℕ} (x : Fin N → ℝ) (A : Matrix (Fin N) (Fin M) ℝ) :
    Matrix.vecMul x A = fun m => (Matrix.transpose (Matrix.replicateCol Unit x) * A) () m := by
  funext m
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- **Section M.A** (MWG, p. 926). The derivative matrix `Df(x)` of a linear map `f'`: the
`mn` entry is `∂fₘ/∂xₙ = f'(eₙ)ₘ`. -/
def jacobian {N M : ℕ} (f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)) : Matrix (Fin M) (Fin N) ℝ :=
  Matrix.of fun m n => f' (Pi.single n 1) m

/-- The derivative acts on a direction by multiplication with its matrix:
`f'(v) = Df(x) v`. -/
theorem jacobian_mulVec {N M : ℕ} (f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)) (v : Fin N → ℝ) :
    Matrix.mulVec (jacobian f') v = f' v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  funext m
  simp only [map_sum, Finset.sum_apply, jacobian, Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : Pi.single n (v n) = v n • (Pi.single n (1 : ℝ) : Fin N → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Section M.A** (MWG, pp. 926–927). The gradient `∇f(x) ∈ ℝ^N` of a real-valued function,
the vector of partial derivatives `∂f/∂xₙ = f'(eₙ)`. -/
def gradientVec {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) : Fin N → ℝ := fun n => f' (Pi.single n 1)

/-- **Section M.A** (MWG, p. 927). For `M = 1`, `∇f(x) = [Df(x)]ᵀ`: the `1 × N` derivative
matrix of `x ↦ (f x)` is the transpose of the gradient column. -/
theorem gradient_eq_transpose_jacobian {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) :
    Matrix.replicateCol (Fin 1) (gradientVec f') =
      Matrix.transpose (jacobian (ContinuousLinearMap.pi fun _ : Fin 1 => f')) := by
  ext n u
  simp [gradientVec, jacobian]

/-- The gradient represents the derivative: `f'(v) = ∇f(x)·v`. -/
theorem fderiv_apply_eq_gradient_dot {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    f' v = gradientVec f' ⬝ᵥ v := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum, gradientVec, dotProduct]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : Pi.single n (v n) = v n • (Pi.single n (1 : ℝ) : Fin N → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- **Section M.A** (MWG, p. 927). For `f : ℝ^{N+K} → ℝ^M`, the partial derivative matrix
`D_x f(x, y)`: the `M × N` matrix of `∂fₘ/∂xₙ`. -/
def partialJacobianFst {N K M : ℕ} (f' : ((Fin N → ℝ) × (Fin K → ℝ)) →L[ℝ] (Fin M → ℝ)) :
    Matrix (Fin M) (Fin N) ℝ :=
  jacobian (f'.comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin K → ℝ)))

/-- `D_x f(x, y)` has `mn` entry `∂fₘ(x, y)/∂xₙ`: the derivative in direction `(eₙ, 0)`. -/
theorem partialJacobianFst_apply {N K M : ℕ}
    (f' : ((Fin N → ℝ) × (Fin K → ℝ)) →L[ℝ] (Fin M → ℝ)) (m : Fin M) (n : Fin N) :
    partialJacobianFst f' m n = f' (Pi.single n 1, 0) m := rfl

/-- **Section M.A** (MWG, p. 927). The Hessian `D²f(x) = D[∇f(x)]`: the derivative matrix of the
gradient map `y ↦ ∇f(y)`. -/
noncomputable def hessianMatrix {N : ℕ} (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  jacobian (fderiv ℝ (fun y => gradientVec (fderiv ℝ f y)) x)

/-- **Equation (M.A.1)** (MWG, p. 927), the chain rule: if `g : ℝ^S → ℝ^N` is differentiable at
`x` and `f : ℝ^N → ℝ^M` at `g(x)`, then `f ∘ g` is differentiable at `x` and
`D_x f(g(x)) = Df(g(x)) Dg(x)`. -/
theorem equation_M_A_1 {S N M : ℕ} {g : (Fin S → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → (Fin M → ℝ)} {x : Fin S → ℝ} {g' : (Fin S → ℝ) →L[ℝ] (Fin N → ℝ)}
    {f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)} (hg : HasFDerivAt g g' x) (hf : HasFDerivAt f f' (g x)) :
    HasFDerivAt (f ∘ g) (f'.comp g') x ∧ jacobian (f'.comp g') = jacobian f' * jacobian g' := by
  refine ⟨hf.comp x hg, ?_⟩
  ext m s
  rw [Matrix.mul_apply]
  have := congrFun (jacobian_mulVec f' (g' (Pi.single s 1))) m
  simp only [jacobian, Matrix.of_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
    at this ⊢
  rw [← this]
  simp [Matrix.mulVec, dotProduct]

/-- **Equation (M.A.2)** (MWG, p. 927), the product rule for `f = g h` with `g, h : ℝ^N → ℝ`:
`Df(x) = g(x) Dh(x) + h(x) Dg(x)`, equivalently `∇f(x) = g(x)∇h(x) + h(x)∇g(x)`. -/
theorem equation_M_A_2 {N : ℕ} {g h : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {g' h' : (Fin N → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g g' x) (hh : HasFDerivAt h h' x) :
    HasFDerivAt (fun y => g y * h y) (g x • h' + h x • g') x ∧
      gradientVec (g x • h' + h x • g') = g x • gradientVec h' + h x • gradientVec g' := by
  refine ⟨hg.fun_mul hh, ?_⟩
  funext n
  simp [gradientVec]

/-- **Equation (M.A.3)** (MWG, p. 927), the product rule for the inner product `f = g·h` of
`g, h : ℝ^N → ℝ^M`: `Df(x) = g(x)·Dh(x) + h(x)·Dg(x)`, where `h(x)·Dg(x) = [h(x)]ᵀDg(x)`. -/
theorem equation_M_A_3 {N M : ℕ} {g h : (Fin N → ℝ) → (Fin M → ℝ)} {x : Fin N → ℝ}
    {g' h' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)} (hg : HasFDerivAt g g' x)
    (hh : HasFDerivAt h h' x) :
    ∃ f' : (Fin N → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun y => g y ⬝ᵥ h y) f' x ∧
      gradientVec f' = Matrix.vecMul (g x) (jacobian h') + Matrix.vecMul (h x) (jacobian g') := by
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin M)),
      HasFDerivAt (fun y => g y m * h y m)
        (g x m • (ContinuousLinearMap.proj m).comp h' +
          h x m • (ContinuousLinearMap.proj m).comp g') x := by
    intro m _
    exact (hasFDerivAt_pi'.mp hg m).fun_mul (hasFDerivAt_pi'.mp hh m)
  refine ⟨_, HasFDerivAt.fun_sum hterm, ?_⟩
  funext n
  simp [gradientVec, Matrix.vecMul, dotProduct, jacobian, Finset.sum_add_distrib]

/-- **Equation (M.A.5)** (MWG, p. 927), the product rule for `f = h g` with `h : ℝ^N → ℝ` and
`g : ℝ^N → ℝ^M`: `Df(x) = h(x) Dg(x) + g(x) Dh(x)`, where `g(x) Dh(x)` is the `M × N` outer
product. -/
theorem equation_M_A_5 {N M : ℕ} {h : (Fin N → ℝ) → ℝ} {g : (Fin N → ℝ) → (Fin M → ℝ)}
    {x : Fin N → ℝ} {h' : (Fin N → ℝ) →L[ℝ] ℝ} {g' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)}
    (hh : HasFDerivAt h h' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => h y • g y) (h x • g' + h'.smulRight (g x)) x ∧
      jacobian (h x • g' + h'.smulRight (g x)) =
        h x • jacobian g' + Matrix.vecMulVec (g x) (gradientVec h') := by
  refine ⟨hh.fun_smul hg, ?_⟩
  ext m n
  simp [jacobian, gradientVec, Matrix.vecMulVec, mul_comm]

/-- **Section M.A** (MWG, p. 927). The outer product `g(x) Dh(x)` has rank at most one. -/
theorem rank_vecMulVec_le_one {N M : ℕ} (a : Fin M → ℝ) (b : Fin N → ℝ) :
    Matrix.rank (Matrix.vecMulVec a b) ≤ 1 := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- **Equation (M.A.4)** (MWG, p. 927), the product rule for `f = α g` with `α : ℝ → ℝ` and
`g : ℝ → ℝ^M`: `Df(x) = α(x) Dg(x) + α'(x) g(x)`. It is the special case `N = 1` of (M.A.5). -/
theorem equation_M_A_4 {M : ℕ} {α : ℝ → ℝ} {g : ℝ → (Fin M → ℝ)} {x α' : ℝ}
    {g' : Fin M → ℝ} (hα : HasDerivAt α α' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => α y • g y) (α x • g' + α' • g x) x :=
  hα.smul hg

end MWG.ConsumerChoice
