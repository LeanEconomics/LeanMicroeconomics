/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Commodities
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field

/-!
# Homogeneous functions and Euler's formula

MWG, Mathematical Appendix, Section M.B, pp. 928–929.

Functions are defined on the nonnegative orthant `ℝ^N_+` (encoded as functions on `ℝ^N` whose
homogeneity is required only on `ℝ^N_+`). Proved:

* Definition M.B.1 and its two examples (`x₁/x₂` of degree zero, `(x₁x₂)^{1/2}` of degree
  one), and the normalisations `f(1, x₂/x₁, …) = f(x)` (degree zero) and
  `f(1, x₂/x₁, …) = f(x)/x₁` (degree one).
* Theorem M.B.1: the partial derivatives of a degree-`r` homogeneous function are homogeneous
  of degree `r - 1`. The proof holds at every point of `ℝ^N_+`, including boundary points, by
  uniqueness of derivatives within the convex orthant (which has nonempty interior). The
  example `∂(x₁x₂)^{1/2}/∂x₁ = ½(x₂/x₁)^{1/2}` is checked.
* Radial expansions of level sets are level sets; slopes of level sets are constant along rays;
  homothetic functions `h ∘ f` (with `h` strictly increasing) have the same level sets as `f`.
* Theorem M.B.2 (Euler's formula) `∇f(x̄)·x̄ = r f(x̄)`, and its degree-zero case.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- **Definition M.B.1** (MWG, p. 928). `f` is homogeneous of degree `r ∈ ℤ` on `ℝ^N_+`:
`f(tx) = t^r f(x)` for every `x ≥ 0` and `t > 0`. -/
def HomogeneousOfDegree {N : ℕ} (f : (Fin N → ℝ) → ℝ) (r : ℤ) : Prop :=
  ∀ x ∈ nonnegOrthant N, ∀ t : ℝ, 0 < t → f (t • x) = t ^ r * f x

/-- **Section M.B** (MWG, p. 928). `f(x₁, x₂) = x₁/x₂` is homogeneous of degree zero. -/
theorem example_M_B_quotient : HomogeneousOfDegree (fun x : Fin 2 → ℝ => x 0 / x 1) 0 := by
  intro x _ t ht
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, one_mul]
  rw [mul_div_mul_left _ _ ht.ne']

/-- **Section M.B** (MWG, p. 928). `f(x₁, x₂) = (x₁x₂)^{1/2}` is homogeneous of degree one. -/
theorem example_M_B_sqrt :
    HomogeneousOfDegree (fun x : Fin 2 → ℝ => Real.sqrt (x 0 * x 1)) 1 := by
  intro x hx t ht
  simp only [Pi.smul_apply, smul_eq_mul, zpow_one]
  have : t * x 0 * (t * x 1) = t ^ 2 * (x 0 * x 1) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

/-- **Section M.B** (MWG, p. 928). If `f` is homogeneous of degree zero and `x₁ > 0`, then
`f(1, x₂/x₁, …, x_N/x₁) = f(x)`. -/
theorem homogeneous_zero_normalize {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : HomogeneousOfDegree f 0) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (i : Fin N)
    (hxi : 0 < x i) : f ((x i)⁻¹ • x) = f x ∧ ((x i)⁻¹ • x) i = 1 := by
  refine ⟨?_, by simp [hxi.ne']⟩
  rw [hf x hx _ (inv_pos.mpr hxi), zpow_zero, one_mul]

/-- **Section M.B** (MWG, p. 928). If `f` is homogeneous of degree one and `x₁ > 0`, then
`f(1, x₂/x₁, …, x_N/x₁) = (1/x₁) f(x)`. -/
theorem homogeneous_one_normalize {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : HomogeneousOfDegree f 1) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (i : Fin N)
    (hxi : 0 < x i) : f ((x i)⁻¹ • x) = (x i)⁻¹ * f x := by
  rw [hf x hx _ (inv_pos.mpr hxi), zpow_one]

/-- The strictly positive orthant lies in the interior of `ℝ^N_+`, which is therefore
nonempty. -/
theorem interior_nonnegOrthant_nonempty (N : ℕ) : (interior (nonnegOrthant N)).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  have hopen : IsOpen (Set.pi Set.univ fun _ : Fin N => Set.Ioi (0 : ℝ)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  apply interior_maximal _ hopen
  · simp
  · intro y hy l
    exact (hy l (Set.mem_univ l)).le

/-- **Theorem M.B.1** (MWG, p. 928). If `f` is homogeneous of degree `r` and differentiable at
`x ∈ ℝ^N_+` and at `tx` (`t > 0`), then its derivative at `tx` is `t^{r-1}` times its derivative
at `x`; in particular every partial derivative `∂f/∂xₙ` is homogeneous of degree `r - 1`. -/
theorem theorem_M_B_1 {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin N → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x)) :
    f₂ = t ^ (r - 1) • f₁ := by
  set S := nonnegOrthant N
  have hS : UniqueDiffOn ℝ S :=
    uniqueDiffOn_convex (convex_nonnegOrthant N) (interior_nonnegOrthant_nonempty N)
  -- `y ↦ f(t y)` has derivative `t f₂` at `x`
  have hscale : HasFDerivAt (fun y : Fin N → ℝ => t • y) (t • ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).const_smul t
  have hg : HasFDerivAt (fun y => f (t • y)) (f₂.comp (t • ContinuousLinearMap.id ℝ _)) x :=
    h₂.comp x hscale
  -- `y ↦ t^r f(y)` has derivative `t^r f₁` at `x`, and agrees with `f(t ·)` on `ℝ^N_+`
  have hh : HasFDerivAt (fun y => t ^ r * f y) (t ^ r • f₁) x := h₁.const_mul _
  have hg' : HasFDerivWithinAt (fun y => t ^ r * f y)
      (f₂.comp (t • ContinuousLinearMap.id ℝ _)) S x :=
    hg.hasFDerivWithinAt.congr (fun y hy => (hf y hy t ht).symm) (hf x hx t ht).symm
  have heq := (hS x hx).eq hg' hh.hasFDerivWithinAt
  ext v
  have := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L v) heq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    map_smul, smul_eq_mul] at this
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have htr : t ^ r = t * t ^ (r - 1) := by
    rw [← zpow_one_add₀ ht.ne', add_sub_cancel]
  rw [htr] at this
  have := mul_left_cancel₀ ht.ne' (this.trans (mul_assoc _ _ _))
  exact this

/-- **Theorem M.B.1** (MWG, p. 928), partial-derivative form:
`∂f(tx)/∂xₙ = t^{r-1} ∂f(x)/∂xₙ`. -/
theorem theorem_M_B_1_partial {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ}
    (hf : HomogeneousOfDegree f r) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {t : ℝ}
    (ht : 0 < t) {f₁ f₂ : (Fin N → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x)
    (h₂ : HasFDerivAt f f₂ (t • x)) (n : Fin N) :
    f₂ (Pi.single n 1) = t ^ (r - 1) * f₁ (Pi.single n 1) := by
  rw [theorem_M_B_1 hf hx ht h₁ h₂]
  rfl

/-- **Section M.B** (MWG, p. 928), example of Theorem M.B.1: for `f = (x₁x₂)^{1/2}` at
`x ≫ 0`, `∂f/∂x₁ = ½ (x₂/x₁)^{1/2}`, which is homogeneous of degree zero. -/
theorem example_M_B_sqrt_partial {x : Fin 2 → ℝ} (h0 : 0 < x 0) (h1 : 0 < x 1) :
    HasDerivAt (fun s => Real.sqrt ((x 0 + s) * x 1)) (1 / 2 * Real.sqrt (x 1 / x 0)) 0 ∧
      ∀ t : ℝ, 0 < t → 1 / 2 * Real.sqrt (t * x 1 / (t * x 0)) =
        1 / 2 * Real.sqrt (x 1 / x 0) := by
  constructor
  · have hin : HasDerivAt (fun s => (x 0 + s) * x 1) (x 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (x 0)).mul_const (x 1)
    have hpos : (x 0 + 0) * x 1 ≠ 0 := by simp only [add_zero]; positivity
    convert hin.sqrt hpos using 1
    simp only [add_zero]
    rw [Real.sqrt_mul h0.le, Real.sqrt_div h1.le]
    have hs0 := Real.sqrt_pos.mpr h0
    have hs1 := Real.sqrt_pos.mpr h1
    field_simp
    rw [Real.sq_sqrt h1.le]
  · intro t ht
    rw [mul_div_mul_left _ _ ht.ne']

/-- **Section M.B** (MWG, p. 928). A radial expansion of a level set of a homogeneous function
is a level set: `f(x) = f(x')` implies `f(tx) = f(tx')` for `t > 0`. -/
theorem level_set_radial {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x x' : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (hx' : x' ∈ nonnegOrthant N) {t : ℝ}
    (ht : 0 < t) (h : f x = f x') : f (t • x) = f (t • x') := by
  rw [hf x hx t ht, hf x' hx' t ht, h]

/-- **Section M.B** (MWG, pp. 928–929, Figure M.B.1). For `N = 2`, the slope
`-(∂f/∂x₁)/(∂f/∂x₂)` of the level set of a homogeneous function is the same at `x̄` and at
`tx̄`. -/
theorem level_set_slope_radial {f : (Fin 2 → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin 2 → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x)) :
    f₂ (Pi.single 0 1) / f₂ (Pi.single 1 1) = f₁ (Pi.single 0 1) / f₁ (Pi.single 1 1) := by
  rw [theorem_M_B_1_partial hf hx ht h₁ h₂, theorem_M_B_1_partial hf hx ht h₁ h₂]
  have : t ^ (r - 1) ≠ 0 := zpow_ne_zero _ ht.ne'
  rw [mul_div_mul_left _ _ this]

/-- **Section M.B** (MWG, p. 929). For a homothetic function `h ∘ f` with `h` strictly
increasing, the level sets of `h ∘ f` coincide with those of `f`. -/
theorem homothetic_level_sets {N : ℕ} {f : (Fin N → ℝ) → ℝ} {h : ℝ → ℝ} (hh : StrictMono h)
    (x : Fin N → ℝ) : {y | h (f y) = h (f x)} = {y | f y = f x} := by
  ext y
  exact hh.injective.eq_iff

/-- **Section M.B** (MWG, p. 929). For a homothetic function `h ∘ f` (`f` homogeneous, `h`
with nonzero derivative), the level-set slopes are also unchanged along rays. -/
theorem homothetic_slope_radial {f : (Fin 2 → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {h : ℝ → ℝ} {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin 2 → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x))
    {a b : ℝ} (ha : HasDerivAt h a (f x)) (hb : HasDerivAt h b (f (t • x))) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    HasFDerivAt (h ∘ f) (a • f₁) x ∧ HasFDerivAt (h ∘ f) (b • f₂) (t • x) ∧
      (b • f₂) (Pi.single 0 1) / (b • f₂) (Pi.single 1 1) =
        (a • f₁) (Pi.single 0 1) / (a • f₁) (Pi.single 1 1) := by
  refine ⟨ha.comp_hasFDerivAt x h₁, hb.comp_hasFDerivAt (t • x) h₂, ?_⟩
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hb0, mul_div_mul_left _ _ ha0]
  exact level_set_slope_radial hf hx ht h₁ h₂

/-- **Theorem M.B.2** (MWG, p. 929), Euler's formula. If `f` is homogeneous of degree `r` and
differentiable at `x̄ ∈ ℝ^N_+` with derivative `f'`, then `∑ₙ (∂f(x̄)/∂xₙ) x̄ₙ = r f(x̄)`, i.e.
`∇f(x̄)·x̄ = r f(x̄)`. -/
theorem theorem_M_B_2 {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    (h : HasFDerivAt f f' x) : f' x = r * f x := by
  have hγ : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hc := h.comp_hasDerivAt_of_eq (1 : ℝ) hγ (one_smul ℝ x).symm
  have hz : HasDerivAt (fun t : ℝ => t ^ r * f x) ((r : ℝ) * 1 ^ (r - 1) * f x) 1 :=
    (hasDerivAt_zpow r 1 (Or.inl one_ne_zero)).mul_const (f x)
  have hev : (fun t : ℝ => t ^ r * f x) =ᶠ[𝓝 1] (f ∘ fun t : ℝ => t • x) := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact (hf x hx t ht).symm
  have := hc.unique (hz.congr_of_eventuallyEq hev.symm)
  rw [this, one_zpow, mul_one]

/-- **Section M.B** (MWG, p. 929). For a function homogeneous of degree zero, Euler's formula
reads `∑ₙ (∂f(x)/∂xₙ) xₙ = 0`. -/
theorem euler_degree_zero {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : HomogeneousOfDegree f 0)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    (h : HasFDerivAt f f' x) : f' x = 0 := by
  rw [theorem_M_B_2 hf hx h]
  simp

end MWG.ConsumerChoice
