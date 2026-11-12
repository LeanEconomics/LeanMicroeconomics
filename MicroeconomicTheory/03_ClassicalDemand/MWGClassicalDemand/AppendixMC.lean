/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Module

/-!
# Mathematical Appendix M.C: concave and quasiconcave functions

MWG, Section M.C, pp. 930-935. Functions are `f : ℝ^N → ℝ` (`Fin N → ℝ`), studied on a convex
domain `A`; the gradient `∇f(x)` is the derivative `f' x : (Fin N → ℝ) →L[ℝ] ℝ`, so that
`∇f(x)·z = f' x z`.

* Definition M.C.1 is Mathlib's `ConcaveOn`/`StrictConcaveOn` (bridges `definition_M_C_1`,
  `definition_M_C_1_strict`); (M.C.2) is finite Jensen; convexity is concavity of `-f`.
* Theorem M.C.1: concavity is the gradient inequality `f(x + z) ≤ f(x) + ∇f(x)·z` (both
  directions; the strict inequality gives strict concavity), with the convex analogue.
  Only differentiability at the points of `A` is used (the book assumes `C¹`).
* Definition M.C.3: quasiconcavity is Mathlib's `QuasiconcaveOn`; strict quasiconcavity and
  quasiconvexity are defined here; (M.C.7) is the minimum form.
* Theorem M.C.3: all three assertions, including sufficiency of (M.C.8) (the book proves only
  necessity), the strict sufficiency, and the strict necessity under `∇f ≠ 0` on an open `A`;
  the cube `x³` shows the gradient condition cannot be dropped.
* Remarks: concave functions are quasiconcave, an increasing function is quasiconcave but need
  not be concave, quasiconcavity (unlike concavity) survives increasing transformations,
  `-x⁴` is strictly concave with zero second derivative at `0` (p. 933).
-/

namespace MWG.ClassicalDemand

variable {N : ℕ}

/-- The derivative of `f` along the line `t ↦ x + t z` at `t = 0` is `∇f(x)·z`. -/
theorem mc_line_hasDerivAt {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {x : Fin N → ℝ} (hf : HasFDerivAt f f' x) (z : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • z)) (f' z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have hf' : HasFDerivAt f f' (x + (0 : ℝ) • z) := by simpa using hf
  exact hf'.comp_hasDerivAt (0 : ℝ) h1

/-- The derivative along the line through `x` at any parameter `t`. -/
theorem mc_line_hasDerivAt_at {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {x z : Fin N → ℝ} {t : ℝ} (hf : HasFDerivAt f f' (x + t • z)) :
    HasDerivAt (fun s : ℝ => f (x + s • z)) (f' z) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  exact hf.comp_hasDerivAt t h1

/-- A lower bound on all slopes over `(0, 1]` bounds the right derivative at `0`. -/
theorem mc_le_deriv_of_slope {g : ℝ → ℝ} {d c : ℝ} (hg : HasDerivAt g d 0)
    (h : ∀ t : ℝ, 0 < t → t < 1 → c ≤ (g t - g 0) / t) : c ≤ d := by
  apply ge_of_tendsto hg.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
  rw [zero_add, smul_eq_mul, inv_mul_eq_div]
  exact h t ht.1 ht.2

/-- **Definition M.C.1** (MWG, p. 930). `f` is concave on the convex set `A` iff
`f(αx' + (1-α)x) ≥ αf(x') + (1-α)f(x)` for `x, x' ∈ A`, `α ∈ [0, 1]` (Mathlib's `ConcaveOn`). -/
theorem definition_M_C_1 {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) (f : (Fin N → ℝ) → ℝ) :
    ConcaveOn ℝ A f ↔ ∀ x ∈ A, ∀ x' ∈ A, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α * f x' + (1 - α) * f x ≤ f (α • x' + (1 - α) • x) := by
  constructor
  · intro h x hx x' hx' α h0 h1
    exact h.2 hx' hx h0 (by linarith) (by ring)
  · intro h
    refine ⟨hA, fun x' hx' x hx a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    exact h x hx x' hx' a ha (by linarith)

/-- **Definition M.C.1** (MWG, p. 930), strict concavity: strict inequality for `x' ≠ x` and
`α ∈ (0, 1)` (Mathlib's `StrictConcaveOn`). -/
theorem definition_M_C_1_strict {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    (f : (Fin N → ℝ) → ℝ) :
    StrictConcaveOn ℝ A f ↔ ∀ x ∈ A, ∀ x' ∈ A, x' ≠ x → ∀ α : ℝ, 0 < α → α < 1 →
      α * f x' + (1 - α) * f x < f (α • x' + (1 - α) • x) := by
  constructor
  · intro h x hx x' hx' hne α h0 h1
    exact h.2 hx' hx hne h0 (by linarith) (by ring)
  · intro h
    refine ⟨hA, fun x' hx' x hx hne a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    exact h x hx x' hx' hne a ha (by linarith)

/-- **Equation (M.C.2)** (MWG, p. 931). A concave function satisfies the finite Jensen
inequality `f(∑ αₖ xᵏ) ≥ ∑ αₖ f(xᵏ)` for weights `αₖ ≥ 0` summing to one. -/
theorem equation_M_C_2 {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} (hf : ConcaveOn ℝ A f)
    {K : ℕ} (α : Fin K → ℝ) (xs : Fin K → Fin N → ℝ) (h0 : ∀ k, 0 ≤ α k)
    (h1 : ∑ k, α k = 1) (hmem : ∀ k, xs k ∈ A) :
    ∑ k, α k * f (xs k) ≤ f (∑ k, α k • xs k) :=
  hf.le_map_sum (fun k _ => h0 k) h1 (fun k _ => hmem k)

/-- **Section M.C** (MWG, p. 931). `f` is concave if and only if `-f` is convex. -/
theorem concaveOn_iff_neg_convexOn {A : Set (Fin N → ℝ)} (f : (Fin N → ℝ) → ℝ) :
    ConcaveOn ℝ A f ↔ ConvexOn ℝ A (-f) := neg_convexOn_iff.symm

/-- **Theorem M.C.1** (MWG, p. 931), necessity. If `f` is concave on `A` and differentiable at
the points of `A`, then `f(x + z) ≤ f(x) + ∇f(x)·z` whenever `x, x + z ∈ A`. -/
theorem theorem_M_C_1_necessity {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ} (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x)
    (hc : ConcaveOn ℝ A f) {x z : Fin N → ℝ} (hx : x ∈ A) (hxz : x + z ∈ A) :
    f (x + z) ≤ f x + f' x z := by
  have hd := mc_line_hasDerivAt (hf x hx) z
  have key : f (x + z) - f x ≤ f' x z := by
    apply mc_le_deriv_of_slope hd
    intro t ht0 ht1
    have hconc := hc.2 hxz hx ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    have heq : t • (x + z) + (1 - t) • x = x + t • z := by module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconc
    simp only [zero_smul, add_zero]
    rw [le_div_iff₀ ht0]
    linarith
  linarith

/-- **Theorem M.C.1** (MWG, p. 931), sufficiency (not proved in the book). On a convex set,
the gradient inequality at every point implies concavity. -/
theorem theorem_M_C_1_sufficiency {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (h : ∀ x ∈ A, ∀ z, x + z ∈ A → f (x + z) ≤ f x + f' x z) : ConcaveOn ℝ A f := by
  refine ⟨hA, fun x hx y hy a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  set m := a • x + (1 - a) • y with hm
  have hmA : m ∈ A := hA hx hy ha hb (by ring)
  have h1 := h m hmA (x - m) (by simpa using hx)
  have h2 := h m hmA (y - m) (by simpa using hy)
  simp only [add_sub_cancel] at h1 h2
  have hzero : a • (x - m) + (1 - a) • (y - m) = 0 := by rw [hm]; module
  have hlin : a * f' m (x - m) + (1 - a) * f' m (y - m) = 0 := by
    have := congrArg (f' m) hzero
    simpa [map_add, map_smul] using this
  simp only [smul_eq_mul]
  nlinarith

/-- **Theorem M.C.1** (MWG, p. 931), strict part. If the gradient inequality is strict for
every `z ≠ 0`, then `f` is strictly concave. -/
theorem theorem_M_C_1_strict {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (h : ∀ x ∈ A, ∀ z, z ≠ 0 → x + z ∈ A → f (x + z) < f x + f' x z) :
    StrictConcaveOn ℝ A f := by
  refine ⟨hA, fun x hx y hy hxy a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  set m := a • x + (1 - a) • y with hm
  have hmA : m ∈ A := hA hx hy ha.le hb.le (by ring)
  have hxm : x - m = (1 - a) • (x - y) := by rw [hm]; module
  have hym : y - m = a • (y - x) := by rw [hm]; module
  have hne1 : x - m ≠ 0 := by
    rw [hxm]
    exact smul_ne_zero hb.ne' (sub_ne_zero.mpr hxy)
  have hne2 : y - m ≠ 0 := by
    rw [hym]
    exact smul_ne_zero ha.ne' (sub_ne_zero.mpr hxy.symm)
  have h1 := h m hmA (x - m) hne1 (by simpa using hx)
  have h2 := h m hmA (y - m) hne2 (by simpa using hy)
  simp only [add_sub_cancel] at h1 h2
  have hzero : a • (x - m) + (1 - a) • (y - m) = 0 := by rw [hm]; module
  have hlin : a * f' m (x - m) + (1 - a) * f' m (y - m) = 0 := by
    have := congrArg (f' m) hzero
    simpa [map_add, map_smul] using this
  simp only [smul_eq_mul]
  nlinarith

/-- **Theorem M.C.1** (MWG, p. 931). For `f` differentiable at the points of the convex set
`A`, `f` is concave if and only if `f(x + z) ≤ f(x) + ∇f(x)·z` for all `x, x + z ∈ A`. -/
theorem theorem_M_C_1 {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) {f : (Fin N → ℝ) → ℝ}
    {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ} (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x) :
    ConcaveOn ℝ A f ↔ ∀ x ∈ A, ∀ z, x + z ∈ A → f (x + z) ≤ f x + f' x z :=
  ⟨fun hc _ hx _ hxz => theorem_M_C_1_necessity hf hc hx hxz, theorem_M_C_1_sufficiency hA⟩

/-- **Theorem M.C.1** for convex functions (MWG, p. 932): `f` is convex iff
`f(x + z) ≥ f(x) + ∇f(x)·z` for all `x, x + z ∈ A`. -/
theorem theorem_M_C_1_convex {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) {f : (Fin N → ℝ) → ℝ}
    {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ} (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x) :
    ConvexOn ℝ A f ↔ ∀ x ∈ A, ∀ z, x + z ∈ A → f x + f' x z ≤ f (x + z) := by
  have hneg : ∀ x ∈ A, HasFDerivAt (-f) (-f' x) x := fun x hx => (hf x hx).neg
  rw [← neg_concaveOn_iff, theorem_M_C_1 hA hneg]
  constructor
  · intro h x hx z hxz
    have := h x hx z hxz
    simp only [Pi.neg_apply, neg_apply] at this
    linarith
  · intro h x hx z hxz
    have := h x hx z hxz
    simp only [Pi.neg_apply, neg_apply]
    linarith

/-- **Definition M.C.3** (MWG, p. 933). On a convex set, quasiconcavity (Mathlib's
`QuasiconcaveOn`: convex upper contour sets) is condition (M.C.6). -/
theorem definition_M_C_3 {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) (f : (Fin N → ℝ) → ℝ) :
    QuasiconcaveOn ℝ A f ↔ ∀ t : ℝ, ∀ x ∈ A, ∀ x' ∈ A, t ≤ f x → t ≤ f x' →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → t ≤ f (α • x + (1 - α) • x') := by
  constructor
  · intro h t x hx x' hx' htx htx' α h0 h1
    exact (h t ⟨hx, htx⟩ ⟨hx', htx'⟩ h0 (by linarith) (by ring)).2
  · intro h t x hx x' hx' a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    exact ⟨hA hx.1 hx'.1 ha hb (by ring), h t x hx.1 x' hx'.1 hx.2 hx'.2 a ha (by linarith)⟩

/-- **Definition M.C.3** (MWG, p. 933). `f` is strictly quasiconcave on the convex set `A` if
the concluding inequality of (M.C.6) is strict whenever `x ≠ x'` and `α ∈ (0, 1)`. -/
def StrictlyQuasiconcaveOn (A : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) : Prop :=
  Convex ℝ A ∧ ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ∀ α : ℝ, 0 < α → α < 1 → ∀ t : ℝ,
    t ≤ f x → t ≤ f x' → t < f (α • x + (1 - α) • x')

/-- **Definition M.C.3** (MWG, p. 933). `f` is strictly quasiconvex on `A` if `f(x) ≤ t` and
`f(x') ≤ t` imply `f(αx + (1-α)x') < t` for `x ≠ x'` and `α ∈ (0, 1)`. -/
def StrictlyQuasiconvexOn (A : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) : Prop :=
  Convex ℝ A ∧ ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ∀ α : ℝ, 0 < α → α < 1 → ∀ t : ℝ,
    f x ≤ t → f x' ≤ t → f (α • x + (1 - α) • x') < t

/-- Strict quasiconcavity in minimum form: `f(αx + (1-α)x') > min {f(x), f(x')}`. -/
theorem strictlyQuasiconcaveOn_iff_min {A : Set (Fin N → ℝ)} (f : (Fin N → ℝ) → ℝ) :
    StrictlyQuasiconcaveOn A f ↔ Convex ℝ A ∧ ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ∀ α : ℝ,
      0 < α → α < 1 → min (f x) (f x') < f (α • x + (1 - α) • x') := by
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun x hx x' hx' hne α h0 h1 =>
      h x hx x' hx' hne α h0 h1 _ (min_le_left _ _) (min_le_right _ _)⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun x hx x' hx' hne α h0 h1 t ht ht' =>
      (le_min ht ht').trans_lt (h x hx x' hx' hne α h0 h1)⟩

/-- **Section M.C** (MWG, p. 933). `f` is quasiconcave iff `-f` is quasiconvex. -/
theorem quasiconcaveOn_iff_neg_quasiconvexOn {A : Set (Fin N → ℝ)} (f : (Fin N → ℝ) → ℝ) :
    QuasiconcaveOn ℝ A f ↔ QuasiconvexOn ℝ A (-f) := by
  constructor
  · intro h r
    have := h (-r)
    convert this using 2
    simp only [Pi.neg_apply, neg_le]
  · intro h r
    have := h (-r)
    convert this using 2
    simp only [Pi.neg_apply, neg_le_neg_iff]

/-- **Section M.C** (MWG, p. 933). `f` is strictly quasiconcave iff `-f` is strictly
quasiconvex. -/
theorem strictlyQuasiconcaveOn_iff_neg {A : Set (Fin N → ℝ)} (f : (Fin N → ℝ) → ℝ) :
    StrictlyQuasiconcaveOn A f ↔ StrictlyQuasiconvexOn A (-f) := by
  constructor
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun x hx x' hx' hne α h0 h1 t ht ht' => ?_⟩
    simp only [Pi.neg_apply] at *
    have := h x hx x' hx' hne α h0 h1 (-t) (by linarith) (by linarith)
    linarith
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun x hx x' hx' hne α h0 h1 t ht ht' => ?_⟩
    have := h x hx x' hx' hne α h0 h1 (-t) (by simp; linarith) (by simp; linarith)
    simp only [Pi.neg_apply] at this
    linarith

/-- **Equation (M.C.7)** (MWG, p. 934). On a convex set, `f` is quasiconcave iff
`f(αx + (1-α)x') ≥ min {f(x), f(x')}`. -/
theorem equation_M_C_7 {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) (f : (Fin N → ℝ) → ℝ) :
    QuasiconcaveOn ℝ A f ↔ ∀ x ∈ A, ∀ x' ∈ A, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      min (f x) (f x') ≤ f (α • x + (1 - α) • x') := by
  rw [definition_M_C_3 hA]
  constructor
  · intro h x hx x' hx' α h0 h1
    exact h _ x hx x' hx' (min_le_left _ _) (min_le_right _ _) α h0 h1
  · intro h t x hx x' hx' ht ht' α h0 h1
    exact (le_min ht ht').trans (h x hx x' hx' α h0 h1)

/-- **Section M.C** (MWG, p. 934). A concave function is quasiconcave. -/
theorem quasiconcaveOn_of_concaveOn {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hf : ConcaveOn ℝ A f) : QuasiconcaveOn ℝ A f := hf.quasiconcaveOn

/-- **Section M.C** (MWG, p. 934). The converse fails: the increasing function `x³` of one
variable is quasiconcave but not concave. -/
theorem quasiconcave_not_concave_cube :
    QuasiconcaveOn ℝ Set.univ (fun x : ℝ => x ^ 3) ∧
      ¬ ConcaveOn ℝ Set.univ (fun x : ℝ => x ^ 3) := by
  refine ⟨(Odd.strictMono_pow (by decide : Odd 3)).monotone.quasiconcaveOn, fun h => ?_⟩
  have := h.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (2 : ℝ)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  norm_num at this

/-- **Section M.C** (MWG, p. 934). Quasiconcavity is preserved by increasing transformations. -/
theorem quasiconcaveOn_monotone_comp {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    {g : ℝ → ℝ} (hg : Monotone g) (hf : QuasiconcaveOn ℝ A f) :
    QuasiconcaveOn ℝ A (g ∘ f) := hf.monotone_comp hg

/-- **Section M.C** (MWG, p. 934). Concavity is not preserved: `x ↦ x` is concave on `ℝ` but
its increasing transformation `x ↦ x³` is not. -/
theorem concave_not_preserved :
    ConcaveOn ℝ Set.univ (fun x : ℝ => x) ∧ Monotone (fun x : ℝ => x ^ 3) ∧
      ¬ ConcaveOn ℝ Set.univ ((fun x : ℝ => x ^ 3) ∘ fun x : ℝ => x) :=
  ⟨concaveOn_id convex_univ, (Odd.strictMono_pow (by decide : Odd 3)).monotone,
    quasiconcave_not_concave_cube.2⟩

/-- **Section M.C** (MWG, p. 933). `f(x) = -x⁴` is strictly concave, yet its second derivative
vanishes at `0`: negative definiteness of `D²f` is sufficient but not necessary for strict
concavity. -/
theorem neg_pow_four_strictConcave :
    StrictConcaveOn ℝ Set.univ (fun x : ℝ => -x ^ 4) ∧
      deriv (deriv (fun x : ℝ => -x ^ 4)) 0 = 0 := by
  refine ⟨(Even.strictConvexOn_pow (by decide : Even 4) (by norm_num)).neg, ?_⟩
  have h1 : deriv (fun x : ℝ => -x ^ 4) = fun x => -(4 * x ^ 3) := by
    ext x
    simp
  rw [h1]
  simp

/-- The line restriction of `f` to the segment from `x` towards `x'`. -/
theorem mc_segment_point (x x' : Fin N → ℝ) (t : ℝ) :
    x + t • (x' - x) = t • x' + (1 - t) • x := by module

/-- **Theorem M.C.3** (MWG, p. 934), necessity. If `f` is quasiconcave on `A` and
differentiable at `x ∈ A`, then `∇f(x)·(x' - x) ≥ 0` whenever `x' ∈ A` and `f(x') ≥ f(x)`. -/
theorem theorem_M_C_3_necessity {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    {f' : (Fin N → ℝ) →L[ℝ] ℝ} (hq : QuasiconcaveOn ℝ A f) {x x' : Fin N → ℝ}
    (hx : x ∈ A) (hx' : x' ∈ A) (hf : HasFDerivAt f f' x) (hle : f x ≤ f x') :
    0 ≤ f' (x' - x) := by
  have hd := mc_line_hasDerivAt hf (x' - x)
  apply mc_le_deriv_of_slope hd
  intro t ht0 ht1
  have hmem := hq (f x) ⟨hx', hle⟩ ⟨hx, le_rfl⟩ ht0.le (by linarith : (0 : ℝ) ≤ 1 - t)
    (by ring)
  rw [← mc_segment_point] at hmem
  simp only [zero_smul, add_zero]
  exact div_nonneg (by linarith [hmem.2]) ht0.le

/-- **Theorem M.C.3** (MWG, p. 934), sufficiency (not proved in the book). If `f` is
differentiable on the convex set `A` and `∇f(x)·(x' - x) ≥ 0` whenever `x, x' ∈ A` and
`f(x') ≥ f(x)`, then `f` is quasiconcave. -/
theorem theorem_M_C_3_sufficiency {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x)
    (h : ∀ x ∈ A, ∀ x' ∈ A, f x ≤ f x' → 0 ≤ f' x (x' - x)) : QuasiconcaveOn ℝ A f := by
  rw [equation_M_C_7 hA]
  intro x hx x' hx' α h0 h1
  -- WLOG `f x' ≤ f x`; reduce to the segment from `y` (the worse endpoint) to `y'`.
  have main : ∀ y ∈ A, ∀ y' ∈ A, f y ≤ f y' → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      f y ≤ f (y + s • (y' - y)) := by
    intro y hy y' hy' hyy' s hs0 hs1
    set φ : ℝ → ℝ := fun t => f (y + t • (y' - y)) with hφ
    have hmemt : ∀ t ∈ Set.Icc (0 : ℝ) 1, y + t • (y' - y) ∈ A := by
      intro t ht
      rw [mc_segment_point]
      exact hA hy' hy ht.1 (by linarith [ht.2]) (by ring)
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (f' (y + t • (y' - y)) (y' - y)) t :=
      fun t ht => mc_line_hasDerivAt_at (hf _ (hmemt t ht))
    have hcont : ContinuousOn φ (Set.Icc 0 1) :=
      fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    have hφ0 : φ 0 = f y := by simp [hφ]
    by_contra hlt
    push Not at hlt
    -- the last time before `s` at which `φ ≥ f y`
    set S := {t ∈ Set.Icc (0 : ℝ) s | f y ≤ φ t} with hS
    have hSne : S.Nonempty := ⟨0, ⟨le_rfl, hs0⟩, hφ0.ge⟩
    have hSbdd : BddAbove S := ⟨s, fun t ht => ht.1.2⟩
    set a := sSup S with ha
    have haS : a ∈ S := by
      have hclosed : IsClosed S := by
        have : S = Set.Icc 0 s ∩ φ ⁻¹' Set.Ici (f y) := rfl
        rw [this]
        exact (hcont.mono (Set.Icc_subset_Icc le_rfl hs1)).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_Ici
      exact hclosed.csSup_mem hSne hSbdd
    have has : a < s := by
      rcases haS.1.2.lt_or_eq with h | h
      · exact h
      · exfalso
        have := haS.2
        rw [h] at this
        exact absurd this (not_le.mpr hlt)
    have hlow : ∀ t ∈ Set.Ioc a s, φ t < f y := by
      intro t ht
      by_contra hge
      push Not at hge
      have : t ≤ a := le_csSup hSbdd ⟨⟨haS.1.1.trans ht.1.le, ht.2⟩, hge⟩
      linarith [ht.1]
    -- on `(a, s]`, both comparisons force `φ' = 0`
    have hzero : ∀ t ∈ Set.Ioo a s, HasDerivAt φ 0 t := by
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨haS.1.1.trans ht.1.le, ht.2.le.trans hs1⟩
      have hpt := hmemt t htI
      have hd := hderiv t htI
      have hlt' := hlow t ⟨ht.1, ht.2.le⟩
      have e1 := h _ hpt y hy hlt'.le
      have e2 := h _ hpt y' hy' (hlt'.le.trans hyy')
      have hy1 : y - (y + t • (y' - y)) = (-t) • (y' - y) := by module
      have hy2 : y' - (y + t • (y' - y)) = (1 - t) • (y' - y) := by module
      rw [hy1, map_smul, smul_eq_mul] at e1
      rw [hy2, map_smul, smul_eq_mul] at e2
      have ht0 : 0 < t := lt_of_le_of_lt haS.1.1 ht.1
      have ht1 : t < 1 := lt_of_lt_of_le ht.2 hs1
      have hval : f' (y + t • (y' - y)) (y' - y) = 0 := by
        apply le_antisymm
        · nlinarith
        · nlinarith
      rwa [hval] at hd
    have hconst : φ s = φ a := by
      have hcont' : ContinuousOn φ (Set.Icc a s) :=
        hcont.mono (Set.Icc_subset_Icc haS.1.1 hs1)
      obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope φ (fun _ => (0 : ℝ)) has hcont' hzero
      have hsa : s - a ≠ 0 := sub_ne_zero.mpr has.ne'
      rw [eq_div_iff hsa, zero_mul] at hc
      linarith
    have := hlow s ⟨has, le_rfl⟩
    rw [hconst] at this
    exact absurd haS.2 (not_le.mpr this)
  rcases le_total (f x) (f x') with hxx | hxx
  · have := main x hx x' hx' hxx (1 - α) (by linarith) (by linarith)
    rw [mc_segment_point, sub_sub_cancel, add_comm] at this
    exact (min_le_left _ _).trans this
  · have := main x' hx' x hx hxx α h0 h1
    rw [mc_segment_point] at this
    exact (min_le_right _ _).trans this

/-- **Theorem M.C.3** (MWG, p. 934), strict sufficiency. If `∇f(x)·(x' - x) > 0` whenever
`f(x') ≥ f(x)` and `x' ≠ x`, then `f` is strictly quasiconcave. -/
theorem theorem_M_C_3_strict_sufficiency {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (h : ∀ x ∈ A, ∀ x' ∈ A, x' ≠ x → f x ≤ f x' → 0 < f' x (x' - x)) :
    StrictlyQuasiconcaveOn A f := by
  rw [strictlyQuasiconcaveOn_iff_min]
  refine ⟨hA, fun x hx x' hx' hne α h0 h1 => ?_⟩
  by_contra hle
  push Not at hle
  set z := α • x + (1 - α) • x' with hz
  have hzA : z ∈ A := hA hx hx' h0.le (by linarith) (by ring)
  have hzx : x ≠ z := by
    intro he
    apply hne
    have : (1 - α) • (x - x') = 0 := by
      have : x - z = 0 := sub_eq_zero.mpr he
      rw [hz] at this
      have e : x - (α • x + (1 - α) • x') = (1 - α) • (x - x') := by module
      rw [e] at this
      exact this
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · exact sub_eq_zero.mp h
  have hzx' : x' ≠ z := by
    intro he
    apply hne
    have : α • (x - x') = 0 := by
      have : x' - z = 0 := sub_eq_zero.mpr he
      rw [hz] at this
      have e : x' - (α • x + (1 - α) • x') = (-α) • (x - x') := by module
      rw [e, neg_smul, neg_eq_zero] at this
      exact this
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h h0.ne'
    · exact sub_eq_zero.mp h
  have e1 := h z hzA x hx hzx (hle.trans (min_le_left _ _))
  have e2 := h z hzA x' hx' hzx' (hle.trans (min_le_right _ _))
  have hx1 : x - z = (1 - α) • (x - x') := by rw [hz]; module
  have hx2 : x' - z = (-α) • (x - x') := by rw [hz]; module
  rw [hx1, map_smul, smul_eq_mul] at e1
  rw [hx2, map_smul, smul_eq_mul] at e2
  have hp : 0 < f' z (x - x') := by
    by_contra hn
    push Not at hn
    nlinarith
  nlinarith

/-- **Theorem M.C.3** (MWG, p. 934). For `f` differentiable on the convex set `A`, `f` is
quasiconcave if and only if (M.C.8) holds. -/
theorem theorem_M_C_3 {A : Set (Fin N → ℝ)} (hA : Convex ℝ A) {f : (Fin N → ℝ) → ℝ}
    {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ} (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x) :
    QuasiconcaveOn ℝ A f ↔ ∀ x ∈ A, ∀ x' ∈ A, f x ≤ f x' → 0 ≤ f' x (x' - x) :=
  ⟨fun hq x hx _ hx' hle => theorem_M_C_3_necessity hq hx hx' (hf x hx) hle,
    theorem_M_C_3_sufficiency hA hf⟩

/-- **Theorem M.C.3** (MWG, p. 934), strict necessity. If `f` is strictly quasiconcave on the
open convex set `A`, differentiable there, and `∇f(x) ≠ 0` on `A`, then
`∇f(x)·(x' - x) > 0` whenever `f(x') ≥ f(x)` and `x' ≠ x`. -/
theorem theorem_M_C_3_strict_necessity {A : Set (Fin N → ℝ)} (hAo : IsOpen A)
    {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x ∈ A, HasFDerivAt f (f' x) x) (hne : ∀ x ∈ A, f' x ≠ 0)
    (hs : StrictlyQuasiconcaveOn A f) {x x' : Fin N → ℝ} (hx : x ∈ A) (hx' : x' ∈ A)
    (hxx : x' ≠ x) (hle : f x ≤ f x') : 0 < f' x (x' - x) := by
  have hq : QuasiconcaveOn ℝ A f := by
    rw [equation_M_C_7 hs.1]
    intro y hy y' hy' α h0 h1
    rcases eq_or_ne y y' with rfl | hyy
    · rw [← add_smul, add_sub_cancel, one_smul, min_self]
    rcases h0.lt_or_eq with h0 | rfl
    · rcases h1.lt_or_eq with h1 | rfl
      · exact (hs.2 y hy y' hy' hyy α h0 h1 _ (min_le_left _ _) (min_le_right _ _)).le
      · simp
    · simp
  have hnn := theorem_M_C_3_necessity hq hx hx' (hf x hx) hle
  rcases hnn.lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  set m := (1 / 2 : ℝ) • x' + (1 - 1 / 2 : ℝ) • x with hm
  have hmA : m ∈ A := hs.1 hx' hx (by norm_num) (by norm_num) (by ring)
  have hfm : f x < f m :=
    hs.2 x' hx' x hx hxx (1 / 2) (by norm_num) (by norm_num) (f x) hle le_rfl
  -- a direction in which `∇f(x)` is positive
  obtain ⟨v, hv⟩ : ∃ v, 0 < f' x v := by
    by_contra hall
    push Not at hall
    apply hne x hx
    ext w
    have h1 := hall w
    have h2 := hall (-w)
    rw [map_neg] at h2
    simp only [zero_apply]
    linarith
  -- nearby points still beat `x` and stay in `A`
  have hcont : ContinuousAt f m := (hf m hmA).continuousAt
  have hev : ∀ᶠ δ in nhds (0 : ℝ), m - δ • v ∈ A ∧ f x < f (m - δ • v) := by
    have hpath : Filter.Tendsto (fun δ : ℝ => m - δ • v) (nhds 0) (nhds m) := by
      have : Continuous (fun δ : ℝ => m - δ • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hpath.eventually (hAo.mem_nhds hmA)).and
      (hpath.eventually (hcont.eventually (lt_mem_nhds hfm)))
  obtain ⟨δ, hδ, hδpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
  have hδ0 : 0 < δ := hδpos
  have hge := theorem_M_C_3_necessity hq hx hδ.1 (hf x hx) hδ.2.le
  have hdecomp : m - δ • v - x = (1 / 2 : ℝ) • (x' - x) - δ • v := by rw [hm]; module
  rw [hdecomp, map_sub, map_smul, map_smul, ← hzero, smul_eq_mul, smul_eq_mul] at hge
  nlinarith

/-- **Theorem M.C.3** (MWG, p. 934): the condition `∇f(x) ≠ 0` cannot be dropped. `f(x) = x³`
is strictly quasiconcave on `ℝ`, `f'(0) = 0`, and `f'(0)·(x' - 0) = 0` although `f(1) ≥ f(0)`. -/
theorem theorem_M_C_3_cube :
    (∀ x x' : ℝ, x ≠ x' → ∀ α : ℝ, 0 < α → α < 1 →
      min (x ^ 3) (x' ^ 3) < (α * x + (1 - α) * x') ^ 3) ∧
      HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧ (0 : ℝ) ^ 3 ≤ 1 ^ 3 := by
  refine ⟨fun x x' hne α h0 h1 => ?_, by simpa using hasDerivAt_pow 3 (0 : ℝ), by norm_num⟩
  have hmono := Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left (hmono h).le]
    exact hmono (by nlinarith)
  · rw [min_eq_right (hmono h).le]
    exact hmono (by nlinarith)

end MWG.ClassicalDemand
