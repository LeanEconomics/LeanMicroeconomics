/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GrossSubstitutes
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exercise 17.F.5: additively separable utilities and gross substitutes (MWG Example 17.F.2)

The utility `u(x) = ∑ₗ uₗ(xₗ)` with each `uₗ` strictly concave on `ℝ₊`, differentiable on
`ℝ₊₊` with `u'ₗ > 0`. An interior bundle `x ≫ 0` with multiplier `λ > 0`, `u'ₗ(xₗ) = λpₗ` and
`p·x = w` is a first-order point (`SepFOC`).

* First-order points are the unique demanded bundles (`ex17F5_demand_eq`, by the tangent
  inequality of concave functions `ex17F5_tangent`, `ex17F5_tangent_strict`).
* **Example 17.F.2 / Exercise 17.F.5**: if `t ↦ t u'ₗ(t)` is strictly increasing (the condition
  `-t u''ₗ(t)/u'ₗ(t) < 1`, `ex17F5_rra`), raising `p_k` (with wealth not falling) strictly
  raises the demand for every other good (`exercise_17_F_5_foc`); hence the excess demand has the
  gross substitute property for any endowments, whenever demand is interior
  (`exercise_17_F_5`).
* **CES with `0 < ρ < 1`**: `uₗ(t) = aₗ t^ρ` satisfies the condition (`-t u''/u' = 1 - ρ`,
  `ex17F5_ces_rra`), demand is interior and explicit (`ex17F5_cesDemand`, `ex17F5_ces_foc`,
  `ex17F5_ces_demand`), the same as for `(∑ₗ aₗ xₗ^ρ)^{1/ρ}` (`ex17F5_ces_transform`), and the
  excess demand has the gross substitute property for every `ω ≥ 0`, `ω ≠ 0`
  (`exercise_17_F_5_ces`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L : ℕ}

/-! ### Concave functions -/

/-- The tangent inequality: a concave `f` on `ℝ₊` with derivative `d` at `x > 0` satisfies
`f(y) ≤ f(x) + d(y - x)` for `y ≥ 0`. -/
theorem ex17F5_tangent {f : ℝ → ℝ} {d x y : ℝ} (hfc : ConcaveOn ℝ (Set.Ici 0) f) (hx : 0 < x)
    (hy : 0 ≤ y) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  have hcv : ConvexOn ℝ (Set.Ici 0) (-f) := hfc.neg
  have hxS : x ∈ Set.Ici (0 : ℝ) := hx.le
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hcv.slope_le_of_hasDerivAt (Set.mem_Ici.2 hy) hxS hyx hd.neg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    simp only [Pi.neg_apply] at h
    nlinarith
  · simp
  · have h := hcv.le_slope_of_hasDerivAt hxS (Set.mem_Ici.2 hy) hxy hd.neg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    simp only [Pi.neg_apply] at h
    nlinarith

/-- The strict tangent inequality for a strictly concave `f`: `f(y) < f(x) + d(y - x)` for
`y ≥ 0`, `y ≠ x`. -/
theorem ex17F5_tangent_strict {f : ℝ → ℝ} {d x y : ℝ} (hfc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hx : 0 < x) (hy : 0 ≤ y) (hne : y ≠ x) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  have hm := hfc.2 (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hy) (Ne.symm hne)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have ht := ex17F5_tangent hfc.concaveOn hx (y := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
    (by simp only [smul_eq_mul]; positivity) hd
  simp only [smul_eq_mul] at hm ht
  nlinarith

/-! ### First-order points of separable utilities -/

/-- **Example 17.F.2** (MWG, p. 612). An interior first-order point of the UMP for
`u(x) = ∑ₗ uₗ(xₗ)` with marginal utilities `du`: `x ≫ 0`, `λ > 0`, `u'ₗ(xₗ) = λpₗ`,
`p·x = w`. -/
def SepFOC (du : Fin L → ℝ → ℝ) (p x : Fin L → ℝ) (lam w : ℝ) : Prop :=
  (∀ l, 0 < x l) ∧ 0 < lam ∧ (∀ l, du l (x l) = lam * p l) ∧ p ⬝ᵥ x = w

/-- **Example 17.F.2** (MWG, p. 612). For `u(x) = ∑ₗ uₗ(xₗ)` with `uₗ` strictly concave on `ℝ₊`
and differentiable on `ℝ₊₊` with derivative `du l`, a first-order point `x` at `(p, w)` is the
unique demanded bundle: `x(p, w) = {x}`. -/
theorem ex17F5_demand_eq {u du : Fin L → ℝ → ℝ} (hconc : ∀ l, StrictConcaveOn ℝ (Set.Ici 0) (u l))
    (hd : ∀ l, ∀ t, 0 < t → HasDerivAt (u l) (du l t) t) {p x : Fin L → ℝ} {lam w : ℝ}
    (hfoc : SepFOC du p x lam w) :
    walrasianDemand (fun y => ∑ l, u l (y l)) p w = {x} := by
  obtain ⟨hx, hlam, hdu, hb⟩ := hfoc
  have hxb : x ∈ budgetSetOn (nonnegOrthant L) p w := ⟨fun l => (hx l).le, hb.le⟩
  have key : ∀ y ∈ budgetSetOn (nonnegOrthant L) p w,
      ∑ l, u l (y l) ≤ ∑ l, u l (x l) ∧ (y ≠ x → ∑ l, u l (y l) < ∑ l, u l (x l)) := by
    intro y ⟨hy0, hyb⟩
    have htan : ∀ l, u l (y l) ≤ u l (x l) + lam * p l * (y l - x l) := fun l => by
      rw [← hdu l]
      exact ex17F5_tangent (hconc l).concaveOn (hx l) (hy0 l) (hd l _ (hx l))
    have hlin : ∑ l, lam * p l * (y l - x l) ≤ 0 := by
      have : ∑ l, lam * p l * (y l - x l) = lam * (p ⬝ᵥ y - p ⬝ᵥ x) := by
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hlam.le (by linarith)
    have hsum : ∑ l, u l (y l) ≤ ∑ l, u l (x l) + ∑ l, lam * p l * (y l - x l) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun l _ => htan l
    refine ⟨by linarith, fun hne => ?_⟩
    obtain ⟨l0, hl0⟩ := Function.ne_iff.1 hne
    have hstrict : ∑ l, u l (y l) < ∑ l, u l (x l) + ∑ l, lam * p l * (y l - x l) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_lt_sum (fun l _ => htan l) ⟨l0, Finset.mem_univ _, ?_⟩
      rw [← hdu l0]
      exact ex17F5_tangent_strict (hconc l0) (hx l0) (hy0 l0) hl0 (hd l0 _ (hx l0))
    linarith
  ext y
  constructor
  · intro hy
    by_contra hne
    have h1 := (key y hy.1).2 hne
    have h2 := hy.2 x hxb
    linarith
  · rintro rfl
    exact ⟨hxb, fun y hy => (key y hy).1⟩

/-- **Example 17.F.2** (MWG, p. 612), the condition `-t u''(t)/u'(t) < 1`: if `u'(t) > 0` and
`u'` has derivative `u''(t)` on `ℝ₊₊`, then `t ↦ t u'(t)` is strictly increasing on `ℝ₊₊`. -/
theorem ex17F5_rra {du d2 : ℝ → ℝ} (hd : ∀ t, 0 < t → HasDerivAt du (d2 t) t)
    (hpos : ∀ t, 0 < t → 0 < du t) (hrra : ∀ t, 0 < t → -(t * d2 t) / du t < 1) :
    StrictMonoOn (fun t => t * du t) (Set.Ioi 0) := by
  have hderiv : ∀ t, 0 < t → HasDerivAt (fun t => t * du t) (1 * du t + t * d2 t) t :=
    fun t ht => (hasDerivAt_id t).mul (hd t ht)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt) fun t ht => ?_
  rw [interior_Ioi] at ht
  rw [(hderiv t ht).deriv]
  have h := hrra t ht
  rw [div_lt_one (hpos t ht)] at h
  linarith

/-- **Exercise 17.F.5** (MWG, p. 645), the key step of Example 17.F.2. Let the marginal utilities
`u'ₗ` be strictly decreasing and `t ↦ t u'ₗ(t)` strictly increasing on `ℝ₊₊`. If `x` and `x'`
are first-order points at `(p, w)` and `(p', w')`, where `p'` raises only the price of good `k`
and `w' ≥ w`, then `x'ₗ > xₗ` for every `ℓ ≠ k`. -/
theorem exercise_17_F_5_foc {du : Fin L → ℝ → ℝ} (hdec : ∀ l, StrictAntiOn (du l) (Set.Ioi 0))
    (hinc : ∀ l, StrictMonoOn (fun t => t * du l t) (Set.Ioi 0)) {p p' x x' : Fin L → ℝ}
    {lam lam' w w' : ℝ} (hfoc : SepFOC du p x lam w) (hfoc' : SepFOC du p' x' lam' w')
    (hp : p ∈ posOrthant L) {k : Fin L} (hk : p k < p' k) (he : ∀ j, j ≠ k → p' j = p j)
    (hw : w ≤ w') : ∀ l, l ≠ k → x l < x' l := by
  obtain ⟨hx, hlam, hdu, hb⟩ := hfoc
  obtain ⟨hx', hlam', hdu', hb'⟩ := hfoc'
  have hpk' : 0 < p' k := (hp k).trans hk
  have hle : ∀ j, p j ≤ p' j := fun j => by
    by_cases hj : j = k
    · subst hj; exact hk.le
    · rw [he j hj]
  -- the marginal utility of wealth falls
  have hlamlt : lam' < lam := by
    by_contra hge
    rw [not_lt] at hge
    have hterm : ∀ j, lam * (p' j * x' j) ≤ lam * (p j * x j) ∧
        (j = k → lam * (p' j * x' j) < lam * (p j * x j)) := by
      intro j
      have hpj' : 0 < p' j := lt_of_lt_of_le (hp j) (hle j)
      have hmu : lam * p j ≤ lam' * p' j := mul_le_mul hge (hle j) (hp j).le hlam'.le
      have hxle : x' j ≤ x j := by
        by_contra hlt
        rw [not_le] at hlt
        have := (hdec j) (Set.mem_Ioi.2 (hx j)) (Set.mem_Ioi.2 (hx' j)) hlt
        rw [hdu j, hdu' j] at this
        linarith
      have hφ : x' j * du j (x' j) ≤ x j * du j (x j) :=
        (hinc j).le_iff_le (Set.mem_Ioi.2 (hx' j)) (Set.mem_Ioi.2 (hx j)) |>.2 hxle
      rw [hdu j, hdu' j] at hφ
      have h1 : lam * (p' j * x' j) ≤ lam' * (p' j * x' j) :=
        mul_le_mul_of_nonneg_right hge (mul_pos hpj' (hx' j)).le
      refine ⟨by nlinarith, fun hjk => ?_⟩
      subst hjk
      have hmu' : lam * p j < lam' * p' j :=
        lt_of_lt_of_le (mul_lt_mul_of_pos_left hk hlam) (mul_le_mul_of_nonneg_right hge hpk'.le)
      have hxlt : x' j < x j := by
        by_contra hge'
        rw [not_lt] at hge'
        rcases eq_or_lt_of_le hge' with heq | hlt
        · have e1 := hdu j
          have e2 := hdu' j
          rw [heq] at e1
          linarith
        · have := (hdec j) (Set.mem_Ioi.2 (hx j)) (Set.mem_Ioi.2 (hx' j)) hlt
          rw [hdu j, hdu' j] at this
          linarith
      have hφ' : x' j * du j (x' j) < x j * du j (x j) :=
        (hinc j) (Set.mem_Ioi.2 (hx' j)) (Set.mem_Ioi.2 (hx j)) hxlt
      rw [hdu j, hdu' j] at hφ'
      nlinarith
    have hsum : lam * w' < lam * w := by
      rw [← hb, ← hb', dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_lt_sum (fun j _ => (hterm j).1) ⟨k, Finset.mem_univ _, (hterm k).2 rfl⟩
    nlinarith
  intro l hl
  by_contra hge
  rw [not_lt] at hge
  have hmu : du l (x' l) < du l (x l) := by
    rw [hdu l, hdu' l, he l hl]
    exact mul_lt_mul_of_pos_right hlamlt (hp l)
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [heq] at hmu; exact lt_irrefl _ hmu
  · have := (hdec l) (Set.mem_Ioi.2 (hx' l)) (Set.mem_Ioi.2 (hx l)) hlt
    linarith

/-- **Exercise 17.F.5** (MWG, p. 645; Example 17.F.2). If the consumer's demand
`x(p) = x(p, p·ω)` (`ω ≥ 0`) is an interior first-order point at every `p ≫ 0`, marginal
utilities are strictly decreasing and `t ↦ t u'ₗ(t)` strictly increasing (`-t u''/u' < 1`), then
the excess demand `z(p) = x(p) - ω` has the gross substitute property. -/
theorem exercise_17_F_5 {du : Fin L → ℝ → ℝ} (hdec : ∀ l, StrictAntiOn (du l) (Set.Ioi 0))
    (hinc : ∀ l, StrictMonoOn (fun t => t * du l t) (Set.Ioi 0)) {ω : Fin L → ℝ}
    (hω : ∀ l, 0 ≤ ω l) {x : (Fin L → ℝ) → Fin L → ℝ}
    (hx : ∀ p ∈ posOrthant L, ∃ lam, SepFOC du p (x p) lam (p ⬝ᵥ ω)) :
    GrossSubstitute (fun p => x p - ω) := by
  intro p hp p' hp' k hk he l hl
  obtain ⟨lam, hfoc⟩ := hx p hp
  obtain ⟨lam', hfoc'⟩ := hx p' hp'
  have hw : p ⬝ᵥ ω ≤ p' ⬝ᵥ ω := Finset.sum_le_sum fun j _ => by
    by_cases hj : j = k
    · subst hj; exact mul_le_mul_of_nonneg_right hk.le (hω j)
    · rw [he j hj]
  have := exercise_17_F_5_foc hdec hinc hfoc hfoc' hp hk he hw l hl
  simp only [Pi.sub_apply]
  linarith

/-! ### CES utilities, `0 < ρ < 1` -/

/-- **Example 17.F.2** (MWG, p. 612). The additively separable form `∑ₗ aₗ xₗ^ρ` of the CES
utility. -/
noncomputable def ex17F5_cesU (a : Fin L → ℝ) (ρ : ℝ) (y : Fin L → ℝ) : ℝ :=
  ∑ l, a l * y l ^ ρ

/-- The CES demand: `xₗ = μ cₗ` with `cₗ = (pₗ/(aₗρ))^{1/(ρ-1)}` and `μ = w/∑ⱼ pⱼcⱼ`. -/
noncomputable def ex17F5_cesDemand (a : Fin L → ℝ) (ρ : ℝ) (p : Fin L → ℝ) (w : ℝ) :
    Fin L → ℝ :=
  fun l => w / (∑ j, p j * (p j / (a j * ρ)) ^ (ρ - 1)⁻¹) * (p l / (a l * ρ)) ^ (ρ - 1)⁻¹

/-- The CES excess demand `z(p) = x(p, p·ω) - ω`. -/
noncomputable def ex17F5_cesED (a : Fin L → ℝ) (ρ : ℝ) (ω p : Fin L → ℝ) : Fin L → ℝ :=
  ex17F5_cesDemand a ρ p (p ⬝ᵥ ω) - ω

/-- **Example 17.F.2** (MWG, p. 612). For `uₗ(t) = aₗt^ρ`, `0 < ρ < 1`, `aₗ > 0`:
`u'(t) = aₗρt^{ρ-1}`, `u''(t) = aₗρ(ρ-1)t^{ρ-2}`, and `-t u''(t)/u'(t) = 1 - ρ < 1`; hence
`t u'(t)` is strictly increasing, and `u'` is positive and strictly decreasing. -/
theorem ex17F5_ces_rra {a ρ : ℝ} (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ t, 0 < t → HasDerivAt (fun t => a * ρ * t ^ (ρ - 1)) (a * ρ * ((ρ - 1) * t ^ (ρ - 2))) t)
      ∧ (∀ t, 0 < t → -(t * (a * ρ * ((ρ - 1) * t ^ (ρ - 2)))) / (a * ρ * t ^ (ρ - 1)) = 1 - ρ)
      ∧ StrictMonoOn (fun t => t * (a * ρ * t ^ (ρ - 1))) (Set.Ioi 0)
      ∧ StrictAntiOn (fun t => a * ρ * t ^ (ρ - 1)) (Set.Ioi 0) := by
  have hd : ∀ t, 0 < t →
      HasDerivAt (fun t => a * ρ * t ^ (ρ - 1)) (a * ρ * ((ρ - 1) * t ^ (ρ - 2))) t := by
    intro t ht
    have := (Real.hasDerivAt_rpow_const (p := ρ - 1) (Or.inl ht.ne')).const_mul (a * ρ)
    convert this using 2
    ring_nf
  have hval : ∀ t, 0 < t → -(t * (a * ρ * ((ρ - 1) * t ^ (ρ - 2)))) / (a * ρ * t ^ (ρ - 1)) =
      1 - ρ := by
    intro t ht
    have hpow : t * t ^ (ρ - 2) = t ^ (ρ - 1) := by
      rw [show ρ - 1 = (ρ - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one, mul_comm]
    have hpos : 0 < t ^ (ρ - 1) := Real.rpow_pos_of_pos ht _
    field_simp
    rw [show t * (ρ - 1) * t ^ (ρ - 2) = (ρ - 1) * (t * t ^ (ρ - 2)) by ring, hpow]
    ring
  refine ⟨hd, hval, ex17F5_rra hd (fun t ht => by positivity) fun t ht => by
    rw [hval t ht]; linarith, fun s hs t ht hst => ?_⟩
  have := Real.rpow_lt_rpow_of_neg (Set.mem_Ioi.1 hs) hst (by linarith : ρ - 1 < 0)
  have hpos : 0 < a * ρ := by positivity
  exact mul_lt_mul_of_pos_left this hpos

/-- **Example 17.F.2** (MWG, p. 612). The CES demand is an interior first-order point at every
`p ≫ 0`, `w > 0` (`L ≥ 1`), with multiplier `λ = μ^{ρ-1}`. -/
theorem ex17F5_ces_foc [NeZero L] {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {w : ℝ} (hw : 0 < w) :
    SepFOC (fun l t => a l * ρ * t ^ (ρ - 1)) p (ex17F5_cesDemand a ρ p w)
      ((w / ∑ j, p j * (p j / (a j * ρ)) ^ (ρ - 1)⁻¹) ^ (ρ - 1)) w := by
  set c : Fin L → ℝ := fun l => (p l / (a l * ρ)) ^ (ρ - 1)⁻¹ with hc
  have hcpos : ∀ l, 0 < c l := fun l => Real.rpow_pos_of_pos (div_pos (hp l) (by
    have := ha l; positivity)) _
  have hS : 0 < ∑ j, p j * c j :=
    Finset.sum_pos (fun j _ => mul_pos (hp j) (hcpos j)) Finset.univ_nonempty
  set μ := w / ∑ j, p j * c j with hμ
  have hμpos : 0 < μ := div_pos hw hS
  have hx : ∀ l, ex17F5_cesDemand a ρ p w l = μ * c l := fun l => rfl
  refine ⟨fun l => by rw [hx]; exact mul_pos hμpos (hcpos l),
    Real.rpow_pos_of_pos hμpos _, fun l => ?_, ?_⟩
  · simp only [hx]
    rw [Real.mul_rpow hμpos.le (hcpos l).le]
    have hcl : c l ^ (ρ - 1) = p l / (a l * ρ) := by
      simp only [hc]
      exact Real.rpow_inv_rpow (div_pos (hp l) (by have := ha l; positivity)).le
        (by linarith : ρ - 1 ≠ 0)
    rw [hcl]
    have := ha l
    field_simp
  · simp only [dotProduct, hx]
    rw [show ∑ l, p l * (μ * c l) = μ * ∑ l, p l * c l by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring]
    rw [hμ]
    field_simp

/-- **Example 17.F.2** (MWG, p. 612). For `aₗ > 0` and `0 < ρ < 1` the CES demand is the unique
maximizer of `∑ₗ aₗ xₗ^ρ` on the budget set (`p ≫ 0`, `w > 0`). -/
theorem ex17F5_ces_demand [NeZero L] {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {w : ℝ} (hw : 0 < w) :
    walrasianDemand (ex17F5_cesU a ρ) p w = {ex17F5_cesDemand a ρ p w} := by
  have hconc : ∀ l, StrictConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => a l * t ^ ρ) := fun l => by
    refine ⟨convex_Ici 0, fun x hx y hy hxy α β hα hβ hαβ => ?_⟩
    have := (Real.strictConcaveOn_rpow hρ0 hρ1).2 hx hy hxy hα hβ hαβ
    simp only [smul_eq_mul] at this ⊢
    have hal := ha l
    nlinarith
  have hd : ∀ l, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => a l * t ^ ρ) (a l * ρ * t ^ (ρ - 1)) t := fun l t ht => by
    have := (Real.hasDerivAt_rpow_const (p := ρ) (Or.inl ht.ne')).const_mul (a l)
    convert this using 1
    ring
  exact ex17F5_demand_eq (u := fun l t => a l * t ^ ρ) hconc hd (ex17F5_ces_foc ha hρ0 hρ1 hp hw)

/-- **Example 17.F.2** (MWG, p. 612). The CES utility `(∑ₗ aₗ xₗ^ρ)^{1/ρ}` (`ρ > 0`) has the same
demand as its additively separable transform `∑ₗ aₗ xₗ^ρ`. -/
theorem ex17F5_ces_transform {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {ρ : ℝ} (hρ0 : 0 < ρ)
    (p : Fin L → ℝ) (w : ℝ) :
    walrasianDemand (fun y => ex17F5_cesU a ρ y ^ (1 / ρ)) p w =
      walrasianDemand (ex17F5_cesU a ρ) p w := by
  have hnn : ∀ y ∈ nonnegOrthant L, 0 ≤ ex17F5_cesU a ρ y := fun y hy =>
    Finset.sum_nonneg fun l _ => mul_nonneg (ha l).le (Real.rpow_nonneg (hy l) _)
  ext x
  simp only [walrasianDemand, walrasianDemandOn]
  constructor
  · rintro ⟨hxb, hmax⟩
    refine ⟨hxb, fun y hy => ?_⟩
    have := hmax y hy
    exact (Real.rpow_le_rpow_iff (hnn y hy.1) (hnn x hxb.1) (by positivity)).1 this
  · rintro ⟨hxb, hmax⟩
    refine ⟨hxb, fun y hy => ?_⟩
    exact Real.rpow_le_rpow (hnn y hy.1) (hmax y hy) (by positivity)

/-- **Exercise 17.F.5** (MWG, p. 645; Example 17.F.2). For CES preferences with `0 < ρ < 1` and
weights `aₗ > 0`, the excess demand `z(p) = x(p, p·ω) - ω` has the gross substitute property for
every endowment `ω ≥ 0`, `ω ≠ 0`. -/
theorem exercise_17_F_5_ces [NeZero L] {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ω : Fin L → ℝ} (hω : ∀ l, 0 ≤ ω l) (hω0 : ∃ l, 0 < ω l) :
    GrossSubstitute (ex17F5_cesED a ρ ω) := by
  have hr := fun l => ex17F5_ces_rra (ha l) hρ0 hρ1
  refine exercise_17_F_5 (du := fun l t => a l * ρ * t ^ (ρ - 1))
    (x := fun p => ex17F5_cesDemand a ρ p (p ⬝ᵥ ω)) (fun l => (hr l).2.2.2)
    (fun l => (hr l).2.2.1) hω fun p hp => ⟨_, ex17F5_ces_foc ha hρ0 hρ1 hp ?_⟩
  obtain ⟨l, hl⟩ := hω0
  exact lt_of_lt_of_le (mul_pos (hp l) hl) (Finset.single_le_sum
    (fun j _ => mul_nonneg (hp j).le (hω j)) (Finset.mem_univ l))

end MWG.PositiveEquilibriumTheory
