/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Concave functions of several variables: tangent inequality and Kuhn-Tucker on the orthant

Tools for the exercises with several choice variables (Exercises 11.B.5, 11.D.2, 11.D.4).

* `convex_tangent`, `concave_tangent`: for a convex (concave) function with Fréchet derivative
  `L` at `x`, `c(x) + L(y - x) ≤ c(y)` (resp. `≥`) for all `y` in the domain.
* `orthant_kt_iff`: a point `x ≥ 0` maximizes a concave differentiable `F` on the nonnegative
  orthant of `ℝ^ι` iff each partial derivative `∂ⱼF(x) = L(eⱼ)` is `≤ 0`, with equality if
  `xⱼ > 0`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-- **Tangent inequality for convex functions.** If `c` is convex on `S`, `x, y ∈ S` and `c` has
Fréchet derivative `L` at `x`, then `c(x) + L(y - x) ≤ c(y)`. -/
theorem convex_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {c : E → ℝ} (hc : ConvexOn ℝ S c) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {L : E →L[ℝ] ℝ}
    (hL : HasFDerivAt c L x) : c x + L (y - x) ≤ c y := by
  set ℓ : ℝ → E := fun s => x + s • (y - x)
  have hℓS : ∀ s ∈ Set.Icc (0 : ℝ) 1, ℓ s ∈ S := fun s hs => by
    have := hc.1 hx hy (sub_nonneg.2 hs.2) hs.1 (by ring)
    convert this using 1
    simp only [ℓ, smul_sub, sub_smul, one_smul]
    abel
  set g : ℝ → ℝ := fun s => c (ℓ s)
  have hg : ConvexOn ℝ (Set.Icc 0 1) g := by
    refine ⟨convex_Icc 0 1, fun s hs t ht a b ha hb hab => ?_⟩
    have := hc.2 (hℓS s hs) (hℓS t ht) ha hb hab
    convert this using 2
    have hx' : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    simp only [ℓ, smul_add, smul_smul, smul_eq_mul, add_smul]
    nth_rewrite 1 [hx']
    abel
  have hℓ : HasDerivAt ℓ (y - x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • (y - x)) ((1 : ℝ) • (y - x)) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    rw [one_smul] at h1
    exact h1.const_add x
  have hℓ0 : ℓ 0 = x := by simp [ℓ]
  have hL' : HasFDerivAt c L (ℓ 0) := by rw [hℓ0]; exact hL
  have hgd : HasDerivAt g (L (y - x)) 0 := hL'.comp_hasDerivAt 0 hℓ
  have := hg.deriv_le_slope ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    hgd.differentiableAt
  rw [hgd.deriv, slope_def_field] at this
  have h1 : g 1 = c y := by simp [g, ℓ]
  have h0 : g 0 = c x := by simp [g, ℓ]
  rw [h1, h0] at this
  linarith

/-- **Tangent inequality for concave functions**: `c(y) ≤ c(x) + L(y - x)`. -/
theorem concave_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {c : E → ℝ} (hc : ConcaveOn ℝ S c) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {L : E →L[ℝ] ℝ}
    (hL : HasFDerivAt c L x) : c y ≤ c x + L (y - x) := by
  have := convex_tangent hc.neg hx hy hL.neg
  have e : (-L) (y - x) = -(L (y - x)) := rfl
  simp only [Pi.neg_apply, e] at this
  linarith

/-- The nonnegative orthant of `ℝ^ι`. -/
def orthant (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, 0 ≤ x i}

theorem convex_orthant (ι : Type*) : Convex ℝ (orthant ι) := by
  intro x hx y hy a b ha hb _ i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- The derivative of `F` along the `j`-th coordinate line through `x`. -/
theorem hasDerivAt_update {ι : Type*} [Finite ι] [DecidableEq ι] {F : (ι → ℝ) → ℝ}
    {x : ι → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt F L x) (j : ι) :
    HasDerivAt (fun t => F (Function.update x j t)) (L (Pi.single j 1)) (x j) := by
  have := Fintype.ofFinite ι
  have hupd : ∀ t, Function.update x j t = x + (t - x j) • Pi.single j 1 := fun t => by
    funext k
    rcases eq_or_ne k j with h | h
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  have hℓ : HasDerivAt (fun t => x + (t - x j) • (Pi.single j 1 : ι → ℝ)) (Pi.single j 1)
      (x j) := by
    have h1 : HasDerivAt (fun t : ℝ => (t - x j) • (Pi.single j 1 : ι → ℝ))
        ((1 : ℝ) • (Pi.single j 1 : ι → ℝ)) (x j) :=
      ((hasDerivAt_id (x j)).sub_const (x j)).smul_const (Pi.single j 1 : ι → ℝ)
    rw [one_smul] at h1
    exact h1.const_add x
  have hx : x + (x j - x j) • (Pi.single j 1 : ι → ℝ) = x := by simp
  have hL' : HasFDerivAt F L (x + (x j - x j) • (Pi.single j 1 : ι → ℝ)) := by rw [hx]; exact hL
  have := hL'.comp_hasDerivAt (x j) hℓ
  simp_rw [hupd]
  exact this

/-- `L(v) = ∑ⱼ vⱼ L(eⱼ)` for a linear functional on `ℝ^ι`. -/
theorem clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ) : L v = ∑ j, v j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (Pi.single j (v j) : ι → ℝ) = v j • Pi.single j 1 := by
    ext k
    rcases eq_or_ne k j with h | h
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs, map_smul, smul_eq_mul]

/-- **Kuhn-Tucker on the orthant.** For `F` concave on `ℝ^ι₊` with derivative `L` at `x ≥ 0`,
`x` maximizes `F` on `ℝ^ι₊` iff every partial derivative `L(eⱼ)` is `≤ 0`, with equality if
`xⱼ > 0`. -/
theorem orthant_kt_iff {ι : Type*} [Finite ι] [DecidableEq ι] {F : (ι → ℝ) → ℝ}
    (hF : ConcaveOn ℝ (orthant ι) F) {x : ι → ℝ} (hx : x ∈ orthant ι)
    {L : (ι → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt F L x) :
    (∀ y ∈ orthant ι, F y ≤ F x) ↔
      ∀ j, L (Pi.single j 1) ≤ 0 ∧ (0 < x j → L (Pi.single j 1) = 0) := by
  have := Fintype.ofFinite ι
  constructor
  · intro hmax j
    have hmax' : ∀ t, 0 ≤ t → F (Function.update x j t) ≤ F (Function.update x j (x j)) := by
      intro t ht
      rw [Function.update_eq_self]
      refine hmax _ fun k => ?_
      rcases eq_or_ne k j with h | h
      · subst h; simpa using ht
      · rw [Function.update_of_ne h]; exact hx k
    exact foc_max_necessary (hasDerivAt_update hL j).hasDerivWithinAt (hx j) hmax'
  · intro hkt y hy
    have ht := concave_tangent hF hx hy hL
    rw [clm_apply_eq_sum] at ht
    have : ∑ j, (y - x) j * L (Pi.single j 1) ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      rcases eq_or_lt_of_le (hx j) with h0 | hp
      · simp only [Pi.sub_apply, ← h0, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hy j) (hkt j).1
      · rw [(hkt j).2 hp, mul_zero]
    linarith

end MWG.ExternalitiesPublicGoods
