/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.UniquenessPareto
import MWGPositiveEquilibriumTheory.Exercises17D

/-!
# Instances for Section 17.F (MWG pp. 610, 615)

* **(17.F.1)**, instance of the strict differential condition: one Cobb-Douglas consumer with
  `a = ω = (1, 1)`, `z(p) = (p₂/2p₁ - ½, p₁/2p₂ - ½)` (`wadZ`). Where `dp·z(p) = 0` with `dp` not
  proportional to `p`, necessarily `p₁ = p₂` and `dp·Dz(p) dp = -(dp₁ - dp₂)²/2p₁ < 0`
  (`wadZ_condition`); so `eq_17_F_1_sufficient` applies (`eq_17_F_1_instance`).
* **Example 17.F.3**, instance of the index argument: the two-good excess demand
  `twoGoodED g`, `g(t) = (1 - t)(2 - t)(3 - t)/(t(1 + t²))`, satisfies (i)-(v) and has a regular
  equilibrium `p = (2, 1)` of index `-1` (`ex17F3_index`); hence another equilibrium exists
  (`example_17_F_3_index_instance`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

/-! ### (17.F.1): an instance -/

/-- One Cobb-Douglas consumer with `a = ω = (1, 1)`: `z(p) = (p₂/2p₁ - ½, p₁/2p₂ - ½)`. -/
noncomputable def wadZ (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 1 / (2 * p 0) - 1 / 2, p 0 / (2 * p 1) - 1 / 2]

/-- `wadZ` is homogeneous of degree zero and satisfies Walras' law. -/
theorem wadZ_props : EDHomogeneous wadZ ∧ EDWalrasLaw wadZ := by
  refine ⟨fun p hp α hα => ?_, fun p hp => ?_⟩
  · have h0 := (hp 0).ne'
    have h1 := (hp 1).ne'
    have := hα.ne'
    funext l
    rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) l with rfl | rfl
    · change (α * p 1) / (2 * (α * p 0)) - 1 / 2 = p 1 / (2 * p 0) - 1 / 2
      field_simp
    · change (α * p 0) / (2 * (α * p 1)) - 1 / 2 = p 0 / (2 * p 1) - 1 / 2
      field_simp
  · have h0 := (hp 0).ne'
    have h1 := (hp 1).ne'
    simp only [dotProduct, Fin.sum_univ_two]
    change p 0 * (p 1 / (2 * p 0) - 1 / 2) + p 1 * (p 0 / (2 * p 1) - 1 / 2) = 0
    field_simp
    ring

/-- `wadZ` is differentiable on `ℝ²₊₊`. -/
theorem wadZ_differentiableAt {p : Fin 2 → ℝ} (hp : p ∈ posOrthant 2) :
    DifferentiableAt ℝ wadZ p := by
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  refine differentiableAt_pi.2 fun l => ?_
  rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) l with rfl | rfl
  · change DifferentiableAt ℝ (fun q : Fin 2 → ℝ => q 1 / (2 * q 0) - 1 / 2) p
    fun_prop (disch := simp [h0])
  · change DifferentiableAt ℝ (fun q : Fin 2 → ℝ => q 0 / (2 * q 1) - 1 / 2) p
    fun_prop (disch := simp [h1])

/-- **(17.F.1)**, instance (MWG, p. 610): `wadZ` satisfies the strict differential condition. -/
theorem wadZ_condition {p : Fin 2 → ℝ} (hp : p ∈ posOrthant 2) (v : Fin 2 → ℝ)
    (hv : v ⬝ᵥ wadZ p = 0) (hprop : ∀ α : ℝ, v ≠ α • p) :
    v ⬝ᵥ fderiv ℝ wadZ p v < 0 := by
  have h0 := hp 0
  have h1 := hp 1
  -- the derivative along the line `p + t v`
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hg := wad_hasDerivAt_dot v
    ((wadZ_differentiableAt hp).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp))
  have hexp : HasDerivAt (fun t : ℝ => v 0 * ((p 1 + t * v 1) / (2 * (p 0 + t * v 0)) - 1 / 2) +
      v 1 * ((p 0 + t * v 0) / (2 * (p 1 + t * v 1)) - 1 / 2))
      (v 0 * ((v 1 * (2 * p 0) - p 1 * (2 * v 0)) / (2 * p 0) ^ 2) +
        v 1 * ((v 0 * (2 * p 1) - p 0 * (2 * v 1)) / (2 * p 1) ^ 2)) 0 := by
    have hl : ∀ a b : ℝ, HasDerivAt (fun t : ℝ => a + t * b) b 0 := fun a b => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
    have d1 := ((hl (p 1) (v 1)).div ((hl (p 0) (v 0)).const_mul 2)
      (by rw [zero_mul, add_zero]; positivity))
    have d2 := ((hl (p 0) (v 0)).div ((hl (p 1) (v 1)).const_mul 2)
      (by rw [zero_mul, add_zero]; positivity))
    have := ((d1.sub_const (1 / 2)).const_mul (v 0)).add ((d2.sub_const (1 / 2)).const_mul (v 1))
    convert this using 1
    simp
  have hfun : (fun t : ℝ => v ⬝ᵥ wadZ (p + t • v)) = fun t : ℝ =>
      v 0 * ((p 1 + t * v 1) / (2 * (p 0 + t * v 0)) - 1 / 2) +
        v 1 * ((p 0 + t * v 0) / (2 * (p 1 + t * v 1)) - 1 / 2) := by
    funext t
    simp only [dotProduct, Fin.sum_univ_two]
    rfl
  have hg' : HasDerivAt (fun t : ℝ => v ⬝ᵥ wadZ (p + t • v)) (v ⬝ᵥ fderiv ℝ wadZ p v) 0 := hg
  rw [hfun] at hg'
  rw [hg'.unique hexp]
  -- `v·z(p) = 0` and `v` not proportional to `p` force `p₁ = p₂`
  have hvz : (p 1 - p 0) * (v 0 / p 0 - v 1 / p 1) = 0 := by
    have := hv
    simp only [dotProduct, Fin.sum_univ_two] at this
    change v 0 * (p 1 / (2 * p 0) - 1 / 2) + v 1 * (p 0 / (2 * p 1) - 1 / 2) = 0 at this
    field_simp at this ⊢
    linarith
  have hratio : v 0 / p 0 ≠ v 1 / p 1 := fun h => hprop (v 0 / p 0) (by
    funext l
    rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) l with rfl | rfl
    · simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    · simp only [Pi.smul_apply, smul_eq_mul, h]; field_simp)
  have hpp : p 1 = p 0 := by
    rcases mul_eq_zero.1 hvz with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h) hratio
  have hv01 : v 0 ≠ v 1 := fun h => hratio (by rw [h, hpp])
  rw [hpp]
  have : v 0 * ((v 1 * (2 * p 0) - p 0 * (2 * v 0)) / (2 * p 0) ^ 2) +
      v 1 * ((v 0 * (2 * p 0) - p 0 * (2 * v 1)) / (2 * p 0) ^ 2) =
      -((v 0 - v 1) ^ 2 / (2 * p 0)) := by
    field_simp
    ring
  rw [this, neg_lt_zero]
  exact div_pos (by have := sub_ne_zero.2 hv01; positivity) (by positivity)

/-- **(17.F.1)**, instance (MWG, p. 610): `eq_17_F_1_sufficient` applies to `wadZ`, which
therefore satisfies the weak axiom. -/
theorem eq_17_F_1_instance : WeakAxiomED wadZ :=
  eq_17_F_1_sufficient wadZ_props.1 wadZ_props.2 (D := fun p => fderiv ℝ wadZ p)
    (fun _ hp => (wadZ_differentiableAt hp).hasFDerivAt)
    (fun _ hp v hv hprop => wadZ_condition hp v hv hprop)

/-! ### Example 17.F.3: an equilibrium of index `-1` -/

/-- `g(t) = (1 - t)(2 - t)(3 - t)/(t(1 + t²))`: `z₁(p₁, 1) = g(p₁)` vanishes at `p₁ = 1, 2, 3`. -/
noncomputable def ex17F3g (t : ℝ) : ℝ := (1 - t) * (2 - t) * (3 - t) / (t * (1 + t ^ 2))

/-- The two-good excess demand `(g(p₁/p₂), -(p₁/p₂)g(p₁/p₂))`. -/
noncomputable def ex17F3Z : (Fin 2 → ℝ) → Fin 2 → ℝ := twoGoodED ex17F3g

/-- `ex17F3Z` satisfies (i)-(v) of Proposition 17.B.2. -/
theorem ex17F3Z_isStandard : IsStandardExcessDemand ex17F3Z := by
  refine twoGoodED_isStandard ?_ ⟨7, by norm_num, fun t ht => ⟨?_, ?_⟩⟩ (fun M => ?_)
    (fun M => ?_)
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    have : 0 < t := ht
    positivity
  · have hd : 0 < t * (1 + t ^ 2) := by positivity
    rw [ex17F3g, lt_div_iff₀ hd]
    nlinarith [sq_nonneg (t - 3 / 4), pow_pos ht 3]
  · have hd : 0 < 1 + t ^ 2 := by positivity
    rw [ex17F3g, show t * ((1 - t) * (2 - t) * (3 - t) / (t * (1 + t ^ 2))) =
      (1 - t) * (2 - t) * (3 - t) / (1 + t ^ 2) by field_simp, div_lt_iff₀ hd]
    nlinarith [pow_pos ht 3, sq_nonneg t]
  · refine ⟨min (1 / 2) (1 / (2 * (|M| + 1))), by positivity, fun t ht htδ => ?_⟩
    have ht1 : t < 1 / 2 := lt_of_lt_of_le htδ (min_le_left _ _)
    have ht2 : t < 1 / (2 * (|M| + 1)) := lt_of_lt_of_le htδ (min_le_right _ _)
    have hM : t * (2 * (|M| + 1)) < 1 := by
      rw [lt_div_iff₀ (by positivity)] at ht2; linarith
    have hd : 0 < t * (1 + t ^ 2) := by positivity
    rw [ex17F3g, lt_div_iff₀ hd]
    have hN : 1 < (1 - t) * (2 - t) * (3 - t) := by
      have : 1 / 2 < 1 - t := by linarith
      have : 3 / 2 < 2 - t := by linarith
      have : 5 / 2 < 3 - t := by linarith
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) (by linarith : (0 : ℝ) < 2 - t)]
    have hsq : 1 + t ^ 2 < 2 := by nlinarith
    have habs := le_abs_self M
    have : M * (t * (1 + t ^ 2)) ≤ |M| * (t * 2) := by
      calc M * (t * (1 + t ^ 2)) ≤ |M| * (t * (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_right habs hd.le
        _ ≤ |M| * (t * 2) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq.le ht.le) (abs_nonneg M)
    nlinarith [abs_nonneg M]
  · refine ⟨6 + 4 * |M|, fun t ht => ?_⟩
    have ht6 : 6 < t := by linarith [abs_nonneg M]
    have hpos : 0 < t := by linarith
    have hd : 0 < 1 + t ^ 2 := by positivity
    have heq : -(t * ex17F3g t) = (t - 1) * (t - 2) * (t - 3) / (1 + t ^ 2) := by
      rw [ex17F3g]; field_simp; ring
    rw [heq, lt_div_iff₀ hd]
    have h12 : t ^ 2 / 2 ≤ (t - 1) * (t - 2) := by nlinarith
    have h3 : 4 * |M| < t - 3 := by linarith
    have hX : t ^ 2 / 2 * (t - 3) ≤ (t - 1) * (t - 2) * (t - 3) :=
      mul_le_mul_of_nonneg_right h12 (by linarith)
    have hMb : M * (1 + t ^ 2) ≤ |M| * (2 * t ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self M) hd.le).trans
        (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg M))
    nlinarith [abs_nonneg M, sq_nonneg t]

/-- `g'(2) = 1/10`. -/
theorem ex17F3g_hasDerivAt : HasDerivAt ex17F3g (1 / 10) 2 := by
  have hN : HasDerivAt (fun t : ℝ => (1 - t) * (2 - t) * (3 - t)) 1 2 := by
    have h := (((hasDerivAt_id (2 : ℝ)).const_sub 1).mul ((hasDerivAt_id (2 : ℝ)).const_sub 2)).mul
      ((hasDerivAt_id (2 : ℝ)).const_sub 3)
    convert h using 1
    · funext t; rfl
    · norm_num
  have hD : HasDerivAt (fun t : ℝ => t * (1 + t ^ 2)) 13 2 := by
    have h := (hasDerivAt_id (2 : ℝ)).mul (((hasDerivAt_id (2 : ℝ)).pow 2).const_add 1)
    convert h using 1
    · funext t; simp
    · simp; norm_num
  have h := hN.div hD (by norm_num)
  unfold ex17F3g
  convert h using 1
  norm_num

/-- **Example 17.F.3**, instance (MWG, p. 615): `(2, 1)` is a regular equilibrium of `ex17F3Z`
with index `-1`. -/
theorem ex17F3_index : IsRegularEqm ex17F3Z (vec1 2) ∧ eqmIndex ex17F3Z (vec1 2) = -1 := by
  have hnorm : normED ex17F3Z = fun q _ => ex17F3g (q 0) := by
    funext q l
    rw [Subsingleton.elim l 0]
    have h1 : (Fin.snoc (α := fun _ => ℝ) q 1 1 : ℝ) = 1 := rfl
    simp [normED, truncExcessDemand, normPrice, ex17F3Z, twoGoodED, h1]
  have hdiff : DifferentiableAt ℝ (normED ex17F3Z) (vec1 2) := by
    rw [hnorm]
    have hg : DifferentiableAt ℝ ex17F3g ((fun q : Fin 1 → ℝ => q 0) (vec1 2)) :=
      ex17F3g_hasDerivAt.differentiableAt
    have hc : DifferentiableAt ℝ (ex17F3g ∘ fun q : Fin 1 → ℝ => q 0) (vec1 2) :=
      hg.comp (vec1 2) (by fun_prop)
    exact differentiableAt_pi.2 fun _ => hc
  have hslope : slope2 ex17F3Z 2 = 1 / 10 := by
    have h := two_goods_hasDerivAt hdiff
    have hf : (fun s => ex17F3Z ![s, 1] 0) = ex17F3g := by
      funext s
      simp [ex17F3Z, twoGoodED]
    rw [hf] at h
    exact h.unique ex17F3g_hasDerivAt
  have heqm : IsNormEqm ex17F3Z (vec1 2) :=
    (isNormEqm_vec1_iff ex17F3Z_isStandard.walras).2 ⟨two_pos, by
      simp [ex17F3Z, twoGoodED, ex17F3g]⟩
  refine ⟨⟨heqm, hdiff, ?_⟩, ?_⟩
  · rw [det_eq_slope2, hslope]; norm_num
  · rw [eqmIndex_two]
    change -itgSgn (slope2 ex17F3Z 2) = -1
    rw [hslope, itgSgn_pos (by norm_num)]

/-- **Example 17.F.3**, instance (MWG, p. 615): since `(2, 1)` has index `-1`, `ex17F3Z` has
another normalized equilibrium. -/
theorem example_17_F_3_index_instance :
    ∃ q', IsNormEqm ex17F3Z q' ∧ q' ≠ vec1 2 :=
  example_17_F_3_index ex17F3Z_isStandard ex17F3_index.1 ex17F3_index.2

end MWG.PositiveEquilibriumTheory
