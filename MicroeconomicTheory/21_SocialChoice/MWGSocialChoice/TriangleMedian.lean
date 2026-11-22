/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.EuclideanExercises
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The uniform distribution on a triangle has no median

MWG, Example 21.D.6 and Figure 21.D.8(b), p. 806, and the nonexistence half of
Exercise 21.D.9(d), p. 814.

The median property is invariant under affine bijections: if `v + L x` is a median of the
uniform distribution on `v + L(S)`, then `x` is a median of the uniform distribution on `S`
(`isMedianPoint_of_affine_image`; the hyperplane with normal `q` through `x` is carried to the
one with normal `(L⁻¹)* q`, and Lebesgue measure is multiplied by `|det L|`). Every triangle
with nonempty interior is the image of the standard triangle
`{z : 0 < z₀, 0 < z₁, z₀ + z₁ < 1}` under such a map.

For the standard triangle, the line `z₀ = c` through a median must cut the triangle into two
pieces of area `1/4`: integrating, `(1 - c)² / 2 = 1/4` (`stdTriangle_median_coord`). The
coordinate swap and `z ↦ (1 - z₀ - z₁, z₁)` map the triangle onto itself, so the same holds for
the lines through the median parallel to the other two sides:
`(1 - x₀)² = (1 - x₁)² = (x₀ + x₁)² = 1/2` with all three bases positive, which forces
`1 - x₀ = x₀ + x₁ = 2(1 - x₀)`, impossible. Hence no point is a median
(`figure_21_D_8b`, for every triangle: `figure_21_D_8b_affine`), and a parameter density on
`ℝ²_{++}` need not have a median agent (`exercise_21_D_9d_not_exists`).

The triangle is taken open; the uniform distribution does not depend on the boundary (a null
set). Measures are not normalised; the median property is invariant under scaling.
-/

namespace MWG.SocialChoice

open MeasureTheory

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 806), affine invariance of medians. If `v + L x` is a median of
a Haar measure restricted to `v + L(S)`, then `x` is a median of its restriction to `S`. -/
theorem isMedianPoint_of_affine_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : E ≃ₗ[ℝ] E) (v : E) (S : Set E) (x : E)
    (h : IsMedianPoint (μ.restrict ((fun z => v + L z) '' S)) (v + L x)) :
    IsMedianPoint (μ.restrict S) x := by
  intro q hq
  set A : E →ₗ[ℝ] E := (L.symm : E →ₗ[ℝ] E) with hA
  set q' := LinearMap.adjoint A q with hq'def
  have hq' : q' ≠ 0 := by
    intro h0
    have e := LinearMap.adjoint_inner_right A (L q) q
    rw [← hq'def, h0, inner_zero_right] at e
    have e2 : ⟪q, q⟫ = 0 := by simpa [hA] using e.symm
    exact hq (inner_self_eq_zero.1 e2)
  have key := h q' hq'
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at key
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hpre : (fun z => v + L z) ⁻¹' openHalfSpace (v + L x) q' = openHalfSpace x q := by
    ext z
    simp only [openHalfSpace, Set.mem_preimage, Set.mem_ofPred_eq]
    have e : v + L z - (v + L x) = L (z - x) := by rw [map_sub]; abel
    rw [e, hq'def, LinearMap.adjoint_inner_right]
    simp [hA]
  have himg : openHalfSpace (v + L x) q' ∩ (fun z => v + L z) '' S =
      (fun z => v + L z) '' (openHalfSpace x q ∩ S) := by
    rw [Set.inter_comm, ← Set.image_inter_preimage, hpre, Set.inter_comm]
  have hmeas : ∀ T : Set E, μ ((fun z => v + L z) '' T) =
      ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * μ T := by
    intro T
    have e : (fun z => v + L z) '' T = (fun z => v + z) '' ((L : E →ₗ[ℝ] E) '' T) := by
      rw [Set.image_image]
      rfl
    rw [e, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap]
  rw [himg, hmeas, hmeas] at key
  have hd0 : ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (IsUnit.ne_zero L.isUnit_det')
  rw [mul_left_comm] at key
  exact (ENNReal.mul_le_mul_iff_right hd0 ENNReal.ofReal_ne_top).1 key

/-- The standard (open) triangle `{z : 0 < z₀, 0 < z₁, z₀ + z₁ < 1}` in the plane. -/
def stdTriangle : Set (EuclideanSpace ℝ (Fin 2)) := {z | 0 < z 0 ∧ 0 < z 1 ∧ z 0 + z 1 < 1}

/-- The coordinate map `z ↦ (z₀, z₁)` from the Euclidean plane to `ℝ × ℝ` preserves Lebesgue
measure. -/
theorem triangle_coords_measurePreserving :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- Area under the line `b = 1 - a` over `u < a < w`. -/
theorem triangle_strip_volume {u w : ℝ} (huw : u ≤ w) (hw : w ≤ 1) :
    volume (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) =
      ENNReal.ofReal ((w - u) - (w ^ 2 - u ^ 2) / 2) := by
  have hc : Continuous fun a : ℝ => 1 - a := continuous_const.sub continuous_id
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (continuous_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
    (hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo
    (fun a ha => by linarith [ha.2])]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huw]
  simp only [Pi.sub_apply, sub_zero]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- The standard triangle in coordinates: the region under `b = 1 - a` over `0 < a < 1`. -/
theorem stdTriangle_eq_preimage : stdTriangle = (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
    regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo 0 1) := by
  ext z
  simp only [stdTriangle, Set.mem_ofPred_eq, Set.mem_preimage, regionBetween, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  · rintro ⟨⟨h1, -⟩, h2, h3⟩
    exact ⟨h1, h2, by linarith⟩

/-- Through a median `x` of the uniform distribution on the standard triangle, the line
`z₀ = x₀` cuts the triangle into two pieces of equal area `1/4`: `0 < x₀ < 1` and
`(1 - x₀)² = 1/2`. -/
theorem stdTriangle_median_coord (x : EuclideanSpace ℝ (Fin 2))
    (h : IsMedianPoint (volume.restrict stdTriangle) x) :
    0 < x 0 ∧ x 0 < 1 ∧ (1 - x 0) ^ 2 = 1 / 2 := by
  set c := x 0 with hcdef
  set m := max 0 (min c 1) with hm
  have hm0 : 0 ≤ m := le_max_left _ _
  have hm1 : m ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hP := triangle_coords_measurePreserving
  have hR : ∀ u w : ℝ, MeasurableSet
      (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) := fun u w =>
    measurableSet_regionBetween measurable_const (measurable_const.sub measurable_id)
      measurableSet_Ioo
  have hup : openHalfSpace x (EuclideanSpace.single 0 1) ∩ stdTriangle =
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
        regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo m 1) := by
    ext z
    simp only [openHalfSpace, stdTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, regionBetween, Set.mem_Ioo, EuclideanSpace.inner_single_right,
      PiLp.sub_apply, one_mul, hm, max_lt_iff, min_lt_iff, RCLike.conj_to_real]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨h2, Or.inl (by linarith)⟩, by linarith⟩, h3, by linarith⟩
    · rintro ⟨⟨⟨h2, h5⟩, h6⟩, h3, h4⟩
      rcases h5 with h5 | h5
      · exact ⟨by linarith, h2, h3, by linarith⟩
      · exact absurd h6 (by linarith)
  have hlow : openHalfSpace x (-EuclideanSpace.single 0 1) ∩ stdTriangle =
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
        regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo 0 m) := by
    ext z
    simp only [openHalfSpace, stdTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, regionBetween, Set.mem_Ioo, inner_neg_right,
      EuclideanSpace.inner_single_right, PiLp.sub_apply, one_mul, hm, lt_max_iff, lt_min_iff,
      RCLike.conj_to_real]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h2, Or.inr ⟨by linarith, by linarith⟩⟩, h3, by linarith⟩
    · rintro ⟨⟨h2, h5⟩, h3, h4⟩
      rcases h5 with h5 | h5
      · exact absurd h2 (by linarith)
      · exact ⟨by linarith [h5.1], h2, h3, by linarith⟩
  have vol : ∀ u w : ℝ, volume ((fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
      regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) =
      volume (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) :=
    fun u w => hP.measure_preimage (hR u w).nullMeasurableSet
  have hq : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h0
    simp at this
  have h1 := h _ hq
  have h2 := h _ (neg_ne_zero.2 hq)
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hup, stdTriangle_eq_preimage,
    vol, vol, triangle_strip_volume hm1 le_rfl, triangle_strip_volume zero_le_one le_rfl,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hlow, stdTriangle_eq_preimage,
    vol, vol, triangle_strip_volume hm0 hm1, triangle_strip_volume zero_le_one le_rfl,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  have hsq : (1 - m) ^ 2 = 1 / 2 := by nlinarith
  have hmpos : 0 < m := by
    rcases eq_or_lt_of_le hm0 with e | e
    · rw [← e] at hsq
      norm_num at hsq
    · exact e
  have hmlt : m < 1 := by
    rcases eq_or_lt_of_le hm1 with e | e
    · rw [e] at hsq
      norm_num at hsq
    · exact e
  have hmc : m = c := by
    rcases le_total c 0 with hc | hc
    · have : m = 0 := by rw [hm]; exact max_eq_left (le_trans (min_le_left _ _) hc)
      linarith
    · rcases le_total c 1 with hc1 | hc1
      · rw [hm, min_eq_left hc1, max_eq_right hc]
      · have : m = 1 := by rw [hm, min_eq_right hc1, max_eq_right zero_le_one]
        linarith
  rw [← hmc]
  exact ⟨hmpos, hmlt, hsq⟩

/-- The coordinate swap of the plane, as a linear map. -/
def triSwapLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun z := WithLp.toLp 2 ![z 1, z 0]
  map_add' a b := by
    ext i
    fin_cases i <;> simp
  map_smul' r a := by
    ext i
    fin_cases i <;> simp

/-- The linear part `z ↦ (-z₀ - z₁, z₁)` of the reflection `z ↦ (1 - z₀ - z₁, z₁)` of the
standard triangle. -/
def triShearLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun z := WithLp.toLp 2 ![-z 0 - z 1, z 1]
  map_add' a b := by
    ext i
    fin_cases i
    all_goals simp
    all_goals ring
  map_smul' r a := by
    ext i
    fin_cases i
    all_goals simp
    all_goals ring

/-- The swap is an involution. -/
theorem triSwapLin_involutive : Function.Involutive triSwapLin := by
  intro z
  ext i
  fin_cases i <;> simp [triSwapLin]

/-- The shear is an involution. -/
theorem triShearLin_involutive : Function.Involutive triShearLin := by
  intro z
  ext i
  fin_cases i <;> simp [triShearLin]

/-- Through a median `x` of the uniform distribution on the standard triangle, each of the three
lines through `x` parallel to a side bisects the area. -/
theorem stdTriangle_median_three (x : EuclideanSpace ℝ (Fin 2))
    (h : IsMedianPoint (volume.restrict stdTriangle) x) :
    (0 < x 0 ∧ x 0 < 1 ∧ (1 - x 0) ^ 2 = 1 / 2) ∧ (0 < x 1 ∧ x 1 < 1 ∧ (1 - x 1) ^ 2 = 1 / 2) ∧
      (0 < 1 - x 0 - x 1 ∧ 1 - x 0 - x 1 < 1 ∧ (x 0 + x 1) ^ 2 = 1 / 2) := by
  refine ⟨stdTriangle_median_coord x h, ?_, ?_⟩
  · set L := LinearEquiv.ofInvolutive triSwapLin triSwapLin_involutive
    have hL : ∀ z, L z = triSwapLin z := fun z => rfl
    have himg : (fun z => 0 + L z) '' stdTriangle = stdTriangle := by
      ext z
      simp only [zero_add, hL, Set.mem_image]
      constructor
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp [triSwapLin] <;> linarith
      · rintro ⟨h1, h2, h3⟩
        refine ⟨triSwapLin z, ⟨?_, ?_, ?_⟩, triSwapLin_involutive z⟩ <;>
          simp [triSwapLin] <;> linarith
    have hx : 0 + L (triSwapLin x) = x := by rw [zero_add, hL, triSwapLin_involutive x]
    have hmed := isMedianPoint_of_affine_image volume L 0 stdTriangle (triSwapLin x)
      (by rw [himg, hx]; exact h)
    simpa [triSwapLin] using stdTriangle_median_coord _ hmed
  · set L := LinearEquiv.ofInvolutive triShearLin triShearLin_involutive
    have hL : ∀ z, L z = triShearLin z := fun z => rfl
    set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    have hv0 : v 0 = 1 := by simp [v]
    have hv1 : v 1 = 0 := by simp [v]
    have himg : (fun z => v + L z) '' stdTriangle = stdTriangle := by
      ext z
      simp only [hL, Set.mem_image]
      constructor
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp [triShearLin, hv0, hv1] <;> linarith
      · rintro ⟨h1, h2, h3⟩
        refine ⟨v + triShearLin z, ⟨?_, ?_, ?_⟩, ?_⟩
        · simp [triShearLin, hv0]
          linarith
        · simp [triShearLin, hv1]
          linarith
        · simp [triShearLin, hv0, hv1]
          linarith
        · ext i
          fin_cases i
          · simp [triShearLin, hv0, hv1]
            ring
          · simp [triShearLin, hv1]
    have hx : v + L (v + triShearLin x) = x := by
      rw [hL]
      ext i
      fin_cases i
      · simp [triShearLin, hv0, hv1]
        ring
      · simp [triShearLin, hv1]
    have hmed := isMedianPoint_of_affine_image volume L v stdTriangle (v + triShearLin x)
      (by rw [himg, hx]; exact h)
    have := stdTriangle_median_coord _ hmed
    simp only [PiLp.add_apply, hv0, triShearLin, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero] at this
    obtain ⟨a, b, e⟩ := this
    refine ⟨by linarith, by linarith, ?_⟩
    rw [← e]
    ring

/-- **Figure 21.D.8(b)** (MWG, p. 806). The uniform distribution on a triangle has no median:
"through any point of a triangle we can draw a line that divides it into two regions of unequal
area". Standard triangle. -/
theorem figure_21_D_8b (x : EuclideanSpace ℝ (Fin 2)) :
    ¬IsMedianPoint (volume.restrict stdTriangle) x := by
  intro h
  obtain ⟨⟨-, a1, e0⟩, ⟨b0, b1, e1⟩, ⟨c0, -, e2⟩⟩ := stdTriangle_median_three x h
  have hr : 1 - x 0 = 1 - x 1 := by
    have : (1 - x 0 - (1 - x 1)) * (1 - x 0 + (1 - x 1)) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hs : x 0 + x 1 = 1 - x 0 := by
    have : (x 0 + x 1 - (1 - x 0)) * (x 0 + x 1 + (1 - x 0)) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have : x 0 = 1 / 3 := by linarith
  rw [this] at e0
  norm_num at e0

/-- **Figure 21.D.8(b)** (MWG, p. 806), every triangle. The image of the standard triangle under
any affine bijection `z ↦ v + L z` (every triangle with nonempty interior is such an image)
carries a uniform distribution with no median. -/
theorem figure_21_D_8b_affine (L : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (v y : EuclideanSpace ℝ (Fin 2)) :
    ¬IsMedianPoint (volume.restrict ((fun z => v + L z) '' stdTriangle)) y := by
  intro h
  have hy : v + L (L.symm (y - v)) = y := by simp
  rw [← hy] at h
  exact figure_21_D_8b _ (isMedianPoint_of_affine_image volume L v stdTriangle _ h)

/-- **Exercise 21.D.9(d)** (MWG, p. 814), nonexistence half. For the uniform density of
parameters on the triangle with vertices `(1, 1)`, `(2, 1)`, `(1, 2)` inside `ℝ²_{++}`, no
`β*` is a median agent. -/
theorem exercise_21_D_9d_not_exists :
    (fun z => EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 + z) '' stdTriangle ⊆
        {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 < z i} ∧
      ∀ β : EuclideanSpace ℝ (Fin 2), ¬IsMedianPoint (volume.restrict
        ((fun z => EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 + z) '' stdTriangle))
        β := by
  refine ⟨?_, fun β => ?_⟩
  · rintro _ ⟨w, ⟨h1, h2, -⟩, rfl⟩ i
    fin_cases i
    · simp
      linarith
    · simp
      linarith
  · have := figure_21_D_8b_affine (LinearEquiv.refl ℝ _)
      (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) β
    simpa using this

end MWG.SocialChoice
