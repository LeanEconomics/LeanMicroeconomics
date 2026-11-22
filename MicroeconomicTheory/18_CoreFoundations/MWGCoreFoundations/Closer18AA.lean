/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.ShapleyExamples
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Closing Appendix A items: cross partials (Example 18.AA.8, Exercise 18.AA.7) and closedness
of `V(S)` (Example 18.AA.1) (MWG pp. 675, 683, 686)

Example 18.AA.8 assumes `∂²f(z)/∂z_h∂z_k ≥ 0` for all `z` and all `h, k` and Exercise 18.AA.7
asks to show that the production game `v(S) = f(∑_{i∈S} ωᵢ)` is convex. `ShapleyExamples` proves
the game convex under increasing differences (`exercise_18_AA_7`) and derives increasing
differences from the second-derivative condition only for `N = 1`. Here the step is proved for
every `N`:

* `c18_partial_mono`: if `f` is `C²` on an open set `U ⊇ ℝ^N₊` and every second partial
  `∂(∂f/∂z_k)/∂z_h` is nonnegative on `ℝ^N₊`, then every first partial `∂f/∂z_k` is nondecreasing
  along nonnegative directions in `ℝ^N₊` (mean value theorem along the segment `x + s a`);
* `c18_fderiv_mono`: hence `Df(y) d ≤ Df(y + a) d` for `y, a, d ≥ 0`;
* `example_18_AA_8_increasingDifferences`: hence `f` has increasing differences on `ℝ^N₊`
  (mean value theorem along `z + t (z' - z)`);
* `exercise_18_AA_7_crossPartials`: the production game is convex, under the book's hypothesis;
* `c18_product_crossPartials`: an instance, `f(z) = z₁z₂` on `ℝ²`
  (`exercise_18_AA_7_product`).

Example 18.AA.1 (p. 675) asserts that `V(S)` is a utility possibility set; closedness fails for
non-closed `Y` (`example_18_AA_1_not_closed` in `CoopGames`) and was proved there only for closed
`Y ⊆ -ℝ^L₊`. Here:

* `c18_cone_bounded`: in a closed cone `Y` with `Y ∩ ℝ^L₊ = {0}`, `{y ∈ Y : y ≥ -c}` is bounded
  (the negative-part sum `∑ min(y_l, 0)` has a negative maximum on `Y ∩ S^{L-1}`);
* `example_18_AA_1_closed_cone`, `example_18_AA_1_closed_crs`: `V(S)` is closed for every closed
  (convex) constant returns technology with no free production and continuous utilities;
  instance `example_18_AA_1_closed_halfPlane` (`Y = {y₁ + y₂ ≤ 0}`, not inside `-ℝ²₊`);
* `example_18_AA_1_free_production`: the hypothesis `Y ∩ ℝ^L₊ = {0}` cannot be dropped (`Y = ℝ₊`,
  `u(x) = 1 - 1/(1 + x)`, `V = {w < 1}`).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice

/-- **Example 18.AA.8** (MWG, p. 683). The partial derivative `∂f/∂z_k (y) = Df(y) e_k`. -/
noncomputable def c18Partial {N : ℕ} (f : (Fin N → ℝ) → ℝ) (k : Fin N) (y : Fin N → ℝ) : ℝ :=
  fderiv ℝ f y (Pi.single k 1)

/-- A vector is the sum of its coordinates times the unit vectors. -/
theorem c18_eq_sum_single {N : ℕ} (a : Fin N → ℝ) : a = ∑ h, a h • Pi.single h (1 : ℝ) := by
  ext l
  simp [Finset.sum_apply, Pi.single_apply]

/-- A linear functional in coordinates: `L a = ∑_h a_h L(e_h)`. -/
theorem c18_clm_apply_eq_sum {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) (a : Fin N → ℝ) :
    L a = ∑ h, a h * L (Pi.single h 1) := by
  conv_lhs => rw [c18_eq_sum_single a]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- A `C²` function on an open set has differentiable partial derivatives there. -/
theorem c18_partial_differentiableAt {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (k : Fin N) {y : Fin N → ℝ} (hy : y ∈ U) :
    DifferentiableAt ℝ (c18Partial f k) y := by
  have h2 : ContDiffAt ℝ 2 f y := hf.contDiffAt (hU.mem_nhds hy)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := h2.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)

/-- The derivative of `s ↦ F(x + s a)`. -/
theorem c18_hasDerivAt_line {N : ℕ} {F : (Fin N → ℝ) → ℝ} {x a : Fin N → ℝ} {s : ℝ}
    (hF : DifferentiableAt ℝ F (x + s • a)) :
    HasDerivAt (fun s : ℝ => F (x + s • a)) (fderiv ℝ F (x + s • a) a) s := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  exact hF.hasFDerivAt.comp_hasDerivAt s hγ

/-- Points `x + s a` with `x, a ≥ 0`, `s ≥ 0` are in the orthant. -/
theorem c18_line_mem {N : ℕ} {x a : Fin N → ℝ} (hx : x ∈ nonnegOrthant N)
    (ha : a ∈ nonnegOrthant N) {s : ℝ} (hs : 0 ≤ s) : x + s • a ∈ nonnegOrthant N := fun l => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (hx l) (mul_nonneg hs (ha l))

/-- **Example 18.AA.8** (MWG, p. 683), first step. If `f` is `C²` on an open `U ⊇ ℝ^N₊` and all
second partials `∂(∂f/∂z_k)/∂z_h` are nonnegative on `ℝ^N₊`, then each partial `∂f/∂z_k` is
nondecreasing along nonnegative directions: `∂f/∂z_k (x) ≤ ∂f/∂z_k (x + a)` for `x, a ≥ 0`. -/
theorem c18_partial_mono {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    (k : Fin N) {x a : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (ha : a ∈ nonnegOrthant N) :
    c18Partial f k x ≤ c18Partial f k (x + a) := by
  have hdiff : ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ (c18Partial f k) (x + s • a) := fun s hs =>
    c18_partial_differentiableAt hU hf k (hsub (c18_line_mem hx ha hs))
  have hmono : MonotoneOn (fun s : ℝ => c18Partial f k (x + s • a)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => fderiv ℝ (c18Partial f k) (x + s • a) a)
      (fun s hs => (c18_hasDerivAt_line (hdiff s hs)).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (c18_hasDerivAt_line (hdiff s (le_of_lt hs))).hasDerivWithinAt
    · rw [interior_Ici] at hs
      rw [c18_clm_apply_eq_sum]
      refine Finset.sum_nonneg fun h _ => ?_
      exact mul_nonneg (ha h) (hcross _ (c18_line_mem hx ha (le_of_lt hs)) h k)
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simpa using h

/-- **Example 18.AA.8** (MWG, p. 683), second step. Under the hypotheses of `c18_partial_mono`,
`Df(y) d ≤ Df(y + a) d` for `y, a, d ≥ 0`. -/
theorem c18_fderiv_mono {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    {y a d : Fin N → ℝ} (hy : y ∈ nonnegOrthant N) (ha : a ∈ nonnegOrthant N)
    (hd : d ∈ nonnegOrthant N) : fderiv ℝ f y d ≤ fderiv ℝ f (y + a) d := by
  rw [c18_clm_apply_eq_sum (fderiv ℝ f y), c18_clm_apply_eq_sum (fderiv ℝ f (y + a))]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (c18_partial_mono hU hsub hf hcross k hy ha) (hd k)

/-- **Example 18.AA.8** (MWG, p. 683), the book's hypothesis. If `f` is `C²` on an open set
containing `ℝ^N₊` and `∂²f(z)/∂z_h∂z_k ≥ 0` for all `z ∈ ℝ^N₊` and all `h, k`, then `f` has
increasing differences on `ℝ^N₊`: `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'`,
`a ≥ 0`. -/
theorem example_18_AA_8_increasingDifferences {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1)) :
    IncreasingDifferences f := by
  intro z z' a hz hzz ha
  set d := z' - z with hd
  have hd0 : d ∈ nonnegOrthant N := fun l => by
    simp only [hd, Pi.sub_apply]; linarith [hzz l]
  have hfd : ∀ y ∈ nonnegOrthant N, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hsub hy))
  have hmem : ∀ s : ℝ, 0 ≤ s → z + s • d ∈ nonnegOrthant N := fun s hs => c18_line_mem hz hd0 hs
  have hmem' : ∀ s : ℝ, 0 ≤ s → (z + a) + s • d ∈ nonnegOrthant N := fun s hs =>
    c18_line_mem (fun l => add_nonneg (hz l) (ha l)) hd0 hs
  have hder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun s : ℝ => f ((z + a) + s • d) - f (z + s • d))
      (fderiv ℝ f ((z + a) + s • d) d - fderiv ℝ f (z + s • d) d) s := fun s hs =>
    (c18_hasDerivAt_line (hfd _ (hmem' s hs))).sub (c18_hasDerivAt_line (hfd _ (hmem s hs)))
  have hmono : MonotoneOn (fun s : ℝ => f ((z + a) + s • d) - f (z + s • d)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => fderiv ℝ f ((z + a) + s • d) d - fderiv ℝ f (z + s • d) d)
      (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (hder s (le_of_lt hs)).hasDerivWithinAt
    · rw [interior_Ici] at hs
      have e : (z + a) + s • d = (z + s • d) + a := by abel
      rw [e, sub_nonneg]
      exact c18_fderiv_mono hU hsub hf hcross (hmem s (le_of_lt hs)) ha hd0
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  have e1 : z + (1 : ℝ) • d = z' := by rw [one_smul, hd]; abel
  have e2 : (z + a) + (1 : ℝ) • d = z' + a := by rw [one_smul, hd]; abel
  simp only [zero_smul, add_zero] at h
  rw [e1, e2] at h
  exact h

/-- **Exercise 18.AA.7** (MWG, p. 686), with the hypothesis of Example 18.AA.8 as printed: if `f`
is `C²` on an open set containing `ℝ^N₊` with `∂²f/∂z_h∂z_k ≥ 0` on `ℝ^N₊` for all `h, k`, and
`ωᵢ ∈ ℝ^N₊`, then the production game `v(S) = f(∑_{i∈S} ωᵢ)` is convex. -/
theorem exercise_18_AA_7_crossPartials {n N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    {ω : Fin n → Fin N → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (inputGame f ω) :=
  exercise_18_AA_7 (example_18_AA_8_increasingDifferences hU hsub hf hcross) hω

/-- **Example 18.AA.8** (MWG, p. 683), an instance of the hypotheses: `f(z) = z₁z₂` on `ℝ²` is
`C²` (on the open set `ℝ²`) and every second partial `∂(∂f/∂z_k)/∂z_h` is `0` or `1`, so
nonnegative. -/
theorem c18_product_crossPartials :
    IsOpen (Set.univ : Set (Fin 2 → ℝ)) ∧ nonnegOrthant 2 ⊆ Set.univ ∧
      ContDiffOn ℝ 2 (fun z : Fin 2 → ℝ => z 0 * z 1) Set.univ ∧
      ∀ z ∈ nonnegOrthant 2, ∀ h k : Fin 2,
        0 ≤ fderiv ℝ (c18Partial (fun z : Fin 2 → ℝ => z 0 * z 1) k) z (Pi.single h 1) := by
  refine ⟨isOpen_univ, Set.subset_univ _, ?_, fun z _ h k => ?_⟩
  · exact ((contDiff_apply ℝ ℝ (0 : Fin 2)).mul (contDiff_apply ℝ ℝ (1 : Fin 2))).contDiffOn
  · have hf : ∀ y : Fin 2 → ℝ, fderiv ℝ (fun z : Fin 2 → ℝ => z 0 * z 1) y =
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
          y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 := fun y =>
      ((hasFDerivAt_apply (0 : Fin 2) y).mul (hasFDerivAt_apply (1 : Fin 2) y)).fderiv
    set L : (Fin 2 → ℝ) →L[ℝ] ℝ := Pi.single (M := fun _ : Fin 2 => ℝ) k 1 1 •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      Pi.single (M := fun _ : Fin 2 => ℝ) k 1 0 •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 with hL
    have hP : c18Partial (fun z : Fin 2 → ℝ => z 0 * z 1) k = L := by
      funext y
      simp only [c18Partial, hf, hL, FunLike.coe_add, FunLike.coe_smul,
        Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [hP, L.fderiv]
    simp only [hL, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hs : ∀ (j l : Fin 2), 0 ≤ Pi.single (M := fun _ : Fin 2 => ℝ) j 1 l := fun j l => by
      simp only [Pi.single_apply]; split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg (hs _ _) (hs _ _)) (mul_nonneg (hs _ _) (hs _ _))

/-- **Exercise 18.AA.7** (MWG, p. 686), instance: the production game of `f(z) = z₁z₂` with any
endowments `ωᵢ ∈ ℝ²₊` is convex, by `exercise_18_AA_7_crossPartials`. -/
theorem exercise_18_AA_7_product {n : ℕ} {ω : Fin n → Fin 2 → ℝ} (hω : ∀ i, 0 ≤ ω i) :
    IsConvexGame (inputGame (fun z : Fin 2 → ℝ => z 0 * z 1) ω) :=
  exercise_18_AA_7_crossPartials c18_product_crossPartials.1 c18_product_crossPartials.2.1
    c18_product_crossPartials.2.2.1 c18_product_crossPartials.2.2.2 hω

/-! ### Example 18.AA.1: closedness of `V(S)` for a closed cone with no free production -/

/-- The sum of the negative parts `∑_l min(y_l, 0)` of a vector. -/
noncomputable def c18NegSum {L : ℕ} (y : Fin L → ℝ) : ℝ := ∑ l, min (y l) 0

theorem c18NegSum_continuous {L : ℕ} : Continuous (c18NegSum (L := L)) :=
  continuous_finsetSum _ fun l _ => (continuous_apply l).min continuous_const

theorem c18NegSum_smul {L : ℕ} {t : ℝ} (ht : 0 ≤ t) (y : Fin L → ℝ) :
    c18NegSum (t • y) = t * c18NegSum y := by
  simp only [c18NegSum, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_zero t, ← mul_min_of_nonneg _ _ ht, mul_zero]

/-- **Example 18.AA.1** (MWG, p. 675), boundedness lemma. If `Y` is a closed cone with
`Y ∩ ℝ^L₊ = {0}` (no free production), then for every `c` the vectors `y ∈ Y` with `y ≥ -c` are
bounded. -/
theorem c18_cone_bounded {L : ℕ} {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y)
    (hcone : ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0) (c : Fin L → ℝ) :
    ∃ B : ℝ, ∀ y ∈ Y, (∀ l, -c l ≤ y l) → ‖y‖ ≤ B := by
  set K := Y ∩ Metric.sphere (0 : Fin L → ℝ) 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left hYc
  have hnorm : ∀ y ∈ Y, y ≠ 0 → ‖y‖⁻¹ • y ∈ K := fun y hy hne =>
    ⟨hcone y hy _ (inv_nonneg.2 (norm_nonneg y)), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]⟩
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, fun y hy _ => ?_⟩
    by_contra hlt
    have hne : y ≠ 0 := fun h => hlt (by simp [h])
    have := hnorm y hy hne
    rw [hKe] at this
    exact this
  obtain ⟨y₀, hy₀K, hmax⟩ := hKc.exists_isMaxOn hKne c18NegSum_continuous.continuousOn
  have hy₀ne : y₀ ≠ 0 := fun h => by
    have := hy₀K.2
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  have hm : c18NegSum y₀ < 0 := by
    have hnot : ¬ y₀ ∈ nonnegOrthant L := fun h => hy₀ne (hpos y₀ hy₀K.1 h)
    simp only [nonnegOrthant, Set.mem_ofPred_eq, not_forall, not_le] at hnot
    obtain ⟨l, hl⟩ := hnot
    have h1 : ∑ l', min (y₀ l') 0 ≤ min (y₀ l) 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
      have : ∑ l' ∈ Finset.univ.erase l, min (y₀ l') 0 ≤ 0 :=
        Finset.sum_nonpos fun l' _ => min_le_right _ _
      linarith
    simp only [c18NegSum]
    linarith [min_eq_left hl.le, h1]
  set C : ℝ := -∑ l, min (-c l) 0 with hC
  refine ⟨C / (-c18NegSum y₀), fun y hy hyc => ?_⟩
  rcases eq_or_ne y 0 with rfl | hne
  · rw [norm_zero]
    refine div_nonneg ?_ (by linarith)
    rw [hC, neg_nonneg]
    exact Finset.sum_nonpos fun l _ => min_le_right _ _
  have h1 : c18NegSum (‖y‖⁻¹ • y) ≤ c18NegSum y₀ := hmax (hnorm y hy hne)
  rw [c18NegSum_smul (inv_nonneg.2 (norm_nonneg y))] at h1
  have h2 : -C ≤ c18NegSum y := by
    rw [hC, neg_neg]
    exact Finset.sum_le_sum fun l _ => min_le_min_right 0 (hyc l)
  have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hne
  have h3 : c18NegSum y ≤ ‖y‖ * c18NegSum y₀ := by
    have := mul_le_mul_of_nonneg_left h1 hnpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at this
  rw [le_div_iff₀ (by linarith)]
  nlinarith

open Filter Topology in
/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness for a general technology: if `Y` is a
closed cone with no free production (`Y ∩ ℝ^L₊ = {0}`) and the utilities are continuous on
`ℝ^L₊`, then every `V(S)` is closed. This extends `example_18_AA_1_closed` (closed
`Y ⊆ -ℝ^L₊`); without closedness the claim fails (`example_18_AA_1_not_closed`), and without
`Y ∩ ℝ^L₊ = {0}` too (`example_18_AA_1_free_production`). Convexity of `Y` and `ωᵢ ≥ 0` are not
needed. -/
theorem example_18_AA_1_closed_cone {n L : ℕ} {u : Fin n → (Fin L → ℝ) → ℝ}
    {ω : Fin n → Fin L → ℝ} {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y)
    (hcone : ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) := by
  classical
  obtain ⟨B, hB⟩ := c18_cone_bounded hYc hcone hpos (∑ j ∈ S, ω j)
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨ws, hws, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose x hx hy hux using hws
  choose y hyY hsum using hy
  have hyc : ∀ k, ∀ l, -(∑ j ∈ S, ω j) l ≤ y k l := fun k l => by
    have h2 := congrFun (hsum k) l
    have h4 : 0 ≤ ∑ j ∈ S, x k j l := Finset.sum_nonneg fun j hj => hx k j hj l
    simp only [Finset.sum_apply, Pi.add_apply] at h2 ⊢
    linarith
  have hyB : ∀ k l, y k l ≤ B := fun k l =>
    (le_abs_self _).trans ((norm_le_pi_norm (y k) l).trans (hB _ (hyY k) (hyc k)))
  set M : Fin n → Fin L → ℝ := fun _ l => (∑ j ∈ S, ω j) l + B with hM
  set xt : ℕ → Fin n → Fin L → ℝ := fun k i => if i ∈ S then x k i else 0 with hxt
  have hxtS : ∀ k, ∀ i ∈ S, xt k i = x k i := fun k i hi => by simp [hxt, hi]
  have hbox : ∀ k, xt k ∈ Set.Icc (0 : Fin n → Fin L → ℝ) M := by
    intro k
    refine ⟨fun i l => ?_, fun i l => ?_⟩
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]; exact hx k i hi l
      · simp [hxt, hi]
    · have h2 := congrFun (hsum k) l
      simp only [Finset.sum_apply, Pi.add_apply] at h2
      have h3 := hyB k l
      have h5 := hyc k l
      simp only [Finset.sum_apply] at h5
      by_cases hi : i ∈ S
      · rw [hxtS k i hi]
        have h1 : x k i l ≤ ∑ j ∈ S, x k j l :=
          Finset.single_le_sum (f := fun j => x k j l) (fun j hj => hx k j hj l) hi
        simp only [hM, Finset.sum_apply]
        linarith
      · simp only [hxt, hi, ↓reduceIte, hM, Pi.zero_apply, Finset.sum_apply]
        linarith
  obtain ⟨xb, hxb, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hbox
  have hcoord : ∀ i, Tendsto (fun k => xt (φ k) i) atTop (𝓝 (xb i)) :=
    fun i => tendsto_pi_nhds.1 hconv i
  have hxbnn : ∀ i, xb i ∈ nonnegOrthant L := fun i l => hxb.1 i l
  refine ⟨xb, fun i _ => hxbnn i, ⟨∑ i ∈ S, xb i - ∑ i ∈ S, ω i, ?_, by abel⟩, fun i hi => ?_⟩
  · refine hYc.mem_of_tendsto (f := fun k => y (φ k)) (b := atTop) ?_
      (Eventually.of_forall fun k => hyY _)
    have hy' : (fun k => y (φ k)) = fun k => ∑ i ∈ S, xt (φ k) i - ∑ i ∈ S, ω i := by
      funext k
      rw [Finset.sum_congr rfl fun i hi => hxtS (φ k) i hi, hsum (φ k)]
      abel
    rw [hy']
    exact (tendsto_finsetSum S fun i _ => hcoord i).sub tendsto_const_nhds
  · have hwl : Tendsto (fun k => ws (φ k) i) atTop (𝓝 (w i)) :=
      (tendsto_pi_nhds.1 hlim i).comp hφ.tendsto_atTop
    have hul : Tendsto (fun k => u i (xt (φ k) i)) atTop (𝓝 (u i (xb i))) :=
      ((hu i) (xb i) (hxbnn i)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hcoord i, Eventually.of_forall fun k l =>
          (hbox (φ k)).1 i l⟩)
    refine le_of_tendsto_of_tendsto hwl hul (Eventually.of_forall fun k => ?_)
    simp only [hxtS (φ k) i hi]
    exact hux (φ k) i hi

/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness under the book's hypotheses on `Y`: a
closed convex constant returns technology with no free production. -/
theorem example_18_AA_1_closed_crs {n L : ℕ} {u : Fin n → (Fin L → ℝ) → ℝ}
    {ω : Fin n → Fin L → ℝ} {Y : Set (Fin L → ℝ)} (hY : IsCRSTechnology Y) (hYc : IsClosed Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) :=
  example_18_AA_1_closed_cone hYc hY.2.2 hpos hu S

/-- **Example 18.AA.1**, an instance beyond `Y ⊆ -ℝ^L₊`: the half-plane `{y : y₁ + y₂ ≤ 0}`
(which contains `(1, -1)`). -/
def c18HalfPlane : Set (Fin 2 → ℝ) := {y | y 0 + y 1 ≤ 0}

/-- **Example 18.AA.1**, instance: the half-plane technology is a closed convex constant returns
technology with no free production, not contained in `-ℝ²₊`. -/
theorem c18HalfPlane_hyp : IsCRSTechnology c18HalfPlane ∧ IsClosed c18HalfPlane ∧
    (∀ y ∈ c18HalfPlane, y ∈ nonnegOrthant 2 → y = 0) ∧
      ¬ c18HalfPlane ⊆ MWG.WelfareTheorems.nonposOrthant 2 := by
  refine ⟨⟨?_, ?_, fun y hy t ht => ?_⟩, ?_, fun y hy hy0 => ?_, fun h => ?_⟩
  · intro a ha b hb s t hs ht _
    simp only [c18HalfPlane, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ -(a 0 + a 1)),
      mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(b 0 + b 1))]
  · simp [c18HalfPlane]
  · simp only [c18HalfPlane, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(y 0 + y 1))]
  · exact isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const
  · simp only [c18HalfPlane, Set.mem_ofPred_eq] at hy
    have h0 := hy0 0
    have h1 := hy0 1
    funext l
    fin_cases l <;> simp <;> linarith
  · have := h (show (![1, -1] : Fin 2 → ℝ) ∈ c18HalfPlane by simp [c18HalfPlane]) 0
    norm_num at this

/-- **Example 18.AA.1**, instance of `example_18_AA_1_closed_crs`: with the half-plane technology,
`V(S)` is closed for any continuous utilities, e.g. `u(x) = x₁ + x₂`. -/
theorem example_18_AA_1_closed_halfPlane {n : ℕ} (ω : Fin n → Fin 2 → ℝ) (S : Finset (Fin n)) :
    IsClosed (econGame (fun _ x => x 0 + x 1) ω c18HalfPlane S) :=
  example_18_AA_1_closed_crs c18HalfPlane_hyp.1 c18HalfPlane_hyp.2.1 c18HalfPlane_hyp.2.2.1
    (fun _ => ((continuous_apply 0).add (continuous_apply 1)).continuousOn) S

/-- **Example 18.AA.1** (MWG, p. 675), the hypothesis `Y ∩ ℝ^L₊ = {0}` cannot be dropped: with
`L = 1`, the closed convex cone `Y = ℝ₊` (free production), one consumer with `ω = 0` and the
continuous, strictly increasing, concave utility `u(x) = 1 - 1/(1 + x)`, `V(I) = {w : w < 1}`,
which is not closed. -/
theorem example_18_AA_1_free_production :
    IsCRSTechnology (nonnegOrthant 1) ∧ IsClosed (nonnegOrthant 1) ∧
      ConcaveOn ℝ (nonnegOrthant 1) (fun x : Fin 1 → ℝ => 1 - 1 / (1 + x 0)) ∧
      StrictMonoOn (fun t : ℝ => 1 - 1 / (1 + t)) (Set.Ici 0) ∧
      ContinuousOn (fun x : Fin 1 → ℝ => 1 - 1 / (1 + x 0)) (nonnegOrthant 1) ∧
      econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0) (nonnegOrthant 1)
        Finset.univ = {w | w 0 < 1} ∧
      ¬ IsClosed (econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0)
        (nonnegOrthant 1) Finset.univ) := by
  have hV : econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0) (nonnegOrthant 1)
      Finset.univ = {w | w 0 < 1} := by
    ext w
    simp only [econGame, Finset.mem_univ, true_implies, Fin.sum_univ_one, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, -, hu⟩
      have h0 := hx 0 0
      have hw := hu 0
      have : 0 < 1 / (1 + x 0 0) := by positivity
      linarith
    · intro hw
      set t : ℝ := max (1 / (1 - w 0) - 1) 0 with ht
      have h1w : 0 < 1 - w 0 := by linarith
      refine ⟨fun _ => fun _ => t, fun _ _ => le_max_right _ _, ⟨fun _ => t, fun _ =>
        le_max_right _ _, by simp⟩, fun j => ?_⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only
      have hge : 1 / (1 - w 0) ≤ 1 + t := by
        rw [ht]; linarith [le_max_left (1 / (1 - w 0) - 1) 0]
      have hpos : 0 < 1 + t := by linarith [le_max_right (1 / (1 - w 0) - 1) 0]
      have : 1 / (1 + t) ≤ 1 - w 0 := by
        rw [div_le_iff₀ hpos]
        rw [div_le_iff₀ h1w] at hge
        linarith
      linarith
  refine ⟨⟨convex_nonnegOrthant 1, fun _ => le_rfl, fun y hy t ht l => ?_⟩,
    ?_, ?_, ?_, ?_, hV, fun hcl => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht (hy l)
  · have e : nonnegOrthant 1 = ⋂ l : Fin 1, {y : Fin 1 → ℝ | 0 ≤ y l} := by
      ext y; simp [nonnegOrthant]
    rw [e]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  · refine ⟨convex_nonnegOrthant 1, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hx0 := hx 0
    have hy0 := hy 0
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h1 : 0 < 1 + x 0 := by linarith
    have h2 : 0 < 1 + y 0 := by linarith
    have h3 : 0 < 1 + (a * x 0 + (1 - a) * y 0) := by nlinarith
    have key : 1 / (1 + (a * x 0 + (1 - a) * y 0)) ≤ a / (1 + x 0) + (1 - a) / (1 + y 0) := by
      rw [div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀ h3 (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]
    have e : a * (1 - 1 / (1 + x 0)) + (1 - a) * (1 - 1 / (1 + y 0)) =
        1 - (a / (1 + x 0) + (1 - a) / (1 + y 0)) := by ring
    rw [e]
    linarith
  · intro s hs t htt hst
    simp only [Set.mem_Ici] at hs htt
    have h1 : 0 < 1 + s := by linarith
    have : 1 / (1 + t) < 1 / (1 + s) := one_div_lt_one_div_of_lt h1 (by linarith)
    linarith
  · refine ContinuousOn.sub continuousOn_const (ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuous_apply 0).continuousOn) fun x hx => ?_)
    have := hx 0
    linarith
  · rw [hV] at hcl
    have hc : IsClosed (Set.Iio (1 : ℝ)) := by
      have : Set.Iio (1 : ℝ) = (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' {w | w 0 < 1} := by
        ext t; simp
      rw [this]; exact hcl.preimage (continuous_pi fun _ => continuous_id)
    have := hc.closure_eq
    rw [closure_Iio] at this
    have h1 : (1 : ℝ) ∈ Set.Iic (1 : ℝ) := Set.mem_Iic.2 le_rfl
    rw [this] at h1
    exact lt_irrefl _ (Set.mem_Iio.1 h1)

end MWG.CoreFoundations
