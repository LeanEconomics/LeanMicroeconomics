/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Appendix A: nonconvexities and the theory of externalities (MWG, pp. 374-377)

* **Example 11.AA.1** (positive externalities as a source of increasing returns). Firm 2's
  production `q = h^β z^α`, input price `1`. For `0 < α < 1` its maximized profit is
  `π₂(h) = γ h^{β/(1-α)}` with `γ = (1 - α) α^{α/(1-α)} > 0` (`example_11_AA_1`), its problem in
  `z` is concave, and `π₂` is convex when `α + β ≥ 1` and not concave when `α + β > 1`. MWG allows
  `α ∈ [0, 1]`; the formula also holds at `α = 0` (`example_11_AA_1_alpha_zero`), but at `α = 1`
  profit is unbounded for `h > 1` (`example_11_AA_1_alpha_one`; correction).
* **Example 11.AA.2** (negative externalities as a source of nonconvexities, Starrett): a
  differentiable profit function that is nonnegative (shutdown is possible) and strictly
  decreasing somewhere cannot be concave on `[0, ∞)` (`example_11_AA_2`); an instance.
* **Example 11.AA.3** (multiple local social optima): `π₁(h) = min(h, 1)`,
  `π₂(h) = 2(1 - h)²` for `h ≤ 1` and `0` beyond. The social optimum is `h = 0` (joint profit `2`),
  implemented by any tax `t > 1`; `h = 1` is a local optimum and surplus exceeds its value only for
  `h < 1/2`. MWG says `h = 1` satisfies the first- and second-order conditions; in fact surplus is
  not differentiable at `h = 1` (left derivative `1`, right derivative `0`), and a zero tax leaves
  firm 1 indifferent among all `h ≥ 1` (correction).
-/

namespace MWG.ExternalitiesPublicGoods

/-! ## Example 11.AA.1 -/

/-- The constant `γ = (1 - α) α^{α/(1-α)}` of Example 11.AA.1. -/
noncomputable def aa1Gamma (α : ℝ) : ℝ := (1 - α) * α ^ (α / (1 - α))

/-- **Example 11.AA.1** (MWG, p. 375). For `0 < α < 1`, `h ≥ 0`: every input level `z ≥ 0` gives
firm 2 profit `h^β z^α - z ≤ γ h^{β/(1-α)}`, with equality at `z* = (α h^β)^{1/(1-α)}`; so its
derived profit function is `π₂(h) = γ h^{β/(1-α)}`, and `γ > 0`. -/
theorem example_11_AA_1 {α β h : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hh : 0 ≤ h) :
    (∀ z, 0 ≤ z → h ^ β * z ^ α - z ≤ aa1Gamma α * h ^ (β / (1 - α))) ∧
      h ^ β * ((α * h ^ β) ^ (1 - α)⁻¹) ^ α - (α * h ^ β) ^ (1 - α)⁻¹ =
        aa1Gamma α * h ^ (β / (1 - α)) ∧ 0 < aa1Gamma α := by
  have h1α : 0 < 1 - α := by linarith
  set A := h ^ β with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg hh β
  -- `M = (α^α A)^{1/(1-α)}`
  set M := (α ^ α * A) ^ (1 - α)⁻¹ with hM
  have hαα : 0 < α ^ α := Real.rpow_pos_of_pos hα0 α
  have hM0 : 0 ≤ M := Real.rpow_nonneg (mul_nonneg hαα.le hA0) _
  have hMpow : M ^ (1 - α) = α ^ α * A := Real.rpow_inv_rpow (mul_nonneg hαα.le hA0) h1α.ne'
  have hMeq : M = α ^ (α / (1 - α)) * h ^ (β / (1 - α)) := by
    rw [hM, Real.mul_rpow hαα.le hA0, ← Real.rpow_mul hα0.le, hA, ← Real.rpow_mul hh,
      div_eq_mul_inv, div_eq_mul_inv]
  have hval : (1 - α) * M = aa1Gamma α * h ^ (β / (1 - α)) := by
    rw [hMeq, aa1Gamma]; ring
  refine ⟨fun z hz => ?_, ?_, mul_pos h1α (Real.rpow_pos_of_pos hα0 _)⟩
  · have hgm := Real.geom_mean_le_arith_mean2_weighted hα0.le h1α.le (div_nonneg hz hα0.le) hM0
      (by ring : α + (1 - α) = 1)
    have hlhs : (z / α) ^ α * M ^ (1 - α) = A * z ^ α := by
      rw [hMpow, Real.div_rpow hz hα0.le]
      field_simp
    rw [hlhs] at hgm
    have : α * (z / α) = z := by field_simp
    rw [this] at hgm
    rw [← hval]
    linarith
  · -- the optimal input `z* = α M`
    have hz : (α * A) ^ (1 - α)⁻¹ = α * M := by
      rw [hM, Real.mul_rpow hαα.le hA0, Real.mul_rpow hα0.le hA0, ← Real.rpow_mul hα0.le]
      have : α ^ (α * (1 - α)⁻¹) = α ^ ((1 - α)⁻¹ - 1) := by
        congr 1; field_simp; ring
      rw [this, Real.rpow_sub hα0, Real.rpow_one]
      field_simp
    rw [hz, ← hval]
    have hzα : (α * M) ^ α = α ^ α * M ^ α := Real.mul_rpow hα0.le hM0
    rw [hzα]
    have hMM : M ^ α * M ^ (1 - α) = M := by
      rw [← Real.rpow_add' hM0 (by norm_num : α + (1 - α) ≠ 0)]; simp
    have : A * (α ^ α * M ^ α) = M ^ α * M ^ (1 - α) := by rw [hMpow]; ring
    rw [this, hMM]
    ring

/-- **Example 11.AA.1** (MWG, p. 375): for fixed `h`, firm 2's problem is concave in `z`. -/
theorem example_11_AA_1_concave_in_z {α β h : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 ≤ h) :
    ConcaveOn ℝ (Set.Ici 0) fun z : ℝ => h ^ β * z ^ α - z := by
  have hc := (Real.concaveOn_rpow hα0 hα1).smul (Real.rpow_nonneg hh β)
  exact hc.sub (convexOn_id (convex_Ici 0))

/-- **Example 11.AA.1** (MWG, p. 375; Figure 11.AA.1). The derived profit `γ h^{β/(1-α)}` is
convex on `[0, ∞)` when `α + β ≥ 1`, and not concave when `α + β > 1`. -/
theorem example_11_AA_1_convex {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (1 ≤ α + β → ConvexOn ℝ (Set.Ici 0) fun h : ℝ => aa1Gamma α * h ^ (β / (1 - α))) ∧
      (1 < α + β → ¬ ConcaveOn ℝ (Set.Ici 0) fun h : ℝ => aa1Gamma α * h ^ (β / (1 - α))) := by
  have h1α : 0 < 1 - α := by linarith
  have hγ : 0 < aa1Gamma α := mul_pos h1α (Real.rpow_pos_of_pos hα0 _)
  refine ⟨fun hab => ?_, fun hab hconc => ?_⟩
  · have hk : 1 ≤ β / (1 - α) := by rw [le_div_iff₀ h1α]; linarith
    exact (convexOn_rpow hk).smul hγ.le
  · have hk : 1 < β / (1 - α) := by rw [lt_div_iff₀ h1α]; linarith
    have := hconc.2 (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hk0 : β / (1 - α) ≠ 0 := by linarith
    rw [Real.zero_rpow hk0, show (1 / 2 : ℝ) * 0 + 1 / 2 * 2 = 1 by norm_num, Real.one_rpow]
      at this
    have h2 : (2 : ℝ) ^ (1 : ℝ) < 2 ^ (β / (1 - α)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hk
    rw [Real.rpow_one] at h2
    nlinarith

/-- **Example 11.AA.1 at `α = 0`**: the formula `π₂(h) = γ h^β` holds with `γ = 1`
(`0^0 = 1`): the best input is `z = 0`. -/
theorem example_11_AA_1_alpha_zero {β h : ℝ} :
    (∀ z, 0 ≤ z → h ^ β * z ^ (0 : ℝ) - z ≤ aa1Gamma 0 * h ^ (β / (1 - 0))) ∧
      h ^ β * (0 : ℝ) ^ (0 : ℝ) - 0 = aa1Gamma 0 * h ^ (β / (1 - 0)) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · simp only [aa1Gamma, sub_zero, div_one, Real.rpow_zero, mul_one, one_mul]
    linarith
  · simp only [aa1Gamma, sub_zero, div_one, Real.rpow_zero, mul_one, one_mul]

/-- **Correction to Example 11.AA.1 at `α = 1`** (MWG, p. 375 allows `α ∈ [0, 1]`): with
`q = h^β z` and `h^β > 1` (e.g. `h > 1`, `β > 0`), firm 2's profit `(h^β - 1) z` is unbounded, so
there is no maximized profit function. -/
theorem example_11_AA_1_alpha_one {β h : ℝ} (hh : 1 < h) (hβ : 0 < β) (B : ℝ) :
    ∃ z, 0 ≤ z ∧ B < h ^ β * z ^ (1 : ℝ) - z := by
  have hA : 1 < h ^ β := Real.one_lt_rpow hh hβ
  refine ⟨(|B| + 1) / (h ^ β - 1), div_nonneg (by positivity) (by linarith), ?_⟩
  rw [Real.rpow_one]
  have hne : h ^ β - 1 ≠ 0 := (by linarith : 0 < h ^ β - 1).ne'
  have : h ^ β * ((|B| + 1) / (h ^ β - 1)) - (|B| + 1) / (h ^ β - 1) = |B| + 1 := by
    field_simp
  rw [this]
  linarith [le_abs_self B]

/-! ## Example 11.AA.2 -/

/-- **Example 11.AA.2** (MWG, pp. 375-376; Figure 11.AA.2; Starrett 1972). If firm 2 can shut down
(so `π₂ ≥ 0` on `[0, ∞)`) and `π₂` is differentiable with `π₂'(h₀) < 0` somewhere, then `π₂` is not
concave on `[0, ∞)`. -/
theorem example_11_AA_2 {f : ℝ → ℝ} (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hnonneg : ∀ h, 0 ≤ h → 0 ≤ f h) {h₀ : ℝ} (h₀0 : 0 ≤ h₀) (hneg : deriv f h₀ < 0) :
    ¬ ConcaveOn ℝ (Set.Ici 0) f := by
  intro hconc
  set y := h₀ + (f h₀ + 1) / (-deriv f h₀)
  have hfh0 := hnonneg h₀ h₀0
  have hgap : 0 < (f h₀ + 1) / (-deriv f h₀) := div_pos (by linarith) (by linarith)
  have hy : h₀ < y := by simp only [y]; linarith
  have hs := hconc.slope_le_deriv (Set.mem_Ici.2 h₀0) (Set.mem_Ici.2 (by linarith)) hy
    (hdiff h₀)
  rw [slope_def_field] at hs
  have hyh : y - h₀ = (f h₀ + 1) / (-deriv f h₀) := by simp only [y]; ring
  rw [div_le_iff₀ (by linarith), hyh] at hs
  have hd : deriv f h₀ ≠ 0 := hneg.ne
  have : deriv f h₀ * ((f h₀ + 1) / -deriv f h₀) = -(f h₀ + 1) := by
    field_simp
  rw [this] at hs
  have := hnonneg y (by linarith)
  linarith

/-- An instance of the hypotheses of Example 11.AA.2: `π₂(h) = e^{-h}` (nonnegative, strictly
decreasing); it is indeed not concave. -/
theorem example_11_AA_2_instance : ¬ ConcaveOn ℝ (Set.Ici 0) fun h : ℝ => Real.exp (-h) := by
  refine example_11_AA_2 (h₀ := 0) (fun x => ?_) (fun h _ => (Real.exp_pos _).le) le_rfl ?_
  · exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).differentiableAt
  · have : HasDerivAt (fun h : ℝ => Real.exp (-h)) (Real.exp (-0) * -1) 0 :=
      (Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)
    rw [this.deriv]
    simp

/-! ## Example 11.AA.3 -/

/-- Firm 1's profit in Example 11.AA.3. -/
noncomputable def aa3π₁ (h : ℝ) : ℝ := min h 1

/-- Firm 2's profit in Example 11.AA.3. -/
noncomputable def aa3π₂ (h : ℝ) : ℝ := if h ≤ 1 then 2 * (1 - h) ^ 2 else 0

theorem aa3_surplus_le {h : ℝ} (hh : h ≤ 1) : aa3π₁ h + aa3π₂ h = 2 - 3 * h + 2 * h ^ 2 := by
  simp only [aa3π₁, aa3π₂, min_eq_left hh, hh, ↓reduceIte]; ring

theorem aa3_surplus_ge {h : ℝ} (hh : 1 ≤ h) : aa3π₁ h + aa3π₂ h = 1 := by
  rcases eq_or_lt_of_le hh with h1 | h1
  · subst h1; norm_num [aa3π₁, aa3π₂]
  · simp only [aa3π₁, aa3π₂, min_eq_right hh, not_le.2 h1, ↓reduceIte]; ring

/-- **Example 11.AA.3** (MWG, pp. 376-377). The social optimum is `h = 0` with joint profit `2`
(uniquely); a tax `t > 1` on firm 1 implements it (uniquely). -/
theorem example_11_AA_3_optimum :
    (∀ h, 0 ≤ h → aa3π₁ h + aa3π₂ h ≤ aa3π₁ 0 + aa3π₂ 0) ∧ aa3π₁ 0 + aa3π₂ 0 = 2 ∧
      (∀ h, 0 < h → aa3π₁ h + aa3π₂ h < 2) ∧
      ∀ t, 1 < t → ∀ h, 0 < h → aa3π₁ h - t * h < aa3π₁ 0 - t * 0 := by
  have h0 : aa3π₁ 0 + aa3π₂ 0 = 2 := by norm_num [aa3π₁, aa3π₂]
  have hlt : ∀ h, 0 < h → aa3π₁ h + aa3π₂ h < 2 := fun h hh => by
    rcases le_total h 1 with h1 | h1
    · rw [aa3_surplus_le h1]; nlinarith
    · rw [aa3_surplus_ge h1]; norm_num
  refine ⟨fun h hh => ?_, h0, hlt, fun t ht h hh => ?_⟩
  · rcases eq_or_lt_of_le hh with he | hp
    · rw [← he]
    · rw [h0]; exact (hlt h hp).le
  · simp only [aa3π₁, mul_zero, sub_zero, min_eq_left (zero_le_one' ℝ)]
    have := min_le_left h 1
    nlinarith

/-- **Example 11.AA.3**: `h = 1` is a local social optimum; surplus exceeds its value `1` exactly
for `h < 1/2`. With a zero tax, firm 1 chooses any `h ≥ 1` (all maximize `π₁`). -/
theorem example_11_AA_3_local :
    aa3π₁ 1 + aa3π₂ 1 = 1 ∧ (∀ h, 1 / 2 ≤ h → aa3π₁ h + aa3π₂ h ≤ 1) ∧
      (∀ h, 0 ≤ h → h < 1 / 2 → 1 < aa3π₁ h + aa3π₂ h) ∧
      (∀ h, (∀ y, 0 ≤ y → aa3π₁ y ≤ aa3π₁ h) ↔ 1 ≤ h) := by
  refine ⟨aa3_surplus_ge le_rfl, fun h hh => ?_, fun h _ hh => ?_, fun h => ⟨fun hmax => ?_,
    fun h1 y _ => ?_⟩⟩
  · rcases le_total h 1 with h1 | h1
    · rw [aa3_surplus_le h1]; nlinarith
    · rw [aa3_surplus_ge h1]
  · rw [aa3_surplus_le (by linarith)]; nlinarith
  · have := hmax 1 zero_le_one
    simp only [aa3π₁, min_self] at this
    by_contra hlt
    push Not at hlt
    rw [min_eq_left hlt.le] at this
    linarith
  · simp only [aa3π₁, min_eq_right h1]
    exact min_le_right _ _

/-- **Correction to Example 11.AA.3** (MWG, p. 377: `h = 1` "satisfies both the first-order and
second-order conditions"). Aggregate surplus has left derivative `1` and right derivative `0` at
`h = 1`, so it is not differentiable there. -/
theorem example_11_AA_3_kink :
    HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 1 (Set.Iic 1) 1 ∧
      HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 0 (Set.Ici 1) 1 ∧
      ¬ DifferentiableAt ℝ (fun h => aa3π₁ h + aa3π₂ h) 1 := by
  have hl : HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 1 (Set.Iic 1) 1 := by
    have hg : HasDerivAt (fun h : ℝ => 2 - 3 * h + 2 * h ^ 2) 1 1 := by
      have h' := ((hasDerivAt_id (1 : ℝ)).const_mul 3).const_sub 2 |>.add
        ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 2)
      exact (h'.congr_deriv (by norm_num) : HasDerivAt (fun h : ℝ => 2 - 3 * h + 2 * h ^ 2) 1 1)
    exact hg.hasDerivWithinAt.congr (fun y hy => aa3_surplus_le hy) (aa3_surplus_le le_rfl)
  have hr : HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 0 (Set.Ici 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (1 : ℝ)).congr (fun y hy => aa3_surplus_ge hy)
      (aa3_surplus_ge le_rfl)
  refine ⟨hl, hr, fun hd => ?_⟩
  have e1 := (uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hl
  have e2 := (uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hr
  rw [e1] at e2
  exact one_ne_zero e2

end MWG.ExternalitiesPublicGoods
