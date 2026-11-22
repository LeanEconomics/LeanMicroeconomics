/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPBasic
import ConsumerDemand.CobbDouglasDemand

/-!
# Cobb-Douglas demand and indirect utility

MWG, Examples 3.D.1-3.D.2 and Exercises 3.D.1-3.D.2, pp. 55-57.

* Bridges: Walrasian demand depends only on the utility's values on `ℝ^L_+` and is unchanged by
  strictly increasing transformations; it is Kreps's Marshallian demand of the restricted
  utility.
* Example 3.D.1: for `u(x) = k x₁^α x₂^{1-α}` (`k > 0`, `α ∈ (0, 1)`), `p ≫ 0`, `w ≥ 0`, the
  demand is the single bundle `(αw/p₁, (1-α)w/p₂)`. The book solves the problem with the
  log transform `α ln x₁ + (1 - α) ln x₂` (with `ln 0 = -∞`); we use the Cobb-Douglas utility
  itself, which has the same demand on `ℝ²_{++}` and is defined on all of `ℝ²_+`.
* Exercise 3.D.1: the demand function is homogeneous of degree zero, satisfies Walras' law and
  is single-valued.
* Example 3.D.2: `v(p, w) = (αw/p₁)^α ((1-α)w/p₂)^{1-α}`, whose logarithm is the book's
  `[α ln α + (1 - α) ln(1 - α)] + ln w - α ln p₁ - (1 - α) ln p₂`.
* Exercise 3.D.2: the four properties of Proposition 3.D.3 for that function.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- Walrasian demand depends only on the values of `u` on `ℝ^L_+`. -/
theorem walrasianDemand_congr {u v : (Fin L → ℝ) → ℝ}
    (h : ∀ x ∈ nonnegOrthant L, u x = v x) (p : Fin L → ℝ) (w : ℝ) :
    walrasianDemand u p w = walrasianDemand v p w := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => by rw [← h y hy.1, ← h x hx.1]; exact hmax y hy⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => by rw [h y hy.1, h x hx.1]; exact hmax y hy⟩

/-- Walrasian demand is unchanged by a strictly increasing transformation of utility. -/
theorem walrasianDemand_comp_strictMono {u : (Fin L → ℝ) → ℝ} {f : ℝ → ℝ} (hf : StrictMono f)
    (p : Fin L → ℝ) (w : ℝ) : walrasianDemand (f ∘ u) p w = walrasianDemand u p w := by
  ext x
  simp only [mem_walrasianDemand_iff, Function.comp_apply, hf.le_iff_le]

/-- Walrasian demand of the extension of a subtype utility is Kreps's Marshallian demand. -/
theorem walrasianDemand_extendOrthant (v : Kreps.ConsumerDemand.NonnegativeOrthant L → ℝ)
    {p : Fin L → ℝ} (hp : ∀ j, 0 < p j) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand (extendOrthant v) p w =
      Subtype.val '' Kreps.ConsumerDemand.MarshallianDemand v ⟨p, hp⟩ w.toNNReal := by
  have hcoe : ((w.toNNReal : NNReal) : ℝ) = w := Real.coe_toNNReal w hw
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨⟨x, fun l => hx.1 l⟩, ⟨?_, fun z hz => ?_⟩, rfl⟩
    · change p ⬝ᵥ x ≤ ((w.toNNReal : NNReal) : ℝ)
      rw [hcoe]
      exact hx.2
    · have hz' : p ⬝ᵥ z.1 ≤ w := by
        have : p ⬝ᵥ z.1 ≤ ((w.toNNReal : NNReal) : ℝ) := hz
        rwa [hcoe] at this
      have := hmax z.1 ⟨fun l => z.2 l, hz'⟩
      rwa [extendOrthant_apply v (fun l => z.2 l), extendOrthant_apply v hx.1] at this
  · rintro ⟨a, ⟨ha, hmax⟩, rfl⟩
    have ha' : p ⬝ᵥ a.1 ≤ w := by
      have : p ⬝ᵥ a.1 ≤ ((w.toNNReal : NNReal) : ℝ) := ha
      rwa [hcoe] at this
    refine ⟨⟨fun l => a.2 l, ha'⟩, fun y hy => ?_⟩
    rw [extendOrthant_apply v hy.1, extendOrthant_apply v (fun l => a.2 l)]
    refine hmax ⟨y, fun l => hy.1 l⟩ ?_
    change p ⬝ᵥ y ≤ ((w.toNNReal : NNReal) : ℝ)
    rw [hcoe]
    exact hy.2

/-- **Example 3.D.1** (MWG, p. 55). The Cobb-Douglas utility `u(x₁, x₂) = k x₁^α x₂^{1-α}`. -/
noncomputable def cobbDouglasUtility (k α : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  k * (x 0 ^ α * x 1 ^ (1 - α))

/-- **Example 3.D.1** (MWG, p. 56). The Cobb-Douglas demand function
`x(p, w) = (αw/p₁, (1-α)w/p₂)`. -/
noncomputable def cobbDouglasDemand (α : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![α * w / p 0, (1 - α) * w / p 1]

/-- **Example 3.D.1** (MWG, pp. 55-56). For `k > 0`, `α ∈ (0, 1)`, `p ≫ 0` and `w ≥ 0`, the UMP
for the Cobb-Douglas utility has the unique solution `(αw/p₁, (1-α)w/p₂)`; expenditure shares
are `α` and `1 - α`. -/
theorem example_3_D_1 {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand (cobbDouglasUtility k α) p w = {cobbDouglasDemand α p w} := by
  have hp' : ∀ j, 0 < p j := hp
  set a : Fin 2 → ℝ := ![α, 1 - α] with ha
  have ha' : ∀ j, 0 < a j := by
    intro j
    fin_cases j
    · simpa [ha] using hα0
    · simpa [ha] using hα1
  have hcongr : ∀ x ∈ nonnegOrthant 2, cobbDouglasUtility k α x =
      ((fun t => k * t) ∘ extendOrthant (Kreps.ConsumerDemand.CobbDouglas a)) x := by
    intro x hx
    rw [Function.comp_apply, extendOrthant_apply _ hx]
    simp [cobbDouglasUtility, Kreps.ConsumerDemand.CobbDouglas,
      Kreps.ConsumerDemand.ShiftedCobbDouglas, Fin.prod_univ_two, ha]
  rw [walrasianDemand_congr hcongr, walrasianDemand_comp_strictMono (strictMono_mul_left_of_pos hk),
    walrasianDemand_extendOrthant _ hp' hw, Kreps.ConsumerDemand.cobbDouglas_demand a ha',
    Set.image_singleton]
  congr 1
  funext j
  fin_cases j
  · simp [Kreps.ConsumerDemand.CobbDouglasBundle, cobbDouglasDemand, ha, max_eq_left hw]
    ring
  · simp [Kreps.ConsumerDemand.CobbDouglasBundle, cobbDouglasDemand, ha, max_eq_left hw]
    ring

/-- **Example 3.D.1** (MWG, p. 56). Expenditure on each good is a constant fraction of wealth:
`p₁x₁(p, w) = αw` and `p₂x₂(p, w) = (1-α)w`. -/
theorem example_3_D_1_shares {α : ℝ} {p : Fin 2 → ℝ} (hp : StrictlyPositive p) (w : ℝ) :
    p 0 * cobbDouglasDemand α p w 0 = α * w ∧ p 1 * cobbDouglasDemand α p w 1 = (1 - α) * w := by
  simp only [cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨mul_div_cancel₀ _ (hp 0).ne', mul_div_cancel₀ _ (hp 1).ne'⟩

/-- **Exercise 3.D.1** (MWG, p. 56), homogeneity of degree zero of the Cobb-Douglas demand. -/
theorem exercise_3_D_1_homogeneous (α : ℝ) : HomogeneousZero (cobbDouglasDemand α) := by
  intro p w t _ ht
  funext j
  fin_cases j <;>
    simp only [cobbDouglasDemand, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] <;>
    field_simp

/-- **Exercise 3.D.1** (MWG, p. 56), Walras' law for the Cobb-Douglas demand. -/
theorem exercise_3_D_1_walras (α : ℝ) : WalrasLaw (cobbDouglasDemand α) := by
  intro p w hd
  rw [dotProduct, Fin.sum_univ_two]
  have := example_3_D_1_shares (α := α) hd.1 w
  rw [this.1, this.2]
  ring

/-- **Exercise 3.D.1** (MWG, p. 56), convexity/uniqueness: the Cobb-Douglas demand
correspondence is single-valued (so in particular convex). -/
theorem exercise_3_D_1_unique {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1)
    {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    (walrasianDemand (cobbDouglasUtility k α) p w).Subsingleton ∧
      Convex ℝ (walrasianDemand (cobbDouglasUtility k α) p w) := by
  rw [example_3_D_1 hk hα0 hα1 hp hw]
  exact ⟨Set.subsingleton_singleton, convex_singleton _⟩

/-- **Example 3.D.2** (MWG, p. 57). The Cobb-Douglas indirect utility function
`v(p, w) = (αw/p₁)^α ((1-α)w/p₂)^{1-α}` (for `k = 1`). -/
noncomputable def cobbDouglasIndirect (α : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : ℝ :=
  (α * w / p 0) ^ α * ((1 - α) * w / p 1) ^ (1 - α)

/-- **Example 3.D.2** (MWG, p. 57). The book's logarithmic indirect utility
`[α ln α + (1 - α) ln(1 - α)] + ln w - α ln p₁ - (1 - α) ln p₂`. -/
noncomputable def cobbDouglasLogIndirect (α : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : ℝ :=
  (α * Real.log α + (1 - α) * Real.log (1 - α)) + Real.log w - α * Real.log (p 0) -
    (1 - α) * Real.log (p 1)

/-- **Example 3.D.2** (MWG, p. 57). The indirect utility of the Cobb-Douglas utility is
`v(p, w) = u(x(p, w))`, the formula `cobbDouglasIndirect`. -/
theorem example_3_D_2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    indirectUtility (cobbDouglasUtility 1 α) p w = cobbDouglasIndirect α p w := by
  have hx : cobbDouglasDemand α p w ∈ walrasianDemand (cobbDouglasUtility 1 α) p w := by
    rw [example_3_D_1 one_pos hα0 hα1 hp hw]
    exact Set.mem_singleton _
  rw [indirectUtility_eq_of_mem hx]
  simp [cobbDouglasUtility, cobbDouglasDemand, cobbDouglasIndirect]

/-- **Example 3.D.2** (MWG, p. 57). For `w > 0`, the logarithm of the Cobb-Douglas indirect
utility is the book's formula: it is the indirect utility of the representation
`α ln x₁ + (1 - α) ln x₂ = ln u(x)` on `ℝ²_{++}`. -/
theorem example_3_D_2_log {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    Real.log (cobbDouglasIndirect α p w) = cobbDouglasLogIndirect α p w := by
  have h1 : 0 < α * w / p 0 := div_pos (mul_pos hα0 hw) (hp 0)
  have h2 : 0 < (1 - α) * w / p 1 := div_pos (mul_pos (by linarith) hw) (hp 1)
  unfold cobbDouglasIndirect cobbDouglasLogIndirect
  rw [Real.log_mul (Real.rpow_pos_of_pos h1 _).ne' (Real.rpow_pos_of_pos h2 _).ne',
    Real.log_rpow h1, Real.log_rpow h2, Real.log_div (mul_pos hα0 hw).ne' (hp 0).ne',
    Real.log_div (mul_pos (by linarith) hw).ne' (hp 1).ne', Real.log_mul hα0.ne' hw.ne',
    Real.log_mul (by linarith) hw.ne']
  ring

/-- **Exercise 3.D.2(i)** (MWG, p. 57). The logarithmic Cobb-Douglas indirect utility is
homogeneous of degree zero. -/
theorem exercise_3_D_2_i (α : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 < w) {t : ℝ} (ht : 0 < t) :
    cobbDouglasLogIndirect α (t • p) (t * w) = cobbDouglasLogIndirect α p w := by
  unfold cobbDouglasLogIndirect
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.log_mul ht.ne' hw.ne', Real.log_mul ht.ne' (hp 0).ne',
    Real.log_mul ht.ne' (hp 1).ne']
  ring

/-- **Exercise 3.D.2(ii)** (MWG, p. 57). The logarithmic Cobb-Douglas indirect utility is
strictly increasing in `w > 0` and nonincreasing (indeed decreasing) in each price. -/
theorem exercise_3_D_2_ii {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p p' : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hpp : p ≤ p') {w w' : ℝ} (hw : 0 < w) (hww : w < w') :
    cobbDouglasLogIndirect α p w < cobbDouglasLogIndirect α p w' ∧
      cobbDouglasLogIndirect α p' w ≤ cobbDouglasLogIndirect α p w := by
  unfold cobbDouglasLogIndirect
  constructor
  · have := Real.log_lt_log hw hww
    linarith
  · have h0 := Real.log_le_log (hp 0) (hpp 0)
    have h1 := Real.log_le_log (hp 1) (hpp 1)
    nlinarith

/-- **Exercise 3.D.2(iii)** (MWG, p. 57). The logarithmic Cobb-Douglas indirect utility is
quasiconvex in `(p, w)` on `(p, w) ≫ 0` (via Proposition 3.D.3(iii) and `v > 0`). -/
theorem exercise_3_D_2_iii {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    QuasiconvexOn ℝ (pwDomainSet 2) (fun q => cobbDouglasLogIndirect α q.1 q.2) := by
  have hcont : ContinuousOn (cobbDouglasUtility 1 α) (nonnegOrthant 2) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold cobbDouglasUtility
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.mul
    · exact (continuous_apply 0).continuousAt.rpow_const (Or.inr hα0.le)
    · exact (continuous_apply 1).continuousAt.rpow_const (Or.inr (by linarith))
  have hq := proposition_3_D_3_iii hcont
  intro t q hq1 q' hq1' a b ha hb hab
  have hpos : ∀ q ∈ pwDomainSet 2, 0 < cobbDouglasIndirect α q.1 q.2 := by
    intro q hq
    unfold cobbDouglasIndirect
    exact mul_pos (Real.rpow_pos_of_pos (div_pos (mul_pos hα0 hq.2) (hq.1 0)) _)
      (Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) hq.2) (hq.1 1)) _)
  have hiff : ∀ q ∈ pwDomainSet 2, (cobbDouglasLogIndirect α q.1 q.2 ≤ t ↔
      indirectUtility (cobbDouglasUtility 1 α) q.1 q.2 ≤ Real.exp t) := by
    intro q hq
    rw [example_3_D_2 hα0 hα1 hq.1 hq.2.le, ← example_3_D_2_log hα0 hα1 hq.1 hq.2,
      Real.log_le_iff_le_exp (hpos q hq)]
  have h1 := (hiff q hq1.1).mp hq1.2
  have h2 := (hiff q' hq1'.1).mp hq1'.2
  have hm := hq (Real.exp t) ⟨hq1.1, h1⟩ ⟨hq1'.1, h2⟩ ha hb hab
  exact ⟨hm.1, (hiff _ hm.1).mpr hm.2⟩

/-- **Exercise 3.D.2(iv)** (MWG, p. 57). The logarithmic Cobb-Douglas indirect utility is
continuous on `(p, w) ≫ 0`. -/
theorem exercise_3_D_2_iv (α : ℝ) :
    ContinuousOn (fun q : (Fin 2 → ℝ) × ℝ => cobbDouglasLogIndirect α q.1 q.2)
      (pwDomainSet 2) := by
  unfold cobbDouglasLogIndirect
  apply ContinuousOn.sub
  · apply ContinuousOn.sub
    · exact continuousOn_const.add (continuous_snd.continuousOn.log fun q hq => hq.2.ne')
    · exact continuousOn_const.mul
        (((continuous_apply 0).comp continuous_fst).continuousOn.log fun q hq => (hq.1 0).ne')
  · exact continuousOn_const.mul
      (((continuous_apply 1).comp continuous_fst).continuousOn.log fun q hq => (hq.1 1).ne')

end MWG.ClassicalDemand
