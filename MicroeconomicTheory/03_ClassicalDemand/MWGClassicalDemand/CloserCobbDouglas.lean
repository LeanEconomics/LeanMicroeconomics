/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserLESSlutsky
import MWGClassicalDemand.UMPExamples

/-!
# Exercise 3.G.2: Cobb-Douglas satisfies Propositions 3.G.1-3.G.4

MWG, Exercise 3.G.2, p. 99. The general Propositions 3.G.1-3.G.4 (`RelationsBasic`) assume a
strictly convex `≿` on all of `ℝ^L_+`, which Cobb-Douglas preferences are not (they are flat
along the axes). Instead of an interior version of those propositions, the exercise is
verified directly: Cobb-Douglas utility `x₁^α x₂^{1-α}` is the linear expenditure system of
`CloserLES` with `b = 0` and exponents `(α, 1 - α)` (`cobbDouglas_eq_les`), whose demand,
Hicksian demand, expenditure function and all partial derivatives were computed there. Roy's
identity for the linear expenditure system is added (`les_roy`).

* Proposition 3.G.1: `∂e/∂p_l = h_l` (`exercise_3_G_2`, from `exercise_3_G_3b`).
* Proposition 3.G.2: `∂h_l/∂p_k` exists, the matrix is symmetric, negative semidefinite and
  annihilates `p`.
* Proposition 3.G.3: the Slutsky equation `∂h_l/∂p_k = ∂x_l/∂p_k + (∂x_l/∂w) x_k`.
* Proposition 3.G.4: Roy's identity `x_l = -(∂v/∂p_l)/(∂v/∂w)`.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

/-- On `ℝ²_+` the Cobb-Douglas utility `x₁^α x₂^{1-α}` is the Stone-Geary utility with `b = 0`
and exponents `(α, 1 - α)`. -/
theorem cobbDouglas_eq_les (α : ℝ) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) :
    cobbDouglasUtility 1 α x = lesUtility ![α, 1 - α] 0 x := by
  simp only [cobbDouglasUtility, lesUtility, Fin.prod_univ_two, Pi.zero_apply, sub_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul,
    max_eq_left (hx 0), max_eq_left (hx 1)]

/-- Hicksian demand depends only on the values of `u` on `ℝ^L_+`. -/
theorem hicksianDemand_congr {L : ℕ} {u v : (Fin L → ℝ) → ℝ}
    (h : ∀ x ∈ nonnegOrthant L, u x = v x) (p : Fin L → ℝ) (ub : ℝ) :
    hicksianDemand u p ub = hicksianDemand v p ub := by
  ext x
  simp only [mem_hicksianDemand_iff]
  constructor
  · rintro ⟨⟨hx, hxu⟩, hmin⟩
    exact ⟨⟨hx, h x hx ▸ hxu⟩, fun y hy hyu => hmin y hy (by rw [h y hy]; exact hyu)⟩
  · rintro ⟨⟨hx, hxu⟩, hmin⟩
    exact ⟨⟨hx, (h x hx).symm ▸ hxu⟩, fun y hy hyu => hmin y hy (by rw [← h y hy]; exact hyu)⟩

/-- **Proposition 3.G.4** for the linear expenditure system (Roy's identity), used in Exercise
3.G.2. With `C(p) = ∏ (a_l/p_l)^{a_l}`, `∂v/∂w = C(p)`,
`∂v/∂p_l = -b_l C(p) - (w - p·b) a_l C(p)/p_l`, and `x_l(p, w) = -(∂v/∂p_l)/(∂v/∂w)`. -/
theorem les_roy {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (b : Fin L → ℝ) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (w : ℝ) (l : Fin L) :
    HasDerivAt (fun w' => lesIndirect a b p w') (lesIndex a p)⁻¹ w ∧
      HasDerivAt (fun t => lesIndirect a b (Function.update p l t) w)
        (-(b l) * (lesIndex a p)⁻¹ - (w - p ⬝ᵥ b) * a l * (lesIndex a p)⁻¹ / p l) (p l) ∧
      lesDemand a b p w l = -((-(b l) * (lesIndex a p)⁻¹ -
        (w - p ⬝ᵥ b) * a l * (lesIndex a p)⁻¹ / p l) / (lesIndex a p)⁻¹) := by
  have hQ := lesIndex_pos ha hp
  have hpl := hp l
  -- `C = Q⁻¹`
  have hC : ∀ q : Fin L → ℝ, StrictlyPositive q →
      ∏ k, (a k / q k) ^ a k = (lesIndex a q)⁻¹ := by
    intro q hq
    unfold lesIndex
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Real.inv_rpow (div_pos (hq k) (ha k)).le, inv_div]
  have hupd : ∀ t : ℝ, 0 < t → StrictlyPositive (Function.update p l t) := by
    intro t ht k
    by_cases hk : k = l
    · subst hk; simpa using ht
    · rw [Function.update_of_ne hk]; exact hp k
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id w).sub_const (p ⬝ᵥ b)).mul_const (lesIndex a p)⁻¹
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq ?_
    filter_upwards with w'
    simp [lesIndirect, hC p hp]
  · have hdot : HasDerivAt (fun t => w - Function.update p l t ⬝ᵥ b) (-(b l)) (p l) := by
      have := ((((hasDerivAt_id (p l)).sub_const (p l)).mul_const (b l)).const_add
        (p ⬝ᵥ b)).const_sub w
      refine (this.congr_deriv (by simp)).congr_of_eventuallyEq ?_
      filter_upwards with t
      simp [les_update_dotProduct]
    have hinv := (lesIndex_hasDerivAt ha hp l).inv (by rw [Function.update_eq_self]; exact hQ.ne')
    have h := hdot.mul hinv
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [Pi.inv_apply, Function.update_eq_self]
      field_simp
      ring
    · filter_upwards [lt_mem_nhds hpl] with t ht
      simp only [lesIndirect, hC _ (hupd t ht), Pi.mul_apply, Pi.inv_apply]
  · simp only [lesDemand]
    field_simp
    ring

/-- **Exercise 3.G.2** (MWG, p. 99). For the Cobb-Douglas utility `x₁^α x₂^{1-α}`, `α ∈ (0, 1)`,
`p ≫ 0`, `ū > 0`, `w > 0`, with `a = (α, 1-α)`: the Walrasian and Hicksian demands and the
expenditure and indirect utility functions are those of the linear expenditure system with
`b = 0`; and Propositions 3.G.1-3.G.4 hold: (3.G.1) `∂e/∂p_l = h_l`; (3.G.2) `∂h_l/∂p_k` exists,
is symmetric, the matrix is negative semidefinite and annihilates `p`; (3.G.3) the Slutsky
equation; (3.G.4) Roy's identity. -/
theorem exercise_3_G_2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub w : ℝ} (hub : 0 < ub) (hw : 0 < w) :
    walrasianDemand (cobbDouglasUtility 1 α) p w = {lesDemand ![α, 1 - α] 0 p w} ∧
      indirectUtility (cobbDouglasUtility 1 α) p w = lesIndirect ![α, 1 - α] 0 p w ∧
      hicksianDemand (cobbDouglasUtility 1 α) p ub = {lesHicks ![α, 1 - α] 0 p ub} ∧
      expenditure (cobbDouglasUtility 1 α) p ub = lesExpenditure ![α, 1 - α] 0 p ub ∧
      (∀ k, HasDerivAt (fun t => lesExpenditure ![α, 1 - α] 0 (Function.update p k t) ub)
        (lesHicks ![α, 1 - α] 0 p ub k) (p k)) ∧
      (∀ l k, HasDerivAt (fun t => lesHicks ![α, 1 - α] 0 (Function.update p k t) ub l)
        (lesSlutsky ![α, 1 - α] p ub l k) (p k)) ∧
      (∀ l k, lesSlutsky ![α, 1 - α] p ub l k = lesSlutsky ![α, 1 - α] p ub k l) ∧
      NegSemidef (Matrix.of (lesSlutsky ![α, 1 - α] p ub)) ∧
      (Matrix.of (lesSlutsky ![α, 1 - α] p ub)).mulVec p = 0 ∧
      (∀ l k, lesSlutsky ![α, 1 - α] p ub l k =
        lesPriceEffect ![α, 1 - α] 0 p (lesExpenditure ![α, 1 - α] 0 p ub) l k +
          (![α, 1 - α] l / p l) *
            lesDemand ![α, 1 - α] 0 p (lesExpenditure ![α, 1 - α] 0 p ub) k) ∧
      (∀ l, lesDemand ![α, 1 - α] 0 p w l =
        -((-((0 : Fin 2 → ℝ) l) * (lesIndex ![α, 1 - α] p)⁻¹ -
          (w - p ⬝ᵥ 0) * ![α, 1 - α] l * (lesIndex ![α, 1 - α] p)⁻¹ / p l) /
            (lesIndex ![α, 1 - α] p)⁻¹)) := by
  set a : Fin 2 → ℝ := ![α, 1 - α] with hadef
  have ha : ∀ l, 0 < a l := by
    intro l; fin_cases l
    · simpa [hadef] using hα0
    · simp [hadef]; linarith
  have hsum : ∑ l, a l = 1 := by simp [hadef, Fin.sum_univ_two]
  have hb : (0 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun _ => le_rfl
  have hpb : p ⬝ᵥ (0 : Fin 2 → ℝ) < w := by simpa using hw
  have hcongr : ∀ x ∈ nonnegOrthant 2, cobbDouglasUtility 1 α x = lesUtility a 0 x :=
    fun x hx => cobbDouglas_eq_les α hx
  have hW := walrasianDemand_congr hcongr p w
  have hH := hicksianDemand_congr hcongr p ub
  refine ⟨?_, ?_, ?_, ?_, fun k => exercise_3_G_3b ha hp ub k,
    fun l k => les_hicks_derivative ha 0 hp ub l k,
    (exercise_3_G_3d ha hp hub).2, (exercise_3_G_3e ha hsum hp hub).1,
    ((exercise_3_G_3e ha hsum hp hub).2.1 p).2 ⟨1, (one_smul ℝ p).symm⟩,
    fun l k => (exercise_3_G_3c ha 0 hp ub l k).2.2.2,
    fun l => (les_roy ha 0 hp w l).2.2⟩
  · rw [hW]; exact exercise_3_D_6b_demand ha hsum hb hp hpb
  · have hx : lesDemand a 0 p w ∈ walrasianDemand (cobbDouglasUtility 1 α) p w := by
      rw [hW, exercise_3_D_6b_demand ha hsum hb hp hpb]; rfl
    rw [indirectUtility_eq_of_mem hx, hcongr _ hx.1.1, lesUtility_lesDemand ha hsum hp hpb]
  · rw [hH]; exact (exercise_3_G_3a ha hsum hb hp hub).1
  · have hx : lesHicks a 0 p ub ∈ hicksianDemand (cobbDouglasUtility 1 α) p ub := by
      rw [hH, (exercise_3_G_3a ha hsum hb hp hub).1]; rfl
    rw [expenditure_eq_of_mem hx, ← expenditure_eq_of_mem (by
      rw [(exercise_3_G_3a ha hsum hb hp hub).1]; rfl :
        lesHicks a 0 p ub ∈ hicksianDemand (lesUtility a 0) p ub)]
    exact (exercise_3_G_3a ha hsum hb hp hub).2

end MWG.ClassicalDemand
