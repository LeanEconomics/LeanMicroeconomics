/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserLES
import MWGConsumerChoice.MatrixDefiniteness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The linear expenditure system: Exercise 3.G.3(b)-(e)

MWG, Exercise 3.G.3, p. 99, for the linear expenditure system of `CloserLES` (any `L ≥ 1`;
the book's case is `L = 3`). Write `Q(p) = ∏ (p_l/a_l)^{a_l}` and `M = ū Q(p)`, so that
`e(p, ū) = p·b + M` and `h_l = b_l + a_l M / p_l`. Partial derivatives are taken along
coordinates (`Function.update p k t`).

* **(b)** `∂e/∂p_k = h_k` (`exercise_3_G_3b`).
* **(c)** The Slutsky equation `∂h_l/∂p_k = ∂x_l/∂p_k + (∂x_l/∂w) x_k` at `w = e(p, ū)`, with all
  three partial derivatives computed (`exercise_3_G_3c`).
* **(d)** `∂h_l/∂p_l < 0` (when `L ≥ 2`, i.e. `a_l < 1`) and `∂h_l/∂p_k = ∂h_k/∂p_l`
  (`exercise_3_G_3d`).
* **(e)** `S = [∂h_l/∂p_k]` is negative semidefinite, its kernel is the line through `p`, and so
  its rank is `L - 1`, which is `2` for the book's three goods (`exercise_3_G_3e`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

/-- The price index `Q(p) = ∏ (p_l/a_l)^{a_l}` of the linear expenditure system. -/
noncomputable def lesIndex {L : ℕ} (a p : Fin L → ℝ) : ℝ := ∏ l, (p l / a l) ^ a l

/-- `Q(p) > 0` for `a, p ≫ 0`. -/
theorem lesIndex_pos {L : ℕ} {a p : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hp : StrictlyPositive p) :
    0 < lesIndex a p :=
  Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (hp l) (ha l)) _

/-- Changing one price is a rank-one change of `p·b`. -/
theorem les_update_dotProduct {L : ℕ} (p b : Fin L → ℝ) (k : Fin L) (t : ℝ) :
    Function.update p k t ⬝ᵥ b = p ⬝ᵥ b + (t - p k) * b k := by
  have : Function.update p k t = p + (t - p k) • Pi.single k 1 := by
    funext l
    by_cases h : l = k
    · subst h
      simp
    · simp [h]
  rw [this, add_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]

/-- `Q` along the `k`th price: `Q(p with p_k = t) = (t/a_k)^{a_k} ∏_{l ≠ k} (p_l/a_l)^{a_l}`. -/
theorem lesIndex_update {L : ℕ} (a p : Fin L → ℝ) (k : Fin L) (t : ℝ) :
    lesIndex a (Function.update p k t) =
      (t / a k) ^ a k * ∏ l ∈ Finset.univ.erase k, (p l / a l) ^ a l := by
  unfold lesIndex
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- `∂Q/∂p_k = a_k Q(p)/p_k`. -/
theorem lesIndex_hasDerivAt {L : ℕ} {a p : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hp : StrictlyPositive p) (k : Fin L) :
    HasDerivAt (fun t => lesIndex a (Function.update p k t)) (a k * lesIndex a p / p k)
      (p k) := by
  have hpk := hp k
  have hak := ha k
  set R := ∏ l ∈ Finset.univ.erase k, (p l / a l) ^ a l
  have hf : (fun t => lesIndex a (Function.update p k t)) = fun t => (t / a k) ^ a k * R :=
    funext fun t => lesIndex_update a p k t
  have hQ : lesIndex a p = (p k / a k) ^ a k * R := by
    have := lesIndex_update a p k (p k)
    rwa [Function.update_eq_self] at this
  rw [hf, hQ]
  have h1 : HasDerivAt (fun t => t / a k) (1 / a k) (p k) := by
    simpa using (hasDerivAt_id (p k)).div_const (a k)
  have h2 := (h1.rpow_const (p := a k) (Or.inl (div_pos hpk hak).ne')).mul_const R
  convert h2 using 1
  rw [Real.rpow_sub_one (div_pos hpk hak).ne']
  field_simp

/-- The Hicksian demand of the linear expenditure system: `h_l = b_l + a_l ū Q(p)/p_l`. -/
theorem lesHicks_apply {L : ℕ} (a b p : Fin L → ℝ) (ub : ℝ) (l : Fin L) :
    lesHicks a b p ub l = b l + a l * (ub * lesIndex a p) / p l := by
  simp [lesHicks, lesDemand, lesExpenditure, lesIndex]

/-- **Exercise 3.G.3(b)** (MWG, p. 99). The derivatives of the expenditure function are the
Hicksian demands: `∂e(p, ū)/∂p_k = h_k(p, ū)`. -/
theorem exercise_3_G_3b {L : ℕ} {a b p : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hp : StrictlyPositive p) (ub : ℝ) (k : Fin L) :
    HasDerivAt (fun t => lesExpenditure a b (Function.update p k t) ub) (lesHicks a b p ub k)
      (p k) := by
  have hd1 : HasDerivAt (fun t => p ⬝ᵥ b + (t - p k) * b k) (b k) (p k) := by
    have := (((hasDerivAt_id (p k)).sub_const (p k)).mul_const (b k)).const_add (p ⬝ᵥ b)
    exact this.congr_deriv (by ring)
  have hd := hd1.add ((lesIndex_hasDerivAt ha hp k).const_mul ub)
  convert hd using 1
  · funext t
    simp only [lesExpenditure, les_update_dotProduct]
    rfl
  · rw [lesHicks_apply]
    ring

/-- The own- and cross-price effects of the linear expenditure system:
`∂x_l/∂p_k = -a_l b_k/p_l - [l = k] a_l (w - p·b)/p_l²`. -/
noncomputable def lesPriceEffect {L : ℕ} (a b p : Fin L → ℝ) (w : ℝ) (l k : Fin L) : ℝ :=
  -(a l * b k / p l) - if l = k then a l * (w - p ⬝ᵥ b) / p l ^ 2 else 0

/-- The substitution terms of the linear expenditure system:
`∂h_l/∂p_k = a_l a_k M/(p_l p_k) - [l = k] a_l M/p_l²`, `M = ū Q(p)`. -/
noncomputable def lesSlutsky {L : ℕ} (a p : Fin L → ℝ) (ub : ℝ) (l k : Fin L) : ℝ :=
  a l * a k * (ub * lesIndex a p) / (p l * p k) -
    if l = k then a l * (ub * lesIndex a p) / p l ^ 2 else 0

/-- **Exercise 3.G.3(c)** (MWG, p. 99), the price derivatives of Walrasian demand:
`∂x_l(p, w)/∂p_k = lesPriceEffect a b p w l k`. -/
theorem les_price_derivative {L : ℕ} (a b : Fin L → ℝ) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (w : ℝ) (l k : Fin L) :
    HasDerivAt (fun t => lesDemand a b (Function.update p k t) w l)
      (lesPriceEffect a b p w l k) (p k) := by
  by_cases hlk : l = k
  · subst hlk
    have hf : (fun t => lesDemand a b (Function.update p l t) w l) =
        fun t => b l + (a l * (w - (p ⬝ᵥ b + (t - p l) * b l))) / t := by
      funext t
      simp only [lesDemand, les_update_dotProduct, Function.update_self]
    rw [hf]
    have hg : HasDerivAt (fun t => a l * (w - (p ⬝ᵥ b + (t - p l) * b l))) (-(a l * b l))
        (p l) := by
      have := ((((hasDerivAt_id (p l)).sub_const (p l)).mul_const (b l)).const_add
        (p ⬝ᵥ b)).const_sub w |>.const_mul (a l)
      exact this.congr_deriv (by ring)
    have := (hg.div (hasDerivAt_id (p l)) (hp l).ne').const_add (b l)
    refine this.congr_deriv ?_
    have hpl := (hp l).ne'
    simp only [lesPriceEffect, ↓reduceIte, id]
    field_simp
    ring
  · have hf : (fun t => lesDemand a b (Function.update p k t) w l) =
        fun t => b l + a l * (w - (p ⬝ᵥ b + (t - p k) * b k)) / p l := by
      funext t
      simp only [lesDemand, les_update_dotProduct, Function.update_of_ne hlk]
    rw [hf]
    have := (((((hasDerivAt_id (p k)).sub_const (p k)).mul_const (b k)).const_add
      (p ⬝ᵥ b)).const_sub w |>.const_mul (a l) |>.div_const (p l)).const_add (b l)
    refine this.congr_deriv ?_
    have hpl := (hp l).ne'
    simp only [lesPriceEffect, hlk, ↓reduceIte]
    field_simp
    ring

/-- **Exercise 3.G.3(c)** (MWG, p. 99), the wealth derivative `∂x_l/∂w = a_l/p_l`. -/
theorem les_wealth_derivative {L : ℕ} (a b p : Fin L → ℝ) (w : ℝ) (l : Fin L) :
    HasDerivAt (fun w => lesDemand a b p w l) (a l / p l) w := by
  have := (((hasDerivAt_id w).sub_const (p ⬝ᵥ b)).const_mul (a l) |>.div_const (p l)).const_add
    (b l)
  exact this.congr_deriv (by ring)

/-- **Exercise 3.G.3(c)** (MWG, p. 99), the price derivatives of Hicksian demand:
`∂h_l(p, ū)/∂p_k = lesSlutsky a p ū l k`. -/
theorem les_hicks_derivative {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (b : Fin L → ℝ)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (ub : ℝ) (l k : Fin L) :
    HasDerivAt (fun t => lesHicks a b (Function.update p k t) ub l) (lesSlutsky a p ub l k)
      (p k) := by
  have hQ := lesIndex_hasDerivAt ha hp k
  by_cases hlk : l = k
  · subst hlk
    have hf : (fun t => lesHicks a b (Function.update p l t) ub l) =
        fun t => b l + (a l * ub * lesIndex a (Function.update p l t)) / t := by
      funext t
      rw [lesHicks_apply, Function.update_self]
      ring
    rw [hf]
    have := ((hQ.const_mul (a l * ub)).div (hasDerivAt_id (p l)) (hp l).ne').const_add (b l)
    refine this.congr_deriv ?_
    have hpl := (hp l).ne'
    simp only [lesSlutsky, ↓reduceIte, id, Function.update_eq_self]
    field_simp
  · have hf : (fun t => lesHicks a b (Function.update p k t) ub l) =
        fun t => b l + (a l * ub * lesIndex a (Function.update p k t)) / p l := by
      funext t
      rw [lesHicks_apply, Function.update_of_ne hlk]
      ring
    rw [hf]
    have := ((hQ.const_mul (a l * ub)).div_const (p l)).const_add (b l)
    refine this.congr_deriv ?_
    have hpl := (hp l).ne'
    have hpk := (hp k).ne'
    simp only [lesSlutsky, hlk, ↓reduceIte]
    field_simp
    ring

/-- **Exercise 3.G.3(c)** (MWG, p. 99). The Slutsky equation holds for the linear expenditure
system: at `w = e(p, ū)`,
`∂h_l(p, ū)/∂p_k = ∂x_l(p, w)/∂p_k + (∂x_l(p, w)/∂w) x_k(p, w)`, each partial derivative being
the one computed in `les_hicks_derivative`, `les_price_derivative`, `les_wealth_derivative`. -/
theorem exercise_3_G_3c {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (b : Fin L → ℝ)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (ub : ℝ) (l k : Fin L) :
    HasDerivAt (fun t => lesHicks a b (Function.update p k t) ub l) (lesSlutsky a p ub l k)
        (p k) ∧
      HasDerivAt (fun t => lesDemand a b (Function.update p k t) (lesExpenditure a b p ub) l)
        (lesPriceEffect a b p (lesExpenditure a b p ub) l k) (p k) ∧
      HasDerivAt (fun w => lesDemand a b p w l) (a l / p l) (lesExpenditure a b p ub) ∧
      lesSlutsky a p ub l k = lesPriceEffect a b p (lesExpenditure a b p ub) l k +
        (a l / p l) * lesDemand a b p (lesExpenditure a b p ub) k := by
  refine ⟨les_hicks_derivative ha b hp ub l k, les_price_derivative a b hp _ l k,
    les_wealth_derivative a b p _ l, ?_⟩
  have he : lesExpenditure a b p ub - p ⬝ᵥ b = ub * lesIndex a p := by
    simp [lesExpenditure, lesIndex]
  have hpl := (hp l).ne'
  have hpk := (hp k).ne'
  simp only [lesSlutsky, lesPriceEffect, lesDemand, he]
  split_ifs with h
  · subst h
    field_simp
    ring
  · field_simp
    ring

/-- **Exercise 3.G.3(d)** (MWG, p. 99). Own-substitution effects are negative (for `a_l < 1`,
which holds as soon as there are two goods) and compensated cross-price effects are
symmetric. -/
theorem exercise_3_G_3d {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 < ub) :
    (∀ l, a l < 1 → lesSlutsky a p ub l l < 0) ∧
      ∀ l k, lesSlutsky a p ub l k = lesSlutsky a p ub k l := by
  have hQ := lesIndex_pos ha hp
  refine ⟨fun l hl => ?_, fun l k => ?_⟩
  · simp only [lesSlutsky, ↓reduceIte]
    have hpl := hp l
    have hM : 0 < ub * lesIndex a p := mul_pos hub hQ
    have : a l * a l * (ub * lesIndex a p) / (p l * p l) - a l * (ub * lesIndex a p) / p l ^ 2 =
        a l * (a l - 1) * (ub * lesIndex a p) / p l ^ 2 := by
      field_simp
    rw [this]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (ha l) (by linarith)) hM) (by positivity)
  · simp only [lesSlutsky]
    by_cases h : l = k
    · subst h; rfl
    · simp only [h, Ne.symm h, ↓reduceIte]
      ring

/-- `(S z)_l = M a_l (ȳ - z_l/p_l)/p_l` with `ȳ = ∑ a_k z_k/p_k`. -/
theorem lesSlutsky_mulVec {L : ℕ} (a p : Fin L → ℝ) (hp : StrictlyPositive p) (ub : ℝ)
    (z : Fin L → ℝ) (l : Fin L) :
    (Matrix.of (lesSlutsky a p ub)).mulVec z l =
      ub * lesIndex a p * a l * ((∑ k, a k * (z k / p k)) - z l / p l) / p l := by
  have hpl := (hp l).ne'
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, lesSlutsky, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs : ∑ k, a l * a k * (ub * lesIndex a p) / (p l * p k) * z k =
      ub * lesIndex a p * a l / p l * ∑ k, a k * (z k / p k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpk := (hp k).ne'
    field_simp
  rw [hs]
  field_simp

/-- `∑ a_l y_l² - (∑ a_l y_l)² = ∑ a_l (y_l - ȳ)² ≥ 0` for weights summing to one. -/
theorem les_weighted_variance {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (y : Fin L → ℝ) :
    (∑ l, a l * y l) ^ 2 ≤ ∑ l, a l * y l ^ 2 := by
  have key : ∀ c : ℝ, ∑ l, a l * (y l - c) ^ 2 =
      ∑ l, a l * y l ^ 2 - 2 * c * ∑ l, a l * y l + c ^ 2 * ∑ l, a l := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h := key (∑ l, a l * y l)
  rw [hsum] at h
  have : 0 ≤ ∑ l, a l * (y l - ∑ k, a k * y k) ^ 2 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (ha l).le (sq_nonneg _)
  nlinarith

/-- **Exercise 3.G.3(e)** (MWG, p. 99). The substitution matrix `S` of the linear expenditure
system is negative semidefinite, and `S z = 0` exactly for `z` on the line through `p`; hence
`rank S = L - 1` (`= 2` for the book's three goods, `exercise_3_G_3e_three`). -/
theorem exercise_3_G_3e {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hsum : ∑ l, a l = 1)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 < ub) :
    NegSemidef (Matrix.of (lesSlutsky a p ub)) ∧
      (∀ z, (Matrix.of (lesSlutsky a p ub)).mulVec z = 0 ↔ ∃ c : ℝ, z = c • p) ∧
      (Matrix.of (lesSlutsky a p ub)).rank = L - 1 := by
  have hM : 0 < ub * lesIndex a p := mul_pos hub (lesIndex_pos ha hp)
  have hker : ∀ z, (Matrix.of (lesSlutsky a p ub)).mulVec z = 0 ↔ ∃ c : ℝ, z = c • p := by
    intro z
    constructor
    · intro h
      refine ⟨∑ k, a k * (z k / p k), funext fun l => ?_⟩
      have := congrFun h l
      rw [lesSlutsky_mulVec a p hp ub z l, Pi.zero_apply] at this
      have h1 : (∑ k, a k * (z k / p k)) - z l / p l = 0 := by
        rcases div_eq_zero_iff.1 this with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · rcases mul_eq_zero.1 h3 with h4 | h4
            · exact absurd h4 hM.ne'
            · exact absurd h4 (ha l).ne'
          · exact h3
        · exact absurd h2 (hp l).ne'
      have hpl := (hp l).ne'
      simp only [Pi.smul_apply, smul_eq_mul]
      have h2 : z l / p l = ∑ k, a k * (z k / p k) := (sub_eq_zero.1 h1).symm
      rw [div_eq_iff hpl] at h2
      exact h2
    · rintro ⟨c, rfl⟩
      funext l
      rw [lesSlutsky_mulVec a p hp ub _ l]
      have : ∀ k, a k * ((c • p) k / p k) = a k * c := by
        intro k
        simp [(hp k).ne']
      simp only [this, ← Finset.sum_mul, hsum, one_mul]
      simp [(hp l).ne']
  refine ⟨fun z => ?_, hker, ?_⟩
  · set y : Fin L → ℝ := fun l => z l / p l with hy
    have hq : z ⬝ᵥ (Matrix.of (lesSlutsky a p ub)).mulVec z =
        ub * lesIndex a p * ((∑ l, a l * y l) ^ 2 - ∑ l, a l * y l ^ 2) := by
      simp only [dotProduct, lesSlutsky_mulVec a p hp ub z]
      have : ∀ l ∈ Finset.univ, z l * (ub * lesIndex a p * a l *
          ((∑ k, a k * (z k / p k)) - z l / p l) / p l) =
          ub * lesIndex a p * ((∑ k, a k * y k) * (a l * y l) - a l * y l ^ 2) := by
        intro l _
        have hpl := (hp l).ne'
        simp only [hy]
        field_simp
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hq]
    exact mul_nonpos_of_nonneg_of_nonpos hM.le
      (sub_nonpos.2 (les_weighted_variance ha hsum y))
  · have hkerS : LinearMap.ker (Matrix.of (lesSlutsky a p ub)).mulVecLin = ℝ ∙ p := by
      ext z
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hker, Submodule.mem_span_singleton]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    have hp0 : p ≠ 0 := by
      intro h
      have hL : 0 < L := by
        by_contra h0
        push Not at h0
        have : L = 0 := by omega
        subst this
        simp at hsum
      have := hp ⟨0, hL⟩
      rw [h] at this
      simp at this
    have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.of (lesSlutsky a p ub)).mulVecLin
    rw [hkerS, finrank_span_singleton hp0, Module.finrank_fin_fun] at hrn
    unfold Matrix.rank
    omega

/-- **Exercise 3.G.3(e)** (MWG, p. 99), the book's case of three goods: `S(p, w)` is negative
semidefinite and has rank `2`. -/
theorem exercise_3_G_3e_three {a : Fin 3 → ℝ} (ha : ∀ l, 0 < a l) (hsum : ∑ l, a l = 1)
    {p : Fin 3 → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 < ub) :
    NegSemidef (Matrix.of (lesSlutsky a p ub)) ∧ (Matrix.of (lesSlutsky a p ub)).rank = 2 :=
  ⟨(exercise_3_G_3e ha hsum hp hub).1, (exercise_3_G_3e ha hsum hp hub).2.2⟩

end MWG.ClassicalDemand
