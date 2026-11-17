/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Profit
import MWGClassicalDemand.AppendixMC

/-!
# First-order conditions for profit maximization (MWG Section 5.C, pp. 136-137)

* (5.C.1): if `y* ∈ y(p)` for `Y = {y : F(y) ≤ 0}` with `F` differentiable at `y*` and
  `∇F(y*) ≠ 0`, then `p = λ∇F(y*)` for some `λ ≥ 0` (`foc_5_C_1`), and
  `p_l/p_k = MRT_{lk}(y*)` (`foc_5_C_1_ratio`). Sufficiency for convex `Y` (p. 137):
  `foc_5_C_1_sufficient`.
* (5.C.2): the single-output conditions `p ∂f(z*)/∂z_l ≤ w_l`, with equality if `z*_l > 0`
  (`foc_5_C_2`), `MRTS_{lk} = w_l/w_k` for interior inputs, and sufficiency for concave `f`
  (`foc_5_C_2_sufficient`).

Departure: (5.C.1) needs the constraint qualification `∇F(y*) ≠ 0`, which the book does not
state; `foc_5_C_1_needs_cq` is a transformation function `F(y) = (y₁ + y₂)³` with
`∇F(0) = 0` and `0 ∈ y(1, 1)`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- A real function with negative derivative at `0` is below `g 0` just to the right of `0`. -/
theorem eventually_lt_of_hasDerivAt_neg {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hd : d < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < g 0 := by
  filter_upwards [hg.tendsto_slope_zero_right.eventually (eventually_lt_nhds hd),
    self_mem_nhdsWithin] with t ht htpos
  rw [zero_add, smul_eq_mul] at ht
  have htpos' : (0 : ℝ) < t := htpos
  have : g t - g 0 < 0 := by
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg (inv_nonneg.mpr htpos'.le) h
    linarith
  linarith

/-- If `p` is not a nonnegative multiple of `g ≠ 0`, some direction `d` has `g·d < 0 < p·d`. -/
theorem exists_dir_of_not_nonneg_multiple {g p : Fin L → ℝ} (hg : g ≠ 0)
    (h : ¬ ∃ lam : ℝ, 0 ≤ lam ∧ p = lam • g) : ∃ d, g ⬝ᵥ d < 0 ∧ 0 < p ⬝ᵥ d := by
  have hgg : 0 < g ⬝ᵥ g := by
    have h0 : 0 ≤ g ⬝ᵥ g := Finset.sum_nonneg fun i _ => mul_self_nonneg (g i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hg (dotProduct_self_eq_zero.mp h))
  set μ := (p ⬝ᵥ g) / (g ⬝ᵥ g) with hμ
  set r := p - μ • g with hr
  have hgr : g ⬝ᵥ r = 0 := by
    rw [hr, dotProduct_sub, dotProduct_smul, smul_eq_mul, hμ, dotProduct_comm g p]
    field_simp
    ring
  have hpr : p ⬝ᵥ r = r ⬝ᵥ r := by
    have : p = r + μ • g := by rw [hr]; abel
    conv_lhs => rw [this]
    rw [add_dotProduct, smul_dotProduct, hgr, smul_zero, add_zero]
  by_cases hr0 : r = 0
  · have hp : p = μ • g := by rw [← sub_eq_zero, ← hr, hr0]
    have hμneg : μ < 0 := by
      by_contra hμ0
      exact h ⟨μ, not_lt.mp hμ0, hp⟩
    refine ⟨-g, by rw [dotProduct_neg]; linarith, ?_⟩
    rw [hp, dotProduct_neg, smul_dotProduct, smul_eq_mul]
    nlinarith
  · have hrr : 0 < r ⬝ᵥ r := by
      have h0 : 0 ≤ r ⬝ᵥ r := Finset.sum_nonneg fun i _ => mul_self_nonneg (r i)
      exact lt_of_le_of_ne h0 (Ne.symm fun h => hr0 (dotProduct_self_eq_zero.mp h))
    set s := (r ⬝ᵥ r) / (|p ⬝ᵥ g| + 1) with hs
    have hspos : 0 < s := by positivity
    refine ⟨r - s • g, ?_, ?_⟩
    · rw [dotProduct_sub, hgr, dotProduct_smul, smul_eq_mul]
      nlinarith
    · rw [dotProduct_sub, hpr, dotProduct_smul, smul_eq_mul]
      have h1 : s * (|p ⬝ᵥ g| + 1) = r ⬝ᵥ r := by rw [hs]; field_simp
      nlinarith [le_abs_self (p ⬝ᵥ g)]

/-- **Section 5.C** (MWG, p. 136), condition (5.C.1). Let `Y = {y : F(y) ≤ 0}`, `y* ∈ y(p)`, and
`F` differentiable at `y*` with `∇F(y*) ≠ 0`. Then `p = λ∇F(y*)` for some `λ ≥ 0`. -/
theorem foc_5_C_1 {F : (Fin L → ℝ) → ℝ} {p y : Fin L → ℝ}
    (hy : y ∈ supply {y | F y ≤ 0} p) (hF : DifferentiableAt ℝ F y)
    (hcq : gradientVec (fderiv ℝ F y) ≠ 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ p = lam • gradientVec (fderiv ℝ F y) := by
  by_contra h
  obtain ⟨d, hgd, hpd⟩ := exists_dir_of_not_nonneg_multiple hcq h
  have hline := mc_line_hasDerivAt hF.hasFDerivAt d
  rw [fderiv_apply_eq_gradient_dot] at hline
  have hev := eventually_lt_of_hasDerivAt_neg hline hgd
  obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  simp only [zero_smul, add_zero] at ht
  have hmem : y + t • d ∈ {y | F y ≤ 0} := le_of_lt (ht.trans_le hy.1)
  have := hy.2 _ hmem
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have htpos' : (0 : ℝ) < t := htpos
  nlinarith

/-- **Section 5.C** (MWG, p. 137). Under (5.C.1) with `p ≫ 0` and `∂F(y*)/∂y_k ≠ 0`:
`p_l/p_k = MRT_{lk}(y*)`. -/
theorem foc_5_C_1_ratio {F : (Fin L → ℝ) → ℝ} {p y : Fin L → ℝ} (hp : StrictlyPositive p)
    (hy : y ∈ supply {y | F y ≤ 0} p) (hF : DifferentiableAt ℝ F y)
    (hcq : gradientVec (fderiv ℝ F y) ≠ 0) (l k : Fin L) :
    p l / p k = MRT F y l k := by
  obtain ⟨lam, _, hlam⟩ := foc_5_C_1 hy hF hcq
  have hl : p l = lam * partialAt F y l := by
    have := congrFun hlam l
    simpa [gradientVec, partialAt] using this
  have hk : p k = lam * partialAt F y k := by
    have := congrFun hlam k
    simpa [gradientVec, partialAt] using this
  have hlam0 : lam ≠ 0 := by
    intro h0
    have := hp k
    rw [hk, h0, zero_mul] at this
    exact lt_irrefl 0 this
  rw [hl, hk, MRT, mul_div_mul_left _ _ hlam0]

/-- **Section 5.C** (MWG, p. 137), sufficiency of (5.C.1) for convex `Y = {y : F(y) ≤ 0}`: if
`F(y*) = 0`, `F` is differentiable at `y*` and `p = λ∇F(y*)` with `λ ≥ 0`, then `y* ∈ y(p)`. -/
theorem foc_5_C_1_sufficient {F : (Fin L → ℝ) → ℝ} (hc : Convex ℝ {y | F y ≤ 0})
    {p y : Fin L → ℝ} (hy0 : F y = 0) (hF : DifferentiableAt ℝ F y) {lam : ℝ}
    (hlam : 0 ≤ lam) (hp : p = lam • gradientVec (fderiv ℝ F y)) :
    y ∈ supply {y | F y ≤ 0} p := by
  refine ⟨le_of_eq hy0, fun y' hy' => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rcases hlam.lt_or_eq with hpos | hzero
  · have hgd : 0 < gradientVec (fderiv ℝ F y) ⬝ᵥ (y' - y) := by
      have : 0 < p ⬝ᵥ (y' - y) := by rw [dotProduct_sub]; linarith
      rw [hp, smul_dotProduct, smul_eq_mul] at this
      exact pos_of_mul_pos_right this hpos.le
    have hline := mc_line_hasDerivAt hF.hasFDerivAt (y' - y)
    rw [fderiv_apply_eq_gradient_dot] at hline
    have hev := eventually_lt_of_hasDerivAt_neg hline.neg (neg_lt_zero.mpr hgd)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := by
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds one_pos)] with t ht
      exact ht
    obtain ⟨t, ⟨ht, ht1⟩, htpos⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
    have ht0 : 0 < F (y + t • (y' - y)) := by simpa [hy0] using ht
    have htpos' : (0 : ℝ) < t := htpos
    have hmem : y + t • (y' - y) ∈ {y | F y ≤ 0} := by
      have := hc (show y ∈ {y | F y ≤ 0} from le_of_eq hy0) hy' (by linarith : (0 : ℝ) ≤ 1 - t)
        htpos'.le (by ring)
      have heq : (1 - t) • y + t • y' = y + t • (y' - y) := by module
      rwa [heq] at this
    have : F (y + t • (y' - y)) ≤ 0 := hmem
    linarith
  · rw [← hzero, zero_smul] at hp
    rw [hp, zero_dotProduct, zero_dotProduct] at hlt
    exact lt_irrefl 0 hlt

/-- The transformation function `F(y) = (y₁ + y₂)³` of the half-plane `{y₁ + y₂ ≤ 0}`. -/
def cubeTransformation (y : Fin 2 → ℝ) : ℝ := (y 0 + y 1) ^ 3

/-- **(5.C.1)** needs a constraint qualification (correction): `F(y) = (y₁ + y₂)³` is a
transformation function for `Y = {y₁ + y₂ ≤ 0}`, differentiable with `∇F(0) = 0`, and
`0 ∈ y(1, 1)`, but `(1, 1) ≠ λ∇F(0)` for every `λ`. -/
theorem foc_5_C_1_needs_cq :
    IsTransformationFunction cubeTransformation {y | cubeTransformation y ≤ 0} ∧
      DifferentiableAt ℝ cubeTransformation 0 ∧
      gradientVec (fderiv ℝ cubeTransformation 0) = 0 ∧
      (0 : Fin 2 → ℝ) ∈ supply {y | cubeTransformation y ≤ 0} ![1, 1] ∧
      ¬ ∃ lam : ℝ, (![1, 1] : Fin 2 → ℝ) =
        lam • gradientVec (fderiv ℝ cubeTransformation 0) := by
  have hiff : ∀ y : Fin 2 → ℝ, cubeTransformation y ≤ 0 ↔ y 0 + y 1 ≤ 0 := fun y =>
    Odd.pow_nonpos_iff (by decide)
  have hset : {y | cubeTransformation y ≤ 0} = {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} := by
    ext y
    exact hiff y
  have a := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)
  have b := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
  have h2 := (a.fun_add b).pow 3
  have hcube : cubeTransformation = fun x : Fin 2 → ℝ => (x 0 + x 1) ^ 3 := rfl
  have hgrad : gradientVec (fderiv ℝ cubeTransformation 0) = 0 := by
    rw [hcube, h2.fderiv]
    funext i
    simp [gradientVec]
  refine ⟨⟨rfl, fun y => ?_⟩, by rw [hcube]; exact h2.differentiableAt, hgrad, ?_, ?_⟩
  · rw [hset, ← isTransformationFunction_halfPlane.2 y, cubeTransformation]
    exact pow_eq_zero_iff (by norm_num)
  · refine ⟨show cubeTransformation 0 ≤ 0 by simp [cubeTransformation], fun y' hy' => ?_⟩
    have := (hiff y').mp hy'
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      Pi.zero_apply, mul_zero, add_zero]
    linarith
  · rintro ⟨lam, h⟩
    rw [hgrad, smul_zero] at h
    have := congrFun h 0
    simp at this

/-! ### The single-output case (5.C.2) -/

/-- **Section 5.C** (MWG, p. 137), condition (5.C.2). If `z* ≥ 0` maximizes `p f(z) - w·z` over
`z ≥ 0` and `f` is differentiable at `z*`, then `p ∂f(z*)/∂z_l ≤ w_l` for every input, with
equality when `z*_l > 0`; in matrix form `p∇f(z*) ≤ w` and `[p∇f(z*) - w]·z* = 0`. -/
theorem foc_5_C_2 {n : ℕ} {f : (Fin n → ℝ) → ℝ} {p : ℝ} {w z : Fin n → ℝ} (hz : 0 ≤ z)
    (hopt : ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z)
    (hf : DifferentiableAt ℝ f z) :
    (∀ l, p * partialF f z l ≤ w l) ∧ (∀ l, 0 < z l → p * partialF f z l = w l) ∧
      (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0 := by
  have hline : ∀ l, HasDerivAt (fun t : ℝ => p * f (z + t • Pi.single l 1) -
      w ⬝ᵥ (z + t • Pi.single l 1)) (p * partialF f z l - w l) 0 := by
    intro l
    have h1 := (mc_line_hasDerivAt hf.hasFDerivAt (Pi.single l 1)).const_mul p
    have h2 : HasDerivAt (fun t : ℝ => w ⬝ᵥ (z + t • Pi.single l 1)) (w l) 0 := by
      have : (fun t : ℝ => w ⬝ᵥ (z + t • Pi.single l 1)) = fun t => w ⬝ᵥ z + t * w l := by
        funext t
        rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w l)).const_add (w ⬝ᵥ z)
    exact h1.sub h2
  have hle : ∀ l, p * partialF f z l ≤ w l := by
    intro l
    have := hasDerivAt_nonpos_of_right_le (hline l) ?_
    · linarith
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [zero_smul, add_zero]
    apply hopt
    exact add_nonneg hz (smul_nonneg ht'.le (Pi.single_nonneg.mpr zero_le_one))
  have heq : ∀ l, 0 < z l → p * partialF f z l = w l := by
    intro l hzl
    apply le_antisymm (hle l)
    have hl' := hline l
    rw [← neg_zero] at hl'
    have hneg := hl'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simp only [mul_neg, mul_one] at hneg
    have := hasDerivAt_nonpos_of_right_le hneg ?_
    · linarith
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < z l :=
      nhdsWithin_le_nhds (eventually_lt_nhds hzl)
    filter_upwards [self_mem_nhdsWithin, hI] with t ht htz
    have ht' : (0 : ℝ) < t := ht
    simp only [Function.comp_apply, neg_zero, zero_smul, add_zero]
    apply hopt
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.zero_apply]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero,
        add_zero, Pi.zero_apply]
      exact hz i
  refine ⟨hle, heq, ?_⟩
  apply Finset.sum_eq_zero
  intro l _
  change (p * partialF f z l - w l) * z l = 0
  have hzl : (0 : ℝ) ≤ z l := hz l
  rcases hzl.lt_or_eq with hpos | hzero
  · rw [heq l hpos, sub_self, zero_mul]
  · rw [← hzero, mul_zero]

/-- **Section 5.C** (MWG, p. 137). Under (5.C.2) with `p > 0`, two inputs used in positive amounts
have `MRTS_{lk}(z*) = w_l/w_k` (for `w_k ≠ 0`). -/
theorem foc_5_C_2_mrts {n : ℕ} {f : (Fin n → ℝ) → ℝ} {p : ℝ} {w z : Fin n → ℝ} (hz : 0 ≤ z)
    (hopt : ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z)
    (hf : DifferentiableAt ℝ f z) (hp : 0 < p) {l k : Fin n} (hl : 0 < z l) (hk : 0 < z k) :
    MRTS f z l k = w l / w k := by
  obtain ⟨-, heq, -⟩ := foc_5_C_2 hz hopt hf
  rw [MRTS, ← heq l hl, ← heq k hk, mul_div_mul_left _ _ hp.ne']

/-- A concave function lies below its tangent plane at a point of differentiability. -/
theorem concave_le_tangent {n : ℕ} {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ A f) {x y : Fin n → ℝ} (hx : x ∈ A) (hy : y ∈ A)
    (hf : DifferentiableAt ℝ f x) : f y ≤ f x + fderiv ℝ f x (y - x) := by
  have hd := mc_line_hasDerivAt hf.hasFDerivAt (y - x)
  have key : f y - f x ≤ fderiv ℝ f x (y - x) := by
    apply mc_le_deriv_of_slope hd
    intro t ht0 ht1
    have hconc := hc.2 hy hx ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    have heq : t • y + (1 - t) • x = x + t • (y - x) := by module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconc
    simp only [zero_smul, add_zero]
    rw [le_div_iff₀ ht0]
    linarith
  linarith

/-- **Section 5.C** (MWG, p. 137), sufficiency of (5.C.2): if `f` is concave on `ℝ^{L-1}_+`
(equivalently `Y` is convex, Exercise 5.B.3), differentiable at `z* ≥ 0`, and (5.C.2) holds,
then `z*` maximizes `p f(z) - w·z` over `z ≥ 0` (for `p ≥ 0`). -/
theorem foc_5_C_2_sufficient {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {p : ℝ} (hp : 0 ≤ p) {w z : Fin n → ℝ}
    (hz : 0 ≤ z) (hf : DifferentiableAt ℝ f z) (hle : ∀ l, p * partialF f z l ≤ w l)
    (hcs : (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0) :
    ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z := by
  intro z' hz'
  have htan := concave_le_tangent hc hz hz' hf
  have hgrad : fderiv ℝ f z (z' - z) = (fun l => partialF f z l) ⬝ᵥ (z' - z) := by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  rw [hgrad] at htan
  have h1 : (fun l => p * partialF f z l - w l) ⬝ᵥ z' ≤ 0 := by
    apply Finset.sum_nonpos
    intro l _
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle l]) (hz' l)
  have h2 : p * ((fun l => partialF f z l) ⬝ᵥ (z' - z)) =
      (fun l => p * partialF f z l - w l) ⬝ᵥ z' - (fun l => p * partialF f z l - w l) ⬝ᵥ z
        + w ⬝ᵥ z' - w ⬝ᵥ z := by
    simp only [dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.sub_apply]
    ring
  have h3 := mul_le_mul_of_nonneg_left htan hp
  rw [mul_add, h2, hcs] at h3
  linarith

end MWG.Production
