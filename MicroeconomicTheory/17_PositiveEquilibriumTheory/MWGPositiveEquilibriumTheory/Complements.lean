/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17FMore
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Complementary inputs (MWG Exercise 17.F.14, p. 646)

A firm produces good 1 from the inputs `v = (v₂, …, v_L)` (here `v ∈ ℝ^n`) with production
function `f`. Inputs `ℓ, ℓ'` are complements at `v` if `∂²f/∂vₗ∂vₗ' > 0` (`secondPartial`,
`InputComplements`).

* **(a)** (`exercise_17_F_14a`) For Cobb-Douglas `f = ∏ vⱼ^{αⱼ}` (`αⱼ > 0`) any two inputs are
  complements at every `v ≫ 0`: `∂²f/∂vₗ∂vₗ' = αₗαₗ' f(v)/(vₗvₗ')` (the bound `∑ αⱼ ≤ 1` is not
  needed).
* **(b)** (`exercise_17_F_14b`) With constant returns, `∑ₗ' vₗ' ∂²f/∂vₗ∂vₗ' = 0` (Euler for the
  degree-zero `∂f/∂vₗ`), so if `∂²f/∂vₗ² < 0` some `ℓ' ≠ ℓ` is a complement to `ℓ`. As printed
  (only concavity) the claim is false: the linear `f = v₁ + v₂` is concave, increasing, `C²`, of
  constant returns, and has no complements (`exercise_17_F_14b_counter`; corrections).
* **(c)** (`exercise_17_F_14c`) If the Hessian `D²f` is negative definite and all inputs are
  complements, then differentiating the first-order conditions `p₁ ∇f(v(p)) = w` gives
  `∂vₗ/∂p₁ > 0`, `∂vₗ/∂wₗ < 0` and `∂vₗ/∂wₗ' < 0`: the inverse of a negative definite matrix with
  positive off-diagonal entries has all entries negative (`cmp_inv_neg`). (The book assumes strict
  concavity, which gives only a negative semidefinite Hessian; corrections.)
* **(d)** is a discussion (listed (verbal)): by (c), input demands are gross complements
  (`∂vₗ/∂wₗ' < 0`), so the gross substitute property fails for the factor demands of such a firm.
-/

namespace MWG.PositiveEquilibriumTheory

variable {n : ℕ}

/-- **Exercise 17.F.14** (MWG, p. 646). `∂²f/∂vₗ∂vₗ'(v)`: the derivative in direction `eˡ'` of
`w ↦ ∂f/∂vₗ(w)`. -/
noncomputable def secondPartial (f : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ) (l l' : Fin n) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ f w (Pi.single l 1)) v (Pi.single l' 1)

/-- **Exercise 17.F.14** (MWG, p. 646). Inputs `ℓ` and `ℓ'` are complements at `v`:
`∂²f/∂vₗ∂vₗ' > 0`. -/
def InputComplements (f : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ) (l l' : Fin n) : Prop :=
  0 < secondPartial f v l l'

/-! ### (a) Cobb-Douglas -/

/-- The Cobb-Douglas production function `∏ⱼ vⱼ^{αⱼ}`. -/
noncomputable def cdProduction (α v : Fin n → ℝ) : ℝ := ∏ j, v j ^ α j

/-- `h_β(w) = exp(∑ βⱼ log wⱼ)`. -/
noncomputable def cmpH (β w : Fin n → ℝ) : ℝ := Real.exp (∑ j, β j * Real.log (w j))

/-- The derivative of `h_β` at `w ≫ 0`: `v ↦ h_β(w) ∑ βⱼvⱼ/wⱼ`. -/
noncomputable def cmpD (β w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  cmpH β w • ∑ j, (β j / w j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j

theorem cmpD_single (β w : Fin n → ℝ) (l : Fin n) :
    cmpD β w (Pi.single l 1) = cmpH β w * (β l / w l) := by
  simp [cmpD, Pi.single_apply]

theorem cmp_hasFDerivAt (β : Fin n → ℝ) {w : Fin n → ℝ} (hw : ∀ j, 0 < w j) :
    HasFDerivAt (cmpH β) (cmpD β w) w := by
  have hS : HasFDerivAt (fun w : Fin n → ℝ => ∑ j, β j * Real.log (w j))
      (∑ j, (β j / w j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) w := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h := ((hasFDerivAt_apply j w).log (hw j).ne').const_mul (β j)
    convert h using 1
    ext v
    simp [div_eq_mul_inv]
    ring
  exact hS.exp

/-- On `ℝ^n_{++}`, `∏ vⱼ^{αⱼ} = exp(∑ αⱼ log vⱼ)`. -/
theorem cdProduction_eq {α w : Fin n → ℝ} (hw : ∀ j, 0 < w j) : cdProduction α w = cmpH α w := by
  rw [cdProduction, cmpH, Real.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Real.rpow_def_of_pos (hw j), mul_comm]

theorem cmp_eventually_pos {v : Fin n → ℝ} (hv : ∀ j, 0 < v j) :
    ∀ᶠ w in nhds v, ∀ j, 0 < w j :=
  Filter.eventually_all.2 fun j =>
    continuousAt_const.eventually_lt (continuous_apply j).continuousAt (hv j)

/-- `h_α(w)/wₗ = h_{α - eˡ}(w)`. -/
theorem cmpH_div {α w : Fin n → ℝ} (hw : ∀ j, 0 < w j) (l : Fin n) :
    cmpH α w / w l = cmpH (α - Pi.single l 1) w := by
  have hS : ∑ j, (α - Pi.single l 1 : Fin n → ℝ) j * Real.log (w j) =
      ∑ j, α j * Real.log (w j) - Real.log (w l) := by
    simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  rw [cmpH, cmpH, hS, Real.exp_sub, Real.exp_log (hw l)]

/-- **Exercise 17.F.14(a)** (MWG, p. 646). For the Cobb-Douglas production function
`f(v) = ∏ vⱼ^{αⱼ}` with `αⱼ > 0`, any two distinct inputs are complements at any `v ≫ 0`:
`∂²f/∂vₗ∂vₗ' = αₗαₗ' f(v)/(vₗvₗ') > 0`. -/
theorem exercise_17_F_14a {α : Fin n → ℝ} (hα : ∀ j, 0 < α j) {v : Fin n → ℝ}
    (hv : ∀ j, 0 < v j) {l l' : Fin n} (hll : l ≠ l') :
    secondPartial (cdProduction α) v l l' =
        α l * α l' * cdProduction α v / (v l * v l') ∧
      InputComplements (cdProduction α) v l l' := by
  -- `∂f/∂vₗ = αₗ h_{α - eˡ}` near `v`
  have hfd : ∀ w : Fin n → ℝ, (∀ j, 0 < w j) →
      fderiv ℝ (cdProduction α) w (Pi.single l 1) = α l * cmpH (α - Pi.single l 1) w := by
    intro w hw
    have h : HasFDerivAt (cdProduction α) (cmpD α w) w :=
      (cmp_hasFDerivAt α hw).congr_of_eventuallyEq
        ((cmp_eventually_pos hw).mono fun u hu => cdProduction_eq hu)
    rw [h.fderiv, cmpD_single, ← cmpH_div hw]
    ring
  have hG : HasFDerivAt (fun w => fderiv ℝ (cdProduction α) w (Pi.single l 1))
      (α l • cmpD (α - Pi.single l 1) v) v :=
    ((cmp_hasFDerivAt (α - Pi.single l 1) hv).const_mul (α l)).congr_of_eventuallyEq
      ((cmp_eventually_pos hv).mono fun u hu => hfd u hu)
  have hval : secondPartial (cdProduction α) v l l' =
      α l * α l' * cdProduction α v / (v l * v l') := by
    rw [secondPartial, hG.fderiv]
    change α l * cmpD (α - Pi.single l 1) v (Pi.single l' 1) = _
    rw [cmpD_single, ← cmpH_div hv, ← cdProduction_eq hv]
    have hne : Pi.single (M := fun _ : Fin n => ℝ) l (1 : ℝ) l' = 0 := by
      simp [hll.symm]
    simp only [Pi.sub_apply, hne, sub_zero]
    have := (hv l).ne'
    have := (hv l').ne'
    field_simp
  refine ⟨hval, ?_⟩
  rw [InputComplements, hval]
  have hf : 0 < cdProduction α v := by rw [cdProduction_eq hv]; exact Real.exp_pos _
  exact div_pos (mul_pos (mul_pos (hα l) (hα l')) hf) (mul_pos (hv l) (hv l'))

/-! ### (b) Constant returns -/

/-- `D v = ∑ₗ vₗ D eˡ` for a linear functional. -/
theorem cmp_apply_eq_sum (D : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    D v = ∑ k, v k * D (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (v k) : Fin n → ℝ) = v k • Pi.single k (1 : ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

/-- With constant returns, `∇f` is homogeneous of degree zero: `Df(tw) = Df(w)` for `t > 0`. -/
theorem cmp_fderiv_smul {f : (Fin n → ℝ) → ℝ}
    (hdiff : ∀ w ∈ posOrthant n, DifferentiableAt ℝ f w)
    (hcrs : ∀ w ∈ posOrthant n, ∀ t : ℝ, 0 < t → f (t • w) = t * f w) {w : Fin n → ℝ}
    (hw : w ∈ posOrthant n) {t : ℝ} (ht : 0 < t) : fderiv ℝ f (t • w) = fderiv ℝ f w := by
  have htw := smul_mem_posOrthant hw ht
  have h1 : HasFDerivAt (fun u => f (t • u))
      ((fderiv ℝ f (t • w)).comp (t • ContinuousLinearMap.id ℝ (Fin n → ℝ))) w :=
    (hdiff _ htw).hasFDerivAt.comp w ((hasFDerivAt_id w).const_smul t)
  have h2 : HasFDerivAt (fun u => f (t • u)) (t • fderiv ℝ f w) w := by
    have := ((hdiff w hw).hasFDerivAt.const_mul t)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_posOrthant n).mem_nhds hw] with u hu
    exact hcrs u hu t ht
  have h := h1.unique h2
  ext x
  have := congrArg (fun T : (Fin n → ℝ) →L[ℝ] ℝ => T x) h
  have e1 : ((fderiv ℝ f (t • w)).comp (t • ContinuousLinearMap.id ℝ (Fin n → ℝ))) x =
      t * fderiv ℝ f (t • w) x := by simp
  have e2 : (t • fderiv ℝ f w) x = t * fderiv ℝ f w x := rfl
  rw [e1, e2] at this
  exact mul_left_cancel₀ ht.ne' this

/-- **Exercise 17.F.14(b)** (MWG, p. 646), corrected. If `f` has constant returns
(`f(tw) = tf(w)`, `t > 0`) and is differentiable on `ℝ^n_{++}`, and `∂f/∂vₗ` is differentiable at
`v ≫ 0`, then `∑ₗ' vₗ' ∂²f/∂vₗ∂vₗ' = 0`; hence if `∂²f/∂vₗ² < 0` there is an input `ℓ' ≠ ℓ` that is
a complement to `ℓ` at `v`. -/
theorem exercise_17_F_14b {f : (Fin n → ℝ) → ℝ}
    (hdiff : ∀ w ∈ posOrthant n, DifferentiableAt ℝ f w)
    (hcrs : ∀ w ∈ posOrthant n, ∀ t : ℝ, 0 < t → f (t • w) = t * f w) {v : Fin n → ℝ}
    (hv : v ∈ posOrthant n) (l : Fin n)
    (hG : DifferentiableAt ℝ (fun w => fderiv ℝ f w (Pi.single l 1)) v) :
    ∑ l', v l' * secondPartial f v l l' = 0 ∧
      (secondPartial f v l l < 0 → ∃ l', l' ≠ l ∧ InputComplements f v l l') := by
  set G := fun w => fderiv ℝ f w (Pi.single l 1) with hGdef
  -- `t ↦ G(tv)` is constant near `t = 1`
  have hline : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have h1 : HasDerivAt (fun t : ℝ => G (t • v)) (fderiv ℝ G v v) 1 :=
    hG.hasFDerivAt.comp_hasDerivAt_of_eq 1 hline (by simp)
  have h2 : HasDerivAt (fun t : ℝ => G (t • v)) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (G v)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with t ht
    simp only [hGdef, cmp_fderiv_smul hdiff hcrs hv ht]
  have hsum : ∑ l', v l' * secondPartial f v l l' = 0 := by
    rw [← h1.unique h2, cmp_apply_eq_sum]
    rfl
  refine ⟨hsum, fun hneg => ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : ∀ l', l' ≠ l → v l' * secondPartial f v l l' ≤ 0 := fun l' hl' =>
    mul_nonpos_of_nonneg_of_nonpos (hv l').le (not_lt.1 (hcon l' hl'))
  have : ∑ l', v l' * secondPartial f v l l' < 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have h3 := Finset.sum_nonpos fun l' (hl' : l' ∈ Finset.univ.erase l) =>
      hle l' (Finset.ne_of_mem_erase hl')
    have h4 := mul_neg_of_pos_of_neg (hv l) hneg
    linarith
  linarith

/-- The linear production function `f(v) = v₁ + v₂`. -/
noncomputable def cmpLinear : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

/-- **Exercise 17.F.14(b)** (MWG, p. 646), as printed, is false: `f(v) = v₁ + v₂` is concave,
increasing, twice continuously differentiable and of the constant returns type, but
`∂²f/∂vₗ∂vₗ' = 0` everywhere, so no input is a complement to any other. -/
theorem exercise_17_F_14b_counter :
    ConcaveOn ℝ Set.univ (cmpLinear : (Fin 2 → ℝ) → ℝ) ∧
      (∀ v w : Fin 2 → ℝ, v ≤ w → v ≠ w → cmpLinear v < cmpLinear w) ∧
      ContDiff ℝ 2 (cmpLinear : (Fin 2 → ℝ) → ℝ) ∧
      (∀ v : Fin 2 → ℝ, ∀ t : ℝ, 0 < t → cmpLinear (t • v) = t * cmpLinear v) ∧
      ∀ v : Fin 2 → ℝ, ∀ l l', ¬ InputComplements (cmpLinear : (Fin 2 → ℝ) → ℝ) v l l' := by
  refine ⟨cmpLinear.toLinearMap.concaveOn convex_univ, fun v w hvw hne => ?_, cmpLinear.contDiff,
    fun v t _ => by rw [map_smul, smul_eq_mul], fun v l l' => ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, v j < w j := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun i => le_antisymm (hvw i) (hcon i))
    change v 0 + v 1 < w 0 + w 1
    have h0 := hvw 0
    have h1 := hvw 1
    fin_cases j <;> simp at hj <;> linarith
  · have hconst : (fun w => fderiv ℝ (cmpLinear : (Fin 2 → ℝ) → ℝ) w (Pi.single l 1)) =
        fun _ => cmpLinear (Pi.single l 1) := by
      funext w; rw [ContinuousLinearMap.fderiv]
    rw [InputComplements, secondPartial, hconst]
    simp

/-! ### (c) Input demand -/

/-- The inverse of a negative definite matrix with positive off-diagonal entries has all its
entries negative. -/
theorem cmp_inv_neg {H : Matrix (Fin n) (Fin n) ℝ} (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ H.mulVec v < 0)
    (hoff : ∀ i j, i ≠ j → 0 < H i j) : IsUnit H.det ∧ ∀ i j, H⁻¹ i j < 0 := by
  obtain ⟨hu, -⟩ := cs_inv_nd hnd
  refine ⟨hu, fun i j => ?_⟩
  set y := H⁻¹.mulVec (Pi.single j 1) with hy
  have hHy : H.mulVec y = Pi.single j 1 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hyi : y i = H⁻¹ i j := by simp [hy]
  -- `y ≤ 0`
  set yp : Fin n → ℝ := fun k => max (y k) 0 with hyp
  set ym : Fin n → ℝ := fun k => max (-y k) 0 with hym
  have hsplit : y = yp - ym := by
    funext k; simp only [hyp, hym, Pi.sub_apply]
    rcases le_total (y k) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hcross : 0 ≤ yp ⬝ᵥ H.mulVec ym := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun m _ => ?_
    by_cases hkm : k = m
    · subst hkm
      simp only [hyp, hym]
      rcases le_total (y k) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_right (by linarith : -y k ≤ 0)]; simp
    · exact mul_nonneg (le_max_right _ _) (mul_nonneg (hoff k m hkm).le (le_max_right _ _))
  have hj : yp ⬝ᵥ H.mulVec y = yp j := by rw [hHy, dotProduct_single, mul_one]
  have hpp : 0 ≤ yp ⬝ᵥ H.mulVec yp := by
    rw [hsplit, Matrix.mulVec_sub, dotProduct_sub] at hj
    linarith [le_max_right (y j) 0]
  have hyp0 : yp = 0 := by
    by_contra h
    linarith [hnd yp h]
  have hle : ∀ k, y k ≤ 0 := fun k => by
    have := congrFun hyp0 k
    simp only [hyp, Pi.zero_apply] at this
    rw [← this]; exact le_max_left _ _
  -- strictly negative
  rw [← hyi]
  rcases (hle i).lt_or_eq with h | h
  · exact h
  · exfalso
    have hterm : ∀ k, H i k * y k ≤ 0 := fun k => by
      by_cases hk : k = i
      · subst hk; rw [h, mul_zero]
      · exact mul_nonpos_of_nonneg_of_nonpos (hoff i k (Ne.symm hk)).le (hle k)
    have hrow := congrFun hHy i
    simp only [Matrix.mulVec, dotProduct] at hrow
    by_cases hij : i = j
    · subst hij
      simp only [Pi.single_eq_same] at hrow
      linarith [Finset.sum_nonpos fun k (_ : k ∈ Finset.univ) => hterm k]
    · simp only [Pi.single_apply, hij, ↓reduceIte] at hrow
      have hall := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).1 hrow
      have hy0 : y = 0 := funext fun k => by
        by_cases hk : k = i
        · subst hk; exact h
        · rcases mul_eq_zero.1 (hall k (Finset.mem_univ k)) with h1 | h1
          · exact absurd h1 (hoff i k (Ne.symm hk)).ne'
          · exact h1
      have := congrFun hHy j
      rw [hy0, Matrix.mulVec_zero] at this
      simp at this

/-- **Exercise 17.F.14(c)** (MWG, p. 646). Let `v(p₁, w)` be the input demand function (output
price `p₁`, input prices `w`), differentiable at `(p̄₁, w̄)`, satisfying the first-order
conditions `p₁ ∇f(v(p₁, w)) = w` near `(p̄₁, w̄)`; let `∇f` be differentiable at `v̄ = v(p̄₁, w̄)`
with Hessian `H` negative definite, `∇f(v̄) ≫ 0` (`f` increasing), and every two inputs complements
(`Hₗₗ' > 0`). Then `∂vₗ/∂p₁ > 0`, `∂vₗ/∂wₗ < 0` and `∂vₗ/∂wₗ' < 0` for `ℓ' ≠ ℓ`. -/
theorem exercise_17_F_14c {G : (Fin n → ℝ) → Fin n → ℝ} {V : ℝ × (Fin n → ℝ) → Fin n → ℝ}
    {P : ℝ × (Fin n → ℝ)} (hp1 : 0 < P.1) {V' : ℝ × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hV : HasFDerivAt V V' P) {H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hG : HasFDerivAt G H (V P))
    (hfoc : ∀ᶠ P' in nhds P, P'.1 • G (V P') = P'.2)
    (hnd : ∀ u, u ≠ 0 → u ⬝ᵥ H u < 0) (hcomp : ∀ l l', l ≠ l' → 0 < H (Pi.single l' 1) l)
    (hgrad : ∀ l, 0 < G (V P) l) :
    (∀ l, 0 < V' (1, 0) l) ∧ ∀ l j, V' (0, Pi.single j 1) l < 0 := by
  -- differentiate the first-order conditions
  have hΦ : HasFDerivAt (fun P' : ℝ × (Fin n → ℝ) => P'.1 • G (V P') - P'.2)
      ((P.1 • H.comp V' + (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight (G (V P))) -
        ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) P :=
    (hasFDerivAt_fst.smul (hG.comp P hV)).sub hasFDerivAt_snd
  have hΦ0 : HasFDerivAt (fun P' : ℝ × (Fin n → ℝ) => P'.1 • G (V P') - P'.2)
      (0 : ℝ × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) P :=
    (hasFDerivAt_const (0 : Fin n → ℝ) P).congr_of_eventuallyEq
      (hfoc.mono fun P' h => by
        change P'.1 • G (V P') - P'.2 = 0
        rw [h, sub_self])
  have hD := hΦ.unique hΦ0
  have hdir : ∀ d : ℝ × (Fin n → ℝ), P.1 • H (V' d) + d.1 • G (V P) - d.2 = 0 := fun d => by
    have := congrArg (fun T : ℝ × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T d) hD
    simpa using this
  set Hm := LinearMap.toMatrix' (H : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hHm
  have hHv : ∀ u, Hm.mulVec u = H u := fun u => by rw [hHm, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨hu, hneg⟩ := cmp_inv_neg (H := Hm) (fun u hu => by rw [hHv]; exact hnd u hu)
    (fun i j hij => by rw [hHm, LinearMap.toMatrix'_apply]; exact hcomp i j hij)
  -- `p̄₁ H y = b` gives `y = (1/p̄₁) H⁻¹ b`
  have hsolve : ∀ (y b : Fin n → ℝ), P.1 • H y = b → y = P.1⁻¹ • Hm⁻¹.mulVec b := by
    intro y b hyb
    rw [← hyb, ← hHv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hp1.ne', one_smul]
  constructor
  · intro l
    have h := hdir (1, 0)
    simp only [one_smul, sub_zero] at h
    have hy := hsolve _ _ (eq_neg_of_add_eq_zero_left h)
    rw [hy, Matrix.mulVec_neg, smul_neg, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      neg_pos]
    refine mul_neg_of_pos_of_neg (inv_pos.2 hp1) ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_neg (fun k _ => mul_neg_of_neg_of_pos (hneg l k) (hgrad k))
      ⟨l, Finset.mem_univ l⟩
  · intro l j
    have h := hdir (0, Pi.single j 1)
    simp only [zero_smul, add_zero, sub_eq_zero] at h
    have hy := hsolve _ _ h
    rw [hy, Pi.smul_apply, smul_eq_mul]
    refine mul_neg_of_pos_of_neg (inv_pos.2 hp1) ?_
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hneg l j

/-- Instance of the hypotheses of `cmp_inv_neg`: `H = [[-2, 1], [1, -2]]` is negative definite with
positive off-diagonal entries; `H⁻¹ = -(1/3)[[2, 1], [1, 2]]`. -/
theorem cmp_inv_neg_instance :
    (∀ v : Fin 2 → ℝ, v ≠ 0 → v ⬝ᵥ (!![-2, 1; 1, -2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec v < 0) ∧
      ∀ i j : Fin 2, i ≠ j → 0 < (!![-2, 1; 1, -2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  refine ⟨fun v hv => ?_, fun i j hij => ?_⟩
  · have hq : v ⬝ᵥ (!![-2, 1; 1, -2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec v =
        -(v 0 ^ 2 + v 1 ^ 2) - (v 0 - v 1) ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      by_contra h
      push Not at h
      apply hv
      funext k; fin_cases k <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    rw [hq]; nlinarith [sq_nonneg (v 0 - v 1)]
  · fin_cases i <;> fin_cases j <;> simp_all

end MWG.PositiveEquilibriumTheory
