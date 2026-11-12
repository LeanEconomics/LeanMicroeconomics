/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Aggregation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exercises 2.E.5, 2.E.6 and 2.E.8

MWG, Exercises 2.E.5, 2.E.6 and 2.E.8 (p. 37).

* Exercise 2.E.5: homogeneity of degree one in wealth, Walras' law, homogeneity of degree
  zero and zero cross-price effects force `x_ℓ(p, w) = α_ℓ w / p_ℓ`. The constants satisfy
  `α_ℓ ≥ 0` and `∑ α_ℓ = 1`; the printed `α_ℓ > 0` does not follow (counterexample
  `x(p, w) = (w/p₁, 0)`). Differentiability of demand on the domain is assumed, since
  "cross-price effects" are derivatives.
* Exercise 2.E.6: the demand of Exercise 2.E.1 with `β = 1` is differentiable on the domain,
  so Propositions 2.E.1–2.E.3 apply to it.
* Exercise 2.E.8: elasticities are logarithmic derivatives, and the coefficients of a
  log-linear demand equation are the elasticities.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- Under zero cross-price effects, `x_ℓ(p, w)` depends on `p` only through `p_ℓ`. -/
theorem demand_eq_of_own_price_eq {L : ℕ} {x : DemandFunction L}
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hcross : ∀ p w, PWDomain p w → ∀ l k, k ≠ l →
      priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l k = 0)
    {p p' : Fin L → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') {w : ℝ}
    (hw : 0 < w) (l : Fin L) (hl : p l = p' l) : x p w l = x p' w l := by
  set v := p' - p with hv
  let f : ℝ → ℝ := fun t => x (p + t • v) (w + t * 0) l
  have hdom : ∀ t ∈ Set.Icc (0 : ℝ) 1, PWDomain (p + t • v) (w + t * 0) := by
    intro t ht
    refine ⟨fun k => ?_, by simpa using hw⟩
    have h1 := hp k
    have h2 := hp' k
    simp only [hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      linarith
    · nlinarith [mul_nonneg ht.1 h2.le, mul_pos (sub_pos.mpr h) h1]
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f 0 t := by
    intro t ht
    have hD := (hdiff _ _ (hdom t ht)).hasFDerivAt
    have h := hasDerivAt_pi.mp (hasDerivAt_line (x := x) (p := p) (v := v) (w := w) (c := 0)
      (t₀ := t) hD) l
    convert h using 1
    rw [deriv_apply_eq]
    simp only [mul_zero, add_zero]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = l
    · subst hk
      simp [hv, hl]
    · have hdom' : PWDomain (p + t • v) w := by simpa using hdom t ht
      rw [hcross _ _ hdom' l k hk, zero_mul]
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hder t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1
    (Set.right_mem_Icc.mpr zero_le_one)
  simpa [f, hv] using hconst.symm

/-- **Exercise 2.E.5** (MWG, p. 37), corrected. If `x` is homogeneous of degree one in `w`,
satisfies Walras' law and homogeneity of degree zero, takes values in `ℝ^L_+`, is
differentiable on the domain and has zero cross-price effects, then there are constants
`α_ℓ ≥ 0` with `∑ α_ℓ = 1` and `x_ℓ(p, w) = α_ℓ w / p_ℓ`. -/
theorem exercise_2_E_5 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (h1 : HomogeneousOneInWealth x)
    (hX : ∀ p w, PWDomain p w → ∀ l, 0 ≤ x p w l)
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hcross : ∀ p w, PWDomain p w → ∀ l k, k ≠ l →
      priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l k = 0) :
    ∃ α : Fin L → ℝ, (∀ l, 0 ≤ α l) ∧ ∑ l, α l = 1 ∧
      ∀ p w, PWDomain p w → ∀ l, x p w l = α l * w / p l := by
  have hone : StrictlyPositive (fun _ : Fin L => (1 : ℝ)) := fun _ => one_pos
  refine ⟨x (fun _ => 1) 1, fun l => hX _ _ ⟨hone, one_pos⟩ l, ?_, ?_⟩
  · have := hW _ _ ⟨hone, one_pos⟩
    simpa [dotProduct] using this
  · intro p w hd l
    have hpl := hd.1 l
    set a := (p l)⁻¹ with ha
    have ha0 : 0 < a := inv_pos.mpr hpl
    have hq : StrictlyPositive (a • p) := (pwDomain_smul hd ha0).1
    have e1 : x p w = w • x p 1 := by
      have := h1 p 1 w ⟨hd.1, one_pos⟩ hd.2
      rwa [mul_one] at this
    have e2 : x p 1 = x (a • p) a := by
      have := hH p 1 a ⟨hd.1, one_pos⟩ ha0
      rw [mul_one] at this
      exact this.symm
    have e3 : x (a • p) a = a • x (a • p) 1 := by
      have := h1 (a • p) 1 a ⟨hq, one_pos⟩ ha0
      rwa [mul_one] at this
    have e4 : x (a • p) 1 l = x (fun _ => 1) 1 l :=
      demand_eq_of_own_price_eq hdiff hcross hq hone one_pos l (by simp [ha, hpl.ne'])
    rw [e1, e2, e3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e4, ha]
    field_simp

/-- **Exercise 2.E.5** (MWG, p. 37): the counterexample demand `x(p, w) = (w/p₁, 0)`. -/
noncomputable def demand_2_E_5_counterexample : DemandFunction 2 := fun p w => ![w / p 0, 0]

/-- The counterexample demand is differentiable on the domain. -/
theorem demand_2_E_5_counterexample_differentiableAt {p : Fin 2 → ℝ} {w : ℝ}
    (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w) := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · have h0 := (hd.1 0).ne'
    simp only [Fin.zero_eta, demand_2_E_5_counterexample, Function.uncurry_def,
      Matrix.cons_val_zero, div_eq_mul_inv]
    fun_prop (disch := assumption)
  · simp only [Fin.mk_one, demand_2_E_5_counterexample, Function.uncurry_def,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    exact differentiableAt_const _

/-- **Exercise 2.E.5** (MWG, p. 37). The printed conclusion `α_ℓ > 0` is false: the demand
`x(p, w) = (w/p₁, 0)` satisfies every hypothesis of the exercise, but no representation
`x_ℓ = α_ℓ w/p_ℓ` has all `α_ℓ > 0`. -/
theorem exercise_2_E_5_alpha_pos_counterexample :
    HomogeneousZero demand_2_E_5_counterexample ∧ WalrasLaw demand_2_E_5_counterexample ∧
      HomogeneousOneInWealth demand_2_E_5_counterexample ∧
      (∀ p w, PWDomain p w → ∀ l, 0 ≤ demand_2_E_5_counterexample p w l) ∧
      (∀ p w, PWDomain p w →
        DifferentiableAt ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w)) ∧
      (∀ p w, PWDomain p w → ∀ l k, k ≠ l →
        priceEffect (fderiv ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w)) l k = 0) ∧
      ¬ ∃ α : Fin 2 → ℝ, (∀ l, 0 < α l) ∧ ∀ p w, PWDomain p w → ∀ l,
        demand_2_E_5_counterexample p w l = α l * w / p l := by
  refine ⟨?_, ?_, ?_, ?_, fun p w hd => demand_2_E_5_counterexample_differentiableAt hd, ?_, ?_⟩
  · intro p w a hd ha
    funext l
    fin_cases l
    · simp only [demand_2_E_5_counterexample, Fin.zero_eta, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      field_simp [ha.ne', (hd.1 0).ne']
    · simp [demand_2_E_5_counterexample]
  · intro p w hd
    simp only [demand_2_E_5_counterexample, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, add_zero]
    field_simp [(hd.1 0).ne']
  · intro p w a hd ha
    funext l
    fin_cases l
    · simp only [demand_2_E_5_counterexample, Fin.zero_eta, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      ring
    · simp [demand_2_E_5_counterexample]
  · intro p w hd l
    fin_cases l
    · simpa [demand_2_E_5_counterexample] using div_nonneg hd.2.le (hd.1 0).le
    · simp [demand_2_E_5_counterexample]
  · intro p w hd l k hkl
    have hD := (demand_2_E_5_counterexample_differentiableAt hd).hasFDerivAt
    have h := hasDerivAt_path_apply hD (Pi.single k 1) 0 l
    apply hasDerivAt_eq_zero_of_eventually_const h (demand_2_E_5_counterexample p w l)
    refine Filter.Eventually.of_forall fun t => ?_
    fin_cases l <;> fin_cases k
    · exact absurd rfl hkl
    · simp [demand_2_E_5_counterexample]
    · simp [demand_2_E_5_counterexample]
    · exact absurd rfl hkl
  · rintro ⟨α, hα, hrep⟩
    have hd : PWDomain (fun _ : Fin 2 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
    have := hrep _ _ hd 1
    simp [demand_2_E_5_counterexample] at this
    linarith [hα 1]

/-- The Exercise 2.E.1 demand (any `β`) is differentiable at every domain point. -/
theorem demand_2_E_1_differentiableAt (β : ℝ) {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry (demand_2_E_1 β)) (p, w) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_E_1, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.E.6** (MWG, p. 37). For the demand of Exercise 2.E.1 with `β = 1`, the
conclusions of Propositions 2.E.1, 2.E.2 and 2.E.3 hold at every `(p, w)`. -/
theorem exercise_2_E_6 {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    (∀ l, ∑ k, priceEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l k * p k +
        wealthEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l * w = 0) ∧
      (∀ k, ∑ l, p l * priceEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l k +
        demand_2_E_1 1 p w k = 0) ∧
      ∑ l, p l * wealthEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l = 1 := by
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have hW := (exercise_2_E_1_walras_iff 1).mpr rfl
  exact ⟨proposition_2_E_1 (exercise_2_E_1_homogeneous 1) hd hD,
    proposition_2_E_2 hW hd hD, proposition_2_E_3 hW hd hD⟩

/-! ### Exercise 2.E.8 -/

/-- The curve `s ↦ (p + (e^s - p_k) e_k, w)` passes through `(p, w)` at `s = ln p_k` with
velocity `(p_k e_k, 0)`. -/
theorem hasDerivAt_exp_price_curve {L : ℕ} {p : Fin L → ℝ} (w : ℝ) (k : Fin L)
    (hk : 0 < p k) :
    HasDerivAt (fun s : ℝ => ((p + (Real.exp s - p k) • Pi.single k 1, w) :
      (Fin L → ℝ) × ℝ)) (p k • ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ)) (Real.log (p k)) := by
  have he : HasDerivAt (fun s : ℝ => Real.exp s - p k) (p k) (Real.log (p k)) := by
    have := (Real.hasDerivAt_exp (Real.log (p k))).sub_const (p k)
    rwa [Real.exp_log hk] at this
  have := (he.smul_const ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ)).const_add
    ((p, w) : (Fin L → ℝ) × ℝ)
  convert this using 1
  funext s
  simp

/-- **Exercise 2.E.8** (MWG, p. 37). The price elasticity is a logarithmic derivative:
`ε_ℓk(p, w) = d ln x_ℓ / d ln p_k`, i.e. the derivative of
`s ↦ ln x_ℓ(p with p_k = e^s, w)` at `s = ln p_k` (for `x_ℓ(p, w) > 0`). -/
theorem exercise_2_E_8_price {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l k : Fin L) (hx : 0 < x p w l) :
    HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p k) • Pi.single k 1) w l))
      (priceElasticity D p (x p w) l k) (Real.log (p k)) := by
  have hk := hd.1 k
  have hy : ((p, w) : (Fin L → ℝ) × ℝ) =
      (p + (Real.exp (Real.log (p k)) - p k) • Pi.single k 1, w) := by
    simp [Real.exp_log hk]
  have hc := hD.comp_hasDerivAt_of_eq (Real.log (p k)) (hasDerivAt_exp_price_curve w k hk) hy
  have hl := (hasDerivAt_pi.mp hc l).log (by simpa [Real.exp_log hk] using hx.ne')
  have hval : (Function.uncurry x ∘ fun s => (p + (Real.exp s - p k) • Pi.single k 1, w))
      (Real.log (p k)) = x p w := by simp [Real.exp_log hk]
  rw [hval, map_smul] at hl
  convert hl using 1
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, priceElasticity, priceEffect]
    field_simp

/-- **Exercise 2.E.8** (MWG, p. 37). The wealth elasticity is `d ln x_ℓ / d ln w`. -/
theorem exercise_2_E_8_wealth {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) (hx : 0 < x p w l) :
    HasDerivAt (fun s => Real.log (x p (Real.exp s) l)) (wealthElasticity D w (x p w) l)
      (Real.log w) := by
  have hw := hd.2
  have hγ : HasDerivAt (fun s : ℝ => ((p, Real.exp s) : (Fin L → ℝ) × ℝ))
      (w • ((0, 1) : (Fin L → ℝ) × ℝ)) (Real.log w) := by
    have he := Real.hasDerivAt_exp (Real.log w)
    rw [Real.exp_log hw] at he
    have := (he.smul_const ((0, 1) : (Fin L → ℝ) × ℝ)).const_add ((p, 0) : (Fin L → ℝ) × ℝ)
    convert this using 1
    funext s
    simp
  have hy : ((p, w) : (Fin L → ℝ) × ℝ) = (p, Real.exp (Real.log w)) := by
    simp [Real.exp_log hw]
  have hc := hD.comp_hasDerivAt_of_eq (Real.log w) hγ hy
  have hl := (hasDerivAt_pi.mp hc l).log (by simpa [Real.exp_log hw] using hx.ne')
  have hval : (Function.uncurry x ∘ fun s => ((p, Real.exp s) : (Fin L → ℝ) × ℝ))
      (Real.log w) = x p w := by simp [Real.exp_log hw]
  rw [hval, map_smul] at hl
  convert hl using 1
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, wealthElasticity, wealthEffect]
    field_simp

/-- **Exercise 2.E.8** (MWG, p. 37). If, for `L = 2`,
`ln x_ℓ(p, w) = α₀ + α₁ ln p₁ + α₂ ln p₂ + γ ln w` on the whole domain, then the parameters
are the elasticities: `ε_ℓ1 = α₁`, `ε_ℓ2 = α₂` and `ε_ℓw = γ` (goods indexed `0, 1`). -/
theorem exercise_2_E_8_loglinear {x : DemandFunction 2} {l : Fin 2} {a0 a1 a2 γ : ℝ}
    (hpos : ∀ p w, PWDomain p w → 0 < x p w l)
    (hlog : ∀ p w, PWDomain p w → Real.log (x p w l) =
      a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1) + γ * Real.log w)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    priceElasticity D p (x p w) l 0 = a1 ∧ priceElasticity D p (x p w) l 1 = a2 ∧
      wealthElasticity D w (x p w) l = γ := by
  have hx := hpos p w hd
  have hupd : ∀ (k : Fin 2) (s : ℝ),
      PWDomain (p + (Real.exp s - p k) • Pi.single k 1) w := by
    intro k s
    refine ⟨fun j => ?_, hd.2⟩
    by_cases hj : j = k
    · subst hj
      simpa using Real.exp_pos s
    · simpa [Pi.single_apply, hj] using hd.1 j
  refine ⟨?_, ?_, ?_⟩
  · have h := exercise_2_E_8_price hd hD l 0 hx
    have hlin : HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p 0) • Pi.single 0 1) w l))
        a1 (Real.log (p 0)) := by
      have : (fun s => Real.log (x (p + (Real.exp s - p 0) • Pi.single 0 1) w l)) =
          fun s => a0 + a1 * s + a2 * Real.log (p 1) + γ * Real.log w := by
        funext s
        rw [hlog _ _ (hupd 0 s)]
        simp [Real.log_exp]
      rw [this]
      have := (((hasDerivAt_id (Real.log (p 0))).const_mul a1).const_add a0).add_const
        (a2 * Real.log (p 1) + γ * Real.log w)
      convert this using 1
      · funext s
        simp only [id]
        ring
      · simp
    exact h.unique hlin
  · have h := exercise_2_E_8_price hd hD l 1 hx
    have hlin : HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p 1) • Pi.single 1 1) w l))
        a2 (Real.log (p 1)) := by
      have : (fun s => Real.log (x (p + (Real.exp s - p 1) • Pi.single 1 1) w l)) =
          fun s => a0 + a1 * Real.log (p 0) + a2 * s + γ * Real.log w := by
        funext s
        rw [hlog _ _ (hupd 1 s)]
        simp [Real.log_exp]
      rw [this]
      simpa using ((((hasDerivAt_id _).const_mul a2).const_add
        (a0 + a1 * Real.log (p 0))).add_const (γ * Real.log w))
    exact h.unique hlin
  · have h := exercise_2_E_8_wealth hd hD l hx
    have hlin : HasDerivAt (fun s => Real.log (x p (Real.exp s) l)) γ (Real.log w) := by
      have : (fun s => Real.log (x p (Real.exp s) l)) =
          fun s => a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1) + γ * s := by
        funext s
        rw [hlog _ _ ⟨hd.1, Real.exp_pos s⟩, Real.log_exp]
      rw [this]
      simpa using ((hasDerivAt_id _).const_mul γ).const_add
        (a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1))
    exact h.unique hlin

end MWG.ConsumerChoice
