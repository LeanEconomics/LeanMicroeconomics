/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.DemandCalculus

/-!
# Implications of homogeneity and Walras' law for price and wealth effects

MWG, Section 2.E, pp. 27–28: Propositions 2.E.1–2.E.3 (equations (2.E.1)–(2.E.7)), the
elasticity forms, and Exercise 2.E.2 (p. 28). Demand is differentiable at the point in
question, in the Fréchet sense (`HasFDerivAt` of `(p, w) ↦ x(p, w)`), at an interior point
`p ≫ 0`, `w > 0`. Elasticities are taken where `x_ℓ(p, w) ≠ 0`, where they are defined.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.E** (MWG, p. 27). The price elasticity `ε_ℓk = (∂x_ℓ/∂p_k)(p_k/x_ℓ)`. -/
noncomputable def priceElasticity {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (p xv : Fin L → ℝ) (l k : Fin L) : ℝ :=
  priceEffect D l k * (p k / xv l)

/-- **Section 2.E** (MWG, p. 27). The wealth elasticity `ε_ℓw = (∂x_ℓ/∂w)(w/x_ℓ)`. -/
noncomputable def wealthElasticity {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (w : ℝ) (xv : Fin L → ℝ) (l : Fin L) : ℝ :=
  wealthEffect D l * (w / xv l)

/-- **Exercise 2.E.2** (MWG, p. 28). The budget share `b_ℓ = p_ℓ x_ℓ / w`. -/
noncomputable def budgetShare {L : ℕ} (p xv : Fin L → ℝ) (w : ℝ) (l : Fin L) : ℝ :=
  p l * xv l / w

/-- **Proposition 2.E.1** (MWG, p. 27), equation (2.E.1). If `x` is homogeneous of degree zero
and differentiable at `(p, w)`, then `∑_k (∂x_ℓ/∂p_k) p_k + (∂x_ℓ/∂w) w = 0` for every `ℓ`. -/
theorem proposition_2_E_1 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) :
    ∑ k, priceEffect D l k * p k + wealthEffect D l * w = 0 := by
  rw [← deriv_apply_eq, homogeneous_deriv_identity hH hd hD]
  rfl

/-- **Proposition 2.E.1** (MWG, p. 27), matrix form (2.E.2): `D_p x(p, w) p + D_w x(p, w) w = 0`.
-/
theorem proposition_2_E_1_matrix {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.mulVec (priceJacobian D) p + w • wealthJacobian D = 0 := by
  rw [← deriv_apply_eq_mulVec, homogeneous_deriv_identity hH hd hD]

/-- **Proposition 2.E.1** (MWG, p. 27), elasticity form (2.E.3):
`∑_k ε_ℓk(p, w) + ε_ℓw(p, w) = 0` (elasticities are meaningful where `x_ℓ(p, w) ≠ 0`; where
`x_ℓ(p, w) = 0` Lean's convention `a/0 = 0` makes both sides zero, so no hypothesis is needed).
-/
theorem proposition_2_E_1_elasticity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) :
    ∑ k, priceElasticity D p (x p w) l k + wealthElasticity D w (x p w) l = 0 := by
  have h := proposition_2_E_1 hH hd hD l
  simp only [priceElasticity, wealthElasticity, mul_div_assoc']
  rw [← Finset.sum_div, ← add_div, h, zero_div]

/-- **Proposition 2.E.2** (MWG, p. 28), equation (2.E.4) (Cournot aggregation). If `x`
satisfies Walras' law and is differentiable at `(p, w)`, then
`∑_ℓ p_ℓ (∂x_ℓ/∂p_k) + x_k(p, w) = 0` for every `k`. -/
theorem proposition_2_E_2 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (k : Fin L) :
    ∑ l, p l * priceEffect D l k + x p w k = 0 := by
  have h := walras_deriv_identity hW hd hD (Pi.single k 1) 0
  rw [single_dotProduct, one_mul] at h
  simpa [dotProduct, priceEffect, add_comm] using h

/-- **Proposition 2.E.2** (MWG, p. 28), matrix form (2.E.5): `p·D_p x(p, w) + x(p, w)ᵀ = 0ᵀ`.
-/
theorem proposition_2_E_2_matrix {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (priceJacobian D) + x p w = 0 := by
  funext k
  simpa [Matrix.vecMul, dotProduct, priceJacobian] using proposition_2_E_2 hW hd hD k

/-- **Proposition 2.E.3** (MWG, p. 28), equation (2.E.6) (Engel aggregation). If `x` satisfies
Walras' law and is differentiable at `(p, w)`, then `∑_ℓ p_ℓ (∂x_ℓ/∂w) = 1`. -/
theorem proposition_2_E_3 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    ∑ l, p l * wealthEffect D l = 1 := by
  have h := walras_deriv_identity hW hd hD 0 1
  simpa [dotProduct, wealthEffect] using h

/-- **Proposition 2.E.3** (MWG, p. 28), matrix form (2.E.7): `p·D_w x(p, w) = 1`. -/
theorem proposition_2_E_3_matrix {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : p ⬝ᵥ wealthJacobian D = 1 :=
  proposition_2_E_3 hW hd hD

/-- **Exercise 2.E.2** (MWG, p. 28), first formula. With Walras' law and every
`x_ℓ(p, w) ≠ 0`: `∑_ℓ b_ℓ ε_ℓk + b_k = 0`. -/
theorem exercise_2_E_2_price {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (hx : ∀ l, x p w l ≠ 0) (k : Fin L) :
    ∑ l, budgetShare p (x p w) w l * priceElasticity D p (x p w) l k +
      budgetShare p (x p w) w k = 0 := by
  have h := proposition_2_E_2 hW hd hD k
  have hw := hd.2.ne'
  have hterm : ∀ l, budgetShare p (x p w) w l * priceElasticity D p (x p w) l k =
      p k / w * (p l * priceEffect D l k) := by
    intro l
    simp only [budgetShare, priceElasticity]
    field_simp [hx l]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum]
  simp only [budgetShare]
  calc p k / w * ∑ l, p l * priceEffect D l k + p k * x p w k / w
      = p k / w * (∑ l, p l * priceEffect D l k + x p w k) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- **Exercise 2.E.2** (MWG, p. 28), second formula. With Walras' law and every
`x_ℓ(p, w) ≠ 0`: `∑_ℓ b_ℓ ε_ℓw = 1`. -/
theorem exercise_2_E_2_wealth {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (hx : ∀ l, x p w l ≠ 0) :
    ∑ l, budgetShare p (x p w) w l * wealthElasticity D w (x p w) l = 1 := by
  have h := proposition_2_E_3 hW hd hD
  have hw := hd.2.ne'
  have hterm : ∀ l, budgetShare p (x p w) w l * wealthElasticity D w (x p w) l =
      p l * wealthEffect D l := by
    intro l
    simp only [budgetShare, wealthElasticity]
    field_simp [hx l]
  simp only [hterm, h]

/-- **Exercise 2.E.3** (MWG, p. 36). With Walras' law, `p·D_p x(p, w) p = -w`: a proportional
rise in all prices at constant wealth lowers real expenditure capacity one-for-one. (Only
Walras' law, through Proposition 2.E.2, is used.) -/
theorem exercise_2_E_3 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    p ⬝ᵥ Matrix.mulVec (priceJacobian D) p = -w := by
  rw [Matrix.dotProduct_mulVec]
  have h := proposition_2_E_2_matrix hW hd hD
  rw [eq_neg_of_add_eq_zero_left h, neg_dotProduct, dotProduct_comm, hW p w hd]

/-- **Exercise 2.E.3** (MWG, p. 36), by the route the hint suggests: Proposition 2.E.1 gives
`D_p x p = -w D_w x`, and Proposition 2.E.3 gives `p·D_w x = 1`. -/
theorem exercise_2_E_3_via_homogeneity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    p ⬝ᵥ Matrix.mulVec (priceJacobian D) p = -w := by
  have h := proposition_2_E_1_matrix hH hd hD
  rw [eq_neg_of_add_eq_zero_left h, dotProduct_neg, dotProduct_smul,
    proposition_2_E_3_matrix hW hd hD, smul_eq_mul, mul_one]

/-! ### Exercise 2.E.4 -/

/-- **Exercise 2.E.4** (MWG, p. 36). Demand is homogeneous of degree one in wealth:
`x(p, αw) = αx(p, w)` for `α > 0`. -/
def HomogeneousOneInWealth {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x p (α * w) = α • x p w

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth,
`D_w x(p, w) = (1/w) x(p, w)`. -/
theorem exercise_2_E_4_wealthJacobian {L : ℕ} {x : DemandFunction L}
    (h1 : HomogeneousOneInWealth x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    wealthJacobian D = w⁻¹ • x p w := by
  have hpath := hasDerivAt_path hD 0 1
  have hw := hd.2
  have hlin : HasDerivAt (fun t : ℝ => (1 + t * w⁻¹) • x p w) (w⁻¹ • x p w) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const w⁻¹).const_add 1).smul_const (x p w)
  have hev : (fun t : ℝ => x (p + t • 0) (w + t * 1)) =ᶠ[nhds 0]
      (fun t : ℝ => (1 + t * w⁻¹) • x p w) := by
    have hpos : ∀ᶠ t in nhds (0 : ℝ), 0 < 1 + t * w⁻¹ := by
      have hc : Continuous (fun t : ℝ => 1 + t * w⁻¹) := by fun_prop
      have := hc.tendsto (0 : ℝ)
      simp only [zero_mul, add_zero] at this
      exact this.eventually_const_lt one_pos
    filter_upwards [hpos] with t ht
    simp only [smul_zero, add_zero, mul_one]
    rw [← h1 p w _ hd ht]
    congr 1
    field_simp
  have := hpath.unique (hlin.congr_of_eventuallyEq hev)
  funext l
  have := congrFun this l
  simpa [wealthJacobian, wealthEffect] using this

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth,
`ε_ℓw(p, w) = 1` for every good with `x_ℓ(p, w) ≠ 0`. -/
theorem exercise_2_E_4 {L : ℕ} {x : DemandFunction L} (h1 : HomogeneousOneInWealth x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) (hx : x p w l ≠ 0) :
    wealthElasticity D w (x p w) l = 1 := by
  have h := congrFun (exercise_2_E_4_wealthJacobian h1 hd hD) l
  simp only [wealthJacobian, Pi.smul_apply, smul_eq_mul] at h
  simp only [wealthElasticity, h]
  field_simp [hd.2.ne', hx]

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth the Engel
function is linear, `x(p, w) = w x(p, 1)`, so the wealth expansion path is the open ray
through `x(p, 1)`. -/
theorem exercise_2_E_4_engel {L : ℕ} {x : DemandFunction L} (h1 : HomogeneousOneInWealth x)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    (∀ w, 0 < w → engelFunction x p w = w • x p 1) ∧
      wealthExpansionPath x p = {y | ∃ t : ℝ, 0 < t ∧ y = t • x p 1} := by
  have he : ∀ w, 0 < w → engelFunction x p w = w • x p 1 := by
    intro w hw
    have := h1 p 1 w ⟨hp, one_pos⟩ hw
    rwa [mul_one] at this
  refine ⟨he, ?_⟩
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, he w hw⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (he t ht).symm⟩

end MWG.ConsumerChoice
