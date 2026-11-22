/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Slutsky
import MWGConsumerChoice.AggregationExercises

/-!
# Slutsky matrices of explicit demand functions

MWG, Exercises 2.F.10, 2.F.15, 2.F.16 and 2.F.17 (pp. 38–39).

The Slutsky matrix is computed from its characterisation `S v = D(v, v·x)` as the derivative
of demand along the compensated path `t ↦ (p + t v, w + t v·x(p, w))`
(`slutsky_mulVec_of_hasDerivAt`), which only needs one-variable derivatives.

* Exercise 2.F.10: the demand of Exercise 2.E.1 with `β = 1`; at `p = (1,1,1)`, `w = 1`, the
  Slutsky matrix is `(1/3)[[-1,1,0],[0,-1,1],[1,0,-1]]`, negative semidefinite but not
  symmetric; at `p = (1, 1, ε)` with `0 < ε < 1/22` it is not negative semidefinite, so the
  demand violates the weak axiom (Proposition 2.F.2).
* Exercise 2.F.15 (consumption set `ℝ³`): the demand is determined by the stated data; it
  satisfies the weak axiom (proved directly), `v·S v < 0` for `v` not proportional to `p`, and
  `S` is not symmetric.
* Exercise 2.F.16 (consumption set `ℝ³`): homogeneous, Walras' law, violates the weak axiom,
  and `v·S v = 0` for all `v`.
* Exercise 2.F.17: `x_k = w / ∑ p_ℓ` is homogeneous, satisfies Walras' law and the weak axiom,
  and its Slutsky matrix is zero: negative semidefinite, symmetric, not negative definite.
-/

namespace MWG.ConsumerChoice

/-- The Slutsky matrix applied to `v` is the derivative of demand along the compensated path;
it can be read off from one-variable derivatives of the components. -/
theorem slutsky_mulVec_of_hasDerivAt {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v d : Fin L → ℝ)
    (h : ∀ l, HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * (v ⬝ᵥ x p w)) l) (d l) 0) :
    Matrix.mulVec (slutskyMatrix D (x p w)) v = d := by
  rw [slutskyMatrix_mulVec]
  funext l
  exact (hasDerivAt_path_apply hD v _ l).unique (h l)

/-- An affine function of `t` has derivative its slope. -/
theorem hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-! ### Exercise 2.F.10 -/

/-- Derivative of a typical component `(a + t a')/(P + t P') · (w + t c)/(b + t b')` of the
Exercise 2.E.1 demand along a line. -/
theorem hasDerivAt_share_term (a a' P P' w c b b' : ℝ) (hP : P ≠ 0) (hb : b ≠ 0) :
    HasDerivAt (fun t : ℝ => (a + t * a') / (P + t * P') * ((w + t * c) / (b + t * b')))
      ((a' * P - a * P') / P ^ 2 * (w / b) + a / P * ((c * b - w * b') / b ^ 2)) 0 := by
  have h1 := (hasDerivAt_affine a a').div (hasDerivAt_affine P P') (by simpa using hP)
  have h2 := (hasDerivAt_affine w c).div (hasDerivAt_affine b b') (by simpa using hb)
  convert h1.mul h2 using 1
  simp only [Pi.div_apply, zero_mul, add_zero]

/-- **Exercise 2.F.10** (MWG, p. 38). The compensated derivative `S v` of the Exercise 2.E.1
demand (`β = 1`) at any `(p, w)`, with `P = p₁ + p₂ + p₃`, `V = v₁ + v₂ + v₃`, `c = v·x`. -/
theorem slutsky_2_E_1_mulVec {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w))
      (demand_2_E_1 1 p w)) v =
    let P := p 0 + p 1 + p 2
    let V := v 0 + v 1 + v 2
    let c := v ⬝ᵥ demand_2_E_1 1 p w
    ![(v 1 * P - p 1 * V) / P ^ 2 * (w / p 0) + p 1 / P * ((c * p 0 - w * v 0) / p 0 ^ 2),
      (v 2 * P - p 2 * V) / P ^ 2 * (w / p 1) + p 2 / P * ((c * p 1 - w * v 1) / p 1 ^ 2),
      (v 0 * P - p 0 * V) / P ^ 2 * (w / p 2) + p 0 / P * ((c * p 2 - w * v 2) / p 2 ^ 2)] := by
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  apply slutsky_mulVec_of_hasDerivAt hD
  intro l
  fin_cases l
  · convert hasDerivAt_share_term (p 1) (v 1) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 0) (v 0) hP h0 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
        Matrix.cons_val_zero]
      ring
    · rfl
  · convert hasDerivAt_share_term (p 2) (v 2) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 1) (v 1) hP h1 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · rfl
  · convert hasDerivAt_share_term (p 0) (v 0) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 2) (v 2) hP h2 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
    · rfl

/-- **Exercise 2.F.10(a)** (MWG, p. 38). At `p = (1,1,1)`, `w = 1`, the Slutsky matrix of the
Exercise 2.E.1 demand with `β = 1` is `(1/3)[[-1,1,0],[0,-1,1],[1,0,-1]]`. -/
theorem exercise_2_F_10a_matrix :
    slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1) =
    !![-1 / 3, 1 / 3, 0; 0, -1 / 3, 1 / 3; 1 / 3, 0, -1 / 3] := by
  have hd : PWDomain (fun _ : Fin 3 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
  ext l k
  have h := congrFun (slutsky_2_E_1_mulVec hd (Pi.single k 1)) l
  rw [Matrix.mulVec_single_one] at h
  simp only [Matrix.col_apply] at h
  rw [h]
  fin_cases l <;> fin_cases k <;>
    simp [demand_2_E_1, dotProduct, Pi.single_apply] <;> norm_num

/-- **Exercise 2.F.10(a)** (MWG, p. 38). At `p = (1,1,1)`, `w = 1`, the Slutsky matrix is
negative semidefinite but not symmetric. -/
theorem exercise_2_F_10a :
    NegSemidef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1)) ∧
    ¬ (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1)).IsSymm := by
  rw [exercise_2_F_10a_matrix]
  constructor
  · intro z
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    nlinarith [sq_nonneg (z 0 - z 1), sq_nonneg (z 1 - z 2), sq_nonneg (z 2 - z 0)]
  · intro h
    have := congrFun (congrFun h.eq 0) 1
    simp at this

/-- **Exercise 2.F.10(b)** (MWG, p. 38). At `p = (1, 1, ε)`, `w = 1`, with `0 < ε < 1/22`,
the direction `v = (1, 0, 3ε/2)` gives `v·S v = (1 - 22ε)/(4(2+ε)²) > 0`: the Slutsky matrix is
not negative semidefinite. -/
theorem exercise_2_F_10b_quadratic {ε : ℝ} (hε : 0 < ε) :
    let S := slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (![1, 1, ε], 1))
      (demand_2_E_1 1 ![1, 1, ε] 1)
    ![1, 0, 3 * ε / 2] ⬝ᵥ Matrix.mulVec S ![1, 0, 3 * ε / 2] = (1 - 22 * ε) / (4 * (2 + ε) ^ 2)
    := by
  have hd : PWDomain (![1, 1, ε] : Fin 3 → ℝ) 1 := by
    refine ⟨fun l => ?_, one_pos⟩
    fin_cases l <;> simp [hε]
  intro S
  rw [slutsky_2_E_1_mulVec hd]
  have h2 : (2 + ε) ≠ 0 := by positivity
  simp [demand_2_E_1, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- **Exercise 2.F.10(b)** (MWG, p. 38). The demand of Exercise 2.E.1 with `β = 1` violates the
weak axiom: otherwise Proposition 2.F.2 would make `S(p, w)` negative semidefinite at
`p = (1, 1, 1/44)`, `w = 1`. -/
theorem exercise_2_F_10b : ¬ WeakAxiom (demand_2_E_1 1) := by
  intro hWA
  set ε : ℝ := 1 / 44
  have hε : 0 < ε := by norm_num
  have hd : PWDomain (![1, 1, ε] : Fin 3 → ℝ) 1 := by
    refine ⟨fun l => ?_, one_pos⟩
    fin_cases l <;> simp [hε]
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have hW := (exercise_2_E_1_walras_iff 1).mpr rfl
  have hns := proposition_2_F_2 hW hWA hd hD ![1, 0, 3 * ε / 2]
  have hq := exercise_2_F_10b_quadratic hε
  simp only at hq
  rw [hq] at hns
  have : 0 < (1 - 22 * ε) / (4 * (2 + ε) ^ 2) := by
    apply div_pos <;> norm_num [ε]
  linarith

/-! ### Exercise 2.F.16 -/

/-- **Exercise 2.F.16** (MWG, p. 39). The demand `x₁ = p₂/p₃`, `x₂ = -p₁/p₃`, `x₃ = w/p₃` on
the consumption set `ℝ³` (goods indexed `0, 1, 2`). -/
noncomputable def demand_2_F_16 : DemandFunction 3 := fun p w => ![p 1 / p 2, -(p 0 / p 2), w / p 2]

/-- **Exercise 2.F.16(a)** (MWG, p. 39). The demand is homogeneous of degree zero and satisfies
Walras' law. -/
theorem exercise_2_F_16a : HomogeneousZero demand_2_F_16 ∧ WalrasLaw demand_2_F_16 := by
  constructor
  · intro p w a hd ha
    have := (hd.1 2).ne'
    funext l
    fin_cases l <;> simp [demand_2_F_16] <;> field_simp
  · intro p w hd
    have := (hd.1 2).ne'
    simp [demand_2_F_16, dotProduct, Fin.sum_univ_three]
    field_simp
    ring

/-- **Exercise 2.F.16(b)** (MWG, p. 39). The demand violates the weak axiom: at `p = (1,1,1)`,
`w = 2` and `p' = (1,2,1)`, `w' = 1`, each bundle is affordable in the other situation. -/
theorem exercise_2_F_16b : ¬ WeakAxiom demand_2_F_16 := by
  intro h
  have hd : PWDomain (![1, 1, 1] : Fin 3 → ℝ) 2 :=
    ⟨fun l => by fin_cases l <;> simp, by norm_num⟩
  have hd' : PWDomain (![1, 2, 1] : Fin 3 → ℝ) 1 :=
    ⟨fun l => by fin_cases l <;> simp, by norm_num⟩
  have := h _ _ _ _ hd hd' (by simp [demand_2_F_16, dotProduct, Fin.sum_univ_three])
    (by
      intro he
      have := congrFun he 0
      simp [demand_2_F_16] at this)
  simp [demand_2_F_16, dotProduct, Fin.sum_univ_three] at this

/-- The Exercise 2.F.16 demand is differentiable at every domain point. -/
theorem demand_2_F_16_differentiableAt {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_F_16) (p, w) := by
  have h2 := (hd.1 2).ne'
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_F_16, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.F.16(c)** (MWG, p. 39). `v·S(p, w) v = 0` for all `v ∈ ℝ³`. -/
theorem exercise_2_F_16c {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_16) (p, w))
      (demand_2_F_16 p w)) v = 0 := by
  have hD := (demand_2_F_16_differentiableAt hd).hasFDerivAt
  have h2 := (hd.1 2).ne'
  set c := v ⬝ᵥ demand_2_F_16 p w with hc
  have hS := slutsky_mulVec_of_hasDerivAt hD v
    ![(v 1 * p 2 - p 1 * v 2) / p 2 ^ 2, -((v 0 * p 2 - p 0 * v 2) / p 2 ^ 2),
      (c * p 2 - w * v 2) / p 2 ^ 2] (by
    intro l
    fin_cases l
    · convert (hasDerivAt_affine (p 1) (v 1)).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2) using 1
      · funext t
        simp [demand_2_F_16]
      · simp
    · convert ((hasDerivAt_affine (p 0) (v 0)).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2)).neg using 1
      · funext t
        simp [demand_2_F_16]
      · simp
    · convert (hasDerivAt_affine w c).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2) using 1
      · funext t
        simp [demand_2_F_16, hc]
      · simp)
  rw [hS]
  simp only [hc, demand_2_F_16, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-! ### Exercise 2.F.15 -/

/-- **Exercise 2.F.15** (MWG, p. 39). The demand on the consumption set `ℝ³` that is
homogeneous of degree zero, satisfies Walras' law and, at `p₃ = 1`, has `x₁ = -p₁ + p₂` and
`x₂ = -p₂` (goods indexed `0, 1, 2`):
`x = ((p₂ - p₁)/p₃, -p₂/p₃, w/p₃ + (p₁² - p₁p₂ + p₂²)/p₃²)`. -/
noncomputable def demand_2_F_15 : DemandFunction 3 := fun p w =>
  ![(p 1 - p 0) / p 2, -(p 1 / p 2), w / p 2 + (p 0 ^ 2 - p 0 * p 1 + p 1 ^ 2) / p 2 ^ 2]

/-- The quadratic form `Q(a, b) = a² - ab + b²`, positive definite. -/
theorem quadForm_pos {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < a ^ 2 - a * b + b ^ 2 := by
  rcases h with h | h
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (b - a / 2), sq_abs a]
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (a - b / 2), sq_abs b]

/-- **Exercise 2.F.15** (MWG, p. 39). The demand is homogeneous of degree zero, satisfies
Walras' law, and has the stated first two components at `p₃ = 1`. -/
theorem exercise_2_F_15_basic :
    HomogeneousZero demand_2_F_15 ∧ WalrasLaw demand_2_F_15 ∧
      ∀ p w, p 2 = 1 → demand_2_F_15 p w 0 = -p 0 + p 1 ∧ demand_2_F_15 p w 1 = -p 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p w a hd ha
    have := (hd.1 2).ne'
    funext l
    fin_cases l <;> simp [demand_2_F_15] <;> field_simp
  · intro p w hd
    have := (hd.1 2).ne'
    simp [demand_2_F_15, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · intro p w h
    simp [demand_2_F_15, h]
    ring

/-- **Exercise 2.F.15** (MWG, p. 39). The data determine the demand: any demand function that
is homogeneous of degree zero, satisfies Walras' law and has `x₁ = -p₁ + p₂`, `x₂ = -p₂` at
`p₃ = 1` coincides with `demand_2_F_15` on the domain. -/
theorem exercise_2_F_15_unique {x : DemandFunction 3} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (h0 : ∀ p w, PWDomain p w → p 2 = 1 → x p w 0 = -p 0 + p 1)
    (h1 : ∀ p w, PWDomain p w → p 2 = 1 → x p w 1 = -p 1) :
    ∀ p w, PWDomain p w → x p w = demand_2_F_15 p w := by
  intro p w hd
  have hc := hd.1 2
  set a := (p 2)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hc
  have hd' := pwDomain_smul hd ha0
  have hq2 : (a • p) 2 = 1 := by simp [ha, hc.ne']
  have e := hH p w a hd ha0
  rw [← e]
  have hw := hW _ _ hd'
  simp only [dotProduct, Fin.sum_univ_three, h0 _ _ hd' hq2, h1 _ _ hd' hq2, hq2,
    one_mul] at hw
  funext l
  fin_cases l
  · change x (a • p) (a * w) 0 = demand_2_F_15 p w 0
    rw [h0 _ _ hd' hq2]
    simp only [demand_2_F_15, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, ha]
    field_simp
    ring
  · change x (a • p) (a * w) 1 = demand_2_F_15 p w 1
    rw [h1 _ _ hd' hq2]
    simp only [demand_2_F_15, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply,
      smul_eq_mul, ha]
    field_simp
  · simp only [Fin.reduceFinMk, demand_2_F_15, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have : x (a • p) (a * w) 2 = a * w - (a • p) 0 * (-(a • p) 0 + (a • p) 1) -
        (a • p) 1 * -(a • p) 1 := by linarith
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul, ha]
    field_simp
    ring

/-- **Exercise 2.F.15** (MWG, p. 39). The demand satisfies the weak axiom (proved directly). -/
theorem exercise_2_F_15_weakAxiom : WeakAxiom demand_2_F_15 := by
  intro p w p' w' hd hd' hle hne
  have hc := hd.1 2
  have hc' := hd'.1 2
  -- normalised prices and wealth
  set q0 := p 0 / p 2
  set q1 := p 1 / p 2
  set u := w / p 2
  set r0 := p' 0 / p' 2
  set r1 := p' 1 / p' 2
  set u' := w' / p' 2
  have hx : demand_2_F_15 p w = ![q1 - q0, -q1, u + (q0 ^ 2 - q0 * q1 + q1 ^ 2)] := by
    funext l
    fin_cases l <;> simp [demand_2_F_15, q0, q1, u] <;> field_simp
  have hx' : demand_2_F_15 p' w' = ![r1 - r0, -r1, u' + (r0 ^ 2 - r0 * r1 + r1 ^ 2)] := by
    funext l
    fin_cases l <;> simp [demand_2_F_15, r0, r1, u'] <;> field_simp
  have hdot : ∀ (z : Fin 3 → ℝ), p ⬝ᵥ z = p 2 * (q0 * z 0 + q1 * z 1 + z 2) := by
    intro z
    simp only [dotProduct, Fin.sum_univ_three, q0, q1]
    field_simp
  have hdot' : ∀ (z : Fin 3 → ℝ), p' ⬝ᵥ z = p' 2 * (r0 * z 0 + r1 * z 1 + z 2) := by
    intro z
    simp only [dotProduct, Fin.sum_univ_three, r0, r1]
    field_simp
  have hw : w = p 2 * u := by simp only [u]; field_simp
  have hw' : w' = p' 2 * u' := by simp only [u']; field_simp
  rw [hdot, hx', hw] at hle
  rw [hdot', hx, hw']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hle ⊢
  have hle' : q0 * (r1 - r0) + q1 * -r1 + (u' + (r0 ^ 2 - r0 * r1 + r1 ^ 2)) ≤ u :=
    le_of_mul_le_mul_left hle hc
  apply mul_lt_mul_of_pos_left _ hc'
  by_cases hq : q0 = r0 ∧ q1 = r1
  · obtain ⟨e0, e1⟩ := hq
    have hu : u ≠ u' := by
      intro hu
      apply hne
      rw [hx, hx', e0, e1, hu]
    rw [← e0, ← e1] at hle' ⊢
    have : u' ≤ u := by nlinarith
    have : u' < u := lt_of_le_of_ne this (Ne.symm hu)
    nlinarith
  · have hpos : 0 < (q0 - r0) ^ 2 - (q0 - r0) * (q1 - r1) + (q1 - r1) ^ 2 := by
      apply quadForm_pos
      by_contra hc0
      push Not at hc0
      exact hq ⟨by linarith [hc0.1], by linarith [hc0.2]⟩
    nlinarith

/-- **Exercise 2.F.15** (MWG, p. 39). The Exercise 2.F.15 demand is differentiable at every
domain point. -/
theorem demand_2_F_15_differentiableAt {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_F_15) (p, w) := by
  have h2 := (hd.1 2).ne'
  have h2' : p 2 ^ 2 ≠ 0 := pow_ne_zero 2 h2
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_F_15, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.F.15** (MWG, p. 39). The compensated derivative `S v` of the demand. -/
theorem slutsky_2_F_15_mulVec {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v =
    ![((v 1 - v 0) * p 2 - (p 1 - p 0) * v 2) / p 2 ^ 2, -((v 1 * p 2 - p 1 * v 2) / p 2 ^ 2),
      (p 0 * v 0 - p 0 * v 1 + p 1 * v 1) / p 2 ^ 2 -
        (p 0 ^ 2 - p 0 * p 1 + p 1 ^ 2) * v 2 / p 2 ^ 3] := by
  have hD := (demand_2_F_15_differentiableAt hd).hasFDerivAt
  have h2 := (hd.1 2).ne'
  have h2' : p 2 + 0 * v 2 ≠ 0 := by simpa using h2
  apply slutsky_mulVec_of_hasDerivAt hD
  intro l
  fin_cases l
  · convert ((hasDerivAt_affine (p 1) (v 1)).sub (hasDerivAt_affine (p 0) (v 0))).div
      (hasDerivAt_affine (p 2) (v 2)) h2' using 1
    · funext t
      simp [demand_2_F_15]
    · simp
  · convert ((hasDerivAt_affine (p 1) (v 1)).div (hasDerivAt_affine (p 2) (v 2)) h2').neg
      using 1
    · funext t
      simp [demand_2_F_15]
    · simp
  · set c := v ⬝ᵥ demand_2_F_15 p w with hc
    have hA := hasDerivAt_affine (p 0) (v 0)
    have hB := hasDerivAt_affine (p 1) (v 1)
    have hC := hasDerivAt_affine (p 2) (v 2)
    have hnum := ((hA.pow 2).sub (hA.mul hB)).add (hB.pow 2)
    have hden := hC.pow 2
    have hq := hnum.div hden (by simpa using pow_ne_zero 2 h2)
    have hw := (hasDerivAt_affine w c).div hC h2'
    convert hw.add hq using 1
    · funext t
      simp [demand_2_F_15]
    · rw [hc]
      simp [demand_2_F_15, dotProduct, Fin.sum_univ_three]
      field_simp
      ring

/-- **Exercise 2.F.15** (MWG, p. 39). The Slutsky quadratic form is
`v·S v = -Q(p₃v₁ - v₃p₁, p₃v₂ - v₃p₂)/p₃³` with `Q(a, b) = a² - ab + b²`. -/
theorem exercise_2_F_15_quadratic {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v =
    -(((p 2 * v 0 - v 2 * p 0) ^ 2 - (p 2 * v 0 - v 2 * p 0) * (p 2 * v 1 - v 2 * p 1) +
      (p 2 * v 1 - v 2 * p 1) ^ 2) / p 2 ^ 3) := by
  rw [slutsky_2_F_15_mulVec hd]
  have h2 := (hd.1 2).ne'
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-- **Exercise 2.F.15** (MWG, p. 39). `v·S(p, w) v < 0` for every `v` that is not a multiple of
`p`. -/
theorem exercise_2_F_15_negDef_off_p {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin 3 → ℝ) (hv : ∀ α : ℝ, v ≠ α • p) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v < 0 := by
  rw [exercise_2_F_15_quadratic hd]
  have hc := hd.1 2
  rw [neg_neg_iff_pos]
  apply div_pos _ (pow_pos hc 3)
  apply quadForm_pos
  by_contra h
  push Not at h
  apply hv (v 2 / p 2)
  funext l
  fin_cases l
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [h.1]
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [h.2]
  · simp only [Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- **Exercise 2.F.15** (MWG, p. 39). The Slutsky matrix is not symmetric: `s₁₂ = 1/p₃` while
`s₂₁ = 0`. -/
theorem exercise_2_F_15_not_symm {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    ¬ (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)).IsSymm := by
  intro h
  have e01 := congrFun (slutsky_2_F_15_mulVec hd (Pi.single 1 1)) 0
  have e10 := congrFun (slutsky_2_F_15_mulVec hd (Pi.single 0 1)) 1
  rw [Matrix.mulVec_single_one] at e01 e10
  have hs := congrFun (congrFun h.eq 0) 1
  simp only [Matrix.transpose_apply] at hs
  simp only [Matrix.col_apply] at e01 e10
  rw [← hs, e10] at e01
  have h2 := (hd.1 2).ne'
  have key : p 2 / p 2 ^ 2 = 0 := by simpa using e01.symm
  exact div_ne_zero h2 (pow_ne_zero 2 h2) key

/-! ### Exercise 2.F.17 -/

/-- **Exercise 2.F.17** (MWG, p. 39). The demand `x_k(p, w) = w / ∑_ℓ p_ℓ`. -/
noncomputable def demand_2_F_17 (L : ℕ) : DemandFunction L := fun p w _ => w / ∑ l, p l

/-- **Exercise 2.F.17(a)** (MWG, p. 39). The demand is homogeneous of degree zero. -/
theorem exercise_2_F_17a (L : ℕ) : HomogeneousZero (demand_2_F_17 L) := by
  intro p w a hd ha
  funext k
  simp only [demand_2_F_17, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ ha.ne']

/-- With at least one good, the price sum is positive. -/
theorem sum_prices_pos {L : ℕ} {p : Fin L → ℝ} (hp : StrictlyPositive p) (l : Fin L) :
    0 < ∑ k, p k :=
  Finset.sum_pos (fun k _ => hp k) ⟨l, Finset.mem_univ l⟩

/-- **Exercise 2.F.17(b)** (MWG, p. 39). The demand satisfies Walras' law (for `L ≥ 1`). -/
theorem exercise_2_F_17b (L : ℕ) [NeZero L] : WalrasLaw (demand_2_F_17 L) := by
  intro p w hd
  have := (sum_prices_pos hd.1 0).ne'
  simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul]
  field_simp

/-- **Exercise 2.F.17(c)** (MWG, p. 39). The demand satisfies the weak axiom. -/
theorem exercise_2_F_17c (L : ℕ) : WeakAxiom (demand_2_F_17 L) := by
  intro p w p' w' hd hd' hle hne
  rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨l⟩⟩
  · exact absurd (funext fun i => (hL.false i).elim) hne
  have hs := sum_prices_pos hd.1 l
  have hs' := sum_prices_pos hd'.1 l
  simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul] at hle ⊢
  have hne' : w' / ∑ k, p' k ≠ w / ∑ k, p k := fun h => hne (funext fun _ => h)
  have hle' : w' / ∑ k, p' k ≤ w / ∑ k, p k := by
    rw [le_div_iff₀ hs]
    linarith
  have hlt := lt_of_le_of_ne hle' hne'
  rw [div_lt_div_iff₀ hs' hs] at hlt
  rw [mul_div_assoc', lt_div_iff₀ hs]
  linarith

/-- The Exercise 2.F.17 demand is differentiable at every domain point. -/
theorem demand_2_F_17_differentiableAt {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (l : Fin L) : DifferentiableAt ℝ (Function.uncurry (demand_2_F_17 L)) (p, w) := by
  have hs := (sum_prices_pos hd.1 l).ne'
  rw [differentiableAt_pi]
  intro i
  simp only [demand_2_F_17, Function.uncurry_def, div_eq_mul_inv]
  fun_prop (disch := assumption)

/-- **Exercise 2.F.17(d)** (MWG, p. 39). The Slutsky matrix is zero at every `(p, w)`. -/
theorem exercise_2_F_17d_zero {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (l : Fin L) :
    slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w)) (demand_2_F_17 L p w)
      = 0 := by
  have hD := (demand_2_F_17_differentiableAt hd l).hasFDerivAt
  have hs := (sum_prices_pos hd.1 l).ne'
  have hcol : ∀ v, Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L))
      (p, w)) (demand_2_F_17 L p w)) v = 0 := by
    intro v
    apply slutsky_mulVec_of_hasDerivAt hD
    intro k
    set c := v ⬝ᵥ demand_2_F_17 L p w with hc
    have h := (hasDerivAt_affine w c).div (hasDerivAt_affine (∑ l, p l) (∑ l, v l))
      (by simpa using hs)
    convert h using 1
    · funext t
      simp [demand_2_F_17, Finset.sum_add_distrib, Finset.mul_sum]
    · rw [hc]
      simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul, Pi.zero_apply]
      field_simp
      ring
  ext i k
  have := congrFun (hcol (Pi.single k 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa using this

/-- **Exercise 2.F.17(d)** (MWG, p. 39). The Slutsky matrix is negative semidefinite,
symmetric, and (with at least one good) not negative definite. -/
theorem exercise_2_F_17d {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    NegSemidef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)) ∧
      (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)).IsSymm ∧
      ¬ NegDef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)) := by
  rw [exercise_2_F_17d_zero hd l]
  refine ⟨fun z => by simp, Matrix.isSymm_zero, fun h => ?_⟩
  have := h (Pi.single l 1) (by simp)
  simp at this

end MWG.ConsumerChoice
