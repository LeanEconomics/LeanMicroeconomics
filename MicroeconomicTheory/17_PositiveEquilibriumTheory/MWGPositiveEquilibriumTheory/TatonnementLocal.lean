/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Tatonnement
import MWGPositiveEquilibriumTheory.IndexTwoGoods
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Local analysis of tâtonnement (MWG Section 17.H, p. 624)

With the numeraire normalization `p_L = 1` the dynamics are `dp̂ₗ/dt = cₗ ẑₗ(p̂)`, `ℓ < L`
(`IsNormTatPath`); `p̂*` is locally stable if trajectories starting within some `ε` of `p̂*`
converge to it (`NormLocallyStable`).

* p. 624: if `Dẑ(p̂*)` is negative definite, `p̂*` is locally stable for every choice of the
  speeds of adjustment `C` (`tat_local_stable_of_negDef`); the proof is the Lyapunov function
  `∑ₗ (1/cₗ)(p̂ₗ - p̂*ₗ)²`, which decays exponentially near `p̂*`.
* p. 624: "`p*` is locally stable if and only if all the eigenvalues of `CDẑ(p*)` have negative
  real parts". The "only if" is false: in `tat_eigen_counterexample` an excess demand with three
  goods (homogeneous, Walras' law) has a regular equilibrium where `Dẑ` has eigenvalues `±i`
  (characteristic polynomial `X² + 1`), yet every normalized trajectory converges to it. The
  "if" direction (Lyapunov's indirect method) is proved here for negative definite `Dẑ(p̂*)` and,
  with two goods, in `tat_two_locally_stable`; in general it is OPEN (it needs the Lyapunov
  matrix equation `AᵀP + PA = -I` for a matrix with eigenvalues of negative real part).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {n : ℕ}

/-! ### Normalized dynamics -/

/-- **Section 17.H** (MWG, p. 624). With `p_L = 1` fixed, (17.H.1) is limited to the first
`L - 1` prices: `q(t) ≫ 0` and `dqₗ/dt = cₗ ẑₗ(q(t))` for `t ≥ 0`, with `ẑ = normED z`. -/
def IsNormTatPath (c : Fin n → ℝ) (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (q : ℝ → Fin n → ℝ) : Prop :=
  (∀ t, 0 ≤ t → q t ∈ posOrthant n) ∧
    ∀ t, 0 ≤ t → HasDerivWithinAt q (tatField c (normED z) (q t)) (Ici 0) t

/-- **Section 17.H** (MWG, p. 624). `p̂*` is *locally stable*: there is `ε > 0` such that
`p̂(t) → p̂*` whenever `‖p̂(0) - p̂*‖ < ε`. -/
def NormLocallyStable (c : Fin n → ℝ) (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (qs : Fin n → ℝ) : Prop :=
  ∃ ε > 0, ∀ q : ℝ → Fin n → ℝ, IsNormTatPath c z q → dist (q 0) qs < ε →
    Tendsto q atTop (𝓝 qs)

/-- Exponential decay: if `F' ≤ -μF` on `[0, ∞)`, then `F(t) ≤ F(0)e^{-μt}`. -/
theorem tat_exp_decay {F F' : ℝ → ℝ} {μ : ℝ}
    (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (F' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → F' t ≤ -μ * F t) {t : ℝ} (ht : 0 ≤ t) :
    F t ≤ F 0 * Real.exp (-μ * t) := by
  have hmono := tat_monotoneOn (F := fun s => -(F s * Real.exp (μ * s)))
    (F' := fun s => -(F' s * Real.exp (μ * s) + F s * (Real.exp (μ * s) * μ)))
    (fun s hs => ((hF s hs).mul ((((hasDerivAt_id s).const_mul μ).exp).congr_deriv
      (by simp) |>.hasDerivWithinAt)).fun_neg) (fun s hs => by
        have := mul_le_mul_of_nonneg_right (hb s hs) (Real.exp_pos (μ * s)).le
        nlinarith)
  have h := hmono (Set.mem_Ici.2 le_rfl) ht ht
  simp only [mul_zero, Real.exp_zero, mul_one, neg_le_neg_iff] at h
  have he : Real.exp (μ * t) * Real.exp (-μ * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc F t = F t * Real.exp (μ * t) * Real.exp (-μ * t) := by rw [mul_assoc, he, mul_one]
    _ ≤ F 0 * Real.exp (-μ * t) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- `|a·b| ≤ n ‖a‖ ‖b‖` in `ℝⁿ` with the sup norm. -/
theorem tat_dot_le (a b : Fin n → ℝ) : |a ⬝ᵥ b| ≤ n * (‖a‖ * ‖b‖) := by
  unfold dotProduct
  calc |∑ l, a l * b l| ≤ ∑ l, |a l * b l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin n, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm a l) (by simpa using norm_le_pi_norm b l)
          (abs_nonneg _) (norm_nonneg _)
    _ = n * (‖a‖ * ‖b‖) := by simp

/-- A negative definite quadratic form is uniformly negative: `v·Dv ≤ -m‖v‖²` for some `m > 0`. -/
theorem tat_negDef_uniform {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hnd : ∀ v ≠ 0, v ⬝ᵥ D v < 0) : ∃ m > 0, ∀ v, v ⬝ᵥ D v ≤ -m * ‖v‖ ^ 2 := by
  by_cases hS : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty
  · have hcont : Continuous fun v : Fin n → ℝ => v ⬝ᵥ D v :=
      continuous_id.dotProduct D.continuous
    obtain ⟨v0, hv0, hmax⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMaxOn hS
      hcont.continuousOn
    have hv0ne : v0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hv0
      exact zero_ne_one hv0
    refine ⟨-(v0 ⬝ᵥ D v0), neg_pos.2 (hnd v0 hv0ne), fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
      set w := ‖v‖⁻¹ • v with hw
      have hwS : w ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, hw, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnv.ne']
      have h1 : w ⬝ᵥ D w ≤ v0 ⬝ᵥ D v0 := hmax hwS
      have h2 : v ⬝ᵥ D v = ‖v‖ ^ 2 * (w ⬝ᵥ D w) := by
        have hvw : v = ‖v‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
        conv_lhs => rw [hvw]
        rw [D.map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2]
      nlinarith [sq_nonneg ‖v‖]
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · exfalso
      apply hS
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.2 hv).ne']


/-- If `|xₗ|² ≤ cₗ V` for all `ℓ` and `(∑ₗ cₗ) V < r²`, then `‖x‖ < r`. -/
theorem tat_norm_lt_of_wNormSq {c : Fin n → ℝ} (hc : ∀ l, 0 < c l) {x : Fin n → ℝ} {r : ℝ}
    (hr : 0 < r) (h : (∑ l, c l) * wNormSq c x < r ^ 2) : ‖x‖ < r := by
  have hV := wNormSq_nonneg hc x
  have hCs : 0 ≤ ∑ l, c l := Finset.sum_nonneg fun l _ => (hc l).le
  have hle : ‖x‖ ≤ Real.sqrt ((∑ l, c l) * wNormSq c x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun l => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ((sq_le_wNormSq hc x l).trans ?_)
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := c) (fun k _ => (hc k).le)
      (Finset.mem_univ l)) hV
  refine lt_of_le_of_lt hle ?_
  rw [Real.sqrt_lt' hr]
  exact h

/-- `∑ₗ xₗ²/cₗ ≤ (∑ₗ 1/cₗ) ‖x‖²`. -/
theorem tat_wNormSq_le {c : Fin n → ℝ} (hc : ∀ l, 0 < c l) (x : Fin n → ℝ) :
    wNormSq c x ≤ (∑ l, 1 / c l) * ‖x‖ ^ 2 := by
  unfold wNormSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 : x l ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x l) 2
  have := hc l
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Section 17.H** (MWG, p. 624; footnote 66). If `ẑ(p̂*) = 0` and `Dẑ(p̂*)` is negative
definite, then `p̂*` is locally stable for every choice of the speeds of adjustment `cₗ > 0`
("irrespective of the speeds of adjustment"). -/
theorem tat_local_stable_of_negDef {c : Fin n → ℝ} (hc : ∀ l, 0 < c l)
    {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {qs : Fin n → ℝ} (h0 : normED z qs = 0)
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt (normED z) D qs)
    (hnd : ∀ v ≠ 0, v ⬝ᵥ D v < 0) : NormLocallyStable c z qs := by
  obtain ⟨m, hm, hmD⟩ := tat_negDef_uniform hnd
  set κ := m / (2 * ((n : ℝ) + 1)) with hκ
  have hκpos : 0 < κ := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO.1 hD).def hκpos)
  have hkey : ∀ x, ‖x - qs‖ < δ → (x - qs) ⬝ᵥ normED z x ≤ -(m / 2) * ‖x - qs‖ ^ 2 := by
    intro x hx
    have he := hball (show dist x qs < δ by rwa [dist_eq_norm])
    rw [h0, sub_zero] at he
    set e := normED z x - D (x - qs) with hedef
    have hsplit : (x - qs) ⬝ᵥ normED z x = (x - qs) ⬝ᵥ D (x - qs) + (x - qs) ⬝ᵥ e := by
      rw [hedef, dotProduct_sub]; ring
    have h1 := hmD (x - qs)
    have h2 := (abs_le.1 (tat_dot_le (x - qs) e)).2
    have h3 : (n : ℝ) * (‖x - qs‖ * ‖e‖) ≤ m / 2 * ‖x - qs‖ ^ 2 := by
      have h4 : ‖x - qs‖ * ‖e‖ ≤ ‖x - qs‖ * (κ * ‖x - qs‖) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      have h5 : (n : ℝ) * κ ≤ m / 2 := by
        rw [hκ, mul_div_assoc']
        rw [div_le_div_iff₀ (by positivity) two_pos]
        nlinarith
      calc (n : ℝ) * (‖x - qs‖ * ‖e‖) ≤ n * (‖x - qs‖ * (κ * ‖x - qs‖)) :=
            mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg n)
        _ = (n * κ) * ‖x - qs‖ ^ 2 := by ring
        _ ≤ m / 2 * ‖x - qs‖ ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
    rw [hsplit]
    linarith
  set C1 := ∑ l, 1 / c l with hC1
  set Cs := ∑ l, c l with hCs
  have hC1 : 0 ≤ C1 := Finset.sum_nonneg fun l _ => (one_div_pos.2 (hc l)).le
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun l _ => (hc l).le
  set ε := δ / Real.sqrt (C1 * Cs + 1) with hε
  have hsq : 0 < Real.sqrt (C1 * Cs + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε, div_pos hδ hsq, fun q hq hq0 => ?_⟩
  set V : ℝ → ℝ := fun t => wNormSq c (q t - qs) with hV
  have hVd : ∀ t, 0 ≤ t →
      HasDerivWithinAt V (2 * ((q t - qs) ⬝ᵥ normED z (q t))) (Ici 0) t := by
    intro t ht
    have hα : HasDerivWithinAt (fun s => q s - qs)
        (tatField c (fun x => normED z (x + qs)) (q t - qs)) (Ici 0) t := by
      have := (hq.2 t ht).sub_const qs
      have he : tatField c (fun x => normED z (x + qs)) (q t - qs) =
          tatField c (normED z) (q t) := by
        unfold tatField; simp
      rw [he]
      exact this
    have := tatField_hasDeriv_wNormSq hc hα
    simpa using this
  have hV0 : Cs * V 0 < δ ^ 2 := by
    have h1 : V 0 ≤ C1 * ‖q 0 - qs‖ ^ 2 := tat_wNormSq_le hc _
    have h2 : ‖q 0 - qs‖ ^ 2 < ε ^ 2 := by
      rw [← dist_eq_norm]
      exact pow_lt_pow_left₀ hq0 dist_nonneg two_ne_zero
    have h3 : ε ^ 2 = δ ^ 2 / (C1 * Cs + 1) := by
      rw [hε, div_pow, Real.sq_sqrt (by positivity)]
    have h4 : Cs * V 0 ≤ Cs * C1 * ε ^ 2 := by
      calc Cs * V 0 ≤ Cs * (C1 * ‖q 0 - qs‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hCs0
        _ ≤ Cs * C1 * ε ^ 2 := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h2.le (by positivity)
    rw [h3] at h4
    have h5 : Cs * C1 * (δ ^ 2 / (C1 * Cs + 1)) < δ ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg δ, pow_pos hδ 2]
    linarith
  -- the trajectory stays in the `δ`-ball
  have hVle : ∀ T, 0 ≤ T → V T ≤ V 0 := by
    intro T hT
    have hη : ∀ η, 0 < η → Cs * (V 0 + η) < δ ^ 2 → V T ≤ V 0 + η := by
      intro η hη hηδ
      refine image_le_of_deriv_right_lt_deriv_boundary' (f := V)
        (f' := fun t => 2 * ((q t - qs) ⬝ᵥ normED z (q t))) (B := fun _ => V 0 + η)
        (B' := fun _ => 0) (fun x hx => (hVd x hx.1).continuousWithinAt.mono fun y hy => hy.1)
        (fun x hx => (hVd x hx.1).mono fun y (hy : x ≤ y) => hx.1.trans hy)
        (by linarith) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_
        ⟨hT, le_rfl⟩
      intro x _ hVx
      have hlt : ‖q x - qs‖ < δ := tat_norm_lt_of_wNormSq hc hδ (by rw [← hVx] at hηδ; exact hηδ)
      have hne : q x - qs ≠ 0 := by
        intro h
        have : V x = 0 := by simp only [hV]; rw [h]; simp [wNormSq]
        have := wNormSq_nonneg hc (q 0 - qs)
        simp only [hV] at hVx
        linarith
      have h1 := hkey (q x) hlt
      have h2 := mul_pos hm (pow_pos (norm_pos_iff.2 hne) 2)
      linarith
    by_contra hcon
    push Not at hcon
    have hV0' : 0 ≤ V 0 := wNormSq_nonneg hc _
    set η := min (V T - V 0) ((δ ^ 2 - Cs * V 0) / (Cs + 1)) / 2 with hηdef
    have hpos2 : 0 < (δ ^ 2 - Cs * V 0) / (Cs + 1) := div_pos (by linarith) (by positivity)
    have hη0 : 0 < η := by
      have : 0 < min (V T - V 0) ((δ ^ 2 - Cs * V 0) / (Cs + 1)) := lt_min (by linarith) hpos2
      linarith
    have h1 := min_le_left (V T - V 0) ((δ ^ 2 - Cs * V 0) / (Cs + 1))
    have h2 := min_le_right (V T - V 0) ((δ ^ 2 - Cs * V 0) / (Cs + 1))
    have h3 : Cs * η < δ ^ 2 - Cs * V 0 := by
      have h4 : η < (δ ^ 2 - Cs * V 0) / (Cs + 1) := by linarith
      rw [lt_div_iff₀ (by positivity)] at h4
      nlinarith
    have := hη η hη0 (by linarith)
    linarith
  have hin : ∀ t, 0 ≤ t → ‖q t - qs‖ < δ := fun t ht =>
    tat_norm_lt_of_wNormSq hc hδ (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hVle t ht) hCs0) hV0)
  -- exponential decay
  set μ := m / (C1 + 1) with hμ
  have hdecay : ∀ t, 0 ≤ t → V t ≤ V 0 * Real.exp (-μ * t) := fun t ht =>
    tat_exp_decay hVd (fun s hs => by
      have h1 := hkey (q s) (hin s hs)
      have h2 : V s ≤ (C1 + 1) * ‖q s - qs‖ ^ 2 := by
        have := tat_wNormSq_le hc (q s - qs)
        nlinarith [sq_nonneg ‖q s - qs‖]
      have h3 : μ * V s ≤ m * ‖q s - qs‖ ^ 2 := by
        rw [hμ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith) ht
  have hlim : Tendsto (fun t => Cs * (V 0 * Real.exp (-μ * t))) atTop (𝓝 0) := by
    have : Tendsto (fun t => -μ * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 (by positivity))
    simpa using ((Real.tendsto_exp_atBot.comp this).const_mul (V 0)).const_mul Cs
  refine Metric.tendsto_atTop.2 fun r hr => ?_
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hlim (r ^ 2) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  have h1 := hT t ((le_max_left _ _).trans ht)
  rw [Real.dist_eq, sub_zero] at h1
  have h2 : Cs * V t ≤ Cs * (V 0 * Real.exp (-μ * t)) :=
    mul_le_mul_of_nonneg_left (hdecay t ht0) hCs0
  rw [dist_eq_norm]
  exact tat_norm_lt_of_wNormSq hc hr (lt_of_le_of_lt h2 (lt_of_abs_lt h1))


/-- **Section 17.H** (MWG, p. 624), instance of `tat_local_stable_of_negDef`: one Cobb-Douglas
consumer with `a = ω = (1, 1)`; at the equilibrium `p̂* = 1`, `Dẑ(p̂*) = -1/2 < 0`, so `p̂*` is
locally stable for every speed `c > 0`. -/
theorem tat_local_stable_cd1 {c : Fin 1 → ℝ} (hc : ∀ l, 0 < c l) :
    NormLocallyStable c (cd1ED ![1, 1] ![1, 1]) (fun _ => 1) := by
  have hq : (fun _ => (1 : ℝ)) ∈ posOrthant 1 := fun _ => one_pos
  have heq : IsNormEqm (cd1ED ![1, 1] ![1, 1]) (fun _ => 1) := by
    refine (cd1_eqm_iff (fun l => by fin_cases l <;> simp) (fun l => by fin_cases l <;> simp)).2
      fun l => ?_
    fin_cases l
    simp
  refine tat_local_stable_of_negDef hc heq.normED_eq_zero (cd1_hasFDerivAt _ _ hq) ?_
  intro v hv
  have hv0 : v 0 ≠ 0 := fun h => hv (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  have : v ⬝ᵥ (LinearMap.toContinuousLinearMap (Matrix.toLin' (cd1Jacobian ![1, 1] ![1, 1]
      (fun _ => 1)))) v = -(1 / 2) * v 0 ^ 2 := by
    simp [cd1Jacobian, dotProduct, Matrix.mulVec, Matrix.vecMulVec, normPrice,
      Fin.sum_univ_two, Matrix.diagonal, Fin.snoc]
    norm_num
    ring
  rw [this]
  have := pow_pos (abs_pos.2 hv0) 2
  rw [sq_abs] at this
  linarith

/-! ### The eigenvalue criterion: "only if" fails -/

/-- The normalized excess demand of the counterexample: with `x = p̂₁ - 1`, `y = p̂₂ - 1`,
`ẑ = (-y - x³, x - y³)`. -/
noncomputable def cxF (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-(q 1 - 1) - (q 0 - 1) ^ 3, (q 0 - 1) - (q 1 - 1) ^ 3]

/-- The excess demand with three goods whose normalized form is `cxF`: the first two excess
demands depend on the relative prices `(p₁/p₃, p₂/p₃)`, and `z₃` is fixed by Walras' law. -/
noncomputable def cxZ (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![cxF ![p 0 / p 2, p 1 / p 2] 0, cxF ![p 0 / p 2, p 1 / p 2] 1,
    -(p 0 * cxF ![p 0 / p 2, p 1 / p 2] 0 + p 1 * cxF ![p 0 / p 2, p 1 / p 2] 1) / p 2]

/-- `cxZ` is homogeneous of degree zero and satisfies Walras' law. -/
theorem cxZ_props : EDHomogeneous cxZ ∧ EDWalrasLaw cxZ := by
  refine ⟨fun p hp α hα => ?_, fun p hp => ?_⟩
  · have h1 : α * p 0 / (α * p 2) = p 0 / p 2 := mul_div_mul_left _ _ hα.ne'
    have h2 : α * p 1 / (α * p 2) = p 1 / p 2 := mul_div_mul_left _ _ hα.ne'
    have h3 := (hp 2).ne'
    simp only [cxZ, Pi.smul_apply, smul_eq_mul, h1, h2]
    congr 2
    congr 1
    field_simp
  · have h3 := (hp 2).ne'
    simp only [cxZ, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    ring

/-- The normalized excess demand of `cxZ` is `cxF`. -/
theorem normED_cxZ : normED cxZ = cxF := by
  funext q l
  have h0 : normPrice q 0 = q 0 := normPrice_castSucc q 0
  have h1 : normPrice q 1 = q 1 := normPrice_castSucc q 1
  have h2 : normPrice q 2 = 1 := normPrice_last q
  fin_cases l
  · simp only [normED, truncExcessDemand, cxZ]
    simp [h0, h1, h2, cxF]
  · simp only [normED, truncExcessDemand, cxZ]
    simp [h0, h1, h2, cxF]

/-- The Jacobian `Dẑ(1, 1) = [[0, -1], [1, 0]]`. -/
def cxJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem cxF_hasFDerivAt :
    HasFDerivAt cxF (LinearMap.toContinuousLinearMap (Matrix.toLin' cxJ)) ![1, 1] := by
  rw [hasFDerivAt_pi']
  intro i
  have hp0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (0 : Fin 2) ![(1 : ℝ), 1]
  have hp1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (1 : Fin 2) ![(1 : ℝ), 1]
  fin_cases i
  · have h := ((hp1.sub_const 1).neg).sub ((hp0.sub_const 1).pow 3)
    have hfun : (fun x => cxF x ((fun i => i) ⟨0, by norm_num⟩)) =
        (-fun x : Fin 2 → ℝ => x 1 - 1) - fun x => (x 0 - 1) ^ 3 := by
      funext x; simp [cxF]
    rw [hfun]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [cxJ, dotProduct, Fin.sum_univ_two]
  · have h := (hp0.sub_const 1).sub ((hp1.sub_const 1).pow 3)
    have hfun : (fun x => cxF x ((fun i => i) ⟨1, by norm_num⟩)) =
        (fun x : Fin 2 → ℝ => x 0 - 1) - fun x => (x 1 - 1) ^ 3 := by
      funext x; simp [cxF]
    rw [hfun]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [cxJ, dotProduct, Fin.sum_univ_two]

/-- `(1, 1)` is a regular normalized equilibrium of `cxZ`: `|Dẑ(1, 1)| = 1`. -/
theorem cxZ_regular : IsRegularEqm cxZ ![1, 1] := by
  have hd : HasFDerivAt (normED cxZ) (LinearMap.toContinuousLinearMap (Matrix.toLin' cxJ))
      ![1, 1] := by rw [normED_cxZ]; exact cxF_hasFDerivAt
  refine ⟨⟨normPrice_mem_posOrthant.2 fun l => by fin_cases l <;> simp, ?_⟩, hd.differentiableAt,
    ?_⟩
  · funext l
    have h0 : normPrice (![1, 1] : Fin 2 → ℝ) 0 = 1 := normPrice_castSucc _ 0
    have h1 : normPrice (![1, 1] : Fin 2 → ℝ) 1 = 1 := normPrice_castSucc _ 1
    have h2 : normPrice (![1, 1] : Fin 2 → ℝ) 2 = 1 := normPrice_last _
    fin_cases l <;> simp [cxZ, cxF, h0, h1, h2]
  · rw [hd.fderiv, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
      LinearMap.det_toLin', cxJ, Matrix.det_fin_two_of]
    norm_num

/-- The characteristic polynomial of `CDẑ(1, 1)` (`C = I`) is `X² + 1`: the eigenvalues `±i` have
zero real part. -/
theorem cxJ_eigen : cxJ.charpoly = Polynomial.X ^ 2 + 1 ∧
    ∀ μ : ℂ, μ ^ 2 + 1 = 0 → μ.re = 0 := by
  refine ⟨?_, fun μ hμ => ?_⟩
  · rw [Matrix.charpoly_fin_two]
    simp [cxJ]
  · have hre : μ.re * μ.re - μ.im * μ.im + 1 = 0 := by
      have := congrArg Complex.re hμ
      simpa [pow_two] using this
    have him : μ.re * μ.im + μ.im * μ.re = 0 := by
      have := congrArg Complex.im hμ
      simpa [pow_two] using this
    have hm : μ.re * μ.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg μ.re]

/-- Along every normalized trajectory of `cxZ` (speeds `1`), `q(t) → (1, 1)`: the Lyapunov function
`V = x² + y²` has `dV/dt = -2(x⁴ + y⁴) ≤ -V²`. -/
theorem cxZ_converges {q : ℝ → Fin 2 → ℝ} (hq : IsNormTatPath (fun _ => 1) cxZ q) :
    Tendsto q atTop (𝓝 ![1, 1]) := by
  have hc : ∀ l : Fin 2, (0 : ℝ) < (fun _ => (1 : ℝ)) l := fun _ => one_pos
  set qs : Fin 2 → ℝ := ![1, 1] with hqs
  set V : ℝ → ℝ := fun t => wNormSq (fun _ => 1) (q t - qs) with hV
  have hVd : ∀ t, 0 ≤ t →
      HasDerivWithinAt V (2 * ((q t - qs) ⬝ᵥ normED cxZ (q t))) (Ici 0) t := by
    intro t ht
    have hα : HasDerivWithinAt (fun s => q s - qs)
        (tatField (fun _ => 1) (fun x => normED cxZ (x + qs)) (q t - qs)) (Ici 0) t := by
      have := (hq.2 t ht).sub_const qs
      have he : tatField (fun _ => (1 : ℝ)) (fun x => normED cxZ (x + qs)) (q t - qs) =
          tatField (fun _ => 1) (normED cxZ) (q t) := by
        unfold tatField; simp
      rw [he]
      exact this
    have := tatField_hasDeriv_wNormSq hc hα
    simpa using this
  have hVform : ∀ t, V t = (q t 0 - 1) ^ 2 + (q t 1 - 1) ^ 2 := fun t => by
    simp [hV, wNormSq, Fin.sum_univ_two, hqs]
  have hV' : ∀ t, 2 * ((q t - qs) ⬝ᵥ normED cxZ (q t)) ≤ -V t ^ 2 := fun t => by
    rw [hVform, normED_cxZ]
    simp only [dotProduct, Fin.sum_univ_two, cxF, hqs, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg ((q t 0 - 1) ^ 2 - (q t 1 - 1) ^ 2)]
  have hV0 : ∀ t, 0 ≤ V t := fun t => wNormSq_nonneg hc _
  have hanti : AntitoneOn V (Ici 0) := by
    intro a ha b hb hab
    have := tat_monotoneOn (F := fun t => -V t) (fun t ht => (hVd t ht).fun_neg)
      (fun t _ => by have := hV' t; nlinarith [sq_nonneg (V t)]) ha hb hab
    simp only at this
    linarith
  have hsmall : ∀ ε > 0, ∃ T, 0 ≤ T ∧ V T < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hmono := tat_monotoneOn (F := fun t => -(V t + ε ^ 2 * t))
      (fun t ht => ((hVd t ht).add ((hasDerivWithinAt_id t _).const_mul (ε ^ 2))).fun_neg)
      (fun t ht => by
        have h1 := hV' t
        have h2 := hcon t ht
        have : ε ^ 2 ≤ V t ^ 2 := pow_le_pow_left₀ hε.le h2 2
        simp only [mul_one]
        linarith)
    set T := V 0 / ε ^ 2 + 1 with hT
    have hT0 : 0 ≤ T := by have := hV0 0; positivity
    have h1 := hmono (Set.mem_Ici.2 le_rfl) hT0 hT0
    simp only [mul_zero, add_zero, neg_le_neg_iff] at h1
    have h2 : ε ^ 2 * T = V 0 + ε ^ 2 := by rw [hT]; field_simp
    have := hV0 T
    nlinarith [pow_pos hε 2]
  refine Metric.tendsto_atTop.2 fun r hr => ?_
  obtain ⟨T, hT0, hT⟩ := hsmall (r ^ 2 / 2) (by positivity)
  refine ⟨T, fun t ht => ?_⟩
  have h1 : V t ≤ V T := hanti hT0 (hT0.trans ht) ht
  rw [dist_eq_norm]
  refine tat_norm_lt_of_wNormSq hc hr ?_
  have : (∑ l : Fin 2, (fun _ => (1 : ℝ)) l) = 2 := by norm_num
  rw [this]
  simp only [hV] at h1 hT
  linarith

/-- **Section 17.H** (MWG, p. 624), "`p*` is locally stable if and only if all the eigenvalues of
`CDẑ(p*)` have negative real parts": the "only if" is false. For the homogeneous excess demand
`cxZ` with Walras' law, `p̂* = (1, 1)` is a regular equilibrium, the eigenvalues of `CDẑ(p̂*)`
(`C = I`) are `±i` (characteristic polynomial `X² + 1`, zero real parts), yet `p̂*` is locally
(indeed globally) stable. -/
theorem tat_eigen_counterexample :
    EDHomogeneous cxZ ∧ EDWalrasLaw cxZ ∧ IsRegularEqm cxZ ![1, 1] ∧
      HasFDerivAt (normED cxZ) (LinearMap.toContinuousLinearMap (Matrix.toLin' cxJ)) ![1, 1] ∧
      cxJ.charpoly = Polynomial.X ^ 2 + 1 ∧ (∀ μ : ℂ, μ ^ 2 + 1 = 0 → μ.re = 0) ∧
      NormLocallyStable (fun _ => 1) cxZ ![1, 1] :=
  ⟨cxZ_props.1, cxZ_props.2, cxZ_regular, by rw [normED_cxZ]; exact cxF_hasFDerivAt,
    cxJ_eigen.1, cxJ_eigen.2, ⟨1, one_pos, fun _ hq _ => cxZ_converges hq⟩⟩

/-- **Footnote 66** (MWG, p. 624). The revealed-preference-like property of Proposition 17.H.1
implies negative semidefiniteness at the equilibrium: if `z` satisfies Walras' law, `z(p*) = 0`,
`z` is differentiable at `p*` with derivative `D`, and `p*·z(p) ≥ 0` for every `p ≫ 0`, then
`v·Dv ≤ 0` for every `v` (in particular for `v = (v̂, 0)`, so `Dẑ(p*)` is negative
semidefinite). -/
theorem footnote_17_66 {L : ℕ} {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    {ps : Fin L → ℝ} (hps : ps ∈ posOrthant L) (h0 : z ps = 0)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt z D ps)
    (hrev : ∀ q ∈ posOrthant L, 0 ≤ ps ⬝ᵥ z q) (v : Fin L → ℝ) : v ⬝ᵥ D v ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hline : HasDerivAt (fun t : ℝ => ps + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ps
  have hz := hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  set g : ℝ → ℝ := fun t => v ⬝ᵥ z (ps + t • v) with hg
  have hgd : HasDerivAt g (v ⬝ᵥ D v) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun l t => v l * z (ps + t • v) l)
      (A' := fun l => v l * D v l) fun l _ => (hasDerivAt_pi.1 hz l).const_mul (v l)
    simpa [hg, dotProduct] using h
  have hg0 : g 0 = 0 := by simp [hg, h0]
  obtain ⟨δ, hδ, hsign⟩ := two_goods_local_sign hgd hg0 hcon.ne'
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_posOrthant L) ps hps
  set t := min δ (r / (‖v‖ + 1)) / 2 with ht
  have hpos1 : 0 < min δ (r / (‖v‖ + 1)) := lt_min hδ (by positivity)
  have htpos : 0 < t := by positivity
  have htδ : t < δ := by
    have := min_le_left δ (r / (‖v‖ + 1)); linarith
  have hqin : ps + t • v ∈ posOrthant L := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    have h1 : t ≤ r / (‖v‖ + 1) / 2 := by
      have := min_le_right δ (r / (‖v‖ + 1)); linarith
    have h2 : r / (‖v‖ + 1) * ‖v‖ < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    nlinarith [norm_nonneg v]
  have hgt : 0 < g t := by
    have := hsign t htpos.ne' (by rw [sub_zero, abs_of_pos htpos]; exact htδ)
    rw [sub_zero] at this
    by_contra hle
    push Not at hle
    have : g t * t * (v ⬝ᵥ D v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle htpos.le) hcon.le
    linarith
  have hw := hW _ hqin
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at hw
  have := hrev _ hqin
  have : ps ⬝ᵥ z (ps + t • v) = -(t * g t) := by simp only [hg]; linarith
  nlinarith [mul_pos htpos hgt]

end MWG.PositiveEquilibriumTheory
