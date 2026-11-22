/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.REExamples

/-!
# Exercises 19.F.5 and 19.H.6 (MWG pp. 728-730)

* **Exercise 19.F.5** (insurance with unobservable disability): (a) with a full set of
  Arrow-Debreu markets the allocation equates marginal utilities, `U_a'(c_a) = U_d'(c_d)` and
  `c_a + c_d = k` (`exercise_19_F_5a`); (b) if this gives `c_a > c_d` it is incentive compatible and
  is the competitive outcome with unobservable disability (`exercise_19_F_5b`); (c) if it gives
  `c_a < c_d` it is not reachable, and the best incentive-compatible zero-profit allocation, the
  competitive outcome, is `c_a = c_d = k/2`, which is optimal among the allocations a government
  that cannot observe disability can achieve (`exercise_19_F_5c`).
* **Exercise 19.H.6**: (a) the Arrow-Debreu equilibrium: consumer 2 consumes `1/4` of good 1 in
  every state (`exercise_19_H_6a`); total surplus is maximal exactly when consumer 2's good-1
  consumption is `1/4` in every state (`exercise_19_H_6_surplus`), so allocations where it varies
  across states (as with non-contingent trade in (b), and in (c) within the event `{2, 3}`) are not
  Pareto optimal (`exercise_19_H_6_not_po`), while the allocations of (a) and (d) are.
-/

namespace MWG.EquilibriumUncertainty

/-! ## Exercise 19.F.5 -/

/-- The tangent-line inequality for a strictly concave differentiable function. -/
theorem strictConcave_tangent {D : Set ℝ} {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ D u) {x y a : ℝ}
    (hx : x ∈ D) (hy : y ∈ D) (ha : HasDerivAt u a x) : u y ≤ u x + a * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hu.slope_lt_of_hasDerivAt hx hy h ha
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr h)] at this
    linarith
  · subst h; simp
  · have := hu.lt_slope_of_hasDerivAt hy hx h ha
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr h)] at this
    linarith

/-- Ex ante expected utility `½ U_a(c_a) + ½ U_d(c_d)` of a worker able (probability `1/2`) or
disabled (probability `1/2`). -/
noncomputable def welfare19F5 (Ua Ud : ℝ → ℝ) (ca cd : ℝ) : ℝ := Ua ca / 2 + Ud cd / 2

/-- **Exercise 19.F.5(a)** (MWG, p. 728). With Arrow-Debreu markets open before disability is known
(actuarially fair prices, output `k` per able worker, so `c_a + c_d ≤ k` in expected value), the
equilibrium allocation is the solution of `max ½U_a(c_a) + ½U_d(c_d)`: if `U_a, U_d` are strictly
concave and increasing and `U_a'(c_a) = U_d'(c_d) ≥ 0` with `c_a + c_d = k`, then `(c_a, c_d)` is
optimal. -/
theorem exercise_19_F_5a {Ua Ud : ℝ → ℝ} (hca : StrictConcaveOn ℝ (Set.Ici 0) Ua)
    (hcd : StrictConcaveOn ℝ (Set.Ici 0) Ud) {k ca cd lam : ℝ} (hca0 : 0 ≤ ca) (hcd0 : 0 ≤ cd)
    (hk : ca + cd = k) (hlam : 0 ≤ lam) (hda : HasDerivAt Ua lam ca) (hdd : HasDerivAt Ud lam cd)
    {ya yd : ℝ} (hya : 0 ≤ ya) (hyd : 0 ≤ yd) (hy : ya + yd ≤ k) :
    welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd := by
  have h1 := strictConcave_tangent hca hca0 hya hda
  have h2 := strictConcave_tangent hcd hcd0 hyd hdd
  unfold welfare19F5
  nlinarith

/-- **Exercise 19.F.5(b)** (MWG, p. 728). If disability is unobservable, an able worker can claim
disability and consume `c_d` (with utility `U_a(c_d)`). If the full-insurance allocation of (a) has
`c_a > c_d` (as when `U_a'(c_a) = U_d'(c_d)` implies `c_a > c_d`) and `U_a` is increasing, it is
incentive compatible; being optimal among all feasible allocations it is optimal among the
incentive-compatible zero-profit contracts, i.e. it is the competitive equilibrium. -/
theorem exercise_19_F_5b {Ua Ud : ℝ → ℝ} (hma : StrictMonoOn Ua (Set.Ici 0)) {ca cd : ℝ}
    (hcd0 : 0 ≤ cd) (hgt : cd < ca) (hopt : ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ ca + cd →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd) :
    Ua cd < Ua ca ∧ ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ ca + cd → Ua yd ≤ Ua ya →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd :=
  ⟨hma (Set.mem_Ici.mpr hcd0) (Set.mem_Ici.mpr (hcd0.trans hgt.le)) hgt,
    fun ya yd hya hyd hy _ => hopt ya yd hya hyd hy⟩

/-- **Exercise 19.F.5(c)** (MWG, pp. 728-729). If the allocation of (a) has `c_a < c_d`, it is not
incentive compatible (an able worker prefers to claim disability), so it is not reachable. If at
equal consumption the disabled have the higher marginal utility (`U_a'(k/2) ≤ U_d'(k/2)`, the
counterpart of "`U_a'(c_a) = U_d'(c_d)` implies `c_a < c_d`"), the best allocation subject to
feasibility and incentive compatibility (`c_a ≥ c_d`) is `c_a = c_d = k/2`: this is the competitive
equilibrium, and it is optimal relative to everything a government that cannot observe disability
can achieve (the same constraints). -/
theorem exercise_19_F_5c {Ua Ud : ℝ → ℝ} (hma : StrictMonoOn Ua (Set.Ici 0))
    (hca : StrictConcaveOn ℝ (Set.Ici 0) Ua) (hcd : StrictConcaveOn ℝ (Set.Ici 0) Ud)
    {k A D : ℝ} (hk : 0 ≤ k) (hA : HasDerivAt Ua A (k / 2)) (hD : HasDerivAt Ud D (k / 2))
    (hA0 : 0 ≤ A) (hAD : A ≤ D) {ca cd : ℝ} (hca0 : 0 ≤ ca) (hlt : ca < cd) :
    Ua ca < Ua cd ∧ ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ k → yd ≤ ya →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud (k / 2) (k / 2) := by
  refine ⟨hma (Set.mem_Ici.mpr hca0) (Set.mem_Ici.mpr (hca0.trans hlt.le)) hlt,
    fun ya yd hya hyd hy hic => ?_⟩
  have hk2 : (0 : ℝ) ≤ k / 2 := by linarith
  have h1 := strictConcave_tangent hca (Set.mem_Ici.mpr hk2) (Set.mem_Ici.mpr hya) hA
  have h2 := strictConcave_tangent hcd (Set.mem_Ici.mpr hk2) (Set.mem_Ici.mpr hyd) hD
  have hbr : A * (ya - k / 2) + D * (yd - k / 2) ≤ 0 := by
    rcases le_or_gt (k / 2) ya with ht | ht
    · nlinarith
    · nlinarith
  unfold welfare19F5
  linarith

/-! ## Exercise 19.H.6 -/

/-- Consumer 1's expected utility `∑_s ⅓ (x_{1s} + x_{2s})` (three equally likely states). -/
noncomputable def U1_19H6 (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * (x s 0 + x s 1)

/-- Consumer 2's expected utility `∑_s ⅓ (√x_{1s} + x_{2s})`. -/
noncomputable def U2_19H6 (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * (√(x s 0) + x s 1)

/-- Endowments: consumer 1 has `ω₂₁` of good 2 in every state; consumer 2 has `w_s` of good 1. -/
def omega19H6 (w21 : ℝ) (w : Fin 3 → ℝ) : Fin 2 → CVec 3 2 :=
  ![fun _ => ![0, w21], fun s => ![w s, 0]]

/-- The Arrow-Debreu allocation of Exercise 19.H.6(a). -/
noncomputable def x19H6 (w21 : ℝ) (w : Fin 3 → ℝ) : Fin 2 → CVec 3 2 :=
  ![fun s => ![w s - 1 / 4, w21 - w s + 1 / 4], fun s => ![1 / 4, w s - 1 / 4]]

theorem sqrt_le_add_quarter (t : ℝ) (ht : 0 ≤ t) : √t ≤ t + 1 / 4 := by
  nlinarith [Real.sq_sqrt ht, sq_nonneg (√t - 1 / 2)]

/-- **Exercise 19.H.6(a)** (MWG, p. 730). With interior parameters (`w_s ≥ 1/4`,
`ω₂₁ ≥ w_s - 1/4`), all contingent prices equal (`1/3`) and the allocation in which consumer 2
consumes `1/4` of good 1 in every state form an Arrow-Debreu equilibrium. -/
theorem exercise_19_H_6a {w21 : ℝ} {w : Fin 3 → ℝ} (hw : ∀ s, 1 / 4 ≤ w s)
    (hw21 : ∀ s, w s - 1 / 4 ≤ w21) :
    IsADEqmU ![U1_19H6, U2_19H6] (omega19H6 w21 w) (x19H6 w21 w) (fun _ _ => 1 / 3) := by
  have hcv : ∀ y : CVec 3 2, cval (fun _ _ => 1 / 3) y = ∑ s, (1 / 3) * (y s 0 + y s 1) := by
    intro y; simp [cval, dotProduct, Fin.sum_univ_two, mul_add]
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hw1 : cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1) = ∑ s, (1 / 3) * w s := by
    rw [hcv]; simp [omega19H6]
  have hx1 : cval (fun _ _ => 1 / 3) (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s := by
    rw [hcv]; simp [x19H6]
  have hw0 : cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0) = w21 := by
    rw [hcv]; simp [omega19H6]
  have hx0 : cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) = w21 := by
    rw [hcv]; simp [x19H6]
  have c0 : (NonnegC (x19H6 w21 w 0) ∧ cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) ≤
      cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0)) ∧ ∀ x', NonnegC x' →
        cval (fun _ _ => 1 / 3) x' ≤ cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0) →
          U1_19H6 x' ≤ U1_19H6 (x19H6 w21 w 0) := by
    refine ⟨⟨fun s l => ?_, by rw [hx0, hw0]⟩, fun x' _ hb => ?_⟩
    · fin_cases l <;> simp [x19H6] <;> linarith [hw s, hw21 s]
    · rw [hw0, hcv] at hb
      have : U1_19H6 (x19H6 w21 w 0) = cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) := by
        rw [hcv]; rfl
      rw [this, hx0]; exact hb
  have c1 : (NonnegC (x19H6 w21 w 1) ∧ cval (fun _ _ => 1 / 3) (x19H6 w21 w 1) ≤
      cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1)) ∧ ∀ x', NonnegC x' →
        cval (fun _ _ => 1 / 3) x' ≤ cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1) →
          U2_19H6 x' ≤ U2_19H6 (x19H6 w21 w 1) := by
    refine ⟨⟨fun s l => ?_, by rw [hx1, hw1]⟩, fun x' hx' hb => ?_⟩
    · fin_cases l
      · simp [x19H6]
      · change (0 : ℝ) ≤ w s - 1 / 4; linarith [hw s]
    · rw [hw1, hcv] at hb
      have hval : U2_19H6 (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s + 1 / 4 := by
        simp only [U2_19H6, x19H6, Matrix.cons_val_one, Matrix.cons_val_zero, hq,
          Fin.sum_univ_three]
        ring
      have h2 : U2_19H6 x' ≤ ∑ s, (1 / 3) * (x' s 0 + x' s 1) + 1 / 4 := by
        calc U2_19H6 x' ≤ ∑ s, ((1 / 3) * (x' s 0 + x' s 1) + 1 / 12) :=
              Finset.sum_le_sum fun s _ => by
                nlinarith [sqrt_le_add_quarter (x' s 0) (hx' s 0)]
          _ = ∑ s, (1 / 3) * (x' s 0 + x' s 1) + 1 / 4 := by
              norm_num [Finset.sum_add_distrib]
      rw [hval]; linarith
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact c0
    · exact c1
  · funext s l
    fin_cases l <;> simp [x19H6, omega19H6, Fin.sum_univ_two]

/-- **Exercise 19.H.6(e)** (MWG, p. 730), the surplus comparison. For any allocation that uses up
the endowments, `U₁ + U₂ = ∑_s ⅓ (w_s + ω₂₁) + ∑_s ⅓ (√y_s - y_s)` where `y_s` is consumer 2's
good-1 consumption: it is at most the value at the Arrow-Debreu allocation, with equality iff
`y_s = 1/4` in every state. -/
theorem exercise_19_H_6_surplus {w21 : ℝ} {w : Fin 3 → ℝ} {x : Fin 2 → CVec 3 2}
    (hx : ∑ i, x i = ∑ i, omega19H6 w21 w i) (hy : ∀ s, 0 ≤ x 1 s 0) :
    U1_19H6 (x 0) + U2_19H6 (x 1) ≤
        U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) ∧
      (U1_19H6 (x 0) + U2_19H6 (x 1) = U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) →
        ∀ s, x 1 s 0 = 1 / 4) := by
  have hc : ∀ s l, x 0 s l + x 1 s l = omega19H6 w21 w 0 s l + omega19H6 w21 w 1 s l := by
    intro s l
    have := congrFun (congrFun hx s) l
    simpa [Fin.sum_univ_two] using this
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have key : U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) -
      (U1_19H6 (x 0) + U2_19H6 (x 1)) = ∑ s, (1 / 3) * (√(x 1 s 0) - 1 / 2) ^ 2 := by
    unfold U1_19H6 U2_19H6
    simp only [x19H6, Matrix.cons_val_zero, Matrix.cons_val_one, hq, Fin.sum_univ_three]
    have h0 := hc 0 0; have h1 := hc 0 1; have h2 := hc 1 0; have h3 := hc 1 1
    have h4 := hc 2 0; have h5 := hc 2 1
    simp [omega19H6] at h0 h1 h2 h3 h4 h5
    nlinarith [Real.sq_sqrt (hy 0), Real.sq_sqrt (hy 1), Real.sq_sqrt (hy 2)]
  have hnn : 0 ≤ ∑ s, (1 / 3 : ℝ) * (√(x 1 s 0) - 1 / 2) ^ 2 :=
    Finset.sum_nonneg fun s _ => by positivity
  refine ⟨by linarith, fun heq s => ?_⟩
  have hz : ∑ s, (1 / 3 : ℝ) * (√(x 1 s 0) - 1 / 2) ^ 2 = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => by positivity).mp hz s (Finset.mem_univ s)
  have hs : √(x 1 s 0) = 1 / 2 := by nlinarith [sq_nonneg (√(x 1 s 0) - 1 / 2)]
  have := Real.sq_sqrt (hy s)
  rw [hs] at this
  linarith

/-- **Exercise 19.H.6(b)-(c)** (MWG, p. 730). An allocation in which consumer 2's consumption of
good 1 is not `1/4` in some state (as with non-contingent trade when `w_s` varies, `y_s = w_s + z`)
is not Pareto optimal (when the compensating reallocation keeps consumption nonnegative): giving
consumer 2 `1/4` of good 1 and compensating him in good 2 makes consumer 1 strictly better off. -/
theorem exercise_19_H_6_not_po {w21 : ℝ} {w : Fin 3 → ℝ} {x : Fin 2 → CVec 3 2}
    (hpo : IsParetoOptimalU ![U1_19H6, U2_19H6] (omega19H6 w21 w) x) {s₀ : Fin 3}
    (hne : x 1 s₀ 0 ≠ 1 / 4)
    (hnn : ∀ s, 0 ≤ x 1 s 1 + √(x 1 s 0) - 1 / 2 ∧ 0 ≤ x 0 s 1 - √(x 1 s 0) + 1 / 2 ∧
      1 / 4 ≤ x 0 s 0 + x 1 s 0) : False := by
  obtain ⟨⟨hx, hf⟩, hno⟩ := hpo
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  set x' : Fin 2 → CVec 3 2 :=
    ![fun s => ![x 0 s 0 + x 1 s 0 - 1 / 4, x 0 s 1 - √(x 1 s 0) + 1 / 2],
      fun s => ![1 / 4, x 1 s 1 + √(x 1 s 0) - 1 / 2]] with hx'
  have hsq : √(x 1 s₀ 0) ≠ 1 / 2 := by
    intro h
    have := Real.sq_sqrt (hx 1 s₀ 0)
    rw [h] at this; apply hne; linarith
  refine hno ⟨x', ⟨fun i s l => ?_, fun s l => ?_⟩, fun i => ?_, 0, ?_⟩
  · fin_cases i <;> fin_cases l <;> simp [hx'] <;> linarith [hnn s, hx 0 s 0, hx 1 s 0]
  · have := hf s l
    fin_cases l <;> simp [hx', Fin.sum_univ_two] at this ⊢ <;> linarith
  · fin_cases i
    · change U1_19H6 (x 0) ≤ U1_19H6 (x' 0)
      unfold U1_19H6
      refine Finset.sum_le_sum fun s _ => ?_
      simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (hx 1 s 0), sq_nonneg (√(x 1 s 0) - 1 / 2)]
    · change U2_19H6 (x 1) ≤ U2_19H6 (x' 1)
      unfold U2_19H6
      refine le_of_eq (Finset.sum_congr rfl fun s _ => ?_)
      simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one, hq]
      ring
  · change U1_19H6 (x 0) < U1_19H6 (x' 0)
    unfold U1_19H6
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, Finset.mem_univ _, ?_⟩
    · simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (hx 1 s 0), sq_nonneg (√(x 1 s 0) - 1 / 2)]
    · simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      have hpos : 0 < (√(x 1 s₀ 0) - 1 / 2) ^ 2 := by
        have : √(x 1 s₀ 0) - 1 / 2 ≠ 0 := sub_ne_zero.mpr hsq
        positivity
      nlinarith [Real.sq_sqrt (hx 1 s₀ 0)]

end MWG.EquilibriumUncertainty
