/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.RobinsonCrusoe
import MWGGeneralEquilibriumExamples.Blair
import MWGGeneralEquilibriumExamples.CobbDouglasBox

/-!
# Exercises 15.C.1(b) and 15.C.2 (MWG p. 542)

* `rc_budget_eq`: the budget set of (15.C.2) is the Walrasian budget set at prices `(w, p)` and
  wealth `w L̄ + π`.
* `sqrt_firm_profit`: profit maximization for the firm with `f(z) = √z`.
* **Exercise 15.C.2** (`exercise_15_C_2`): with `f(z) = z^{1/2}`, `u = ln x₁ + ln x₂`
  (represented by `x₁^{1/2}x₂^{1/2}`, which ranks bundles of `ℝ²₊₊` identically and gives the
  boundary the lowest value, as `ln 0 = -∞` does) and `L̄ = 1`, the equilibria are `w/p = √3/2`
  with `x = (2/3, √3/3)`, `z = 1/3`, `q = √3/3` and profits `π = p√3/6`.
* **Exercise 15.C.1(b)**: at an equilibrium the slope of the excess demand for labor is the
  compensated (Slutsky) own-price effect on leisure plus the slope of the firm's labor demand, hence
  nonpositive (`exercise_15_C_1b`, with an instance from Exercise 15.C.2); and the slope need not
  have one sign globally (`exercise_15_C_1b_not_monotone`, a CES consumer with `f = √z`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The budget set (15.C.2) is the Walrasian budget set at prices `(w, p)` and wealth `w L̄ + π`. -/
theorem rc_budget_eq (E : RCEconomy) (p w π₀ : ℝ) :
    E.budget p w π₀ = budgetSet ![w, p] (w * E.Lbar + π₀) := by
  ext x
  simp only [RCEconomy.budget, budgetSet, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- The consumer's problem (15.C.2) is Chapter 3's utility maximization problem at prices `(w, p)`
and wealth `w L̄ + π`. -/
theorem rc_consumerOpt_iff (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) :
    E.IsConsumerOpt p w π₀ x ↔ x ∈ walrasianDemand E.u ![w, p] (w * E.Lbar + π₀) := by
  unfold RCEconomy.IsConsumerOpt
  rw [rc_budget_eq]
  rfl

/-- The firm with `f(z) = √z`: for `p, w > 0`, `p√z - wz ≤ p²/(4w)` on `z ≥ 0`, with equality
exactly at `z = p²/(4w²)`. -/
theorem sqrt_firm_profit {p w : ℝ} (hp : 0 < p) (hw : 0 < w) {z : ℝ} (hz : 0 ≤ z) :
    p * Real.sqrt z - w * z ≤ p ^ 2 / (4 * w) ∧
      (p * Real.sqrt z - w * z = p ^ 2 / (4 * w) ↔ z = p ^ 2 / (4 * w ^ 2)) := by
  have hs := Real.sq_sqrt hz
  have key : p * Real.sqrt z - w * z = p ^ 2 / (4 * w) - w * (Real.sqrt z - p / (2 * w)) ^ 2 := by
    field_simp
    linear_combination 16 * w ^ 2 * hs
  rw [key]
  have hsq : 0 ≤ w * (Real.sqrt z - p / (2 * w)) ^ 2 := by positivity
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : w * (Real.sqrt z - p / (2 * w)) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · have h1 : Real.sqrt z = p / (2 * w) := by nlinarith [sq_nonneg (Real.sqrt z - p / (2 * w))]
      rw [← hs, h1]
      field_simp
      ring
  · have h1 : Real.sqrt z = p / (2 * w) := by
      rw [h, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le,
        show (4 : ℝ) * w ^ 2 = (2 * w) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h1]
    ring

/-- **Exercise 15.C.2** (MWG, p. 542). The economy: `u = x₁^{1/2}x₂^{1/2}` (representing
`ln x₁ + ln x₂`), `L̄ = 1`, `f(z) = z^{1/2}`. -/
noncomputable def ex15C2Economy : RCEconomy where
  u := cobbDouglasUtility 1 (1 / 2)
  Lbar := 1
  f := Real.sqrt

/-- **Exercise 15.C.2** (MWG, p. 542). The Walrasian equilibria are exactly: `p > 0`,
`w = (√3/2) p`, consumption `x = (2/3, √3/3)`, labor `z = 1/3`; output is `q = √3/3` and profits
are `π = p √3/6`. -/
theorem exercise_15_C_2 (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) :
    ex15C2Economy.IsWalrasEqm p w x z ↔
      0 < p ∧ w = Real.sqrt 3 / 2 * p ∧ x = ![2 / 3, Real.sqrt 3 / 3] ∧ z = 1 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq13 : Real.sqrt (1 / 3) = Real.sqrt 3 / 3 := by
    rw [show (1 / 3 : ℝ) = (Real.sqrt 3 / 3) ^ 2 by rw [div_pow, h3]; norm_num,
      Real.sqrt_sq (by positivity)]
  constructor
  · rintro ⟨hz, hx, hx1, hzx⟩
    have hπ0 : 0 ≤ p * ex15C2Economy.f z - w * z := by
      have := hz.2 0 le_rfl
      simpa [ex15C2Economy] using this
    rw [rc_consumerOpt_iff] at hx
    -- `p > 0`: otherwise the consumption good is free
    have hp : 0 < p := by
      by_contra hp
      rw [not_lt] at hp
      have hb : (![1, 0] : Fin 2 → ℝ) ∈ budgetSet ![w, p]
          (w * ex15C2Economy.Lbar + (p * ex15C2Economy.f z - w * z)) :=
        ⟨fun l => by fin_cases l <;> norm_num, by
          simp only [ex15C2Economy] at hπ0
          simp [dotProduct, Fin.sum_univ_two, ex15C2Economy]; linarith⟩
      have := cd_no_demand_1 (α := 1 / 2) (by norm_num) (by norm_num)
        (p := ![w, p]) (by simpa using hp) hb (by simp)
      have hx' : x ∈ walrasianDemand (cobbDouglasUtility 1 (1 / 2)) ![w, p]
          (w * ex15C2Economy.Lbar + (p * ex15C2Economy.f z - w * z)) := hx
      rw [this] at hx'
      exact hx'
    -- `w > 0`: otherwise profits are unbounded
    have hw : 0 < w := by
      by_contra hw
      rw [not_lt] at hw
      set s := (|p * Real.sqrt z - w * z| + 1) / p with hs
      have hs0 : 0 ≤ s := by positivity
      have h := hz.2 (s ^ 2) (sq_nonneg s)
      simp only [ex15C2Economy, Real.sqrt_sq hs0] at h
      have : p * s = |p * Real.sqrt z - w * z| + 1 := by rw [hs]; field_simp
      nlinarith [le_abs_self (p * Real.sqrt z - w * z), sq_nonneg s]
    -- the firm's demand for labor
    have hzval : z = p ^ 2 / (4 * w ^ 2) := by
      have h1 := (sqrt_firm_profit hp hw hz.1).1
      have h2 := hz.2 (p ^ 2 / (4 * w ^ 2)) (by positivity)
      have h3' := ((sqrt_firm_profit hp hw (by positivity : (0 : ℝ) ≤ p ^ 2 / (4 * w ^ 2))).2).2
        rfl
      simp only [ex15C2Economy] at h2
      exact ((sqrt_firm_profit hp hw hz.1).2).1 (le_antisymm h1 (by linarith))
    have hsz : Real.sqrt z = p / (2 * w) := by
      rw [hzval, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le,
        show (4 : ℝ) * w ^ 2 = (2 * w) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hπ : p * ex15C2Economy.f z - w * z = p ^ 2 / (4 * w) := by
      simp only [ex15C2Economy]
      rw [hsz, hzval]
      field_simp
      ring
    -- the consumer's Cobb-Douglas demand
    have hpp : StrictlyPositive ![w, p] := fun l => by fin_cases l; exacts [hw, hp]
    have hm : 0 ≤ w * ex15C2Economy.Lbar + p ^ 2 / (4 * w) := by
      simp only [ex15C2Economy]; positivity
    rw [hπ] at hx
    have hx' : x ∈ walrasianDemand (cobbDouglasUtility 1 (1 / 2)) ![w, p]
        (w * ex15C2Economy.Lbar + p ^ 2 / (4 * w)) := hx
    rw [example_3_D_1 one_pos (by norm_num) (by norm_num) hpp hm, Set.mem_singleton_iff] at hx'
    have ex0 : x 0 = 1 / 2 * (w + p ^ 2 / (4 * w)) / w := by
      rw [hx']; simp [cobbDouglasDemand, ex15C2Economy]
    have ex1 : x 1 = (1 - 1 / 2) * (w + p ^ 2 / (4 * w)) / p := by
      rw [hx']; simp [cobbDouglasDemand, ex15C2Economy]
    -- goods-market clearing gives `w² = (3/4) p²`
    have hx1' : x 1 = Real.sqrt z := hx1
    rw [ex1, hsz] at hx1'
    have hw2 : w ^ 2 = 3 / 4 * p ^ 2 := by
      field_simp at hx1'
      nlinarith
    have hwv : w = Real.sqrt 3 / 2 * p := by
      have : (w - Real.sqrt 3 / 2 * p) * (w + Real.sqrt 3 / 2 * p) = 0 := by nlinarith [h3]
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · nlinarith [mul_pos h3pos hp]
    refine ⟨hp, hwv, ?_, ?_⟩
    · funext l
      fin_cases l
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        rw [ex0, hwv]
        field_simp
        nlinarith [h3]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [ex1, hwv]
        field_simp
        nlinarith [h3]
    · rw [hzval, hwv]
      field_simp
      nlinarith [h3]
  · rintro ⟨hp, hwv, rfl, rfl⟩
    have hw : 0 < w := by rw [hwv]; positivity
    have hzval : (1 / 3 : ℝ) = p ^ 2 / (4 * w ^ 2) := by
      rw [hwv]; field_simp; nlinarith [h3]
    have hfirm : ∀ z', 0 ≤ z' → p * Real.sqrt z' - w * z' ≤
        p * Real.sqrt (1 / 3) - w * (1 / 3) := by
      intro z' hz'
      have h1 := (sqrt_firm_profit hp hw hz').1
      have h2 := ((sqrt_firm_profit hp hw (by norm_num : (0 : ℝ) ≤ 1 / 3)).2).2 hzval
      linarith
    have hπ : p * Real.sqrt (1 / 3) - w * (1 / 3) = p ^ 2 / (4 * w) :=
      ((sqrt_firm_profit hp hw (by norm_num : (0 : ℝ) ≤ 1 / 3)).2).2 hzval
    refine ⟨⟨by norm_num, fun z' hz' => hfirm z' hz'⟩, ?_, ?_, by norm_num [ex15C2Economy]⟩
    · rw [rc_consumerOpt_iff]
      have hpp : StrictlyPositive ![w, p] := fun l => by fin_cases l; exacts [hw, hp]
      simp only [ex15C2Economy] at hπ ⊢
      rw [hπ, example_3_D_1 one_pos (by norm_num) (by norm_num) hpp (by positivity),
        Set.mem_singleton_iff]
      funext l
      fin_cases l
      · simp only [cobbDouglasDemand, Fin.zero_eta, Matrix.cons_val_zero]
        rw [hwv]
        field_simp
        nlinarith [h3]
      · simp only [cobbDouglasDemand, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hwv]
        field_simp
        nlinarith [h3]
    · simp only [ex15C2Economy, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hsq13]

/-- **Exercise 15.C.1(b)** (MWG, p. 542). Fix `p = 1`. Let `x₁(w, m)` be the leisure demand,
differentiable at `(w, wL̄ + π(w))` with partial derivatives `∂x₁/∂w = L'(1,0)`,
`∂x₁/∂m = L'(0,1)`; let the profit function satisfy Hotelling's lemma `π'(w) = -ℓ(w)` and let the
labor demand `ℓ` have derivative `ℓ'`. At an equilibrium wage (`ℓ(w) = L̄ - x₁`), the excess demand
for labor `x₁(w, wL̄ + π(w)) + ℓ(w) - L̄` has derivative `s₁₁ + ℓ'(w)`, where
`s₁₁ = ∂x₁/∂w + x₁ ∂x₁/∂m` is the compensated (Slutsky) own-price effect on leisure. -/
theorem exercise_15_C_1b {x₁ : ℝ × ℝ → ℝ} {L' : ℝ × ℝ →L[ℝ] ℝ} {ℓ π₀ : ℝ → ℝ} {Lbar w ℓ' : ℝ}
    (hx : HasFDerivAt x₁ L' (w, w * Lbar + π₀ w)) (hπ : HasDerivAt π₀ (-ℓ w) w)
    (hℓ : HasDerivAt ℓ ℓ' w) (heq : ℓ w = Lbar - x₁ (w, w * Lbar + π₀ w)) :
    HasDerivAt (fun v => x₁ (v, v * Lbar + π₀ v) + ℓ v - Lbar)
      ((L' (1, 0) + x₁ (w, w * Lbar + π₀ w) * L' (0, 1)) + ℓ') w := by
  have hg : HasDerivAt (fun v : ℝ => (v, v * Lbar + π₀ v)) (1, Lbar + -ℓ w) w :=
    (hasDerivAt_id w).prodMk (((hasDerivAt_id w).mul_const Lbar).add hπ |>.congr_deriv
      (by simp))
  have hc := hx.comp_hasDerivAt w hg
  have hL : L' (1, Lbar + -ℓ w) = L' (1, 0) + x₁ (w, w * Lbar + π₀ w) * L' (0, 1) := by
    have e : ((1 : ℝ), Lbar + -ℓ w) = ((1 : ℝ), (0 : ℝ)) +
        x₁ (w, w * Lbar + π₀ w) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp [heq]
    rw [e, map_add, map_smul, smul_eq_mul]
  rw [hL] at hc
  exact (hc.add hℓ).sub_const Lbar

/-- **Exercise 15.C.1(b)** (MWG, p. 542). Consequently, if the compensated own-price effect on
leisure is `≤ 0` (Chapter 3, negative semidefiniteness of the Slutsky matrix) and labor demand is
nonincreasing, the excess demand for labor has nonpositive slope at the equilibrium, and negative
slope if labor demand is strictly decreasing there. -/
theorem exercise_15_C_1b_sign {s ℓ' : ℝ} (hs : s ≤ 0) (hℓ : ℓ' ≤ 0) :
    s + ℓ' ≤ 0 ∧ (ℓ' < 0 → s + ℓ' < 0) :=
  ⟨by linarith, fun h => by linarith⟩

/-- **Exercise 15.C.1(b)** (MWG, p. 542), an instance (the economy of Exercise 15.C.2 with `p = 1`):
leisure demand `x₁(w, m) = m/(2w)`, labor demand `ℓ(w) = 1/(4w²)`, profits `π(w) = 1/(4w)`. At the
equilibrium wage `w* = √3/2` the hypotheses of `exercise_15_C_1b` hold and the slope of the excess
demand for labor, `s₁₁ + ℓ'(w*) = -(w* + π(w*))/(4w*²) - 1/(2w*³)`, is negative. -/
theorem exercise_15_C_1b_instance :
    let w := Real.sqrt 3 / 2
    let x₁ : ℝ × ℝ → ℝ := fun q => q.2 / (2 * q.1)
    let ℓ : ℝ → ℝ := fun v => 1 / (4 * v ^ 2)
    let π₀ : ℝ → ℝ := fun v => 1 / (4 * v)
    ∃ L' : ℝ × ℝ →L[ℝ] ℝ, ∃ ℓ' : ℝ, HasFDerivAt x₁ L' (w, w * 1 + π₀ w) ∧
      HasDerivAt π₀ (-ℓ w) w ∧ HasDerivAt ℓ ℓ' w ∧ ℓ w = 1 - x₁ (w, w * 1 + π₀ w) ∧
      L' (1, 0) + x₁ (w, w * 1 + π₀ w) * L' (0, 1) < 0 ∧ ℓ' < 0 := by
  intro w x₁ ℓ π₀
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hw : 0 < w := by positivity
  have hw2 : w ^ 2 = 3 / 4 := by simp only [w]; rw [div_pow, h3]; norm_num
  set m := w * 1 + π₀ w with hm
  have hm0 : 0 < m := by simp only [hm, π₀]; positivity
  -- the derivative of `x₁(q) = q₂/(2q₁)`
  have hd : HasFDerivAt x₁ ((1 / (2 * w)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
      (m / (2 * w ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (w, m) := by
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (w, m) :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => (2 * q.1)⁻¹)
        (-(1 / (2 * w ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (w, m) := by
      have := (hasDerivAt_inv (by positivity : (2 * w) ≠ 0)).comp_hasFDerivAt (w, m)
        ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (w, m))).const_mul 2)
      convert this using 1
      · rfl
      · rw [smul_smul]
        congr 1
        field_simp
    have := h1.mul h2
    convert this using 1
    · funext q
      simp [x₁, div_eq_mul_inv]
    · ext <;> first | (simp; done) | (simp; field_simp)
  refine ⟨_, -(1 / (2 * w ^ 3)), hd, ?_, ?_, ?_, ?_, by
    have : 0 < 1 / (2 * w ^ 3) := by positivity
    linarith⟩
  · have := (hasDerivAt_inv (by positivity : (4 * w) ≠ 0)).comp w
      ((hasDerivAt_id w).const_mul 4)
    convert this using 1
    · funext v; simp [π₀]
    · simp [ℓ]; field_simp
  · have := (hasDerivAt_inv (by positivity : (4 * w ^ 2) ≠ 0)).comp w
      (((hasDerivAt_id w).pow 2).const_mul 4)
    convert this using 1
    · funext v; simp [ℓ]
    · simp; field_simp; ring
  · simp only [ℓ, x₁, hm, π₀]
    field_simp
    nlinarith [hw2]
  · simp only [x₁, one_div, mul_inv_rev, sub_apply, smul_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul, mul_zero, ContinuousLinearMap.coe_fst', mul_one, zero_sub, sub_zero,
      neg_add_lt_iff_lt_add, add_zero]
    have e : m / (2 * w) * (w⁻¹ * 2⁻¹) = m / (4 * w ^ 2) := by field_simp; ring
    rw [e]
    have : m / (4 * w ^ 2) < m / (2 * w ^ 2) :=
      div_lt_div_of_pos_left hm0 (by positivity) (by nlinarith [pow_pos hw 2])
    exact this

/-- The economy of `exercise_15_C_1b_not_monotone`: the CES consumer
`u = (x₁⁻² + x₂⁻²)^{-1/2}`, `L̄ = 1`, `f(z) = √z`. -/
noncomputable def ces15C1Economy : RCEconomy where
  u := cesNeg2 1 1
  Lbar := 1
  f := Real.sqrt

/-- Leisure demanded by the CES consumer at `p = 1`, wage `w = c³` and profit income
`π = 1/(4w)`: `(w + 1/(4w))/(w + c)`. -/
noncomputable def cesLeisure (c : ℝ) : ℝ := (c ^ 3 + 1 / (4 * c ^ 3)) / (c ^ 3 + c)

/-- In `ces15C1Economy`, at `p = 1` and wage `w = c³` (`c > 0`): the firm's unique profit maximizing
labor input is `1/(4w²)`, with profit `1/(4w)`, and the consumer's unique optimum (with that
profit income) is `(ℓ, cℓ)`, `ℓ = cesLeisure c`. -/
theorem ces15C1_demands {c : ℝ} (hc : 0 < c) :
    (∀ z, ces15C1Economy.IsProfitMax 1 (c ^ 3) z ↔ z = 1 / (4 * (c ^ 3) ^ 2)) ∧
      1 * Real.sqrt (1 / (4 * (c ^ 3) ^ 2)) - c ^ 3 * (1 / (4 * (c ^ 3) ^ 2)) = 1 / (4 * c ^ 3) ∧
      ∀ x, ces15C1Economy.IsConsumerOpt 1 (c ^ 3) (1 / (4 * c ^ 3)) x ↔
        x = ![cesLeisure c, c * cesLeisure c] := by
  have hw : 0 < c ^ 3 := by positivity
  have hz0 : (1 : ℝ) / (4 * (c ^ 3) ^ 2) = 1 ^ 2 / (4 * (c ^ 3) ^ 2) := by ring
  have hprof : 1 * Real.sqrt (1 / (4 * (c ^ 3) ^ 2)) - c ^ 3 * (1 / (4 * (c ^ 3) ^ 2)) =
      1 / (4 * c ^ 3) := by
    have := ((sqrt_firm_profit one_pos hw (by positivity : (0 : ℝ) ≤ 1 / (4 * (c ^ 3) ^ 2))).2).2
      hz0
    rw [this]
    ring
  refine ⟨fun z => ⟨fun h => ?_, fun h => ?_⟩, hprof, fun x => ?_⟩
  · have h1 := (sqrt_firm_profit one_pos hw h.1).1
    have h2 := h.2 (1 / (4 * (c ^ 3) ^ 2)) (by positivity)
    simp only [ces15C1Economy] at h2
    rw [hprof] at h2
    rw [hz0]
    exact ((sqrt_firm_profit one_pos hw h.1).2).1 (le_antisymm h1 (by
      have : (1 : ℝ) ^ 2 / (4 * c ^ 3) = 1 / (4 * c ^ 3) := by ring
      linarith))
  · refine ⟨by rw [h]; positivity, fun z' hz' => ?_⟩
    simp only [ces15C1Economy]
    rw [h, hprof]
    have := (sqrt_firm_profit one_pos hw hz').1
    have e : (1 : ℝ) ^ 2 / (4 * c ^ 3) = 1 / (4 * c ^ 3) := by ring
    linarith
  · rw [rc_consumerOpt_iff]
    have hl0 : 0 < cesLeisure c := by unfold cesLeisure; positivity
    have hp : StrictlyPositive ![c ^ 3, (1 : ℝ)] := fun l => by
      fin_cases l
      · exact hw
      · exact one_pos
    have hdem := cesNeg2_demand one_pos one_pos hp (x := ![cesLeisure c, c * cesLeisure c])
      (by simpa using hl0) (by simpa using mul_pos hc hl0) (by simp; ring)
    have hwealth : (![c ^ 3, (1 : ℝ)] : Fin 2 → ℝ) ⬝ᵥ ![cesLeisure c, c * cesLeisure c] =
        c ^ 3 * ces15C1Economy.Lbar + 1 / (4 * c ^ 3) := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ces15C1Economy, cesLeisure]
      field_simp
    rw [hwealth] at hdem
    change x ∈ walrasianDemand (cesNeg2 1 1) _ _ ↔ _
    rw [hdem, Set.mem_singleton_iff]

/-- **Exercise 15.C.1(b)** (MWG, p. 542). The slope of the excess demand for labor
`z(w) = x₁(w, w + π(w)) + ℓ(w) - 1` is not of one sign over all wages: in `ces15C1Economy`,
`z(1/8) = 92/5 > z(1) = -1/8` (falling) but `z(8) = -247/1280 < z(27)` (rising). -/
theorem exercise_15_C_1b_not_monotone :
    let z : ℝ → ℝ := fun c => cesLeisure c + 1 / (4 * (c ^ 3) ^ 2) - 1
    z 1 < z (1 / 2) ∧ z 2 < z 3 ∧ z (1 / 2) = 92 / 5 ∧ z 1 = -1 / 8 ∧ z 2 = -247 / 1280 := by
  intro z
  simp only [z, cesLeisure]
  norm_num

/-- **Footnote 8** (MWG, p. 529). If identical consumers have an indirect utility of wealth `v` that
is concave, and the social welfare function `W` is concave, nondecreasing and symmetric (invariant
under permutations of the consumers), then the equal distribution of a given aggregate wealth
maximizes social welfare: `W(v(m₁), …, v(mₙ)) ≤ W(v(M/n), …, v(M/n))`, `M = ∑ mᵢ`. -/
theorem footnote_8 {n : ℕ} [NeZero n] {W : (Fin n → ℝ) → ℝ} {v : ℝ → ℝ}
    (hW : ConcaveOn ℝ Set.univ W) (hsym : ∀ (σ : Equiv.Perm (Fin n)) (a : Fin n → ℝ),
      W (a ∘ σ) = W a) (hmono : Monotone W) (hv : ConcaveOn ℝ Set.univ v) (m : Fin n → ℝ) :
    W (fun i => v (m i)) ≤ W (fun _ => v ((∑ i, m i) / n)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  set a : Fin n → ℝ := fun i => v (m i) with ha
  -- average over the cyclic shifts `i ↦ i + k`
  have hshift : ∀ k : Fin n, W (a ∘ (Equiv.addRight k)) = W a := fun k => hsym _ a
  have hsum : ∀ i : Fin n, ∑ k : Fin n, a (i + k) = ∑ j, a j := fun i =>
    Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun k => rfl)
  have hJ := hW.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ) / n)
    (p := fun k : Fin n => a ∘ (Equiv.addRight k)) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]) (fun _ _ => Set.mem_univ _)
  have hlhs : ∑ k : Fin n, ((1 : ℝ) / n) • W (a ∘ (Equiv.addRight k)) = W a := by
    simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      smul_eq_mul]
    field_simp
  have hrhs : ∑ k : Fin n, ((1 : ℝ) / n) • (a ∘ (Equiv.addRight k)) =
      fun _ => (∑ j, a j) / n := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Equiv.coe_addRight,
      smul_eq_mul, ← Finset.mul_sum, hsum i]
    ring
  rw [hlhs, hrhs] at hJ
  -- Jensen for `v`: the mean utility is at most the utility of the mean wealth
  have hv' := hv.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ) / n)
    (p := m) (fun _ _ => by positivity) (by simp [Finset.card_univ])
    (fun _ _ => Set.mem_univ _)
  have hmean : (∑ j, a j) / n ≤ v ((∑ i, m i) / n) := by
    simp only [smul_eq_mul, ← Finset.mul_sum] at hv'
    rw [ha]
    calc (∑ j, v (m j)) / n = 1 / n * ∑ i, v (m i) := by ring
      _ ≤ v (1 / n * ∑ i, m i) := hv'
      _ = v ((∑ i, m i) / n) := by ring_nf
  exact hJ.trans (hmono fun _ => hmean)

end MWG.GeneralEquilibriumExamples
