/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Tatonnement
import MWGPositiveEquilibriumTheory.IndexTwoGoods
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Tâtonnement with two goods (MWG Section 17.H, pp. 621-623)

For `L = 2` the dynamics of the relative price `r(t) = p₁(t)/p₂(t)` are one-dimensional.

* Footnote 60 (`footnote_17_60`): with homogeneity and Walras' law,
  `dr/dt = z₁(r, 1) (c₁p₂² + c₂p₁²)/p₂³`; the factor depends on the absolute price levels
  (`footnote_17_60_levels`), but its sign does not: `r(t)` increases at `t` iff
  `z₁(r(t), 1) > 0` (`tat_two_ratio_increases_iff`, p. 621).
* Property (a), p. 621-622: a regular equilibrium `r̄` with negative slope of `z₁(·, 1)` (index
  `+1`) is locally stable (`tat_two_locally_stable`), with positive slope (index `-1`) locally
  totally unstable (`tat_two_locally_totally_unstable`); in terms of the index of Definition
  17.D.2: `tat_two_stable_of_index`, `tat_two_unstable_of_index`.
* Footnote 62 for `L = 2` (`footnote_17_62_two_goods`): a unique equilibrium is globally stable,
  through Proposition 17.H.1.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {c : Fin 2 → ℝ} {z : (Fin 2 → ℝ) → Fin 2 → ℝ} {p : ℝ → Fin 2 → ℝ}

/-- `![r, 1] ≫ 0` for `r > 0`. -/
theorem ttg_vec_mem {r : ℝ} (hr : 0 < r) : (![r, 1] : Fin 2 → ℝ) ∈ posOrthant 2 := by
  intro l
  fin_cases l
  · simpa using hr
  · simp

/-- By homogeneity, `z(q) = z(q₁/q₂, 1)` for `q ≫ 0`. -/
theorem ttg_hom (hH : EDHomogeneous z) {q : Fin 2 → ℝ} (hq : q ∈ posOrthant 2) :
    z q = z ![q 0 / q 1, 1] := by
  have hq1 := hq 1
  have : q = q 1 • (![q 0 / q 1, 1] : Fin 2 → ℝ) := by
    funext l
    fin_cases l
    · simp [hq1.ne', mul_div_cancel₀]
    · simp
  conv_lhs => rw [this]
  exact hH _ (ttg_vec_mem (div_pos (hq 0) hq1)) _ hq1

/-- Walras' law with two goods: `z₂(q) = -(q₁/q₂) z₁(q)`. -/
theorem ttg_walras (hW : EDWalrasLaw z) {q : Fin 2 → ℝ} (hq : q ∈ posOrthant 2) :
    z q 1 = -(q 0 / q 1) * z q 0 := by
  have hw := hW q hq
  simp only [dotProduct, Fin.sum_univ_two] at hw
  have := (hq 1).ne'
  field_simp
  linarith

/-- The factor `k = (c₁p₂² + c₂p₁²)/p₂³` of footnote 60. -/
noncomputable def ttgFactor (c q : Fin 2 → ℝ) : ℝ := (c 0 * q 1 ^ 2 + c 1 * q 0 ^ 2) / q 1 ^ 3

theorem ttgFactor_pos (hc : ∀ l, 0 < c l) {q : Fin 2 → ℝ} (hq : q ∈ posOrthant 2) :
    0 < ttgFactor c q := by
  have := hq 0; have := hq 1; have := hc 0; have := hc 1
  unfold ttgFactor
  positivity

/-- **Footnote 60** (MWG, p. 622). Along a trajectory of (17.H.1) with two goods, homogeneity and
Walras' law give `d(p₁/p₂)/dt = z₁(p₁/p₂, 1) (c₁p₂² + c₂p₁²)/p₂³`. -/
theorem footnote_17_60 (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    (hp : IsTatPath c z p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => p s 0 / p s 1)
      (z ![p t 0 / p t 1, 1] 0 * ttgFactor c (p t)) (Ici 0) t := by
  have hq := hp.1 t ht
  have h := (tat_coord hp ht 0).div (tat_coord hp ht 1) (hq 1).ne'
  convert h using 1
  rw [ttg_walras hW hq, ← ttg_hom hH hq, ttgFactor]
  have := (hq 1).ne'
  field_simp
  ring

/-- **Footnote 60** (MWG, p. 622). The change in `p₁/p₂` depends on the absolute levels: scaling
both prices by `α > 0` divides the factor `k` by `α`. -/
theorem footnote_17_60_levels (c q : Fin 2 → ℝ) {α : ℝ} (hα : 0 < α) (hq : q 1 ≠ 0) :
    ttgFactor c (α • q) = ttgFactor c q / α := by
  simp only [ttgFactor, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **Section 17.H** (MWG, p. 621). Whatever the absolute price levels, `p₁(t)/p₂(t)` increases at
`t` (positive derivative) iff `z₁(p₁(t)/p₂(t), 1) > 0`. -/
theorem tat_two_ratio_increases_iff (hc : ∀ l, 0 < c l) {q : Fin 2 → ℝ}
    (hq : q ∈ posOrthant 2) : 0 < z ![q 0 / q 1, 1] 0 * ttgFactor c q ↔ 0 < z ![q 0 / q 1, 1] 0 :=
  mul_pos_iff_of_pos_right (ttgFactor_pos hc hq)

/-- Along a trajectory, `p₂(t)` is bounded by `√(c₂ N₀)`, so `k(t) ≥ c₁/√(c₂ N₀)`. -/
theorem ttg_factor_lower (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z) (hp : IsTatPath c z p)
    {t : ℝ} (ht : 0 ≤ t) :
    c 0 / Real.sqrt (c 1 * wNormSq c (p 0)) ≤ ttgFactor c (p t) := by
  have hq := hp.1 t ht
  have h1 : p t 1 ≤ Real.sqrt (c 1 * wNormSq c (p 0)) := by
    rw [← tat_wNormSq_const hc hW hp ht]
    refine Real.le_sqrt_of_sq_le (sq_le_wNormSq hc _ 1)
  have hq0 := hq 0
  have hq1 := hq 1
  have hc0 := hc 0
  have hc1 := hc 1
  calc c 0 / Real.sqrt (c 1 * wNormSq c (p 0)) ≤ c 0 / p t 1 :=
        div_le_div_of_nonneg_left hc0.le hq1 h1
    _ = c 0 * p t 1 ^ 2 / p t 1 ^ 3 := by field_simp
    _ ≤ ttgFactor c (p t) := by
        unfold ttgFactor
        gcongr
        nlinarith [sq_nonneg (p t 0)]

/-- Near a zero `r̄` of `g` with `g'(r̄) = d`: `|(s - r̄)g(s) - d(s - r̄)²| ≤ (|d|/2)(s - r̄)²`. -/
theorem ttg_quad_bound {g : ℝ → ℝ} {rb d : ℝ} (hd : HasDerivAt g d rb) (h0 : g rb = 0)
    (hd0 : d ≠ 0) : ∃ δ > 0, ∀ s, |s - rb| < δ →
      |(s - rb) * g s - d * (s - rb) ^ 2| ≤ |d| / 2 * (s - rb) ^ 2 := by
  have hlo := (hasDerivAt_iff_isLittleO.1 hd).def (show (0 : ℝ) < |d| / 2 by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have h := hball (show dist s rb < δ by rwa [Real.dist_eq])
  simp only [h0, sub_zero, smul_eq_mul, Real.norm_eq_abs] at h
  have : (s - rb) * g s - d * (s - rb) ^ 2 = (s - rb) * (g s - (s - rb) * d) := by ring
  rw [this, abs_mul]
  calc |s - rb| * |g s - (s - rb) * d| ≤ |s - rb| * (|d| / 2 * |s - rb|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |d| / 2 * (s - rb) ^ 2 := by rw [← sq_abs (s - rb)]; ring

/-- **Section 17.H, property (a)** (MWG, pp. 621-622), the stable case. With two goods, an
equilibrium `(r̄, 1)` at which `z₁(·, 1)` has negative slope (`d < 0`, index `+1`) is locally
stable: every trajectory starting with `p₁(0)/p₂(0)` close to `r̄` has `p₁(t)/p₂(t) → r̄`. -/
theorem tat_two_locally_stable (hc : ∀ l, 0 < c l) (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    {rb d : ℝ} (h0 : z ![rb, 1] 0 = 0) (hd : HasDerivAt (fun s => z ![s, 1] 0) d rb)
    (hneg : d < 0) : ∃ ε > 0, ∀ p : ℝ → Fin 2 → ℝ, IsTatPath c z p →
      |p 0 0 / p 0 1 - rb| < ε → Tendsto (fun t => p t 0 / p t 1) atTop (𝓝 rb) := by
  obtain ⟨δ, hδ, hb⟩ := ttg_quad_bound hd h0 hneg.ne
  refine ⟨δ, hδ, fun p hp h0p => ?_⟩
  set r : ℝ → ℝ := fun t => p t 0 / p t 1 with hr
  set D : ℝ → ℝ := fun t => (r t - rb) ^ 2 with hD
  set κ := c 0 / Real.sqrt (c 1 * wNormSq c (p 0)) with hκ
  have hκpos : 0 < κ := div_pos (hc 0) (Real.sqrt_pos.2 (mul_pos (hc 1)
    (wNormSq_pos hc (posOrthant_ne_zero (hp.1 0 le_rfl)))))
  have hDd : ∀ t, 0 ≤ t → HasDerivWithinAt D
      (2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t)) (Ici 0) t := by
    intro t ht
    have := ((footnote_17_60 hH hW hp ht).sub_const rb).pow 2
    convert this using 1
    simp only [hr]
    ring
  have hquad : ∀ t, |r t - rb| < δ → (r t - rb) * z ![r t, 1] 0 ≤ d / 2 * (r t - rb) ^ 2 := by
    intro t ht
    have := hb (r t) ht
    rw [abs_of_neg hneg] at this
    have := (abs_le.1 this).2
    linarith
  have hD0 : D 0 < δ ^ 2 := by
    simp only [hD]
    rw [← sq_abs]
    exact pow_lt_pow_left₀ h0p (abs_nonneg _) two_ne_zero
  -- the trajectory stays within `δ` of `r̄`
  have hDle : ∀ T, 0 ≤ T → D T ≤ D 0 := by
    intro T hT
    have hε : ∀ η, 0 < η → D 0 + η < δ ^ 2 → D T ≤ D 0 + η := by
      intro η hη hηδ
      refine image_le_of_deriv_right_lt_deriv_boundary' (f := D)
        (f' := fun t => 2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t))
        (B := fun _ => D 0 + η) (B' := fun _ => 0)
        (fun x hx => (hDd x hx.1).continuousWithinAt.mono fun y hy => hy.1)
        (fun x hx => (hDd x hx.1).mono fun y (hy : x ≤ y) => hx.1.trans hy)
        (by linarith) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_
        ⟨hT, le_rfl⟩
      intro x hx hDx
      have hpos : 0 < D x := by have := sq_nonneg (r 0 - rb); simp only [hD] at hDx ⊢; linarith
      have hlt : |r x - rb| < δ := by
        have : (r x - rb) ^ 2 < δ ^ 2 := by simp only [hD] at hDx; linarith
        exact abs_lt_of_sq_lt_sq this hδ.le
      have h1 := hquad x hlt
      have h2 := ttgFactor_pos hc (hp.1 x hx.1)
      have h3 : d / 2 * (r x - rb) ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
      have := mul_lt_mul_of_pos_right (lt_of_le_of_lt h1 h3) h2
      nlinarith
    by_contra hcon
    push Not at hcon
    set η := min (D T - D 0) (δ ^ 2 - D 0) / 2 with hη
    have hη0 : 0 < η := by
      have : 0 < min (D T - D 0) (δ ^ 2 - D 0) := lt_min (by linarith) (by linarith)
      linarith
    have h1 := min_le_left (D T - D 0) (δ ^ 2 - D 0)
    have h2 := min_le_right (D T - D 0) (δ ^ 2 - D 0)
    have := hε η hη0 (by linarith)
    linarith
  have hin : ∀ t, 0 ≤ t → |r t - rb| < δ := fun t ht =>
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt (hDle t ht) hD0) hδ.le
  -- exponential decay: `D(t) e^{-dκt}` is nonincreasing
  set F : ℝ → ℝ := fun t => D t * Real.exp (-(d * κ) * t) with hF
  have hFanti : ∀ t, 0 ≤ t → F t ≤ F 0 := by
    have hmono := tat_monotoneOn (F := fun t => -F t)
      (F' := fun t => -((2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t)) *
        Real.exp (-(d * κ) * t) + D t * (Real.exp (-(d * κ) * t) * (-(d * κ)))))
      (fun t ht => ((hDd t ht).mul ((((hasDerivAt_id t).const_mul (-(d * κ))).exp).congr_deriv
        (by simp) |>.hasDerivWithinAt)).fun_neg) ?_
    · intro t ht
      have := hmono (Set.mem_Ici.2 le_rfl) ht ht
      simp only at this
      linarith
    · intro t ht
      have h1 := hquad t (hin t ht)
      have h2 := ttg_factor_lower hc hW hp ht
      have hk := ttgFactor_pos hc (hp.1 t ht)
      have he := Real.exp_pos (-(d * κ) * t)
      have hDt : 0 ≤ D t := sq_nonneg _
      have h3 : 2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t) ≤ d * κ * D t := by
        have h4 : 2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t) ≤
            d * D t * ttgFactor c (p t) := by
          have := mul_le_mul_of_nonneg_right h1 hk.le
          simp only [hD]
          nlinarith
        have h5 : d * D t * ttgFactor c (p t) ≤ d * D t * κ :=
          mul_le_mul_of_nonpos_left h2 (mul_nonpos_of_nonpos_of_nonneg hneg.le hDt)
        linarith
      have := mul_le_mul_of_nonneg_right h3 he.le
      nlinarith
  have hbound : ∀ t, 0 ≤ t → D t ≤ D 0 * Real.exp (d * κ * t) := by
    intro t ht
    have h := hFanti t ht
    simp only [hF, mul_zero, Real.exp_zero, mul_one] at h
    have he := Real.exp_pos (-(d * κ) * t)
    have : D t = D t * Real.exp (-(d * κ) * t) * Real.exp (d * κ * t) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hlim : Tendsto (fun t => D 0 * Real.exp (d * κ * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t => d * κ * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (mul_neg_of_neg_of_pos hneg hκpos)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (D 0)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hlim (ε ^ 2) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  have h1 := hT t ((le_max_left _ _).trans ht)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
  have h2 := hbound t ht0
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq (by simp only [hD] at h2; linarith) hε.le


/-- **Section 17.H, property (a)** (MWG, pp. 621-622), the unstable case. With two goods, an
equilibrium `(r̄, 1)` at which `z₁(·, 1)` has positive slope (`d > 0`, index `-1`) is locally
totally unstable: there is `ε > 0` such that every trajectory starting with `p₁(0)/p₂(0) ≠ r̄`
within `ε` of `r̄` leaves the `ε`-neighbourhood of `r̄`. -/
theorem tat_two_locally_totally_unstable (hc : ∀ l, 0 < c l) (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {rb d : ℝ} (h0 : z ![rb, 1] 0 = 0)
    (hd : HasDerivAt (fun s => z ![s, 1] 0) d rb) (hpos : 0 < d) :
    ∃ ε > 0, ∀ p : ℝ → Fin 2 → ℝ, IsTatPath c z p → p 0 0 / p 0 1 ≠ rb →
      |p 0 0 / p 0 1 - rb| < ε → ∃ t, 0 ≤ t ∧ ε ≤ |p t 0 / p t 1 - rb| := by
  obtain ⟨δ, hδ, hb⟩ := ttg_quad_bound hd h0 hpos.ne'
  refine ⟨δ, hδ, fun p hp hne _ => ?_⟩
  by_contra hcon
  push Not at hcon
  set r : ℝ → ℝ := fun t => p t 0 / p t 1 with hr
  set D : ℝ → ℝ := fun t => (r t - rb) ^ 2 with hD
  set κ := c 0 / Real.sqrt (c 1 * wNormSq c (p 0)) with hκ
  have hκpos : 0 < κ := div_pos (hc 0) (Real.sqrt_pos.2 (mul_pos (hc 1)
    (wNormSq_pos hc (posOrthant_ne_zero (hp.1 0 le_rfl)))))
  have hDd : ∀ t, 0 ≤ t → HasDerivWithinAt D
      (2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t)) (Ici 0) t := by
    intro t ht
    have := ((footnote_17_60 hH hW hp ht).sub_const rb).pow 2
    convert this using 1
    simp only [hr]
    ring
  have hquad : ∀ t, 0 ≤ t → d / 2 * (r t - rb) ^ 2 ≤ (r t - rb) * z ![r t, 1] 0 := by
    intro t ht
    have := hb (r t) (hcon t ht)
    rw [abs_of_pos hpos] at this
    have := (abs_le.1 this).1
    linarith
  set G : ℝ → ℝ := fun t => D t * Real.exp (-(d * κ) * t) with hG
  have hmono := tat_monotoneOn (F := G)
    (F' := fun t => (2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t)) *
      Real.exp (-(d * κ) * t) + D t * (Real.exp (-(d * κ) * t) * (-(d * κ))))
    (fun t ht => (hDd t ht).mul ((((hasDerivAt_id t).const_mul (-(d * κ))).exp).congr_deriv
      (by simp) |>.hasDerivWithinAt)) (fun t ht => by
        have h1 := hquad t ht
        have h2 := ttg_factor_lower hc hW hp ht
        have hk := ttgFactor_pos hc (hp.1 t ht)
        have he := Real.exp_pos (-(d * κ) * t)
        have hDt : 0 ≤ D t := sq_nonneg _
        have h3 : d * κ * D t ≤ 2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t) := by
          have h4 : d * D t * ttgFactor c (p t) ≤
              2 * ((r t - rb) * z ![r t, 1] 0) * ttgFactor c (p t) := by
            have := mul_le_mul_of_nonneg_right h1 hk.le
            simp only [hD]
            nlinarith
          have h5 : d * D t * κ ≤ d * D t * ttgFactor c (p t) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hpos.le hDt)
          linarith
        have := mul_le_mul_of_nonneg_right h3 he.le
        nlinarith)
  have hD0 : 0 < D 0 := by
    simp only [hD]
    exact pow_pos (abs_pos.2 (sub_ne_zero.2 hne)) 2 |>.trans_eq (sq_abs _)
  set T := δ ^ 2 / (D 0 * (d * κ)) with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 := hmono (Set.mem_Ici.2 le_rfl) hT0 hT0
  simp only [hG, mul_zero, Real.exp_zero, mul_one] at h1
  have h2 : D T ≥ D 0 * Real.exp (d * κ * T) := by
    have he := Real.exp_pos (d * κ * T)
    have : D T * Real.exp (-(d * κ) * T) * Real.exp (d * κ * T) = D T := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [← this]
    exact mul_le_mul_of_nonneg_right h1 he.le
  have h3 : D 0 * (1 + d * κ * T) ≤ D 0 * Real.exp (d * κ * T) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (d * κ * T)]) hD0.le
  have h4 : D 0 * (1 + d * κ * T) = D 0 + δ ^ 2 := by
    rw [hT]; field_simp
  have h5 : D T < δ ^ 2 := by
    have := hcon T hT0
    simp only [hD]
    rw [← sq_abs]
    exact pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
  linarith

/-- A sign value `-1` comes from a negative number. -/
theorem itgSgn_neg_iff {x : ℝ} (h : itgSgn x = -1) : x < 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact hx
  · simp [itgSgn] at h
  · rw [itgSgn_pos hx] at h
    norm_num at h

/-- A sign value `+1` comes from a positive number. -/
theorem itgSgn_pos_iff {x : ℝ} (h : itgSgn x = 1) : 0 < x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [itgSgn_neg hx] at h
    norm_num at h
  · simp [itgSgn] at h
  · exact hx

/-- **Section 17.H, property (a)** (MWG, p. 622): a regular equilibrium of index `+1`
(Definition 17.D.2) is locally stable. -/
theorem tat_two_stable_of_index (hc : ∀ l, 0 < c l) (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    {rb : ℝ} (hreg : IsRegularEqm z (vec1 rb)) (hidx : eqmIndex z (vec1 rb) = 1) :
    ∃ ε > 0, ∀ p : ℝ → Fin 2 → ℝ, IsTatPath c z p →
      |p 0 0 / p 0 1 - rb| < ε → Tendsto (fun t => p t 0 / p t 1) atTop (𝓝 rb) := by
  have h0 := ((isNormEqm_vec1_iff hW).1 hreg.1).2
  rw [eqmIndex_two] at hidx
  have hs : itgSgn (slope2 z rb) = -1 := by simp only [vec1] at hidx; linarith
  exact tat_two_locally_stable hc hH hW h0 (two_goods_hasDerivAt hreg.2.1) (itgSgn_neg_iff hs)

/-- **Section 17.H, property (a)** (MWG, p. 622): a regular equilibrium of index `-1` is locally
totally unstable. -/
theorem tat_two_unstable_of_index (hc : ∀ l, 0 < c l) (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {rb : ℝ} (hreg : IsRegularEqm z (vec1 rb))
    (hidx : eqmIndex z (vec1 rb) = -1) :
    ∃ ε > 0, ∀ p : ℝ → Fin 2 → ℝ, IsTatPath c z p → p 0 0 / p 0 1 ≠ rb →
      |p 0 0 / p 0 1 - rb| < ε → ∃ t, 0 ≤ t ∧ ε ≤ |p t 0 / p t 1 - rb| := by
  have h0 := ((isNormEqm_vec1_iff hW).1 hreg.1).2
  rw [eqmIndex_two] at hidx
  have hs : itgSgn (slope2 z rb) = 1 := by simp only [vec1] at hidx; linarith
  exact tat_two_locally_totally_unstable hc hH hW h0 (two_goods_hasDerivAt hreg.2.1)
    (itgSgn_pos_iff hs)

/-! ### Footnote 62 with two goods -/

/-- With two goods and (i)-(v), if `r̄` is the only zero of `z₁(·, 1)` on `(0, ∞)`, then
`z₁(r, 1) > 0` for `r < r̄` and `< 0` for `r > r̄` (boundary behaviour, footnote 8, and the
intermediate value theorem). -/
theorem ttg_sign_of_unique (hz : IsStandardExcessDemand z) {rb : ℝ}
    (huniq : ∀ r, 0 < r → z ![r, 1] 0 = 0 → r = rb) {r : ℝ} (hr : 0 < r) (hne : r ≠ rb) :
    0 < z ![r, 1] 0 * (rb - r) := by
  have hvec : Continuous fun t : ℝ => (![t, 1] : Fin 2 → ℝ) := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact continuous_id'
    · simpa using continuous_const
  have hg : ContinuousOn (fun t => z ![t, 1] 0) (Ioi 0) :=
    (continuous_apply 0).comp_continuousOn (hz.continuous.comp hvec.continuousOn
      fun t ht => ttg_vec_mem ht)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine mul_pos ?_ (by linarith)
    by_contra hcon
    push Not at hcon
    have hlow := footnote_17_8_low hz (as := fun k : ℕ => 1 / ((k : ℝ) + 1))
      (fun k => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < r :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hr)
    obtain ⟨k, hk1, hk2⟩ := (hlow.and hsmall).exists
    set a := 1 / ((k : ℝ) + 1)
    have ha : 0 < a := by positivity
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' hk2.le
      (hg.mono fun x hx => lt_of_lt_of_le ha hx.1) ⟨hcon, hk1.le⟩
    have := huniq s (lt_of_lt_of_le ha hs.1) hs0
    linarith [hs.2]
  · refine mul_pos_of_neg_of_neg ?_ (by linarith)
    by_contra hcon
    push Not at hcon
    have hhigh := footnote_17_8_high hz (bs := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hlarge : ∀ᶠ k : ℕ in atTop, r < (k : ℝ) + 1 :=
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually_gt_atTop r
    obtain ⟨k, hk1, hk2⟩ := (hhigh.and hlarge).exists
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' hk2.le
      (hg.mono fun x hx => lt_of_lt_of_le hr hx.1) ⟨hk1.le, hcon⟩
    have := huniq s (lt_of_lt_of_le hr hs.1) hs0
    linarith [hs.1]

/-- **Footnote 62** (MWG, p. 623), the case `L = 2`: uniqueness implies (global) stability. If
`z` satisfies (i)-(v) and `(r̄, 1)` is the only normalized equilibrium, every tâtonnement
trajectory converges to the ray of `(r̄, 1)` (Proposition 17.H.1 applies, since
`(r̄, 1)·z(p) = z₁(r, 1)(r̄ - r)` with `r = p₁/p₂`). -/
theorem footnote_17_62_two_goods (hc : ∀ l, 0 < c l) (hz : IsStandardExcessDemand z) {rb : ℝ}
    (hrb : 0 < rb) (h0 : z ![rb, 1] 0 = 0)
    (huniq : ∀ r, 0 < r → z ![r, 1] 0 = 0 → r = rb) (hp : IsTatPath c z p) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • (![rb, 1] : Fin 2 → ℝ))) := by
  have heq : IsEqmPrice z ![rb, 1] := by
    have := (isNormEqm_vec1_iff hz.walras).2 ⟨hrb, h0⟩
    rwa [IsNormEqm, normPrice_vec1] at this
  refine proposition_17_H_1 hc hz.continuous hz.walras hz.boundedBelow hz.boundary heq ?_ hp
  intro q hq hnot
  have hq1 := hq 1
  set r := q 0 / q 1 with hr
  have hne : r ≠ rb := by
    intro h
    apply hnot
    refine ⟨q 1, hq1, funext fun l => ?_⟩
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      rw [← h, hr]
      field_simp
    · simp
  have hval : (![rb, 1] : Fin 2 → ℝ) ⬝ᵥ z q = z ![r, 1] 0 * (rb - r) := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul]
    rw [ttg_walras hz.walras hq, ttg_hom hz.homogeneous hq]
    ring
  rw [hval]
  exact ttg_sign_of_unique hz huniq (div_pos (hq 0) hq1) hne

end MWG.PositiveEquilibriumTheory
