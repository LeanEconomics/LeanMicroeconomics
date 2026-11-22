/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UtilityMore

/-!
# Infinite risk aversion

MWG, Section 14.C, p. 494 and footnote 15.

The manager's Bernoulli utility `u_ρ(v) = -v^ρ` (`ρ < 0`) applied to the utility levels
`v_H, v_L > 0` of the two states gives expected utility `EU = -[λ v_H^ρ + (1 - λ) v_L^ρ]`, ordered
by the certainty equivalent `(-EU)^{1/ρ}`; as `ρ → -∞` this tends to `min {v_H, v_L}`. The limit is
MWG's Exercise 3.C.6(c), imported from Chapter 3 (`MWG.ClassicalDemand.exercise_3_C_6c`).

* `footnote_15_order`: for `ρ < 0`, `(-EU)^{1/ρ}` orders contracts as `EU` does.
* `footnote_15`: `(λ v_H^ρ + (1 - λ) v_L^ρ)^{1/ρ} → min {v_H, v_L}` as `ρ → -∞`.
* `footnote_15_accept`, `footnote_15_reject`: a contract is accepted by the manager with the
  certain reservation utility `ū` for every `ρ < 0` if `min {v_H, v_L} ≥ ū`, and rejected for all
  sufficiently negative `ρ` if `min {v_H, v_L} < ū`.
* `infinite_ra_insure`: with an infinitely risk-averse manager, lowering the better state's
  utility to the worse one's keeps him equally well off and lowers the wage bill (p. 494).
-/

namespace MWG.PrincipalAgent

open Filter Topology

/-- The certainty equivalent `(λ v_H^ρ + (1 - λ) v_L^ρ)^{1/ρ}` of footnote 15. -/
noncomputable def ceRho (lam vH vL ρ : ℝ) : ℝ := (lam * vH ^ ρ + (1 - lam) * vL ^ ρ) ^ (1 / ρ)

/-- **Footnote 15** (MWG, p. 494): for `ρ < 0` the expected utility `-(λ v_H^ρ + (1 - λ) v_L^ρ)`
is ordered correctly by `(-EU)^{1/ρ}`. -/
theorem footnote_15_order {ρ X Y : ℝ} (hρ : ρ < 0) (hX : 0 < X) (hY : 0 < Y) :
    -X < -Y ↔ X ^ (1 / ρ) < Y ^ (1 / ρ) := by
  have hr : 1 / ρ < 0 := one_div_neg.2 hρ
  constructor
  · intro h; exact Real.rpow_lt_rpow_of_neg hY (by linarith) hr
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · have := Real.rpow_lt_rpow_of_neg hX (by linarith : X < Y) hr; linarith
    · have : X = Y := by linarith
      rw [this] at h; exact lt_irrefl _ h

/-- **Footnote 15** (MWG, p. 494, via Exercise 3.C.6): as `ρ → -∞` the certainty equivalent tends
to `min {v_H, v_L}`. -/
theorem footnote_15 {lam vH vL : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hH : 0 < vH) (hL : 0 < vL) :
    Tendsto (ceRho lam vH vL) atBot (𝓝 (min vH vL)) :=
  MWG.ClassicalDemand.exercise_3_C_6c hl0 (by linarith) hH hL

/-- The certainty equivalent is at least `min {v_H, v_L}` for every `ρ < 0`. -/
theorem ceRho_ge_min {lam vH vL ρ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hH : 0 < vH)
    (hL : 0 < vL) (hρ : ρ < 0) : min vH vL ≤ ceRho lam vH vL ρ := by
  set m := min vH vL
  have hm : 0 < m := lt_min hH hL
  have hHm : vH ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm (min_le_left _ _) hρ.le
  have hLm : vL ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm (min_le_right _ _) hρ.le
  have hS : lam * vH ^ ρ + (1 - lam) * vL ^ ρ ≤ m ^ ρ := by
    nlinarith [mul_le_mul_of_nonneg_left hHm hl0,
      mul_le_mul_of_nonneg_left hLm (by linarith : (0:ℝ) ≤ 1 - lam)]
  have hSpos : 0 < lam * vH ^ ρ + (1 - lam) * vL ^ ρ := by
    rcases hl0.lt_or_eq with h | h
    · have := Real.rpow_pos_of_pos hH ρ
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (Real.rpow_pos_of_pos hL ρ).le
      nlinarith
    · rw [← h]; simp only [zero_mul, zero_add, sub_zero, one_mul]
      exact Real.rpow_pos_of_pos hL ρ
  have := Real.rpow_le_rpow_of_nonpos hSpos hS (one_div_neg.2 hρ).le
  rw [← Real.rpow_mul hm.le, mul_one_div_cancel hρ.ne, Real.rpow_one] at this
  exact this

/-- **Footnote 15**: if `min {v_H, v_L} ≥ ū > 0`, the contract gives the manager an expected utility
at least that of his certain reservation utility `ū`, for every `ρ < 0`. -/
theorem footnote_15_accept {lam vH vL u ρ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hu : 0 < u)
    (hρ : ρ < 0) (hmin : u ≤ min vH vL) :
    -(u ^ ρ) ≤ -(lam * vH ^ ρ + (1 - lam) * vL ^ ρ) := by
  have h1 := Real.rpow_le_rpow_of_nonpos hu (hmin.trans (min_le_left _ _)) hρ.le
  have h2 := Real.rpow_le_rpow_of_nonpos hu (hmin.trans (min_le_right _ _)) hρ.le
  nlinarith [mul_le_mul_of_nonneg_left h1 hl0,
    mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Footnote 15**: if `min {v_H, v_L} < ū`, then for all sufficiently negative `ρ` the certainty
equivalent is below `ū` (the contract is rejected). -/
theorem footnote_15_reject {lam vH vL u : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hH : 0 < vH)
    (hL : 0 < vL) (hmin : min vH vL < u) : ∀ᶠ ρ in atBot, ceRho lam vH vL ρ < u :=
  (footnote_15 hl0 hl1 hH hL).eventually (gt_mem_nhds hmin)

/-- **p. 494**: for an infinitely risk-averse manager, whose utility is the lower of his two
state utilities `min {x_H, x_L}`, paying the minimum in both states leaves him as well off and
lowers the expected wage payment. -/
theorem infinite_ra_insure {lam xH xL : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    min (min xH xL) (min xH xL) = min xH xL ∧
      lam * min xH xL + (1 - lam) * min xH xL ≤ lam * xH + (1 - lam) * xL := by
  refine ⟨min_self _, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left xH xL) hl0,
    mul_le_mul_of_nonneg_left (min_le_right xH xL) (by linarith : (0:ℝ) ≤ 1 - lam)]

end MWG.PrincipalAgent
