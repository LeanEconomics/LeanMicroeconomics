/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv

/-!
# Exercise 14.B.1

MWG, Exercise 14.B.1, p. 507: with a general utility `u(w, e)` (not of the form `v(w) - g(e)`),
must the reservation utility constraint bind in an optimal contract? No.

Two profit levels; `f(π_H | e_H) = 1/2 > f(π_H | e_L) = 5/16`; `u(w, e_L) = w` and
`u(w, e_H) = w - c(w)` with `c(w) = 1/8 + ((1 - w)⁺)³` (the disutility of effort falls with
income); `ū = 0`. Then `u_w > 0`, `u_ww ≤ 0` (`c` is convex and `C¹`; here
`c(w) = 1/8 + ((1 - w)³ + |1 - w|³)/2`), and `u(w, e_H) < u(w, e_L)`.

* `b1_c_deriv`, `b1_uw_pos`, `b1_c_convex`, `b1_uH_lt`: the model satisfies MWG's assumptions.
* `exercise_14_B_1`: the scheme `w(π_L) = 1/2`, `w(π_H) = 3/2` implements `e_H` at expected wage
  `1`; every scheme satisfying the incentive constraint costs at least `1`, with equality only for
  this scheme; and it gives the manager `13/16 > ū = 0`. So the unique optimal contract for `e_H`
  has a slack participation constraint (lowering wages would violate incentive compatibility).
-/

namespace MWG.PrincipalAgent

/-- The disutility of high effort in money terms, `c(w) = 1/8 + ((1 - w)⁺)³`. -/
noncomputable def b1c (w : ℝ) : ℝ := 1 / 8 + ((1 - w) ^ 3 + ((1 - w) ^ 2) ^ (3 / 2 : ℝ)) / 2

/-- Its derivative, `-3 ((1 - w)⁺)²`. -/
noncomputable def b1dc (w : ℝ) : ℝ := (-3 * (1 - w) ^ 2 - 3 * (1 - w) * |1 - w|) / 2

theorem b1_rpow32 (t : ℝ) : (t ^ 2) ^ (3 / 2 : ℝ) = |t| ^ 3 := by
  rw [← sq_abs t, ← Real.rpow_natCast |t| 2, ← Real.rpow_mul (abs_nonneg t)]
  norm_num

theorem b1_rpow12 (t : ℝ) : (t ^ 2) ^ (1 / 2 : ℝ) = |t| := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- `c(w) = 1/8 + ((1 - w)³ + |1 - w|³)/2`. -/
theorem b1c_eq (w : ℝ) : b1c w = 1 / 8 + ((1 - w) ^ 3 + |1 - w| ^ 3) / 2 := by
  rw [b1c, b1_rpow32]

/-- `c` is differentiable with derivative `b1dc`. -/
theorem b1_c_deriv (w : ℝ) : HasDerivAt b1c (b1dc w) w := by
  have h0 : HasDerivAt (fun w : ℝ => 1 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h1 := h0.pow 3
  have h2 := (h0.pow 2).rpow_const (p := 3 / 2) (Or.inr (by norm_num))
  have h : HasDerivAt b1c ((↑3 * (1 - w) ^ (3 - 1) * -1 + ↑2 * (1 - w) ^ (2 - 1) * -1 * (3 / 2) *
      ((1 - w) ^ 2) ^ ((3 : ℝ) / 2 - 1)) / 2) w := ((h1.add h2).div_const 2).const_add (1 / 8)
  refine h.congr_deriv ?_
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, b1_rpow12]
  unfold b1dc; push_cast; ring

/-- `c(w) ≥ 1/8`, so `u(w, e_H) < u(w, e_L)`. -/
theorem b1_c_ge (w : ℝ) : 1 / 8 ≤ b1c w := by
  rw [b1c_eq]
  have : -(1 - w) ^ 3 ≤ |1 - w| ^ 3 := by
    rcases le_total 0 (1 - w) with h | h
    · rw [abs_of_nonneg h]; nlinarith [pow_nonneg h 3]
    · rw [abs_of_nonpos h]; ring_nf; exact le_refl _
  linarith

theorem b1_uH_lt (w : ℝ) : w - b1c w < w := by have := b1_c_ge w; linarith

/-- `c' ≤ 0`, so `u_w(w, e_H) = 1 - c'(w) ≥ 1 > 0`. -/
theorem b1_uw_pos (w : ℝ) : 0 < 1 - b1dc w := by
  unfold b1dc
  have : -(1 - w) * |1 - w| ≤ (1 - w) ^ 2 := by
    rw [← sq_abs (1 - w), sq]
    nlinarith [neg_abs_le (1 - w), abs_nonneg (1 - w)]
  nlinarith [sq_nonneg (1 - w)]

/-- `c'` is nondecreasing, so `c` is convex and `u(·, e_H)` is concave (`u_ww ≤ 0`). -/
theorem b1_c_convex : ConvexOn ℝ Set.univ b1c := by
  have hd : deriv b1c = b1dc := funext fun w => (b1_c_deriv w).deriv
  refine Monotone.convexOn_univ_of_deriv (fun w => (b1_c_deriv w).differentiableAt) ?_
  rw [hd]
  intro a b hab
  unfold b1dc
  -- with `s = 1 - a ≥ t = 1 - b`, `s² + s|s| ≥ t² + t|t|`
  set s := 1 - a
  set t := 1 - b
  have hts : t ≤ s := by simp only [s, t]; linarith
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (ht.trans hts)]; nlinarith
  · rcases le_total 0 s with hs | hs
    · rw [abs_of_nonpos ht, abs_of_nonneg hs]; nlinarith
    · rw [abs_of_nonpos ht, abs_of_nonpos hs]; nlinarith

/-- The tangent line of `c` at `1/2`: `c(x) ≥ 1/4 - (3/4)(x - 1/2)`. -/
theorem b1_c_tangent (x : ℝ) : 1 / 4 - 3 / 4 * (x - 1 / 2) ≤ b1c x := by
  rw [b1c_eq]
  rcases le_total 0 (1 - x) with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg (sq_nonneg (1 - x - 1 / 2)) (by linarith : (0:ℝ) ≤ 1 - x + 1)]
  · rw [abs_of_nonpos h]
    nlinarith

theorem b1_c_half : b1c (1 / 2) = 1 / 4 := by rw [b1c_eq]; norm_num [abs_of_pos]

theorem b1_c_threehalf : b1c (3 / 2) = 1 / 8 := by rw [b1c_eq]; norm_num [abs_of_neg]

/-- **Exercise 14.B.1** (MWG, p. 507). In the model above (`u(w, e_H) = w - c(w)`, `u(w, e_L) = w`,
`f(π_H|e_H) = 1/2`, `f(π_H|e_L) = 5/16`, `ū = 0`), the scheme `(w_L, w_H) = (1/2, 3/2)` satisfies
the incentive constraint for `e_H` with expected wage `1`, every scheme satisfying the incentive
constraint has expected wage at least `1` with equality only for this scheme, and the manager's
expected utility under it is `13/16 > 0 = ū`: the reservation utility constraint does not bind in
the (unique) optimal contract. -/
theorem exercise_14_B_1 :
    let EUH : ℝ → ℝ → ℝ := fun w0 w1 => 1 / 2 * (w1 - b1c w1) + 1 / 2 * (w0 - b1c w0)
    let EUL : ℝ → ℝ → ℝ := fun w0 w1 => 5 / 16 * w1 + 11 / 16 * w0
    EUL (1 / 2) (3 / 2) ≤ EUH (1 / 2) (3 / 2) ∧ 1 / 2 * (1 / 2) + 1 / 2 * (3 / 2 : ℝ) = 1 ∧
      EUH (1 / 2) (3 / 2) = 13 / 16 ∧
      ∀ w0 w1, EUL w0 w1 ≤ EUH w0 w1 →
        1 ≤ 1 / 2 * w0 + 1 / 2 * w1 ∧
          (1 / 2 * w0 + 1 / 2 * w1 = 1 → w0 = 1 / 2 ∧ w1 = 3 / 2) := by
  intro EUH EUL
  simp only [EUH, EUL, b1_c_half, b1_c_threehalf]
  refine ⟨by norm_num, by norm_num, by norm_num, fun w0 w1 hIC => ?_⟩
  have t0 := b1_c_tangent w0
  have t1 := b1_c_ge w1
  refine ⟨by linarith, fun heq => ?_⟩
  -- equality forces equality in the tangent bound at `w₀`, hence `w₀ = 1/2`
  have he : b1c w0 = 1 / 4 - 3 / 4 * (w0 - 1 / 2) := by linarith
  have h0 : w0 = 1 / 2 := by
    rw [b1c_eq] at he
    rcases le_total 0 (1 - w0) with h | h
    · rw [abs_of_nonneg h] at he
      have : (1 - w0 - 1 / 2) ^ 2 * (1 - w0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h' | h'
      · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h']
      · linarith
    · rw [abs_of_nonpos h] at he
      nlinarith
  exact ⟨h0, by rw [h0] at heq; linarith⟩

end MWG.PrincipalAgent
