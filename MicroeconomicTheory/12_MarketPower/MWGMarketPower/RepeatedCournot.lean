/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Cournot
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exercise 12.D.3: Nash reversion in the repeated linear Cournot duopoly

MWG, Exercise 12.D.3, p. 433.

With `A = a − c > 0`, symmetric outputs `(q, q)`, the stationary condition (12.AA.3) reads
`π̂(q) − π(q) ≤ δ/(1 − δ)(π(q) − π*)`, where `π(q) = (A − 2bq)q`, the best-response profit is
`π̂(q) = (A − bq)²/(4b)` (for `q ≤ A/b`, Example 12.C.1), and `π* = A²/(9b)` is the Cournot profit.
The gain from deviating is `π̂(q) − π(q) = (A − 3bq)²/(4b)`.

* `exercise_12_D_3a`: the joint monopoly outputs `(A/(4b), A/(4b))` satisfy (12.AA.3) iff
  `δ ≥ 9/17`.
* `exercise_12_D_3b_printed_false` (correction): for every `q` in the printed interval
  `[A/(2b), A/b]` and every `δ ∈ [0, 1)`, (12.AA.3) fails (the price is at most `c`).
* `exercise_12_D_3b_corrected`: for `q ∈ [A/(4b), A/(3b))` (between joint monopoly and Cournot),
  (12.AA.3) holds iff `δ ≥ δ(q) = 9(A − 3bq)/(5A − 3bq)`; `δ(q)` is differentiable and strictly
  *decreasing* in `q` (not increasing, as printed).
-/

namespace MWG.MarketPower

/-- The deviation gain `π̂(q) − π(q) = (A − 3bq)²/(4b)`. -/
theorem cournot_gain {A b q : ℝ} (hb : 0 < b) :
    (A - b * q) ^ 2 / (4 * b) - (A - 2 * b * q) * q = (A - 3 * b * q) ^ 2 / (4 * b) := by
  field_simp; ring

/-- Condition (12.AA.3) for the symmetric output `q` of the linear Cournot duopoly. -/
def CournotNR (A b δ q : ℝ) : Prop :=
  (A - b * q) ^ 2 / (4 * b) - (A - 2 * b * q) * q ≤
    δ / (1 - δ) * ((A - 2 * b * q) * q - A ^ 2 / (9 * b))

/-- **Exercise 12.D.3(b), corrected** (MWG, p. 433). For `q ∈ [A/(4b), A/(3b))`, condition
(12.AA.3) holds iff `δ ≥ 9(A − 3bq)/(5A − 3bq)` (indeed for every `q < A/(3b)`). -/
theorem exercise_12_D_3b_corrected {A b δ q : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hδ1 : δ < 1) (hq2 : q < A / (3 * b)) :
    CournotNR A b δ q ↔ 9 * (A - 3 * b * q) / (5 * A - 3 * b * q) ≤ δ := by
  unfold CournotNR
  rw [cournot_gain hb]
  have h3 : 0 < A - 3 * b * q := by
    rw [lt_div_iff₀ (by positivity)] at hq2; linarith
  have h5 : 0 < 5 * A - 3 * b * q := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hπ : (A - 2 * b * q) * q - A ^ 2 / (9 * b) =
      (A - 3 * b * q) * (6 * b * q - A) / (9 * b) := by
    field_simp; ring
  rw [hπ, div_le_iff₀ h5]
  set X := A - 3 * b * q with hX
  set Y := 6 * b * q - A with hY
  have h36 : 0 < 36 * b * (1 - δ) := by positivity
  rw [show δ / (1 - δ) * (X * Y / (9 * b)) = 4 * δ * X * Y / (36 * b * (1 - δ)) by
      field_simp; ring,
    show X ^ 2 / (4 * b) = 9 * X ^ 2 * (1 - δ) / (36 * b * (1 - δ)) by field_simp; ring,
    div_le_div_iff_of_pos_right h36]
  have e : 9 * X - δ * (5 * A - 3 * b * q) = 9 * X * (1 - δ) - 4 * δ * Y := by
    rw [hX, hY]; ring
  constructor
  · intro h
    have : 9 * X * (1 - δ) ≤ 4 * δ * Y := by
      by_contra hc; push Not at hc
      nlinarith [mul_lt_mul_of_pos_left hc h3]
    linarith
  · intro h
    have : 9 * X * (1 - δ) ≤ 4 * δ * Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h3.le]

/-- **Exercise 12.D.3(a)** (MWG, p. 433). The joint monopoly outputs `(A/(4b), A/(4b))` are
sustained by Nash reversion iff `δ ≥ 9/17`. -/
theorem exercise_12_D_3a {A b δ : ℝ} (hA : 0 < A) (hb : 0 < b) (hδ1 : δ < 1) :
    CournotNR A b δ (A / (4 * b)) ↔ 9 / 17 ≤ δ := by
  rw [exercise_12_D_3b_corrected hA hb hδ1 (by
    apply div_lt_div_of_pos_left hA (by positivity); linarith)]
  have : 9 * (A - 3 * b * (A / (4 * b))) / (5 * A - 3 * b * (A / (4 * b))) = 9 / 17 := by
    field_simp; ring
  rw [this]

/-- **Exercise 12.D.3(b) is false on the printed interval** (MWG, p. 433; correction). For
`q ∈ [A/(2b), A/b]` the market price is at most `c`, so `π(q) ≤ 0 < π*` and (12.AA.3) fails for
every `δ ∈ [0, 1)`: no output in the printed interval is sustainable by Nash reversion. -/
theorem exercise_12_D_3b_printed_false {A b δ q : ℝ} (hA : 0 < A) (hb : 0 < b) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hq1 : A / (2 * b) ≤ q) : ¬ CournotNR A b δ q := by
  unfold CournotNR
  rw [cournot_gain hb]
  intro h
  have hq : A ≤ 2 * b * q := by rw [div_le_iff₀ (by positivity)] at hq1; linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hgain : 0 < (A - 3 * b * q) ^ 2 / (4 * b) := by
    have : A - 3 * b * q ≠ 0 := by nlinarith
    positivity
  have hπ : (A - 2 * b * q) * q - A ^ 2 / (9 * b) < 0 := by
    have h1 : (A - 2 * b * q) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le
    have h2 : 0 < A ^ 2 / (9 * b) := by positivity
    linarith
  have : δ / (1 - δ) * ((A - 2 * b * q) * q - A ^ 2 / (9 * b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hδ0 (by linarith)) hπ.le
  linarith

/-- **Exercise 12.D.3(b): the threshold is differentiable and decreasing** (MWG, p. 433;
correction: MWG says increasing). `δ(q) = 9(A − 3bq)/(5A − 3bq)` has derivative
`−108Ab/(5A − 3bq)² < 0` on `q < 5A/(3b)`. -/
theorem exercise_12_D_3b_threshold {A b q : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hq : 3 * b * q < 5 * A) :
    HasDerivAt (fun q => 9 * (A - 3 * b * q) / (5 * A - 3 * b * q))
      (-(108 * A * b) / (5 * A - 3 * b * q) ^ 2) q ∧
    -(108 * A * b) / (5 * A - 3 * b * q) ^ 2 < 0 := by
  have hne : 5 * A - 3 * b * q ≠ 0 := by linarith
  constructor
  · have h1 : HasDerivAt (fun q => 9 * (A - 3 * b * q)) (9 * (-(3 * b))) q := by
      have := ((hasDerivAt_id q).const_mul (3 * b)).const_sub A |>.const_mul 9
      simpa using this
    have h2 : HasDerivAt (fun q => 5 * A - 3 * b * q) (-(3 * b)) q := by
      have := ((hasDerivAt_id q).const_mul (3 * b)).const_sub (5 * A)
      simpa using this
    refine (h1.div h2 hne).congr_deriv ?_
    field_simp; ring
  · apply div_neg_of_neg_of_pos (by nlinarith) (by positivity)

end MWG.MarketPower
