/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.MonopolyExercises
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Exercises 12.B.7(c)-(d), 12.B.8-12.B.10

MWG, Exercises 12.B.7-12.B.10, pp. 429-430.

* 12.B.7(c): the welfare-maximizing split of a total output `X` between men and women equalizes
  marginal valuations; (d): discrimination charges `(a/θₖ + c)/2`, leaves total output unchanged
  when both groups are served, and then lowers welfare; when the uniform price serves only
  women, discrimination raises welfare.
* 12.B.8: learning by doing: the monopolist's outputs, the planner's outputs (price equals
  marginal cost net of the learning benefit), and the planner's wish for more period-1 output.
* 12.B.9: investment in cost reduction: first-order conditions of the monopolist and of the
  planner, and the first- and second-best comparisons.
* 12.B.10: given its price, a monopolist does not over-provide quality, and under-provides it at
  an interior optimum.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.B.7(c)-(d) -/

/-- **Exercise 12.B.7(c)** (MWG, p. 429). Of all splits `xₘ + x_w = X`, gross benefit is
maximized at `xₘ* = (Xθₘ − a(θₘ − θ_w))/(θₘ + θ_w)`, where marginal valuations are equal:
`(a − xₘ*)/θₘ = (a − x_w*)/θ_w`; so (with a common cost) this split maximizes welfare. -/
theorem exercise_12_B_7c {a θm θw X : ℝ} (hm : 0 < θm) (hw : 0 < θw) :
    (∀ xm, groupBenefit a θm xm + groupBenefit a θw (X - xm) ≤
      groupBenefit a θm ((X * θm - a * (θm - θw)) / (θm + θw)) +
        groupBenefit a θw (X - (X * θm - a * (θm - θw)) / (θm + θw))) ∧
    (a - (X * θm - a * (θm - θw)) / (θm + θw)) / θm =
      (a - (X - (X * θm - a * (θm - θw)) / (θm + θw))) / θw := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun xm => ?_, by field_simp; ring⟩
  set s := (X * θm - a * (θm - θw)) / (θm + θw) with hs
  have key : groupBenefit a θm s + groupBenefit a θw (X - s) -
      (groupBenefit a θm xm + groupBenefit a θw (X - xm)) =
      (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by
    unfold groupBenefit; rw [hs]; field_simp; ring
  have : 0 ≤ (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by positivity
  linarith

/-- **Exercise 12.B.7(d)** (MWG, pp. 429-430). With discrimination the monopolist charges
`pₖ = (a/θₖ + c)/2` in each market (each maximizes `(p − c)(a − θₖp)`). If both groups are
served under the uniform price `p* = (2a + Θc)/(2Θ)`, total output is the same,
`(a − θₘc)/2 + (a − θ_wc)/2 = 2a − Θp*`, and aggregate surplus is strictly lower under
discrimination (when `θ_w < θₘ`), since the same output is split with unequal marginal
valuations (compare (c)). -/
theorem exercise_12_B_7d {a θm θw c : ℝ} (ha : 0 < a) (hm : 0 < θm) (hw : 0 < θw) (hθ : θw < θm) :
    (∀ p, (p - c) * (a - θm * p) ≤ ((a / θm + c) / 2 - c) * (a - θm * ((a / θm + c) / 2))) ∧
    (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) =
      2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) ∧
    widgetWelfare a θm θw c (a - θm * ((a / θm + c) / 2)) (a - θw * ((a / θw + c) / 2)) <
      widgetWelfare a θm θw c (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))))
        (a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun p => ?_, by field_simp; ring, ?_⟩
  · have key : ((a / θm + c) / 2 - c) * (a - θm * ((a / θm + c) / 2)) - (p - c) * (a - θm * p) =
        θm * (p - (a / θm + c) / 2) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hm.le (sq_nonneg (p - (a / θm + c) / 2))]
  · set X := (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) with hX
    obtain ⟨h1, _⟩ := exercise_12_B_7c (a := a) (X := X) hm hw
    have hsplit : (X * θm - a * (θm - θw)) / (θm + θw) =
        a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) := by
      rw [hX]; field_simp; ring
    have hsplit2 : X - (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) =
        a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) := by
      rw [hX]; field_simp; ring
    have hdisc : X - (a - θm * ((a / θm + c) / 2)) = a - θw * ((a / θw + c) / 2) := by
      rw [hX]; ring
    unfold widgetWelfare
    have hstrict : groupBenefit a θm (a - θm * ((a / θm + c) / 2)) +
        groupBenefit a θw (X - (a - θm * ((a / θm + c) / 2))) <
        groupBenefit a θm ((X * θm - a * (θm - θw)) / (θm + θw)) +
          groupBenefit a θw (X - (X * θm - a * (θm - θw)) / (θm + θw)) := by
      set s := (X * θm - a * (θm - θw)) / (θm + θw) with hs
      set xm := a - θm * ((a / θm + c) / 2) with hxm
      have key : groupBenefit a θm s + groupBenefit a θw (X - s) -
          (groupBenefit a θm xm + groupBenefit a θw (X - xm)) =
          (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by
        unfold groupBenefit; rw [hs]; field_simp; ring
      have hdiff : xm - s = a * (θm - θw) / (2 * (θm + θw)) := by
        rw [hsplit, hxm]; field_simp; ring
      have hne : xm - s ≠ 0 := by
        rw [hdiff]; have : 0 < θm - θw := by linarith
        positivity
      have : 0 < (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by positivity
      linarith
    rw [hdisc, hsplit, hsplit2] at hstrict
    have hcost : (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) =
        (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) +
          (a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) := by
      field_simp; ring
    rw [hcost]
    linarith

/-- **Exercise 12.B.7(d), one group served** (MWG, p. 430). If the uniform price serves only
women, discrimination leaves the women's market unchanged (same price `(a/θ_w + c)/2`) and opens
the men's market with `xₘ = (a − θₘc)/2 > 0` units, which adds the strictly positive surplus
`groupBenefit a θₘ xₘ − c xₘ`. -/
theorem exercise_12_B_7d_one_served {a θm c : ℝ} (hm : 0 < θm) (hmc : θm * c < a) :
    0 < groupBenefit a θm (a - θm * ((a / θm + c) / 2)) - c * (a - θm * ((a / θm + c) / 2)) := by
  unfold groupBenefit
  have e : a - θm * ((a / θm + c) / 2) = (a - θm * c) / 2 := by field_simp; ring
  rw [e]
  have h1 : 0 < a - θm * c := by linarith
  rw [show (a * ((a - θm * c) / 2) - ((a - θm * c) / 2) ^ 2 / 2) / θm - c * ((a - θm * c) / 2) =
    3 * (a - θm * c) ^ 2 / (8 * θm) by field_simp; ring]
  positivity

/-! ### Exercise 12.B.8 -/

/-- The monopolist's two-period profit with learning by doing: `c₂ = c₁ − mq₁`. -/
def lbdProfit (a b c1 m q1 q2 : ℝ) : ℝ :=
  (a - b * q1 - c1) * q1 + (a - b * q2 - (c1 - m * q1)) * q2

/-- Two-period aggregate surplus with learning by doing. -/
noncomputable def lbdWelfare (a b c1 m q1 q2 : ℝ) : ℝ :=
  (a * q1 - b * q1 ^ 2 / 2 - c1 * q1) + (a * q2 - b * q2 ^ 2 / 2 - (c1 - m * q1) * q2)

/-- **Exercise 12.B.8(a)** (MWG, p. 430). With `0 < m < b` and `a > c₁`, the monopolist
produces `q₁ = q₂ = (a − c₁)/(2b − m)`; this is its unique optimal plan, and the period-2 output
is the monopoly output `(a − c₂)/(2b)` at the learned cost `c₂ = c₁ − mq₁`. -/
theorem exercise_12_B_8a {a b c1 m : ℝ} (hm : 0 < m) (hmb : m < b) :
    (∀ q1 q2, lbdProfit a b c1 m q1 q2 ≤
      lbdProfit a b c1 m ((a - c1) / (2 * b - m)) ((a - c1) / (2 * b - m))) ∧
    (a - c1) / (2 * b - m) = (a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b) := by
  have hd : 0 < 2 * b - m := by linarith
  have hb : 0 < b := by linarith
  have hd' : 2 * b - m ≠ 0 := hd.ne'
  have hd'' : b * 2 - m ≠ 0 := by linarith
  refine ⟨fun q1 q2 => ?_, by field_simp; ring⟩
  set Q := (a - c1) / (2 * b - m) with hQ
  have key : lbdProfit a b c1 m Q Q - lbdProfit a b c1 m q1 q2 =
      b * (q1 - Q) ^ 2 + b * (q2 - Q) ^ 2 - m * (q1 - Q) * (q2 - Q) := by
    unfold lbdProfit; rw [hQ]; field_simp; ring
  nlinarith [sq_nonneg (q1 - Q - (q2 - Q)), sq_nonneg (q1 - Q + (q2 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q1 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q2 - Q)), sq_nonneg (q1 - Q), sq_nonneg (q2 - Q)]

/-- **Exercise 12.B.8(b)** (MWG, p. 430). A planner produces `q₁ = q₂ = (a − c₁)/(b − m)`
(maximizing aggregate surplus), and then the period-1 price equals marginal cost net of the
learning benefit, `p(q₁) = c₁ − mq₂`, while the period-2 price equals the period-2 cost
`c₂ = c₁ − mq₁`. -/
theorem exercise_12_B_8b {a b c1 m : ℝ} (hm : 0 < m) (hmb : m < b) :
    (∀ q1 q2, lbdWelfare a b c1 m q1 q2 ≤
      lbdWelfare a b c1 m ((a - c1) / (b - m)) ((a - c1) / (b - m))) ∧
    a - b * ((a - c1) / (b - m)) = c1 - m * ((a - c1) / (b - m)) := by
  have hd : 0 < b - m := by linarith
  have hd' : b - m ≠ 0 := hd.ne'
  refine ⟨fun q1 q2 => ?_, by field_simp; ring⟩
  set Q := (a - c1) / (b - m) with hQ
  have key : lbdWelfare a b c1 m Q Q - lbdWelfare a b c1 m q1 q2 =
      b / 2 * (q1 - Q) ^ 2 + b / 2 * (q2 - Q) ^ 2 - m * (q1 - Q) * (q2 - Q) := by
    unfold lbdWelfare; rw [hQ]; field_simp; ring
  nlinarith [sq_nonneg (q1 - Q - (q2 - Q)), mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q1 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q2 - Q))]

/-- **Exercise 12.B.8(c)** (MWG, p. 430). When the monopolist will choose the period-2 output
`(a − c₂)/(2b)` itself, the planner would like it to raise period-1 output slightly above its
choice `q₁ᵐ = (a − c₁)/(2b − m)`: welfare strictly increases for all small increases `h > 0`.
(Intuition: more period-1 output both raises period-1 surplus, since price exceeds cost, and
lowers `c₂`, which raises the monopolist's period-2 output.) -/
theorem exercise_12_B_8c {a b c1 m : ℝ} (hac : c1 < a) (hm : 0 < m) (hmb : m < b) :
    ∃ ε > 0, ∀ h, 0 < h → h < ε →
      lbdWelfare a b c1 m ((a - c1) / (2 * b - m))
          ((a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b)) <
        lbdWelfare a b c1 m ((a - c1) / (2 * b - m) + h)
          ((a - (c1 - m * ((a - c1) / (2 * b - m) + h))) / (2 * b)) := by
  have hb : 0 < b := by linarith
  have hd : 0 < 2 * b - m := by linarith
  set D := (a - c1) * b / (2 * b - m) * (1 + m / (2 * b)) with hD
  set E := (4 * b ^ 2 - 3 * m ^ 2) / (8 * b) with hE
  have hDpos : 0 < D := by
    rw [hD]; have : 0 < a - c1 := by linarith
    positivity
  have hEpos : 0 < E := by
    rw [hE]; apply div_pos _ (by positivity); nlinarith
  refine ⟨D / E, div_pos hDpos hEpos, fun h hh hε => ?_⟩
  have key : lbdWelfare a b c1 m ((a - c1) / (2 * b - m) + h)
        ((a - (c1 - m * ((a - c1) / (2 * b - m) + h))) / (2 * b)) -
      lbdWelfare a b c1 m ((a - c1) / (2 * b - m))
        ((a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b)) = h * (D - E * h) := by
    unfold lbdWelfare; rw [hD, hE]; field_simp; ring
  have : E * h < D := by rwa [lt_div_iff₀ hEpos, mul_comm] at hε
  have : 0 < h * (D - E * h) := mul_pos hh (by linarith)
  linarith

/-! ### Exercise 12.B.9 -/

/-- **Exercise 12.B.9(a)** (MWG, p. 430). If `(q, I)` with `q, I > 0` maximizes the monopolist's
profit `p(q)q − c(I)q − I` over `q, I ≥ 0`, then marginal revenue equals marginal cost,
`p'(q)q + p(q) = c(I)`, and the marginal cost saving equals the marginal investment cost,
`−c'(I)q = 1`. -/
theorem exercise_12_B_9a {p c : ℝ → ℝ} {dp dc q I : ℝ} (hq : 0 < q) (hI : 0 < I)
    (hp : HasDerivAt p dp q) (hc : HasDerivAt c dc I)
    (hmax : ∀ q' I', 0 ≤ q' → 0 ≤ I' → p q' * q' - c I' * q' - I' ≤ p q * q - c I * q - I) :
    dp * q + p q = c I ∧ -dc * q = 1 := by
  constructor
  · have hloc : IsLocalMax (fun q' => p q' * q' - c I * q' - I) q :=
      Filter.mem_of_superset (Ioi_mem_nhds hq) fun q' hq' => hmax q' I (le_of_lt hq') hI.le
    have hd : HasDerivAt (fun q' => p q' * q' - c I * q' - I) (dp * q + p q * 1 - c I * 1) q :=
      ((hp.mul (hasDerivAt_id q)).sub ((hasDerivAt_id q).const_mul (c I))).sub_const I
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · have hloc : IsLocalMax (fun I' => p q * q - c I' * q - I') I :=
      Filter.mem_of_superset (Ioi_mem_nhds hI) fun I' hI' => hmax q I' hq.le (le_of_lt hI')
    have hd : HasDerivAt (fun I' => p q * q - c I' * q - I') (0 - dc * q - 1) I :=
      (((hasDerivAt_const I (p q * q)).sub (hc.mul_const q)).sub (hasDerivAt_id I))
    have := hloc.hasDerivAt_eq_zero hd
    linarith

/-- **Exercise 12.B.9(b)** (MWG, p. 430). A first-best planner maximizes
`S(q) − c(I)q − I`, where `S' = p` is gross consumer benefit; at an interior optimum price equals
marginal cost, `p(q) = c(I)`, and `−c'(I)q = 1`. Compared with the monopolist (`p' < 0`): at the
monopolist's choice the planner's marginal welfare of output is `p(qᵐ) − c(Iᵐ) = −p'(qᵐ)qᵐ > 0`,
and since `c'' > 0` (`c'` strictly increasing), more first-best output means more first-best
investment: `qᶠᵇ > qᵐ` implies `Iᶠᵇ > Iᵐ`. -/
theorem exercise_12_B_9b {S p c c' : ℝ → ℝ} {dp qf If qm Im : ℝ} (hqf : 0 < qf) (hIf : 0 < If)
    (hS : HasDerivAt S (p qf) qf) (hc : HasDerivAt c (c' If) If)
    (hmax : ∀ q' I', 0 ≤ q' → 0 ≤ I' → S q' - c I' * q' - I' ≤ S qf - c If * qf - If)
    (hqm : 0 < qm) (hmono : StrictMono c') (hmr : dp * qm + p qm = c Im) (hdp : dp < 0)
    (hinv : -c' Im * qm = 1) :
    p qf = c If ∧ -c' If * qf = 1 ∧ 0 < p qm - c Im ∧ (qm < qf → Im < If) := by
  have h1 : p qf = c If := by
    have hloc : IsLocalMax (fun q' => S q' - c If * q' - If) qf :=
      Filter.mem_of_superset (Ioi_mem_nhds hqf) fun q' hq' => hmax q' If (le_of_lt hq') hIf.le
    have hd : HasDerivAt (fun q' => S q' - c If * q' - If) (p qf - c If * 1) qf :=
      (hS.sub ((hasDerivAt_id qf).const_mul (c If))).sub_const If
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  have h2 : -c' If * qf = 1 := by
    have hloc : IsLocalMax (fun I' => S qf - c I' * qf - I') If :=
      Filter.mem_of_superset (Ioi_mem_nhds hIf) fun I' hI' => hmax qf I' hqf.le (le_of_lt hI')
    have hd : HasDerivAt (fun I' => S qf - c I' * qf - I') (0 - c' If * qf - 1) If :=
      (((hasDerivAt_const If (S qf)).sub (hc.mul_const qf)).sub (hasDerivAt_id If))
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  refine ⟨h1, h2, by nlinarith, fun hlt => ?_⟩
  by_contra hle
  push Not at hle
  have := hmono.monotone hle
  have hcIm : c' Im < 0 := by nlinarith
  nlinarith [mul_lt_mul_of_neg_left hlt hcIm, mul_le_mul_of_nonneg_right this hqf.le]

/-- **Exercise 12.B.9(c)** (MWG, p. 430). Second best: the planner picks `I` and the monopolist
then picks `q(I)` (with `q'(Iᵐ) > 0`). The planner's welfare `V(I) = S(q(I)) − c(I)q(I) − I` has
derivative `(p(qᵐ) − c(Iᵐ))q'(Iᵐ)` at the monopolist's own choice `Iᵐ` (where `−c'(Iᵐ)qᵐ = 1`),
which is positive: the planner would invest more than the monopolist. -/
theorem exercise_12_B_9c {S p c q : ℝ → ℝ} {dc dq Im : ℝ} (hS : HasDerivAt S (p (q Im)) (q Im))
    (hc : HasDerivAt c dc Im) (hq : HasDerivAt q dq Im) (hinv : -dc * q Im = 1)
    (hmarg : c Im < p (q Im)) (hdq : 0 < dq) :
    HasDerivAt (fun I => S (q I) - c I * q I - I) ((p (q Im) - c Im) * dq) Im ∧
      0 < (p (q Im) - c Im) * dq := by
  refine ⟨?_, mul_pos (by linarith) hdq⟩
  have h := ((hS.comp Im hq).sub (hc.mul hq)).sub (hasDerivAt_id Im)
  refine h.congr_deriv ?_
  linear_combination hinv

/-! ### Exercise 12.B.10 -/

/-- **Exercise 12.B.10** (MWG, p. 430). Fix the monopolist's price `p`. Let `CS(q)` be consumer
surplus at quality `q` (strictly increasing in `q`, as `x(p, q)` is increasing in `q`; see
`consumerSurplus_strictMono`) and `π(q)` the profit. If `qᵐ` maximizes `π`, then every
welfare-maximizing quality `qˢ` (maximizing `CS + π`) satisfies `qˢ > qᵐ` or `qˢ = qᵐ`; and if
`CS` has positive derivative at `qᵐ` and `π` has derivative `0` there, `qᵐ` is not
welfare-maximizing: the monopolist does not choose the efficient quality. -/
theorem exercise_12_B_10 {CS π : ℝ → ℝ} {qm qs dCS : ℝ} (hCS : StrictMono CS)
    (hm : ∀ q, π q ≤ π qm) (hs : ∀ q, CS q + π q ≤ CS qs + π qs) :
    qm ≤ qs ∧ (HasDerivAt CS dCS qm → 0 < dCS → HasDerivAt π 0 qm →
      ¬ ∀ q, CS q + π q ≤ CS qm + π qm) := by
  refine ⟨?_, fun hd hpos hπ hmax => ?_⟩
  · by_contra hlt
    push Not at hlt
    have := hCS hlt
    linarith [hs qm, hm qs]
  · have hloc : IsLocalMax (fun q => CS q + π q) qm := Filter.Eventually.of_forall hmax
    have := hloc.hasDerivAt_eq_zero (hd.add hπ)
    linarith

/-- Consumer surplus `∫_p^{p̄} x(s, q) ds` is strictly increasing in quality when `x(s, ·)` is
increasing, strictly at some price in `[p, p̄]`, and `x(·, q)` is continuous. -/
theorem consumerSurplus_strictMono {x : ℝ → ℝ → ℝ} {p pbar q q' : ℝ} (hp : p < pbar)
    (hc : ∀ r, ContinuousOn (fun s => x s r) (Icc p pbar))
    (hle : ∀ s ∈ Ioc p pbar, x s q ≤ x s q') (hlt : ∃ s ∈ Icc p pbar, x s q < x s q') :
    ∫ s in p..pbar, x s q < ∫ s in p..pbar, x s q' :=
  intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hp (hc q) (hc q')
    hle hlt

end MWG.MarketPower
