/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExercisesC2

/-!
# Exercises 6.C.13, 6.C.14, 6.C.16 and 6.C.18

MWG, pp. 211-212. The risk-neutral firm prefers random prices (6.C.13); "strongly more risk
averse" implies the Arrow-Pratt comparison and is strictly stronger (6.C.14); selling and
buying prices of a lottery (6.C.16); square-root utility (6.C.18).

In 6.C.14 the Bernoulli utilities are defined on the line and compared pointwise; part (b)
works on `[0, ∞)` as the hint says. In 6.C.16 the lottery pays `G` with probability `p` and
`B` otherwise, and the probability in part (d) is left general by the book; we give the
selling price for every `p` and both prices at `p = 1/2`.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- The maximal profit `π(p) = max_{y ∈ Y} p · y`. -/
noncomputable def maxProfit {L : ℕ} (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : ℝ :=
  sSup ((fun y => ∑ l, p l * y l) '' Y)

/-- **Exercise 6.C.13** (MWG, p. 211). If production decisions are made after uncertain prices
are revealed, a risk-neutral firm weakly prefers the random prices to their expected value:
`π(∑ q_i P_i) ≤ ∑ q_i π(P_i)` (the profit function is convex). -/
theorem exercise_6_C_13 {L n : ℕ} (Y : Set (Fin L → ℝ)) (hY : Y.Nonempty)
    (hb : ∀ p : Fin L → ℝ, BddAbove ((fun y => ∑ l, p l * y l) '' Y)) (q : Fin n → ℝ)
    (P : Fin n → Fin L → ℝ) (hq : ∀ i, 0 ≤ q i) :
    maxProfit Y (∑ i, q i • P i) ≤ ∑ i, q i * maxProfit Y (P i) := by
  apply csSup_le (hY.image _)
  rintro _ ⟨y, hy, rfl⟩
  have e : ∑ l, (∑ i, q i • P i) l * y l = ∑ i, q i * ∑ l, P i l * y l := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  dsimp only
  rw [e]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (le_csSup (hb (P i)) ⟨y, hy, rfl⟩) (hq i)

/-- **Exercise 6.C.14(a)** (MWG, p. 211). If `u* = ku + v` with `k > 0` and `v` nonincreasing
and concave, then `u*` is more risk averse than `u` in the Arrow-Pratt sense at every `x`
where `u' > 0`, `u'' ≤ 0` and `u*' > 0`. -/
theorem exercise_6_C_14a {u v : ℝ → ℝ} {k : ℝ} (hu1 : Differentiable ℝ u)
    (hv1 : Differentiable ℝ v) (hv : Antitone v) (hvc : ConcaveOn ℝ univ v) {x : ℝ}
    (hu2 : DifferentiableAt ℝ (deriv u) x) (hv2 : ∀ y, DifferentiableAt ℝ (deriv v) y)
    (hup : 0 < deriv u x) (huc : deriv (deriv u) x ≤ 0)
    (hpos : 0 < k * deriv u x + deriv v x) :
    arrowPratt u x ≤ arrowPratt (fun y => k * u y + v y) x := by
  have hvd : deriv v x ≤ 0 := hv.deriv_nonpos
  have hvcc : deriv (deriv v) x ≤ 0 :=
    (footnote_6_16 convex_univ isOpen_univ (fun y _ => hv1 y) (fun y _ => hv2 y)).mp hvc x
      (mem_univ x)
  have hd : deriv (fun y => k * u y + v y) = fun y => k * deriv u y + deriv v y := by
    funext y
    exact (((hu1 y).hasDerivAt.const_mul k).add (hv1 y).hasDerivAt).deriv
  have hd2 : deriv (fun y => k * deriv u y + deriv v y) x =
      k * deriv (deriv u) x + deriv (deriv v) x := by
    exact ((hu2.hasDerivAt.const_mul k).add (hv2 x).hasDerivAt).deriv
  unfold arrowPratt
  rw [hd, hd2, div_le_div_iff₀ hup hpos]
  nlinarith [mul_nonneg (neg_nonneg.mpr huc) (neg_nonneg.mpr hvd), mul_nonneg
    (neg_nonneg.mpr hvcc) hup.le]

/-- **Exercise 6.C.14(b)** (MWG, p. 211). If `u` is bounded on `[0, ∞)` and `u* = ku + v` is
increasing there with `v` nonincreasing and concave, then `v` is constant: the only strongly
more risk-averse utilities are `ku + c`. -/
theorem exercise_6_C_14b {u ustar v : ℝ → ℝ} {k : ℝ} (hk : 0 < k) {B : ℝ}
    (hbd : ∀ x ≥ 0, |u x| ≤ B) (hmono : MonotoneOn ustar (Ici 0)) (hv : AntitoneOn v (Ici 0))
    (hvc : ConcaveOn ℝ (Ici 0) v) (he : ∀ x ≥ 0, ustar x = k * u x + v x) :
    ∀ x ≥ 0, v x = v 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · rw [← h0]
  by_contra hne
  have hlt : v x < v 0 := lt_of_le_of_ne (hv (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx) hne
  set s := (v x - v 0) / (x - 0)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  set T := (2 * k * B + |v x| + |v 0| + 1) / (-s)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hbd 0 le_rfl)
  have hT : 0 < T := div_pos (by positivity) (by linarith)
  set t := x + T
  have hslope := hvc.slope_anti_adjacent (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith))
    hxpos (show x < t by simp only [t]; linarith)
  have hvt : v t ≤ v x + s * T := by
    rw [div_le_iff₀ (show (0 : ℝ) < t - x by simp only [t]; linarith)] at hslope
    simp only [t] at hslope ⊢
    have : x + T - x = T := by ring
    rw [this] at hslope
    linarith
  have hs0 : s ≠ 0 := hs.ne
  have hsT : s * T = -(2 * k * B + |v x| + |v 0| + 1) := by
    simp only [T]; field_simp
  have hmt := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by simp only [t]; linarith))
    (show (0 : ℝ) ≤ t by simp only [t]; linarith)
  rw [he 0 le_rfl, he t (by simp only [t]; linarith)] at hmt
  have h1 := abs_le.mp (hbd 0 le_rfl)
  have h2 := abs_le.mp (hbd t (by simp only [t]; linarith))
  have h3 := le_abs_self (v x)
  have h4 := neg_abs_le (v 0)
  nlinarith

/-- **Exercise 6.C.14(c)** (MWG, p. 211). Being strongly more risk averse is strictly stronger
than the Arrow-Pratt comparison: `u* = -e^{-2x}` has `r_A = 2 > 1 = r_A(-e^{-x})` everywhere,
yet it is not of the form `k(-e^{-x}) + v` with `k > 0` and `v` nonincreasing and concave on
`[0, ∞)`. -/
theorem exercise_6_C_14c :
    (∀ x, arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1) x <
      arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 2) x) ∧
    ¬∃ k > 0, ∃ v : ℝ → ℝ, AntitoneOn v (Ici 0) ∧ ConcaveOn ℝ (Ici 0) v ∧
      ∀ x ≥ 0, Kreps.UtilityForMoney.ExponentialUtility 2 x =
        k * Kreps.UtilityForMoney.ExponentialUtility 1 x + v x := by
  constructor
  · intro x
    rw [arrowPratt_eq_kreps, arrowPratt_eq_kreps,
      Kreps.UtilityForMoney.absoluteRiskAversion_exponential one_ne_zero,
      Kreps.UtilityForMoney.absoluteRiskAversion_exponential two_ne_zero]
    norm_num
  · rintro ⟨k, hk, v, hv, hvc, he⟩
    have hbd : ∀ x ≥ 0, |Kreps.UtilityForMoney.ExponentialUtility 1 x| ≤ 1 := by
      intro x hx
      simp only [Kreps.UtilityForMoney.ExponentialUtility, abs_neg, neg_mul, one_mul,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hconst := exercise_6_C_14b hk hbd
      ((Kreps.UtilityForMoney.exponentialUtility_strictMono two_pos).monotone.monotoneOn _)
      hv hvc he
    have hval (x : ℝ) (hx : 0 ≤ x) : -Real.exp (-2 * x) = -k * Real.exp (-x) + v 0 := by
      have := he x hx
      rw [hconst x hx] at this
      simp only [Kreps.UtilityForMoney.ExponentialUtility] at this
      rw [this]; ring_nf
    have hl2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log two_pos, one_div]
    have hsq (t : ℝ) : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    have e0 := hval 0 le_rfl
    have e1 := hval (Real.log 2) (Real.log_nonneg (by norm_num))
    have e2 := hval (2 * Real.log 2) (by positivity)
    rw [hsq, hl2] at e1
    rw [hsq, show -(2 * Real.log 2) = -Real.log 2 + -Real.log 2 by ring, Real.exp_add, hl2]
      at e2
    simp only [mul_zero, Real.exp_zero, neg_zero] at e0
    nlinarith

/-- **Exercise 6.C.16(a)** (MWG, p. 212). The minimum selling price `s` of the lottery
(`G` with probability `p`, `B` otherwise) owned at wealth `w`: `u(w + s) = E u(w + L)`. -/
def IsSellingPrice (u : ℝ → ℝ) (w G B p s : ℝ) : Prop :=
  u (w + s) = p * u (w + G) + (1 - p) * u (w + B)

/-- **Exercise 6.C.16(b)** (MWG, p. 212). The maximum buying price `b`:
`E u(w - b + L) = u(w)`. -/
def IsBuyingPrice (u : ℝ → ℝ) (w G B p b : ℝ) : Prop :=
  p * u (w - b + G) + (1 - p) * u (w - b + B) = u w

/-- **Exercise 6.C.16(a)** (MWG, p. 212). A continuous, strictly increasing Bernoulli utility
has a unique selling price. -/
theorem exercise_6_C_16a {u : ℝ → ℝ} (hc : Continuous u) (hi : StrictMono u) (w G B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃! s, IsSellingPrice u w G B p s := by
  have hlo : u (w + min G B) ≤ p * u (w + G) + (1 - p) * u (w + B) := by
    have h1 := hi.monotone (show w + min G B ≤ w + G by linarith [min_le_left G B])
    have h2 := hi.monotone (show w + min G B ≤ w + B by linarith [min_le_right G B])
    nlinarith
  have hhi : p * u (w + G) + (1 - p) * u (w + B) ≤ u (w + max G B) := by
    have h1 := hi.monotone (show w + G ≤ w + max G B by linarith [le_max_left G B])
    have h2 := hi.monotone (show w + B ≤ w + max G B by linarith [le_max_right G B])
    nlinarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (min_le_max) (f := fun s => u (w + s))
    (by fun_prop : Continuous fun s => u (w + s)).continuousOn ⟨hlo, hhi⟩
  refine ⟨s, hs, fun t ht => ?_⟩
  have := hi.injective (ht.trans hs.symm)
  linarith

/-- **Exercise 6.C.16(b)** (MWG, p. 212). A continuous, strictly increasing Bernoulli utility
has a unique buying price. -/
theorem exercise_6_C_16b {u : ℝ → ℝ} (hc : Continuous u) (hi : StrictMono u) (w G B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃! b, IsBuyingPrice u w G B p b := by
  let g := fun b : ℝ => p * u (w - b + G) + (1 - p) * u (w - b + B)
  have hg : Continuous g := by simp only [g]; fun_prop
  have hanti : StrictAnti g := by
    intro b b' hbb
    simp only [g]
    have h1 := hi (show w - b' + G < w - b + G by linarith)
    have h2 := hi (show w - b' + B < w - b + B by linarith)
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; nlinarith
    · nlinarith
  have hlo : g (max G B) ≤ u w := by
    simp only [g]
    have h1 := hi.monotone (show w - max G B + G ≤ w by linarith [le_max_left G B])
    have h2 := hi.monotone (show w - max G B + B ≤ w by linarith [le_max_right G B])
    nlinarith
  have hhi : u w ≤ g (min G B) := by
    simp only [g]
    have h1 := hi.monotone (show w ≤ w - min G B + G by linarith [min_le_left G B])
    have h2 := hi.monotone (show w ≤ w - min G B + B by linarith [min_le_right G B])
    nlinarith
  obtain ⟨b, -, hb⟩ := intermediate_value_Icc' min_le_max hg.continuousOn ⟨hlo, hhi⟩
  exact ⟨b, hb, fun t ht => hanti.injective (ht.trans hb.symm)⟩

/-- **Exercise 6.C.16(c)** (MWG, p. 212). Buying and selling prices coincide under constant
absolute risk aversion `u(x) = -e^{-ax}`, `a > 0` (no wealth effect on risk attitudes). -/
theorem exercise_6_C_16c_cara {a : ℝ} (ha : 0 < a) {w G B p s b : ℝ}
    (hs : IsSellingPrice (Kreps.UtilityForMoney.ExponentialUtility a) w G B p s)
    (hb : IsBuyingPrice (Kreps.UtilityForMoney.ExponentialUtility a) w G B p b) : s = b := by
  unfold IsSellingPrice IsBuyingPrice Kreps.UtilityForMoney.ExponentialUtility at *
  set M := p * Real.exp (-a * G) + (1 - p) * Real.exp (-a * B)
  have k0 (t : ℝ) : Real.exp (-a * (w + t)) = Real.exp (-a * w) * Real.exp (-a * t) := by
    rw [← Real.exp_add]; ring_nf
  have k1 (t : ℝ) : Real.exp (-a * (w - b + t)) =
      Real.exp (-a * w) * (Real.exp (a * b) * Real.exp (-a * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [k0, k0, k0] at hs
  rw [k1, k1] at hb
  have hw := (Real.exp_pos (-a * w)).ne'
  have h1 : Real.exp (-a * w) * (Real.exp (-a * s) - M) = 0 := by
    simp only [M]; linear_combination (-1 : ℝ) * hs
  have h2 : Real.exp (-a * w) * (Real.exp (a * b) * M - 1) = 0 := by
    simp only [M]; linear_combination (-1 : ℝ) * hb
  have hsM : Real.exp (-a * s) = M := by
    have := (mul_eq_zero.mp h1).resolve_left hw; linarith
  have hbM : Real.exp (a * b) * M = 1 := by
    have := (mul_eq_zero.mp h2).resolve_left hw; linarith
  rw [← hsM, ← Real.exp_add, Real.exp_eq_one_iff] at hbM
  have : a * (b - s) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **Exercise 6.C.16(c)** (MWG, p. 212). For a riskless lottery (`G = B`) buying and selling
prices coincide (both equal `G`) for every strictly increasing `u`. -/
theorem exercise_6_C_16c_riskless {u : ℝ → ℝ} (hi : StrictMono u) {w G p s b : ℝ}
    (hs : IsSellingPrice u w G G p s) (hb : IsBuyingPrice u w G G p b) : s = G ∧ b = G := by
  unfold IsSellingPrice IsBuyingPrice at *
  constructor
  · have : u (w + s) = u (w + G) := by rw [hs]; ring
    have := hi.injective this; linarith
  · have : u (w - b + G) = u w := by rw [← hb]; ring
    have := hi.injective this; linarith

/-- Square-root facts used in Exercises 6.C.16(d) and 6.C.18. -/
theorem sqrt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : Real.sqrt a = b := by
  rw [h, Real.sqrt_sq hb]

/-- **Exercise 6.C.16(d)** (MWG, p. 212). With `G = 10`, `B = 5`, `w = 10`, `u(x) = √x`, the
selling price is `s = (p√20 + (1 - p)√15)² - 10` for every `p ∈ [0,1]`; at `p = 1/2` it is
`5√3 - 5/4`, the buying price is `235/32`, and the buying price is strictly lower. -/
theorem exercise_6_C_16d :
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → IsSellingPrice Real.sqrt 10 10 5 p
      ((p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 - 10)) ∧
    IsSellingPrice Real.sqrt 10 10 5 (1 / 2) (5 * Real.sqrt 3 - 5 / 4) ∧
    IsBuyingPrice Real.sqrt 10 10 5 (1 / 2) (235 / 32) ∧
    (235 / 32 : ℝ) < 5 * Real.sqrt 3 - 5 / 4 := by
  have h20 := Real.sqrt_nonneg 20
  have h15 := Real.sqrt_nonneg 15
  have h3 := Real.sqrt_nonneg 3
  have s20 := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
  have s15 := Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)
  have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hprod : Real.sqrt 20 * Real.sqrt 15 = 10 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact sqrt_of_sq (by positivity) (by nlinarith)
  refine ⟨fun p hp0 hp1 => ?_, ?_, ?_, ?_⟩
  · unfold IsSellingPrice
    rw [show (10 : ℝ) + ((p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 - 10) =
      (p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 by ring,
      Real.sqrt_sq (by nlinarith)]
    norm_num
  · unfold IsSellingPrice
    rw [sqrt_of_sq (b := (Real.sqrt 20 + Real.sqrt 15) / 2) (by positivity) (by nlinarith)]
    norm_num; ring
  · unfold IsBuyingPrice
    have h10 := Real.sqrt_nonneg 10
    have s10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
    have h405 : Real.sqrt (10 - 235 / 32 + 10) = 9 * Real.sqrt 10 / 8 :=
      sqrt_of_sq (by positivity) (by nlinarith)
    have h245 : Real.sqrt (10 - 235 / 32 + 5) = 7 * Real.sqrt 10 / 8 :=
      sqrt_of_sq (by positivity) (by nlinarith)
    rw [h405, h245]
    ring
  · nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1.71875)]

/-- The Arrow-Pratt coefficient of `√x` is `1/(2x)` on `x > 0`. -/
theorem arrowPratt_sqrt {x : ℝ} (hx : 0 < x) : arrowPratt Real.sqrt x = 1 / (2 * x) := by
  have hd : deriv Real.sqrt =ᶠ[𝓝 x] fun y => 1 / (2 * Real.sqrt y) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (Real.hasDerivAt_sqrt hy.ne').deriv
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h2 : HasDerivAt (fun y => 1 / (2 * Real.sqrt y))
      ((0 * (2 * Real.sqrt x) - 1 * (2 * (1 / (2 * Real.sqrt x)))) / (2 * Real.sqrt x) ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2) (by positivity)
  unfold arrowPratt
  rw [hd.deriv_eq, h2.deriv, (Real.hasDerivAt_sqrt hx.ne').deriv]
  have := Real.sq_sqrt hx.le
  field_simp
  nlinarith

/-- **Exercise 6.C.18(a)** (MWG, p. 212). For `u(x) = √x` at wealth `5`, `r_A = 1/10` and
`r_R = 1/2`. -/
theorem exercise_6_C_18a :
    arrowPratt Real.sqrt 5 = 1 / 10 ∧ relativeRiskAversion Real.sqrt 5 = 1 / 2 := by
  have h := arrowPratt_sqrt (show (0 : ℝ) < 5 by norm_num)
  refine ⟨by rw [h]; norm_num, by rw [relativeRiskAversion, h]; norm_num⟩

/-- **Exercise 6.C.18(b)** (MWG, p. 212). For the gamble `(16, 4; 1/2, 1/2)`: the certainty
equivalent is `9` and the probability premium at the mean `10` is `(√10 - 3)/2`. -/
theorem exercise_6_C_18b :
    Real.sqrt 9 = (Real.sqrt 16 + Real.sqrt 4) / 2 ∧
      probPremium Real.sqrt 10 6 = (Real.sqrt 10 - 3) / 2 := by
  have e9 : Real.sqrt 9 = 3 := sqrt_of_sq (by norm_num) (by norm_num)
  have e16 : Real.sqrt 16 = 4 := sqrt_of_sq (by norm_num) (by norm_num)
  have e4 : Real.sqrt 4 = 2 := sqrt_of_sq (by norm_num) (by norm_num)
  refine ⟨by rw [e9, e16, e4]; norm_num, ?_⟩
  unfold probPremium
  rw [show (10 : ℝ) + 6 = 16 by norm_num, show (10 : ℝ) - 6 = 4 by norm_num, e16, e4]
  ring

/-- **Exercise 6.C.18(c)** (MWG, p. 212). For `(36, 16; 1/2, 1/2)`: the certainty equivalent is
`25` and the probability premium is `(√26 - 5)/2`. Compared with (b), the risk premium
(mean minus certainty equivalent) is `1` in both, while the probability premium is smaller at
the higher wealth (decreasing absolute risk aversion). -/
theorem exercise_6_C_18c :
    Real.sqrt 25 = (Real.sqrt 36 + Real.sqrt 16) / 2 ∧
      probPremium Real.sqrt 26 10 = (Real.sqrt 26 - 5) / 2 ∧
      (10 : ℝ) - 9 = 26 - 25 ∧ (Real.sqrt 26 - 5) / 2 < (Real.sqrt 10 - 3) / 2 := by
  have e25 : Real.sqrt 25 = 5 := sqrt_of_sq (by norm_num) (by norm_num)
  have e36 : Real.sqrt 36 = 6 := sqrt_of_sq (by norm_num) (by norm_num)
  have e16 : Real.sqrt 16 = 4 := sqrt_of_sq (by norm_num) (by norm_num)
  refine ⟨by rw [e25, e36, e16]; norm_num, ?_, by norm_num, ?_⟩
  · unfold probPremium
    rw [show (26 : ℝ) + 10 = 36 by norm_num, show (26 : ℝ) - 10 = 16 by norm_num, e36, e16]
    ring
  · have h26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
    have h10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
    nlinarith [Real.sqrt_nonneg 26, Real.sqrt_nonneg 10, sq_nonneg (Real.sqrt 26 - 5.1),
      sq_nonneg (Real.sqrt 10 - 3.16)]

end MWG.ChoiceUnderUncertainty
