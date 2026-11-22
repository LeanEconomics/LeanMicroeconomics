/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Zigger
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exercise 8.E.2: the first-price auction with uniform private values

MWG, Exercise 8.E.2, p. 265.

Each of `I = n + 1` bidders knows only his own valuation, drawn uniformly and independently from
`[0, v̄]`; bids are any real numbers, the highest bid wins and pays its bid. As in Example 8.E.2
(module `Zigger`) the continuum of types is handled type by type: when every rival bids
`s(x) = βx`, a single rival bids below `b` with probability `fpBelow v̄ β b`, the Lebesgue measure
of `{x ∈ [0, v̄] : βx < b}` divided by `v̄`; ties have probability zero (`fpTie_zero`); and a
bidder with value `v` who bids `b` against `n` independent rivals expects
`fpExp v̄ β n v b = (v - b) · fpBelow v̄ β b ^ n`.

* `fpBelow_eq`: `fpBelow v̄ β b = min(1, b/(βv̄))` for `b ≥ 0`, and `0` for `b ≤ 0`.
* `fp_core`: the inequality `(v - b) (b (n + 1)/n)^n ≤ v^{n+1}/(n + 1)` for `b ≥ 0`, from
  Bernoulli's inequality (an AM-GM step).
* **Exercise 8.E.2(b)** (`exercise_8_E_2b`): with `I = n + 1 ≥ 2` bidders, the linear rule
  `s(v) = ((I - 1)/I) v` is a symmetric Bayesian Nash equilibrium: against rivals using it, every
  type's bid `((I - 1)/I) v` maximizes `fpExp` over all real bids.
* **Exercise 8.E.2(a)** (`exercise_8_E_2a`): two bidders bid half their valuation.
* As `I → ∞` the equilibrium bid `((I - 1)/I) v` increases to `v` (`exercise_8_E_2b_limit`,
  `exercise_8_E_2b_mono`).
-/

namespace MWG.SimultaneousMoveGames

open MeasureTheory Filter Topology

/-- The probability that a rival with valuation uniform on `[0, v̄]` who bids `βx` bids below
`b`. -/
noncomputable def fpBelow (vbar β b : ℝ) : ℝ :=
  (volume (Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b})).toReal / vbar

/-- **Exercise 8.E.2** (MWG, p. 265). The expected payoff of a bidder with valuation `v` who bids
`b` when each of his `n` rivals bids `βx` at valuation `x`: he wins (paying `b`) iff all rivals bid
less, with probability `fpBelow v̄ β b ^ n` by independence. -/
noncomputable def fpExp (vbar β : ℝ) (n : ℕ) (v b : ℝ) : ℝ := (v - b) * fpBelow vbar β b ^ n

/-- Ties have probability zero: `{x : βx = b}` is a single point. -/
theorem fpTie_zero {β : ℝ} (hβ : 0 < β) (vbar b : ℝ) :
    volume (Set.Icc (0 : ℝ) vbar ∩ {x | β * x = b}) = 0 := by
  refine measure_mono_null (t := {b / β}) (fun x hx => ?_) (measure_singleton _)
  rw [Set.mem_singleton_iff, eq_div_iff hβ.ne', mul_comm]
  exact hx.2

/-- `fpBelow v̄ β b = min(1, b/(βv̄))` for `b ≥ 0`. -/
theorem fpBelow_eq {vbar β b : ℝ} (hv : 0 < vbar) (hβ : 0 < β) (hb : 0 ≤ b) :
    fpBelow vbar β b = min 1 (b / (β * vbar)) := by
  unfold fpBelow
  rcases le_or_gt b (β * vbar) with hle | hgt
  · have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = Set.Ico 0 (b / β) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_Ico]
      rw [lt_div_iff₀ hβ, mul_comm x β]
      constructor
      · rintro ⟨⟨h0, -⟩, h⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩
        refine ⟨⟨h0, ?_⟩, h⟩
        by_contra hx
        push Not at hx
        nlinarith
    rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (div_nonneg hb hβ.le),
      min_eq_right ((div_le_one (by positivity)).2 hle), div_div]
  · have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = Set.Icc 0 vbar := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, by nlinarith [h.2]⟩
    rw [hset, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hv.le, div_self hv.ne',
      min_eq_left ((one_le_div (by positivity)).2 hgt.le)]

/-- Nobody bids below a nonpositive amount. -/
theorem fpBelow_nonpos {vbar β b : ℝ} (hβ : 0 < β) (hb : b ≤ 0) : fpBelow vbar β b = 0 := by
  unfold fpBelow
  have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]
    intro h0
    nlinarith [h0.1]
  rw [hset, measure_empty, ENNReal.toReal_zero, zero_div]

/-- Bernoulli's inequality in the form `(1 + n(1 - u)) uⁿ ≤ 1` for `u ≥ 0`. -/
theorem fp_bernoulli (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1 + n * (1 - u)) * u ^ n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt (1 + n * (1 - u)) 0 with hneg | hpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hneg (pow_nonneg hu n)).trans zero_le_one
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hu2 : u ≤ 2 := by
      by_contra h
      push Not at h
      nlinarith
    have hb := one_add_mul_le_pow (a := 1 - u) (by linarith) n
    calc (1 + n * (1 - u)) * u ^ n ≤ (1 + (1 - u)) ^ n * u ^ n :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg hu n)
      _ = ((2 - u) * u) ^ n := by rw [mul_pow]; ring
      _ ≤ 1 := pow_le_one₀ (mul_nonneg (by linarith) hu) (by nlinarith [sq_nonneg (u - 1)])

/-- The core inequality: with `n ≥ 1` rivals, `(v - b) (b (n + 1)/n)ⁿ ≤ (v/(n + 1)) vⁿ` for
`v, b ≥ 0`; equality at `b = (n/(n + 1)) v`. -/
theorem fp_core {n : ℕ} (hn : 1 ≤ n) {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) :
    (v - b) * (b * (n + 1) / n) ^ n ≤ v / (n + 1) * v ^ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases hv.eq_or_lt with rfl | hvp
  · have : 0 ≤ (b * (n + 1) / n) ^ n := pow_nonneg (by positivity) n
    simp only [zero_sub, zero_div, zero_mul]
    nlinarith
  · set u := b * (n + 1) / (n * v) with hu
    have hu0 : 0 ≤ u := by positivity
    have hbu : b * (n + 1) / n = v * u := by
      rw [hu]; field_simp
    have hvb : v - b = v / (n + 1) * (1 + n * (1 - u)) := by
      rw [hu]; field_simp; ring
    rw [hbu, hvb, mul_pow]
    have key := fp_bernoulli n hu0
    have hpos : 0 ≤ v / (n + 1) * v ^ n := by positivity
    calc v / (↑n + 1) * (1 + ↑n * (1 - u)) * (v ^ n * u ^ n)
        = v / (↑n + 1) * v ^ n * ((1 + ↑n * (1 - u)) * u ^ n) := by ring
      _ ≤ v / (↑n + 1) * v ^ n * 1 := mul_le_mul_of_nonneg_left key hpos
      _ = v / (↑n + 1) * v ^ n := mul_one _

/-- **Exercise 8.E.2(b)** (MWG, p. 265). With `I = n + 1 ≥ 2` bidders whose valuations are
uniform on `[0, v̄]`, the linear bid function `s(v) = (n/(n + 1)) v = ((I - 1)/I) v` is a symmetric
Bayesian Nash equilibrium: when every rival uses it, a bidder of any type `v ∈ [0, v̄]` maximizes
his expected payoff over all real bids `b` by bidding `s(v)`. -/
theorem exercise_8_E_2b {vbar : ℝ} (hvbar : 0 < vbar) {n : ℕ} (hn : 1 ≤ n) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ vbar) (b : ℝ) :
    fpExp vbar (n / (n + 1)) n v b ≤ fpExp vbar (n / (n + 1)) n v (n / (n + 1) * v) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := n / (n + 1) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β < 1 := by rw [hβ, div_lt_one (by positivity)]; linarith
  -- the equilibrium payoff
  have hstar : fpExp vbar β n v (β * v) = v / (n + 1) * (v / vbar) ^ n := by
    unfold fpExp
    rw [fpBelow_eq hvbar hβ0 (by positivity)]
    rw [min_eq_right]
    · rw [mul_div_mul_left _ _ hβ0.ne', hβ]
      field_simp
      ring
    · rw [mul_div_mul_left _ _ hβ0.ne', div_le_one hvbar]; exact hv1
  have hRHS0 : 0 ≤ v / (n + 1) * (v / vbar) ^ n := by positivity
  rw [hstar]
  unfold fpExp
  rcases le_or_gt b 0 with hb | hb
  · rw [fpBelow_nonpos hβ0 hb, zero_pow (by omega), mul_zero]
    exact hRHS0
  -- the core inequality, divided by `v̄ⁿ`
  have hcore : ∀ b', 0 ≤ b' → (v - b') * (b' / (β * vbar)) ^ n ≤ v / (n + 1) * (v / vbar) ^ n := by
    intro b' hb'
    have := fp_core hn hv0 hb'
    have hvn : 0 < vbar ^ n := pow_pos hvbar n
    have e1 : (b' / (β * vbar)) ^ n = (b' * (n + 1) / n) ^ n / vbar ^ n := by
      rw [← div_pow]; congr 1; rw [hβ]; field_simp
    have e2 : (v / vbar) ^ n = v ^ n / vbar ^ n := div_pow _ _ _
    rw [e1, e2, ← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right this hvn.le
  rw [fpBelow_eq hvbar hβ0 hb.le]
  rcases le_or_gt b (β * vbar) with hle | hgt
  · rw [min_eq_right ((div_le_one (by positivity)).2 hle)]
    exact hcore b hb.le
  · rw [min_eq_left ((one_le_div (by positivity)).2 hgt.le), one_pow, mul_one]
    have := hcore (β * vbar) (by positivity)
    rw [div_self (by positivity), one_pow, mul_one] at this
    linarith

/-- **Exercise 8.E.2(a)** (MWG, p. 265). With two bidders, bidding half one's valuation,
`s(v) = v/2`, is a symmetric Bayesian Nash equilibrium. -/
theorem exercise_8_E_2a {vbar : ℝ} (hvbar : 0 < vbar) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ vbar)
    (b : ℝ) : fpExp vbar (1 / 2) 1 v b ≤ fpExp vbar (1 / 2) 1 v (v / 2) := by
  convert exercise_8_E_2b hvbar (n := 1) le_rfl hv0 hv1 b using 3 <;> norm_num
  ring

/-- **Exercise 8.E.2(b)** (MWG, p. 265). As the number of bidders `I` grows, each bidder's
equilibrium bid `((I - 1)/I) v` converges to his valuation `v`. -/
theorem exercise_8_E_2b_limit (v : ℝ) :
    Tendsto (fun I : ℕ => ((I : ℝ) - 1) / I * v) atTop (𝓝 v) := by
  have h : Tendsto (fun I : ℕ => (1 : ℝ) - 1 / I) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h
  have h2 := h.mul_const v
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with I hI
  have : (I : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exercise 8.E.2(b)** (MWG, p. 265). The equilibrium bid `((I - 1)/I) v` is increasing in the
number of bidders `I`. -/
theorem exercise_8_E_2b_mono {v : ℝ} (hv : 0 ≤ v) {I J : ℕ} (hI : 1 ≤ I) (hIJ : I ≤ J) :
    ((I : ℝ) - 1) / I * v ≤ ((J : ℝ) - 1) / J * v := by
  have hI' : (1 : ℝ) ≤ I := by exact_mod_cast hI
  have hIJ' : (I : ℝ) ≤ J := by exact_mod_cast hIJ
  apply mul_le_mul_of_nonneg_right _ hv
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end MWG.SimultaneousMoveGames
