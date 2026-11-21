/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.LinearCity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The linear city with nonpurchase

MWG, Example 12.C.2 (pp. 396-398) without the assumption `v > c + 3t`: the small type on p. 398,
Figure 12.C.6(a), and the best-response analysis behind Exercises 12.C.13 and 12.C.14.

A consumer at `z ∈ [0, 1]` buys from firm 1 iff `v − p₁ − tz > 0` and
`p₁ + tz < p₂ + t(1 − z)`, i.e. iff `z < min{(v − p₁)/t, ẑ}` (`lcv_buys_iff`). Firm 1's share of the
`M` consumers is the length of that set, `max{0, min{1, (v − p₁)/t, ẑ}}` (`lcvShare`,
`lcvShare_spec`); firm 2's is `lcvShare v t p₂ p₁`. `lcvProfit` is `(p₁ − c)M·share`.

Firm 1's profit is bounded above, for `p₁ ≥ c`, by `M·max{0, (p₁ − c)L(p₁)}` for each of
`L ∈ {1, (v − p₁)/t, ẑ}` (`lcv_le_one`, `lcv_le_A`, `lcv_le_B`). Combining these bounds gives the
unique best response on each region of the rival's price:

* `lcvBR_low`: `p₂ ≤ c − t`: no price earns a positive profit;
* `lcvBR_duo`: interior duopoly `(t + p₂ + c)/2` (the middle line of (12.C.12));
* `lcvBR_kink`: the kink `2v − t − p₂`, where the indifferent consumer gets zero surplus;
* `lcvBR_mono`: the local monopoly price `(v + c)/2`;
* `lcvBR_cover`: the price `v − t` that just covers the firm's whole side of the market;
* `lcvBR_capture`: the price `p₂ − t` that captures the whole market.

`lcvBRLow` (for `c < v ≤ c + 2t`), `lcvBRMid` (for `c + 2t ≤ v < c + 3t`) and `lcvBRHigh` (for
`v ≥ c + 3t`) assemble these into best-response functions (`lcvBRLow_spec`, `lcvBRMid_spec`,
`lcvBRHigh_spec`), and every Nash equilibrium has both prices at least `c` (`lcvNash_ge_c`).
-/

namespace MWG.MarketPower

open MeasureTheory

/-- Firm 1's share of the market in the linear city with nonpurchase: the length of the set of
consumers `z ∈ [0, 1]` with `z < min{(v − p₁)/t, ẑ}`. -/
noncomputable def lcvShare (v t p1 p2 : ℝ) : ℝ :=
  max 0 (min 1 (min ((v - p1) / t) (lcHat t p1 p2)))

/-- Firm 1's profit `(p₁ − c)M·share` in the linear city with nonpurchase. -/
noncomputable def lcvProfit (v t M c p1 p2 : ℝ) : ℝ := (p1 - c) * (M * lcvShare v t p1 p2)

/-- A Nash equilibrium of the linear city with nonpurchase. -/
def IsLCVNash (v t M c p1 p2 : ℝ) : Prop :=
  (∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) ∧
    ∀ q, lcvProfit v t M c q p1 ≤ lcvProfit v t M c p2 p1

/-- `ps` is the unique best response to `p₂`, and it earns a strictly positive profit. -/
def IsLCVUniqueBR (v t M c p2 ps : ℝ) : Prop :=
  0 < lcvProfit v t M c ps p2 ∧ ∀ p, p ≠ ps → lcvProfit v t M c p p2 < lcvProfit v t M c ps p2

/-- **Figure 12.C.6** (MWG, pp. 396-397). A consumer at `z` buys from firm 1 (positive surplus,
and strictly cheaper than firm 2) iff `z < min{(v − p₁)/t, ẑ}`. -/
theorem lcv_buys_iff {v t p1 p2 z : ℝ} (ht : 0 < t) :
    (0 < v - p1 - t * z ∧ p1 + t * z < p2 + t * (1 - z)) ↔
      z < min ((v - p1) / t) (lcHat t p1 p2) := by
  rw [lt_min_iff, ← linearCity_prefers ht, lt_div_iff₀ ht]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

/-- The length of `{z ∈ [0, 1] : z < m}` is `max{0, min{1, m}}`. -/
theorem volume_unit_inter_Iio (m : ℝ) :
    volume (Set.Icc (0 : ℝ) 1 ∩ Set.Iio m) = ENNReal.ofReal (max 0 (min 1 m)) := by
  rcases le_or_gt m 1 with h | h
  · have hs : Set.Icc (0 : ℝ) 1 ∩ Set.Iio m = Set.Ico 0 m := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h0, _⟩, hm⟩; exact ⟨h0, hm⟩
      · rintro ⟨h0, hm⟩; exact ⟨⟨h0, by linarith⟩, hm⟩
    rw [hs, Real.volume_Ico, sub_zero, min_eq_right h]
    rcases le_total m 0 with h0 | h0
    · rw [max_eq_left h0, ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_zero]
    · rw [max_eq_right h0]
  · have hs : Set.Icc (0 : ℝ) 1 ∩ Set.Iio m = Set.Icc 0 1 := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio]
      constructor
      · rintro ⟨hz, _⟩; exact hz
      · rintro ⟨h0, h1⟩; exact ⟨⟨h0, h1⟩, by linarith⟩
    rw [hs, Real.volume_Icc, sub_zero, min_eq_left h.le, max_eq_right zero_le_one]

/-- **Firm 1's demand with nonpurchase** (MWG, pp. 396-397): the set of consumers buying from
firm 1, `{z ∈ [0, 1] : z < min{(v − p₁)/t, ẑ}}`, has length `lcvShare v t p₁ p₂`. -/
theorem lcvShare_spec (v t p1 p2 : ℝ) :
    volume (Set.Icc (0 : ℝ) 1 ∩ Set.Iio (min ((v - p1) / t) (lcHat t p1 p2))) =
      ENNReal.ofReal (lcvShare v t p1 p2) :=
  volume_unit_inter_Iio _

/-- Firm 2's indifferent-consumer share is `1 − ẑ`. -/
theorem lcHat_symm {t p1 p2 : ℝ} (ht : 0 < t) : lcHat t p2 p1 = 1 - lcHat t p1 p2 := by
  unfold lcHat; field_simp; ring

theorem lcvShare_nonneg (v t p1 p2 : ℝ) : 0 ≤ lcvShare v t p1 p2 := le_max_left _ _

/-- Computing the share: if `s ∈ [0, 1]` is at most `(v − p₁)/t` and `ẑ` and equals one of
`1, (v − p₁)/t, ẑ`, the share is `s`. -/
theorem lcvShare_eq_of {v t p1 p2 s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hA : s ≤ (v - p1) / t)
    (hB : s ≤ lcHat t p1 p2) (hatt : s = 1 ∨ s = (v - p1) / t ∨ s = lcHat t p1 p2) :
    lcvShare v t p1 p2 = s := by
  unfold lcvShare
  have hmin : min 1 (min ((v - p1) / t) (lcHat t p1 p2)) = s := by
    refine le_antisymm ?_ (le_min hs1 (le_min hA hB))
    rcases hatt with h | h | h
    · rw [← h]; exact min_le_left _ _
    · rw [h]; exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [h]; exact (min_le_right _ _).trans (min_le_right _ _)
  rw [hmin, max_eq_right hs0]

/-- The share is zero when `ẑ ≤ 0`. -/
theorem lcvShare_eq_zero {v t p1 p2 : ℝ} (h : lcHat t p1 p2 ≤ 0) : lcvShare v t p1 p2 = 0 := by
  unfold lcvShare
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans h))

/-- A firm pricing below cost earns at most zero. -/
theorem lcv_le_zero_of_lt {v t M c p p2 : ℝ} (hM : 0 ≤ M) (h : p < c) :
    lcvProfit v t M c p p2 ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hM (lcvShare_nonneg _ _ _ _))

theorem lcv_mul_le {a s L : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hsL : s ≤ max 0 L) :
    a * s ≤ max 0 (a * L) := by
  rcases le_total L 0 with h | h
  · rw [max_eq_left h] at hsL
    rw [le_antisymm hsL hs, mul_zero]; exact le_max_left _ _
  · rw [max_eq_right h] at hsL
    exact (mul_le_mul_of_nonneg_left hsL ha).trans (le_max_right _ _)

theorem lcv_le_of_share {v t M c p p2 L : ℝ} (hM : 0 ≤ M) (hp : c ≤ p)
    (hL : lcvShare v t p p2 ≤ max 0 L) : lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * L) := by
  unfold lcvProfit
  have := lcv_mul_le (sub_nonneg.2 hp) (lcvShare_nonneg v t p p2) hL
  calc (p - c) * (M * lcvShare v t p p2) = M * ((p - c) * lcvShare v t p p2) := by ring
    _ ≤ M * max 0 ((p - c) * L) := mul_le_mul_of_nonneg_left this hM

/-- Bound by the full-coverage piece `L = 1`. -/
theorem lcv_le_one {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * 1) :=
  lcv_le_of_share hM hp (max_le_max le_rfl (min_le_left _ _))

/-- Bound by the local-monopoly piece `L = (v − p)/t`. -/
theorem lcv_le_A {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * ((v - p) / t)) :=
  lcv_le_of_share hM hp (max_le_max le_rfl ((min_le_right _ _).trans (min_le_left _ _)))

/-- Bound by the duopoly piece `L = ẑ`. -/
theorem lcv_le_B {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * lcHat t p p2) :=
  lcv_le_of_share hM hp (max_le_max le_rfl ((min_le_right _ _).trans (min_le_right _ _)))

/-- The unique best response from the piecewise bounds. -/
theorem lcv_uniqueBR_of {v t M c p2 ps T : ℝ} (hM : 0 < M) (hT : 0 < T)
    (hval : lcvProfit v t M c ps p2 = M * T)
    (hb : ∀ p, c ≤ p → p ≠ ps →
      (p - c) * 1 < T ∨ (p - c) * ((v - p) / t) < T ∨ (p - c) * lcHat t p p2 < T) :
    IsLCVUniqueBR v t M c p2 ps := by
  refine ⟨by rw [hval]; positivity, fun p hp => ?_⟩
  rw [hval]
  rcases lt_or_ge p c with h | h
  · exact lt_of_le_of_lt (lcv_le_zero_of_lt hM.le h) (by positivity)
  · rcases hb p h hp with h1 | h1 | h1
    · exact lt_of_le_of_lt (lcv_le_one hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)
    · exact lt_of_le_of_lt (lcv_le_A hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)
    · exact lt_of_le_of_lt (lcv_le_B hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)

/-- A unique best response is the only maximizer. -/
theorem lcv_eq_of_uniqueBR {v t M c p2 ps p1 : ℝ} (h : IsLCVUniqueBR v t M c p2 ps)
    (hmax : ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) : p1 = ps := by
  by_contra hne
  linarith [h.2 p1 hne, hmax ps]

theorem lcv_max_of_uniqueBR {v t M c p2 ps : ℝ} (h : IsLCVUniqueBR v t M c p2 ps) :
    ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c ps p2 := fun q => by
  by_cases hq : q = ps
  · rw [hq]
  · exact (h.2 q hq).le

/-- Two unique best responses to each other form a Nash equilibrium. -/
theorem lcvNash_of_BR {v t M c p1 p2 : ℝ} (h1 : IsLCVUniqueBR v t M c p2 p1)
    (h2 : IsLCVUniqueBR v t M c p1 p2) : IsLCVNash v t M c p1 p2 :=
  ⟨lcv_max_of_uniqueBR h1, lcv_max_of_uniqueBR h2⟩

/-! ### Best responses on the regions of the rival's price -/

/-- **Best response, `p₂ ≤ c − t`** (MWG, (12.C.12), with nonpurchase). No price earns a positive
profit; the price `c` earns zero. -/
theorem lcvBR_low {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h : p2 ≤ c - t) :
    lcvProfit v t M c c p2 = 0 ∧ ∀ p, lcvProfit v t M c p p2 ≤ 0 := by
  refine ⟨by unfold lcvProfit; ring, fun p => ?_⟩
  rcases lt_or_ge p c with hp | hp
  · exact lcv_le_zero_of_lt hM.le hp
  · refine (lcv_le_B hM.le hp).trans ?_
    have : lcHat t p p2 ≤ 0 := by
      unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by linarith) this), mul_zero]

/-- **Best response, interior duopoly** (MWG, (12.C.12), middle line). If `c − t < p₂ < c + 3t`
and `3p₂ ≤ 4v − 3t − c` (the indifferent consumer then gets positive surplus), the unique best
response is `(t + p₂ + c)/2`, with share `(t + p₂ − c)/(4t)`. -/
theorem lcvBR_duo {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p2)
    (h2 : p2 < c + 3 * t) (h3 : 3 * p2 ≤ 4 * v - 3 * t - c) :
    lcvShare v t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) ∧
      IsLCVUniqueBR v t M c p2 ((t + p2 + c) / 2) := by
  have hs : lcvShare v t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]; linarith
    · rw [div_le_div_iff₀ (by positivity) ht]; nlinarith
    · unfold lcHat; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · right; right; unfold lcHat; field_simp; ring
  refine ⟨hs, lcv_uniqueBR_of (T := (t + p2 - c) ^ 2 / (8 * t)) hM
    (div_pos (pow_pos (by linarith) 2) (by positivity)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; field_simp; ring
  · right; right
    have key : (t + p2 - c) ^ 2 / (8 * t) - (p - c) * lcHat t p p2 =
        (p - (t + p2 + c) / 2) ^ 2 / (2 * t) := by unfold lcHat; field_simp; ring
    have hne : p - (t + p2 + c) / 2 ≠ 0 := sub_ne_zero.2 hp
    have : 0 < (p - (t + p2 + c) / 2) ^ 2 / (2 * t) := by positivity
    linarith

/-- **Best response at the kink** (MWG, p. 398 small type). If `v − t < p₂ ≤ v`,
`(v + c)/2 ≤ α ≤ (t + p₂ + c)/2`, where `α = 2v − t − p₂`, the unique best response is
`α`: the indifferent consumer `ẑ` gets zero surplus. The share is `(p₂ + t − v)/t`. -/
theorem lcvBR_kink {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : v - t < p2) (h2 : p2 ≤ v)
    (h3 : v + c ≤ 2 * (2 * v - t - p2)) (h4 : 2 * (2 * v - t - p2) ≤ t + p2 + c) :
    lcvShare v t (2 * v - t - p2) p2 = (p2 + t - v) / t ∧
      IsLCVUniqueBR v t M c p2 (2 * v - t - p2) := by
  have eA : (v - (2 * v - t - p2)) / t = (p2 + t - v) / t := by congr 1; ring
  have eB : lcHat t (2 * v - t - p2) p2 = (p2 + t - v) / t := by unfold lcHat; field_simp; ring
  have hs : lcvShare v t (2 * v - t - p2) p2 = (p2 + t - v) / t := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) ht.le
    · rw [div_le_one ht]; linarith
    · rw [eA]
    · rw [eB]
    · right; left; rw [eA]
  refine ⟨hs, lcv_uniqueBR_of (T := (2 * v - t - p2 - c) * ((p2 + t - v) / t)) hM
    (mul_pos (by linarith) (div_pos (by linarith) ht)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · right; right
      have key : (2 * v - t - p2 - c) * ((p2 + t - v) / t) - (p - c) * lcHat t p p2 =
          (2 * v - t - p2 - p) * (t + p2 + c - (2 * v - t - p2) - p) / (2 * t) := by
        unfold lcHat; field_simp; ring
      have : 0 < (2 * v - t - p2 - p) * (t + p2 + c - (2 * v - t - p2) - p) / (2 * t) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
      linarith
    · right; left
      have key : (2 * v - t - p2 - c) * ((p2 + t - v) / t) - (p - c) * ((v - p) / t) =
          (p - (2 * v - t - p2)) * (p + (2 * v - t - p2) - v - c) / t := by
        field_simp; ring
      have : 0 < (p - (2 * v - t - p2)) * (p + (2 * v - t - p2) - v - c) / t :=
        div_pos (mul_pos (by linarith) (by linarith)) ht
      linarith

/-- **Best response, local monopoly** (MWG, p. 398 small type). If `c < v ≤ c + 2t` and
`2p₂ ≥ 3v − 2t − c`, the unique best response is `(v + c)/2`, with share `(v − c)/(2t)`: the
firm's market area does not reach the indifferent consumer. -/
theorem lcvBR_mono {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v ≤ c + 2 * t) (h : 3 * v - 2 * t - c ≤ 2 * p2) :
    lcvShare v t ((v + c) / 2) p2 = (v - c) / (2 * t) ∧
      IsLCVUniqueBR v t M c p2 ((v + c) / 2) := by
  have eA : (v - (v + c) / 2) / t = (v - c) / (2 * t) := by field_simp; ring
  have hs : lcvShare v t ((v + c) / 2) p2 = (v - c) / (2 * t) := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]; linarith
    · rw [eA]
    · unfold lcHat; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · right; left; rw [eA]
  refine ⟨hs, lcv_uniqueBR_of (T := (v - c) ^ 2 / (4 * t)) hM
    (div_pos (pow_pos (by linarith) 2) (by positivity)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; field_simp; ring
  · right; left
    have key : (v - c) ^ 2 / (4 * t) - (p - c) * ((v - p) / t) = (p - (v + c) / 2) ^ 2 / t := by
      field_simp; ring
    have hne : p - (v + c) / 2 ≠ 0 := sub_ne_zero.2 hp
    have : 0 < (p - (v + c) / 2) ^ 2 / t := by positivity
    linarith

/-- **Best response, covering the market** (MWG, p. 398). If `v ≥ c + 2t` and `p₂ ≥ v`, the unique
best response is `v − t`, at which every consumer buys from the firm (share `1`). -/
theorem lcvBR_cover {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 2 * t ≤ v)
    (h : v ≤ p2) : lcvShare v t (v - t) p2 = 1 ∧ IsLCVUniqueBR v t M c p2 (v - t) := by
  have eA : (v - (v - t)) / t = 1 := by field_simp; ring
  have hs : lcvShare v t (v - t) p2 = 1 := by
    apply lcvShare_eq_of zero_le_one le_rfl (by rw [eA])
    · unfold lcHat; rw [le_div_iff₀ (by positivity)]; linarith
    · left; rfl
  refine ⟨hs, lcv_uniqueBR_of (T := v - t - c) hM (by linarith) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · left; linarith
    · right; left
      have key : v - t - c - (p - c) * ((v - p) / t) = (p - (v - t)) * (p - (c + t)) / t := by
        field_simp; ring
      have : 0 < (p - (v - t)) * (p - (c + t)) / t :=
        div_pos (mul_pos (by linarith) (by linarith)) ht
      linarith

/-- **Best response, capturing the market** (MWG, (12.C.12), last line). If
`c + 3t ≤ p₂ ≤ v`, the unique best response is `p₂ − t`, capturing every consumer. -/
theorem lcvBR_capture {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c + 3 * t ≤ p2)
    (h2 : p2 ≤ v) : lcvShare v t (p2 - t) p2 = 1 ∧ IsLCVUniqueBR v t M c p2 (p2 - t) := by
  have eB : lcHat t (p2 - t) p2 = 1 := by unfold lcHat; field_simp; ring
  have hs : lcvShare v t (p2 - t) p2 = 1 := by
    apply lcvShare_eq_of zero_le_one le_rfl _ (by rw [eB])
    · right; right; rw [eB]
    · rw [le_div_iff₀ ht]; linarith
  refine ⟨hs, lcv_uniqueBR_of (T := p2 - t - c) hM (by linarith) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · left; linarith
    · right; right
      have key : p2 - t - c - (p - c) * lcHat t p p2 =
          (p - (p2 - t)) * (p - (2 * t + c)) / (2 * t) := by
        unfold lcHat; field_simp; ring
      have : 0 < (p - (p2 - t)) * (p - (2 * t + c)) / (2 * t) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
      linarith

/-! ### Best-response functions and equilibrium prices above cost -/

/-- The best-response function for `c < v ≤ c + 2t` and `p₂ > c − t`: interior duopoly, kink,
local monopoly. -/
noncomputable def lcvBRLow (v t c p2 : ℝ) : ℝ :=
  if 3 * p2 ≤ 4 * v - 3 * t - c then (t + p2 + c) / 2
  else if 2 * p2 ≤ 3 * v - 2 * t - c then 2 * v - t - p2 else (v + c) / 2

/-- The best-response function for `c + 2t ≤ v < c + 3t` and `p₂ > c − t`: interior duopoly,
kink, covering the market. -/
noncomputable def lcvBRMid (v t c p2 : ℝ) : ℝ :=
  if 3 * p2 ≤ 4 * v - 3 * t - c then (t + p2 + c) / 2 else if p2 ≤ v then 2 * v - t - p2 else v - t

/-- The best-response function for `v ≥ c + 3t` and `p₂ > c − t`: interior duopoly, capturing
the market, covering the market. For `p₂ ≤ v` it is (12.C.12). -/
noncomputable def lcvBRHigh (v t c p2 : ℝ) : ℝ :=
  if p2 < c + 3 * t then (t + p2 + c) / 2 else if p2 ≤ v then p2 - t else v - t

/-- `lcvBRLow` is the unique best response when `c < v ≤ c + 2t` and `p₂ > c − t`. -/
theorem lcvBRLow_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v ≤ c + 2 * t) (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2) := by
  unfold lcvBRLow
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 (by linarith) h1).2
  · exact (lcvBR_kink ht hM (by linarith) (by linarith) (by linarith) (by linarith)).2
  · exact (lcvBR_mono ht hM hcv hv (by linarith)).2

/-- `lcvBRMid` is the unique best response when `c + 2t ≤ v < c + 3t` and `p₂ > c − t`. -/
theorem lcvBRMid_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + 2 * t ≤ v)
    (hv2 : v < c + 3 * t) (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRMid v t c p2) := by
  unfold lcvBRMid
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 (by linarith) h1).2
  · exact (lcvBR_kink ht hM (by linarith) h2 (by linarith) (by linarith)).2
  · exact (lcvBR_cover ht hM hv1 (by linarith)).2

/-- `lcvBRHigh` is the unique best response when `v ≥ c + 3t` and `p₂ > c − t`. -/
theorem lcvBRHigh_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t ≤ v)
    (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRHigh v t c p2) := by
  unfold lcvBRHigh
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 h1 (by linarith)).2
  · exact (lcvBR_capture ht hM (by linarith) h2).2
  · exact (lcvBR_cover ht hM (by linarith) (by linarith)).2

/-- A firm pricing below cost with a nonnegative profit sells nothing, so its rival's price is at
most its own minus `t`. -/
theorem lcv_rival_low {v t M c p p' : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v) (hp : p < c)
    (h0 : 0 ≤ lcvProfit v t M c p p') : p' ≤ p - t := by
  unfold lcvProfit at h0
  have hs : lcvShare v t p p' ≤ 0 := by
    by_contra h; push Not at h
    have : (p - c) * (M * lcvShare v t p p') < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (mul_pos hM h)
    linarith
  unfold lcvShare at hs
  have hmin : min 1 (min ((v - p) / t) (lcHat t p p')) ≤ 0 := (le_max_right _ _).trans hs
  have hA : 0 < (v - p) / t := div_pos (by linarith) ht
  rcases min_le_iff.1 hmin with h | h
  · linarith
  · rcases min_le_iff.1 h with h' | h'
    · linarith
    · unfold lcHat at h'
      have := (div_nonpos_iff.1 h')
      rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · linarith

/-- In every Nash equilibrium of the linear city with `v > c`, both prices are at least `c`. -/
theorem lcvNash_ge_c {v t M c p1 p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hne : IsLCVNash v t M c p1 p2) : c ≤ p1 ∧ c ≤ p2 := by
  have z : ∀ q, lcvProfit v t M c c q = 0 := fun q => by unfold lcvProfit; ring
  have h1 : 0 ≤ lcvProfit v t M c p1 p2 := by rw [← z p2]; exact hne.1 c
  have h2 : 0 ≤ lcvProfit v t M c p2 p1 := by rw [← z p1]; exact hne.2 c
  have key : ∀ a b, 0 ≤ lcvProfit v t M c a b → 0 ≤ lcvProfit v t M c b a → c ≤ a := by
    intro a b ha hb
    by_contra h; push Not at h
    have hba := lcv_rival_low ht hM hcv h ha
    have hab := lcv_rival_low ht hM hcv (show b < c by linarith) hb
    linarith
  exact ⟨key p1 p2 h1 h2, key p2 p1 h2 h1⟩

/-- At a symmetric profile `p ≤ v − t/2` each firm serves half the market. -/
theorem lcvShare_symm_half {v t p : ℝ} (ht : 0 < t) (hp : 2 * p ≤ 2 * v - t) :
    lcvShare v t p p = 1 / 2 := by
  have e : lcHat t p p = 1 / 2 := by unfold lcHat; field_simp; ring
  apply lcvShare_eq_of (by norm_num) (by norm_num) _ (by rw [e])
  · right; right; rw [e]
  · rw [le_div_iff₀ ht]; linarith

end MWG.MarketPower
