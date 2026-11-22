/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.IntervalPreferences

/-!
# Majority voting over a redistributive tax rate

MWG, Exercise 21.D.10, p. 814.

An odd number of agents with wealths `wᵢ > 0` vote over a proportional tax rate
`t ∈ X = [0, 1]`; receipts are redistributed equally. Agent `i` ranks tax rates by ex post
wealth `fᵢ(t)` through a strictly increasing utility `Uᵢ`. The mean wealth `w̄` enters only as a
positive parameter (the results hold for every `w̄ > 0`, in particular for the mean). The
median wealth `w*` is the wealth of a median agent `h` (`IsMedianAgent w h`).

(a) is an interpretation, listed only. (b) `fᵢ(t) = (1 - t)wᵢ + t w̄`: an agent is single peaked
at `0` if `wᵢ > w̄` and at `1` if `wᵢ < w̄`, but **not** single peaked if `wᵢ = w̄`
(correction); `t = 0` (resp. `t = 1`) strictly defeats every other rate when `w* > w̄` (resp.
`w* < w̄`). (c) `fᵢ(t) = (1 - t)²wᵢ + t(1 - t)w̄`: all agents are single peaked with peak
`tᵢ = max(0, (w̄ - 2wᵢ)/(2(w̄ - wᵢ)))` (`tᵢ = 0` if `w̄ ≤ 2wᵢ`); the peak of the median agent is
the Condorcet winner `t_c`, `t_c ≤ 1/2`, `t_c = 0` if `w* ≥ w̄/2` and `t_c > 0` if `w* < w̄/2`.
(d) `fᵢ(t) = (1 - t²)((1 - t)wᵢ + t w̄)`: the claim that preferences need no longer be single
peaked is **false**; they are always single peaked (`exercise_21_D_10d`).
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι : Type*}

/-- The tax rates `X = [0, 1]`. -/
abbrev TaxRates := Set.Icc (0 : ℝ) 1

/-- The preference over tax rates induced by ex post wealth `f` and utility of wealth `U`. -/
def wealthPref (U f : ℝ → ℝ) : TaxRates → TaxRates → Prop := fun t t' => U (f t') ≤ U (f t)

/-- With a strictly increasing utility, the preference compares ex post wealth. -/
theorem wealthPref_iff {U : ℝ → ℝ} (hU : StrictMono U) (f : ℝ → ℝ) (t t' : TaxRates) :
    wealthPref U f t t' ↔ f t' ≤ f t := hU.le_iff_le

/-- Strict preference compares ex post wealth strictly. -/
theorem wealthPref_strict_iff {U : ℝ → ℝ} (hU : StrictMono U) (f : ℝ → ℝ) (t t' : TaxRates) :
    Strict (wealthPref U f) t t' ↔ f t' < f t := by
  simp only [Strict, wealthPref_iff hU, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- The preference induced by ex post wealth is rational. -/
theorem wealthPref_rational (U f : ℝ → ℝ) : Rational (wealthPref U f) :=
  ⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h2 h1⟩

/-- A strictly decreasing ex post wealth gives a preference single peaked at `0`. -/
theorem isPeak_zero {U : ℝ → ℝ} (hU : StrictMono U) {f : ℝ → ℝ}
    (hf : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → f t < f s) :
    IsPeak (wealthPref U f) (⟨0, le_rfl, zero_le_one⟩ : TaxRates) := by
  intro y z
  refine ⟨fun hz hyz => absurd (lt_of_lt_of_le hyz hz) (not_lt.2 ?_), fun _ hzy => ?_⟩
  · exact Subtype.coe_le_coe.1 y.2.1
  · rw [wealthPref_strict_iff hU]
    exact hf z y z.2.1 (Subtype.coe_lt_coe.2 hzy) y.2.2

/-- A strictly increasing ex post wealth gives a preference single peaked at `1`. -/
theorem isPeak_one {U : ℝ → ℝ} (hU : StrictMono U) {f : ℝ → ℝ}
    (hf : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → f s < f t) :
    IsPeak (wealthPref U f) (⟨1, zero_le_one, le_rfl⟩ : TaxRates) := by
  intro y z
  refine ⟨fun _ hyz => ?_, fun hz hzy => absurd (lt_of_le_of_lt hz hzy) (not_lt.2 ?_)⟩
  · rw [wealthPref_strict_iff hU]
    exact hf y z y.2.1 (Subtype.coe_lt_coe.2 hyz) z.2.2
  · exact Subtype.coe_le_coe.1 y.2.2

/-- Ex post wealth in Exercise 21.D.10(b): `(1 - t)wᵢ + t w̄`. -/
def wealthB (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t) * wi + t * wbar

/-- **Exercise 21.D.10(b)** (MWG, p. 814). An agent with `wᵢ > w̄` is single peaked at `0`, an
agent with `wᵢ < w̄` at `1`. -/
theorem exercise_21_D_10b_singlePeaked {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ} :
    (wbar < wi → IsPeak (wealthPref U (wealthB wi wbar)) ⟨0, le_rfl, zero_le_one⟩) ∧
      (wi < wbar → IsPeak (wealthPref U (wealthB wi wbar)) ⟨1, zero_le_one, le_rfl⟩) :=
  ⟨fun h => isPeak_zero hU fun s t _ hst _ => by unfold wealthB; nlinarith,
    fun h => isPeak_one hU fun s t _ hst _ => by unfold wealthB; nlinarith⟩

/-- **Exercise 21.D.10(b)**, correction (MWG, p. 814). An agent whose wealth equals the mean is
indifferent between all tax rates, so her preference is not single peaked. -/
theorem exercise_21_D_10b_mean_agent (U : ℝ → ℝ) (wbar : ℝ) :
    ¬SinglePeaked (wealthPref U (wealthB wbar wbar)) := by
  rintro ⟨-, x, hx⟩
  have hc : ∀ t, wealthB wbar wbar t = wbar := fun t => by unfold wealthB; ring
  obtain ⟨y, hyx⟩ : ∃ y : TaxRates, y ≠ x := by
    by_cases h : (x : ℝ) = 0
    · exact ⟨⟨1, zero_le_one, le_rfl⟩, fun e => by
        have := congrArg Subtype.val e
        simp only at this
        linarith⟩
    · exact ⟨⟨0, le_rfl, zero_le_one⟩, fun e => h (congrArg Subtype.val e).symm⟩
  have := (hx.strict_best hyx).2
  exact this (by simp only [wealthPref, hc, le_refl])

/-- **Exercise 21.D.10(b)** (MWG, p. 814). With an odd number of agents and median agent `h`:
if `w* = wₕ > w̄`, the tax rate `t = 0` is the Condorcet winner and strictly defeats every other
rate; if `w* < w̄`, so does `t = 1`. -/
theorem exercise_21_D_10b_condorcet [Fintype ι] (hodd : Odd (Fintype.card ι)) {U : ι → ℝ → ℝ}
    (hU : ∀ i, StrictMono (U i)) (w : ι → ℝ) (wbar : ℝ) {h : ι} (hh : IsMedianAgent w h) :
    let p : Profile ι TaxRates := fun i => wealthPref (U i) (wealthB (w i) wbar)
    (wbar < w h → IsCondorcetWinner p ⟨0, le_rfl, zero_le_one⟩ ∧
        ∀ t : TaxRates, t ≠ ⟨0, le_rfl, zero_le_one⟩ →
          ¬majorityRel p t ⟨0, le_rfl, zero_le_one⟩) ∧
      (w h < wbar → IsCondorcetWinner p ⟨1, zero_le_one, le_rfl⟩ ∧
        ∀ t : TaxRates, t ≠ ⟨1, zero_le_one, le_rfl⟩ →
          ¬majorityRel p t ⟨1, zero_le_one, le_rfl⟩) := by
  classical
  intro p
  constructor
  · intro hw
    have key : ∀ t : TaxRates, t ≠ ⟨0, le_rfl, zero_le_one⟩ →
        majorityRel p ⟨0, le_rfl, zero_le_one⟩ t ∧
          (univ.filter fun i => Strict (p i) t ⟨0, le_rfl, zero_le_one⟩).card <
            (univ.filter fun i => Strict (p i) ⟨0, le_rfl, zero_le_one⟩ t).card := by
      intro t ht
      have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun e => ht (Subtype.ext e.symm)
      obtain ⟨h1, h2⟩ := majority_of_supporters (m := ⟨0, le_rfl, zero_le_one⟩) (y := t) p
        (univ.filter fun i => w h ≤ w i) hh.1
        fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [wealthPref_strict_iff (hU i)]
          simp only [wealthB]
          nlinarith [t.2.2]
      exact ⟨h1, h2 hodd⟩
    refine ⟨fun t => ?_, fun t ht hmaj => ?_⟩
    · by_cases ht : t = ⟨0, le_rfl, zero_le_one⟩
      · rw [ht, majorityRel_iff]
      · exact (key t ht).1
    · have := (key t ht).2
      rw [majorityRel_iff] at hmaj
      omega
  · intro hw
    have key : ∀ t : TaxRates, t ≠ ⟨1, zero_le_one, le_rfl⟩ →
        majorityRel p ⟨1, zero_le_one, le_rfl⟩ t ∧
          (univ.filter fun i => Strict (p i) t ⟨1, zero_le_one, le_rfl⟩).card <
            (univ.filter fun i => Strict (p i) ⟨1, zero_le_one, le_rfl⟩ t).card := by
      intro t ht
      have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun e => ht (Subtype.ext e)
      obtain ⟨h1, h2⟩ := majority_of_supporters (m := ⟨1, zero_le_one, le_rfl⟩) (y := t) p
        (univ.filter fun i => w i ≤ w h) hh.2
        fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [wealthPref_strict_iff (hU i)]
          simp only [wealthB]
          nlinarith [t.2.1]
      exact ⟨h1, h2 hodd⟩
    refine ⟨fun t => ?_, fun t ht hmaj => ?_⟩
    · by_cases ht : t = ⟨1, zero_le_one, le_rfl⟩
      · rw [ht, majorityRel_iff]
      · exact (key t ht).1
    · have := (key t ht).2
      rw [majorityRel_iff] at hmaj
      omega

/-- Ex post wealth in Exercise 21.D.10(c): `(1 - t)²wᵢ + t(1 - t)w̄`. -/
def wealthC (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t) ^ 2 * wi + t * (1 - t) * wbar

/-- The peak of `wealthC`: `0` if `w̄ ≤ 2wᵢ`, otherwise `(w̄ - 2wᵢ)/(2(w̄ - wᵢ))`. -/
noncomputable def peakC (wi wbar : ℝ) : ℝ :=
  if wbar ≤ 2 * wi then 0 else (wbar - 2 * wi) / (2 * (wbar - wi))

/-- The peak of `wealthC` lies in `[0, 1/2]` (for `wᵢ > 0`). -/
theorem peakC_mem {wi wbar : ℝ} (hwi : 0 < wi) : 0 ≤ peakC wi wbar ∧ peakC wi wbar ≤ 1 / 2 := by
  unfold peakC
  split_ifs with h
  · norm_num
  · push Not at h
    have hd : 0 < 2 * (wbar - wi) := by linarith
    constructor
    · exact div_nonneg (by linarith) hd.le
    · rw [div_le_iff₀ hd]
      linarith

/-- The peak of `wealthC` as a tax rate. -/
noncomputable def peakCRate {wi : ℝ} (wbar : ℝ) (hwi : 0 < wi) : TaxRates :=
  ⟨peakC wi wbar, (peakC_mem (wbar := wbar) hwi).1, by linarith [(peakC_mem (wbar := wbar) hwi).2]⟩

/-- **Exercise 21.D.10(c)** (MWG, p. 814). Every agent's preference over tax rates is single
peaked, with peak `peakC wᵢ w̄`. -/
theorem exercise_21_D_10c_singlePeaked {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ}
    (hwi : 0 < wi) (hwbar : 0 < wbar) :
    IsPeak (wealthPref U (wealthC wi wbar)) (peakCRate wbar hwi) := by
  intro y z
  have hy0 := y.2.1
  have hy1 := y.2.2
  have hz0 := z.2.1
  have hz1 := z.2.2
  simp only [wealthPref_strict_iff hU]
  by_cases hge : wbar ≤ wi
  · have hpk : (peakCRate wbar hwi : ℝ) = 0 := by
      simp only [peakCRate, peakC, show wbar ≤ 2 * wi by linarith, ↓reduceIte]
    refine ⟨fun hz hyz => ?_, fun _ hzy => ?_⟩
    · have := Subtype.coe_le_coe.2 hz
      have := Subtype.coe_lt_coe.2 hyz
      rw [hpk] at *
      linarith
    · have hlt : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
      have hD : (wbar - 2 * wi) + ((y : ℝ) + z) * (wi - wbar) < 0 := by
        have : ((y : ℝ) + z) * (wi - wbar) ≤ 2 * (wi - wbar) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have e : wealthC wi wbar y - wealthC wi wbar z =
          ((y : ℝ) - z) * ((wbar - 2 * wi) + ((y : ℝ) + z) * (wi - wbar)) := by
        simp only [wealthC]
        ring
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hlt) hD]
  · push Not at hge
    set k := wbar - wi with hk
    have hkpos : 0 < k := by linarith
    set r := (wbar - 2 * wi) / (2 * k) with hr
    have hsq : ∀ t : ℝ, wealthC wi wbar t = wealthC wi wbar r - k * (t - r) ^ 2 := by
      intro t
      simp only [wealthC, hr]
      field_simp
      ring
    have hcmp : ∀ s t : ℝ, (s - r) ^ 2 < (t - r) ^ 2 → wealthC wi wbar t < wealthC wi wbar s :=
      fun s t h => by rw [hsq s, hsq t]; nlinarith
    by_cases hle : wbar ≤ 2 * wi
    · have hpk : (peakCRate wbar hwi : ℝ) = 0 := by
        simp only [peakCRate, peakC, hle, ↓reduceIte]
      have hr0 : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      refine ⟨fun hz hyz => ?_, fun _ hzy => ?_⟩
      · have := Subtype.coe_le_coe.2 hz
        have := Subtype.coe_lt_coe.2 hyz
        rw [hpk] at *
        linarith
      · have hlt : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
        exact hcmp z y (by nlinarith)
    · have hpk : (peakCRate wbar hwi : ℝ) = r := by
        simp only [peakCRate, peakC, hle, ↓reduceIte, hr, hk]
      refine ⟨fun hz hyz => ?_, fun hz hzy => ?_⟩
      · have h1 : (z : ℝ) ≤ r := hpk ▸ Subtype.coe_le_coe.2 hz
        have h2 : (y : ℝ) < z := Subtype.coe_lt_coe.2 hyz
        exact hcmp z y (by nlinarith)
      · have h1 : r ≤ (z : ℝ) := hpk ▸ Subtype.coe_le_coe.2 hz
        have h2 : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
        exact hcmp z y (by nlinarith)

/-- The peak `peakC` is antitone in wealth. -/
theorem peakC_antitone {wi wj wbar : ℝ} (hwi : 0 < wi) (hij : wi ≤ wj) :
    peakC wj wbar ≤ peakC wi wbar := by
  have hj := peakC_mem (wbar := wbar) (lt_of_lt_of_le hwi hij)
  have hi := peakC_mem (wbar := wbar) hwi
  unfold peakC at hj hi ⊢
  by_cases h2 : wbar ≤ 2 * wj
  · simp only [h2, ↓reduceIte] at hj ⊢
    exact hi.1
  · have h1 : ¬wbar ≤ 2 * wi := by linarith
    simp only [h1, h2, ↓reduceIte]
    push Not at h1 h2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- **Exercise 21.D.10(c)** (MWG, p. 814). With an odd number of agents and `h` a median agent
for wealth, the median agent's peak `t_c` is the Condorcet winner (and strictly defeats every
other rate); `t_c ≤ 1/2`; `t_c = 0` if `w* ≥ w̄/2` and `t_c > 0` if `w* < w̄/2`. -/
theorem exercise_21_D_10c [Fintype ι] (hodd : Odd (Fintype.card ι)) {U : ι → ℝ → ℝ}
    (hU : ∀ i, StrictMono (U i)) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {wbar : ℝ} (hwbar : 0 < wbar)
    {h : ι} (hh : IsMedianAgent w h) :
    let p : Profile ι TaxRates := fun i => wealthPref (U i) (wealthC (w i) wbar)
    IsCondorcetWinner p (peakCRate wbar (hw h)) ∧
      (∀ t, t ≠ peakCRate wbar (hw h) → ¬IsCondorcetWinner p t) ∧
      (peakCRate wbar (hw h) : ℝ) ≤ 1 / 2 ∧
      (wbar / 2 ≤ w h → (peakCRate wbar (hw h) : ℝ) = 0) ∧
      (w h < wbar / 2 → 0 < (peakCRate wbar (hw h) : ℝ)) := by
  classical
  intro p
  let pk : ι → TaxRates := fun i => peakCRate wbar (hw i)
  have hpk : ∀ i, IsPeak (p i) (pk i) := fun i =>
    exercise_21_D_10c_singlePeaked (hU i) (hw i) hwbar
  have hmed : IsMedianAgent pk h := by
    constructor
    · refine le_trans hh.2 (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact Subtype.coe_le_coe.1 (peakC_antitone (hw i) hi)
    · refine le_trans hh.1 (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact Subtype.coe_le_coe.1 (peakC_antitone (hw h) hi)
  obtain ⟨hcw, hstrict⟩ := proposition_21_D_1 hpk hmed
  refine ⟨hcw, fun t ht hcwt => ?_, (peakC_mem (hw h)).2, fun hge => ?_, fun hlt => ?_⟩
  · have h1 := hstrict hodd t ht
    have h2 := hcwt (pk h)
    rw [majorityRel_iff] at h2
    omega
  · simp only [peakCRate, peakC, show wbar ≤ 2 * w h by linarith, ↓reduceIte]
  · simp only [peakCRate, peakC, show ¬wbar ≤ 2 * w h by linarith, ↓reduceIte]
    exact div_pos (by linarith) (by linarith)

/-- Ex post wealth in Exercise 21.D.10(d): `(1 - t²)((1 - t)wᵢ + t w̄)`. -/
def wealthD (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t ^ 2) * ((1 - t) * wi + t * wbar)

/-- `wealthD` is strictly quasiconcave on `[0, 1]`: it is a product of positive affine functions
on `[0, 1)`, hence strictly log-concave there, and it vanishes at `1`. -/
theorem wealthD_strictQuasiconcave {wi wbar : ℝ} (hwi : 0 < wi) (hwbar : 0 < wbar) :
    ∀ y z : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → z ∈ Set.Icc (0 : ℝ) 1 → y ≠ z →
      ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        min (wealthD wi wbar y) (wealthD wi wbar z) < wealthD wi wbar (α * y + (1 - α) * z) := by
  intro y z hy hz hyz α hα
  obtain ⟨hα0, hα1⟩ := hα
  set m := α * y + (1 - α) * z with hm
  have hm0 : 0 ≤ m := by nlinarith [hy.1, hz.1]
  have hm1 : m < 1 := by
    rcases lt_or_gt_of_ne hyz with h | h <;> nlinarith [hy.2, hz.2]
  have pos3 : ∀ t, 0 ≤ t → t ≤ 1 → 0 < (1 - t) * wi + t * wbar := fun t h0 h1 => by
    rcases eq_or_lt_of_le h1 with e | e
    · rw [e]; linarith
    · nlinarith
  have posD : ∀ t, 0 ≤ t → t < 1 → 0 < wealthD wi wbar t := fun t h0 h1 =>
    mul_pos (by nlinarith) (pos3 t h0 h1.le)
  have hDm := posD m hm0 hm1
  by_cases hy1 : y = 1
  · have : wealthD wi wbar y = 0 := by rw [hy1]; simp [wealthD]
    rw [this]
    exact lt_of_le_of_lt (min_le_left _ _) hDm
  by_cases hz1 : z = 1
  · have : wealthD wi wbar z = 0 := by rw [hz1]; simp [wealthD]
    rw [this]
    exact lt_of_le_of_lt (min_le_right _ _) hDm
  have hy1' : y < 1 := lt_of_le_of_ne hy.2 hy1
  have hz1' : z < 1 := lt_of_le_of_ne hz.2 hz1
  have hDy := posD y hy.1 hy1'
  have hDz := posD z hz.1 hz1'
  have hβ : (0 : ℝ) < 1 - α := by linarith
  have hsum : α + (1 - α) = 1 := by ring
  have logD : ∀ t, 0 ≤ t → t < 1 → Real.log (wealthD wi wbar t) =
      Real.log (1 - t) + Real.log (1 + t) + Real.log ((1 - t) * wi + t * wbar) := by
    intro t h0 h1
    have e : wealthD wi wbar t = (1 - t) * (1 + t) * ((1 - t) * wi + t * wbar) := by
      simp only [wealthD]
      ring
    rw [e, Real.log_mul (by nlinarith) (pos3 t h0 h1.le).ne', Real.log_mul (by linarith)
      (by linarith)]
  have c1 : α * Real.log (1 - y) + (1 - α) * Real.log (1 - z) < Real.log (1 - m) := by
    have := strictConcaveOn_log_Ioi.2 (show (1 - y) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith) (show (1 - z) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith) (fun e => hyz (by linarith)) hα0 hβ hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have c2 : α * Real.log (1 + y) + (1 - α) * Real.log (1 + z) ≤ Real.log (1 + m) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 + y) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith [hy.1]) (show (1 + z) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith [hz.1]) hα0.le hβ.le hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have c3 : α * Real.log ((1 - y) * wi + y * wbar) + (1 - α) * Real.log ((1 - z) * wi + z * wbar)
      ≤ Real.log ((1 - m) * wi + m * wbar) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (pos3 y hy.1 hy.2) (pos3 z hz.1 hz.2) hα0.le
      hβ.le hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have hlog : α * Real.log (wealthD wi wbar y) + (1 - α) * Real.log (wealthD wi wbar z) <
      Real.log (wealthD wi wbar m) := by
    rw [logD y hy.1 hy1', logD z hz.1 hz1', logD m hm0 hm1]
    linarith
  have hmin : Real.log (min (wealthD wi wbar y) (wealthD wi wbar z)) <
      Real.log (wealthD wi wbar m) := by
    rcases min_choice (wealthD wi wbar y) (wealthD wi wbar z) with e | e
    · rw [e]
      have : Real.log (wealthD wi wbar y) ≤ Real.log (wealthD wi wbar z) :=
        Real.log_le_log hDy (e ▸ min_le_right _ _)
      nlinarith
    · rw [e]
      have : Real.log (wealthD wi wbar z) ≤ Real.log (wealthD wi wbar y) :=
        Real.log_le_log hDz (e ▸ min_le_left _ _)
      nlinarith
  exact (Real.log_lt_log_iff (lt_min hDy hDz) hDm).1 hmin

/-- **Exercise 21.D.10(d)** (MWG, p. 814), refuted. With the deadweight loss `(1 - t²)wᵢ`,
every agent's preference over tax rates is still single peaked (for any `wᵢ, w̄ > 0` and any
strictly increasing utility of wealth), contrary to the printed claim. -/
theorem exercise_21_D_10d {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ} (hwi : 0 < wi)
    (hwbar : 0 < wbar) : SinglePeaked (wealthPref U (wealthD wi wbar)) := by
  have hcont : Continuous (wealthD wi wbar) := by unfold wealthD; fun_prop
  have hc : ContinuousPref (wealthPref U (wealthD wi wbar)) := by
    have e : {q : TaxRates × TaxRates | wealthPref U (wealthD wi wbar) q.1 q.2} =
        {q | wealthD wi wbar q.2 ≤ wealthD wi wbar q.1} := by
      ext q
      exact wealthPref_iff hU _ q.1 q.2
    unfold ContinuousPref
    rw [e]
    exact isClosed_le (hcont.comp (continuous_subtype_val.comp continuous_snd))
      (hcont.comp (continuous_subtype_val.comp continuous_fst))
  have hsc : StrictlyConvexPref (wealthPref U (wealthD wi wbar)) := by
    have := strictlyConvex_of_strictQuasiconcave (a := 0) (b := 1)
      (wealthD_strictQuasiconcave hwi hwbar)
    intro w y z α hα hyw hzw hyz
    have h := this w y z α hα ((wealthPref_iff hU _ y w).1 hyw) ((wealthPref_iff hU _ z w).1 hzw)
      hyz
    exact (wealthPref_strict_iff hU _ _ _).2 (lt_of_le_of_ne h.1 fun e => h.2 e.ge)
  exact example_21_D_4_sufficiency zero_le_one (wealthPref_rational U _) hc hsc

end MWG.SocialChoice
