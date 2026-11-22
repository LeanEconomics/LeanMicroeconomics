/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bayesian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Example 8.E.2: the Alphabeta research consortium

MWG, Example 8.E.2, pp. 256-257.

Each firm's type `θ_i` is uniform on `[0, 1]`, independently; developing costs `c ∈ (0, 1)` and
is worth `θ_i²` to firm `i`, and an invention is shared. A strategy is a decision rule
`s_i : [0, 1] → {develop, not}` (`true` = develop). With a continuum of types the book analyses
the equilibrium type by type, through condition (8.E.3) (see footnote 8: Proposition 8.E.1 holds
for almost every type); this is the formulation used here.

* `zProb s = Prob(s(θ) = develop)` is the Lebesgue measure of `{θ ∈ [0, 1] : s(θ) = true}`.
* `ZiggerBNE c s₁ s₂`: every type develops exactly when developing is at least as good as not
  developing, `θ_i² - c ≥ θ_i² Prob(s_j(θ_j) = 1)` (ties: develop).
* (8.E.3) and the cutoff rule (`zigger_cutoff`): firm `i` develops iff
  `θ_i ≥ [c / (1 - Prob(s_j(θ_j) = 1))]^{1/2}`, a cutoff at least `√c` (`zigger_cutoff_ge_sqrt`).
* `example_8_E_2`: in every equilibrium both firms use the cutoff `θ* = c^{1/3}`, and this is an
  equilibrium (`example_8_E_2_exists`); the cutoffs lie in `(0, 1)` and satisfy
  `(θ̂₁)² θ̂₂ = c = (θ̂₂)² θ̂₁`. The probabilities that neither, exactly one, or both firms develop
  are `(θ*)²`, `2θ*(1 - θ*)`, `(1 - θ*)²` (`example_8_E_2_outcomes`).
-/

namespace MWG.SimultaneousMoveGames

open MeasureTheory

/-- The probability `Prob(s(θ) = 1)` that a firm using the decision rule `s` develops, for `θ`
uniform on `[0, 1]`. -/
noncomputable def zProb (s : ℝ → Bool) : ℝ :=
  (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true})).toReal

/-- **Example 8.E.2** (MWG, p. 256). A Bayesian Nash equilibrium of the Zigger game, type by type:
type `θ` of firm `i` develops iff `θ² - c ≥ θ² Prob(s_j(θ_j) = 1)`. -/
def ZiggerBNE (c : ℝ) (s₁ s₂ : ℝ → Bool) : Prop :=
  (∀ θ ∈ Set.Icc (0 : ℝ) 1, s₁ θ = true ↔ θ ^ 2 * zProb s₂ ≤ θ ^ 2 - c) ∧
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, s₂ θ = true ↔ θ ^ 2 * zProb s₁ ≤ θ ^ 2 - c

/-- `√x < 1` for `x < 1`. -/
theorem zigger_sqrt_lt_one {x : ℝ} (hx : x < 1) : √x < 1 :=
  (Real.sqrt_lt' one_pos).2 (by simpa using hx)

/-- Probabilities lie in `[0, 1]`. -/
theorem zProb_mem (s : ℝ → Bool) : 0 ≤ zProb s ∧ zProb s ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold zProb
  have h : volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true}) ≤ 1 := by
    calc volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true}) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono Set.inter_subset_left
      _ = 1 := by simp [Real.volume_Icc]
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- The measure of `{θ ∈ [0, 1] : θ² ≥ k}` for `k ≤ 1` is `1 - √k`. -/
theorem volume_sq_ge {k : ℝ} (hk1 : k ≤ 1) :
    (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2})).toReal = 1 - √k := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2} = Set.Icc (√k) 1 := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, hk'⟩
      exact ⟨(Real.sqrt_le_left h0).2 hk', h1⟩
    · rintro ⟨h0, h1⟩
      have hθ : 0 ≤ θ := (Real.sqrt_nonneg k).trans h0
      exact ⟨⟨hθ, h1⟩, (Real.sqrt_le_left hθ).1 h0⟩
  have hs : √k ≤ 1 := Real.sqrt_le_one.mpr hk1
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- The set `{θ ∈ [0, 1] : θ² ≥ k}` is empty for `k > 1`. -/
theorem volume_sq_ge_of_one_lt {k : ℝ} (hk : 1 < k) :
    (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2})).toReal = 0 := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2} = ∅ := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro ⟨h0, h1⟩ hk'
    nlinarith
  simp [hset]

/-- **(8.E.3)** (MWG, p. 256): the best response of firm `i` is a cutoff rule. If
`Prob(s_j = 1) < 1`, type `θ ∈ [0, 1]` develops iff `θ ≥ [c / (1 - Prob(s_j(θ_j) = 1))]^{1/2}`; if
`Prob(s_j = 1) = 1` no type develops. -/
theorem zigger_cutoff {c q : ℝ} (hc : 0 < c) (hq : q ≤ 1) (θ : ℝ) (hθ : 0 ≤ θ) :
    (θ ^ 2 * q ≤ θ ^ 2 - c ↔ q < 1 ∧ √(c / (1 - q)) ≤ θ) := by
  constructor
  · intro h
    have hq1 : q < 1 := by
      by_contra hq1
      have : q = 1 := le_antisymm hq (not_lt.1 hq1)
      subst this
      linarith
    refine ⟨hq1, (Real.sqrt_le_left hθ).2 ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rintro ⟨hq1, h⟩
    have := (Real.sqrt_le_left hθ).1 h
    rw [div_le_iff₀ (by linarith)] at this
    linarith

/-- **Section 8.E** (MWG, p. 257). The cutoff of a firm in the consortium is always (weakly) above
`√c`, the cutoff of a firm in isolation: firms free-ride on each other's development. -/
theorem zigger_cutoff_ge_sqrt {c q : ℝ} (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    √c ≤ √(c / (1 - q)) :=
  Real.sqrt_le_sqrt (le_div_self hc.le (by linarith) (by linarith))

/-- The probability that a firm develops, when the other develops with probability `q`. -/
theorem zigger_prob_response {c : ℝ} (hc : 0 < c) {s q : ℝ → Bool} (hq : zProb q ≤ 1)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ θ ^ 2 * zProb q ≤ θ ^ 2 - c) :
    zProb s = if zProb q < 1 ∧ c / (1 - zProb q) ≤ 1 then 1 - √(c / (1 - zProb q)) else 0 := by
  have hz : zProb s = (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true})).toReal := rfl
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true} =
      Set.Icc (0 : ℝ) 1 ∩ {θ | zProb q < 1 ∧ c / (1 - zProb q) ≤ θ ^ 2} := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hθ, h⟩
      obtain ⟨h1, h2⟩ := (zigger_cutoff hc hq θ hθ.1).1 ((hs θ hθ).1 h)
      exact ⟨hθ, h1, (Real.sqrt_le_left hθ.1).1 h2⟩
    · rintro ⟨hθ, h1, h2⟩
      exact ⟨hθ, (hs θ hθ).2 ((zigger_cutoff hc hq θ hθ.1).2 ⟨h1, (Real.sqrt_le_left hθ.1).2 h2⟩)⟩
  rw [hz, hset]
  by_cases h1 : zProb q < 1
  · have hk : 0 < c / (1 - zProb q) := div_pos hc (by linarith)
    simp only [h1, true_and]
    split_ifs with hk1
    · exact volume_sq_ge hk1
    · exact volume_sq_ge_of_one_lt (not_le.1 hk1)
  · simp [h1]

/-- **Example 8.E.2** (MWG, p. 257). In any Bayesian Nash equilibrium both firms use the same cutoff
`θ* = c^{1/3}`: each firm develops exactly when its type is at least `c^{1/3}`, and each develops
with probability `1 - c^{1/3}`. Along the way the cutoffs `θ̂_i = 1 - Prob(s_i = 1)` lie in
`(0, 1)` and satisfy `(θ̂₁)² θ̂₂ = c = (θ̂₂)² θ̂₁`. -/
theorem example_8_E_2 {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s₁ s₂ : ℝ → Bool}
    (h : ZiggerBNE c s₁ s₂) :
    let θ₁ := 1 - zProb s₁
    let θ₂ := 1 - zProb s₂
    (0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1) ∧ θ₁ ^ 2 * θ₂ = c ∧ θ₂ ^ 2 * θ₁ = c ∧
      θ₁ = c ^ (1 / 3 : ℝ) ∧ θ₂ = c ^ (1 / 3 : ℝ) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, s₁ θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ) ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, s₂ θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ := by
  intro θ₁ θ₂
  obtain ⟨hq₁0, hq₁1⟩ := zProb_mem s₁
  obtain ⟨hq₂0, hq₂1⟩ := zProb_mem s₂
  have hr₁ := zigger_prob_response hc hq₂1 h.1
  have hr₂ := zigger_prob_response hc hq₁1 h.2
  have hsqc : √c < 1 := zigger_sqrt_lt_one hc1
  have hsqc0 : 0 < √c := Real.sqrt_pos.2 hc
  -- an interior response: if the other develops with probability below one and the resulting
  -- threshold is at most one, the cutoff is `√(c / (1 - q))`
  have key : ∀ q p : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ p → p ≤ 1 →
      p = (if q < 1 ∧ c / (1 - q) ≤ 1 then 1 - √(c / (1 - q)) else 0) →
      q = (if p < 1 ∧ c / (1 - p) ≤ 1 then 1 - √(c / (1 - p)) else 0) →
      q < 1 ∧ c / (1 - q) < 1 ∧ p = 1 - √(c / (1 - q)) := by
    intro q p hq0 hq1 hp0 hp1 hp hq
    -- `p = 0` is impossible: then `q = 1 - √c` and `p = 1 - c^{1/4} > 0`
    have hp_ne : p ≠ 0 := by
      intro hp00
      rw [hp00] at hq
      simp only [sub_zero, div_one, zero_lt_one, true_and, hc1.le, ↓reduceIte] at hq
      have h1 : q < 1 := by linarith
      have hk : c / (1 - q) = √c := by
        rw [hq, sub_sub_cancel, div_eq_iff hsqc0.ne', Real.mul_self_sqrt hc.le]
      simp only [h1, hk, hsqc.le, true_and, ↓reduceIte] at hp
      have : √(√c) < 1 := zigger_sqrt_lt_one hsqc
      linarith
    by_cases hcond : q < 1 ∧ c / (1 - q) ≤ 1
    · simp only [hcond, and_self, ↓reduceIte] at hp
      refine ⟨hcond.1, lt_of_le_of_ne hcond.2 fun h1 => hp_ne ?_, hp⟩
      rw [hp, h1, Real.sqrt_one, sub_self]
    · simp only [hcond, ↓reduceIte] at hp
      exact absurd hp hp_ne
  obtain ⟨hq₂lt, hk₁, hp₁⟩ := key (zProb s₂) (zProb s₁) hq₂0 hq₂1 hq₁0 hq₁1 hr₁ hr₂
  obtain ⟨hq₁lt, hk₂, hp₂⟩ := key (zProb s₁) (zProb s₂) hq₁0 hq₁1 hq₂0 hq₂1 hr₂ hr₁
  -- the cutoffs
  have hθ₁ : θ₁ = √(c / θ₂) := by simp only [θ₁, θ₂]; rw [hp₁]; ring
  have hθ₂ : θ₂ = √(c / θ₁) := by simp only [θ₁, θ₂]; rw [hp₂]; ring
  have hθ₁pos : 0 < θ₁ := by simp only [θ₁]; linarith
  have hθ₂pos : 0 < θ₂ := by simp only [θ₂]; linarith
  have hθ₁lt : θ₁ < 1 := by
    rw [hθ₁]; exact zigger_sqrt_lt_one (by simpa [θ₂] using hk₁)
  have hθ₂lt : θ₂ < 1 := by
    rw [hθ₂]; exact zigger_sqrt_lt_one (by simpa [θ₁] using hk₂)
  have e₁ : θ₁ ^ 2 * θ₂ = c := by
    rw [hθ₁, Real.sq_sqrt (div_nonneg hc.le hθ₂pos.le), div_mul_cancel₀ _ hθ₂pos.ne']
  have e₂ : θ₂ ^ 2 * θ₁ = c := by
    rw [hθ₂, Real.sq_sqrt (div_nonneg hc.le hθ₁pos.le), div_mul_cancel₀ _ hθ₁pos.ne']
  -- equal cutoffs, equal to `c^{1/3}`
  have heq : θ₁ = θ₂ := by
    have : θ₁ * θ₂ * (θ₁ - θ₂) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h0 | h0
    · nlinarith
    · linarith
  have hcube : θ₁ ^ 3 = c := by rw [← e₁, heq]; ring
  have hroot : θ₁ = c ^ (1 / 3 : ℝ) := by
    rw [← hcube, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast hθ₁pos.le (by norm_num)]
  -- the decision rules
  have hrule : ∀ (s : ℝ → Bool) (q : ℝ), q ≤ 1 → 1 - q = θ₁ →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ θ ^ 2 * q ≤ θ ^ 2 - c) →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ := by
    intro s q hq hqθ hs θ hθ
    rw [hs θ hθ, zigger_cutoff hc hq θ hθ.1]
    have hq1 : q < 1 := by linarith
    have hcut : √(c / (1 - q)) = c ^ (1 / 3 : ℝ) := by
      rw [hqθ, ← hroot, ← e₁, ← heq, show θ₁ ^ 2 * θ₁ / θ₁ = θ₁ ^ 2 by field_simp,
        Real.sqrt_sq hθ₁pos.le]
    rw [hcut]
    exact ⟨fun h => h.2, fun h => ⟨hq1, h⟩⟩
  refine ⟨⟨hθ₁pos, hθ₁lt, hθ₂pos, hθ₂lt⟩, e₁, e₂, hroot, heq ▸ hroot,
    hrule s₁ (zProb s₂) hq₂1 (by simp only [θ₂] at heq; linarith) h.1,
    hrule s₂ (zProb s₁) hq₁1 rfl h.2⟩

/-- **Example 8.E.2** (MWG, p. 257). Both firms using the cutoff `θ* = c^{1/3}` is a Bayesian Nash
equilibrium. -/
theorem example_8_E_2_exists {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ZiggerBNE c (fun θ => decide (c ^ (1 / 3 : ℝ) ≤ θ))
      (fun θ => decide (c ^ (1 / 3 : ℝ) ≤ θ)) := by
  set t := c ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc _
  have ht3 : t ^ 3 = c := by
    rw [ht, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow hc.le (by norm_num)]
  have ht1 : t < 1 := by
    by_contra h
    push Not at h
    nlinarith [pow_le_pow_left₀ zero_le_one h 3]
  have hq : zProb (fun θ => decide (t ≤ θ)) = 1 - t := by
    unfold zProb
    have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | decide (t ≤ θ) = true} = Set.Icc t 1 := by
      ext θ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨⟨ht0.le.trans h2, h1⟩, h2⟩
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hside : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      decide (t ≤ θ) = true ↔ θ ^ 2 * zProb (fun θ => decide (t ≤ θ)) ≤ θ ^ 2 - c := by
    intro θ hθ
    rw [hq, decide_eq_true_eq, zigger_cutoff hc (by linarith) θ hθ.1]
    have hcut : √(c / (1 - (1 - t))) = t := by
      rw [sub_sub_cancel, ← ht3, show t ^ 3 / t = t ^ 2 by field_simp, Real.sqrt_sq ht0.le]
    rw [hcut]
    exact ⟨fun h => ⟨by linarith, h⟩, fun h => h.2⟩
  exact ⟨hside, hside⟩

/-- **Example 8.E.2** (MWG, p. 257). With independent types and both firms developing with
probability `1 - θ*`, the probability that neither develops is `(θ*)²`, that exactly one does is
`2θ*(1 - θ*)`, and that both do is `(1 - θ*)²`. -/
theorem example_8_E_2_outcomes (θ : ℝ) :
    (1 - (1 - θ)) * (1 - (1 - θ)) = θ ^ 2 ∧
      (1 - θ) * (1 - (1 - θ)) + (1 - (1 - θ)) * (1 - θ) = 2 * θ * (1 - θ) ∧
      (1 - θ) * (1 - θ) = (1 - θ) ^ 2 := by
  refine ⟨by ring, by ring, by ring⟩

end MWG.SimultaneousMoveGames
