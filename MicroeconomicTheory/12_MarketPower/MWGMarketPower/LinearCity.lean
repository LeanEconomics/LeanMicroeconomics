/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Bertrand

/-!
# Product differentiation: the linear city

MWG, Example 12.C.2, pp. 396-398.

Consumers of total mass `M` are uniform on `[0, 1]`; firm 1 is at `0`, firm 2 at `1`; buying from
firm `j` at distance `d` costs `p_j + td`. With `v > c + 3t` nobody stays out of the market, and
a consumer at `z` buys from firm 1 iff `p₁ + tz < p₂ + t(1 − z)`, i.e. iff `z < ẑ`
(`linearCity_prefers`), where `ẑ = (t + p₂ − p₁)/(2t)` is the indifferent consumer (12.C.7).
Firm 1's demand is `M` times the clamped `ẑ` (12.C.8) (`lcDemand`).

* `lcBR_mid`, `lcBR_high`, `lcBR_low`: the best-response function (12.C.12), with uniqueness in
  the middle and upper regions.
* `example_12_C_2`: the unique Nash equilibrium is `p₁* = p₂* = c + t`; each firm sells `M/2`
  and earns `tM/2`; there are no asymmetric equilibria.
-/

namespace MWG.MarketPower

/-- The indifferent consumer (12.C.7). -/
noncomputable def lcHat (t p1 p2 : ℝ) : ℝ := (t + p2 - p1) / (2 * t)

/-- **Condition (12.C.7)** (MWG, p. 397). -/
theorem lcHat_spec {t p1 p2 : ℝ} (ht : 0 < t) :
    p1 + t * lcHat t p1 p2 = p2 + t * (1 - lcHat t p1 p2) := by
  unfold lcHat; field_simp; ring

/-- A consumer at `z` strictly prefers firm 1 iff `z < ẑ`. -/
theorem linearCity_prefers {t p1 p2 z : ℝ} (ht : 0 < t) :
    p1 + t * z < p2 + t * (1 - z) ↔ z < lcHat t p1 p2 := by
  unfold lcHat
  rw [lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- **Firm 1's demand (12.C.8)** (MWG, p. 397): `0` if `p₁ > p₂ + t`, `M` if `p₁ < p₂ − t`, and
`(t + p₂ − p₁)M/(2t)` in between. Firm 2's demand (12.C.9) is `lcDemand t M p₂ p₁`. -/
noncomputable def lcDemand (t M p1 p2 : ℝ) : ℝ :=
  if p2 + t < p1 then 0 else if p1 < p2 - t then M else (t + p2 - p1) * M / (2 * t)

/-- The profit `(p_j − c)x_j(p_j, p_{-j})`. -/
noncomputable def lcProfit (t M c pj p : ℝ) : ℝ := (pj - c) * lcDemand t M pj p

/-- The quadratic part of the profit. -/
theorem lcProfit_mid {t M c pj p : ℝ} (h1 : pj ≤ p + t) (h2 : p - t ≤ pj) :
    lcProfit t M c pj p = (pj - c) * ((t + p - pj) * M / (2 * t)) := by
  unfold lcProfit lcDemand
  split_ifs with a b
  · exact absurd a (not_lt.2 h1)
  · exact absurd b (not_lt.2 h2)
  · rfl

theorem lcProfit_low {t M c pj p : ℝ} (ht : 0 < t) (h : pj < p - t) :
    lcProfit t M c pj p = (pj - c) * M := by
  unfold lcProfit lcDemand
  split_ifs with a
  · exfalso; linarith
  · rfl

theorem lcProfit_high {t M c pj p : ℝ} (h : p + t < pj) : lcProfit t M c pj p = 0 := by
  unfold lcProfit lcDemand
  simp only [h, ↓reduceIte, mul_zero]

/-- **Best response, middle region** ((12.C.12), MWG, p. 398). If `p ∈ (c − t, c + 3t)`, the
unique best response is `(t + p + c)/2`, and it earns a strictly positive profit. -/
theorem lcBR_mid {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p) (h2 : p < c + 3 * t) :
    0 < lcProfit t M c ((t + p + c) / 2) p ∧
    ∀ pj, pj ≠ (t + p + c) / 2 → lcProfit t M c pj p < lcProfit t M c ((t + p + c) / 2) p := by
  set m := (t + p + c) / 2 with hm
  have hmid := lcProfit_mid (M := M) (c := c) (show m ≤ p + t by rw [hm]; linarith)
    (show p - t ≤ m by rw [hm]; linarith)
  have hpos : 0 < lcProfit t M c m p := by
    rw [hmid]
    apply mul_pos (by rw [hm]; linarith)
    apply div_pos (mul_pos (by rw [hm]; linarith) hM) (by positivity)
  refine ⟨hpos, fun pj hne => ?_⟩
  rcases lt_or_ge (p + t) pj with h | h
  · rw [lcProfit_high h]; exact hpos
  rcases lt_or_ge pj (p - t) with h' | h'
  · -- below `p − t` the profit is `(p_j − c)M < (p − t − c)M ≤ π(m)`
    rw [lcProfit_low ht h']
    have hpt := lcProfit_mid (M := M) (c := c) (show p - t ≤ p + t by linarith) le_rfl
    have key : lcProfit t M c m p - lcProfit t M c (p - t) p = M / (2 * t) * (p - t - m) ^ 2 := by
      rw [hmid, hpt, hm]; field_simp; ring
    have : 0 ≤ M / (2 * t) * (p - t - m) ^ 2 := by positivity
    rw [hpt] at key
    have hlt : (pj - c) * M < (p - t - c) * M := mul_lt_mul_of_pos_right (by linarith) hM
    have e : (p - t - c) * ((t + p - (p - t)) * M / (2 * t)) = (p - t - c) * M := by
      field_simp; ring
    linarith
  · rw [lcProfit_mid h h', hmid]
    have key : (m - c) * ((t + p - m) * M / (2 * t)) - (pj - c) * ((t + p - pj) * M / (2 * t)) =
        M / (2 * t) * (pj - m) ^ 2 := by rw [hm]; field_simp; ring
    have : 0 < M / (2 * t) * (pj - m) ^ 2 := by
      have : pj - m ≠ 0 := sub_ne_zero.2 hne
      positivity
    linarith

/-- **Best response, upper region** ((12.C.12), MWG, p. 398). If `p ≥ c + 3t`, the unique best
response is `p − t` (capturing the whole market), with strictly positive profit. -/
theorem lcBR_high {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h : c + 3 * t ≤ p) :
    0 < lcProfit t M c (p - t) p ∧
    ∀ pj, pj ≠ p - t → lcProfit t M c pj p < lcProfit t M c (p - t) p := by
  have hpt := lcProfit_mid (M := M) (c := c) (show p - t ≤ p + t by linarith) le_rfl
  have hval : lcProfit t M c (p - t) p = (p - t - c) * M := by
    rw [hpt]; field_simp; ring
  have hpos : 0 < lcProfit t M c (p - t) p := by rw [hval]; exact mul_pos (by linarith) hM
  refine ⟨hpos, fun pj hne => ?_⟩
  rcases lt_or_ge (p + t) pj with h1 | h1
  · rw [lcProfit_high h1]; exact hpos
  rcases lt_or_ge pj (p - t) with h2 | h2
  · rw [lcProfit_low ht h2, hval]; exact mul_lt_mul_of_pos_right (by linarith) hM
  · have hgt : p - t < pj := lt_of_le_of_ne h2 (Ne.symm hne)
    rw [lcProfit_mid h1 h2, hval]
    have key : (p - t - c) * M - (pj - c) * ((t + p - pj) * M / (2 * t)) =
        M / (2 * t) * (pj - (p - t)) * (pj - 2 * t - c) := by field_simp; ring
    have : 0 < M / (2 * t) * (pj - (p - t)) * (pj - 2 * t - c) := by
      apply mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
    linarith

/-- **Best response, lower region** ((12.C.12), MWG, p. 398). If `p ≤ c − t`, no price earns a
positive profit, and `p + t` (which sells nothing) is a best response. -/
theorem lcBR_low {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h : p ≤ c - t) :
    lcProfit t M c (p + t) p = 0 ∧ ∀ pj, lcProfit t M c pj p ≤ 0 := by
  refine ⟨?_, fun pj => ?_⟩
  · rw [lcProfit_mid le_rfl (by linarith)]; ring
  rcases lt_or_ge (p + t) pj with h1 | h1
  · rw [lcProfit_high h1]
  rcases lt_or_ge pj (p - t) with h2 | h2
  · rw [lcProfit_low ht h2]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
  · rw [lcProfit_mid h1 h2]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (div_nonneg (mul_nonneg (by linarith) hM.le) (by positivity))

/-- A Nash equilibrium of the linear-city pricing game. -/
def IsLCNash (t M c p1 p2 : ℝ) : Prop :=
  (∀ q, lcProfit t M c q p2 ≤ lcProfit t M c p1 p2) ∧
    ∀ q, lcProfit t M c q p1 ≤ lcProfit t M c p2 p1

/-- **Example 12.C.2** (MWG, pp. 396-398). With `t > 0`, `M > 0`: `p₁* = p₂* = c + t` is a Nash
equilibrium, each firm sells `M/2` and earns `tM/2`, and it is the only Nash equilibrium (there
are no asymmetric equilibria). -/
theorem example_12_C_2 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCNash t M c (c + t) (c + t) ∧ lcDemand t M (c + t) (c + t) = M / 2 ∧
    lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  have hm : (t + (c + t) + c) / 2 = c + t := by ring
  obtain ⟨_, hbr⟩ := lcBR_mid (M := M) ht hM (show c - t < c + t by linarith)
    (show c + t < c + 3 * t by linarith)
  rw [hm] at hbr
  have hNE : ∀ q, lcProfit t M c q (c + t) ≤ lcProfit t M c (c + t) (c + t) := fun q => by
    by_cases hq : q = c + t
    · rw [hq]
    · exact (hbr q hq).le
  have hdem : lcDemand t M (c + t) (c + t) = M / 2 := by
    unfold lcDemand
    split_ifs with a b
    · exfalso; linarith
    · exfalso; linarith
    · field_simp; ring
  refine ⟨⟨hNE, hNE⟩, hdem, by unfold lcProfit; rw [hdem]; ring, fun p1 p2 hne => ?_⟩
  -- a firm facing a price above `c − t` can earn a positive profit
  have hposprof : ∀ p, c - t < p → ∃ q, 0 < lcProfit t M c q p := by
    intro p hp
    rcases lt_or_ge p (c + 3 * t) with h | h
    · exact ⟨_, (lcBR_mid ht hM hp h).1⟩
    · exact ⟨_, (lcBR_high ht hM h).1⟩
  -- neither price is at most `c − t`
  have hlow : ∀ p p', (∀ q, lcProfit t M c q p' ≤ lcProfit t M c p p') →
      (∀ q, lcProfit t M c q p ≤ lcProfit t M c p' p) → c - t < p' := by
    intro p p' hbr1 hbr2
    by_contra hle
    push Not at hle
    -- the rival's best response sells nothing, so this firm sells `M` at a loss
    have h0 : lcProfit t M c p p' = 0 :=
      le_antisymm ((lcBR_low ht hM hle).2 p) (by
        have := hbr1 (p' + t); rw [(lcBR_low ht hM hle).1] at this; exact this)
    by_cases hp : p' + t < p
    · have : lcProfit t M c p' p = (p' - c) * M := by
        rw [lcProfit_low ht (show p' < p - t by linarith)]
      have hneg : lcProfit t M c p' p < 0 := by
        rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hM
      have hc := hbr2 (p + t + 1)
      rw [lcProfit_high (by linarith)] at hc
      linarith
    · push Not at hp
      rcases eq_or_lt_of_le hp with h3 | h3
      · -- `p = p' + t`: the rival sells everything at `p' < c`
        have : lcProfit t M c p' p = (p' - c) * M := by
          rw [lcProfit_mid (by linarith) (by linarith)]; rw [h3]; field_simp; ring
        have hneg : lcProfit t M c p' p < 0 := by
          rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hM
        have hc := hbr2 (p + t + 1)
        rw [lcProfit_high (by linarith)] at hc
        linarith
      · -- this firm sells a positive amount at a price below `c`
        have hp' : p < c := by linarith
        rcases lt_or_ge p (p' - t) with h2 | h2
        · rw [lcProfit_low ht h2] at h0
          have : (p - c) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
          linarith
        · rw [lcProfit_mid h3.le h2] at h0
          have : (p - c) * ((t + p' - p) * M / (2 * t)) < 0 :=
            mul_neg_of_neg_of_pos (by linarith)
              (div_pos (mul_pos (by linarith) hM) (by positivity))
          linarith
  have h2l := hlow p1 p2 hne.1 hne.2
  have h1l := hlow p2 p1 hne.2 hne.1
  -- neither price is at least `c + 3t`
  have hhigh : ∀ p p', (∀ q, lcProfit t M c q p' ≤ lcProfit t M c p p') →
      (∀ q, lcProfit t M c q p ≤ lcProfit t M c p' p) → c - t < p → p' < c + 3 * t := by
    intro p p' hbr1 hbr2 hp
    by_contra hge
    push Not at hge
    obtain ⟨hpos, huniq⟩ := lcBR_high ht hM hge
    have hpp : p = p' - t := by
      by_contra hne'
      linarith [huniq p hne', hbr1 (p' - t)]
    -- then the rival sells nothing although it could earn a positive profit
    obtain ⟨q, hq⟩ := hposprof p hp
    have : lcProfit t M c p' p = 0 := by
      rw [lcProfit_mid (by linarith) (by linarith), show t + p - p' = 0 by linarith]; ring
    linarith [hbr2 q]
  have h2h := hhigh p1 p2 hne.1 hne.2 h1l
  have h1h := hhigh p2 p1 hne.2 hne.1 h2l
  -- both prices are in the middle region: the unique best responses
  have e1 : p1 = (t + p2 + c) / 2 := by
    by_contra hne'
    linarith [(lcBR_mid ht hM h2l h2h).2 p1 hne', hne.1 ((t + p2 + c) / 2)]
  have e2 : p2 = (t + p1 + c) / 2 := by
    by_contra hne'
    linarith [(lcBR_mid ht hM h1l h1h).2 p2 hne', hne.2 ((t + p1 + c) / 2)]
  constructor <;> linarith

end MWG.MarketPower
