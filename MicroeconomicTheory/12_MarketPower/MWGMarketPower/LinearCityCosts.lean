/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Precommitment

/-!
# The linear city with different costs

MWG, Exercise 12.C.17, p. 433.

The linear city of Example 12.C.2 (`lcDemand`, `lcProfit`; nonpurchase ignored) with unit
costs `c₁ ≤ c₂`.

* `exercise_12_C_17`: if `c₂ − c₁ < 3t` the unique Nash equilibrium is
  `p₁ = t + (2c₁ + c₂)/3`, `p₂ = t + (c₁ + 2c₂)/3`, with both firms making positive sales
  `x₁ = M(t + (c₂ − c₁)/3)/(2t)`, `x₂ = M(t − (c₂ − c₁)/3)/(2t)`; if `c₂ − c₁ ≥ 3t` the Nash
  equilibria are exactly `p₁ = p₂ − t` with `c₁ + 3t ≤ p₂ ≤ c₂`, and in all of them firm 2 makes
  no sales and firm 1 serves the whole market. So an equilibrium with one firm making no sales
  occurs exactly when `c₂ − c₁ ≥ 3t`.
* `exercise_12_C_17_statics`: in the interior equilibrium `dp₁/dc₁ = 2/3`, `dp₂/dc₁ = 1/3`, firm
  1's profit `M(t + (c₂ − c₁)/3)²/(2t)` falls and firm 2's profit `M(t − (c₂ − c₁)/3)²/(2t)`
  rises with `c₁`.
-/

namespace MWG.MarketPower

/-- A Nash equilibrium of the linear-city pricing game with costs `c₁, c₂`. -/
def IsLCNash2 (t M c₁ c₂ p₁ p₂ : ℝ) : Prop :=
  (∀ q, lcProfit t M c₁ q p₂ ≤ lcProfit t M c₁ p₁ p₂) ∧
    ∀ q, lcProfit t M c₂ q p₁ ≤ lcProfit t M c₂ p₂ p₁

/-- A best response in the middle region is the unique one. -/
theorem lc2_br_mid {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p)
    (h2 : p < c + 3 * t) (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) :
    pj = (t + p + c) / 2 := by
  by_contra hne
  linarith [(lcBR_mid ht hM h1 h2).2 pj hne, hbr ((t + p + c) / 2)]

/-- A best response in the upper region is the unique one. -/
theorem lc2_br_high {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h : c + 3 * t ≤ p)
    (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) : pj = p - t := by
  by_contra hne
  linarith [(lcBR_high ht hM h).2 pj hne, hbr (p - t)]

/-- Against a rival price above `c − t` the best response is unique. -/
theorem lc2_br {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p)
    (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) :
    (p < c + 3 * t ∧ pj = (t + p + c) / 2) ∨ (c + 3 * t ≤ p ∧ pj = p - t) := by
  rcases lt_or_ge p (c + 3 * t) with h | h
  · exact Or.inl ⟨h, lc2_br_mid ht hM h1 h hbr⟩
  · exact Or.inr ⟨h, lc2_br_high ht hM h hbr⟩

/-- **Exercise 12.C.17** (MWG, p. 433). In the linear city with costs `c₁ ≤ c₂` (and `v` large):
if `c₂ − c₁ < 3t`, the unique Nash equilibrium is `p₁ = t + (2c₁ + c₂)/3`,
`p₂ = t + (c₁ + 2c₂)/3`, in which both firms make strictly positive sales; if `c₂ − c₁ ≥ 3t`, the
Nash equilibria are exactly the price pairs `p₁ = p₂ − t` with `c₁ + 3t ≤ p₂ ≤ c₂`, in which
firm 2 makes no sales and firm 1 sells to all `M` consumers. -/
theorem exercise_12_C_17 {t M c₁ c₂ : ℝ} (ht : 0 < t) (hM : 0 < M) (h12 : c₁ ≤ c₂) :
    (c₂ - c₁ < 3 * t → (∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ ↔
        p₁ = t + (2 * c₁ + c₂) / 3 ∧ p₂ = t + (c₁ + 2 * c₂) / 3) ∧
      lcDemand t M (t + (2 * c₁ + c₂) / 3) (t + (c₁ + 2 * c₂) / 3) =
        M * (t + (c₂ - c₁) / 3) / (2 * t) ∧
      lcDemand t M (t + (c₁ + 2 * c₂) / 3) (t + (2 * c₁ + c₂) / 3) =
        M * (t - (c₂ - c₁) / 3) / (2 * t) ∧
      0 < M * (t + (c₂ - c₁) / 3) / (2 * t) ∧ 0 < M * (t - (c₂ - c₁) / 3) / (2 * t)) ∧
    (3 * t ≤ c₂ - c₁ → (∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ ↔
        p₁ = p₂ - t ∧ c₁ + 3 * t ≤ p₂ ∧ p₂ ≤ c₂) ∧
      ∀ p₂, lcDemand t M p₂ (p₂ - t) = 0 ∧ lcDemand t M (p₂ - t) p₂ = M) := by
  -- every equilibrium is interior or a corner
  have hnec : ∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ →
      (p₁ = t + (2 * c₁ + c₂) / 3 ∧ p₂ = t + (c₁ + 2 * c₂) / 3 ∧ c₂ - c₁ < 3 * t) ∨
      (p₁ = p₂ - t ∧ c₁ + 3 * t ≤ p₂ ∧ p₂ ≤ c₂) := by
    rintro p₁ p₂ ⟨h1, h2⟩
    have hπ1 : 0 ≤ lcProfit t M c₁ p₁ p₂ := by
      have := h1 (p₂ + t + 1); rwa [lcProfit_high (by linarith)] at this
    have hπ2 : 0 ≤ lcProfit t M c₂ p₂ p₁ := by
      have := h2 (p₁ + t + 1); rwa [lcProfit_high (by linarith)] at this
    -- firm 2's price exceeds `c₁ − t`
    have hp2 : c₁ - t < p₂ := by
      by_contra hle
      push Not at hle
      have h0 : lcProfit t M c₁ p₁ p₂ = 0 := le_antisymm ((lcBR_low ht hM hle).2 p₁) hπ1
      rcases lt_trichotomy (p₂ + t) p₁ with h | h | h
      · have : lcProfit t M c₂ p₂ p₁ = (p₂ - c₂) * M := lcProfit_low ht (by linarith)
        have : (p₂ - c₂) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
        linarith
      · have : lcProfit t M c₂ p₂ p₁ = (p₂ - c₂) * M := by
          rw [lcProfit_mid (by linarith) (by linarith), ← h]; field_simp; ring
        have : (p₂ - c₂) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
        linarith
      · rcases lt_or_ge p₁ (p₂ - t) with h' | h'
        · rw [lcProfit_low ht h'] at h0
          have : (p₁ - c₁) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
          linarith
        · rw [lcProfit_mid h.le h'] at h0
          have : (p₁ - c₁) * ((t + p₂ - p₁) * M / (2 * t)) < 0 :=
            mul_neg_of_neg_of_pos (by linarith) (div_pos (mul_pos (by linarith) hM) (by positivity))
          linarith
    rcases le_or_gt p₁ (c₂ - t) with hA | hB
    · -- firm 2 cannot earn a positive profit
      have h20 : lcProfit t M c₂ p₂ p₁ = 0 := le_antisymm ((lcBR_low ht hM hA).2 p₂) hπ2
      rcases lc2_br ht hM hp2 h1 with ⟨hlt, he⟩ | ⟨hge, he⟩
      · exfalso
        have hsale : 0 < (t + p₁ - p₂) * M / (2 * t) :=
          div_pos (mul_pos (by rw [he]; linarith) hM) (by positivity)
        rw [lcProfit_mid (by rw [he]; linarith) (by rw [he]; linarith)] at h20
        have hp2c : p₂ = c₂ := by
          rcases mul_eq_zero.1 h20 with h | h
          · linarith
          · linarith
        rw [he, hp2c] at hA
        linarith
      · exact Or.inr ⟨he, hge, by linarith⟩
    · rcases lc2_br ht hM hB h2 with ⟨hlt2, he2⟩ | ⟨hge2, he2⟩
      · rcases lc2_br ht hM hp2 h1 with ⟨hlt1, he1⟩ | ⟨hge1, he1⟩
        · left
          refine ⟨by linarith, by linarith, ?_⟩
          have : p₁ = t + (2 * c₁ + c₂) / 3 := by linarith
          linarith
        · exfalso
          have : p₁ = c₂ - t := by linarith
          linarith
      · exfalso
        rcases lc2_br ht hM hp2 h1 with ⟨hlt1, he1⟩ | ⟨hge1, he1⟩
        · linarith
        · linarith
  constructor
  · intro hlt
    refine ⟨fun p₁ p₂ => ⟨fun hne => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rcases hnec p₁ p₂ hne with ⟨e1, e2, -⟩ | ⟨-, hge, hle⟩
      · exact ⟨e1, e2⟩
      · exfalso; linarith
    · rintro ⟨rfl, rfl⟩
      obtain ⟨hb1, hb2⟩ := linearCity_two_costs (M := M) ht hM (by linarith) hlt
      refine ⟨fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = t + (2 * c₁ + c₂) / 3
        · rw [hq]
        · exact (hb1 q hq).le
      · by_cases hq : q = t + (c₁ + 2 * c₂) / 3
        · rw [hq]
        · exact (hb2 q hq).le
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · exfalso; linarith
      · field_simp; ring
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · exfalso; linarith
      · field_simp; ring
    · exact div_pos (mul_pos hM (by linarith)) (by positivity)
    · exact div_pos (mul_pos hM (by linarith)) (by positivity)
  · intro hge
    refine ⟨fun p₁ p₂ => ⟨fun hne => ?_, ?_⟩, fun p₂ => ⟨?_, ?_⟩⟩
    · rcases hnec p₁ p₂ hne with ⟨-, -, hlt⟩ | h
      · exfalso; linarith
      · exact h
    · rintro ⟨rfl, hlo, hhi⟩
      refine ⟨fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = p₂ - t
        · rw [hq]
        · exact ((lcBR_high ht hM hlo).2 q hq).le
      · have hlow := lcBR_low (M := M) ht hM (show p₂ - t ≤ c₂ - t by linarith)
        rw [show p₂ - t + t = p₂ by ring] at hlow
        rw [hlow.1]
        exact hlow.2 q
    · unfold lcDemand
      split_ifs with a b
      · rfl
      · exfalso; linarith
      · rw [show t + (p₂ - t) - p₂ = 0 by ring]; simp
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · rfl
      · field_simp; ring

/-- **Exercise 12.C.17, local comparative statics** (MWG, p. 433). In the interior equilibrium
(`c₂ − c₁ < 3t`), `p₁ = t + (2c₁ + c₂)/3` and `p₂ = t + (c₁ + 2c₂)/3` rise with `c₁` at rates
`2/3` and `1/3`; firm 1's profit `M(t + (c₂ − c₁)/3)²/(2t)` falls and firm 2's profit
`M(t − (c₂ − c₁)/3)²/(2t)` rises with `c₁`. -/
theorem exercise_12_C_17_statics {t M c₂ : ℝ} (ht : 0 < t) (hM : 0 < M) (c₁ : ℝ)
    (h12 : c₁ ≤ c₂) (hlt : c₂ - c₁ < 3 * t) :
    lcProfit t M c₁ (t + (2 * c₁ + c₂) / 3) (t + (c₁ + 2 * c₂) / 3) =
      M * (t + (c₂ - c₁) / 3) ^ 2 / (2 * t) ∧
    lcProfit t M c₂ (t + (c₁ + 2 * c₂) / 3) (t + (2 * c₁ + c₂) / 3) =
      M * (t - (c₂ - c₁) / 3) ^ 2 / (2 * t) ∧
    HasDerivAt (fun c => t + (2 * c + c₂) / 3) (2 / 3) c₁ ∧
    HasDerivAt (fun c => t + (c + 2 * c₂) / 3) (1 / 3) c₁ ∧
    HasDerivAt (fun c => M * (t + (c₂ - c) / 3) ^ 2 / (2 * t))
      (-(M * (t + (c₂ - c₁) / 3) / (3 * t))) c₁ ∧ -(M * (t + (c₂ - c₁) / 3) / (3 * t)) < 0 ∧
    HasDerivAt (fun c => M * (t - (c₂ - c) / 3) ^ 2 / (2 * t))
      (M * (t - (c₂ - c₁) / 3) / (3 * t)) c₁ ∧ 0 < M * (t - (c₂ - c₁) / 3) / (3 * t) := by
  have hd1 := (exercise_12_C_17 (M := M) ht hM h12).1 hlt
  obtain ⟨-, hx1, hx2, -, -⟩ := hd1
  have hA : HasDerivAt (fun c => t + (c₂ - c) / 3) (-1 / 3) c₁ := by
    have := (((hasDerivAt_id c₁).const_sub c₂).div_const 3).const_add t
    simpa [neg_div] using this
  have hB : HasDerivAt (fun c => t - (c₂ - c) / 3) (1 / 3) c₁ := by
    have := (((hasDerivAt_id c₁).const_sub c₂).div_const 3).const_sub t
    simpa [neg_div] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lcProfit; rw [hx1]; field_simp; ring
  · unfold lcProfit; rw [hx2]; field_simp; ring
  · have := (((hasDerivAt_id c₁).const_mul 2).add_const c₂).div_const 3 |>.const_add t
    simpa using this
  · have := (((hasDerivAt_id c₁).add_const (2 * c₂)).div_const 3).const_add t
    simpa using this
  · convert ((hA.pow 2).const_mul M).div_const (2 * t) using 1
    field_simp; ring
  · have : 0 < M * (t + (c₂ - c₁) / 3) / (3 * t) :=
      div_pos (mul_pos hM (by linarith)) (by positivity)
    linarith
  · convert ((hB.pow 2).const_mul M).div_const (2 * t) using 1
    field_simp; ring
  · exact div_pos (mul_pos hM (by linarith)) (by positivity)

end MWG.MarketPower
