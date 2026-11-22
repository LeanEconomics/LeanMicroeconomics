/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Bertrand

/-!
# Product differentiation: prices above cost

MWG, Section 12.C, pp. 395-396, and footnote 13.

There are `J > 1` firms with constant marginal cost `c`; firm `j`'s demand `x_j(p_j, p_{-j})` is
continuous, and firm `j` chooses `p_j` to maximize `(p_j − c)x_j(p_j, p̄_{-j})`. Fixing the rivals'
prices, write `f(p) = x_j(p, p̄_{-j})`.

* `diffProducts_profitable`: if `x_j(c, p̄_{-j}) > 0` and `x_j` is continuous in its own price at
  `c`, firm `j` can assure itself a strictly positive profit by setting its price slightly above
  `c`.
* `diffProducts_br_above_cost`: hence every best response is a price strictly above cost.
* `diffProducts_eqm_above_cost`: in every Nash equilibrium in which `x_j(c, p*_{-j}) > 0` for all
  `j`, every equilibrium price exceeds `c`.
* `footnote_12_13`: in the Bertrand model `x_j(p_j, p_{-j})` is discontinuous at
  `p_j = min_{k ≠ j} p_k` whenever demand is positive there.

Departure: demand is taken nonnegative (it is a quantity demanded); without this a "profit"
`(p − c)x` could be positive at `p < c` with negative `x`.
-/

namespace MWG.MarketPower

open Filter Topology Function

/-- **Product differentiation** (MWG, p. 396). If `x_j(c, p̄_{-j}) > 0` and firm `j`'s demand is
continuous in its own price at `c`, some price `p > c` earns a strictly positive profit. -/
theorem diffProducts_profitable {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) (hpos : 0 < f c) :
    ∃ p, c < p ∧ 0 < (p - c) * f p := by
  have h1 : ∀ᶠ p in 𝓝[>] c, 0 < f p := nhdsWithin_le_nhds (hf.eventually (lt_mem_nhds hpos))
  have hev : ∀ᶠ p in 𝓝[>] c, 0 < f p ∧ c < p := h1.and self_mem_nhdsWithin
  obtain ⟨p, hp, hcp⟩ := hev.exists
  exact ⟨p, hcp, mul_pos (by linarith) hp⟩

/-- **Product differentiation** (MWG, p. 396). As long as `x_j(c, p̄_{-j}) > 0`, firm `j`'s best
response to `p̄_{-j}` is a price strictly above cost. -/
theorem diffProducts_br_above_cost {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) (hpos : 0 < f c)
    (hnn : ∀ p, 0 ≤ f p) {ps : ℝ} (hbr : ∀ p, (p - c) * f p ≤ (ps - c) * f ps) : c < ps := by
  obtain ⟨p, _, hp⟩ := diffProducts_profitable hf hpos
  have h := lt_of_lt_of_le hp (hbr p)
  by_contra hle
  push Not at hle
  have : (ps - c) * f ps ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hnn ps)
  linarith

/-- **Product differentiation** (MWG, p. 396). In a Nash equilibrium `p*` of the simultaneous
price game with demands `x_j(p)` (`x j p`), nonnegative and continuous in own price, if
`x_j(c, p*_{-j}) > 0` for every `j` then every equilibrium price is above cost: "equilibrium
prices will be above the competitive level". -/
theorem diffProducts_eqm_above_cost {ι : Type*} [DecidableEq ι] {x : ι → (ι → ℝ) → ℝ} {c : ℝ}
    {ps : ι → ℝ} (hnn : ∀ j p, 0 ≤ x j p)
    (hcont : ∀ j, ContinuousAt (fun q => x j (update ps j q)) c)
    (hpos : ∀ j, 0 < x j (update ps j c))
    (hne : ∀ j q, (q - c) * x j (update ps j q) ≤ (ps j - c) * x j ps) (j : ι) : c < ps j := by
  refine diffProducts_br_above_cost (f := fun q => x j (update ps j q)) (hcont j) (hpos j)
    (fun p => hnn j _) (fun p => ?_)
  simp only [update_eq_self]
  exact hne j p

/-- The hypotheses of `diffProducts_br_above_cost` are satisfiable: `x(p) = max(0, 1 − p)`,
`c = 1/2`, best response `3/4`. -/
theorem diffProducts_instance :
    ContinuousAt (fun p : ℝ => max 0 (1 - p)) (1 / 2) ∧ 0 < max 0 (1 - (1 / 2 : ℝ)) ∧
    (∀ p : ℝ, 0 ≤ max 0 (1 - p)) ∧
    ∀ p : ℝ, (p - 1 / 2) * max 0 (1 - p) ≤ (3 / 4 - 1 / 2) * max 0 (1 - (3 / 4 : ℝ)) := by
  refine ⟨(continuous_const.max (continuous_const.sub continuous_id)).continuousAt,
    by norm_num, fun p => le_max_left _ _, fun p => ?_⟩
  rw [show max 0 (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num]
  rcases le_total (1 - p) 0 with h | h
  · rw [max_eq_left h]; norm_num
  · rw [max_eq_right h]; nlinarith [sq_nonneg (p - 3 / 4)]

/-- **Footnote 13** (MWG, p. 395). In the Bertrand model firm `j`'s demand `x_j(p_j, p_{-j})` is
discontinuous in `p_j` at `p_j = min_{k ≠ j} p_k = m` whenever `x(m) > 0`: there `j` sells
`x(m)/J̄ > 0`, while at every higher price it sells nothing. -/
theorem footnote_12_13 {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ℝ → ℝ} (p : ι → ℝ) {j k : ι}
    (hkj : k ≠ j) (hmin : ∀ l, l ≠ j → p k ≤ p l) (hxpos : 0 < x (p k)) :
    0 < bertrandSales x (update p j (p k)) j ∧
    (∀ q, p k < q → bertrandSales x (update p j q) j = 0) ∧
    ¬ ContinuousAt (fun q => bertrandSales x (update p j q) j) (p k) := by
  have hval : 0 < bertrandSales x (update p j (p k)) j := by
    unfold bertrandSales
    have hall : ∀ l, p k ≤ update p j (p k) l := by
      intro l
      by_cases hl : l = j
      · rw [hl, update_self]
      · rw [update_of_ne hl]; exact hmin l hl
    simp only [update_self]
    simp only [hall, implies_true, ↓reduceIte]
    apply div_pos hxpos
    exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩
  have hzero : ∀ q, p k < q → bertrandSales x (update p j q) j = 0 := by
    intro q hq
    apply bertrandSales_of_gt (k := k)
    rw [update_self, update_of_ne hkj]; exact hq
  refine ⟨hval, hzero, fun hc => ?_⟩
  have hev : ∀ᶠ q in 𝓝[>] (p k), 0 < bertrandSales x (update p j q) j :=
    nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds hval))
  obtain ⟨q, hq, hqk⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [hzero q hqk] at hq
  exact lt_irrefl _ hq

/-- The hypotheses of `footnote_12_13` are satisfiable: two firms at the price `1`, demand
`x(p) = max(0, 2 − p)`. -/
theorem footnote_12_13_instance :
    (1 : Fin 2) ≠ 0 ∧ (∀ l : Fin 2, l ≠ 0 → (fun _ : Fin 2 => (1 : ℝ)) 1 ≤ (fun _ => 1) l) ∧
      0 < max 0 (2 - (fun _ : Fin 2 => (1 : ℝ)) 1) :=
  ⟨by decide, fun _ _ => le_rfl, by norm_num⟩

end MWG.MarketPower
