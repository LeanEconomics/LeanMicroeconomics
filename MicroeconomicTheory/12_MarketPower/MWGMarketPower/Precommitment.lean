/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.LinearCity
import MWGMarketPower.Cournot
import MWGMarketPower.MonopolyExercises

/-!
# Strategic precommitments

MWG, Section 12.G, pp. 414-417, Exercises 12.C.9, 12.C.17 (interior equilibria) and 12.G.1.

* `eq_12_G_1`: differentiating `s₂*(k) = b₂(b₁(s₂*(k), k))` gives
  `ds₂*/dk = b₂'·(∂b₁/∂k)/(1 − (∂b₁/∂s₂)b₂')` (12.G.1); `figure_12_G_1`: under the stability
  condition the sign of `ds₂*/dk` is that of `b₂'·∂b₁/∂k`.
* `eq_12_G_2`: `dπ₁/dk = ∂π₁/∂k + (∂π₁/∂s₂)(ds₂*/dk)` when `∂π₁/∂s₁ = 0` (12.G.2).
* `cournot_two_costs`: the interior Cournot equilibrium with costs `c₁, c₂` (Exercise 12.C.9(a));
  `linearCity_two_costs`: the interior linear-city equilibrium with costs `c₁, c₂`
  (Exercise 12.C.17).
* `example_12_G_1`, `exercise_12_G_1`: lowering firm 1's cost lowers firm 2's Cournot output
  (`dq₂/dc₁ = 1/(3b) > 0`, beneficial to firm 1) but lowers firm 2's price in the linear city
  (`dp₂/dc₁ = 1/3 > 0`, detrimental to firm 1).
-/

namespace MWG.MarketPower

open Set Filter Topology Function

/-- **Condition (12.G.1)** (MWG, p. 414). Suppose `s₂*(k) = b₂(b₁(s₂*(k), k))` for `k` near
`k₀`, `b₁` has derivative `L` at `(s₂*(k₀), k₀)`, `b₂` has derivative `β` at
`b₁(s₂*(k₀), k₀)`, and `s₂*` has derivative `d` at `k₀`. Then
`d·(1 − L(1,0)β) = β·L(0,1)`, i.e. `ds₂*/dk = b₂'(∂b₁/∂k)/(1 − (∂b₁/∂s₂)b₂')`. -/
theorem eq_12_G_1 {b1 : ℝ × ℝ → ℝ} {b2 s2 : ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {β d k₀ : ℝ}
    (hb1 : HasFDerivAt b1 L (s2 k₀, k₀)) (hb2 : HasDerivAt b2 β (b1 (s2 k₀, k₀)))
    (hs2 : HasDerivAt s2 d k₀) (hid : ∀ᶠ k in 𝓝 k₀, s2 k = b2 (b1 (s2 k, k))) :
    d * (1 - L (1, 0) * β) = β * L (0, 1) := by
  have hf : HasDerivAt (fun k => (s2 k, k)) (d, 1) k₀ := hs2.prodMk (hasDerivAt_id k₀)
  have h1 := HasFDerivAt.comp_hasDerivAt (f := fun k => (s2 k, k)) k₀ hb1 hf
  have h2 := hb2.comp k₀ h1
  have h3 : HasDerivAt (fun k => b2 (b1 (s2 k, k))) d k₀ :=
    hs2.congr_of_eventuallyEq (hid.mono fun k hk => hk.symm)
  have heq := h2.unique h3
  have hsplit : ((d, 1) : ℝ × ℝ) = d • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at heq
  linarith

/-- **Figure 12.G.1** (MWG, p. 415). Under the stability condition `1 − (∂b₁/∂s₂)b₂' > 0`, the
sign of `ds₂*/dk` is the sign of `b₂'·∂b₁/∂k`: with strategic substitutes (`b₂' < 0`) an
investment that makes firm 1 more aggressive (`∂b₁/∂k > 0`) lowers `s₂`, and with strategic
complements (`b₂' > 0`) it raises `s₂`. -/
theorem figure_12_G_1 {Lk Ls β d : ℝ} (hstab : 0 < 1 - Ls * β)
    (h : d * (1 - Ls * β) = β * Lk) : (0 < d ↔ 0 < β * Lk) ∧ (d < 0 ↔ β * Lk < 0) := by
  constructor
  · constructor
    · intro hd; rw [← h]; exact mul_pos hd hstab
    · intro hp; rw [← h] at hp; exact pos_of_mul_pos_left hp hstab.le
  · constructor
    · intro hd; rw [← h]; exact mul_neg_of_neg_of_pos hd hstab
    · intro hp; rw [← h] at hp
      by_contra hge; push Not at hge
      linarith [mul_nonneg hge hstab.le]

/-- **Condition (12.G.2)** (MWG, p. 416). If `π₁` has derivative `Lp` at
`(s₁*(k₀), s₂*(k₀), k₀)` with `∂π₁/∂s₁ = 0` there (stage-2 equilibrium), and `s₁*`, `s₂*` have
derivatives `d₁`, `d₂`, then `k ↦ π₁(s₁*(k), s₂*(k), k)` has derivative
`∂π₁/∂k + (∂π₁/∂s₂)d₂`: the direct effect plus the strategic effect. -/
theorem eq_12_G_2 {π1 : ℝ × ℝ × ℝ → ℝ} {s1 s2 : ℝ → ℝ} {Lp : ℝ × ℝ × ℝ →L[ℝ] ℝ} {d1 d2 k₀ : ℝ}
    (hπ : HasFDerivAt π1 Lp (s1 k₀, s2 k₀, k₀)) (hs1 : HasDerivAt s1 d1 k₀)
    (hs2 : HasDerivAt s2 d2 k₀) (hfoc : Lp (1, 0, 0) = 0) :
    HasDerivAt (fun k => π1 (s1 k, s2 k, k)) (Lp (0, 0, 1) + Lp (0, 1, 0) * d2) k₀ := by
  have hf : HasDerivAt (fun k => (s1 k, s2 k, k)) (d1, d2, 1) k₀ :=
    hs1.prodMk (hs2.prodMk (hasDerivAt_id k₀))
  have h := HasFDerivAt.comp_hasDerivAt (f := fun k => (s1 k, s2 k, k)) k₀ hπ hf
  refine h.congr_deriv ?_
  have hsplit : ((d1, d2, 1) : ℝ × ℝ × ℝ) =
      d1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + d2 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hfoc]
  ring

/-- **Exercise 12.C.9(a), interior case** (MWG, p. 431). In the linear Cournot duopoly with
costs `c₁, c₂`, if `a − 2c₁ + c₂ > 0` and `a − 2c₂ + c₁ > 0` then
`q₁ = (a − 2c₁ + c₂)/(3b)` and `q₂ = (a − 2c₂ + c₁)/(3b)` are mutual best responses (each is the
unique maximizer of the firm's profit over `q ≥ 0`). -/
theorem cournot_two_costs {a b c1 c2 : ℝ} (hb : 0 < b) (h1 : 0 < a - 2 * c1 + c2)
    (h2 : 0 < a - 2 * c2 + c1) :
    0 < (a - 2 * c1 + c2) / (3 * b) ∧ 0 < (a - 2 * c2 + c1) / (3 * b) ∧
    (∀ y, 0 ≤ y → (a - b * (y + (a - 2 * c2 + c1) / (3 * b))) * y - c1 * y ≤
      (a - b * ((a - 2 * c1 + c2) / (3 * b) + (a - 2 * c2 + c1) / (3 * b))) *
        ((a - 2 * c1 + c2) / (3 * b)) - c1 * ((a - 2 * c1 + c2) / (3 * b))) ∧
    (∀ y, 0 ≤ y → (a - b * (y + (a - 2 * c1 + c2) / (3 * b))) * y - c2 * y ≤
      (a - b * ((a - 2 * c2 + c1) / (3 * b) + (a - 2 * c1 + c2) / (3 * b))) *
        ((a - 2 * c2 + c1) / (3 * b)) - c2 * ((a - 2 * c2 + c1) / (3 * b))) := by
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · intro y _
    have key : (a - b * ((a - 2 * c1 + c2) / (3 * b) + (a - 2 * c2 + c1) / (3 * b))) *
        ((a - 2 * c1 + c2) / (3 * b)) - c1 * ((a - 2 * c1 + c2) / (3 * b)) -
        ((a - b * (y + (a - 2 * c2 + c1) / (3 * b))) * y - c1 * y) =
        b * (y - (a - 2 * c1 + c2) / (3 * b)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hb.le (sq_nonneg (y - (a - 2 * c1 + c2) / (3 * b)))]
  · intro y _
    have key : (a - b * ((a - 2 * c2 + c1) / (3 * b) + (a - 2 * c1 + c2) / (3 * b))) *
        ((a - 2 * c2 + c1) / (3 * b)) - c2 * ((a - 2 * c2 + c1) / (3 * b)) -
        ((a - b * (y + (a - 2 * c1 + c2) / (3 * b))) * y - c2 * y) =
        b * (y - (a - 2 * c2 + c1) / (3 * b)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hb.le (sq_nonneg (y - (a - 2 * c2 + c1) / (3 * b)))]

/-- **Exercise 12.C.17, interior case** (MWG, p. 433). In the linear city with costs `c₁, c₂`
and `|c₁ − c₂| < 3t`, the prices `p₁ = t + (2c₁ + c₂)/3`, `p₂ = t + (c₁ + 2c₂)/3` are mutual
best responses (each the unique best response, both firms selling a positive amount). -/
theorem linearCity_two_costs {t M c1 c2 : ℝ} (ht : 0 < t) (hM : 0 < M)
    (h12 : c1 - c2 < 3 * t) (h21 : c2 - c1 < 3 * t) :
    (∀ q, q ≠ t + (2 * c1 + c2) / 3 →
      lcProfit t M c1 q (t + (c1 + 2 * c2) / 3) <
        lcProfit t M c1 (t + (2 * c1 + c2) / 3) (t + (c1 + 2 * c2) / 3)) ∧
    (∀ q, q ≠ t + (c1 + 2 * c2) / 3 →
      lcProfit t M c2 q (t + (2 * c1 + c2) / 3) <
        lcProfit t M c2 (t + (c1 + 2 * c2) / 3) (t + (2 * c1 + c2) / 3)) := by
  have e1 : (t + (t + (c1 + 2 * c2) / 3) + c1) / 2 = t + (2 * c1 + c2) / 3 := by ring
  have e2 : (t + (t + (2 * c1 + c2) / 3) + c2) / 2 = t + (c1 + 2 * c2) / 3 := by ring
  obtain ⟨_, hb1⟩ := lcBR_mid (M := M) (c := c1) (p := t + (c1 + 2 * c2) / 3) ht hM
    (by linarith) (by linarith)
  obtain ⟨_, hb2⟩ := lcBR_mid (M := M) (c := c2) (p := t + (2 * c1 + c2) / 3) ht hM
    (by linarith) (by linarith)
  rw [e1] at hb1
  rw [e2] at hb2
  exact ⟨hb1, hb2⟩

/-- **Example 12.G.1 and Exercise 12.G.1** (MWG, pp. 415-416 and 435). In the interior Cournot
equilibrium firm 2's output `(a − 2c₂ + c₁)/(3b)` has derivative `1/(3b) > 0` in `c₁`, so a
reduction in firm 1's cost lowers firm 2's output (good for firm 1); in the interior linear-city
equilibrium firm 2's price `t + (c₁ + 2c₂)/3` has derivative `1/3 > 0` in `c₁`, so a reduction
in firm 1's cost lowers firm 2's price (bad for firm 1). -/
theorem example_12_G_1 {a b c2 t : ℝ} (hb : 0 < b) (c1 : ℝ) :
    HasDerivAt (fun c1 => (a - 2 * c2 + c1) / (3 * b)) (1 / (3 * b)) c1 ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c1 => t + (c1 + 2 * c2) / 3) (1 / 3) c1 ∧ (0 : ℝ) < 1 / 3 := by
  refine ⟨?_, by positivity, ?_, by norm_num⟩
  · have := ((hasDerivAt_id c1).const_add (a - 2 * c2)).div_const (3 * b)
    simpa using this
  · have := (((hasDerivAt_id c1).add_const (2 * c2)).div_const 3).const_add t
    simpa using this

/-- **Exercise 12.G.1** (MWG, p. 435): an alias of `example_12_G_1`. -/
theorem exercise_12_G_1 {a b c2 t : ℝ} (hb : 0 < b) (c1 : ℝ) :
    HasDerivAt (fun c1 => (a - 2 * c2 + c1) / (3 * b)) (1 / (3 * b)) c1 ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c1 => t + (c1 + 2 * c2) / 3) (1 / 3) c1 ∧ (0 : ℝ) < 1 / 3 :=
  example_12_G_1 hb c1

end MWG.MarketPower
