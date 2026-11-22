/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.LargeEconomies

/-!
# Footnote 71: a pair of replica sizes with no inclusion either way (MWG Section 17.I, p. 628)

Footnote 71 says that for `r'' > r' > 1` "there need not be any inclusion relationship between
`E(r'')` and `E(r')`". `LargeEconomies.lean` shows each inclusion failing for a different pair
in the economy of Figure 17.I.1. Here a single economy and the single pair `(r', r'') = (2, 3)`
have both `E(2) ⊄ E(3)` and `E(3) ⊄ E(2)` (`footnote_71_neither`).

The economy (two goods, consumption sets `ℝ²₊`, four types):
* type `1`: `u = x₁² + x₂²` (Chapter 16's `sqNormU`), `ω = (0, 1)`; at `p = (1, 1)` it demands
  the two corners `(1, 0)` and `(0, 1)`;
* type `2`: `u = (2x₁)² + x₂²` (`fn71SqU`), `ω = (0, 1)`; at `p' = (2, 1)` it demands the two
  corners `(1/2, 0)` and `(0, 1)`;
* type `3`: `u = min(x₁, x₂)`, `ω = (13, 0)`; type `4`: `u = min(x₁, x₂/4)`, `ω = (0, 25)`.

At `p` market clearing needs exactly half of the type-`1` consumers at `(1, 0)`, so `p ∈ E(2)`,
`p ∉ E(3)`; at `p'` it needs exactly a third of the type-`2` consumers at `(1/2, 0)`, so
`p' ∈ E(3)`, `p' ∉ E(2)`. Two nonconvex types switching at different prices are needed, and the
Leontief type `3` (a net seller of good `1` whose demand for good `1` rises with its price)
makes both clearing conditions compatible.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems

/-- **Footnote 71** (MWG, p. 628). The nonconvex utility `u = (2x₁)² + x₂²` of type `2`. -/
def fn71SqU (x : Fin 2 → ℝ) : ℝ := (2 * x 0) ^ 2 + x 1 ^ 2

/-- **Footnote 71** (MWG, p. 628). The Leontief utility `u = min(x₁, x₂)` of type `3`. -/
noncomputable def fn71LeoU (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1)

/-- **Footnote 71** (MWG, p. 628). The Leontief utility `u = min(x₁, x₂/4)` of type `4`. -/
noncomputable def fn71Leo4U (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1 / 4)

/-- **Footnote 71** (MWG, p. 628). The utilities of the four types. -/
noncomputable def fn71U : Fin 4 → (Fin 2 → ℝ) → ℝ := ![sqNormU, fn71SqU, fn71LeoU, fn71Leo4U]

/-- **Footnote 71** (MWG, p. 628). The endowments of the four types. -/
def fn71ω : Fin 4 → Fin 2 → ℝ := ![![0, 1], ![0, 1], ![13, 0], ![0, 25]]

/-- **Footnote 71** (MWG, p. 628). The four-type economy with `ℝ²₊` consumption sets. -/
noncomputable def fn71Economy : ExchangeEconomy (Fin 4) 2 :=
  ExchangeEconomy.ofOrthant fn71U fn71ω

/-- Demand in the economy `fn71Economy` at `p = (a, b)`, coordinatewise. -/
theorem fn71_demand_iff {i : Fin 4} {a b : ℝ} {x : Fin 2 → ℝ} :
    x ∈ fn71Economy.demand i ![a, b] ↔
      ((0 ≤ x 0 ∧ 0 ≤ x 1) ∧ a * x 0 + b * x 1 ≤ a * fn71ω i 0 + b * fn71ω i 1) ∧
        ∀ y : Fin 2 → ℝ, (0 ≤ y 0 ∧ 0 ≤ y 1) → a * y 0 + b * y 1 ≤ a * fn71ω i 0 + b * fn71ω i 1 →
          fn71U i y ≤ fn71U i x := by
  have hm : ∀ z : Fin 2 → ℝ, z ∈ nonnegOrthant 2 ↔ (0 ≤ z 0 ∧ 0 ≤ z 1) := fun z => by
    simp [nonnegOrthant, Fin.forall_fin_two]
  have hd : ∀ z : Fin 2 → ℝ, ![a, b] ⬝ᵥ z = a * z 0 + b * z 1 := fun z => by
    simp [dotProduct, Fin.sum_univ_two]
  unfold ExchangeEconomy.demand walrasianDemandOn budgetSetOn
  simp only [fn71Economy, ExchangeEconomy.ofOrthant, Set.mem_ofPred_eq, hm, hd, and_imp]

/-- The total endowment of `fn71Economy` is `(13, 27)`. -/
theorem fn71_totalEndowment : fn71Economy.totalEndowment = ![13, 27] := by
  funext l
  fin_cases l <;>
    norm_num [ExchangeEconomy.totalEndowment, fn71Economy, ExchangeEconomy.ofOrthant, fn71ω,
      Fin.sum_univ_four]

/-! ### Demands at `p = (1, 1)` -/

/-- At `p = (1, 1)` type `1` demands `(1, 0)`. -/
theorem fn71_t1_mem_10 : ![1, 0] ∈ fn71Economy.demand 0 ![1, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 1 * y 0 + 1 * y 1 ≤ 1 * 0 + 1 * 1 at hb
  change y 0 ^ 2 + y 1 ^ 2 ≤ (1 : ℝ) ^ 2 + 0 ^ 2
  nlinarith

/-- At `p = (1, 1)` type `1` demands `(0, 1)`. -/
theorem fn71_t1_mem_01 : ![0, 1] ∈ fn71Economy.demand 0 ![1, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 1 * y 0 + 1 * y 1 ≤ 1 * 0 + 1 * 1 at hb
  change y 0 ^ 2 + y 1 ^ 2 ≤ (0 : ℝ) ^ 2 + 1 ^ 2
  nlinarith

/-- At `p = (1, 1)` type `1` demands only bundles with `x₁ ∈ {0, 1}`. -/
theorem fn71_t1_one {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 0 ![1, 1]) :
    x 0 = 0 ∨ x 0 = 1 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hb⟩, hmax⟩ := hx
  have h := hmax ![1, 0] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change (1 : ℝ) ^ 2 + 0 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 at h
  change 1 * x 0 + 1 * x 1 ≤ 1 * 0 + 1 * 1 at hb
  have hprod : x 0 * x 1 = 0 := by nlinarith [mul_nonneg hx0 hx1]
  rcases mul_eq_zero.1 hprod with h0 | h1
  · exact Or.inl h0
  · right
    rw [h1] at h hb
    nlinarith

/-- At `p = (1, 1)` type `2` demands `(1, 0)`. -/
theorem fn71_t2_mem_10 : ![1, 0] ∈ fn71Economy.demand 1 ![1, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 1 * y 0 + 1 * y 1 ≤ 1 * 0 + 1 * 1 at hb
  change (2 * y 0) ^ 2 + y 1 ^ 2 ≤ (2 * 1 : ℝ) ^ 2 + 0 ^ 2
  nlinarith

/-- At `p = (1, 1)` type `2` demands only `x₁ = 1`. -/
theorem fn71_t2_one {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 1 ![1, 1]) : x 0 = 1 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hb⟩, hmax⟩ := hx
  have h := hmax ![1, 0] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change (2 * 1 : ℝ) ^ 2 + 0 ^ 2 ≤ (2 * x 0) ^ 2 + x 1 ^ 2 at h
  change 1 * x 0 + 1 * x 1 ≤ 1 * 0 + 1 * 1 at hb
  have hx1' : x 1 ≤ 1 - x 0 := by linarith
  have hsq : x 1 ^ 2 ≤ (1 - x 0) ^ 2 := by nlinarith
  nlinarith

/-- At `p = (1, 1)` type `3` demands `(13/2, 13/2)`. -/
theorem fn71_t3_mem_one : ![13 / 2, 13 / 2] ∈ fn71Economy.demand 2 ![1, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 1 * y 0 + 1 * y 1 ≤ 1 * 13 + 1 * 0 at hb
  change min (y 0) (y 1) ≤ min (13 / 2 : ℝ) (13 / 2)
  rw [min_self, min_le_iff]
  by_contra h
  push Not at h
  linarith

/-- At `p = (1, 1)` type `3` demands only `x₁ = 13/2`. -/
theorem fn71_t3_one {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 2 ![1, 1]) :
    x 0 = 13 / 2 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨-, hb⟩, hmax⟩ := hx
  have h := hmax ![13 / 2, 13 / 2] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change min (13 / 2 : ℝ) (13 / 2) ≤ min (x 0) (x 1) at h
  change 1 * x 0 + 1 * x 1 ≤ 1 * 13 + 1 * 0 at hb
  rw [min_self, le_min_iff] at h
  linarith

/-- At `p = (1, 1)` type `4` demands `(5, 20)`. -/
theorem fn71_t4_mem_one : ![5, 20] ∈ fn71Economy.demand 3 ![1, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 1 * y 0 + 1 * y 1 ≤ 1 * 0 + 1 * 25 at hb
  change min (y 0) (y 1 / 4) ≤ min (5 : ℝ) (20 / 4)
  rw [min_le_iff]
  by_contra h
  push Not at h
  norm_num at h
  linarith

/-- At `p = (1, 1)` type `4` demands only `x₁ = 5`. -/
theorem fn71_t4_one {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 3 ![1, 1]) : x 0 = 5 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨-, hb⟩, hmax⟩ := hx
  have h := hmax ![5, 20] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change min (5 : ℝ) (20 / 4) ≤ min (x 0) (x 1 / 4) at h
  change 1 * x 0 + 1 * x 1 ≤ 1 * 0 + 1 * 25 at hb
  rw [le_min_iff] at h
  norm_num at h
  linarith

/-! ### Demands at `p' = (2, 1)` -/

/-- At `p' = (2, 1)` type `1` demands `(0, 1)`. -/
theorem fn71_t1_mem_two : ![0, 1] ∈ fn71Economy.demand 0 ![2, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 2 * y 0 + 1 * y 1 ≤ 2 * 0 + 1 * 1 at hb
  change y 0 ^ 2 + y 1 ^ 2 ≤ (0 : ℝ) ^ 2 + 1 ^ 2
  nlinarith

/-- At `p' = (2, 1)` type `1` demands only `x₁ = 0`. -/
theorem fn71_t1_two {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 0 ![2, 1]) : x 0 = 0 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hb⟩, hmax⟩ := hx
  have h := hmax ![0, 1] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change (0 : ℝ) ^ 2 + 1 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 at h
  change 2 * x 0 + 1 * x 1 ≤ 2 * 0 + 1 * 1 at hb
  have hsq : x 1 ^ 2 ≤ (1 - 2 * x 0) ^ 2 := by nlinarith
  nlinarith

/-- At `p' = (2, 1)` type `2` demands `(1/2, 0)`. -/
theorem fn71_t2_mem_half : ![1 / 2, 0] ∈ fn71Economy.demand 1 ![2, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 2 * y 0 + 1 * y 1 ≤ 2 * 0 + 1 * 1 at hb
  change (2 * y 0) ^ 2 + y 1 ^ 2 ≤ (2 * (1 / 2) : ℝ) ^ 2 + 0 ^ 2
  nlinarith

/-- At `p' = (2, 1)` type `2` demands `(0, 1)`. -/
theorem fn71_t2_mem_01 : ![0, 1] ∈ fn71Economy.demand 1 ![2, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 2 * y 0 + 1 * y 1 ≤ 2 * 0 + 1 * 1 at hb
  change (2 * y 0) ^ 2 + y 1 ^ 2 ≤ (2 * 0 : ℝ) ^ 2 + 1 ^ 2
  nlinarith

/-- At `p' = (2, 1)` type `2` demands only bundles with `x₁ ∈ {0, 1/2}`. -/
theorem fn71_t2_two {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 1 ![2, 1]) :
    x 0 = 0 ∨ x 0 = 1 / 2 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hb⟩, hmax⟩ := hx
  have h := hmax ![0, 1] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change (2 * 0 : ℝ) ^ 2 + 1 ^ 2 ≤ (2 * x 0) ^ 2 + x 1 ^ 2 at h
  change 2 * x 0 + 1 * x 1 ≤ 2 * 0 + 1 * 1 at hb
  have hprod : x 0 * x 1 = 0 := by nlinarith [mul_nonneg hx0 hx1]
  rcases mul_eq_zero.1 hprod with h0 | h1
  · exact Or.inl h0
  · right
    rw [h1] at h hb
    nlinarith

/-- At `p' = (2, 1)` type `3` demands `(26/3, 26/3)`. -/
theorem fn71_t3_mem_two : ![26 / 3, 26 / 3] ∈ fn71Economy.demand 2 ![2, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 2 * y 0 + 1 * y 1 ≤ 2 * 13 + 1 * 0 at hb
  change min (y 0) (y 1) ≤ min (26 / 3 : ℝ) (26 / 3)
  rw [min_self, min_le_iff]
  by_contra h
  push Not at h
  linarith

/-- At `p' = (2, 1)` type `3` demands only `x₁ = 26/3`. -/
theorem fn71_t3_two {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 2 ![2, 1]) :
    x 0 = 26 / 3 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨-, hb⟩, hmax⟩ := hx
  have h := hmax ![26 / 3, 26 / 3] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change min (26 / 3 : ℝ) (26 / 3) ≤ min (x 0) (x 1) at h
  change 2 * x 0 + 1 * x 1 ≤ 2 * 13 + 1 * 0 at hb
  rw [min_self, le_min_iff] at h
  linarith

/-- At `p' = (2, 1)` type `4` demands `(25/6, 50/3)`. -/
theorem fn71_t4_mem_two : ![25 / 6, 50 / 3] ∈ fn71Economy.demand 3 ![2, 1] := by
  rw [fn71_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [fn71ω]⟩, fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change 2 * y 0 + 1 * y 1 ≤ 2 * 0 + 1 * 25 at hb
  change min (y 0) (y 1 / 4) ≤ min (25 / 6 : ℝ) (50 / 3 / 4)
  rw [min_le_iff]
  by_contra h
  push Not at h
  norm_num at h
  linarith

/-- At `p' = (2, 1)` type `4` demands only `x₁ = 25/6`. -/
theorem fn71_t4_two {x : Fin 2 → ℝ} (hx : x ∈ fn71Economy.demand 3 ![2, 1]) :
    x 0 = 25 / 6 := by
  rw [fn71_demand_iff] at hx
  obtain ⟨⟨-, hb⟩, hmax⟩ := hx
  have h := hmax ![25 / 6, 50 / 3] ⟨by norm_num, by norm_num⟩ (by norm_num [fn71ω])
  change min (25 / 6 : ℝ) (50 / 3 / 4) ≤ min (x 0) (x 1 / 4) at h
  change 2 * x 0 + 1 * x 1 ≤ 2 * 0 + 1 * 25 at hb
  rw [le_min_iff] at h
  norm_num at h
  linarith

/-! ### The equilibrium price sets -/

/-- Good-`1` market clearing in a replica of `fn71Economy`, type by type. -/
theorem fn71_clear0 {r : ℕ} {p : Fin 2 → ℝ} {x : Fin 4 × Fin r → Fin 2 → ℝ}
    (h : (replica fn71Economy r).IsDemandEqm p x) :
    ∑ k, x (0, k) 0 + ∑ k, x (1, k) 0 + ∑ k, x (2, k) 0 + ∑ k, x (3, k) 0 = r * 13 := by
  have h2 := congrFun h.1.2 0
  rw [Finset.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_four, replica_totalEndowment,
    fn71_totalEndowment] at h2
  simpa [Finset.sum_apply] using h2

/-- `p = (1, 1)` is an equilibrium price of the `2`-replica of `fn71Economy`. -/
theorem fn71_one_mem_two : ![1, 1] ∈ eqmPriceSet (replica fn71Economy 2) := by
  set xs : Fin 4 → Fin 2 → Fin 2 → ℝ :=
    ![![![1, 0], ![0, 1]], ![![1, 0], ![1, 0]], ![![13 / 2, 13 / 2], ![13 / 2, 13 / 2]],
      ![![5, 20], ![5, 20]]] with hxs
  refine ⟨fun c => xs c.1 c.2, ⟨fun c => ?_, ?_⟩, fun c => ?_⟩
  · change xs c.1 c.2 ∈ nonnegOrthant 2
    intro l
    obtain ⟨i, k⟩ := c
    fin_cases i <;> fin_cases k <;> fin_cases l <;> simp [hxs] <;> norm_num
  · rw [replica_totalEndowment, fn71_totalEndowment]
    funext l
    fin_cases l <;>
      simp [hxs, Fintype.sum_prod_type, Fin.sum_univ_four, Finset.sum_apply] <;> norm_num
  · obtain ⟨i, k⟩ := c
    change xs i k ∈ fn71Economy.demand i ![1, 1]
    fin_cases i <;> fin_cases k
    · exact fn71_t1_mem_10
    · exact fn71_t1_mem_01
    · exact fn71_t2_mem_10
    · exact fn71_t2_mem_10
    · exact fn71_t3_mem_one
    · exact fn71_t3_mem_one
    · exact fn71_t4_mem_one
    · exact fn71_t4_mem_one

/-- `p' = (2, 1)` is an equilibrium price of the `3`-replica of `fn71Economy`. -/
theorem fn71_two_mem_three : ![2, 1] ∈ eqmPriceSet (replica fn71Economy 3) := by
  set xs : Fin 4 → Fin 3 → Fin 2 → ℝ :=
    ![![![0, 1], ![0, 1], ![0, 1]], ![![1 / 2, 0], ![0, 1], ![0, 1]],
      ![![26 / 3, 26 / 3], ![26 / 3, 26 / 3], ![26 / 3, 26 / 3]],
      ![![25 / 6, 50 / 3], ![25 / 6, 50 / 3], ![25 / 6, 50 / 3]]] with hxs
  refine ⟨fun c => xs c.1 c.2, ⟨fun c => ?_, ?_⟩, fun c => ?_⟩
  · change xs c.1 c.2 ∈ nonnegOrthant 2
    intro l
    obtain ⟨i, k⟩ := c
    fin_cases i <;> fin_cases k <;> fin_cases l <;> simp [hxs] <;> norm_num
  · rw [replica_totalEndowment, fn71_totalEndowment]
    funext l
    fin_cases l <;>
      simp [hxs, Fintype.sum_prod_type, Fin.sum_univ_four, Finset.sum_apply,
        Fin.sum_univ_three] <;> norm_num
  · obtain ⟨i, k⟩ := c
    change xs i k ∈ fn71Economy.demand i ![2, 1]
    fin_cases i <;> fin_cases k
    · exact fn71_t1_mem_two
    · exact fn71_t1_mem_two
    · exact fn71_t1_mem_two
    · exact fn71_t2_mem_half
    · exact fn71_t2_mem_01
    · exact fn71_t2_mem_01
    · exact fn71_t3_mem_two
    · exact fn71_t3_mem_two
    · exact fn71_t3_mem_two
    · exact fn71_t4_mem_two
    · exact fn71_t4_mem_two
    · exact fn71_t4_mem_two

/-- `p = (1, 1)` is not an equilibrium price of the `3`-replica: clearing would need one and a
half type-`1` consumers at `(1, 0)`. -/
theorem fn71_one_not_mem_three : ![1, 1] ∉ eqmPriceSet (replica fn71Economy 3) := by
  rintro ⟨x, hx⟩
  have hd : ∀ c, x c ∈ fn71Economy.demand c.1 ![1, 1] := hx.2
  have hc := fn71_clear0 hx
  simp only [Fin.sum_univ_three, fn71_t2_one (hd (1, _)), fn71_t3_one (hd (2, _)),
    fn71_t4_one (hd (3, _))] at hc
  rcases fn71_t1_one (hd (0, 0)) with h0 | h0 <;> rcases fn71_t1_one (hd (0, 1)) with h1 | h1 <;>
    rcases fn71_t1_one (hd (0, 2)) with h2 | h2 <;> rw [h0, h1, h2] at hc <;> norm_num at hc

/-- `p' = (2, 1)` is not an equilibrium price of the `2`-replica: clearing would need two thirds
of a type-`2` consumer at `(1/2, 0)`. -/
theorem fn71_two_not_mem_two : ![2, 1] ∉ eqmPriceSet (replica fn71Economy 2) := by
  rintro ⟨x, hx⟩
  have hd : ∀ c, x c ∈ fn71Economy.demand c.1 ![2, 1] := hx.2
  have hc := fn71_clear0 hx
  simp only [Fin.sum_univ_two, fn71_t1_two (hd (0, _)), fn71_t3_two (hd (2, _)),
    fn71_t4_two (hd (3, _))] at hc
  rcases fn71_t2_two (hd (1, 0)) with h0 | h0 <;> rcases fn71_t2_two (hd (1, 1)) with h1 | h1 <;>
    rw [h0, h1] at hc <;> norm_num at hc

/-- **Footnote 71** (MWG, p. 628). "For arbitrary `r'' > r' > 1`, there need not be any inclusion
relationship between `E(r'')` and `E(r')`": in `fn71Economy` (two nonconvex and two Leontief
types), `E(2) ⊄ E(3)` and `E(3) ⊄ E(2)`, witnessed by `p = (1, 1)` and `p' = (2, 1)`. -/
theorem footnote_71_neither :
    ¬ eqmPriceSet (replica fn71Economy 2) ⊆ eqmPriceSet (replica fn71Economy 3) ∧
      ¬ eqmPriceSet (replica fn71Economy 3) ⊆ eqmPriceSet (replica fn71Economy 2) :=
  ⟨fun h => fn71_one_not_mem_three (h fn71_one_mem_two),
    fun h => fn71_two_not_mem_two (h fn71_two_mem_three)⟩

end MWG.PositiveEquilibriumTheory
