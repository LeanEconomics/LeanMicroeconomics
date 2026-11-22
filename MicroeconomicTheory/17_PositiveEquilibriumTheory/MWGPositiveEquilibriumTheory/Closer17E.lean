/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17E

/-!
# Exercise 17.E.5 with three consumers (MWG Section 17.E, pp. 604 and 645)

`exercise_17_E_5` excludes two consumers and `exercise_17_E_5_four` shows that the weak-axiom
obstruction disappears with four. Here the case of three consumers is closed.

* `ex17E5_shares`: for any finite set of consumers with consumption sets `ℝ²₊`, endowments
  `≤ (1, 1)` and single-valued demands at `p` and `p'` generating `z(p) = (-1, a)` and
  `z(p') = (b, -1)`, the shares `αᵢ = -zᵢ₁(p)` and `βᵢ = -zᵢ₂(p')` satisfy `∑ αᵢ = ∑ βᵢ = 1`,
  `αᵢ, βᵢ ≤ 1`, and, by the weak axiom, for every consumer `αᵢ < 0`, or `βᵢ < 0`, or
  `αᵢ = βᵢ = 0`.
* `exercise_17_E_5_three`: no such economy with three consumers (the count: a negative `α`
  needs two positive `α`'s, whose consumers have negative `β`'s, and then `∑ β < 1`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

/-- **Exercise 17.E.5** (MWG, p. 645), the constraints on the individual shares, for any finite
number of consumers. -/
theorem ex17E5_shares {ι : Type*} [Fintype ι] {p p' : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (hp' : StrictlyPositive p') (hslope : p 0 * p' 1 < p' 0 * p 1) {a b : ℝ}
    (hza : p ⬝ᵥ ![-1, a] = 0) (hzb : p' ⬝ᵥ ![b, -1] = 0) (E : ExchangeEconomy ι 2)
    (hX : ∀ i, E.X i = nonnegOrthant 2) (hω : ∀ i l, E.ω i l ≤ 1)
    (hd : ∀ i, ∃ x, E.demand i p = {x}) (hd' : ∀ i, ∃ x, E.demand i p' = {x})
    (hz : excessDemand E p = ![-1, a]) (hz' : excessDemand E p' = ![b, -1]) :
    ∃ α β : ι → ℝ, ∑ i, α i = 1 ∧ ∑ i, β i = 1 ∧ (∀ i, α i ≤ 1 ∧ β i ≤ 1) ∧
      ∀ i, α i < 0 ∨ β i < 0 ∨ (α i = 0 ∧ β i = 0) := by
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hza hzb
  have hp0 := hp 0
  have hp1 := hp 1
  have hp0' := hp' 0
  have hp1' := hp' 1
  choose x hx using hd
  choose x' hx' using hd'
  have hxm : ∀ i, x i ∈ E.demand i p := fun i => by rw [hx i]; rfl
  have hxm' : ∀ i, x' i ∈ E.demand i p' := fun i => by rw [hx' i]; rfl
  have hdf : ∀ i, demandFn E i p = x i := fun i => demandFn_eq E (hx i)
  have hdf' : ∀ i, demandFn E i p' = x' i := fun i => demandFn_eq E (hx' i)
  set z := fun i => x i - E.ω i with hzdef
  set z' := fun i => x' i - E.ω i with hz'def
  have hsum : ∀ l, ∑ i, z i l = ![-1, a] l := by
    intro l
    rw [← hz, excessDemand_apply]
    simp only [hdf, z, Pi.sub_apply]
  have hsum' : ∀ l, ∑ i, z' i l = ![b, -1] l := by
    intro l
    rw [← hz', excessDemand_apply]
    simp only [hdf', z', Pi.sub_apply]
  have hs0 := hsum 0
  have hs1 := hsum 1
  have hs0' := hsum' 0
  have hs1' := hsum' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1 hs0' hs1'
  -- affordability, hence individual Walras' law
  have haff : ∀ i, p 0 * z i 0 + p 1 * z i 1 ≤ 0 := by
    intro i
    have := (hxm i).1.2
    simp only [dotProduct, Fin.sum_univ_two] at this
    simp only [z, Pi.sub_apply]; linarith
  have haff' : ∀ i, p' 0 * z' i 0 + p' 1 * z' i 1 ≤ 0 := by
    intro i
    have := (hxm' i).1.2
    simp only [dotProduct, Fin.sum_univ_two] at this
    simp only [z', Pi.sub_apply]; linarith
  have htot : ∑ i, (p 0 * z i 0 + p 1 * z i 1) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs0, hs1]
    linarith
  have htot' : ∑ i, (p' 0 * z' i 0 + p' 1 * z' i 1) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs0', hs1']
    linarith
  have hW : ∀ i, p 0 * z i 0 + p 1 * z i 1 = 0 := fun i =>
    le_antisymm (haff i) ((Finset.sum_eq_zero_iff_of_nonpos fun j _ => haff j).1 htot i
      (Finset.mem_univ i)).ge
  have hW' : ∀ i, p' 0 * z' i 0 + p' 1 * z' i 1 = 0 := fun i =>
    le_antisymm (haff' i) ((Finset.sum_eq_zero_iff_of_nonpos fun j _ => haff' j).1 htot' i
      (Finset.mem_univ i)).ge
  -- bounds from the endowments
  have hbd : ∀ i, -1 ≤ z i 0 := by
    intro i
    have h1 := (hxm i).1.1
    rw [hX i] at h1
    have := hω i 0
    simp only [z, Pi.sub_apply]; linarith [h1 0]
  have hbd' : ∀ i, -1 ≤ z' i 1 := by
    intro i
    have h1 := (hxm' i).1.1
    rw [hX i] at h1
    have := hω i 1
    simp only [z', Pi.sub_apply]; linarith [h1 1]
  refine ⟨fun i => -z i 0, fun i => -z' i 1, ?_, ?_, fun i => ⟨by linarith [hbd i],
    by linarith [hbd' i]⟩, fun i => ?_⟩
  · simp only [Finset.sum_neg_distrib, hs0, neg_neg]
  · simp only [Finset.sum_neg_distrib, hs1', neg_neg]
  -- the weak axiom
  by_cases hα : z i 0 ≤ 0
  · by_cases hβ : z' i 1 ≤ 0
    · right; right
      have hb1 : x' i ∈ budgetSetOn (E.X i) p (p ⬝ᵥ E.ω i) := by
        refine ⟨(hxm' i).1.1, ?_⟩
        have hz1 : z' i 0 = -(p' 1 / p' 0) * z' i 1 := by
          have := hW' i; field_simp; linarith
        have hneg : p 0 * (p' 1 / p' 0) - p 1 ≤ 0 := by
          rw [mul_div_assoc', div_sub' hp0'.ne', div_nonpos_iff]
          right; constructor <;> nlinarith
        have hz'x : x' i = z' i + E.ω i := by simp [z']
        have : p 0 * z' i 0 + p 1 * z' i 1 ≤ 0 := by
          rw [hz1]
          nlinarith
        rw [hz'x, dotProduct_add]
        simp only [dotProduct, Fin.sum_univ_two] at this ⊢
        linarith
      have hb2 : x i ∈ budgetSetOn (E.X i) p' (p' ⬝ᵥ E.ω i) := by
        refine ⟨(hxm i).1.1, ?_⟩
        have hz1 : z i 1 = -(p 0 / p 1) * z i 0 := by
          have := hW i; field_simp; linarith
        have hzx : x i = z i + E.ω i := by simp [z]
        have : p' 0 * z i 0 + p' 1 * z i 1 ≤ 0 := by
          rw [hz1]
          have hk : 0 ≤ p' 0 - p' 1 * (p 0 / p 1) := by
            rw [mul_div_assoc', sub_div' hp1.ne', le_div_iff₀ hp1]; nlinarith
          nlinarith
        rw [hzx, dotProduct_add]
        simp only [dotProduct, Fin.sum_univ_two] at this ⊢
        linarith
      have h2 := (hxm' i).2 _ hb2
      have hmem : x' i ∈ E.demand i p := ⟨hb1, fun y hy => ((hxm i).2 y hy).trans h2⟩
      rw [hx i] at hmem
      have hxx : x' i = x i := hmem
      have heq : z i = z' i := by simp only [z, z', hxx]
      have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have hA : z i 1 = -(p 0 / p 1) * z i 0 := by have := hW i; field_simp; linarith
      have hB : z' i 0 = -(p' 1 / p' 0) * z' i 1 := by have := hW' i; field_simp; linarith
      have hprod : z i 0 * (1 - (p' 1 / p' 0) * (p 0 / p 1)) = 0 := by
        linear_combination e0 + hB + (p' 1 / p' 0) * e1 - (p' 1 / p' 0) * hA
      have hk : (p' 1 / p' 0) * (p 0 / p 1) < 1 := by
        rw [div_mul_div_comm, div_lt_one (by positivity)]; nlinarith
      have h0 : z i 0 = 0 := (mul_eq_zero.1 hprod).resolve_right (by linarith)
      have h1 : z i 1 = 0 := by rw [hA, h0, mul_zero]
      have e1' : z' i 1 = 0 := by rw [← e1, h1]
      exact ⟨by simp only [h0, neg_zero], by simp only [e1', neg_zero]⟩
    · right; left
      push Not at hβ
      linarith
  · left
    push Not at hα
    linarith

/-- **Exercise 17.E.5** (MWG, p. 645; Figure 17.E.3), three consumers. Let `p, p' ≫ 0` with `p`
steeper than `p'`, `z(p) = (-1, a) ∈ T_p` and `z(p') = (b, -1) ∈ T_{p'}`. No exchange economy
with three consumers, consumption sets `ℝ²_+`, endowments bounded above by `(1, 1)` and
single-valued demands at `p` and `p'` has these aggregate excess demands. -/
theorem exercise_17_E_5_three {p p' : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (hp' : StrictlyPositive p') (hslope : p 0 * p' 1 < p' 0 * p 1) {a b : ℝ}
    (hza : p ⬝ᵥ ![-1, a] = 0) (hzb : p' ⬝ᵥ ![b, -1] = 0) (E : ExchangeEconomy (Fin 3) 2)
    (hX : ∀ i, E.X i = nonnegOrthant 2) (hω : ∀ i l, E.ω i l ≤ 1)
    (hd : ∀ i, ∃ x, E.demand i p = {x}) (hd' : ∀ i, ∃ x, E.demand i p' = {x}) :
    ¬ (excessDemand E p = ![-1, a] ∧ excessDemand E p' = ![b, -1]) := by
  rintro ⟨hz, hz'⟩
  obtain ⟨α, β, hsa, hsb, hle, hwa⟩ :=
    ex17E5_shares hp hp' hslope hza hzb E hX hω hd hd' hz hz'
  rw [Fin.sum_univ_three] at hsa hsb
  have l0 := hle 0
  have l1 := hle 1
  have l2 := hle 2
  rcases hwa 0 with h0 | h0 | h0 <;> rcases hwa 1 with h1 | h1 | h1 <;>
    rcases hwa 2 with h2 | h2 | h2 <;> linarith

end MWG.PositiveEquilibriumTheory
