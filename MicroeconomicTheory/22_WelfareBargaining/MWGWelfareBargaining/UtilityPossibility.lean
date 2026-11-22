/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ParetoEquilibrium
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FinCases

/-!
# Utility possibility sets

MWG, Section 22.B, pp. 818-824: Definition 22.B.1, Example 22.B.1 with Exercise 22.B.1,
Example 22.B.2 (the Ramsey first-order conditions, with a correction), and Example 22.B.5.

* `ups X u`: the utility possibility set `{v : v ≤ u(x) for some x ∈ X}` (Definition 22.B.1).
  For the economies of MWG Chapter 10 (imported from `MWGCompetitiveMarkets`), the set
  `Economy.utilityPossibilitySet` is `ups` of the feasible allocations (`ups_economy`).
* Exercise 22.B.1: convex consumption and production sets and concave utilities give a convex
  utility possibility set.
* Example 22.B.5: two nonconvex first-best utility possibility sets (indivisible locations;
  the externality `u₁ = x₁`, `u₂ = x₂/x₁`).
* **Correction (Example 22.B.2).** The printed first-order condition "there is `λ < 0` with
  `λ(p̄ₗ - 1)xₗ'(p̄ₗ) = (1 - λ)xₗ(p̄ₗ)`" has the wrong sign: in the instance `xₗ(p) = 2 - p`,
  `R = 3/8`, the optimum is `p̄ = (5/4, 5/4)` and the only `λ` satisfying the condition is
  `3/2`. The correct multiplier satisfies `λ > 1`, which gives (22.B.1) with `α = (λ-1)/λ`.
-/

namespace MWG.WelfareBargaining

/-- **Definition 22.B.1** (MWG, p. 818). The utility possibility set of the alternatives `X`
for the utility functions `uᵢ`. -/
def ups {ι A : Type*} (X : Set A) (u : ι → A → ℝ) : Set (ι → ℝ) :=
  {v | ∃ x ∈ X, ∀ i, v i ≤ u i x}

/-- **Example 22.B.1** (MWG, p. 818). For an economy of MWG Chapter 10 the utility possibility
set is that of Definition 22.B.1 with `X` the set of feasible allocations and
`uᵢ(x) = uᵢ(xᵢ)`. -/
theorem ups_economy {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}
    (E : MWG.CompetitiveMarkets.Economy ι κ L) :
    E.utilityPossibilitySet = ups {a | E.IsFeasible a} (fun i a => E.u i (a.x i)) := by
  ext v; simp [MWG.CompetitiveMarkets.Economy.utilityPossibilitySet, ups]

/-- **Exercise 22.B.1** (MWG, p. 850). Sufficient conditions for convexity of the first-best
utility possibility set: convex consumption and production sets and concave utilities. -/
theorem exercise_22_B_1 {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}
    (E : MWG.CompetitiveMarkets.Economy ι κ L) (hX : ∀ i, Convex ℝ (E.X i))
    (hY : ∀ j, Convex ℝ (E.Y j)) (hu : ∀ i, ConcaveOn ℝ (E.X i) (E.u i)) :
    Convex ℝ E.utilityPossibilitySet := by
  rintro v ⟨a, ⟨⟨hax, hay⟩, haf⟩, hv⟩ v' ⟨a', ⟨⟨hax', hay'⟩, haf'⟩, hv'⟩ s t hs ht hst
  refine ⟨⟨fun i => s • a.x i + t • a'.x i, fun j => s • a.y j + t • a'.y j⟩,
    ⟨⟨fun i => hX i (hax i) (hax' i) hs ht hst, fun j => hY j (hay j) (hay' j) hs ht hst⟩,
      fun l => ?_⟩, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (haf l) hs
    have h2 := mul_le_mul_of_nonneg_left (haf' l) ht
    have : E.ω l = s * E.ω l + t * E.ω l := by rw [← add_mul, hst, one_mul]
    nlinarith
  · have := (hu i).2 (hax i) (hax' i) hs ht hst
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    nlinarith [mul_le_mul_of_nonneg_left (hv i) hs, mul_le_mul_of_nonneg_left (hv' i) ht]

/-- **Example 22.B.5** (MWG, p. 822, Figure 22.B.5). Two agents who both prefer location `A`:
the two assignments give utility vectors `(1, 0)` and `(0, 1)`, and the utility possibility set
is not convex. -/
theorem example_22_B_5_locations :
    ¬Convex ℝ (ups (Set.univ : Set Bool) fun (i : Fin 2) (x : Bool) =>
      if x then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1)) := by
  intro hc
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ ups Set.univ (fun (i : Fin 2) (x : Bool) =>
      if x then (if i = 0 then (1 : ℝ) else 0) else (if i = 0 then 0 else 1)) :=
    ⟨true, trivial, fun i => by fin_cases i <;> simp⟩
  have h2 : (![0, 1] : Fin 2 → ℝ) ∈ ups Set.univ (fun (i : Fin 2) (x : Bool) =>
      if x then (if i = 0 then (1 : ℝ) else 0) else (if i = 0 then 0 else 1)) :=
    ⟨false, trivial, fun i => by fin_cases i <;> simp⟩
  obtain ⟨x, -, hx⟩ := hc h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h0 := hx 0; have h1' := hx 1
  cases x <;> simp at h0 h1' <;> linarith

/-- **Example 22.B.5** (MWG, p. 822, Figure 22.B.6). One unit of a single good, `u₁ = x₁` and
`u₂ = x₂/x₁` (consumption externality, `x₁ > 0`): the utility possibility set is not convex;
`(1/2, 1)` and `(1/4, 3)` belong to it but their midpoint does not. -/
theorem example_22_B_5_externality :
    ¬Convex ℝ (ups {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}
      fun (i : Fin 2) x => if i = 0 then x 0 else x 1 / x 0) := by
  intro hc
  have h1 : (![1 / 2, 1] : Fin 2 → ℝ) ∈ ups {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}
      (fun (i : Fin 2) x => if i = 0 then x 0 else x 1 / x 0) :=
    ⟨![1 / 2, 1 / 2], by norm_num, fun i => by fin_cases i <;> norm_num⟩
  have h2 : (![1 / 4, 3] : Fin 2 → ℝ) ∈ ups {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}
      (fun (i : Fin 2) x => if i = 0 then x 0 else x 1 / x 0) :=
    ⟨![1 / 4, 3 / 4], by norm_num, fun i => by fin_cases i <;> norm_num⟩
  obtain ⟨x, ⟨hx0, -, hsum⟩, hx⟩ := hc h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e0 := hx 0; have e1 := hx 1
  change (1 / 2 : ℝ) * (1 / 2) + (1 / 2) * (1 / 4) ≤ x 0 at e0
  change (1 / 2 : ℝ) * 1 + (1 / 2) * 3 ≤ x 1 / x 0 at e1
  rw [le_div_iff₀ hx0] at e1
  nlinarith

/-- Consumer surplus `(2 - p)²/2` of the linear demand `x(p) = 2 - p`. -/
noncomputable def ramseyCS (p : ℝ) : ℝ := (2 - p) ^ 2 / 2

/-- **Example 22.B.2, correction** (MWG, p. 820). Two goods with demand `xₗ(p) = 2 - p`,
marginal cost `1` and required revenue `R = 3/8`: the prices `p̄ = (5/4, 5/4)` maximize the
surplus `∑ CS(pₗ)` subject to `∑ (pₗ - 1)xₗ(pₗ) ≥ R`, and the condition
`λ(p̄ₗ - 1)xₗ'(p̄ₗ) = (1 - λ)xₗ(p̄ₗ)` holds only for `λ = 3/2`, never for `λ < 0`. The tax
rate `t = 1/5` and elasticity `ε = 5/3` satisfy (22.B.1) with `α = tε = 1/3 = (λ-1)/λ`. -/
theorem example_22_B_2_correction :
    (5 / 4 - 1) * (2 - 5 / 4) + (5 / 4 - 1) * (2 - 5 / 4) = (3 / 8 : ℝ) ∧
      (∀ p₁ p₂ : ℝ, (p₁ - 1) * (2 - p₁) + (p₂ - 1) * (2 - p₂) ≥ 3 / 8 →
        ramseyCS p₁ + ramseyCS p₂ ≤ ramseyCS (5 / 4) + ramseyCS (5 / 4)) ∧
      (∀ lam : ℝ, lam * (5 / 4 - 1) * (-1) = (1 - lam) * (2 - 5 / 4) ↔ lam = 3 / 2) ∧
      ((5 / 4 - 1) / (5 / 4) * ((5 / 4) / (2 - 5 / 4)) = (1 / 3 : ℝ) ∧
        ((3 / 2 : ℝ) - 1) / (3 / 2) = 1 / 3) := by
  refine ⟨by norm_num, fun p₁ p₂ h => ?_, fun lam => ⟨fun h => by linarith, fun h => by
    rw [h]; norm_num⟩, by norm_num, by norm_num⟩
  simp only [ramseyCS]
  -- with `aₗ = pₗ - 1`: `S = a₁ + a₂ ≥ 3/8 + Q`, `Q = a₁² + a₂² ≥ S²/2`, so `Q ≥ 1/8`
  nlinarith [sq_nonneg (p₁ - p₂), sq_nonneg (p₁ + p₂ - 5 / 2)]

end MWG.WelfareBargaining
