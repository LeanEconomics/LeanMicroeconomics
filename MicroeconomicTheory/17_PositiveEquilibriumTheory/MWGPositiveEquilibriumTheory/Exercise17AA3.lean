/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.NegishiLogEconomy
import MWGWelfareTheorems.SocialWelfare

/-!
# Exercise 17.AA.3: welfare equations with utility weights (MWG, p. 649)

Consumption sets `ℝ^L₊`, concave increasing (here: strongly monotone) utilities, and the simplex
`Δ = {λ ∈ ℝ^I₊ : ∑ᵢ λᵢ = 1}` of utility weights. The suggested equation system: for `λ ∈ Δ`, let
`x(λ)` maximize the linear social welfare function `∑ᵢ λᵢ uᵢ(xᵢ)` over the feasible allocations,
let `p(λ)` support `x(λ)`, and solve `p(λ)·[ωᵢ - xᵢ(λ)] = 0` for every `i`.
`exercise_17_AA_3` proves that the solutions of this system are exactly the Walrasian
equilibria: a solution is an equilibrium by (17.AA.1); conversely an equilibrium allocation is
Pareto optimal (first welfare theorem), hence, the utility possibility set being convex for
concave utilities (Exercise 16.E.2), a maximizer of `∑ᵢ λᵢuᵢ` for some `λ ∈ Δ` (Chapter 16's
`pareto_isWelfareOptimum`), and the equilibrium price supports it. Instance:
`exercise_17_AA_3_instance` (the economy `logEconomy`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {I L : ℕ}

/-- **Exercise 17.AA.3** (MWG, p. 649). In an exchange economy with `I ≥ 1`, `L ≥ 1`,
`Xᵢ = ℝ^L₊` and concave, strongly monotone utilities, `(x, p)` is a Walrasian equilibrium iff
it solves the welfare-weight equation system: `x` is feasible and, for some `λ ∈ Δ`, maximizes
`∑ᵢ λᵢuᵢ(x'ᵢ)` over the feasible allocations `x'`; `p` supports `x`; and
`p·[ωᵢ - xᵢ] = 0` for every `i`. -/
theorem exercise_17_AA_3 {E : ExchangeEconomy (Fin I) L} (hI : 0 < I) (hL : 0 < L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcc : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (E.u i))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) {p : Fin L → ℝ} {x : Fin I → Fin L → ℝ} :
    E.IsWalrasEqm p x ↔ E.InBox x ∧ IsSupportingPrice E x p ∧
      (∃ lam ∈ priceSimplex I, ∀ x', E.InBox x' →
        ∑ i, lam i * E.u i (x' i) ≤ ∑ i, lam i * E.u i (x i)) ∧
      ∀ i, p ⬝ᵥ (E.ω i - x i) = 0 := by
  constructor
  · intro h
    have hbud := walras_budget_eq hL hX hm h
    have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1 i
    have hsup : IsSupportingPrice E x p := fun i y hy hlt => by
      by_contra hle
      push Not at hle
      exact absurd (h.2 i y ⟨hy, by rw [← hbud i]; exact hle⟩) (not_le.2 hlt)
    have hg : ∀ i, p ⬝ᵥ (E.ω i - x i) = 0 := fun i => by rw [dotProduct_sub, hbud i, sub_self]
    have hp0 : ∀ l, 0 ≤ p l := by
      intro l
      by_contra hl
      push Not at hl
      set i₀ : Fin I := ⟨0, hI⟩
      have hsingle : ∀ k, 0 ≤ (Pi.single l (1 : ℝ) : Fin L → ℝ) k := fun k => by
        rw [Pi.single_apply]
        split_ifs <;> norm_num
      have hy : x i₀ + Pi.single l 1 ∈ nonnegOrthant L := fun k =>
        add_nonneg (hxm i₀ k) (hsingle k)
      have hlt : E.u i₀ (x i₀) < E.u i₀ (x i₀ + Pi.single l 1) := by
        refine (hm i₀).lt (hxm i₀) (fun k => ?_) fun h => ?_
        · simp only [Pi.add_apply]
          linarith [hsingle k]
        · have := congrFun h l
          simp at this
      have := hsup i₀ _ ((hX i₀).symm ▸ hy) hlt
      rw [dotProduct_add, dotProduct_single, mul_one] at this
      linarith
    have : Nonempty (Fin I) := ⟨⟨0, hI⟩⟩
    set E' : PrefEconomy (Fin I) Unit L :=
      PrefEconomy.ofUtility E.X E.u (fun _ => nonposOrthant L) E.totalEndowment with hE'
    have hYc : Convex ℝ (nonposOrthant L) := by
      intro a ha b hb s t hs ht _ l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs (ha l))
        (mul_nonpos_of_nonneg_of_nonpos ht (hb l))
    have hU : Convex ℝ (utilityPossibilitySet E' E.u) :=
      exercise_16_E_2 (fun _ => hYc) fun i => by rw [hX i]; exact hcc i
    have hfeas : ∀ x' : Fin I → Fin L → ℝ, E.InBox x' →
        E'.IsFeasible (⟨x', fun _ => 0⟩ : Allocation (Fin I) Unit L) := fun x' hx' =>
      ⟨⟨fun i => hx'.1 i, fun _ _ => le_refl 0⟩, by
        change ∑ i, x' i = E.totalEndowment + ∑ _j : Unit, (0 : Fin L → ℝ)
        simp [hx'.2]⟩
    have hpo : E'.IsParetoOptimal (⟨x, fun _ => 0⟩ : Allocation (Fin I) Unit L) := by
      refine ⟨hfeas x h.1, ?_⟩
      rintro ⟨a', ⟨⟨ha'x, ha'y⟩, hclear⟩, hall, k, hk⟩
      have hge : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ a'.x i := by
        intro i
        by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hpz, huz⟩ :=
          ((hm i).lns hL).exists_better p (hX i ▸ ha'x i) hlt
        exact absurd (h.2 i z ⟨(hX i).symm ▸ hz, hpz.le⟩)
          (not_le.2 (lt_of_le_of_lt (hall i) huz))
      have hgt : p ⬝ᵥ E.ω k < p ⬝ᵥ a'.x k := by
        by_contra hle
        push Not at hle
        exact hk.2 (h.2 k (a'.x k) ⟨ha'x k, hle⟩)
      have hsum : ∑ i, p ⬝ᵥ E.ω i < ∑ i, p ⬝ᵥ a'.x i :=
        Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ _, hgt⟩
      have hclear' : ∑ i, a'.x i = E.totalEndowment + a'.y () := by
        simpa [hE', PrefEconomy.ofUtility] using hclear
      rw [← dotProduct_sum, ← dotProduct_sum, hclear', dotProduct_add] at hsum
      have hy : p ⬝ᵥ a'.y () ≤ 0 :=
        Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp0 l) (ha'y () l)
      have htot : p ⬝ᵥ E.totalEndowment = p ⬝ᵥ ∑ i, E.ω i := rfl
      linarith
    obtain ⟨lam, hlam0, hlamne, hlam⟩ := pareto_isWelfareOptimum hU hpo
    set σ := ∑ i, lam i with hσ
    have hσpos : 0 < σ := by
      obtain ⟨i, hi⟩ : ∃ i, lam i ≠ 0 := by
        by_contra hz
        push Not at hz
        exact hlamne (funext hz)
      exact Finset.sum_pos' (fun j _ => hlam0 j)
        ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hlam0 i) (Ne.symm hi)⟩
    refine ⟨h.1, hsup, ⟨σ⁻¹ • lam, ⟨fun i => ?_, ?_⟩, fun x' hx' => ?_⟩, hg⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hσpos.le) (hlam0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hσ]
      exact inv_mul_cancel₀ hσpos.ne'
    · have hv := hlam (fun i => E.u i (x' i)) ⟨_, hfeas x' hx', fun _ => le_rfl⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hv (inv_nonneg.2 hσpos.le)
  · rintro ⟨hbox, hsup, -, hg⟩
    exact (appendix_A_walras_iff hL hX hm hbox hsup).2 hg

/-- **Exercise 17.AA.3** (MWG, p. 649), instance: in `logEconomy` (concave, strongly monotone
utilities) the welfare-weight equation system has a solution. -/
theorem exercise_17_AA_3_instance :
    ∃ p x, logEconomy.InBox x ∧ IsSupportingPrice logEconomy x p ∧
      (∃ lam ∈ priceSimplex 2, ∀ x', logEconomy.InBox x' →
        ∑ i, lam i * logEconomy.u i (x' i) ≤ ∑ i, lam i * logEconomy.u i (x i)) ∧
      ∀ i, p ⬝ᵥ (logEconomy.ω i - x i) = 0 := by
  obtain ⟨s, -, -, heq⟩ := exercise_17_AA_2_instance
  exact ⟨_, _, (exercise_17_AA_3 two_pos two_pos (fun _ => rfl) (fun _ => logU_concaveOn)
    (fun _ => logU_stronglyMonotone)).1 heq⟩

end MWG.PositiveEquilibriumTheory
