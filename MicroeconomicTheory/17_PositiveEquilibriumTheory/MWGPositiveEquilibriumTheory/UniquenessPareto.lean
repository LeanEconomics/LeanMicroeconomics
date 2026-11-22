/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GrossSubstitutesExamples
import MWGPositiveEquilibriumTheory.IndexTwoGoods

/-!
# Uniqueness from Pareto optimality, and index analysis (MWG Section 17.F, pp. 614-615)

* **Proposition 17.F.5** (`proposition_17_F_5`): if the endowment allocation is a Walrasian
  equilibrium allocation (no trade) of an exchange economy with strictly convex preferences, it is
  the unique equilibrium allocation. The proof compares any other equilibrium allocation `x` with
  `½x + ½ω` directly (the step "by the first welfare theorem, `ω` is Pareto optimal" is replaced by
  the same budget argument). Strong monotonicity is not needed.
* **p. 614**: in the no-trade case, (17.F.3) holds (`notrade_eq_17_F_3`).
* **Exercise 17.F.9** (`exercise_17_F_9`): the production version, with a constant returns
  technology `Y` and `xᵢ - ωᵢ ∈ Y` for all `i`.
* **Example 17.F.3**, the index argument (`example_17_F_3_index`): with two goods, an equilibrium
  of index `-1` implies that there is another equilibrium (index theorem for `L = 2`).
* Instances: one consumer with `u(x) = √x₁ + √x₂`, `ω = (1, 1)`, no trade at `p = (1, 1)`
  (`sqrt1_noTrade`, `sqrt1_eqm`, `sqrt1_cr_eqm`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.Production
open MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- The midpoint of two bundles of `ℝ^L₊` is in `ℝ^L₊`. -/
theorem up_mid_mem {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ nonnegOrthant L := fun l => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [hx l, hy l]

/-- Strict convexity: if `u(x) ≥ u(y)` and `x ≠ y` (both in `ℝ^L₊`), then `u(½x + ½y) > u(y)`. -/
theorem up_mid_gt {u : (Fin L → ℝ) → ℝ} (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) u)
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hne : x ≠ y)
    (hle : u y ≤ u x) : u y < u ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
  have := hsq.2 x hx y hy hne (1 / 2) (by norm_num) (by norm_num) (u y) hle le_rfl
  norm_num at this ⊢
  exact this

/-! ### Proposition 17.F.5 -/

/-- **Proposition 17.F.5** (MWG, p. 614). In an exchange economy with `Xᵢ = ℝ^L₊`, endowments in
`ℝ^L₊` and strictly convex preferences, if the initial endowment allocation `ω` is a Walrasian
equilibrium allocation (at some `p`), then every Walrasian equilibrium allocation equals `ω`. -/
theorem proposition_17_F_5 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {p : Fin L → ℝ} (h0 : E.IsWalrasEqm p E.ω)
    {p' : Fin L → ℝ} {x : ι → Fin L → ℝ} (hx : E.IsWalrasEqm p' x) : x = E.ω := by
  by_contra hne
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hne
  have hxX : ∀ i, x i ∈ nonnegOrthant L := fun i => by rw [← hX i]; exact hx.1.1 i
  have hge : ∀ i, E.u i (E.ω i) ≤ E.u i (x i) := fun i =>
    hx.2 i (E.ω i) ⟨by rw [hX i]; exact hω i, le_rfl⟩
  set m : ι → Fin L → ℝ := fun i => (1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • E.ω i with hm
  have hmX : ∀ i, m i ∈ nonnegOrthant L := fun i => up_mid_mem (hxX i) (hω i)
  have hval : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ m i := fun i => by
    by_contra hlt
    rw [not_le] at hlt
    by_cases hxi : x i = E.ω i
    · rw [hm] at hlt
      simp only [hxi] at hlt
      rw [← add_smul] at hlt
      norm_num at hlt
    · have hgt := up_mid_gt (hsq i) (hxX i) (hω i) hxi (hge i)
      have := h0.2 i (m i) ⟨by rw [hX i]; exact hmX i, hlt.le⟩
      linarith
  have hstrict : p ⬝ᵥ E.ω i0 < p ⬝ᵥ m i0 := by
    by_contra hle
    rw [not_lt] at hle
    have hgt := up_mid_gt (hsq i0) (hxX i0) (hω i0) hi0 (hge i0)
    have := h0.2 i0 (m i0) ⟨by rw [hX i0]; exact hmX i0, hle⟩
    linarith
  have hsum : ∑ i, m i = ∑ i, E.ω i := by
    simp only [hm, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [hx.1.2, ExchangeEconomy.totalEndowment, ← add_smul]
    norm_num
  have hlt : ∑ i, p ⬝ᵥ E.ω i < ∑ i, p ⬝ᵥ m i :=
    Finset.sum_lt_sum (fun i _ => hval i) ⟨i0, Finset.mem_univ _, hstrict⟩
  rw [← dotProduct_sum, ← dotProduct_sum, hsum] at hlt
  exact lt_irrefl _ hlt

/-- **Section 17.F** (MWG, p. 614). In the no-trade case (17.F.3) holds: if at `p ≫ 0` every
consumer demands his endowment, then `z(p') ≠ 0` implies `p·z(p') > 0`. -/
theorem notrade_eq_17_F_3 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hu : ∀ i, StandardUtility (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) (hnt : ∀ i, demandFn E i p = E.ω i) {p' : Fin L → ℝ}
    (hp' : p' ∈ posOrthant L) (hz : excessDemand E p' ≠ 0) :
    0 < p ⬝ᵥ excessDemand E p' := by
  have hd : ∀ q ∈ posOrthant L, ∀ i, demandFn E i q ∈ E.demand i q := fun q hq i =>
    demandFn_mem E (demand_nonempty hX (hu i).1 (hω i) hq)
  have hind : ∀ i, demandFn E i p' = E.ω i ∨ p ⬝ᵥ E.ω i < p ⬝ᵥ demandFn E i p' := fun i => by
    by_cases heq : demandFn E i p' = E.ω i
    · exact Or.inl heq
    · right
      by_contra hle
      rw [not_lt] at hle
      have hx' := hd p' hp' i
      have hω' := hd p hp i
      rw [hnt i] at hω'
      have h1 : E.u i (demandFn E i p') ≤ E.u i (E.ω i) := hω'.2 _ ⟨hx'.1.1, hle⟩
      have h2 : E.u i (E.ω i) ≤ E.u i (demandFn E i p') :=
        hx'.2 _ ⟨by rw [hX i]; exact hω i, le_rfl⟩
      have hmem : demandFn E i p' ∈ E.demand i p :=
        ⟨⟨hx'.1.1, hle⟩, fun y hy => (hω'.2 y hy).trans h2⟩
      exact heq (demand_subsingleton hX (hu i).2.1 p hmem hω')
  obtain ⟨i0, hi0⟩ : ∃ i, demandFn E i p' ≠ E.ω i := by
    by_contra hcon
    push Not at hcon
    apply hz
    simp [excessDemand, indivExcessDemand, hcon]
  have hpos : ∀ i, 0 ≤ p ⬝ᵥ indivExcessDemand E i p' := fun i => by
    rcases hind i with h | h
    · simp [indivExcessDemand, h]
    · rw [indivExcessDemand, dotProduct_sub]; linarith
  unfold excessDemand
  rw [dotProduct_sum]
  refine Finset.sum_pos' (fun i _ => hpos i) ⟨i0, Finset.mem_univ _, ?_⟩
  rcases hind i0 with h | h
  · exact absurd h hi0
  · rw [indivExcessDemand, dotProduct_sub]; linarith

/-! ### Exercise 17.F.9 -/

/-- **Exercise 17.F.9** (MWG, p. 646). In an economy with a constant returns technology `Y` and
strictly convex preferences on `Xᵢ = ℝ^L₊`, suppose `(x, y)` at `p` is a Walrasian equilibrium and
no trade is needed to attain `x` if `Y` is available to everyone: `xᵢ - ωᵢ ∈ Y` for all `i`. Then
every Walrasian equilibrium has consumptions `x`. -/
theorem exercise_17_F_9 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i)) {Y : Set (Fin L → ℝ)}
    (hY : ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y) (θ : ι → ℝ) {p : Fin L → ℝ}
    {x : ι → Fin L → ℝ} {y : Fin L → ℝ}
    (h0 : (crEconomy E Y θ).IsWalrasEqm ⟨x, fun _ => y⟩ p) (hxY : ∀ i, x i - E.ω i ∈ Y)
    {p' : Fin L → ℝ} {x' : ι → Fin L → ℝ} {y' : Fin L → ℝ}
    (h1 : (crEconomy E Y θ).IsWalrasEqm ⟨x', fun _ => y'⟩ p') : x' = x := by
  obtain ⟨hy, hxm, hc⟩ := h0
  obtain ⟨hy', hxm', hc'⟩ := h1
  have hpy := cr_profit_zero hY (hy ())
  have hpy' := cr_profit_zero hY (hy' ())
  have hw : ∀ i, (crEconomy E Y θ).wealth ⟨x, fun _ => y⟩ p i = p ⬝ᵥ E.ω i := fun i => by
    simp [PrivPrefEconomy.wealth, crEconomy, hpy]
  have hw' : ∀ i, (crEconomy E Y θ).wealth ⟨x', fun _ => y'⟩ p' i = p' ⬝ᵥ E.ω i := fun i => by
    simp [PrivPrefEconomy.wealth, crEconomy, hpy']
  have hxd : ∀ i, x i ∈ E.demand i p := fun i => by
    have := hxm i; rw [hw i] at this; exact this
  have hxd' : ∀ i, x' i ∈ E.demand i p' := fun i => by
    have := hxm' i; rw [hw' i] at this; exact this
  have hxX : ∀ i, x i ∈ nonnegOrthant L := fun i => by rw [← hX i]; exact (hxd i).1.1
  have hxX' : ∀ i, x' i ∈ nonnegOrthant L := fun i => by rw [← hX i]; exact (hxd' i).1.1
  have hpY : ∀ v ∈ Y, p ⬝ᵥ v ≤ 0 := fun v hv => by
    have := (hy ()).2 v hv; simpa [crEconomy, hpy] using this
  have hpY' : ∀ v ∈ Y, p' ⬝ᵥ v ≤ 0 := fun v hv => by
    have := (hy' ()).2 v hv; simpa [crEconomy, hpy'] using this
  -- `xᵢ` is affordable at `p'`, so `x'ᵢ ≿ᵢ xᵢ`
  have hge : ∀ i, E.u i (x i) ≤ E.u i (x' i) := fun i =>
    (hxd' i).2 _ ⟨(hxd i).1.1, by have := hpY' _ (hxY i); rw [dotProduct_sub] at this; linarith⟩
  -- each `p·(xᵢ - ωᵢ) = 0`
  have hzero : ∀ i, p ⬝ᵥ x i = p ⬝ᵥ E.ω i := by
    have hle : ∀ i, p ⬝ᵥ (x i - E.ω i) ≤ 0 := fun i => hpY _ (hxY i)
    have hsum : ∑ i, p ⬝ᵥ (x i - E.ω i) = 0 := by
      rw [← dotProduct_sum, Finset.sum_sub_distrib]
      simp only [crEconomy, Finset.univ_unique, Finset.sum_singleton] at hc
      rw [hc]
      simp [hpy]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hle i).1 hsum i (Finset.mem_univ _)
    rw [dotProduct_sub] at this
    linarith
  by_contra hne
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hne
  set m : ι → Fin L → ℝ := fun i => (1 / 2 : ℝ) • x' i + (1 / 2 : ℝ) • x i with hm
  have hmX : ∀ i, m i ∈ nonnegOrthant L := fun i => up_mid_mem (hxX' i) (hxX i)
  have hval : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ m i := fun i => by
    by_cases hxi : x' i = x i
    · simp only [hm, hxi, ← add_smul]
      norm_num
      exact (hzero i).ge
    · by_contra hlt
      rw [not_le] at hlt
      have hgt := up_mid_gt (hsq i) (hxX' i) (hxX i) hxi (hge i)
      have := (hxd i).2 (m i) ⟨by rw [hX i]; exact hmX i, hlt.le⟩
      linarith
  have hstrict : p ⬝ᵥ E.ω i0 < p ⬝ᵥ m i0 := by
    by_contra hle
    rw [not_lt] at hle
    have hgt := up_mid_gt (hsq i0) (hxX' i0) (hxX i0) hi0 (hge i0)
    have := (hxd i0).2 (m i0) ⟨by rw [hX i0]; exact hmX i0, hle⟩
    linarith
  have hlt : ∑ i, p ⬝ᵥ E.ω i < ∑ i, p ⬝ᵥ m i :=
    Finset.sum_lt_sum (fun i _ => hval i) ⟨i0, Finset.mem_univ _, hstrict⟩
  have hmsum : ∑ i, p ⬝ᵥ m i ≤ ∑ i, p ⬝ᵥ E.ω i := by
    simp only [crEconomy, Finset.univ_unique, Finset.sum_singleton] at hc hc'
    have : ∑ i, m i = ∑ i, E.ω i + (1 / 2 : ℝ) • y' + (1 / 2 : ℝ) • y := by
      simp only [hm, Finset.sum_add_distrib, ← Finset.smul_sum, hc, hc']
      module
    rw [← dotProduct_sum, ← dotProduct_sum, this, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hpy, smul_zero, add_zero, smul_eq_mul]
    have := hpY y' (hy' ()).1
    nlinarith
  linarith

/-! ### Instances: one `√`-consumer, no trade at `p = (1, 1)` -/

/-- The one-consumer economy `u(x) = √x₁ + √x₂`, `ω = (1, 1)`. -/
noncomputable def sqrt1Economy : ExchangeEconomy (Fin 1) 2 :=
  ExchangeEconomy.ofOrthant (fun _ => sqrtUtility 2) (fun _ => ![1, 1])

/-- At `p = (1, 1)` the consumer of `sqrt1Economy` demands his endowment `(1, 1)`. -/
theorem sqrt1_demand : ![(1 : ℝ), 1] ∈ sqrt1Economy.demand 0 ![1, 1] := by
  refine ⟨⟨fun l => by fin_cases l <;> simp, le_rfl⟩, fun y hy => ?_⟩
  obtain ⟨hy0, hyb⟩ := hy
  have h0 := hy0 0
  have h1 := hy0 1
  simp only [sqrt1Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] at hyb ⊢
  simp only [sqrtUtility, Fin.sum_univ_two]
  norm_num at hyb ⊢
  have s0 := Real.sq_sqrt h0
  have s1 := Real.sq_sqrt h1
  have n0 := Real.sqrt_nonneg (y 0)
  have n1 := Real.sqrt_nonneg (y 1)
  nlinarith [sq_nonneg (Real.sqrt (y 0) - Real.sqrt (y 1))]

/-- **Proposition 17.F.5**, instance of its hypothesis: in `sqrt1Economy` the endowment
allocation is a Walrasian equilibrium allocation at `p = (1, 1)`. -/
theorem sqrt1_eqm : sqrt1Economy.IsWalrasEqm ![1, 1] sqrt1Economy.ω := by
  refine ⟨⟨fun i => ?_, rfl⟩, fun i y hy => ?_⟩
  · fin_cases i
    exact sqrt1_demand.1.1
  · fin_cases i
    exact sqrt1_demand.2 y hy

/-- **Section 17.F**, instance of the no-trade hypothesis of `notrade_eq_17_F_3`. -/
theorem sqrt1_noTrade (i : Fin 1) : demandFn sqrt1Economy i ![1, 1] = sqrt1Economy.ω i := by
  fin_cases i
  have hX : ∀ i, sqrt1Economy.X i = nonnegOrthant 2 := fun _ => rfl
  have hne : (sqrt1Economy.demand 0 ![1, 1]).Nonempty := ⟨_, sqrt1_demand⟩
  exact demand_subsingleton hX (standardUtility_sqrtUtility 2).2.1 _
    (demandFn_mem _ hne) sqrt1_demand

/-- **Exercise 17.F.9**, instance of its hypotheses: `sqrt1Economy` with the free disposal
technology `Y = -ℝ²₊`; `x = ω`, `y = 0` at `p = (1, 1)`, with `x - ω = 0 ∈ Y`. -/
theorem sqrt1_cr_eqm (θ : Fin 1 → ℝ) :
    (crEconomy sqrt1Economy {y | ∀ l, y l ≤ 0} θ).IsWalrasEqm
        ⟨sqrt1Economy.ω, fun _ => 0⟩ ![1, 1] ∧
      ∀ i, sqrt1Economy.ω i - sqrt1Economy.ω i ∈ {y : Fin 2 → ℝ | ∀ l, y l ≤ 0} := by
  refine ⟨⟨fun _ => ⟨fun l => le_rfl, fun y' hy' => ?_⟩, fun i => ?_, ?_⟩,
    fun i l => by simp⟩
  · simp only [dotProduct_zero]
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (by
      fin_cases l <;> simp) (hy' l)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have : (crEconomy sqrt1Economy {y | ∀ l, y l ≤ 0} θ).wealth
        ⟨sqrt1Economy.ω, fun _ => 0⟩ ![1, 1] 0 = ![1, 1] ⬝ᵥ sqrt1Economy.ω 0 := by
      simp [PrivPrefEconomy.wealth, crEconomy]
    rw [this]
    exact sqrt1_demand
  · simp [crEconomy]

/-! ### Example 17.F.3: the index argument -/

/-- **Example 17.F.3** (MWG, p. 615). With two goods, if `z` satisfies (i)-(v) of Proposition
17.B.2 and has a regular equilibrium `(p̂, 1)` of index `-1`, then there is another (normalized)
equilibrium: the index theorem (`∑ index = +1`) excludes a unique equilibrium of index `-1`. -/
theorem example_17_F_3_index {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hz : IsStandardExcessDemand z)
    {q : Fin 1 → ℝ} (hq : IsRegularEqm z q) (hidx : eqmIndex z q = -1) :
    ∃ q', IsNormEqm z q' ∧ q' ≠ q := by
  by_contra hcon
  push Not at hcon
  have hreg : IsRegularEconomy z := fun q' h' => by rw [hcon q' h']; exact hq
  obtain ⟨hfin, hsum⟩ := proposition_17_D_2_two_goods hz hreg
  have : hfin.toFinset = {q} := by
    ext q'
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun h => hcon q' h, fun h => by rw [h]; exact hq.1⟩
  rw [this, Finset.sum_singleton, hidx] at hsum
  norm_num at hsum

end MWG.PositiveEquilibriumTheory
