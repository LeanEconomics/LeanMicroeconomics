/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Basic

/-!
# Equilibrium of a pure exchange economy as a system of equations (MWG Section 17.B, pp. 579-582)

* **Definition 17.B.1** is Chapter 16's `PrivPrefEconomy.IsWalrasEqm`. A pure exchange economy
  (Chapter 15's `ExchangeEconomy`) is the private ownership economy `pureExchangeEconomy E`
  with one firm with the disposal technology `Y₁ = -ℝ^L₊` (`J = 1`).
* **Exercise 17.B.1**: profit maximization on `-ℝ^L₊` is "`y ≤ 0`, `p·y = 0`, `p ≥ 0`"
  (`exercise_17_B_1`), and conditions **(i')-(iii')** restate Definition 17.B.1
  (`conditions_i'_iii'`).
* **Proposition 17.B.1**: under local nonsatiation, `p ≥ 0` is a Walrasian equilibrium price
  vector iff some demanded bundles satisfy `∑ᵢ (xᵢ - ωᵢ) ≤ 0` (`proposition_17_B_1`); with
  strictly convex preferences, demand is single valued and this is **(17.B.1')**,
  `z(p) ≤ 0` (`proposition_17_B_1'`). The proof uses neither continuity nor strict convexity;
  strict convexity is used only to make `xᵢ(p, p·ωᵢ)` a function.
* The claims of p. 581: at an equilibrium `z(p) ≤ 0` and `p·z(p) = 0`, so `z_ℓ(p) = 0` whenever
  `p_ℓ > 0` (`eqm_excess_eq_zero_of_price_pos`); with strongly monotone preferences demand is
  empty at any price vector with a nonpositive component (`walrasianDemand_eq_empty`), so every
  equilibrium has `p ≫ 0` (`eqm_price_pos`), and `p` is an equilibrium price vector iff
  `z(p) = 0` (17.B.2) (`eqm_iff_isEqmPrice`).

Departure (corrections): the endowments are assumed to lie in the consumption set
`ωᵢ ∈ ℝ^L₊` wherever demand at every `p ≫ 0` is needed.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.Production
open MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {ι : Type*} {L : ℕ}

/-! ### Exercise 17.B.1 and conditions (i')-(iii') -/

/-- **Exercise 17.B.1** (MWG, p. 641). For the disposal technology `Y₁ = -ℝ^L₊`,
"`y ≤ 0`, `p·y = 0` and `p ≥ 0`" iff "`y ∈ Y₁` and `p·y ≥ p·y'` for all `y' ∈ Y₁`". -/
theorem exercise_17_B_1 (p y : Fin L → ℝ) :
    ((∀ l, y l ≤ 0) ∧ p ⬝ᵥ y = 0 ∧ ∀ l, 0 ≤ p l) ↔ y ∈ supply (nonposOrthant L) p := by
  constructor
  · rintro ⟨hy, hpy, hp⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    rw [hpy]
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hy' l)
  · rintro ⟨hy, hmax⟩
    have h0 : (0 : ℝ) ≤ p ⬝ᵥ y := by
      have := hmax 0 fun l => le_rfl
      simpa using this
    have h2 : p ⬝ᵥ ((2 : ℝ) • y) ≤ p ⬝ᵥ y :=
      hmax _ fun l => by simpa using mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hy l)
    rw [dotProduct_smul, smul_eq_mul] at h2
    have hpy : p ⬝ᵥ y = 0 := by linarith
    refine ⟨hy, hpy, fun l => ?_⟩
    have hmem : -Pi.single l (1 : ℝ) ∈ nonposOrthant L := fun k => by
      by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    have := hmax _ hmem
    rw [dotProduct_neg, dotProduct_single, hpy] at this
    linarith

/-- **Section 17.B** (MWG, p. 580). A pure exchange economy as a private ownership economy
(Definition 17.B.1): Chapter 15's exchange economy `E` with one firm (`J = 1`) with the
disposal technology `Y₁ = -ℝ^L₊`, wholly owned by every consumer (`θᵢ₁ = 1`; profits are zero in
equilibrium, so the shares do not matter). -/
def pureExchangeEconomy (E : ExchangeEconomy ι L) : PrivPrefEconomy ι Unit L where
  X := E.X
  pref := fun i => utilityPref (E.u i)
  Y := fun _ => nonposOrthant L
  ωi := E.ω
  θ := fun _ _ => 1

variable [Fintype ι]

/-- **Conditions (i')-(iii')** (MWG, p. 580). For a pure exchange economy, `(x*, y*₁)` and
`p` form a Walrasian equilibrium (Definition 17.B.1) iff (i') `y*₁ ≤ 0`, `p·y*₁ = 0`, `p ≥ 0`;
(ii') `x*ᵢ ∈ xᵢ(p, p·ωᵢ)` for every `i`; (iii') `∑ᵢ x*ᵢ - ∑ᵢ ωᵢ = y*₁`. -/
theorem conditions_i'_iii' (E : ExchangeEconomy ι L) (a : Allocation ι Unit L)
    (p : Fin L → ℝ) :
    (pureExchangeEconomy E).IsWalrasEqm a p ↔
      ((∀ l, a.y () l ≤ 0) ∧ p ⬝ᵥ a.y () = 0 ∧ ∀ l, 0 ≤ p l) ∧
        (∀ i, a.x i ∈ E.demand i p) ∧ ∑ i, a.x i - ∑ i, E.ω i = a.y () := by
  have hw : p ⬝ᵥ a.y () = 0 → ∀ i, (pureExchangeEconomy E).wealth a p i = p ⬝ᵥ E.ω i := by
    intro h i
    simp [PrivPrefEconomy.wealth, pureExchangeEconomy, h]
  constructor
  · rintro ⟨hy, hx, hc⟩
    have h1 := (exercise_17_B_1 p (a.y ())).2 (hy ())
    refine ⟨h1, fun i => ?_, ?_⟩
    · have := hx i
      rw [hw h1.2.1 i] at this
      exact this
    · simp only [pureExchangeEconomy, Finset.univ_unique, Finset.sum_singleton] at hc
      rw [hc]
      abel
  · rintro ⟨h1, hx, hc⟩
    refine ⟨fun _ => (exercise_17_B_1 p _).1 h1, fun i => ?_, ?_⟩
    · rw [hw h1.2.1 i]
      exact hx i
    · simp only [pureExchangeEconomy, Finset.univ_unique, Finset.sum_singleton]
      rw [← hc]
      abel

/-! ### Proposition 17.B.1 and (17.B.1') -/

omit [Fintype ι] in
/-- A demanded bundle of a locally nonsatiated consumer exhausts the wealth `p·ωᵢ`. -/
theorem ed_budget_eq {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    {i : ι} (hlns : UtilityLNS (E.u i)) {p x : Fin L → ℝ} (hx : x ∈ E.demand i p) :
    p ⬝ᵥ x = p ⬝ᵥ E.ω i := by
  have hx' : x ∈ walrasianDemandOn (nonnegOrthant L) (E.u i) p (p ⬝ᵥ E.ω i) := by
    rw [← hX i]
    exact hx
  exact hlns.budget_eq hx'

/-- **Proposition 17.B.1** (MWG, p. 580). In a pure exchange economy (`Xᵢ = ℝ^L₊`) with locally
nonsatiated preferences, `p ≥ 0` is a Walrasian equilibrium price vector iff
`∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ) ≤ 0` (17.B.1) for demanded bundles `xᵢ`. (The book also assumes
continuous and strictly convex preferences; the proof uses neither, and strict convexity only
makes the demanded bundles unique, `proposition_17_B_1'`.) -/
theorem proposition_17_B_1 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) :
    (∃ a, (pureExchangeEconomy E).IsWalrasEqm a p) ↔
      ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ E.demand i p) ∧ ∑ i, (x i - E.ω i) ≤ 0 := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨⟨hy, -, -⟩, hx, hc⟩ := (conditions_i'_iii' E a p).1 ha
    refine ⟨a.x, hx, fun l => ?_⟩
    rw [Finset.sum_sub_distrib, hc]
    exact hy l
  · rintro ⟨x, hx, hz⟩
    refine ⟨⟨x, fun _ => ∑ i, (x i - E.ω i)⟩, (conditions_i'_iii' E _ p).2
      ⟨⟨fun l => hz l, ?_, hp⟩, hx, by simp [Finset.sum_sub_distrib]⟩⟩
    rw [dotProduct_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [dotProduct_sub, ed_budget_eq hX (hlns i) (hx i), sub_self]

omit [Fintype ι] in
/-- With strictly convex preferences (a strictly quasiconcave utility) on `ℝ^L₊`, every
consumer's demand set has at most one element. -/
theorem demand_subsingleton {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    {i : ι} (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i)) (p : Fin L → ℝ) :
    (E.demand i p).Subsingleton := by
  have h := proposition_3_D_2_iii_unique hsq p (p ⬝ᵥ E.ω i)
  simp only [walrasianDemand] at h
  simp only [ExchangeEconomy.demand, hX i]
  exact h

/-- **(17.B.1')** (MWG, p. 581). With locally nonsatiated, strictly convex preferences on
`ℝ^L₊`, at a price vector `p ≥ 0` at which every consumer's demand is nonempty, `p` is a
Walrasian equilibrium price vector iff `z(p) ≤ 0`. (Where some demand is empty, `z(p)` is not
defined and `p` is not an equilibrium price vector.) -/
theorem proposition_17_B_1' {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i))
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i)) {p : Fin L → ℝ}
    (hp : ∀ l, 0 ≤ p l) (hne : ∀ i, (E.demand i p).Nonempty) :
    (∃ a, (pureExchangeEconomy E).IsWalrasEqm a p) ↔ excessDemand E p ≤ 0 := by
  rw [proposition_17_B_1 hX hlns hp]
  constructor
  · rintro ⟨x, hx, hz⟩
    have heq : ∀ i, x i = demandFn E i p := fun i =>
      demand_subsingleton hX (hsq i) p (hx i) (demandFn_mem E (hne i))
    simp only [excessDemand, indivExcessDemand, ← heq]
    exact hz
  · intro hz
    exact ⟨fun i => demandFn E i p, fun i => demandFn_mem E (hne i), hz⟩

/-- **Section 17.B** (MWG, p. 581). At a Walrasian equilibrium of a pure exchange economy with
locally nonsatiated preferences, `z(p) ≤ 0` and `p·z(p) = 0`; hence `z_ℓ(p) = 0` for every good
with `p_ℓ > 0`: a good can be in excess supply only if it is free. -/
theorem eqm_excess_eq_zero_of_price_pos {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ}
    (hp : ∀ l, 0 ≤ p l) {x : ι → Fin L → ℝ} (hx : ∀ i, x i ∈ E.demand i p)
    (hz : ∑ i, (x i - E.ω i) ≤ 0) :
    p ⬝ᵥ ∑ i, (x i - E.ω i) = 0 ∧ ∀ l, 0 < p l → (∑ i, (x i - E.ω i)) l = 0 := by
  have hpz : p ⬝ᵥ ∑ i, (x i - E.ω i) = 0 := by
    rw [dotProduct_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [dotProduct_sub, ed_budget_eq hX (hlns i) (hx i), sub_self]
  refine ⟨hpz, fun l hl => ?_⟩
  have hterms : ∀ k ∈ Finset.univ, p k * (∑ i, (x i - E.ω i)) k ≤ 0 := fun k _ =>
    mul_nonpos_of_nonneg_of_nonpos (hp k) (hz k)
  have h0 := (Finset.sum_eq_zero_iff_of_nonpos hterms).1 hpz l (Finset.mem_univ l)
  exact (mul_eq_zero.1 h0).resolve_left hl.ne'

/-! ### Strong monotonicity: equilibrium prices are strictly positive -/

/-- **Section 17.B** (MWG, p. 581). A consumer with strongly monotone preferences on `ℝ^L₊` has no
demand at a price vector with a nonpositive component: one more unit of that good costs
nothing extra and makes him strictly better off. -/
theorem walrasianDemand_eq_empty {u : (Fin L → ℝ) → ℝ} (hm : UtilityStronglyMonotone u)
    {p : Fin L → ℝ} {l : Fin L} (hpl : p l ≤ 0) (w : ℝ) : walrasianDemand u p w = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  set y := x + Pi.single l (1 : ℝ)
  have hxy : x ≤ y := fun k => by
    by_cases hk : k = l
    · subst hk; simp [y]
    · simp [y, hk]
  have hy0 : y ∈ nonnegOrthant L := fun k => (hx.1.1 k).trans (hxy k)
  have hne : y ≠ x := by
    intro h
    have := congrFun h l
    simp [y] at this
  have hby : y ∈ budgetSetOn (nonnegOrthant L) p w := by
    refine ⟨hy0, ?_⟩
    have : p ⬝ᵥ y = p ⬝ᵥ x + p l := by simp [y, dotProduct_add]
    rw [this]
    linarith [hx.1.2]
  have h1 := hx.2 y hby
  have h2 := hm.lt hx.1.1 hxy hne
  linarith

/-- **Section 17.B** (MWG, p. 581). With strongly monotone preferences on `ℝ^L₊` (and at least
one consumer), every Walrasian equilibrium price vector of a pure exchange economy is strictly
positive: otherwise consumers would demand an unboundedly large quantity of the free goods. -/
theorem eqm_price_pos [Nonempty ι] {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hm : ∀ i, UtilityStronglyMonotone (E.u i))
    {p : Fin L → ℝ} {a : Allocation ι Unit L} (h : (pureExchangeEconomy E).IsWalrasEqm a p) :
    p ∈ posOrthant L := by
  intro l
  by_contra hl
  rw [not_lt] at hl
  obtain ⟨-, hx, -⟩ := (conditions_i'_iii' E a p).1 h
  let i : ι := Classical.arbitrary ι
  have hmem := hx i
  simp only [ExchangeEconomy.demand, hX i] at hmem
  have hempty := walrasianDemand_eq_empty (hm i) hl (p ⬝ᵥ E.ω i)
  simp only [walrasianDemand] at hempty
  rw [hempty] at hmem
  exact hmem

omit [Fintype ι] in
/-- At `p ≫ 0` and nonnegative wealth a continuous utility on `ℝ^L₊` has a demanded bundle
(Proposition 3.D.1). -/
theorem demand_nonempty {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    {i : ι} (hc : ContinuousOn (E.u i) (nonnegOrthant L)) (hω : E.ω i ∈ nonnegOrthant L)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) : (E.demand i p).Nonempty := by
  have hw : 0 ≤ p ⬝ᵥ E.ω i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω l)
  have h := proposition_3_D_1 hc hp hw
  simp only [walrasianDemand] at h
  simp only [ExchangeEconomy.demand, hX i]
  exact h

/-- **(17.B.2)** (MWG, p. 581). In a pure exchange economy with `Xᵢ = ℝ^L₊`, endowments in
`ℝ^L₊`, at least one good, and continuous, strictly convex and strongly monotone preferences,
`p` is a Walrasian equilibrium price vector iff it clears all markets: `p ≫ 0` and
`z_ℓ(p) = 0` for every `ℓ`. -/
theorem eqm_iff_isEqmPrice [Nonempty ι] {E : ExchangeEconomy ι L} (hL : 0 < L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) (p : Fin L → ℝ) :
    (∃ a, (pureExchangeEconomy E).IsWalrasEqm a p) ↔ IsEqmPrice (excessDemand E) p := by
  have hlns : ∀ i, UtilityLNS (E.u i) := fun i => (hu i).2.2.lns hL
  constructor
  · rintro ⟨a, ha⟩
    have hp := eqm_price_pos hX (fun i => (hu i).2.2) ha
    have hne : ∀ i, (E.demand i p).Nonempty := fun i => demand_nonempty hX (hu i).1 (hω i) hp
    have hp0 : ∀ l, 0 ≤ p l := fun l => (hp l).le
    have hz := (proposition_17_B_1' hX hlns (fun i => (hu i).2.1) hp0 hne).1 ⟨a, ha⟩
    have hc := eqm_excess_eq_zero_of_price_pos hX hlns hp0
      (fun i => demandFn_mem E (hne i)) hz
    refine ⟨hp, funext fun l => ?_⟩
    have := hc.2 l (hp l)
    simpa [excessDemand, indivExcessDemand] using this
  · rintro ⟨hp, hz⟩
    have hne : ∀ i, (E.demand i p).Nonempty := fun i => demand_nonempty hX (hu i).1 (hω i) hp
    exact (proposition_17_B_1' hX hlns (fun i => (hu i).2.1) (fun l => (hp l).le) hne).2
      (le_of_eq hz)

end MWG.PositiveEquilibriumTheory
