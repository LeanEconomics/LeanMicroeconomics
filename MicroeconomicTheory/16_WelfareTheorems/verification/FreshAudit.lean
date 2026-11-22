import MWGGeneralEquilibriumExamples.Exchange
import MWGClassicalDemand.EconDebreu
import MWGClassicalDemand.AppendixMG
import Mathlib.Analysis.Convex.Caratheodory
import MWGClassicalDemand.AppendixMK
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The basic model and definitions (MWG Section 16.B, pp. 546-548)

An economy has consumers `i : ι`, firms `j : κ` and `L` commodities. Consumer `i` has a
consumption set `Xᵢ ⊆ ℝ^L` and a preference relation `≿ᵢ` (a relation `pref i x y`, read
`x ≿ᵢ y`, as in Chapter 3); firm `j` has a production set `Yⱼ ⊆ ℝ^L`; `ω̄` is the total
endowment (`PrefEconomy`). A private ownership economy (`PrivPrefEconomy`) has individual
endowments `ωᵢ` and profit shares `θᵢⱼ`. The book's standing assumptions (rational
preferences, `Yⱼ` nonempty and closed, `I, J > 0`) are hypotheses of the results that use them.

* **Definition 16.B.1**: allocations and feasibility, with the market clearing *equality*
  (16.B.1), and the set `A` of feasible allocations. Allocations are Chapter 10's
  `Allocation` (consumption vectors `x` and production vectors `y`).
* **Definition 16.B.2**: Pareto domination and Pareto optimality.
* **Definition 16.B.3**: Walrasian equilibrium of a private ownership economy. Profit
  maximization is Chapter 5's `supply`; "maximal for `≿ᵢ` in `B`" (footnote 2) is
  `IsMaximalFor`.
* **Definition 16.B.4**: price equilibrium with transfers; a Walrasian equilibrium is one, with
  wealth levels `wᵢ = p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` (p. 548).
* **Definition 16.D.1**: price quasiequilibrium with transfers; every price equilibrium with
  transfers and `p ≠ 0` is one (p. 552). The printed claim omits `p ≠ 0`: with `p = 0` it fails,
  even for every other price vector (`priceEqm_not_quasiEqm_counterexample`, correction 1).
  Under local nonsatiation `p ≠ 0` is automatic.
* Pure exchange (`Yⱼ = -ℝ^L₊`), the Edgeworth box as an instance (p. 546), and the claim of
  p. 547 that giving the whole endowment to one strongly monotone consumer is Pareto optimal.
* Bridges: utility economies (`PrefEconomy.ofUtility`); Chapter 10's competitive equilibrium
  (Definition 10.B.3) is Definition 16.B.3 for utility preferences; Chapter 15's exchange
  economy is the pure exchange economy with one disposal firm.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

/-- **Section 16.B** (MWG, p. 546). An economy `({(Xᵢ, ≿ᵢ)}, {Yⱼ}, ω̄)`: consumption sets,
preference relations (`pref i x y` reads `x ≿ᵢ y`), production sets and the total endowment. -/
structure PrefEconomy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets `Xᵢ`. -/
  X : ι → Set (Fin L → ℝ)
  /-- Preference relations `≿ᵢ`. -/
  pref : ι → (Fin L → ℝ) → (Fin L → ℝ) → Prop
  /-- Production sets `Yⱼ`. -/
  Y : κ → Set (Fin L → ℝ)
  /-- The total endowment `ω̄`. -/
  ω : Fin L → ℝ

/-- **Section 16.B** (MWG, p. 547). A private ownership economy
`({(Xᵢ, ≿ᵢ)}, {Yⱼ}, {(ωᵢ, θᵢ₁, ..., θᵢJ)})`. -/
structure PrivPrefEconomy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets `Xᵢ`. -/
  X : ι → Set (Fin L → ℝ)
  /-- Preference relations `≿ᵢ`. -/
  pref : ι → (Fin L → ℝ) → (Fin L → ℝ) → Prop
  /-- Production sets `Yⱼ`. -/
  Y : κ → Set (Fin L → ℝ)
  /-- Individual endowments `ωᵢ`. -/
  ωi : ι → Fin L → ℝ
  /-- Profit shares `θᵢⱼ`. -/
  θ : ι → κ → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- The negative orthant `-ℝ^L₊`, the free disposal technology. -/
def nonposOrthant (L : ℕ) : Set (Fin L → ℝ) := {y | ∀ l, y l ≤ 0}

/-- **Definition 16.B.1** (MWG, p. 546). `(x, y)` is an allocation: `xᵢ ∈ Xᵢ` and `yⱼ ∈ Yⱼ`. -/
def PrefEconomy.IsAllocation (E : PrefEconomy ι κ L) (a : Allocation ι κ L) : Prop :=
  (∀ i, a.x i ∈ E.X i) ∧ ∀ j, a.y j ∈ E.Y j

/-- **Definition 16.B.1** (MWG, pp. 546-547). A feasible allocation: market clearing with
equality, `∑ᵢ xᵢ = ω̄ + ∑ⱼ yⱼ` (16.B.1). -/
def PrefEconomy.IsFeasible (E : PrefEconomy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsAllocation a ∧ ∑ i, a.x i = E.ω + ∑ j, a.y j

/-- **Section 16.B** (MWG, p. 547). The set `A` of feasible allocations. -/
def PrefEconomy.feasibleSet (E : PrefEconomy ι κ L) : Set (Allocation ι κ L) :=
  {a | E.IsFeasible a}

/-- **Definition 16.B.2** (MWG, p. 547). `(x', y')` Pareto dominates `(x, y)`: `x'ᵢ ≿ᵢ xᵢ` for all
`i` and `x'ᵢ ≻ᵢ xᵢ` for some `i`. -/
def PrefEconomy.ParetoDominates (E : PrefEconomy ι κ L) (a' a : Allocation ι κ L) : Prop :=
  (∀ i, E.pref i (a'.x i) (a.x i)) ∧ ∃ i, Strict (E.pref i) (a'.x i) (a.x i)

/-- **Definition 16.B.2** (MWG, p. 547). A feasible allocation is Pareto optimal if no feasible
allocation Pareto dominates it. -/
def PrefEconomy.IsParetoOptimal (E : PrefEconomy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ E.ParetoDominates a' a

/-- **Footnote 2** (MWG, p. 548). `x` is maximal for `≿` in `B`: `x ∈ B` and `x ≿ x'` for all
`x' ∈ B`. -/
def IsMaximalFor (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) (B : Set (Fin L → ℝ))
    (x : Fin L → ℝ) : Prop :=
  x ∈ B ∧ ∀ x' ∈ B, r x x'

/-- **Definition 16.B.4** (MWG, p. 548). `(x*, y*)` and `p` form a price equilibrium with
transfers with wealth levels `w` (`∑ᵢ wᵢ = p·ω̄ + ∑ⱼ p·y*ⱼ`): (i) every `y*ⱼ` maximizes profit on
`Yⱼ`, (ii) every `x*ᵢ` is maximal for `≿ᵢ` in `{xᵢ ∈ Xᵢ : p·xᵢ ≤ wᵢ}`, (iii) markets clear. -/
def PrefEconomy.IsPriceEqmWithTransfers (E : PrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (w : ι → ℝ) : Prop :=
  ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧ (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, IsMaximalFor (E.pref i) (budgetSetOn (E.X i) p (w i)) (a.x i)) ∧
    ∑ i, a.x i = E.ω + ∑ j, a.y j

/-- **Definition 16.D.1** (MWG, pp. 551-552). `(x*, y*)` and `p ≠ 0` form a price quasiequilibrium
with transfers with wealth levels `w`: as Definition 16.B.4 except that (ii) only asks that
`xᵢ ≻ᵢ x*ᵢ` imply `p·xᵢ ≥ wᵢ` (with `x*ᵢ ∈ Xᵢ`, `(x*, y*)` being an allocation). -/
def PrefEconomy.IsPriceQuasiEqmWithTransfers (E : PrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (w : ι → ℝ) : Prop :=
  p ≠ 0 ∧ ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧ (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, a.x i ∈ E.X i ∧ ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → w i ≤ p ⬝ᵥ x) ∧
    ∑ i, a.x i = E.ω + ∑ j, a.y j

/-- **Section 16.B** (MWG, p. 546). A pure exchange economy: every firm has the free disposal
technology `Yⱼ = -ℝ^L₊`. -/
def PrefEconomy.IsPureExchange (E : PrefEconomy ι κ L) : Prop :=
  ∀ j, E.Y j = nonposOrthant L

/-- The economy of utility maximizers: `≿ᵢ` is represented by `uᵢ` (Section 16.E). -/
def PrefEconomy.ofUtility (X : ι → Set (Fin L → ℝ)) (u : ι → (Fin L → ℝ) → ℝ)
    (Y : κ → Set (Fin L → ℝ)) (ω : Fin L → ℝ) : PrefEconomy ι κ L where
  X := X
  pref := fun i => utilityPref (u i)
  Y := Y
  ω := ω

/-- **Section 16.B** (MWG, p. 547). The underlying economy, with `ω̄ = ∑ᵢ ωᵢ`. -/
def PrivPrefEconomy.toEconomy (E : PrivPrefEconomy ι κ L) : PrefEconomy ι κ L where
  X := E.X
  pref := E.pref
  Y := E.Y
  ω := ∑ i, E.ωi i

/-- **Section 16.B** (MWG, p. 547). Admissible shares: `θᵢⱼ ∈ [0, 1]` and `∑ᵢ θᵢⱼ = 1`. -/
def PrivPrefEconomy.SharesValid (E : PrivPrefEconomy ι κ L) : Prop :=
  (∀ i j, 0 ≤ E.θ i j ∧ E.θ i j ≤ 1) ∧ ∀ j, ∑ i, E.θ i j = 1

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` (Definition 16.B.3(ii)). -/
def PrivPrefEconomy.wealth (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (i : ι) : ℝ :=
  p ⬝ᵥ E.ωi i + ∑ j, E.θ i j * (p ⬝ᵥ a.y j)

/-- **Definition 16.B.3** (MWG, pp. 547-548). `(x*, y*)` and `p` form a Walrasian (competitive)
equilibrium: (i) profit maximization, (ii) preference maximization on the budget set with wealth
`p·ωᵢ + ∑ⱼ θᵢⱼ p·y*ⱼ`, (iii) `∑ᵢ x*ᵢ = ω̄ + ∑ⱼ y*ⱼ`. -/
def PrivPrefEconomy.IsWalrasEqm (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) : Prop :=
  (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, IsMaximalFor (E.pref i) (budgetSetOn (E.X i) p (E.wealth a p i)) (a.x i)) ∧
    ∑ i, a.x i = ∑ i, E.ωi i + ∑ j, a.y j

/-- **Definition 16.B.1** (MWG, pp. 546-547), unfolded: feasibility is good-by-good market
clearing `∑ᵢ x_{ℓi} = ω̄_ℓ + ∑ⱼ y_{ℓj}`. -/
theorem definition_16_B_1 (E : PrefEconomy ι κ L) (a : Allocation ι κ L) :
    E.IsFeasible a ↔ (∀ i, a.x i ∈ E.X i) ∧ (∀ j, a.y j ∈ E.Y j) ∧
      ∀ l, ∑ i, a.x i l = E.ω l + ∑ j, a.y j l := by
  unfold PrefEconomy.IsFeasible PrefEconomy.IsAllocation
  constructor
  · rintro ⟨⟨hx, hy⟩, h⟩
    refine ⟨hx, hy, fun l => ?_⟩
    have := congrFun h l
    simpa [Finset.sum_apply] using this
  · rintro ⟨hx, hy, h⟩
    refine ⟨⟨hx, hy⟩, funext fun l => ?_⟩
    simpa [Finset.sum_apply] using h l

/-- **Definition 16.B.2** (MWG, p. 547), unfolded. -/
theorem definition_16_B_2 (E : PrefEconomy ι κ L) (a : Allocation ι κ L) :
    E.IsParetoOptimal a ↔ E.IsFeasible a ∧ ∀ a', E.IsFeasible a' →
      (∀ i, E.pref i (a'.x i) (a.x i)) → ∀ i, ¬ Strict (E.pref i) (a'.x i) (a.x i) := by
  unfold PrefEconomy.IsParetoOptimal PrefEconomy.ParetoDominates
  constructor
  · rintro ⟨h, hno⟩
    exact ⟨h, fun a' ha' hle i hi => hno ⟨a', ha', hle, i, hi⟩⟩
  · rintro ⟨h, hall⟩
    exact ⟨h, fun ⟨a', ha', hle, i, hi⟩ => hall a' ha' hle i hi⟩

/-- **Definition 16.B.3** (MWG, pp. 547-548), unfolded. -/
theorem definition_16_B_3 (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) :
    E.IsWalrasEqm a p ↔
      (∀ j, a.y j ∈ E.Y j ∧ ∀ y ∈ E.Y j, p ⬝ᵥ y ≤ p ⬝ᵥ a.y j) ∧
      (∀ i, (a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ E.wealth a p i) ∧
        ∀ x ∈ E.X i, p ⬝ᵥ x ≤ E.wealth a p i → E.pref i (a.x i) x) ∧
      ∑ i, a.x i = ∑ i, E.ωi i + ∑ j, a.y j := by
  unfold PrivPrefEconomy.IsWalrasEqm supply IsMaximalFor budgetSetOn
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx hb => (h2 i).2 x ⟨hx, hb⟩⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx => (h2 i).2 x hx.1 hx.2⟩, h3⟩

/-- **Definition 16.B.4** (MWG, p. 548), unfolded. -/
theorem definition_16_B_4 (E : PrefEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (w : ι → ℝ) :
    E.IsPriceEqmWithTransfers a p w ↔ ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧
      (∀ j, a.y j ∈ E.Y j ∧ ∀ y ∈ E.Y j, p ⬝ᵥ y ≤ p ⬝ᵥ a.y j) ∧
      (∀ i, (a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ w i) ∧ ∀ x ∈ E.X i, p ⬝ᵥ x ≤ w i →
        E.pref i (a.x i) x) ∧
      ∑ i, a.x i = E.ω + ∑ j, a.y j := by
  unfold PrefEconomy.IsPriceEqmWithTransfers supply IsMaximalFor budgetSetOn
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, fun i => ⟨(h2 i).1, fun x hx hb => (h2 i).2 x ⟨hx, hb⟩⟩, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, fun i => ⟨(h2 i).1, fun x hx => (h2 i).2 x hx.1 hx.2⟩, h3⟩

/-- **Definition 16.C.1** (MWG, p. 549) is Definition 3.B.3 (Chapter 3's `LocallyNonsatiated`):
for every `xᵢ ∈ Xᵢ` and `ε > 0` there is `x'ᵢ ∈ Xᵢ` with `‖x'ᵢ - xᵢ‖ ≤ ε` and `x'ᵢ ≻ᵢ xᵢ`. -/
theorem definition_16_C_1 (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    LocallyNonsatiated X r ↔ ∀ x ∈ X, ∀ ε : ℝ, 0 < ε → ∃ x' ∈ X, euclidDist x' x ≤ ε ∧
      Strict r x' x := Iff.rfl

/-- **Definition 16.D.1** (MWG, pp. 551-552), unfolded. -/
theorem definition_16_D_1 (E : PrefEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (w : ι → ℝ) :
    E.IsPriceQuasiEqmWithTransfers a p w ↔ p ≠ 0 ∧ ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧
      (∀ j, a.y j ∈ E.Y j ∧ ∀ y ∈ E.Y j, p ⬝ᵥ y ≤ p ⬝ᵥ a.y j) ∧
      (∀ i, a.x i ∈ E.X i ∧ ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → w i ≤ p ⬝ᵥ x) ∧
      ∑ i, a.x i = E.ω + ∑ j, a.y j := Iff.rfl

/-- A price equilibrium with transfers is feasible. -/
theorem PrefEconomy.IsPriceEqmWithTransfers.isFeasible {E : PrefEconomy ι κ L}
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) :
    E.IsFeasible a :=
  ⟨⟨fun i => (h.2.2.1 i).1.1, fun j => (h.2.1 j).1⟩, h.2.2.2⟩

/-- A price quasiequilibrium with transfers is feasible. -/
theorem PrefEconomy.IsPriceQuasiEqmWithTransfers.isFeasible {E : PrefEconomy ι κ L}
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) : E.IsFeasible a :=
  ⟨⟨fun i => (h.2.2.2.1 i).1, fun j => (h.2.2.1 j).1⟩, h.2.2.2.2⟩

/-- The wealth levels of a Walrasian equilibrium sum to `p·ω̄ + ∑ⱼ p·yⱼ` when the shares of every
firm sum to one. -/
theorem PrivPrefEconomy.sum_wealth (E : PrivPrefEconomy ι κ L) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    (a : Allocation ι κ L) (p : Fin L → ℝ) :
    ∑ i, E.wealth a p i = p ⬝ᵥ E.toEconomy.ω + ∑ j, p ⬝ᵥ a.y j := by
  simp only [PrivPrefEconomy.wealth, PrivPrefEconomy.toEconomy, Finset.sum_add_distrib,
    dotProduct_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, hθ j, one_mul]

/-- **Section 16.B** (MWG, p. 548). A Walrasian equilibrium is a price equilibrium with transfers
(of the underlying economy) with wealth levels `wᵢ = p·ωᵢ + ∑ⱼ θᵢⱼ p·y*ⱼ`. -/
theorem PrivPrefEconomy.IsWalrasEqm.isPriceEqmWithTransfers {E : PrivPrefEconomy ι κ L}
    (hθ : ∀ j, ∑ i, E.θ i j = 1) {a : Allocation ι κ L} {p : Fin L → ℝ}
    (h : E.IsWalrasEqm a p) :
    E.toEconomy.IsPriceEqmWithTransfers a p (E.wealth a p) :=
  ⟨E.sum_wealth hθ a p, h.1, h.2.1, h.2.2⟩

/-- **Section 16.D** (MWG, p. 552). Every price equilibrium with transfers with `p ≠ 0` is a
price quasiequilibrium with transfers. -/
theorem PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm {E : PrefEconomy ι κ L}
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w)
    (hp : p ≠ 0) : E.IsPriceQuasiEqmWithTransfers a p w := by
  refine ⟨hp, h.1, h.2.1, fun i => ⟨(h.2.2.1 i).1.1, fun x hx hs => ?_⟩, h.2.2.2⟩
  by_contra hlt
  exact hs.2 ((h.2.2.1 i).2 x ⟨hx, (not_le.mp hlt).le⟩)

/-- The economy of the counterexample to the claim of p. 552 without `p ≠ 0`: one consumer on
`ℝ₊` who is indifferent between all bundles, one firm with `Y = ℝ`, no endowment. -/
def priceEqmCounterEconomy : PrefEconomy Unit Unit 1 where
  X := fun _ => nonnegOrthant 1
  pref := fun _ _ _ => True
  Y := fun _ => Set.univ
  ω := 0

/-- **Section 16.D** (MWG, p. 552), correction 1: "any price equilibrium with transfers is a price
quasiequilibrium with transfers" fails for `p = 0`. In `priceEqmCounterEconomy`, `x* = y* = 0`
with `p = 0` is a price equilibrium with transfers, but `(x*, y*)` is not a price quasiequilibrium
with transfers for any price vector (profits are unbounded on `Y = ℝ` for `p ≠ 0`). -/
theorem priceEqmCounterEconomy_counterexample :
    priceEqmCounterEconomy.IsPriceEqmWithTransfers ⟨fun _ => 0, fun _ => 0⟩ 0 (fun _ => 0) ∧
      ∀ p w, ¬ priceEqmCounterEconomy.IsPriceQuasiEqmWithTransfers
        ⟨fun _ => 0, fun _ => 0⟩ p w := by
  refine ⟨⟨by simp, fun _ => ⟨trivial, fun _ _ => by simp⟩,
    fun _ => ⟨⟨fun _ => le_rfl, by simp⟩, fun _ _ => trivial⟩, by simp [priceEqmCounterEconomy]⟩,
    fun p w h => ?_⟩
  obtain ⟨hp, -, hy, -⟩ := h
  have hp0 : p 0 ≠ 0 := fun h0 => hp (funext fun l => by rw [Subsingleton.elim l 0, h0]; rfl)
  have := (hy ()).2 (fun _ => p 0) trivial
  have h2 : p 0 * p 0 ≤ 0 := by simpa [dotProduct] using this
  exact hp0 (by nlinarith [mul_self_nonneg (p 0)])

/-- The sum of the dot products of a fixed price with finitely many vectors. -/
theorem dotProduct_finset_sum (p : Fin L → ℝ) (v : ι → Fin L → ℝ) :
    p ⬝ᵥ ∑ i, v i = ∑ i, p ⬝ᵥ v i :=
  dotProduct_sum p Finset.univ v

/-- A linear function changes by at most `∑ |pₗ|` times the Euclidean distance. -/
theorem abs_dotProduct_sub_le (p x y : Fin L → ℝ) :
    |p ⬝ᵥ y - p ⬝ᵥ x| ≤ (∑ l, |p l|) * euclidDist y x := by
  rw [← dotProduct_sub, dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using abs_sub_le_euclidDist y x l) (abs_nonneg _)

/-- Below wealth `w`, local nonsatiation on `X` gives a strictly preferred bundle of `X` still
costing less than `w`. -/
theorem lns_exists_better_cheaper {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (p : Fin L → ℝ) {x : Fin L → ℝ} (hx : x ∈ X) {w : ℝ}
    (hlt : p ⬝ᵥ x < w) : ∃ y ∈ X, p ⬝ᵥ y < w ∧ Strict r y x := by
  set c := ∑ l, |p l| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun l _ => abs_nonneg _
  set ε := (w - p ⬝ᵥ x) / (c + 1) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨y, hy, hd, hs⟩ := hlns x hx ε hεpos
  refine ⟨y, hy, ?_, hs⟩
  have h1 := abs_dotProduct_sub_le p x y
  have h2 : c * euclidDist y x ≤ c * ε := mul_le_mul_of_nonneg_left hd hc0
  have h3 : c * ε < w - p ⬝ᵥ x := by
    rw [hε, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have := (abs_le.mp h1).2
  linarith

/-- **Section 16.D** (MWG, p. 552). With at least one consumer, local nonsatiation rules out
`p = 0` at a price equilibrium with transfers, so the claim of p. 552 holds as printed. -/
theorem PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm_of_lns {E : PrefEconomy ι κ L}
    [Nonempty ι] (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) :
    E.IsPriceQuasiEqmWithTransfers a p w := by
  refine h.isPriceQuasiEqm fun hp => ?_
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨y, hy, -, hs⟩ := hlns i (a.x i) (h.2.2.1 i).1.1 1 one_pos
  exact hs.2 ((h.2.2.1 i).2 y ⟨hy, by rw [hp, zero_dotProduct]; simpa [hp] using
    (h.2.2.1 i).1.2⟩)

/-- **Footnote 3** (MWG, p. 552). With locally nonsatiated preferences, a price quasiequilibrium
with transfers has `p·x*ᵢ = wᵢ` for every consumer. -/
theorem PrefEconomy.IsPriceQuasiEqmWithTransfers.wealth_eq {E : PrefEconomy ι κ L}
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    ∀ i, p ⬝ᵥ a.x i = w i := by
  have hge : ∀ i, w i ≤ p ⬝ᵥ a.x i := by
    intro i
    by_contra hlt
    obtain ⟨y, hy, hpy, hs⟩ := lns_exists_better_cheaper (hlns i) p (h.2.2.2.1 i).1
      (not_le.mp hlt)
    have := (h.2.2.2.1 i).2 y hy hs
    linarith
  have hsum : ∑ i, p ⬝ᵥ a.x i = ∑ i, w i := by
    rw [← dotProduct_finset_sum, h.2.2.2.2, dotProduct_add, dotProduct_finset_sum, h.2.1]
  intro i
  exact le_antisymm ((Finset.sum_eq_sum_iff_of_le (fun i _ => hge i)).mp hsum.symm i
    (Finset.mem_univ i) ▸ le_rfl) (hge i)

/-- **Footnote 3** (MWG, p. 552). Under local nonsatiation, `(x*, y*, p)` is a price
quasiequilibrium with transfers (for some wealth levels) if and only if `p ≠ 0` and (i), (ii')
`xᵢ ≻ᵢ x*ᵢ ⟹ p·xᵢ ≥ p·x*ᵢ` and (iii) hold; the wealth levels are then `wᵢ = p·x*ᵢ`. -/
theorem footnote_3 {E : PrefEconomy ι κ L} (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i))
    (a : Allocation ι κ L) (p : Fin L → ℝ) :
    (∃ w, E.IsPriceQuasiEqmWithTransfers a p w) ↔ p ≠ 0 ∧
      (∀ j, a.y j ∈ supply (E.Y j) p) ∧
      (∀ i, a.x i ∈ E.X i ∧ ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) →
        p ⬝ᵥ a.x i ≤ p ⬝ᵥ x) ∧
      ∑ i, a.x i = E.ω + ∑ j, a.y j := by
  constructor
  · rintro ⟨w, h⟩
    have hw := h.wealth_eq hlns
    exact ⟨h.1, h.2.2.1, fun i => ⟨(h.2.2.2.1 i).1, fun x hx hs => by
      rw [hw i]; exact (h.2.2.2.1 i).2 x hx hs⟩, h.2.2.2.2⟩
  · rintro ⟨hp, hy, hx, hc⟩
    refine ⟨fun i => p ⬝ᵥ a.x i, hp, ?_, hy, hx, hc⟩
    rw [← dotProduct_finset_sum, hc, dotProduct_add, dotProduct_finset_sum]

/-- **Footnote 4** (MWG, p. 552). Under local nonsatiation and completeness, `(x*, y*, p)` is a
price equilibrium with transfers (for some wealth levels) if and only if (i), (ii'')
`xᵢ ≻ᵢ x*ᵢ ⟹ p·xᵢ > p·x*ᵢ` and (iii) hold; the wealth levels are then `wᵢ = p·x*ᵢ`, and (ii'')
says that `x*ᵢ` is maximal in `{xᵢ ∈ Xᵢ : p·xᵢ ≤ p·x*ᵢ}`. -/
theorem footnote_4 {E : PrefEconomy ι κ L} (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i))
    (hcomp : ∀ i, ∀ x ∈ E.X i, ∀ y ∈ E.X i, E.pref i x y ∨ E.pref i y x)
    (a : Allocation ι κ L) (p : Fin L → ℝ) :
    (∃ w, E.IsPriceEqmWithTransfers a p w) ↔
      (∀ j, a.y j ∈ supply (E.Y j) p) ∧
      (∀ i, a.x i ∈ E.X i ∧ ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) →
        p ⬝ᵥ a.x i < p ⬝ᵥ x) ∧
      ∑ i, a.x i = E.ω + ∑ j, a.y j := by
  constructor
  · rintro ⟨w, h⟩
    have hw : ∀ i, p ⬝ᵥ a.x i = w i := by
      intro i
      refine le_antisymm (h.2.2.1 i).1.2 ?_
      by_contra hlt
      obtain ⟨y, hy, hpy, hs⟩ := lns_exists_better_cheaper (hlns i) p (h.2.2.1 i).1.1
        (not_le.mp hlt)
      exact hs.2 ((h.2.2.1 i).2 y ⟨hy, hpy.le⟩)
    refine ⟨h.2.1, fun i => ⟨(h.2.2.1 i).1.1, fun x hx hs => ?_⟩, h.2.2.2⟩
    by_contra hle
    exact hs.2 ((h.2.2.1 i).2 x ⟨hx, (hw i) ▸ not_lt.mp hle⟩)
  · rintro ⟨hy, hx, hc⟩
    refine ⟨fun i => p ⬝ᵥ a.x i, ?_, hy, fun i => ⟨⟨(hx i).1, le_rfl⟩, fun x hxB => ?_⟩, hc⟩
    · rw [← dotProduct_finset_sum, hc, dotProduct_add, dotProduct_finset_sum]
    · rcases hcomp i (a.x i) (hx i).1 x hxB.1 with h1 | h1
      · exact h1
      · by_contra h2
        have := (hx i).2 x hxB.1 ⟨h1, h2⟩
        exact absurd hxB.2 (not_le.mpr this)

/-- **Section 16.B** (MWG, p. 547). In a pure exchange economy (`J ≥ 1`) with consumption sets
`ℝ^L₊`, the allocation that gives the whole endowment `ω̄ ≥ 0` to a consumer `i₀` with strongly
monotone preferences (and nothing to the others, `y = 0`) is Pareto optimal. -/
theorem paretoOptimal_all_to_one [DecidableEq ι] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L) (hω : 0 ≤ E.ω) (i₀ : ι)
    (hmono : PrefStronglyMonotone (nonnegOrthant L) (E.pref i₀)) :
    E.IsParetoOptimal ⟨fun i => if i = i₀ then E.ω else 0, fun _ => 0⟩ := by
  set a : Allocation ι κ L := ⟨fun i => if i = i₀ then E.ω else 0, fun _ => 0⟩ with ha
  have hsum0 : ∑ i, a.x i = E.ω := by
    simp only [ha, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine ⟨⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩, ?_⟩
  · rw [hX i]
    by_cases hi : i = i₀
    · simp only [ha, hi, ↓reduceIte]
      exact fun l => hω l
    · simp only [ha, hi, ↓reduceIte]
      exact fun _ => le_rfl
  · rw [hpe j]
    exact fun _ => le_rfl
  · rw [hsum0]
    simp [ha]
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hx0 : ∀ i, a'.x i ∈ nonnegOrthant L := fun i => hX i ▸ hx' i
  have hy0 : ∀ j l, a'.y j l ≤ 0 := fun j => by have := hy' j; rw [hpe j] at this; exact this
  -- the other consumers' bundles sum to at most `ω̄ - x'_{i₀}`
  have hsplit : ∀ l, a'.x i₀ l + ∑ i ∈ Finset.univ.erase i₀, a'.x i l =
      E.ω l + ∑ j, a'.y j l := by
    intro l
    have := congrFun hc' l
    simp only [Finset.sum_apply, Pi.add_apply] at this
    rw [← this, Finset.add_sum_erase _ (fun i => a'.x i l) (Finset.mem_univ i₀)]
  have hle0 : ∀ l, a'.x i₀ l ≤ E.ω l := by
    intro l
    have h1 := hsplit l
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, a'.x i l :=
      Finset.sum_nonneg fun i _ => hx0 i l
    have h3 : ∑ j, a'.y j l ≤ 0 := Finset.sum_nonpos fun j _ => hy0 j l
    linarith
  have hxi₀ : a.x i₀ = E.ω := by simp [ha]
  have heq : a'.x i₀ = E.ω := by
    by_contra hne
    have := hmono (a'.x i₀) (hx0 i₀) E.ω (fun l => hω l) hle0 (Ne.symm hne)
    exact this.2 (hxi₀ ▸ hle i₀)
  have hothers : ∀ i, i ≠ i₀ → a'.x i = 0 := by
    intro i hi
    funext l
    have h1 := hsplit l
    rw [heq] at h1
    have h3 : ∑ j, a'.y j l ≤ 0 := Finset.sum_nonpos fun j _ => hy0 j l
    have h4 : ∑ i ∈ Finset.univ.erase i₀, a'.x i l ≤ 0 := by linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx0 i l)).mp
      (le_antisymm h4 (Finset.sum_nonneg fun i _ => hx0 i l)) i (Finset.mem_erase.mpr
        ⟨hi, Finset.mem_univ i⟩)
    simpa using h5
  have hsame : a'.x k = a.x k := by
    by_cases hk0 : k = i₀
    · subst hk0
      rw [heq, hxi₀]
    · rw [hothers k hk0]
      simp [ha, hk0]
  rw [hsame] at hk
  exact hk.2 hk.1

/-- **Section 16.B** (MWG, p. 546). The Edgeworth box economy of Section 15.B as an economy of
this chapter: Chapter 15's exchange economy with one firm with the disposal technology
`Y₁ = -ℝ^L₊`. -/
def exchangeToPrefEconomy (E : MWG.GeneralEquilibriumExamples.ExchangeEconomy ι L) :
    PrefEconomy ι Unit L where
  X := E.X
  pref := fun i => utilityPref (E.u i)
  Y := fun _ => nonposOrthant L
  ω := E.totalEndowment

/-- **Section 16.B** (MWG, p. 546). The exchange economy is a pure exchange economy. -/
theorem exchangeToPrefEconomy_isPureExchange
    (E : MWG.GeneralEquilibriumExamples.ExchangeEconomy ι L) :
    (exchangeToPrefEconomy E).IsPureExchange := fun _ => rfl

/-- **Section 16.B** (MWG, p. 546). Feasibility in Chapter 15's exchange economy, `∑ᵢ xᵢ ≤ ω̄`
(15.B.1), is feasibility (16.B.1) with free disposal by the single firm. -/
theorem exchange_isFeasible_iff (E : MWG.GeneralEquilibriumExamples.ExchangeEconomy ι L)
    (x : ι → Fin L → ℝ) :
    E.IsFeasible x ↔ ∃ y, (exchangeToPrefEconomy E).IsFeasible ⟨x, fun _ => y⟩ := by
  constructor
  · rintro ⟨hx, hle⟩
    refine ⟨∑ i, x i - E.totalEndowment, ⟨⟨hx, fun _ => fun l => ?_⟩, ?_⟩⟩
    · simp only [Pi.sub_apply, Finset.sum_apply]
      linarith [hle l]
    · simp [exchangeToPrefEconomy]
  · rintro ⟨y, ⟨⟨hx, hy⟩, hc⟩⟩
    refine ⟨hx, fun l => ?_⟩
    have := congrFun hc l
    simp only [exchangeToPrefEconomy, Finset.univ_unique, Finset.sum_singleton,
      Pi.add_apply] at this
    have h2 : y l ≤ 0 := hy () l
    rw [Finset.sum_apply] at this
    linarith

/-- **Definitions 15.B.1 and 16.B.3**. A Walrasian equilibrium of Chapter 15's exchange economy at
prices `p ≥ 0` is a price equilibrium with transfers (wealth `p·ωᵢ`, no production) of the
corresponding pure exchange economy. -/
theorem exchange_isDemandEqm_isPriceEqm (E : MWG.GeneralEquilibriumExamples.ExchangeEconomy ι L)
    {p x : _} (hp : ∀ l, 0 ≤ p l) (h : E.IsDemandEqm p x) :
    (exchangeToPrefEconomy E).IsPriceEqmWithTransfers ⟨x, fun _ => 0⟩ p
      (fun i => p ⬝ᵥ E.ω i) := by
  refine ⟨?_, fun _ => ⟨fun _ => le_rfl, fun y hy => ?_⟩, fun i => ⟨(h.2 i).1,
    fun y hy => (h.2 i).2 y hy⟩, ?_⟩
  · simp [exchangeToPrefEconomy, MWG.GeneralEquilibriumExamples.ExchangeEconomy.totalEndowment,
      dotProduct_finset_sum]
  · simp only [dotProduct_zero]
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hy l)
  · simp [exchangeToPrefEconomy, h.1.2]

/-- **Definitions 10.B.3 and 16.B.3**. For preferences represented by utilities, Chapter 10's
competitive equilibrium of a private ownership economy is Definition 16.B.3. -/
theorem isWalrasEqm_iff_competitiveEqm (E : MWG.CompetitiveMarkets.PrivEconomy ι κ L)
    (a : Allocation ι κ L) (p : Fin L → ℝ) :
    (PrivPrefEconomy.mk E.X (fun i => utilityPref (E.u i)) E.Y E.ωi E.θ).IsWalrasEqm a p ↔
      E.IsCompetitiveEqm a p := by
  unfold PrivPrefEconomy.IsWalrasEqm MWG.CompetitiveMarkets.PrivEconomy.IsCompetitiveEqm
    IsMaximalFor walrasianDemandOn
  have hw : ∀ i, (PrivPrefEconomy.mk E.X (fun i => utilityPref (E.u i)) E.Y E.ωi E.θ).wealth
      a p i = E.wealth a p i := fun _ => rfl
  simp only [hw, utilityPref]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun l => ?_⟩
    have := congrFun h3 l
    simpa [Finset.sum_apply] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, funext fun l => ?_⟩
    simpa [Finset.sum_apply] using h3 l

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The first fundamental theorem of welfare economics (MWG Section 16.C, pp. 549-550)

* (16.C.1): at a price equilibrium with transfers anything strictly preferred to `x*ᵢ` costs more
  than `wᵢ`; (16.C.2) (Exercise 16.C.2): with locally nonsatiated (and transitive) preferences,
  anything weakly preferred costs at least `wᵢ`.
* **Proposition 16.C.1** (first welfare theorem) for price equilibria with transfers and for
  Walrasian equilibria. Only local nonsatiation and transitivity are used; no convexity.
* **Figure 16.C.1**: a price equilibrium with transfers in an Edgeworth box with a thick
  indifference "curve" that is not Pareto optimal (local nonsatiation fails).
* **Exercise 16.C.1** and the claim of p. 549: a continuous, locally nonsatiated preference has
  no nonempty closed bounded consumption set.
* **Exercise 16.C.3**: with convex consumption sets and strictly convex preferences, (a) there
  is at most one global satiation point and local nonsatiation holds everywhere else, (b) every
  price equilibrium with transfers is Pareto optimal.
* **Exercise 16.C.4**: Pareto optima for altruistic utilities `Uᵢ(u₁(x₁), ..., u_I(x_I))` are
  Pareto optima for the pleasure functions `uᵢ` (no concavity used); the converse fails.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **(16.C.1)** (MWG, p. 549). If `x*` is maximal for `≿` in `{x ∈ X : p·x ≤ w}`, every `x ∈ X`
with `x ≻ x*` has `p·x > w`. -/
theorem equation_16_C_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    {p : Fin L → ℝ} {w : ℝ} {xs : Fin L → ℝ} (h : IsMaximalFor r (budgetSetOn X p w) xs)
    {x : Fin L → ℝ} (hx : x ∈ X) (hs : Strict r x xs) : w < p ⬝ᵥ x := by
  by_contra hle
  exact hs.2 (h.2 x ⟨hx, not_lt.mp hle⟩)

/-- **Exercise 16.C.2** (MWG, p. 575), property (16.C.2) of p. 549. If `≿` is locally
nonsatiated and transitive on `X` and `x*` is maximal for `≿` in `{x ∈ X : p·x ≤ w}`, then
`x ≿ x*` implies `p·x ≥ w`. -/
theorem exercise_16_C_2 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)
    {p : Fin L → ℝ} {w : ℝ} {xs : Fin L → ℝ} (h : IsMaximalFor r (budgetSetOn X p w) xs)
    {x : Fin L → ℝ} (hx : x ∈ X) (hpref : r x xs) : w ≤ p ⬝ᵥ x := by
  by_contra hlt
  obtain ⟨y, hy, hpy, hs⟩ := lns_exists_better_cheaper hlns p hx (not_le.mp hlt)
  have hys : r xs y := h.2 y ⟨hy, hpy.le⟩
  exact hs.2 (htr x hx xs h.1.1 y hy hpref hys)

/-- **Proposition 16.C.1 (first fundamental theorem of welfare economics)** (MWG, p. 549). If
preferences are locally nonsatiated (and, as throughout, rational) and `(x*, y*, p)` is a price
equilibrium with transfers, then `(x*, y*)` is Pareto optimal. -/
theorem proposition_16_C_1 {E : PrefEconomy ι κ L}
    (hrat : ∀ i, RationalOn (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) : E.IsParetoOptimal a := by
  refine ⟨h.isFeasible, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hge : ∀ i, w i ≤ p ⬝ᵥ a'.x i := fun i =>
    exercise_16_C_2 (hlns i) (hrat i).2 (h.2.2.1 i) (hx' i) (hle i)
  have hgt : w k < p ⬝ᵥ a'.x k := equation_16_C_1 (h.2.2.1 k) (hx' k) hk
  have h1 : ∑ i, w i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a'.y j := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  have h3 : ∑ j, p ⬝ᵥ a'.y j ≤ ∑ j, p ⬝ᵥ a.y j :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 (a'.y j) (hy' j)
  linarith [h.1]

/-- **Proposition 16.C.1** (MWG, p. 549), second part: with locally nonsatiated rational
preferences and shares summing to one, every Walrasian equilibrium allocation is Pareto
optimal. -/
theorem proposition_16_C_1_walras {E : PrivPrefEconomy ι κ L}
    (hrat : ∀ i, RationalOn (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    {a : Allocation ι κ L} {p : Fin L → ℝ} (h : E.IsWalrasEqm a p) :
    E.toEconomy.IsParetoOptimal a :=
  proposition_16_C_1 hrat hlns (h.isPriceEqmWithTransfers hθ)

/-! ## Figure 16.C.1: a thick indifference curve -/

/-- Consumer 1 of Figure 16.C.1: `u₁(x) = min(x₁ + x₂, 1)`, satiated on `{x₁ + x₂ ≥ 1}`. -/
noncomputable def fig16C1u1 (x : Fin 2 → ℝ) : ℝ := min (x 0 + x 1) 1

/-- Consumer 2 of Figure 16.C.1: `u₂(x) = x₁ + x₂`, strongly monotone. -/
def fig16C1u2 (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- **Figure 16.C.1** (MWG, p. 550). The Edgeworth box economy (one disposal firm) with
`ω̄ = (2, 2)` and the utilities `fig16C1u1`, `fig16C1u2`. -/
noncomputable def fig16C1Economy : PrefEconomy (Fin 2) Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) ![fig16C1u1, fig16C1u2]
    (fun _ => nonposOrthant 2) ![2, 2]

/-- The allocation `x*` of Figure 16.C.1: `x*₁ = (3/2, 0)`, `x*₂ = (1/2, 2)`, no production. -/
noncomputable def fig16C1Eqm : Allocation (Fin 2) Unit 2 :=
  ⟨![![3 / 2, 0], ![1 / 2, 2]], fun _ => 0⟩

/-- Dot products in `ℝ²`. -/
theorem dot_two (p x : Fin 2 → ℝ) : p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Free disposal: at prices `p ≥ 0` no plan of `-ℝ^L₊` makes positive profit, so `0` maximizes
profit. -/
theorem zero_mem_supply_nonpos {p : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) :
    (0 : Fin L → ℝ) ∈ supply (nonposOrthant L) p := by
  refine ⟨fun _ => le_rfl, fun y hy => ?_⟩
  rw [dotProduct_zero]
  exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hy l)

/-- **Figure 16.C.1** (MWG, p. 550). `x*` with `p = (1, 1)` and wealth levels `(3/2, 5/2)` is a
price equilibrium with transfers, yet the allocation `x₁ = (1, 0)`, `x₂ = (1, 2)` Pareto dominates
it (consumer 1 is indifferent, consumer 2 strictly better off); local nonsatiation fails for
consumer 1 at `x*₁`. -/
theorem figure_16_C_1 :
    fig16C1Economy.IsPriceEqmWithTransfers fig16C1Eqm ![1, 1] ![3 / 2, 5 / 2] ∧
      ¬ fig16C1Economy.IsParetoOptimal fig16C1Eqm ∧
      ¬ LocallyNonsatiated (nonnegOrthant 2) (fig16C1Economy.pref 0) := by
  have hdot : ∀ x : Fin 2 → ℝ, (![1, 1] : Fin 2 → ℝ) ⬝ᵥ x = x 0 + x 1 := fun x => by
    rw [dot_two]; simp
  refine ⟨⟨?_, fun _ => ?_, fun i => ?_, ?_⟩, ?_, ?_⟩
  · simp [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm, hdot, Fin.sum_univ_two]
    norm_num
  · simpa [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm] using
      zero_mem_supply_nonpos (L := 2) (p := ![1, 1]) (fun l => by fin_cases l <;> simp)
  · fin_cases i
    · refine ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩
      · fin_cases l <;> norm_num [fig16C1Eqm]
      · simp [fig16C1Eqm, hdot]
      · simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm]
        simp [fig16C1u1]
        norm_num
    · refine ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩
      · fin_cases l <;> norm_num [fig16C1Eqm]
      · simp [fig16C1Eqm, hdot]
        norm_num
      · simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm]
        have := hx.2
        rw [hdot] at this
        simp [fig16C1u2]
        norm_num at this ⊢
        linarith
  · funext l
    fin_cases l <;> norm_num [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm, Fin.sum_univ_two]
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨![![1, 0], ![1, 2]], fun _ => 0⟩, ⟨⟨fun i => ?_, fun _ => ?_⟩, ?_⟩,
      fun i => ?_, 1, ?_, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp
    · simp [fig16C1Economy, PrefEconomy.ofUtility, nonposOrthant]
    · funext l
      fin_cases l <;> norm_num [fig16C1Economy, PrefEconomy.ofUtility, Fin.sum_univ_two]
    · fin_cases i <;>
        norm_num [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u1,
          fig16C1u2]
    · simp [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u2]
      norm_num
    · simp [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u2]
      norm_num
  · intro hlns
    obtain ⟨y, -, -, hs⟩ := hlns ![3 / 2, 0] (fun l => by fin_cases l <;> norm_num)
      1 one_pos
    apply hs.2
    simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref]
    simp [fig16C1u1]
    norm_num

/-! ## Exercise 16.C.1 -/

/-- **Exercise 16.C.1** (MWG, p. 575). If `X ⊆ ℝ^L` is nonempty, closed and bounded and the
(rational) preference `≿` on `X` is continuous, then `≿` is not locally nonsatiated: a continuous
utility representation (Proposition 3.C.1, Chapter 3's `proposition_3_C_1_general`) attains a
maximum on the compact set `X`. -/
theorem exercise_16_C_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hne : X.Nonempty) (hcl : IsClosed X) (hb : Bornology.IsBounded X) (hr : RationalOn X r)
    (hc : PrefContinuous X r) : ¬ LocallyNonsatiated X r := by
  intro hlns
  obtain ⟨u, hu, hrep⟩ := proposition_3_C_1_general hr hc
  have hK : IsCompact X := Metric.isCompact_of_isClosed_isBounded hcl hb
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hu
  obtain ⟨y, hy, -, hs⟩ := hlns x hx 1 one_pos
  exact hs.2 ((hrep x hx y hy).mpr (hmax hy))

/-- **Section 16.C** (MWG, p. 549). If `≿` is continuous and locally nonsatiated, a nonempty
closed consumption set must be unbounded. -/
theorem unbounded_of_lns {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hne : X.Nonempty) (hcl : IsClosed X) (hr : RationalOn X r) (hc : PrefContinuous X r)
    (hlns : LocallyNonsatiated X r) : ¬ Bornology.IsBounded X :=
  fun hb => exercise_16_C_1 hne hcl hb hr hc hlns

/-! ## Exercise 16.C.3 -/

/-- **Exercise 16.C.3** (MWG, p. 575). Strict convexity in the form used there: `x' ≿ x` and
`x' ≠ x` imply `αx' + (1 - α)x ≻ x` for `0 < α < 1`. -/
def StrictlyConvexC3 (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, r x' x → x' ≠ x → ∀ α : ℝ, 0 < α → α < 1 →
    Strict r (α • x' + (1 - α) • x) x

/-- With a complete preference, Definition 3.B.5's strict convexity implies the form of Exercise
16.C.3. -/
theorem strictlyConvexC3_of_prefStrictlyConvex {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r)
    (h : PrefStrictlyConvex X r) : StrictlyConvexC3 X r := by
  intro x hx x' hx' hxx hne α h0 h1
  have hrefl : r x x := (hr.1 x hx x hx).elim id id
  exact h x hx x' hx' x hx hxx hrefl hne α h0 h1

/-- With a rational preference on a convex set, the form of Exercise 16.C.3 implies Definition
3.B.5's strict convexity. -/
theorem prefStrictlyConvex_of_strictlyConvexC3 {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hX : Convex ℝ X) (hr : RationalOn X r)
    (h : StrictlyConvexC3 X r) : PrefStrictlyConvex X r := by
  intro x hx y hy z hz hyx hzx hne α h0 h1
  have hmem : α • y + (1 - α) • z ∈ X := hX hy hz h0.le (by linarith) (by ring)
  rcases hr.1 y hy z hz with hyz | hzy
  · have hs := h z hz y hy hyz hne α h0 h1
    refine ⟨hr.2 _ hmem z hz x hx hs.1 hzx, fun hxm => hs.2 (hr.2 z hz x hx _ hmem hzx hxm)⟩
  · have hs := h y hy z hz hzy (Ne.symm hne) (1 - α) (by linarith) (by linarith)
    have heq : (1 - α) • z + (1 - (1 - α)) • y = α • y + (1 - α) • z := by
      rw [sub_sub_cancel, add_comm]
    rw [heq] at hs
    refine ⟨hr.2 _ hmem y hy x hx hs.1 hyx, fun hxm => hs.2 (hr.2 y hy x hx _ hmem hyx hxm)⟩

/-- The Euclidean distance from `x` to `x + α(z - x)` is `α‖z - x‖` for `α ≥ 0`. -/
theorem euclidDist_segment {x z : Fin L → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    euclidDist (α • z + (1 - α) • x) x = α * euclidDist z x := by
  unfold euclidDist
  have : ∀ l, ((α • z + (1 - α) • x) l - x l) ^ 2 = α ^ 2 * (z l - x l) ^ 2 := fun l => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

/-- **Exercise 16.C.3(a)** (MWG, p. 575), first part. With `X` convex and `≿` rational and
strictly convex, there is at most one global satiation point. -/
theorem exercise_16_C_3a_unique {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (h : StrictlyConvexC3 X r) {s s' : Fin L → ℝ} (hs : s ∈ X)
    (hs' : s' ∈ X) (hsat : ∀ z ∈ X, r s z) (hsat' : ∀ z ∈ X, r s' z) : s = s' := by
  by_contra hne
  have hmem : (1 / 2 : ℝ) • s' + ((1 : ℝ) - 1 / 2) • s ∈ X :=
    hX hs' hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num)
  have := h s hs s' hs' (hsat' s hs) (Ne.symm hne) (1 / 2) (by norm_num) (by norm_num)
  exact this.2 (hsat _ hmem)

/-- **Exercise 16.C.3(a)** (MWG, p. 575), second part. With `X` convex and `≿` rational and
strictly convex, `≿` is locally nonsatiated at every bundle that is not a global satiation
point. -/
theorem exercise_16_C_3a_lns {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (h : StrictlyConvexC3 X r) {x : Fin L → ℝ}
    (hx : x ∈ X) (hns : ¬ ∀ z ∈ X, r x z) :
    ∀ ε : ℝ, 0 < ε → ∃ y ∈ X, euclidDist y x ≤ ε ∧ Strict r y x := by
  intro ε hε
  push Not at hns
  obtain ⟨z, hz, hxz⟩ := hns
  have hzx : r z x := (hr.1 x hx z hz).resolve_left hxz
  have hne : z ≠ x := by
    rintro rfl
    exact hxz ((hr.1 z hz z hz).elim id id)
  have hd : 0 < euclidDist z x := by
    rcases (euclidDist_nonneg z x).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      apply hne
      funext l
      have := abs_sub_le_euclidDist z x l
      rw [← h0] at this
      linarith [abs_nonneg (z l - x l), abs_le.mp this]
  set α := min (1 / 2) (ε / euclidDist z x) with hα
  have hα0 : 0 < α := lt_min (by norm_num) (div_pos hε hd)
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨α • z + (1 - α) • x, hX hz hx hα0.le (by linarith) (by ring), ?_,
    h x hx z hz hzx hne α hα0 hα1⟩
  rw [euclidDist_segment hα0.le]
  calc α * euclidDist z x ≤ ε / euclidDist z x * euclidDist z x :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le
    _ = ε := div_mul_cancel₀ ε hd.ne'

/-- **Exercise 16.C.3(b)** (MWG, p. 575). If every `Xᵢ` is convex and every `≿ᵢ` is rational and
strictly convex (in the form of the exercise; rationality is not needed), every price
equilibrium with transfers is Pareto optimal; satiation is allowed. -/
theorem exercise_16_C_3b {E : PrefEconomy ι κ L} (hX : ∀ i, Convex ℝ (E.X i))
    (hsc : ∀ i, StrictlyConvexC3 (E.X i) (E.pref i))
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) :
    E.IsParetoOptimal a := by
  refine ⟨h.isFeasible, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hge : ∀ i, p ⬝ᵥ a.x i ≤ p ⬝ᵥ a'.x i := by
    intro i
    by_cases heq : a'.x i = a.x i
    · rw [heq]
    by_contra hlt
    push Not at hlt
    have hmax := h.2.2.1 i
    have hs := hsc i (a.x i) hmax.1.1 (a'.x i) (hx' i) (hle i) heq (1 / 2) (by norm_num)
      (by norm_num)
    have hmem : (1 / 2 : ℝ) • a'.x i + ((1 : ℝ) - 1 / 2) • a.x i ∈ budgetSetOn (E.X i) p (w i) := by
      refine ⟨(hX i) (hx' i) hmax.1.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num), ?_⟩
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have := hmax.1.2
      linarith
    exact hs.2 (hmax.2 _ hmem)
  have hgt : p ⬝ᵥ a.x k < p ⬝ᵥ a'.x k :=
    lt_of_le_of_lt (h.2.2.1 k).1.2 (equation_16_C_1 (h.2.2.1 k) (hx' k) hk)
  have h1 : ∑ i, p ⬝ᵥ a.x i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a'.y j := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  have h2' : ∑ i, p ⬝ᵥ a.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j := by
    rw [← dotProduct_finset_sum, h.2.2.2, dotProduct_add, dotProduct_finset_sum]
  have h3 : ∑ j, p ⬝ᵥ a'.y j ≤ ∑ j, p ⬝ᵥ a.y j :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 (a'.y j) (hy' j)
  linarith

/-! ## Exercise 16.C.4: altruism -/

/-- **Exercise 16.C.4** (MWG, p. 575). Pareto optimality for utilities `Vᵢ` defined on whole
allocations (consumption externalities). -/
def PrefEconomy.IsParetoOptimalWrt (E : PrefEconomy ι κ L)
    (V : ι → Allocation ι κ L → ℝ) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ (∀ i, V i a ≤ V i a') ∧ ∃ i, V i a < V i a'

/-- **Exercise 16.C.4** (MWG, p. 575). If every altruistic utility
`Uᵢ(x) = Wᵢ(u₁(x₁), ..., u_I(x_I))` is nondecreasing in every consumer's pleasure and strictly
increasing in `i`'s own, an allocation Pareto optimal for the `Uᵢ` is Pareto optimal for the
pleasure functions `uᵢ`. No concavity of the `uᵢ` or the `Wᵢ` is used. -/
theorem exercise_16_C_4 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {W : ι → (ι → ℝ) → ℝ}
    (hmono : ∀ i, Monotone (W i))
    (hown : ∀ i (v v' : ι → ℝ), v ≤ v' → v i < v' i → W i v < W i v')
    {a : Allocation ι κ L}
    (h : (PrefEconomy.ofUtility X u Y ω).IsParetoOptimalWrt
      (fun i b => W i (fun k => u k (b.x k))) a) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a := by
  refine ⟨h.1, ?_⟩
  rintro ⟨a', ha', hle, k, hk⟩
  have hle' : (fun k => u k (a.x k)) ≤ fun k => u k (a'.x k) := fun i => hle i
  have hlt : u k (a.x k) < u k (a'.x k) := not_le.mp hk.2
  exact h.2 ⟨a', ha', fun i => hmono i hle', k, hown k _ _ hle' hlt⟩

/-- The pleasure function `x ↦ x₁` of the one-good example of Exercise 16.C.4. -/
def altruismPleasure : Fin 2 → (Fin 1 → ℝ) → ℝ := fun _ x => x 0

/-- The altruistic utilities of the example: `U₁ = v₁ + 2v₂`, `U₂ = v₁ + v₂`. -/
def altruismW : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun v => v 0 + 2 * v 1, fun v => v 0 + v 1]

/-- **Exercise 16.C.4** (MWG, p. 575): the converse fails, so competitive markets need not reach
altruistic Pareto optima. With one good, endowment `2`, `uᵢ(x) = x` and `U₁ = u₁ + 2u₂`,
`U₂ = u₁ + u₂`, giving everything to consumer 1 is Pareto optimal for the pleasure functions (and
is a Walrasian equilibrium allocation when consumer 1 owns everything) but not for the
altruistic utilities: giving everything to consumer 2 raises `U₁` and leaves `U₂` unchanged. -/
theorem exercise_16_C_4_converse_fails :
    (∀ i, Monotone (altruismW i)) ∧
    (∀ i (v v' : Fin 2 → ℝ), v ≤ v' → v i < v' i → altruismW i v < altruismW i v') ∧
    (PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) altruismPleasure
        (fun _ : Unit => nonposOrthant 1) ![2]).IsParetoOptimal
      ⟨![![2], 0], fun _ => 0⟩ ∧
    ¬ (PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) altruismPleasure
        (fun _ : Unit => nonposOrthant 1) ![2]).IsParetoOptimalWrt
      (fun i b => altruismW i (fun k => altruismPleasure k (b.x k))) ⟨![![2], 0], fun _ => 0⟩ := by
  refine ⟨fun i => ?_, fun i v v' hle hlt => ?_, ?_, ?_⟩
  · intro v v' hle
    have h0 := hle 0
    have h1 := hle 1
    fin_cases i <;> simp [altruismW] <;> linarith
  · have h0 := hle 0
    have h1 := hle 1
    fin_cases i <;> simp [altruismW] at hlt ⊢ <;> linarith
  · have h := paretoOptimal_all_to_one (E := PrefEconomy.ofUtility (fun _ => nonnegOrthant 1)
      altruismPleasure (fun _ : Unit => nonposOrthant 1) ![2]) (fun _ => rfl) (fun _ => rfl)
      (fun l => by fin_cases l; simp [PrefEconomy.ofUtility]) 0 ?_
    · have heq : (fun i : Fin 2 => if i = 0 then (![2] : Fin 1 → ℝ) else 0) = ![![2], 0] := by
        funext i
        fin_cases i <;> simp
      simpa [PrefEconomy.ofUtility, heq] using h
    · intro x hx y hy hxy hne
      simp only [PrefEconomy.ofUtility, utilityPref, altruismPleasure, Strict]
      have : x 0 ≠ y 0 := fun h0 => hne (funext fun l => by
        rw [Subsingleton.elim l 0]; exact h0.symm)
      have h0 := hxy 0
      exact ⟨h0, not_le.mpr (lt_of_le_of_ne h0 this)⟩
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨![0, ![2]], fun _ => 0⟩, ⟨⟨fun i => ?_, fun _ => ?_⟩, ?_⟩, fun i => ?_,
      0, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp
    · simp [PrefEconomy.ofUtility, nonposOrthant]
    · funext l
      fin_cases l
      simp [PrefEconomy.ofUtility, Fin.sum_univ_two]
    · fin_cases i <;> norm_num [altruismW, altruismPleasure]
    · simp [altruismW, altruismPleasure]

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The second fundamental theorem of welfare economics (MWG Section 16.D, pp. 551-554)

* **Proposition 16.D.1** (second welfare theorem): with convex production sets and convex,
  locally nonsatiated (rational) preferences, every Pareto optimal allocation is a price
  quasiequilibrium with transfers for some `p ≠ 0`, with wealth levels `wᵢ = p·x*ᵢ`. The proof
  follows the book's nine steps: the preferred sets `Vᵢ` are convex (Step 1), so are
  `V = ∑ Vᵢ` and `Y + {ω̄}` (Step 2), they are disjoint (Step 3), the separating hyperplane
  theorem (Theorem M.G.2, Chapter 3's `theorem_M_G_2_ii`) gives `p ≠ 0` and `r` (Step 4), and
  Steps 5-9 derive profit maximization and condition (ii) of Definition 16.D.1. The book's
  standing assumptions `I > 0` and the existence of the allocation give `L ≥ 1` (local
  nonsatiation fails in `ℝ⁰`), which Theorem M.G.2 needs.
* **Exercise 16.D.1** (and the small type of p. 552): under local nonsatiation, condition (ii')
  is expenditure minimization on the upper contour set.
* **Exercise 16.D.2**: local nonsatiation cannot be dropped from Proposition 16.D.1.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- Transitivity through a strict preference: `z ≻ x` and `x ≿ x*` give `z ≻ x*`. -/
theorem strict_of_strict_of_pref {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z) {z x xs : Fin L → ℝ}
    (hz : z ∈ X) (hx : x ∈ X) (hxs : xs ∈ X) (hzx : Strict r z x) (hxxs : r x xs) :
    Strict r z xs :=
  ⟨htr z hz x hx xs hxs hzx.1 hxxs, fun h => hzx.2 (htr x hx xs hxs z hz hxxs h)⟩

/-- Transitivity through a strict preference: `z ≿ x` and `x ≻ x*` give `z ≻ x*`. -/
theorem strict_of_pref_of_strict {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z) {z x xs : Fin L → ℝ}
    (hz : z ∈ X) (hx : x ∈ X) (hxs : xs ∈ X) (hzx : r z x) (hxxs : Strict r x xs) :
    Strict r z xs :=
  ⟨htr z hz x hx xs hxs hzx hxxs.1, fun h => hxxs.2 (htr xs hxs z hz x hx h hzx)⟩

/-- The set `Vᵢ = {xᵢ ∈ Xᵢ : xᵢ ≻ᵢ x*ᵢ}` of the proof of Proposition 16.D.1. -/
def preferredSet (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (xs : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ X ∧ Strict r x xs}

/-- The set `V = ∑ᵢ Vᵢ` of the proof of Proposition 16.D.1. -/
def PrefEconomy.aggPreferredSet (E : PrefEconomy ι κ L) (a : Allocation ι κ L) :
    Set (Fin L → ℝ) :=
  {v | ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ preferredSet (E.X i) (E.pref i) (a.x i)) ∧
    v = ∑ i, x i}

/-- The set `Y + {ω̄}` of aggregate bundles available for consumption. -/
def PrefEconomy.availableSet (E : PrefEconomy ι κ L) : Set (Fin L → ℝ) :=
  {z | ∃ y : κ → Fin L → ℝ, (∀ j, y j ∈ E.Y j) ∧ z = E.ω + ∑ j, y j}

/-- **Proposition 16.D.1, Step 1** (MWG, p. 553). With a rational and convex preference, every
set `Vᵢ` of bundles preferred to `x*ᵢ ∈ Xᵢ` is convex. -/
theorem proposition_16_D_1_step1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) (hc : PrefConvex X r) {xs : Fin L → ℝ} (hxs : xs ∈ X) :
    Convex ℝ (preferredSet X r xs) := by
  intro x hx x' hx' α β hα hβ hαβ
  rcases hr.1 x hx.1 x' hx'.1 with hxx' | hx'x
  · -- `x ≿ x'`: the combination is in the upper contour set of `x'`
    have hrefl : r x' x' := (hr.1 x' hx'.1 x' hx'.1).elim id id
    have hm := hc x' hx'.1 ⟨hx.1, hxx'⟩ ⟨hx'.1, hrefl⟩ hα hβ hαβ
    exact ⟨hm.1, strict_of_pref_of_strict hr.2 hm.1 hx'.1 hxs hm.2 hx'.2⟩
  · have hrefl : r x x := (hr.1 x hx.1 x hx.1).elim id id
    have hm := hc x hx.1 ⟨hx.1, hrefl⟩ ⟨hx'.1, hx'x⟩ hα hβ hαβ
    exact ⟨hm.1, strict_of_pref_of_strict hr.2 hm.1 hx.1 hxs hm.2 hx.2⟩

omit [Fintype κ] in
/-- **Proposition 16.D.1, Step 2** (MWG, p. 553), for `V`: a sum of convex sets is convex. -/
theorem proposition_16_D_1_step2_V {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (h : ∀ i, Convex ℝ (preferredSet (E.X i) (E.pref i) (a.x i))) :
    Convex ℝ (E.aggPreferredSet a) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ α β hα hβ hαβ
  refine ⟨fun i => α • x i + β • x' i, fun i => h i (hx i) (hx' i) hα hβ hαβ, ?_⟩
  rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]

omit [Fintype ι] in
/-- **Proposition 16.D.1, Step 2** (MWG, p. 553), for `Y + {ω̄}`. -/
theorem proposition_16_D_1_step2_Y {E : PrefEconomy ι κ L} (h : ∀ j, Convex ℝ (E.Y j)) :
    Convex ℝ E.availableSet := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ α β hα hβ hαβ
  refine ⟨fun j => α • y j + β • y' j, fun j => h j (hy j) (hy' j) hα hβ hαβ, ?_⟩
  have : α • E.ω + β • E.ω = E.ω := by rw [← add_smul, hαβ, one_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, smul_add, smul_add]
  rw [show E.ω + (α • ∑ j, y j + β • ∑ j, y' j) =
    (α • E.ω + β • E.ω) + (α • ∑ j, y j + β • ∑ j, y' j) by rw [this]]
  abel

/-- **Proposition 16.D.1, Step 3** (MWG, p. 553). At a Pareto optimum (with `I > 0`),
`V ∩ (Y + {ω̄}) = ∅`. -/
theorem proposition_16_D_1_step3 [Nonempty ι] {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (hpo : E.IsParetoOptimal a) : Disjoint (E.aggPreferredSet a) E.availableSet := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact hpo.2 ⟨⟨x, y⟩, ⟨⟨fun i => (hx i).1, hy⟩, heq⟩, fun i => (hx i).2.1, i₀, (hx i₀).2⟩

omit [Fintype κ] in
/-- **Proposition 16.D.1, Step 5** (MWG, p. 554). If `p·v ≥ r` on `V` and preferences are locally
nonsatiated and transitive, then `xᵢ ≿ᵢ x*ᵢ` for every `i` implies `p·(∑ᵢ xᵢ) ≥ r` (footnote 5:
`∑ᵢ {xᵢ : xᵢ ≿ᵢ x*ᵢ}` lies in the closure of `V`). -/
theorem proposition_16_D_1_step5 {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (htr : ∀ i, ∀ x ∈ E.X i, ∀ y ∈ E.X i, ∀ z ∈ E.X i, E.pref i x y → E.pref i y z →
      E.pref i x z)
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) (hax : ∀ i, a.x i ∈ E.X i)
    {p : Fin L → ℝ} {r : ℝ} (hV : ∀ v ∈ E.aggPreferredSet a, r ≤ p ⬝ᵥ v)
    {x : ι → Fin L → ℝ} (hx : ∀ i, x i ∈ E.X i) (hpref : ∀ i, E.pref i (x i) (a.x i)) :
    r ≤ p ⬝ᵥ ∑ i, x i := by
  by_contra hlt
  push Not at hlt
  set δ := r - p ⬝ᵥ ∑ i, x i with hδ
  have hδ0 : 0 < δ := by linarith
  set c := ∑ l, |p l| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun l _ => abs_nonneg _
  set n := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set ε := δ / ((c + 1) * (n + 1)) with hε
  have hε0 : 0 < ε := div_pos hδ0 (by positivity)
  have hex : ∀ i, ∃ z ∈ E.X i, euclidDist z (x i) ≤ ε ∧ Strict (E.pref i) z (x i) :=
    fun i => hlns i (x i) (hx i) ε hε0
  choose z hz hzd hzs using hex
  have hzV : ∑ i, z i ∈ E.aggPreferredSet a :=
    ⟨z, fun i => ⟨hz i, strict_of_strict_of_pref (htr i) (hz i) (hx i) (hax i) (hzs i)
      (hpref i)⟩, rfl⟩
  have h1 := hV _ hzV
  have h2 : p ⬝ᵥ ∑ i, z i - p ⬝ᵥ ∑ i, x i ≤ n * (c * ε) := by
    rw [dotProduct_finset_sum, dotProduct_finset_sum, ← Finset.sum_sub_distrib, hn,
      ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i _ => ?_
    have := (abs_le.mp (abs_dotProduct_sub_le p (x i) (z i))).2
    have h3 : c * euclidDist (z i) (x i) ≤ c * ε := mul_le_mul_of_nonneg_left (hzd i) hc0
    linarith
  have h4 : n * (c * ε) < δ := by
    have : n * (c * ε) = δ * (n * c / ((c + 1) * (n + 1))) := by
      rw [hε]; field_simp
    rw [this]
    have hfrac : n * c / ((c + 1) * (n + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    nlinarith
  linarith

/-- **Proposition 16.D.1 (second fundamental theorem of welfare economics)** (MWG, p. 552).
Suppose every `Yⱼ` is convex and every `≿ᵢ` is rational, convex and locally nonsatiated (and
`I > 0`). Then for every Pareto optimal allocation `(x*, y*)` there is `p ≠ 0` such that
`(x*, y*, p)` is a price quasiequilibrium with transfers, with wealth levels `wᵢ = p·x*ᵢ`
(Step 9). -/
theorem proposition_16_D_1 [Nonempty ι] {E : PrefEconomy ι κ L} (hY : ∀ j, Convex ℝ (E.Y j))
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefConvex (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    (hpo : E.IsParetoOptimal a) :
    ∃ p : Fin L → ℝ, p ≠ 0 ∧ E.IsPriceQuasiEqmWithTransfers a p (fun i => p ⬝ᵥ a.x i) := by
  classical
  obtain ⟨⟨hax, hay⟩, hclear⟩ := hpo.1
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- `L ≥ 1`: local nonsatiation fails in `ℝ⁰`
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      obtain ⟨z, -, -, hz⟩ := hlns i₀ (a.x i₀) (hax i₀) 1 one_pos
      have : z = a.x i₀ := funext fun l => l.elim0
      exact absurd (this ▸ hz.1) hz.2
    · exact h0
  -- Steps 1-3
  have hVconv := proposition_16_D_1_step2_V (E := E) (a := a)
    fun i => proposition_16_D_1_step1 (hr i) (hc i) (hax i)
  have hYconv := proposition_16_D_1_step2_Y hY
  have hdisj := proposition_16_D_1_step3 hpo
  have hVne : (E.aggPreferredSet a).Nonempty := by
    have hex : ∀ i, ∃ z ∈ E.X i, euclidDist z (a.x i) ≤ 1 ∧ Strict (E.pref i) z (a.x i) :=
      fun i => hlns i (a.x i) (hax i) 1 one_pos
    choose z hz _ hzs using hex
    exact ⟨_, z, fun i => ⟨hz i, hzs i⟩, rfl⟩
  have hYne : E.availableSet.Nonempty := ⟨_, a.y, hay, rfl⟩
  -- Step 4: the separating hyperplane
  obtain ⟨p, hp, rr, hpV, hpY⟩ := theorem_M_G_2_ii hL hVconv hYconv hVne hYne hdisj
  -- Step 5
  have step5 := fun x hx hpref => proposition_16_D_1_step5 (fun i => (hr i).2) hlns hax hpV
    (x := x) hx hpref
  have hrefl : ∀ i, E.pref i (a.x i) (a.x i) := fun i => ((hr i).1 _ (hax i) _ (hax i)).elim id id
  -- Step 6: `p·(∑ x*ᵢ) = r`
  have hstar : p ⬝ᵥ ∑ i, a.x i = rr :=
    le_antisymm (hpY _ ⟨a.y, hay, hclear⟩) (step5 a.x hax hrefl)
  refine ⟨p, hp, hp, ?_, fun j => ⟨hay j, fun yj hyj => ?_⟩, fun i => ⟨hax i, fun xi hxi hs => ?_⟩,
    hclear⟩
  · rw [← dotProduct_finset_sum, hclear, dotProduct_add, dotProduct_finset_sum]
  · -- Step 7: profit maximization
    have hmem : E.ω + ∑ k, Function.update a.y j yj k ∈ E.availableSet :=
      ⟨Function.update a.y j yj, fun k => by
        by_cases hk : k = j
        · subst hk; simpa using hyj
        · rw [Function.update_of_ne hk]; exact hay k, rfl⟩
    have h1 := hpY _ hmem
    rw [← hstar, hclear, dotProduct_add, dotProduct_add, dotProduct_finset_sum,
      dotProduct_finset_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ a.y k) (Finset.mem_univ j)] at h1
    have h2 : ∑ k ∈ Finset.univ.erase j, p ⬝ᵥ Function.update a.y j yj k =
        ∑ k ∈ Finset.univ.erase j, p ⬝ᵥ a.y k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [Function.update_self] at h1
    linarith
  · -- Step 8: anything preferred costs at least `p·x*ᵢ`
    have h1 := step5 (Function.update a.x i xi) (fun k => by
        by_cases hk : k = i
        · subst hk; simpa using hxi
        · rw [Function.update_of_ne hk]; exact hax k)
      (fun k => by
        by_cases hk : k = i
        · subst hk; simpa using hs.1
        · rw [Function.update_of_ne hk]; exact hrefl k)
    rw [← hstar, dotProduct_finset_sum, dotProduct_finset_sum,
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ Function.update a.x i xi k) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ a.x k) (Finset.mem_univ i)] at h1
    have h2 : ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ Function.update a.x i xi k =
        ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ a.x k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [Function.update_self] at h1
    linarith

/-! ## Exercise 16.D.1 -/

/-- **Exercise 16.D.1** (MWG, p. 575; p. 552). If `≿` is locally nonsatiated and transitive on
`X` and `x* ∈ X`, then "`x ≻ x*` implies `p·x ≥ p·x*`" holds if and only if `x*` minimizes
expenditure at prices `p` on `{x ∈ X : x ≿ x*}`. -/
theorem exercise_16_D_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)
    {xs : Fin L → ℝ} (hxs : xs ∈ X) (p : Fin L → ℝ) :
    (∀ x ∈ X, Strict r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) ↔ (∀ x ∈ X, r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) := by
  constructor
  · intro h x hx hpref
    by_contra hlt
    obtain ⟨z, hz, hpz, hs⟩ := lns_exists_better_cheaper hlns p hx (not_le.mp hlt)
    have := h z hz (strict_of_strict_of_pref htr hz hx hxs hs hpref)
    linarith
  · exact fun h x hx hs => h x hx hs.1

/-! ## Exercise 16.D.2 -/

/-- The utility of Exercise 16.D.2: `u(x) = x` for `x ≤ 1`, `1` on `[1, 2]`, `x - 1` beyond (a
thick indifference interval). -/
noncomputable def ex16D2u (x : Fin 1 → ℝ) : ℝ := min (x 0) (max 1 (x 0 - 1))

/-- **Exercise 16.D.2** (MWG, p. 575). The one-consumer, one-firm economy: `X = ℝ₊`, utility
`ex16D2u` (continuous, nondecreasing, hence convex preferences), the convex free disposal
technology `Y = -ℝ₊` and endowment `ω̄ = 3/2`. -/
noncomputable def ex16D2Economy : PrefEconomy Unit Unit 1 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) (fun _ => ex16D2u) (fun _ => nonposOrthant 1)
    ![3 / 2]

/-- **Exercise 16.D.2** (MWG, p. 575). In `ex16D2Economy` the allocation `x* = 1`, `y* = -1/2` is
Pareto optimal, but it is neither a price equilibrium with transfers (for any `p`, including
`p = 0`) nor a price quasiequilibrium with transfers (for any `p`). The preference is continuous
and convex and `Y` is convex; the condition of Proposition 16.D.1 that fails is local
nonsatiation (at `x* = 1`). -/
theorem exercise_16_D_2 :
    ex16D2Economy.IsParetoOptimal ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ ∧
      (∀ p w, ¬ ex16D2Economy.IsPriceEqmWithTransfers ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ p w) ∧
      (∀ p w, ¬ ex16D2Economy.IsPriceQuasiEqmWithTransfers
        ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ p w) ∧
      Convex ℝ (nonposOrthant 1) ∧ ContinuousOn ex16D2u (nonnegOrthant 1) ∧
      PrefConvex (nonnegOrthant 1) (utilityPref ex16D2u) ∧
      ¬ LocallyNonsatiated (nonnegOrthant 1) (utilityPref ex16D2u) := by
  have hle1 : ∀ t : ℝ, t ≤ 3 / 2 → min t (max 1 (t - 1)) ≤ 1 := fun t ht =>
    (min_le_right _ _).trans (max_le le_rfl (by linarith))
  have hval1 : ex16D2u ![1] = 1 := by norm_num [ex16D2u]
  have hmono : Monotone fun t : ℝ => min t (max 1 (t - 1)) := fun s t hst =>
    min_le_min hst (max_le_max le_rfl (by linarith))
  -- profit maximization on `-ℝ₊` at `y* = -1/2` is impossible for `p ≠ 0`
  have hprofit : ∀ p : Fin 1 → ℝ, (![-1 / 2] : Fin 1 → ℝ) ∈ supply (nonposOrthant 1) p →
      p = 0 := by
    intro p hp
    have h0 := hp.2 0 (fun _ => le_rfl)
    have h1 := hp.2 ![-1] (fun l => by fin_cases l; norm_num)
    simp [dotProduct] at h0 h1
    funext l
    fin_cases l
    simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    linarith
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ l => ?_⟩, ?_⟩, ?_⟩, fun p w h => ?_, fun p w h => ?_,
    ?_, ?_, ?_, ?_⟩
  · fin_cases l; norm_num
  · fin_cases l; norm_num
  · funext l; fin_cases l; simp [ex16D2Economy, PrefEconomy.ofUtility]; norm_num
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have hx'le : a'.x k 0 ≤ 3 / 2 := by
      have h1 := congrFun hc' 0
      have h2 : a'.y () 0 ≤ 0 := hy' () 0
      simp only [ex16D2Economy, PrefEconomy.ofUtility, Finset.univ_unique, Finset.sum_singleton,
        Pi.add_apply, Matrix.cons_val_zero] at h1
      have : k = () := rfl
      subst this
      linarith
    change ex16D2u (a'.x k) ≤ ex16D2u ![1]
    rw [hval1]
    exact hle1 _ hx'le
  · have := hprofit p (h.2.1 ())
    subst this
    have hw : w () = 0 := by
      simpa [ex16D2Economy, PrefEconomy.ofUtility] using h.1
    have hb : (![3] : Fin 1 → ℝ) ∈ budgetSetOn (nonnegOrthant 1) 0 (w ()) :=
      ⟨fun l => by fin_cases l; norm_num, by rw [hw, zero_dotProduct]⟩
    have := (h.2.2.1 ()).2 _ hb
    simp only [ex16D2Economy, PrefEconomy.ofUtility, utilityPref, ex16D2u] at this
    norm_num at this
  · exact h.1 (hprofit p (h.2.2.1 ()))
  · intro y hy z hz α β hα hβ _ l
    have := hy l; have := hz l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · refine Continuous.continuousOn ?_
    unfold ex16D2u
    fun_prop
  · intro x _ y hy z hz α β hα hβ hαβ
    refine ⟨?_, ?_⟩
    · intro l
      have := hy.1 l; have := hz.1 l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · have hyx : ex16D2u x ≤ ex16D2u y := hy.2
      have hzx : ex16D2u x ≤ ex16D2u z := hz.2
      change ex16D2u x ≤ ex16D2u (α • y + β • z)
      have hcomb : min (y 0) (z 0) ≤ (α • y + β • z) 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hy' : y 0 = α * y 0 + β * y 0 := by rw [← add_mul, hαβ, one_mul]
        have hz' : z 0 = α * z 0 + β * z 0 := by rw [← add_mul, hαβ, one_mul]
        rcases le_total (y 0) (z 0) with h | h
        · rw [min_eq_left h]; nlinarith [mul_le_mul_of_nonneg_left h hβ]
        · rw [min_eq_right h]; nlinarith [mul_le_mul_of_nonneg_left h hα]
      rcases le_total (y 0) (z 0) with h | h
      · rw [min_eq_left h] at hcomb
        exact hyx.trans (hmono hcomb)
      · rw [min_eq_right h] at hcomb
        exact hzx.trans (hmono hcomb)
  · intro hlns
    obtain ⟨y, -, hd, hs⟩ := hlns ![1] (fun l => by fin_cases l; norm_num) (1 / 2)
      (by norm_num)
    apply hs.2
    have hy0 : y 0 ≤ 3 / 2 := by
      have := abs_sub_le_euclidDist y ![1] 0
      have h2 := (abs_le.mp (this.trans hd)).2
      simp only [Matrix.cons_val_zero] at h2
      linarith
    change ex16D2u y ≤ ex16D2u ![1]
    rw [hval1]
    exact hle1 _ hy0

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# When is a quasiequilibrium an equilibrium? (MWG Section 16.D, pp. 554-556)

* **Proposition 16.D.2** (the cheaper consumption argument) and footnotes 6-8.
* **Proposition 16.D.3**: with convex consumption sets containing `0`, continuous preferences and
  wealth levels `w ≫ 0`, a price quasiequilibrium with transfers is a price equilibrium with
  transfers. The proof uses the standing local nonsatiation assumption of p. 552 (through
  footnote 3, `p·x*ᵢ = wᵢ`); without it the proposition is false
  (`proposition_16_D_3_needs_lns`, correction 2).
* **Figure 16.D.2** (Figure 15.B.10(a)): a Pareto optimal allocation of an Edgeworth box that is a
  price quasiequilibrium with transfers only at `p = (1, 0)`, where consumer 1's wealth is `0`,
  and is not a price equilibrium with transfers for any prices.
* The small type of p. 556: free disposal forces `p ≥ 0` (footnote 9); in a pure exchange economy
  with `X_i = ℝ^L₊` and continuous locally nonsatiated preferences, a quasiequilibrium with
  `x*ᵢ ≫ 0` for all `i` is an equilibrium; with strongly monotone preferences and `ω̄ ≫ 0`, every
  quasiequilibrium has `p ≫ 0` and is an equilibrium.
* **Exercise 16.D.3**: the same with production, when `∑ⱼ ŷⱼ + ω̄ ≫ 0` for some `ŷⱼ ∈ Yⱼ`.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Proposition 16.D.2** (MWG, p. 555). Let `X` be convex and `≿` rational and continuous on
`X`, `x* ∈ X`, and suppose `x ≻ x*` implies `p·x ≥ w`. If there is a cheaper consumption
`x' ∈ X` with `p·x' < w`, then `x ≻ x*` implies `p·x > w`. -/
theorem proposition_16_D_2 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (hc : PrefContinuous X r) {xs : Fin L → ℝ}
    (hxs : xs ∈ X) {p : Fin L → ℝ} {w : ℝ} (h : ∀ x ∈ X, Strict r x xs → w ≤ p ⬝ᵥ x)
    {x' : Fin L → ℝ} (hx' : x' ∈ X) (hcheap : p ⬝ᵥ x' < w) :
    ∀ x ∈ X, Strict r x xs → w < p ⬝ᵥ x := by
  intro x hx hs
  rcases (h x hx hs).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- the points `zₙ = (1 - tₙ)x + tₙx'`, `tₙ = 1/(n+1)`, are cheaper than `w` and tend to `x`
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => by
    rw [ht, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set z : ℕ → Fin L → ℝ := fun n => (1 - t n) • x + t n • x' with hz
  have hzX : ∀ n, z n ∈ X := fun n => hX hx hx' (by linarith [ht1 n]) (ht0 n).le (by ring)
  have hzp : ∀ n, p ⬝ᵥ z n < w := by
    intro n
    simp only [hz, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [← heq]
    nlinarith [ht0 n]
  have hznot : ∀ n, r xs (z n) := by
    intro n
    rcases hr.1 xs hxs (z n) (hzX n) with h1 | h1
    · exact h1
    · by_contra h2
      have := h (z n) (hzX n) ⟨h1, h2⟩
      linarith [hzp n]
  have htt : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hzt : Tendsto z atTop (𝓝 x) := by
    have hcont : Continuous fun s : ℝ => (1 - s) • x + s • x' := by fun_prop
    have := (hcont.tendsto 0).comp htt
    have h2 : (1 - 0 : ℝ) • x + (0 : ℝ) • x' = x := by simp
    rw [h2] at this
    exact this
  have := hc (fun _ => xs) z xs x (fun _ => hxs) hzX hxs hx hznot tendsto_const_nhds hzt
  exact hs.2 this

/-- A bundle that is affordable and such that everything strictly preferred costs more than the
wealth is maximal in the budget set (completeness is used). -/
theorem isMaximalFor_of_strict_gt {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {p xs : Fin L → ℝ} {w : ℝ} (hxs : xs ∈ X) (hb : p ⬝ᵥ xs ≤ w)
    (h : ∀ x ∈ X, Strict r x xs → w < p ⬝ᵥ x) : IsMaximalFor r (budgetSetOn X p w) xs := by
  refine ⟨⟨hxs, hb⟩, fun x hx => ?_⟩
  rcases hr.1 xs hxs x hx.1 with h1 | h1
  · exact h1
  · by_contra h2
    exact absurd hx.2 (not_le.mpr (h x hx.1 ⟨h1, h2⟩))

/-- **Footnote 6** (MWG, p. 555). If `≿` is locally nonsatiated, rational and continuous on the
convex set `X` and there is a cheaper consumption (`p·x' < p·x*`), then `x*` minimizes expenditure
on `{x ∈ X : x ≿ x*}` if and only if it is maximal for `≿` in `{x ∈ X : p·x ≤ p·x*}`. -/
theorem footnote_6 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (hc : PrefContinuous X r)
    (hlns : LocallyNonsatiated X r) {xs : Fin L → ℝ} (hxs : xs ∈ X) {p x' : Fin L → ℝ}
    (hx' : x' ∈ X) (hcheap : p ⬝ᵥ x' < p ⬝ᵥ xs) :
    (∀ x ∈ X, r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) ↔ IsMaximalFor r (budgetSetOn X p (p ⬝ᵥ xs)) xs := by
  constructor
  · intro h
    refine isMaximalFor_of_strict_gt hr hxs le_rfl ?_
    exact proposition_16_D_2 hX hr hc hxs (fun x hx hs => h x hx hs.1) hx' hcheap
  · intro h x hx hpref
    exact exercise_16_C_2 hlns hr.2 h hx hpref

/-- **Footnote 7** (MWG, p. 555). On a convex `X`, for a bundle `x* ∈ X` with `p·x* ≤ w` (for
instance the Walrasian demand `x(p, w)`), there is a cheaper consumption for `(p, w)` if and only
if there are cheaper consumptions arbitrarily close to `x*` (the locally cheaper consumption
condition of Appendix A of Chapter 3). -/
theorem footnote_7 {X : Set (Fin L → ℝ)} (hX : Convex ℝ X) {p xs : Fin L → ℝ} {w : ℝ}
    (hxs : xs ∈ X) (hb : p ⬝ᵥ xs ≤ w) :
    (∃ x' ∈ X, p ⬝ᵥ x' < w) ↔
      ∀ ε : ℝ, 0 < ε → ∃ x' ∈ X, euclidDist x' xs ≤ ε ∧ p ⬝ᵥ x' < w := by
  constructor
  · rintro ⟨x', hx', hlt⟩ ε hε
    set α := min (1 / 2) (ε / (euclidDist x' xs + 1)) with hα
    have hd0 := euclidDist_nonneg x' xs
    have hα0 : 0 < α := lt_min (by norm_num) (div_pos hε (by linarith))
    have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
    refine ⟨α • x' + (1 - α) • xs, hX hx' hxs hα0.le (by linarith) (by ring), ?_, ?_⟩
    · rw [euclidDist_segment hα0.le]
      calc α * euclidDist x' xs ≤ ε / (euclidDist x' xs + 1) * (euclidDist x' xs + 1) :=
            mul_le_mul (min_le_right _ _) (by linarith) hd0 (by positivity)
        _ = ε := div_mul_cancel₀ ε (by linarith)
    · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
  · intro h
    obtain ⟨x', hx', -, hlt⟩ := h 1 one_pos
    exact ⟨x', hx', hlt⟩

/-- **Footnote 8** (MWG, p. 555). Proposition 16.D.2 generalizes Proposition 3.E.1(ii): on
`X = ℝ^L₊` with wealth `w > 0` the bundle `0` is a cheaper consumption, so (without local
nonsatiation and without `w = p·x*`) "`x ≻ x*` implies `p·x ≥ w`" gives "`x ≻ x*` implies
`p·x > w`". -/
theorem footnote_8 {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn (nonnegOrthant L) r)
    (hc : PrefContinuous (nonnegOrthant L) r) {xs : Fin L → ℝ} (hxs : xs ∈ nonnegOrthant L)
    {p : Fin L → ℝ} {w : ℝ} (hw : 0 < w)
    (h : ∀ x ∈ nonnegOrthant L, Strict r x xs → w ≤ p ⬝ᵥ x) :
    ∀ x ∈ nonnegOrthant L, Strict r x xs → w < p ⬝ᵥ x :=
  proposition_16_D_2 (convex_nonnegOrthant L) hr hc hxs h (x' := 0) (fun _ => le_rfl)
    (by rw [dotProduct_zero]; exact hw)

/-- **Proposition 16.D.3** (MWG, p. 555). Suppose every `Xᵢ` is convex with `0 ∈ Xᵢ` and every
`≿ᵢ` is rational, continuous and (the standing assumption of p. 552) locally nonsatiated. Then
any price quasiequilibrium with transfers with wealth levels `w ≫ 0` is a price equilibrium with
transfers. -/
theorem proposition_16_D_3 {E : PrefEconomy ι κ L} (hX : ∀ i, Convex ℝ (E.X i))
    (h0 : ∀ i, (0 : Fin L → ℝ) ∈ E.X i) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceQuasiEqmWithTransfers a p w)
    (hw : ∀ i, 0 < w i) : E.IsPriceEqmWithTransfers a p w := by
  have hweq := h.wealth_eq hlns
  refine ⟨h.2.1, h.2.2.1, fun i => ?_, h.2.2.2.2⟩
  refine isMaximalFor_of_strict_gt (hr i) (h.2.2.2.1 i).1 (hweq i).le ?_
  exact proposition_16_D_2 (hX i) (hr i) (hc i) (h.2.2.2.1 i).1 (h.2.2.2.1 i).2 (h0 i)
    (by rw [dotProduct_zero]; exact hw i)

/-- The economy of the counterexample to Proposition 16.D.3 without local nonsatiation: two
consumers on `ℝ₊` indifferent between all bundles, one disposal firm, `ω̄ = 2`. -/
def satiatedEconomy : PrefEconomy (Fin 2) Unit 1 where
  X := fun _ => nonnegOrthant 1
  pref := fun _ _ _ => True
  Y := fun _ => nonposOrthant 1
  ω := ![2]

/-- **Proposition 16.D.3** (MWG, p. 555), correction 2: the standing assumption of local
nonsatiation (footnote 3, p. 552) is needed. In `satiatedEconomy` (convex consumption sets
containing `0`, rational continuous preferences), `x* = (1, 1)`, `y* = 0`, `p = 1` and wealth
levels `w = (1/2, 3/2) ≫ 0` form a price quasiequilibrium with transfers that is not a price
equilibrium with transfers (consumer 1 cannot afford `x*₁`). -/
theorem proposition_16_D_3_needs_lns :
    (∀ i, Convex ℝ (satiatedEconomy.X i)) ∧ (∀ i, (0 : Fin 1 → ℝ) ∈ satiatedEconomy.X i) ∧
      (∀ i, RationalOn (satiatedEconomy.X i) (satiatedEconomy.pref i)) ∧
      (∀ i, PrefContinuous (satiatedEconomy.X i) (satiatedEconomy.pref i)) ∧
      satiatedEconomy.IsPriceQuasiEqmWithTransfers ⟨fun _ => ![1], fun _ => 0⟩ ![1]
        ![1 / 2, 3 / 2] ∧
      ¬ satiatedEconomy.IsPriceEqmWithTransfers ⟨fun _ => ![1], fun _ => 0⟩ ![1]
        ![1 / 2, 3 / 2] := by
  refine ⟨fun _ => convex_nonnegOrthant 1, fun _ _ => le_rfl,
    fun _ => ⟨fun _ _ _ _ => Or.inl trivial, fun _ _ _ _ _ _ _ _ => trivial⟩,
    fun _ => fun _ _ _ _ _ _ _ _ _ _ _ => trivial, ⟨?_, ?_, fun _ => ?_, fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · simp [satiatedEconomy, Fin.sum_univ_two, dotProduct]
    norm_num
  · exact zero_mem_supply_nonpos (fun l => by fin_cases l; norm_num)
  · intro l; fin_cases l; norm_num
  · exact fun _ _ hs => absurd trivial hs.2
  · funext l
    fin_cases l
    simp [satiatedEconomy]
  · intro h
    have := (h.2.2.1 0).1.2
    simp [dotProduct] at this
    norm_num at this

/-- **Footnote 9** (MWG, p. 556). With the free disposal technology, profit maximization forces
`p ≥ 0` (otherwise disposing of a good with negative price raises profits). -/
theorem footnote_9 {p y : Fin L → ℝ} (h : y ∈ supply (nonposOrthant L) p) : ∀ l, 0 ≤ p l := by
  intro l
  by_contra hneg
  push Not at hneg
  have hmem : y - Pi.single l 1 ∈ nonposOrthant L := by
    intro k
    have := h.1 k
    by_cases hk : k = l
    · subst hk; simp; linarith
    · simp [hk]; linarith
  have := h.2 _ hmem
  rw [dotProduct_sub] at this
  simp at this
  linarith

/-- A nonnegative nonzero price vector gives positive value to a strictly positive bundle. -/
theorem dotProduct_pos_of_nonneg_ne_zero {p x : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hp0 : p ≠ 0)
    (hx : ∀ l, 0 < x l) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ : ∃ l, p l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hp0 (funext hall)
  have hpos : 0 < p l * x l := mul_pos (lt_of_le_of_ne (hp l) (Ne.symm hl)) (hx l)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => p k * x k)
    (fun k _ => mul_nonneg (hp k) (hx k).le) (Finset.mem_univ l))

/-- **Section 16.D** (MWG, p. 556). In a pure exchange economy (with at least one firm) where
`Xᵢ = ℝ^L₊` and preferences are rational, continuous and locally nonsatiated, every price
quasiequilibrium with transfers in which `x*ᵢ ≫ 0` for all `i` is a price equilibrium with
transfers (`p ≥ 0` by free disposal, so `wᵢ = p·x*ᵢ > 0`). -/
theorem pureExchange_quasiEqm_isPriceEqm_of_interior [Nonempty κ] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceQuasiEqmWithTransfers a p w)
    (hint : ∀ i l, 0 < a.x i l) : E.IsPriceEqmWithTransfers a p w := by
  obtain ⟨j⟩ := ‹Nonempty κ›
  have hp : ∀ l, 0 ≤ p l := footnote_9 (hpe j ▸ h.2.2.1 j)
  refine proposition_16_D_3 (fun i => hX i ▸ convex_nonnegOrthant L)
    (fun i => by rw [hX i]; exact fun _ => le_rfl) hr hc hlns h fun i => ?_
  rw [← h.wealth_eq hlns i]
  exact dotProduct_pos_of_nonneg_ne_zero hp h.1 (hint i)

/-- **Exercise 16.D.3** (MWG, p. 575). Suppose `Xᵢ = ℝ^L₊` and preferences are rational,
continuous and strongly monotone (`I > 0`), and a strictly positive aggregate production is
possible: `∑ⱼ ŷⱼ + ω̄ ≫ 0` for some `ŷⱼ ∈ Yⱼ`. Then every price quasiequilibrium with transfers is
a price equilibrium with transfers, and its prices are strictly positive. -/
theorem exercise_16_D_3 [Nonempty ι] {E : PrefEconomy ι κ L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i))
    {yh : κ → Fin L → ℝ} (hyh : ∀ j, yh j ∈ E.Y j) (hpos : ∀ l, 0 < (∑ j, yh j + E.ω) l)
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    E.IsPriceEqmWithTransfers a p w ∧ StrictlyPositive p := by
  classical
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      exact absurd (funext fun l => l.elim0) h.1
    · exact h0
  have hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i) := fun i =>
    hX i ▸ exercise_3_B_1b_orthant hL (exercise_3_B_1a hL (hmono i))
  have hweq := h.wealth_eq hlns
  have hxX : ∀ i, a.x i ∈ nonnegOrthant L := fun i => hX i ▸ (h.2.2.2.1 i).1
  -- adding one unit of good `l` is strictly better
  have hbetter : ∀ i l, Strict (E.pref i) (a.x i + Pi.single l 1) (a.x i) ∧
      a.x i + Pi.single l 1 ∈ E.X i := by
    intro i l
    have hmem : a.x i + Pi.single l 1 ∈ nonnegOrthant L := fun k => by
      have := hxX i k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]; linarith
    refine ⟨hmono i _ (hxX i) _ hmem (fun k => ?_) ?_, hX i ▸ hmem⟩
    · by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    · intro heq
      have := congrFun heq l
      simp at this
  have hcost : ∀ i l, p ⬝ᵥ (a.x i + Pi.single l 1) = w i + p l := by
    intro i l
    rw [dotProduct_add, hweq i]
    simp
  -- `p ≥ 0`
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hp : ∀ l, 0 ≤ p l := by
    intro l
    have := (h.2.2.2.1 i₀).2 _ (hbetter i₀ l).2 (hbetter i₀ l).1
    rw [hcost] at this
    linarith
  -- some consumer has positive wealth
  have hsum : 0 < ∑ i, w i := by
    rw [h.2.1]
    have h1 : ∑ j, p ⬝ᵥ yh j ≤ ∑ j, p ⬝ᵥ a.y j :=
      Finset.sum_le_sum fun j _ => (h.2.2.1 j).2 (yh j) (hyh j)
    have h2 := dotProduct_pos_of_nonneg_ne_zero hp h.1 hpos
    rw [dotProduct_add, dotProduct_finset_sum] at h2
    linarith
  obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < w i := by
    by_contra hall
    push Not at hall
    exact absurd (Finset.sum_nonpos fun i _ => hall i) (not_le.mpr hsum)
  have hstrict : ∀ i, 0 < w i → ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → w i < p ⬝ᵥ x :=
    fun i hwi => proposition_16_D_2 (hX i ▸ convex_nonnegOrthant L) (hr i) (hc i)
      (h.2.2.2.1 i).1 (h.2.2.2.1 i).2 (x' := 0) (by rw [hX i]; exact fun _ => le_rfl)
      (by rw [dotProduct_zero]; exact hwi)
  -- `p ≫ 0`
  have hpp : StrictlyPositive p := by
    intro l
    rcases (hp l).lt_or_eq with hl | hl
    · exact hl
    · exfalso
      have := hstrict i₁ hi₁ _ (hbetter i₁ l).2 (hbetter i₁ l).1
      rw [hcost, ← hl] at this
      linarith
  refine ⟨⟨h.2.1, h.2.2.1, fun i => ?_, h.2.2.2.2⟩, hpp⟩
  refine isMaximalFor_of_strict_gt (hr i) (h.2.2.2.1 i).1 (hweq i).le ?_
  rcases lt_or_ge 0 (w i) with hwi | hwi
  · exact hstrict i hwi
  · -- zero wealth: `x*ᵢ = 0`, and everything strictly preferred is nonzero
    have hnn : 0 ≤ p ⬝ᵥ a.x i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (hxX i l)
    have hw0 : w i = 0 := le_antisymm hwi (hweq i ▸ hnn)
    have hx0 : a.x i = 0 := by
      have h1 : p ⬝ᵥ a.x i = 0 := by rw [hweq i, hw0]
      funext l
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hp k) (hxX i k))).mp
        h1 l (Finset.mem_univ l)
      rcases mul_eq_zero.mp this with h2 | h2
      · exact absurd h2 (hpp l).ne'
      · simpa using h2
    intro x hx hs
    rw [hw0]
    have hxn : x ∈ nonnegOrthant L := hX i ▸ hx
    have hne : x ≠ 0 := by
      rintro rfl
      rw [hx0] at hs
      exact hs.2 hs.1
    rw [dotProduct_comm]
    exact dotProduct_pos_of_nonneg_ne_zero hxn hne hpp

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A quasiequilibrium that is not an equilibrium (MWG Figure 16.D.2, p. 554)

The Edgeworth box of Figure 15.B.10(a), reproduced in Figure 16.D.2, made concrete: `ω̄ = (1, 1)`,
consumer 1 has `u₁(x) = √x₁ + x₂` (an infinite marginal rate of substitution on the axis
`x₁ = 0`), consumer 2 has `u₂(x) = x₁`, and there is one disposal firm.

* `x* = ((0, 1), (1, 0))` is Pareto optimal, and with `p = (1, 0)` and wealth levels
  `w = (0, 1)` it is a price quasiequilibrium with transfers (`figure_16_D_2_quasi`).
* Normalizing `p₁ = 1`, `p = (1, 0)` is the only supporting price vector, and consumer 1's wealth
  is `0` (`figure_16_D_2_unique_price`).
* `x*₁` satisfies condition (ii) of Definition 16.D.1 but is not maximal in consumer 1's budget
  set `{x : x₁ = 0}`; in fact `x*` is not a price equilibrium with transfers for any prices and
  wealth levels (`figure_16_D_2_not_eqm`). There is no cheaper consumption for `(p, w₁) = (p, 0)`,
  as Proposition 16.D.2 requires.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {L : ℕ}

/-- The Euclidean distance moved by adding `c` units of one good is `|c|`. -/
theorem euclidDist_add_single (x : Fin L → ℝ) (l : Fin L) (c : ℝ) :
    euclidDist (x + Pi.single l c) x = |c| := by
  unfold euclidDist
  have : ∀ k, ((x + (Pi.single l c : Fin L → ℝ)) k - x k) ^ 2 =
      (Pi.single l c : Fin L → ℝ) k ^ 2 := fun k => by
    simp only [Pi.add_apply, add_sub_cancel_left]
  simp only [this]
  rw [Finset.sum_eq_single l (fun k _ hk => by simp [hk]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq_eq_abs]

/-- A utility on `ℝ^L₊` that strictly increases in good `l` everywhere is locally nonsatiated. -/
theorem lns_of_strictMono_coord {u : (Fin L → ℝ) → ℝ} (l : Fin L)
    (h : ∀ x ∈ nonnegOrthant L, ∀ c : ℝ, 0 < c → u x < u (x + Pi.single l c)) :
    LocallyNonsatiated (nonnegOrthant L) (utilityPref u) := by
  intro x hx ε hε
  refine ⟨x + Pi.single l ε, fun k => ?_, ?_, ?_, ?_⟩
  · have := hx k
    by_cases hk : k = l
    · subst hk; simp; linarith
    · simp [hk]; linarith
  · rw [euclidDist_add_single, abs_of_pos hε]
  · exact (h x hx ε hε).le
  · exact not_le.mpr (h x hx ε hε)

/-- Consumer 1 of Figure 16.D.2: `u₁(x) = √x₁ + x₂`. -/
noncomputable def fig16D2u1 (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + x 1

/-- Consumer 2 of Figure 16.D.2: `u₂(x) = x₁`. -/
def fig16D2u2 (x : Fin 2 → ℝ) : ℝ := x 0

/-- **Figure 16.D.2** (MWG, p. 555). The Edgeworth box economy with `ω̄ = (1, 1)`. -/
noncomputable def fig16D2Economy : PrefEconomy (Fin 2) Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) ![fig16D2u1, fig16D2u2]
    (fun _ => nonposOrthant 2) ![1, 1]

/-- The allocation `x*` of Figure 16.D.2: `x*₁ = (0, 1)`, `x*₂ = (1, 0)`, no production. -/
def fig16D2Alloc : Allocation (Fin 2) Unit 2 := ⟨![![0, 1], ![1, 0]], fun _ => 0⟩

/-- Both consumers of Figure 16.D.2 are locally nonsatiated on `ℝ²₊`. -/
theorem fig16D2_lns : ∀ i, LocallyNonsatiated (fig16D2Economy.X i) (fig16D2Economy.pref i) := by
  intro i
  fin_cases i
  · refine lns_of_strictMono_coord 1 fun x _ c hc => ?_
    simp [fig16D2u1]
    linarith
  · refine lns_of_strictMono_coord 0 fun x _ c hc => ?_
    simp [fig16D2u2]
    linarith

/-- **Figure 16.D.2** (MWG, pp. 554-555). `x*` is Pareto optimal, and with `p = (1, 0)` and
`w = (0, 1)` it is a price quasiequilibrium with transfers but not a price equilibrium with
transfers: `(0, 2)` is affordable for consumer 1 and better than `x*₁`. -/
theorem figure_16_D_2_quasi :
    fig16D2Economy.IsParetoOptimal fig16D2Alloc ∧
      fig16D2Economy.IsPriceQuasiEqmWithTransfers fig16D2Alloc ![1, 0] ![0, 1] ∧
      ¬ fig16D2Economy.IsPriceEqmWithTransfers fig16D2Alloc ![1, 0] ![0, 1] := by
  have hdot : ∀ x : Fin 2 → ℝ, (![1, 0] : Fin 2 → ℝ) ⬝ᵥ x = x 0 := fun x => by
    rw [dot_two]; simp
  have hfeas : fig16D2Economy.IsFeasible fig16D2Alloc := by
    refine ⟨⟨fun i => ?_, fun _ => fun _ => le_rfl⟩, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp [fig16D2Alloc]
    · funext l
      fin_cases l <;> simp [fig16D2Economy, PrefEconomy.ofUtility, fig16D2Alloc]
  refine ⟨⟨hfeas, ?_⟩, ⟨?_, ?_, fun _ => ?_, fun i => ⟨hfeas.1.1 i, fun x hx hs => ?_⟩,
    hfeas.2⟩, fun h => ?_⟩
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    have hx0 : ∀ i l, 0 ≤ a'.x i l := fun i => hx' i
    have hy0 : ∀ l, a'.y () l ≤ 0 := hy' ()
    have hc0 := congrFun hc' 0
    have hc1 := congrFun hc' 1
    simp [fig16D2Economy, PrefEconomy.ofUtility, Fin.sum_univ_two] at hc0 hc1
    have h2 : 1 ≤ a'.x 1 0 := by
      have := hle 1
      simpa [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2u2, fig16D2Alloc]
        using this
    have hy00 := hy0 0
    have hy01 := hy0 1
    have h10 : a'.x 0 0 = 0 := by linarith [hx0 0 0, hx0 1 1]
    apply hk.2
    fin_cases k
    · simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc]
      simp [fig16D2u1, h10]
      linarith [hx0 1 1]
    · simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc]
      simp [fig16D2u2]
      linarith [hx0 0 0]
  · intro h
    have := congrFun h 0
    simp at this
  · simp [fig16D2Economy, PrefEconomy.ofUtility, Fin.sum_univ_two, hdot, fig16D2Alloc]
  · exact zero_mem_supply_nonpos (fun l => by fin_cases l <;> simp)
  · rw [hdot]
    have hxn : ∀ l, 0 ≤ x l := hx
    fin_cases i
    · simpa using hxn 0
    · have := hs.2
      simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
      simp [fig16D2u2] at this
      simp
      linarith
  · have hb : (![0, 2] : Fin 2 → ℝ) ∈ budgetSetOn (fig16D2Economy.X 0) ![1, 0] (![0, 1] 0) :=
      ⟨fun l => by fin_cases l <;> simp, by rw [hdot]; simp⟩
    have := (h.2.2.1 0).2 _ hb
    simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
    simp [fig16D2u1] at this

/-- **Figure 16.D.2** (MWG, p. 554). Every price quasiequilibrium with transfers supporting `x*`
has `p₂ = 0` (so `p = (1, 0)` after normalizing `p₁ = 1`) and gives consumer 1 wealth `w₁ = 0`. -/
theorem figure_16_D_2_unique_price {p : Fin 2 → ℝ} {w : Fin 2 → ℝ}
    (h : fig16D2Economy.IsPriceQuasiEqmWithTransfers fig16D2Alloc p w) :
    p 1 = 0 ∧ w 0 = 0 ∧ 0 < p 0 := by
  have hp : ∀ l, 0 ≤ p l := footnote_9 (h.2.2.1 ())
  have hw := h.wealth_eq fig16D2_lns
  have hw0 : w 0 = p 1 := by
    rw [← hw 0, dot_two]; simp [fig16D2Alloc]
  have hp1 : p 1 = 0 := by
    by_contra hne
    have hpos : 0 < p 1 := lt_of_le_of_ne (hp 1) (Ne.symm hne)
    set t := min 1 (p 1 / (4 * (p 0 + 1))) with ht
    have hp0 := hp 0
    have ht0 : 0 < t := lt_min one_pos (div_pos hpos (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htle : t ≤ p 1 / (4 * (p 0 + 1)) := min_le_right _ _
    have hmem : (![t ^ 2, 1 - t / 2] : Fin 2 → ℝ) ∈ fig16D2Economy.X 0 := fun l => by
      fin_cases l
      · change 0 ≤ t ^ 2; positivity
      · change 0 ≤ 1 - t / 2; linarith
    have hs : Strict (fig16D2Economy.pref 0) ![t ^ 2, 1 - t / 2] (fig16D2Alloc.x 0) := by
      simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc, Strict]
      simp only [Matrix.cons_val_zero, fig16D2u1, Matrix.cons_val_one, Real.sqrt_zero]
      rw [Real.sqrt_sq ht0.le]
      constructor <;> linarith
    have := (h.2.2.2.1 0).2 _ hmem hs
    rw [hw0, dot_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    -- `p₂ t / 2 ≤ p₁ t²`, so `p₂ ≤ 2 p₁ t < p₂`
    have h1 : p 1 * t / 2 ≤ p 0 * t ^ 2 := by nlinarith
    have h2 : p 1 / 2 ≤ p 0 * t := by
      by_contra hlt
      push Not at hlt
      nlinarith [mul_lt_mul_of_pos_right hlt ht0]
    have h3 : p 0 * t ≤ p 0 * (p 1 / (4 * (p 0 + 1))) := mul_le_mul_of_nonneg_left htle hp0
    have h4 : p 0 * (p 1 / (4 * (p 0 + 1))) < p 1 / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  refine ⟨hp1, by rw [hw0, hp1], ?_⟩
  rcases (hp 0).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    apply h.1
    funext l
    fin_cases l
    · simp [← h0]
    · simp [hp1]

/-- **Figure 16.D.2** (MWG, p. 554). `x*` is not a price equilibrium with transfers for any price
vector and wealth levels. -/
theorem figure_16_D_2_not_eqm (p w : Fin 2 → ℝ) :
    ¬ fig16D2Economy.IsPriceEqmWithTransfers fig16D2Alloc p w := by
  intro h
  have hq := h.isPriceQuasiEqm_of_lns fig16D2_lns
  obtain ⟨hp1, hw0, -⟩ := figure_16_D_2_unique_price hq
  have hb : (![0, 2] : Fin 2 → ℝ) ∈ budgetSetOn (fig16D2Economy.X 0) p (w 0) :=
    ⟨fun l => by fin_cases l <;> simp, by rw [dot_two, hw0, hp1]; simp⟩
  have := (h.2.2.1 0).2 _ hb
  simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
  simp [fig16D2u1] at this

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Section 16.D** (MWG, p. 556). In a pure exchange economy with `ω̄ ≫ 0`, `Xᵢ = ℝ^L₊` and
continuous, strongly monotone (rational) preferences (`I ≥ 1`), every price quasiequilibrium with
transfers has `p ≫ 0` and is a price equilibrium with transfers: Exercise 16.D.3 with the
inaction plans `ŷⱼ = 0`. -/
theorem pureExchange_quasiEqm_isPriceEqm_of_strongMono [Nonempty ι] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (hω : ∀ l, 0 < E.ω l)
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    E.IsPriceEqmWithTransfers a p w ∧ StrictlyPositive p :=
  exercise_16_D_3 hX hr hc hmono (yh := fun _ => 0) (fun j => by rw [hpe j]; exact fun _ => le_rfl)
    (fun l => by simpa using hω l) h

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Nonconvex preferences and replication (MWG Section 16.D, pp. 557-558; Exercise 16.D.4)

* **Figures 16.D.4 and 16.D.5**: with the nonconvex preference `u(x) = x₁² + x₂²` and
  `ω = (2, 2)`, the endowment of a one-consumer economy is (trivially) Pareto optimal but not
  supportable by prices; in the two-consumer replica the symmetric allocation is Pareto dominated
  by `x'₁ = ω + (1, -1)`, `x'₂ = ω + (-1, 1)`.
* **Exercise 16.D.4**: in the `r`-fold replica of a pure exchange economy with identical
  consumers (`X = ℝ^L₊`, continuous, strongly monotone, possibly nonconvex preferences,
  endowment `ω ≫ 0`), the symmetric allocation in which every consumer keeps `ω` is either a
  Walrasian equilibrium allocation (for some `p`, for every `r`) or, for all `r` large enough, not
  Pareto optimal. The book has two goods; the proof works for any `L ≥ 1`, without
  differentiability. It separates the convex hull of the strictly preferred trades from the
  open negative orthant; if they meet, a convex combination of preferred trades is `≪ 0`, and
  rounding its weights gives integer multiplicities, i.e. a Pareto improvement in a large replica.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {L : ℕ}

/-- **Exercise 16.D.4** (MWG, p. 575). The `r`-fold replica of a pure exchange economy with
identical consumers: consumption sets `ℝ^L₊`, preference `≿`, one disposal firm and total
endowment `r ω`. -/
def replicaEconomy (R : (Fin L → ℝ) → (Fin L → ℝ) → Prop) (ω : Fin L → ℝ) (r : ℕ) :
    PrefEconomy (Fin r) Unit L where
  X := fun _ => nonnegOrthant L
  pref := fun _ => R
  Y := fun _ => nonposOrthant L
  ω := (r : ℝ) • ω

/-- The symmetric allocation in which every consumer consumes her endowment `ω`. -/
def symmetricAlloc (ω : Fin L → ℝ) (r : ℕ) : Allocation (Fin r) Unit L :=
  ⟨fun _ => ω, fun _ => 0⟩

/-- A strictly preferred bundle stays strictly preferred along any sequence converging to it
(continuity and completeness of `≿`): some term of the sequence is strictly preferred. -/
theorem exists_strict_of_tendsto {X : Set (Fin L → ℝ)} {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X R) (hc : PrefContinuous X R) {x z : Fin L → ℝ} (hx : x ∈ X) (hz : z ∈ X)
    (hs : Strict R x z) {zs : ℕ → Fin L → ℝ} (hzs : ∀ n, zs n ∈ X)
    (ht : Tendsto zs atTop (𝓝 x)) : ∃ n, Strict R (zs n) z := by
  by_contra hall
  push Not at hall
  have hle : ∀ n, R z (zs n) := fun n => by
    rcases hr.1 z hz (zs n) (hzs n) with h | h
    · exact h
    · by_contra h'
      exact hall n ⟨h, h'⟩
  exact hs.2 (hc (fun _ => z) zs z x (fun _ => hz) hzs hz hx hle tendsto_const_nhds ht)

/-- Removing a small amount `δ/(n+1)` of a good held in positive quantity keeps a strictly
preferred bundle strictly preferred for some `n`. -/
theorem exists_strict_sub_single {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) R) (hc : PrefContinuous (nonnegOrthant L) R)
    {x z : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) (hs : Strict R x z)
    {m : Fin L} (hm : 0 < x m) :
    ∃ δ : ℝ, 0 < δ ∧ x - Pi.single m δ ∈ nonnegOrthant L ∧ Strict R (x - Pi.single m δ) z := by
  have hmem : ∀ n : ℕ, x - Pi.single m (x m / ((n : ℝ) + 1)) ∈ nonnegOrthant L := by
    intro n k
    by_cases hk : k = m
    · subst hk
      rw [Pi.sub_apply, Pi.single_eq_same]
      have : x k / ((n : ℝ) + 1) ≤ x k := div_le_self hm.le (by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      linarith
    · rw [Pi.sub_apply, Pi.single_eq_of_ne hk, sub_zero]
      exact hx k
  have ht : Tendsto (fun n : ℕ => x - Pi.single m (x m / ((n : ℝ) + 1))) atTop (𝓝 x) := by
    have h1 : Tendsto (fun n : ℕ => x m / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (x m)
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [mul_one_div]
    have hsc : Continuous fun s : ℝ => (Pi.single m s : Fin L → ℝ) :=
      continuous_pi fun k => by
        simp only [Pi.single_apply]
        split_ifs <;> fun_prop
    have hcont : Continuous fun s : ℝ => x - Pi.single m s := continuous_const.sub hsc
    have := (hcont.tendsto 0).comp h1
    rw [Pi.single_zero, sub_zero] at this
    exact this
  obtain ⟨n, hn⟩ := exists_strict_of_tendsto hr hc hx hz hs hmem ht
  exact ⟨x m / ((n : ℝ) + 1), by positivity, hmem n, hn⟩

/-- Rounding the weights of a nonnegative combination that is `≪ 0` down to integers (after
scaling) keeps it `≪ 0`. -/
theorem exists_nat_combination_neg {K : Type*} [Fintype K] (b : K → Fin L → ℝ) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hneg : ∀ l, (∑ k, w k • b k) l < 0) :
    ∃ m : K → ℕ, ∀ l, (∑ k, (m k : ℝ) • b k) l < 0 := by
  -- a scale `N` with `N · (∑ wₖbₖ)_l + ∑ₖ |b_{kl}| < 0` for every good
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l, (N : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| < 0 := by
    have hex : ∀ l, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (n : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| < 0 := by
      intro l
      obtain ⟨N, hN⟩ := exists_nat_gt ((∑ k, |b k l|) / -(∑ k, w k • b k) l)
      refine ⟨N, fun n hn => ?_⟩
      have hn' : (∑ k, |b k l|) / -(∑ k, w k • b k) l < n :=
        lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [div_lt_iff₀ (by linarith [hneg l])] at hn'
      linarith
    choose Nl hNl using hex
    refine ⟨Finset.univ.sup Nl, fun l => hNl l _ (Finset.le_sup (Finset.mem_univ l))⟩
  refine ⟨fun k => ⌊(N : ℝ) * w k⌋₊, fun l => ?_⟩
  have hterm : ∀ k, (⌊(N : ℝ) * w k⌋₊ : ℝ) * b k l ≤ (N : ℝ) * w k * b k l + |b k l| := by
    intro k
    have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hw k))
    have h2 := Nat.lt_floor_add_one ((N : ℝ) * w k)
    have h3 : 0 ≤ (N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊ := by linarith
    have h4 : (N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊ ≤ 1 := by linarith
    have : ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * (-b k l) ≤ |b k l| := by
      calc ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * (-b k l)
          ≤ ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * |b k l| :=
            mul_le_mul_of_nonneg_left (neg_le_abs _) h3
        _ ≤ 1 * |b k l| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
        _ = |b k l| := one_mul _
    nlinarith
  have hsum : (∑ k, (⌊(N : ℝ) * w k⌋₊ : ℝ) • b k) l ≤
      (N : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hterm k
  linarith [hN l]

/-- **Exercise 16.D.4** (MWG, pp. 575-576). In the `r`-fold replica of a pure exchange economy
with identical consumers whose preference on `ℝ^L₊` (`L ≥ 1`) is rational, continuous and strongly
monotone (not necessarily convex), and endowment `ω ≫ 0`: either there is a price vector `p` such
that the symmetric allocation is a price equilibrium with transfers with wealth levels `p·ω` (that
is, a Walrasian equilibrium of the replica in which each consumer owns `ω`) for every `r`, or
there is `r₀` such that the symmetric allocation is not Pareto optimal in every replica with
`r ≥ r₀` consumers. -/
theorem exercise_16_D_4 (hL : 0 < L) {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) R) (hc : PrefContinuous (nonnegOrthant L) R)
    (hmono : PrefStronglyMonotone (nonnegOrthant L) R) {ω : Fin L → ℝ} (hω : ∀ l, 0 < ω l) :
    (∃ p : Fin L → ℝ, ∀ r, (replicaEconomy R ω r).IsPriceEqmWithTransfers (symmetricAlloc ω r) p
      (fun _ => p ⬝ᵥ ω)) ∨
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ¬ (replicaEconomy R ω r).IsParetoOptimal (symmetricAlloc ω r) := by
  classical
  have hωX : ω ∈ nonnegOrthant L := fun l => (hω l).le
  -- the strictly preferred trades
  set B : Set (Fin L → ℝ) := {b | ω + b ∈ nonnegOrthant L ∧ Strict R (ω + b) ω} with hB
  set N : Set (Fin L → ℝ) := {n | ∀ l, n l < 0} with hN
  have hNopen : IsOpen N := by
    have : N = ⋂ l, {n : Fin L → ℝ | n l < 0} := by ext n; simp [hN]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt (continuous_apply l) continuous_const
  have hNconv : Convex ℝ N := by
    intro x hx y hy a b ha hb hab l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx l; have := hy l
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_neg_of_pos_of_neg ha' (hx l), mul_nonpos_of_nonneg_of_nonpos hb (hy l).le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy l
  have hsingle_mem : ∀ (x : Fin L → ℝ) (l : Fin L), x ∈ nonnegOrthant L →
      x + Pi.single l 1 ∈ nonnegOrthant L := by
    intro x l hx k
    by_cases hk : k = l
    · subst hk; simp; linarith [hx k]
    · simpa [hk] using hx k
  have hsingle_strict : ∀ (x : Fin L → ℝ) (l : Fin L), x ∈ nonnegOrthant L →
      Strict R (x + Pi.single l 1) x := by
    intro x l hx
    refine hmono x hx _ (hsingle_mem x l hx) (fun k => ?_) ?_
    · by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    · intro heq
      have := congrFun heq l
      simp at this
  by_cases hdisj : Disjoint N (convexHull ℝ B)
  · -- separation: a price vector `q ≥ 0`, `q ≠ 0`, with `q·b ≥ 0` on the preferred trades
    left
    obtain ⟨f, u, hfN, hfC⟩ := geometric_hahn_banach_open hNconv hNopen (convex_convexHull ℝ B)
      hdisj
    obtain ⟨q, hq⟩ := duality_exists_dot_of_clm f
    have hBne : (Pi.single ⟨0, hL⟩ 1 : Fin L → ℝ) ∈ B :=
      ⟨hsingle_mem ω _ hωX, hsingle_strict ω _ hωX⟩
    have hq0 : ∀ l, 0 ≤ q l := by
      intro l
      by_contra hneg
      push Not at hneg
      set t := max 0 ((u + ∑ k, q k) / -q l) + 1 with ht
      have ht1 : 1 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / -q l)]
      have ht2 : (u + ∑ k, q k) / -q l ≤ t - 1 := by
        linarith [le_max_right 0 ((u + ∑ k, q k) / -q l)]
      have hmem : -Pi.single l t - (fun _ => (1 : ℝ)) ∈ N := by
        intro k
        by_cases hk : k = l
        · subst hk; simp; linarith
        · simp [hk]
      have := hfN _ hmem
      rw [hq, dotProduct_sub, dotProduct_neg] at this
      have hdot1 : q ⬝ᵥ (Pi.single l t : Fin L → ℝ) = q l * t := by simp
      have hdot2 : q ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ k, q k := by simp [dotProduct]
      rw [hdot1, hdot2] at this
      have hql : 0 < -q l := by linarith
      rw [div_le_iff₀ hql] at ht2
      nlinarith
    have hu0 : 0 ≤ u := by
      by_contra hneg
      push Not at hneg
      have hS : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq0 k
      set ε := -u / (∑ k, q k + 1) with hε
      have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
      have := hfN (fun _ => -ε) (fun _ => by linarith)
      rw [hq] at this
      have hdot : q ⬝ᵥ (fun _ => -ε) = -ε * ∑ k, q k := by
        simp [dotProduct, Finset.sum_mul, mul_comm]
      rw [hdot] at this
      have : -ε * ∑ k, q k ≥ u := by
        rw [hε]
        rw [ge_iff_le, neg_div, neg_mul, neg_mul, neg_neg, div_mul_eq_mul_div]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hqB : ∀ b ∈ B, 0 ≤ q ⬝ᵥ b := fun b hb => by
      have := hfC b (subset_convexHull ℝ B hb)
      rw [hq] at this
      linarith
    have hqne : q ≠ 0 := by
      rintro rfl
      have := hfC _ (subset_convexHull ℝ B hBne)
      have h2 := hfN (fun _ => -1) (fun _ => by norm_num)
      rw [hq] at this h2
      simp at this h2
      linarith
    -- `q ≫ 0`
    have hqpos : ∀ l, 0 < q l := by
      intro l
      rcases (hq0 l).lt_or_eq with h | h
      · exact h
      exfalso
      obtain ⟨m, hm⟩ : ∃ m, q m ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hqne (funext hall)
      have hqm : 0 < q m := lt_of_le_of_ne (hq0 m) (Ne.symm hm)
      have hxpos : 0 < (ω + (Pi.single l 1 : Fin L → ℝ)) m := by
        have := hsingle_mem ω l hωX m
        by_cases hml : m = l
        · subst hml; simp; linarith [hω m]
        · simpa [hml] using hω m
      obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single hr hc (hsingle_mem ω l hωX) hωX
        (hsingle_strict ω l hωX) hxpos
      have hb : ω + Pi.single l 1 - Pi.single m δ - ω ∈ B :=
        ⟨by simpa using hmem, by simpa using hs⟩
      have := hqB _ hb
      have hcalc : q ⬝ᵥ (ω + Pi.single l 1 - Pi.single m δ - ω) = q l - q m * δ := by
        simp [dotProduct_sub, dotProduct_add]
        ring
      rw [hcalc, ← h] at this
      nlinarith
    refine ⟨q, fun r => ⟨?_, fun _ => ?_, fun i => ?_, ?_⟩⟩
    · simp [replicaEconomy, symmetricAlloc, dotProduct_smul]
    · exact zero_mem_supply_nonpos hq0
    · refine isMaximalFor_of_strict_gt hr hωX le_rfl fun x hx hs => ?_
      have hb : x - ω ∈ B := ⟨by simpa using hx, by simpa [symmetricAlloc] using hs⟩
      have h1 := hqB _ hb
      rw [dotProduct_sub] at h1
      rcases (sub_nonneg.mp h1).lt_or_eq with h2 | h2
      · exact h2
      exfalso
      -- `x` has a good in positive quantity, which can be reduced
      obtain ⟨m, hm⟩ : ∃ m, 0 < x m := by
        by_contra hall
        push Not at hall
        have hx0 : x = 0 := funext fun m => le_antisymm (hall m) (hx m)
        have : 0 < q ⬝ᵥ ω := dotProduct_pos_of_nonneg_ne_zero hq0 hqne hω
        rw [h2, hx0, dotProduct_zero] at this
        exact lt_irrefl 0 this
      obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single hr hc hx hωX hs hm
      have hb' : x - Pi.single m δ - ω ∈ B :=
        ⟨by simpa using hmem, by simpa [symmetricAlloc] using hs'⟩
      have := hqB _ hb'
      rw [dotProduct_sub, dotProduct_sub, ← h2] at this
      simp at this
      nlinarith [hqpos m]
    · funext l
      simp [replicaEconomy, symmetricAlloc]
  · -- a convex combination of preferred trades is `≪ 0`: integer multiplicities
    right
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨c, hcN, hcC⟩ := hdisj
    obtain ⟨K, hK, z, w, hzB, -, hw, -, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hcC
    obtain ⟨m, hm⟩ := exists_nat_combination_neg z w (fun k => (hw k).le)
      (fun l => by rw [hcomb]; exact hcN l)
    set M := ∑ k, m k with hM
    refine ⟨M, fun r hr0 hpo => ?_⟩
    -- an enumeration of the `M` copies
    have hcard : Fintype.card (Σ k, Fin (m k)) = M := by simp [hM]
    set e : Fin M ≃ Σ k, Fin (m k) := (Fintype.equivFinOfCardEq hcard).symm with he
    set d : Fin L → ℝ := -∑ k, (m k : ℝ) • z k with hd
    have hdpos : ∀ l, 0 < d l := fun l => by
      simp only [hd, Pi.neg_apply]; linarith [hm l]
    have hMpos : 0 < M := by
      by_contra h0
      push Not at h0
      have hm0 : ∀ k, m k = 0 := fun k => by
        have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega
      have := hm ⟨0, hL⟩
      simp [hm0] at this
    have hr1 : 0 < r := lt_of_lt_of_le hMpos hr0
    set φ : ℕ → Fin L → ℝ := fun n => if h : n < M then z (e ⟨n, h⟩).1 else 0 with hφ
    set x' : Fin r → Fin L → ℝ := fun i => ω + φ i + if (i : ℕ) = 0 then d else 0 with hx'
    have hzX : ∀ k, ω + z k ∈ nonnegOrthant L := fun k => (hzB ⟨k, rfl⟩).1
    have hzS : ∀ k, Strict R (ω + z k) ω := fun k => (hzB ⟨k, rfl⟩).2
    have hφX : ∀ n, ω + φ n ∈ nonnegOrthant L := fun n => by
      by_cases h : n < M
      · simp only [hφ, h, ↓reduceDIte]; exact hzX _
      · simp only [hφ, h, ↓reduceDIte, add_zero]; exact hωX
    have hsumφ : ∑ i : Fin r, φ i = -d := by
      rw [Fin.sum_univ_eq_sum_range (fun n => φ n), ← Finset.sum_range_add_sum_Ico _ hr0]
      have h2 : ∑ n ∈ Finset.Ico M r, φ n = 0 :=
        Finset.sum_eq_zero fun n hn => by
          simp only [hφ, not_lt.mpr (Finset.mem_Ico.mp hn).1, ↓reduceDIte]
      rw [h2, add_zero, ← Fin.sum_univ_eq_sum_range (fun n => φ n)]
      have h3 : ∑ i : Fin M, φ i = ∑ i : Fin M, z (e i).1 :=
        Finset.sum_congr rfl fun i _ => by simp [hφ, i.isLt]
      rw [h3, hd, neg_neg, Equiv.sum_comp e (fun σ => z σ.1), Fintype.sum_sigma]
      simp [Nat.cast_smul_eq_nsmul]
    have hx'X : ∀ i, x' i ∈ nonnegOrthant L := by
      intro i l
      have := hφX i l
      simp only [hx', Pi.add_apply] at this ⊢
      split_ifs
      · linarith [hdpos l]
      · simpa using this
    have hφS : ∀ n, n < M → Strict R (ω + φ n) ω := by
      intro n hn
      simp only [hφ, hn, ↓reduceDIte]
      exact hzS _
    have hxR : ∀ i : Fin r, R (x' i) (ω + φ i) := by
      intro i
      by_cases h0 : (i : ℕ) = 0
      · refine (hmono (ω + φ i) (hφX i) (x' i) (hx'X i) (fun l => ?_) ?_).1
        · simp only [hx', h0, ↓reduceIte, Pi.add_apply]
          linarith [hdpos l]
        · intro heq
          have := congrFun heq ⟨0, hL⟩
          simp only [hx', h0, ↓reduceIte, Pi.add_apply] at this
          linarith [hdpos ⟨0, hL⟩]
      · have : x' i = ω + φ i := by simp only [hx', h0, ↓reduceIte, add_zero]
        rw [this]
        exact (hr.1 _ (hφX i) _ (hφX i)).elim id id
    apply hpo.2
    refine ⟨⟨x', fun _ => 0⟩, ⟨⟨hx'X, fun _ => fun _ => le_rfl⟩, ?_⟩, fun i => ?_,
      ⟨0, hr1⟩, ?_⟩
    · change ∑ i, x' i = (r : ℝ) • ω + ∑ _j : Unit, (0 : Fin L → ℝ)
      simp only [hx', Finset.sum_add_distrib, hsumφ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Fintype.card_unit, one_smul, add_zero]
      have : (∑ x : Fin r, if (x : ℕ) = 0 then d else 0) = d := by
        rw [Finset.sum_eq_single (⟨0, hr1⟩ : Fin r)]
        · simp
        · intro i _ hi
          have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          simp [this]
        · simp
      rw [this, neg_add_cancel_right, Nat.cast_smul_eq_nsmul]
    · change R (x' i) ω
      by_cases h : (i : ℕ) < M
      · exact (strict_of_pref_of_strict hr.2 (hx'X i) (hφX i) hωX (hxR i) (hφS i h)).1
      · have hφ0 : φ i = 0 := by simp only [hφ, h, ↓reduceDIte]
        have := hxR i
        rwa [hφ0, add_zero] at this
    · change Strict R (x' ⟨0, hr1⟩) ω
      exact strict_of_pref_of_strict hr.2 (hx'X _) (hφX 0) hωX (hxR ⟨0, hr1⟩) (hφS 0 hMpos)

/-- A preference represented by a utility function is rational. -/
theorem rationalOn_utilityPref (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ) :
    RationalOn X (utilityPref u) :=
  ⟨fun x _ y _ => le_total (u y) (u x), fun _ _ _ _ _ _ hxy hyz => le_trans hyz hxy⟩

/-- A preference represented by a utility function continuous on `X` is continuous on `X`
(Definition 3.C.1). -/
theorem prefContinuous_utilityPref {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u X) : PrefContinuous X (utilityPref u) := by
  intro xs ys x y hxs hys hx hy hle htx hty
  have h1 : Tendsto (fun n => u (xs n)) atTop (𝓝 (u x)) :=
    (hu x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨htx, Eventually.of_forall hxs⟩)
  have h2 : Tendsto (fun n => u (ys n)) atTop (𝓝 (u y)) :=
    (hu y hy).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hty, Eventually.of_forall hys⟩)
  exact le_of_tendsto_of_tendsto' h2 h1 hle

/-- The nonconvex preference of Figures 16.D.4-16.D.6: `u(x) = x₁² + x₂²`. -/
def sqNormU (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `u(x) = x₁² + x₂²` is strongly monotone on `ℝ²₊`. -/
theorem sqNormU_stronglyMonotone :
    PrefStronglyMonotone (nonnegOrthant 2) (utilityPref sqNormU) := by
  intro x hx y _ hxy hne
  have h0 := hxy 0
  have h1 := hxy 1
  have hx0 := hx 0
  have hx1 := hx 1
  have hlt : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra h
    push Not at h
    exact hne (funext fun l => by fin_cases l <;> simp <;> linarith [h.1, h.2])
  have : sqNormU x < sqNormU y := by
    unfold sqNormU
    rcases hlt with h | h <;> nlinarith
  exact ⟨this.le, not_le.mpr this⟩

/-- **Figure 16.D.4** (MWG, p. 558). In the one-consumer economy with `u(x) = x₁² + x₂²`,
`ω = (2, 2)` and free disposal, consuming the endowment is (trivially) Pareto optimal, but it is
not a price equilibrium with transfers for any prices: at any `p ≥ 0` one of the corners
`(4, 0)`, `(0, 4)` is affordable and better. -/
theorem figure_16_D_4 :
    (replicaEconomy (utilityPref sqNormU) ![2, 2] 1).IsParetoOptimal (symmetricAlloc ![2, 2] 1) ∧
      ∀ p w, ¬ (replicaEconomy (utilityPref sqNormU) ![2, 2] 1).IsPriceEqmWithTransfers
        (symmetricAlloc ![2, 2] 1) p w := by
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ _ => le_rfl⟩, ?_⟩, ?_⟩, fun p w h => ?_⟩
  · fin_cases l <;> norm_num [symmetricAlloc]
  · simp [replicaEconomy, symmetricAlloc]
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have hk0 : k = 0 := Subsingleton.elim _ _
    subst hk0
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    simp [replicaEconomy] at h0 h1
    have hy0 := hy' () 0
    have hy1 := hy' () 1
    have hx0 := hx' 0 0
    have hx1 := hx' 0 1
    change sqNormU (a'.x 0) ≤ sqNormU ![2, 2]
    unfold sqNormU
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  · have hp : ∀ l, 0 ≤ p l := footnote_9 (h.2.1 ())
    have hw : w 0 = 2 * p 0 + 2 * p 1 := by
      have := h.1
      simp [replicaEconomy, symmetricAlloc, dotProduct, Fin.sum_univ_two] at this
      linarith
    rcases le_total (p 1) (p 0) with hle | hle
    · have hb : (![0, 4] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (w 0) :=
        ⟨fun l => by fin_cases l <;> norm_num, by rw [dot_two, hw]; simp; linarith⟩
      have := (h.2.2.1 0).2 _ hb
      change sqNormU ![0, 4] ≤ sqNormU ![2, 2] at this
      norm_num [sqNormU] at this
    · have hb : (![4, 0] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (w 0) :=
        ⟨fun l => by fin_cases l <;> norm_num, by rw [dot_two, hw]; simp; linarith⟩
      have := (h.2.2.1 0).2 _ hb
      change sqNormU ![4, 0] ≤ sqNormU ![2, 2] at this
      norm_num [sqNormU] at this

/-- **Figure 16.D.5** (MWG, pp. 557-558). In the two-consumer replica (endowments doubled to
`2ω`), `x'₁ = ω + (1, -1)`, `x'₂ = ω + (-1, 1)` Pareto dominates the symmetric allocation, which is
therefore no longer Pareto optimal. The preference satisfies the hypotheses of Exercise 16.D.4. -/
theorem figure_16_D_5 :
    RationalOn (nonnegOrthant 2) (utilityPref sqNormU) ∧
      PrefContinuous (nonnegOrthant 2) (utilityPref sqNormU) ∧
      PrefStronglyMonotone (nonnegOrthant 2) (utilityPref sqNormU) ∧
      (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).ParetoDominates
        ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ (symmetricAlloc ![2, 2] 2) ∧
      (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsFeasible
        ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ ∧
      ¬ (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsParetoOptimal
        (symmetricAlloc ![2, 2] 2) := by
  have hdom : (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).ParetoDominates
      ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ (symmetricAlloc ![2, 2] 2) := by
    refine ⟨fun i => ?_, 0, ?_, ?_⟩
    · fin_cases i <;> norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
    · norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
    · norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
  have hfeas : (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsFeasible
      ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ := by
    refine ⟨⟨fun i l => ?_, fun _ _ => le_rfl⟩, ?_⟩
    · fin_cases i <;> fin_cases l <;> norm_num [replicaEconomy]
    · funext l
      fin_cases l <;> norm_num [replicaEconomy, Fin.sum_univ_two]
  refine ⟨rationalOn_utilityPref _ _, prefContinuous_utilityPref (by unfold sqNormU; fun_prop),
    sqNormU_stronglyMonotone, hdom, hfeas, fun h => h.2 ⟨_, hfeas, hdom⟩⟩

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pareto optimality and social welfare optima (MWG Section 16.E, pp. 558-561)

Preferences are represented by utility functions `uᵢ` (`PrefEconomy.ofUtility`).

* The utility possibility set `U` and the Pareto frontier `UP` (p. 558-559);
  **Proposition 16.E.1**: a feasible allocation is Pareto optimal iff its utility vector lies in
  `UP`. Footnote 12: a boundary point of `U` need not be Pareto optimal (Figure 16.C.1).
* **Exercise 16.E.2**: convex `Xᵢ`, `Yⱼ` and concave `uᵢ` give a convex `U`.
* **Proposition 16.E.2**: a maximizer of `λ·u` on `U` with `λ ≫ 0` is in `UP`; if `U` is convex,
  every `ū ∈ UP` maximizes `λ·u` on `U` for some `λ ≥ 0`, `λ ≠ 0` (supporting hyperplane,
  Mathlib's geometric Hahn-Banach). Without convexity this fails (the point `ū` of Figure 16.E.1,
  made concrete with `uᵢ(x) = x²`).
* The normative representative consumer (16.E.2) (p. 561).
* **Exercise 16.E.1**: (a) a point of `U'` on the boundary of `U` that is not Pareto optimal;
  (b) with free disposal and continuous, strongly monotone utilities on `ℝ^L₊`, the utility vector
  of a feasible allocation that is not Pareto optimal is interior to `U` (so boundary points of
  `U` in `U'` are Pareto optimal), and `U' = U ∩ ℝ^I₊` when `uᵢ(0) = 0` and `0 ∈ Yⱼ`; (c) in a pure
  exchange economy with `ω̄ ≫ 0` and continuous preferences, no feasible allocation makes every
  consumer better off than at a price quasiequilibrium with transfers.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Section 16.E** (MWG, p. 558). The utility possibility set
`U = {v ∈ ℝ^I : vᵢ ≤ uᵢ(xᵢ) for some feasible (x, y)}`. -/
def utilityPossibilitySet (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i ≤ u i (a.x i)}

/-- **Exercise 16.E.1** (MWG, p. 576). The set `U' ⊆ U` of utility vectors achieved by feasible
allocations. -/
def achievedUtilitySet (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i = u i (a.x i)}

/-- **Section 16.E** (MWG, p. 559). The Pareto frontier `UP`: the points of `U` not weakly
dominated, with a strict improvement, by another point of `U`. -/
def paretoFrontier (U : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | v ∈ U ∧ ¬ ∃ v' ∈ U, (∀ i, v i ≤ v' i) ∧ ∃ i, v i < v' i}

/-- `U' ⊆ U`. -/
theorem achievedUtilitySet_subset (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) :
    achievedUtilitySet E u ⊆ utilityPossibilitySet E u :=
  fun _ ⟨a, ha, hv⟩ => ⟨a, ha, fun i => (hv i).le⟩

/-- `U` is comprehensive: `U - ℝ^I₊ ⊆ U`. -/
theorem utilityPossibilitySet_down {E : PrefEconomy ι κ L} {u : ι → (Fin L → ℝ) → ℝ}
    {v w : ι → ℝ} (hv : v ∈ utilityPossibilitySet E u) (hwv : w ≤ v) :
    w ∈ utilityPossibilitySet E u :=
  let ⟨a, ha, h⟩ := hv
  ⟨a, ha, fun i => (hwv i).trans (h i)⟩

/-- **Proposition 16.E.1** (MWG, p. 559). A feasible allocation is Pareto optimal if and only if
its utility vector lies on the Pareto frontier `UP`. -/
theorem proposition_16_E_1 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a ↔
      (fun i => u i (a.x i)) ∈ paretoFrontier
        (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  constructor
  · rintro ⟨-, hno⟩
    refine ⟨⟨a, ha, fun _ => le_rfl⟩, ?_⟩
    rintro ⟨v', ⟨a', ha', hv'⟩, hle, i, hlt⟩
    exact hno ⟨a', ha', fun k => (hle k).trans (hv' k), i, (hle i).trans (hv' i),
      not_le.mpr (lt_of_lt_of_le hlt (hv' i))⟩
  · rintro ⟨-, hno⟩
    refine ⟨ha, ?_⟩
    rintro ⟨a', ha', hle, i, hi⟩
    exact hno ⟨fun k => u k (a'.x k), ⟨a', ha', fun _ => le_rfl⟩, fun k => hle k, i,
      not_le.mp hi.2⟩

/-- **Exercise 16.E.2** (MWG, p. 576; p. 559). If every `Xᵢ` and every `Yⱼ` is convex and every
`uᵢ` is concave on `Xᵢ`, the utility possibility set `U` is convex. -/
theorem exercise_16_E_2 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} (hY : ∀ j, Convex ℝ (Y j))
    (hu : ∀ i, ConcaveOn ℝ (X i) (u i)) :
    Convex ℝ (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  rintro v ⟨a, ⟨⟨hx, hy⟩, hc⟩, hv⟩ v' ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hv'⟩ α β hα hβ hαβ
  refine ⟨⟨fun i => α • a.x i + β • a'.x i, fun j => α • a.y j + β • a'.y j⟩,
    ⟨⟨fun i => (hu i).1 (hx i) (hx' i) hα hβ hαβ, fun j => hY j (hy j) (hy' j) hα hβ hαβ⟩, ?_⟩,
    fun i => ?_⟩
  · change ∑ i, (α • a.x i + β • a'.x i) = ω + ∑ j, (α • a.y j + β • a'.y j)
    have hc0 : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    have hc1 : ∑ i, a'.x i = ω + ∑ j, a'.y j := hc'
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
      ← Finset.smul_sum, ← Finset.smul_sum, hc0, hc1, smul_add, smul_add]
    have : α • ω + β • ω = ω := by rw [← add_smul, hαβ, one_smul]
    rw [show ω + (α • ∑ j, a.y j + β • ∑ j, a'.y j) =
      (α • ω + β • ω) + (α • ∑ j, a.y j + β • ∑ j, a'.y j) by rw [this]]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := (hu i).2 (hx i) (hx' i) hα hβ hαβ
    simp only [smul_eq_mul] at this
    nlinarith [hv i, hv' i, mul_le_mul_of_nonneg_left (hv i) hα,
      mul_le_mul_of_nonneg_left (hv' i) hβ]

/-- **Proposition 16.E.2** (MWG, p. 560), first part. If `u*` maximizes `λ·u` on `U` for some
`λ ≫ 0`, then `u* ∈ UP`. -/
theorem proposition_16_E_2_i {U : Set (ι → ℝ)} {lam us : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    (hus : us ∈ U) (hmax : ∀ v ∈ U, ∑ i, lam i * v i ≤ ∑ i, lam i * us i) :
    us ∈ paretoFrontier U := by
  refine ⟨hus, ?_⟩
  rintro ⟨v, hv, hle, i, hlt⟩
  have := Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt (hlam i)⟩
  linarith [hmax v hv]

/-- A continuous linear functional on `ℝ^I` is a weighted sum of the coordinates. -/
theorem strongDual_apply_eq_sum [DecidableEq ι] (f : StrongDual ℝ (ι → ℝ)) (v : ι → ℝ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : ι → ℝ) by
    funext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **Proposition 16.E.2** (MWG, p. 560), second part. If `U ⊆ ℝ^I` (`I > 0`) is convex and
comprehensive (`U - ℝ^I₊ ⊆ U`, as is every utility possibility set), then for every `ū ∈ UP`
there are welfare weights `λ ≥ 0`, `λ ≠ 0` such that `ū` maximizes `λ·u` on `U`. -/
theorem proposition_16_E_2_ii [Nonempty ι] {U : Set (ι → ℝ)} (hU : Convex ℝ U)
    (hdown : ∀ v ∈ U, ∀ w, w ≤ v → w ∈ U) {ub : ι → ℝ} (hub : ub ∈ paretoFrontier U) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
      ∀ v ∈ U, ∑ i, lam i * v i ≤ ∑ i, lam i * ub i := by
  classical
  set O : Set (ι → ℝ) := {v | ∀ i, ub i < v i} with hO
  have hOopen : IsOpen O := by
    have : O = ⋂ i, {v : ι → ℝ | ub i < v i} := by ext v; simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hOconv : Convex ℝ O := by
    intro x hx y hy a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hx i; have h2 := hy i
    have : ub i = a * ub i + b * ub i := by rw [← add_mul, hab, one_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
  have hdisj : Disjoint O U := by
    rw [Set.disjoint_left]
    intro v hvO hvU
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact hub.2 ⟨v, hvU, fun i => (hvO i).le, i₀, hvO i₀⟩
  obtain ⟨f, s, hfO, hfU⟩ := geometric_hahn_banach_open hOconv hOopen hU hdisj
  set lam : ι → ℝ := fun i => -f (Pi.single i 1) with hlam
  have hf : ∀ v, f v = -∑ i, lam i * v i := fun v => by
    rw [strongDual_apply_eq_sum]
    simp [hlam, Finset.sum_neg_distrib]
  -- `λ·v ≤ -s` on `U` and `λ·ū ≥ -s`
  have hU' : ∀ v ∈ U, ∑ i, lam i * v i ≤ -s := fun v hv => by
    have := hfU v hv
    rw [hf] at this
    linarith
  have hub' : -s ≤ ∑ i, lam i * ub i := by
    by_contra hlt
    push Not at hlt
    set S := ∑ i, |lam i| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    set ε := (-s - ∑ i, lam i * ub i) / (S + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have hmem : (fun i => ub i + ε) ∈ O := fun i => by simp; linarith
    have h1 := hfO _ hmem
    rw [hf] at h1
    have h2 : ∑ i, lam i * (ub i + ε) ≤ ∑ i, lam i * ub i + ε * S := by
      rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := le_abs_self (lam i)
      nlinarith
    have h3 : ε * S < -s - ∑ i, lam i * ub i := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨lam, fun i => ?_, ?_, fun v hv => (hU' v hv).trans hub'⟩
  · by_contra hneg
    push Not at hneg
    have hmem := hdown ub hub.1 (ub - (Pi.single i 1 : ι → ℝ)) (fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk])
    have := hU' _ hmem
    have hcalc : ∑ k, lam k * (ub - (Pi.single i 1 : ι → ℝ)) k = ∑ k, lam k * ub k - lam i := by
      simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [hcalc] at this
    linarith
  · intro h0
    have := hfU ub hub.1
    have h2 := hfO (fun i => ub i + 1) (fun i => by simp)
    rw [hf] at this h2
    simp [h0] at this h2
    linarith

/-- **Section 16.E** (MWG, p. 560). If the utility possibility set is convex (and `I > 0`), every
Pareto optimal allocation (in particular every Walrasian equilibrium allocation, by Proposition
16.C.1) maximizes `∑ᵢ λᵢuᵢ` on `U` for some welfare weights `λ ≥ 0`, `λ ≠ 0`. -/
theorem pareto_isWelfareOptimum [Nonempty ι] {X : ι → Set (Fin L → ℝ)}
    {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hU : Convex ℝ (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u))
    {a : Allocation ι κ L} (hpo : (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
      ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
        ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i) :=
  proposition_16_E_2_ii hU (fun _ hv _ hwv => utilityPossibilitySet_down hv hwv)
    ((proposition_16_E_1 hpo.1).mp hpo)

/-- **Section 16.E** (MWG, p. 560). Every feasible allocation whose utility vector maximizes a
linear social welfare function with weights `λ ≫ 0` on `U` is Pareto optimal. -/
theorem welfareOptimum_isPareto {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {a : Allocation ι κ L} (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a)
    (hmax : ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
      ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i)) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a :=
  (proposition_16_E_1 ha).mpr (proposition_16_E_2_i hlam ⟨a, ha, fun _ => le_rfl⟩ hmax)

/-! ## Footnote 12 and Exercise 16.E.1(a): boundary points that are not Pareto optimal -/

/-- The utility functions of the economy of Figure 16.C.1. -/
noncomputable def fig16C1Utilities : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fig16C1u1, fig16C1u2]

/-- **Footnote 12** (MWG, p. 559) and **Exercise 16.E.1(a)** (MWG, p. 576). In the two-consumer,
two-good exchange economy of Figure 16.C.1, the utility vector `(1, 5/2)` of `x*` is achieved by a
feasible allocation (it is in `U'`), lies on the boundary of `U` (it is in `U` but not in its
interior), and `x*` is not Pareto optimal. -/
theorem footnote_12 :
    (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
        achievedUtilitySet fig16C1Economy fig16C1Utilities ∧
      (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
        frontier (utilityPossibilitySet fig16C1Economy fig16C1Utilities) ∧
      ¬ fig16C1Economy.IsParetoOptimal fig16C1Eqm := by
  have hpet := figure_16_C_1.1
  have hach : (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
      achievedUtilitySet fig16C1Economy fig16C1Utilities := ⟨_, hpet.isFeasible, fun _ => rfl⟩
  refine ⟨hach, ⟨subset_closure (achievedUtilitySet_subset _ _ hach), fun hint => ?_⟩,
    figure_16_C_1.2.1⟩
  -- consumer 1's utility never exceeds `1`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
  have hmem : (fun i => fig16C1Utilities i (fig16C1Eqm.x i) + ε / 2) ∈
      utilityPossibilitySet fig16C1Economy fig16C1Utilities := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨a, -, ha⟩ := hmem
  have h0 := ha 0
  simp only [fig16C1Utilities, fig16C1Eqm, Matrix.cons_val_zero] at h0
  have h1 : fig16C1u1 ![3 / 2, 0] = 1 := by norm_num [fig16C1u1]
  have h2 : fig16C1u1 (a.x 0) ≤ 1 := min_le_right _ _
  rw [h1] at h0
  linarith

/-! ## Figure 16.E.1: a Pareto optimum that maximizes no linear welfare function -/

/-- The utility `u(x) = x²` of the one-good example. -/
def squareUtility : Fin 2 → (Fin 1 → ℝ) → ℝ := fun _ x => x 0 ^ 2

/-- **Figure 16.E.1** (MWG, pp. 559-561). The exchange economy with one good, endowment `1`, two
consumers with `uᵢ(x) = x²`. -/
def fig16E1Economy : PrefEconomy (Fin 2) Unit 1 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) squareUtility (fun _ => nonposOrthant 1) ![1]

/-- **Figure 16.E.1** (MWG, p. 561). With a nonconvex utility possibility set, a Pareto optimum
need not maximize any linear social welfare function: in `fig16E1Economy` the equal split
`(1/2, 1/2)` is Pareto optimal (utilities `(1/4, 1/4)`), but for every `λ ≥ 0`, `λ ≠ 0`, one of the
extreme allocations gives a strictly higher `λ·u`. -/
theorem figure_16_E_1 :
    fig16E1Economy.IsParetoOptimal ⟨fun _ => ![1 / 2], fun _ => 0⟩ ∧
      ∀ lam : Fin 2 → ℝ, (∀ i, 0 ≤ lam i) → lam ≠ 0 →
        ∃ v ∈ utilityPossibilitySet fig16E1Economy squareUtility,
          ∑ i, lam i * (1 / 4 : ℝ) < ∑ i, lam i * v i := by
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ _ => le_rfl⟩, ?_⟩, ?_⟩, fun lam hlam hne => ?_⟩
  · fin_cases l; norm_num
  · funext l; fin_cases l; simp [fig16E1Economy, PrefEconomy.ofUtility]
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    have h0 := congrFun hc' 0
    simp [fig16E1Economy, PrefEconomy.ofUtility, Fin.sum_univ_two] at h0
    have hy := hy' () 0
    have hx0 := hx' 0 0
    have hx1 := hx' 1 0
    have hl0 := hle 0
    have hl1 := hle 1
    simp only [fig16E1Economy, PrefEconomy.ofUtility, utilityPref, squareUtility] at hl0 hl1 hk
    simp only [Matrix.cons_val_zero] at hl0 hl1 hk
    have ha0 : 1 / 2 ≤ a'.x 0 0 := by nlinarith
    have ha1 : 1 / 2 ≤ a'.x 1 0 := by nlinarith
    have e0 : a'.x 0 0 = 1 / 2 := by linarith
    have e1 : a'.x 1 0 = 1 / 2 := by linarith
    apply hk.2
    fin_cases k <;> simp only [utilityPref, squareUtility] <;> simp [e0, e1]
  · have hfeas : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        fig16E1Economy.IsFeasible ⟨![![t], ![1 - t]], fun _ => 0⟩ := by
      intro t ht0 ht1
      refine ⟨⟨fun i l => ?_, fun _ _ => le_rfl⟩, ?_⟩
      · fin_cases i <;> fin_cases l <;> simp <;> linarith
      · funext l; fin_cases l; simp [fig16E1Economy, PrefEconomy.ofUtility]
    have hsum : 0 < lam 0 + lam 1 := by
      rcases (hlam 0).lt_or_eq with h | h
      · linarith [hlam 1]
      rcases (hlam 1).lt_or_eq with h' | h'
      · linarith
      exfalso; apply hne; funext i; fin_cases i <;> simp [← h, ← h']
    rcases le_total (lam 1) (lam 0) with hle | hle
    · refine ⟨_, ⟨_, hfeas 1 zero_le_one le_rfl, fun _ => le_rfl⟩, ?_⟩
      simp [squareUtility, Fin.sum_univ_two]
      nlinarith
    · refine ⟨_, ⟨_, hfeas 0 le_rfl zero_le_one, fun _ => le_rfl⟩, ?_⟩
      simp [squareUtility, Fin.sum_univ_two]
      nlinarith

/-! ## The normative representative consumer (16.E.2) -/

/-- **(16.E.2)** (MWG, p. 561). The utility of the normative representative consumer for weights
`λ`: `u_λ(x̄) = sup {∑ᵢ λᵢ uᵢ(xᵢ) : xᵢ ∈ Xᵢ, ∑ᵢ xᵢ = x̄}`. -/
noncomputable def repUtility (X : ι → Set (Fin L → ℝ)) (u : ι → (Fin L → ℝ) → ℝ)
    (lam : ι → ℝ) (xb : Fin L → ℝ) : ℝ :=
  sSup {s | ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = xb ∧
    s = ∑ i, lam i * u i (x i)}

/-- **Section 16.E** (MWG, p. 561). Let `(x*, y*)` be feasible and let `λ` be welfare weights at
which `u(x*)` maximizes `λ·u` on `U` (e.g. from Proposition 16.E.2, `λ ≥ 0`). Then `x*` attains
`u_λ(∑ᵢ x*ᵢ) = ∑ᵢ λᵢ uᵢ(x*ᵢ)`, and `(∑ᵢ x*ᵢ, ∑ⱼ y*ⱼ)` solves the representative consumer's problem
`max u_λ(x̄)` subject to `x̄ = ω̄ + ȳ`, `ȳ ∈ Y = ∑ⱼ Yⱼ`. -/
theorem representative_consumer {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {lam : ι → ℝ} {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a)
    (hmax : ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
      ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i)) :
    repUtility X u lam (∑ i, a.x i) = ∑ i, lam i * u i (a.x i) ∧
      ∀ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) →
        (∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = ω + ∑ j, y j) →
        repUtility X u lam (ω + ∑ j, y j) ≤ repUtility X u lam (∑ i, a.x i) := by
  have hbound : ∀ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) → ∀ x : ι → Fin L → ℝ,
      (∀ i, x i ∈ X i) → ∑ i, x i = ω + ∑ j, y j →
      ∑ i, lam i * u i (x i) ≤ ∑ i, lam i * u i (a.x i) := fun y hy x hx hs =>
    hmax _ ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hs⟩, fun _ => le_rfl⟩
  have hval : repUtility X u lam (∑ i, a.x i) = ∑ i, lam i * u i (a.x i) := by
    apply le_antisymm
    · refine csSup_le ⟨_, a.x, ha.1.1, rfl, rfl⟩ ?_
      rintro s ⟨x, hx, hs, rfl⟩
      exact hbound a.y ha.1.2 x hx (hs.trans ha.2)
    · refine le_csSup ⟨∑ i, lam i * u i (a.x i), ?_⟩ ⟨a.x, ha.1.1, rfl, rfl⟩
      rintro s ⟨x, hx, hs, rfl⟩
      exact hbound a.y ha.1.2 x hx (hs.trans ha.2)
  refine ⟨hval, fun y hy hne => ?_⟩
  rw [hval]
  obtain ⟨x0, hx0, hs0⟩ := hne
  refine csSup_le ⟨_, x0, hx0, hs0, rfl⟩ ?_
  rintro s ⟨x, hx, hs, rfl⟩
  exact hbound y hy x hx hs

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The boundary of the utility possibility set (MWG Exercise 16.E.1(b)-(c), p. 576)

* **Exercise 16.E.1(b)**: with `Xᵢ = ℝ^L₊` and continuous, strongly monotone utilities, the utility
  vector of a feasible allocation that is not Pareto optimal lies in the interior of `U`; hence a
  boundary point of `U` that belongs to `U'` is the utility vector only of Pareto optima. The
  hint's claim `U' = U ∩ ℝ^I₊` (for `uᵢ(0) = 0`, free disposal and `J ≥ 1`) is proved too. The
  book's further assumption `0 ∈ Yⱼ` is not needed.
* **Exercise 16.E.1(c)**: in a pure exchange economy with `Xᵢ = ℝ^L₊`, continuous (rational)
  preferences and `ω̄ ≫ 0`, no feasible allocation makes every consumer strictly better off than
  at a price quasiequilibrium with transfers. Local nonsatiation is not needed.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- Strong monotonicity of a utility on `ℝ^L₊` gives weak monotonicity. -/
theorem utility_mono_of_strongMono {u : (Fin L → ℝ) → ℝ}
    (h : PrefStronglyMonotone (nonnegOrthant L) (utilityPref u)) {x y : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y) : u x ≤ u y := by
  by_cases heq : y = x
  · rw [heq]
  · exact (h x hx y (fun l => (hx l).trans (hxy l)) hxy heq).1

/-- **Exercise 16.E.1(b)** (MWG, p. 576). With `Xᵢ = ℝ^L₊` and utilities that are continuous and
strongly monotone on `ℝ^L₊`, if a feasible allocation is not Pareto optimal, its utility vector is
in the interior of the utility possibility set `U`. -/
theorem exercise_16_E_1b_interior {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)}
    {ω : Fin L → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible a)
    (hno : ¬ (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsParetoOptimal a) :
    (fun i => u i (a.x i)) ∈
      interior (utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω)
        u) := by
  classical
  have hno' := hno
  simp only [PrefEconomy.IsParetoOptimal, not_and, not_not] at hno'
  obtain ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩ := hno' ha
  have hle' : ∀ i, u i (a.x i) ≤ u i (a'.x i) := hle
  have hlt : u k (a.x k) < u k (a'.x k) := not_le.mp hk.2
  have hxX : ∀ i, a.x i ∈ nonnegOrthant L := ha.1.1
  have hx'X : ∀ i, a'.x i ∈ nonnegOrthant L := hx'
  -- consumer `k` holds some good in positive quantity
  obtain ⟨l, hl⟩ : ∃ l, 0 < a'.x k l := by
    by_contra hall
    push Not at hall
    have h0 : a'.x k = 0 := funext fun l => le_antisymm (hall l) (hx'X k l)
    have := utility_mono_of_strongMono (hmono k) (x := 0) (y := a.x k) (fun _ => le_rfl)
      (fun l => hxX k l)
    rw [h0] at hlt
    linarith
  obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single (rationalOn_utilityPref _ (u k))
    (prefContinuous_utilityPref (hcont k)) (hx'X k) (hxX k) hk hl
  have hδlt : u k (a.x k) < u k (a'.x k - Pi.single l δ) := not_le.mp hs.2
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨k⟩
  set g : Fin L → ℝ := Pi.single l (δ / n) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    by_cases hm : m = l
    · subst hm; rw [hg, Pi.single_eq_same]; positivity
    · simp [hg, hm]
  set x'' : ι → Fin L → ℝ := fun i => a'.x i + g - if i = k then Pi.single l δ else 0 with hx''
  have hx''X : ∀ i, x'' i ∈ nonnegOrthant L := by
    intro i m
    by_cases hik : i = k
    · subst hik
      simp only [hx'', ↓reduceIte, Pi.sub_apply, Pi.add_apply]
      have h1 := hmem m
      simp only [Pi.sub_apply] at h1
      linarith [hg0 m]
    · simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero]
      linarith [hg0 m, hx'X i m]
  have hbetter : ∀ i, u i (a.x i) < u i (x'' i) := by
    intro i
    by_cases hik : i = k
    · subst hik
      refine lt_of_lt_of_le hδlt (utility_mono_of_strongMono (hmono i) hmem fun m => ?_)
      simp only [hx'', ↓reduceIte, Pi.sub_apply, Pi.add_apply]
      linarith [hg0 m]
    · have hge : a'.x i ≤ x'' i := fun m => by
        simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero]
        linarith [hg0 m]
      have hne : x'' i ≠ a'.x i := by
        intro heq
        have := congrFun heq l
        simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero,
          hg, Pi.single_eq_same] at this
        have : 0 < δ / n := div_pos hδ hn0
        linarith
      exact lt_of_le_of_lt (hle' i) (not_le.mp (hmono i _ (hx'X i) _ (hx''X i) hge hne).2)
  have hcg : (Fintype.card ι) • g = Pi.single l δ := by
    funext m
    by_cases hm : m = l
    · subst hm
      simp only [hg, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul]
      rw [hn] at hn0 ⊢
      field_simp
    · simp [hg, hm]
  have hsum : ∑ i, x'' i = ∑ i, a'.x i := by
    simp only [hx'', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hcg, add_sub_cancel_right]
  have hfeas : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible
      ⟨x'', a'.y⟩ := ⟨⟨hx''X, hy'⟩, hsum.trans hc'⟩
  set O : Set (ι → ℝ) := {w | ∀ i, w i < u i (x'' i)} with hO
  have hOopen : IsOpen O := by
    have : O = ⋂ i, {w : ι → ℝ | w i < u i (x'' i)} := by ext w; simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  refine interior_maximal ?_ hOopen hbetter
  intro w hw
  exact ⟨⟨x'', a'.y⟩, hfeas, fun i => (hw i).le⟩

/-- **Exercise 16.E.1(b)** (MWG, p. 576). Under the assumptions of `exercise_16_E_1b_interior`,
every feasible allocation whose utility vector is a boundary point of `U` (in `U'` by
construction) is Pareto optimal. -/
theorem exercise_16_E_1b {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)}
    {ω : Fin L → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible a)
    (hb : (fun i => u i (a.x i)) ∈
      frontier (utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω)
        u)) :
    (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsParetoOptimal a := by
  by_contra hno
  exact hb.2 (exercise_16_E_1b_interior hcont hmono ha hno)

/-- **Exercise 16.E.1(b)**, hint (MWG, p. 576). With `Xᵢ = ℝ^L₊`, continuous strongly monotone
utilities normalized by `uᵢ(0) = 0`, free disposal in every `Yⱼ` and at least one firm,
`U' = U ∩ ℝ^I₊`. -/
theorem exercise_16_E_1b_hint [Nonempty κ] {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    (hu0 : ∀ i, u i 0 = 0)
    (hfd : ∀ j, ∀ y ∈ Y j, ∀ d ∈ nonnegOrthant L, y - d ∈ Y j) :
    achievedUtilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω) u =
      utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω) u ∩
        {v | ∀ i, 0 ≤ v i} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, hv⟩
    refine ⟨⟨a, ha, fun i => (hv i).le⟩, fun i => ?_⟩
    rw [hv i, ← hu0 i]
    exact utility_mono_of_strongMono (hmono i) (x := 0) (fun _ => le_rfl) (fun l => ha.1.1 i l)
  · rintro ⟨⟨a, ha, hv⟩, hv0⟩
    have hxX : ∀ i, a.x i ∈ nonnegOrthant L := ha.1.1
    -- scale every bundle down to the exact utility level
    have hscale : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1, u i (t • a.x i) = v i := by
      intro i
      have hc : ContinuousOn (fun t : ℝ => u i (t • a.x i)) (Set.Icc 0 1) :=
        (hcont i).comp (continuous_id.smul continuous_const).continuousOn fun t ht l => by
          simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg ht.1 (hxX i l)
      have hivt := intermediate_value_Icc (zero_le_one' ℝ) hc
      have hmemI : v i ∈ Set.Icc (u i ((0 : ℝ) • a.x i)) (u i ((1 : ℝ) • a.x i)) := by
        rw [zero_smul, one_smul, hu0]
        exact ⟨hv0 i, hv i⟩
      obtain ⟨t, ht, htv⟩ := hivt hmemI
      exact ⟨t, ht, htv⟩
    choose t ht htv using hscale
    set x' : ι → Fin L → ℝ := fun i => t i • a.x i with hx'
    set D : Fin L → ℝ := ∑ i, (a.x i - x' i) with hD
    have hD0 : D ∈ nonnegOrthant L := fun l => by
      simp only [hD, Finset.sum_apply, Pi.sub_apply, hx', Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => by nlinarith [(ht i).2, hxX i l]
    obtain ⟨j₀⟩ := ‹Nonempty κ›
    set y' : κ → Fin L → ℝ := fun j => if j = j₀ then a.y j - D else a.y j with hy'
    refine ⟨⟨x', y'⟩, ⟨⟨fun i l => ?_, fun j => ?_⟩, ?_⟩, fun i => (htv i).symm⟩
    · simp only [hx', Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (ht i).1 (hxX i l)
    · by_cases hj : j = j₀
      · subst hj
        simp only [hy', ↓reduceIte]
        exact hfd j _ (ha.1.2 j) D hD0
      · simp only [hy', hj, ↓reduceIte]
        exact ha.1.2 j
    · change ∑ i, x' i = ω + ∑ j, y' j
      have h1 : ∑ i, x' i = ∑ i, a.x i - D := by
        rw [hD, Finset.sum_sub_distrib, sub_sub_cancel]
      have h2 : ∑ j, y' j = ∑ j, a.y j - D := by
        rw [Finset.sum_congr rfl fun j _ => (show y' j = a.y j - if j = j₀ then D else 0 by
          by_cases hj : j = j₀ <;> simp [hy', hj]), Finset.sum_sub_distrib,
          Finset.sum_ite_eq' Finset.univ j₀ (fun _ => D)]
        simp
      have hc : ∑ i, a.x i = ω + ∑ j, a.y j := ha.2
      rw [h1, h2, hc, add_sub_assoc]

/-- **Exercise 16.E.1(c)** (MWG, p. 576). In a pure exchange economy (`J ≥ 1`, `I ≥ 1`) with
`Xᵢ = ℝ^L₊`, rational continuous preferences and `ω̄ ≫ 0`, no feasible allocation makes every
consumer strictly better off than at a price quasiequilibrium with transfers (the utility vector
of the quasiequilibrium is not interior to `U`). Some consumer has `wᵢ > 0` and then Proposition
16.D.2 applies to her. -/
theorem exercise_16_E_1c [Nonempty ι] [Nonempty κ] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hω : ∀ l, 0 < E.ω l) {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    ¬ ∃ a', E.IsFeasible a' ∧ ∀ i, Strict (E.pref i) (a'.x i) (a.x i) := by
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hs⟩
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hp : ∀ l, 0 ≤ p l := footnote_9 (hpe j₀ ▸ h.2.2.1 j₀)
  have hprof : ∀ j, p ⬝ᵥ a.y j = 0 := fun j => by
    have hmax := hpe j ▸ h.2.2.1 j
    have h1 := hmax.2 0 (fun _ => le_rfl)
    rw [dotProduct_zero] at h1
    have h2 : p ⬝ᵥ a.y j ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hmax.1 l)
    linarith
  have hsumw : ∑ i, w i = p ⬝ᵥ E.ω := by
    rw [h.2.1, Finset.sum_eq_zero fun j _ => hprof j, add_zero]
  have hpos : 0 < p ⬝ᵥ E.ω := dotProduct_pos_of_nonneg_ne_zero hp h.1 hω
  obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < w i := by
    by_contra hall
    push Not at hall
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hall i
    linarith
  have hgt : w i₁ < p ⬝ᵥ a'.x i₁ :=
    proposition_16_D_2 (hX i₁ ▸ convex_nonnegOrthant L) (hr i₁) (hc i₁) (h.2.2.2.1 i₁).1
      (h.2.2.2.1 i₁).2 (x' := 0) (by rw [hX i₁]; exact fun _ => le_rfl)
      (by rw [dotProduct_zero]; exact hi₁) _ (hx' i₁) (hs i₁)
  have hge : ∀ i, w i ≤ p ⬝ᵥ a'.x i := fun i => (h.2.2.2.1 i).2 _ (hx' i) (hs i)
  have h1 : ∑ i, w i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₁, Finset.mem_univ _, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i ≤ p ⬝ᵥ E.ω := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
    have : ∑ j, p ⬝ᵥ a'.y j ≤ 0 := Finset.sum_nonpos fun j _ =>
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l)
        ((hpe j ▸ hy' j : a'.y j ∈ nonposOrthant L) l)
    linarith
  linarith

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix A: technical properties of the set of feasible allocations (MWG pp. 573-574)

The set `A` of feasible allocations is `PrefEconomy.feasiblePairs`, a subset of
`ℝ^{LI} × ℝ^{LJ}`; the aggregate production set is `Y = ∑ⱼ Yⱼ` (`aggregateProduction`).

* **Exercise 16.AA.1**: if every `Xᵢ` and `Yⱼ` is closed, `A` is closed.
* **Proposition 16.AA.1**: as printed, the aggregate production set `Y` is only assumed convex
  (not closed), and the text asserts that irreversibility "yields the closedness of `Y`". Both
  fail: `aaCounterEconomy` has closed `Xᵢ` bounded below, closed `Yⱼ`, and a convex aggregate `Y`
  with `0 ∈ Y`, no free lunch and irreversibility, yet `Y` is not closed and `A` is unbounded
  (`proposition_16_AA_1_counterexample`, correction 3). With `Y` closed (an added assumption) the
  proposition holds: `A` is bounded (`proposition_16_AA_1`), and nonempty when `-ℝ^L₊ ⊆ Y` and
  some `x̂ᵢ ∈ Xᵢ` have `∑ᵢ x̂ᵢ ≤ ω̄` (`proposition_16_AA_1_nonempty`). The proof is the standard
  normalization argument: an unbounded sequence of feasible allocations, scaled down, has a
  nonzero limit direction that the assumptions force to be zero.
* **Exercise 16.AA.2**: `(Y + {ω̄}) ∩ ℝ^L₊` is compact for closed convex `Y ∋ 0` without free
  lunch; each of the four assumptions is indispensable (four examples).
* **Exercise 16.AA.3**: with `0 ∈ Y₁, Y₂` and irreversibility of `Y = Y₁ + Y₂`, the feasible
  production plans of firm 1 are bounded.
* **Proposition 16.AA.2**: if `A` is nonempty and compact and the `uᵢ` are continuous, `U` is
  closed and bounded above.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Appendix A** (MWG, p. 573). The aggregate production set `Y = ∑ⱼ Yⱼ`. -/
def aggregateProduction (Y : κ → Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {z | ∃ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) ∧ z = ∑ j, y j}

/-- **Appendix A** (MWG, p. 573). The set `A ⊆ ℝ^{LI} × ℝ^{LJ}` of feasible allocations. -/
def PrefEconomy.feasiblePairs (E : PrefEconomy ι κ L) :
    Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) :=
  {z | E.IsFeasible ⟨z.1, z.2⟩}

/-- The nonnegative orthant is closed. -/
theorem isClosed_nonnegOrthant : IsClosed (nonnegOrthant L) := by
  simp only [nonnegOrthant, Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)

/-- The nonpositive orthant is closed. -/
theorem isClosed_nonposOrthant : IsClosed (nonposOrthant L) := by
  simp only [nonposOrthant, Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_le (continuous_apply l) continuous_const

/-- **Exercise 16.AA.1** (MWG, p. 577). If every `Xᵢ` and every `Yⱼ` is closed, the set `A` of
feasible allocations is closed. -/
theorem exercise_16_AA_1 {E : PrefEconomy ι κ L} (hX : ∀ i, IsClosed (E.X i))
    (hY : ∀ j, IsClosed (E.Y j)) : IsClosed E.feasiblePairs := by
  have h1 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) | ∀ i, z.1 i ∈ E.X i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => (hX i).preimage ((continuous_apply i).comp continuous_fst)
  have h2 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) | ∀ j, z.2 j ∈ E.Y j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => (hY j).preimage ((continuous_apply j).comp continuous_snd)
  have h3 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) |
      ∑ i, z.1 i = E.ω + ∑ j, z.2 j} :=
    isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst)
      (continuous_const.add
        (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd))
  have : E.feasiblePairs = {z | ∀ i, z.1 i ∈ E.X i} ∩ {z | ∀ j, z.2 j ∈ E.Y j} ∩
      {z | ∑ i, z.1 i = E.ω + ∑ j, z.2 j} := by
    ext z
    simp only [PrefEconomy.feasiblePairs, PrefEconomy.IsFeasible, PrefEconomy.IsAllocation,
      Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

/-- **Proposition 16.AA.1** (MWG, p. 573), nonemptiness. If `-ℝ^L₊ ⊆ Y` and some `x̂ᵢ ∈ Xᵢ`
satisfy `∑ᵢ x̂ᵢ ≤ ω̄`, then `A` is nonempty. -/
theorem proposition_16_AA_1_nonempty {E : PrefEconomy ι κ L}
    (hY : nonposOrthant L ⊆ aggregateProduction E.Y) {xh : ι → Fin L → ℝ}
    (hxh : ∀ i, xh i ∈ E.X i) (hle : ∑ i, xh i ≤ E.ω) : E.feasiblePairs.Nonempty := by
  obtain ⟨y, hy, hsum⟩ := hY (show ∑ i, xh i - E.ω ∈ nonposOrthant L from fun l => by
    have := hle l
    simp only [Pi.sub_apply]
    linarith)
  exact ⟨(xh, y), ⟨hxh, hy⟩, by rw [← hsum]; abel⟩

/-- A limit of scaled-down points `sₙ⁻¹ cₙ`, `sₙ ≥ 1`, of a closed convex set containing `0`
belongs to the set. -/
theorem mem_of_tendsto_inv_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Y : Set V} (hc : IsClosed Y) (hconv : Convex ℝ Y) (h0 : (0 : V) ∈ Y) {c : ℕ → V}
    {s : ℕ → ℝ} (hcY : ∀ n, c n ∈ Y) (hs : ∀ n, 1 ≤ s n) {d : V}
    (ht : Tendsto (fun n => (s n)⁻¹ • c n) atTop (𝓝 d)) : d ∈ Y :=
  hc.mem_of_tendsto ht (Eventually.of_forall fun n => hconv.smul_mem_of_zero_mem h0 (hcY n)
    ⟨inv_nonneg.mpr (by linarith [hs n]), inv_le_one_of_one_le₀ (hs n)⟩)

/-- **Proposition 16.AA.1** (MWG, p. 573), boundedness, with the aggregate production set `Y`
assumed closed (correction 3). If every `Xᵢ` is bounded below and `Y = ∑ⱼ Yⱼ` is closed and
convex, contains `0`, has no free lunch and is irreversible, there is `r > 0` with `|x_{ℓi}| < r`
and `|y_{ℓj}| < r` for every feasible allocation. (Closedness of the `Xᵢ` and `Yⱼ` is not needed
for boundedness.) -/
theorem proposition_16_AA_1 {E : PrefEconomy ι κ L}
    (hXb : ∀ i, ∃ r : ℝ, ∀ x ∈ E.X i, ∀ l, -r < x l)
    (hYc : IsClosed (aggregateProduction E.Y)) (hYconv : Convex ℝ (aggregateProduction E.Y))
    (hY0 : (0 : Fin L → ℝ) ∈ aggregateProduction E.Y)
    (hnfl : ∀ y ∈ aggregateProduction E.Y, (∀ l, 0 ≤ y l) → y = 0)
    (hirr : ∀ y ∈ aggregateProduction E.Y, -y ∈ aggregateProduction E.Y → y = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : Allocation ι κ L, E.IsFeasible a →
      (∀ i l, |a.x i l| < r) ∧ ∀ j l, |a.y j l| < r := by
  classical
  -- it suffices to bound the norm of `(x, y)`
  suffices hR : ∃ R : ℝ, ∀ a : Allocation ι κ L, E.IsFeasible a → ‖(a.x, a.y)‖ ≤ R by
    obtain ⟨R, hR⟩ := hR
    refine ⟨|R| + 1, by positivity, fun a ha => ⟨fun i l => ?_, fun j l => ?_⟩⟩
    · calc |a.x i l| = ‖a.x i l‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖a.x i‖ := norm_le_pi_norm _ l
        _ ≤ ‖a.x‖ := norm_le_pi_norm _ i
        _ ≤ ‖(a.x, a.y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
        _ ≤ R := hR a ha
        _ < |R| + 1 := by linarith [le_abs_self R]
    · calc |a.y j l| = ‖a.y j l‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖a.y j‖ := norm_le_pi_norm _ l
        _ ≤ ‖a.y‖ := norm_le_pi_norm _ j
        _ ≤ ‖(a.x, a.y)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        _ ≤ R := hR a ha
        _ < |R| + 1 := by linarith [le_abs_self R]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ a : Allocation ι κ L, E.IsFeasible a ∧ (n : ℝ) + 1 < ‖(a.x, a.y)‖ :=
    fun n => hno _
  choose a ha hbig using hex
  set s : ℕ → ℝ := fun n => ‖((a n).x, (a n).y)‖ with hs
  have hs1 : ∀ n, 1 ≤ s n := fun n => by
    have := hbig n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; simp only [hs]; linarith
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1 n]
  set w : ℕ → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) := fun n => (s n)⁻¹ • ((a n).x, (a n).y)
    with hw
  have hwS : ∀ n, w n ∈ Metric.sphere (0 : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, hw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨z, hzS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hzS
  -- the scale tends to infinity along the subsequence
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h1 := hbig (φ n)
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    simp only [hs]
    linarith
  have hx : ∀ i, Tendsto (fun n => (s (φ n))⁻¹ • (a (φ n)).x i) atTop (𝓝 (z.1 i)) := by
    intro i
    have := ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hlim
    simpa [hw, Function.comp_def] using this
  have hy : ∀ j, Tendsto (fun n => (s (φ n))⁻¹ • (a (φ n)).y j) atTop (𝓝 (z.2 j)) := by
    intro j
    have := ((continuous_apply j).comp continuous_snd).continuousAt.tendsto.comp hlim
    simpa [hw, Function.comp_def] using this
  -- Step 1: the consumption directions are nonnegative
  have hxnn : ∀ i l, 0 ≤ z.1 i l := by
    intro i l
    obtain ⟨r, hr⟩ := hXb i
    have hcoord : Tendsto (fun n => (s (φ n))⁻¹ * (a (φ n)).x i l) atTop (𝓝 (z.1 i l)) := by
      have := ((continuous_apply l).continuousAt.tendsto).comp (hx i)
      simpa [Function.comp_def] using this
    have hlow : Tendsto (fun n => (s (φ n))⁻¹ * -r) atTop (𝓝 0) := by
      simpa using hinv.mul_const (-r)
    exact le_of_tendsto_of_tendsto hlow hcoord (Eventually.of_forall fun n =>
      mul_le_mul_of_nonneg_left (hr _ ((ha (φ n)).1.1 i) l).le
        (inv_nonneg.mpr (hspos _).le))
  -- membership of scaled production limits in `Y`
  have hmemY : ∀ (T : Finset κ) (c : ℕ → Fin L → ℝ), (∀ n, c n ∈ aggregateProduction E.Y) →
      Tendsto (fun n => (s (φ n))⁻¹ • c n) atTop (𝓝 (∑ j ∈ T, z.2 j)) →
      ∑ j ∈ T, z.2 j ∈ aggregateProduction E.Y := fun T c hc ht =>
    mem_of_tendsto_inv_smul hYc hYconv hY0 hc (fun n => hs1 (φ n)) ht
  -- a fixed feasible production plan
  set y0 := (a 0).y with hy0
  have hy0Y : ∀ j, y0 j ∈ E.Y j := (ha 0).1.2
  -- the mixed plan: firms in `T` use the `n`-th plans, the others the fixed plan
  set mix : Finset κ → ℕ → κ → Fin L → ℝ := fun T n j =>
    if j ∈ T then (a (φ n)).y j else y0 j with hmix
  have hmixY : ∀ T n, ∑ j, mix T n j ∈ aggregateProduction E.Y := fun T n =>
    ⟨mix T n, fun j => by
      by_cases hj : j ∈ T
      · simp only [hmix, hj, ↓reduceIte]; exact (ha (φ n)).1.2 j
      · simp only [hmix, hj, ↓reduceIte]; exact hy0Y j, rfl⟩
  have hmixT : ∀ T : Finset κ,
      Tendsto (fun n => (s (φ n))⁻¹ • ∑ j, mix T n j) atTop (𝓝 (∑ j ∈ T, z.2 j)) := by
    intro T
    have hsplit : ∀ n, (s (φ n))⁻¹ • ∑ j, mix T n j =
        ∑ j ∈ T, (s (φ n))⁻¹ • (a (φ n)).y j + (s (φ n))⁻¹ • ∑ j ∈ Finset.univ \ T, y0 j := by
      intro n
      rw [← Finset.sum_sdiff (Finset.subset_univ T), smul_add, Finset.smul_sum,
        Finset.smul_sum, Finset.smul_sum, add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => by simp [hmix, hj]
      · exact Finset.sum_congr rfl fun j hj => by
          simp [hmix, (Finset.mem_sdiff.mp hj).2]
    simp_rw [hsplit]
    have h1 : Tendsto (fun n => ∑ j ∈ T, (s (φ n))⁻¹ • (a (φ n)).y j) atTop
        (𝓝 (∑ j ∈ T, z.2 j)) := tendsto_finsetSum T fun j _ => hy j
    have h2 : Tendsto (fun n => (s (φ n))⁻¹ • ∑ j ∈ Finset.univ \ T, y0 j) atTop (𝓝 0) := by
      simpa using hinv.smul_const (∑ j ∈ Finset.univ \ T, y0 j)
    simpa using h1.add h2
  have hTY : ∀ T : Finset κ, ∑ j ∈ T, z.2 j ∈ aggregateProduction E.Y := fun T =>
    hmemY T _ (hmixY T) (hmixT T)
  -- Step 2: the aggregate direction equals the consumption direction
  have hsumeq : ∑ i, z.1 i = ∑ j, z.2 j := by
    have hfeas : ∀ n, ∑ i, (s (φ n))⁻¹ • (a (φ n)).x i =
        (s (φ n))⁻¹ • E.ω + ∑ j, (s (φ n))⁻¹ • (a (φ n)).y j := fun n => by
      rw [← Finset.smul_sum, ← Finset.smul_sum, (ha (φ n)).2, smul_add]
    have h1 : Tendsto (fun n => ∑ i, (s (φ n))⁻¹ • (a (φ n)).x i) atTop (𝓝 (∑ i, z.1 i)) :=
      tendsto_finsetSum _ fun i _ => hx i
    have h2 : Tendsto (fun n => (s (φ n))⁻¹ • E.ω + ∑ j, (s (φ n))⁻¹ • (a (φ n)).y j) atTop
        (𝓝 (∑ j, z.2 j)) := by
      have := (hinv.smul_const E.ω).add (tendsto_finsetSum Finset.univ fun j _ => hy j)
      simpa using this
    simp_rw [hfeas] at h1
    exact tendsto_nhds_unique h1 h2
  -- Step 3: no free lunch kills the aggregate direction and the consumption directions
  have hagg0 : ∑ j, z.2 j = 0 := by
    refine hnfl _ (by simpa using hTY Finset.univ) fun l => ?_
    rw [← hsumeq, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hxnn i l
  have hx0 : ∀ i, z.1 i = 0 := by
    have hsum0 : ∑ i, z.1 i = 0 := hsumeq.trans hagg0
    intro i
    funext l
    have := congrFun hsum0 l
    rw [Finset.sum_apply] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hxnn k l).mp this i (Finset.mem_univ i)
  -- Step 4: irreversibility kills every firm's direction
  have hy0' : ∀ j, z.2 j = 0 := by
    intro j
    have hj : z.2 j ∈ aggregateProduction E.Y := by simpa using hTY {j}
    have hrest : -z.2 j ∈ aggregateProduction E.Y := by
      have h1 := hTY (Finset.univ.erase j)
      have h2 : ∑ k ∈ Finset.univ.erase j, z.2 k = -z.2 j := by
        rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ j),
          hagg0]
      rwa [h2] at h1
    exact hirr _ hj hrest
  have : z = 0 := Prod.ext (funext hx0) (funext hy0')
  rw [this, norm_zero] at hz1
  exact zero_ne_one hz1

/-! ## The counterexample to Proposition 16.AA.1 as printed -/

/-- Firm 1 of the counterexample: `{0} ∪ {(a, b) : a ≥ 0, ab ≤ -1}` (closed, not convex). -/
def aaY1 : Set (Fin 2 → ℝ) := {y | y = 0 ∨ (0 ≤ y 0 ∧ y 0 * y 1 ≤ -1)}

/-- **Proposition 16.AA.1** counterexample economy: one consumer with `X = ℝ²₊`, `ω̄ = (1, 1)`,
firm 1 with `aaY1`, firm 2 with free disposal. -/
def aaCounterEconomy : PrefEconomy Unit (Fin 2) 2 where
  X := fun _ => nonnegOrthant 2
  pref := fun _ _ _ => True
  Y := ![aaY1, nonposOrthant 2]
  ω := ![1, 1]

/-- The aggregate production set of `aaCounterEconomy` is
`{y : y₂ < 0} ∪ {(y₁, 0) : y₁ ≤ 0}`. -/
theorem aaCounter_agg (z : Fin 2 → ℝ) :
    z ∈ aggregateProduction aaCounterEconomy.Y ↔ z 1 < 0 ∨ (z 1 = 0 ∧ z 0 ≤ 0) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : y 1 ∈ nonposOrthant 2 := hy 1
    simp only [Fin.sum_univ_two, Pi.add_apply]
    rcases hy 0 with h0 | ⟨ha, hab⟩
    · rw [h0]
      simp only [Pi.zero_apply, zero_add]
      rcases (h1 1).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, h1 0⟩
    · left
      have hb : y 0 1 < 0 := by
        by_contra hb
        push Not at hb
        nlinarith
      linarith [h1 1]
  · rintro (h | ⟨h1, h0⟩)
    · set A := max (max 1 (z 0)) (-1 / z 1) with hA
      have hA1 : 1 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
      have hA0 : z 0 ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
      have hAz : -1 / z 1 ≤ A := le_max_right _ _
      refine ⟨![![A, z 1], ![z 0 - A, 0]], fun j => ?_, ?_⟩
      · fin_cases j
        · right
          refine ⟨by simp; linarith, ?_⟩
          simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [div_le_iff_of_neg h] at hAz
          linarith
        · intro l
          fin_cases l
          · simp; linarith
          · simp
      · funext l
        fin_cases l <;> simp
    · refine ⟨![0, z], fun j => ?_, ?_⟩
      · fin_cases j
        · left; rfl
        · intro l
          fin_cases l
          · simpa using h0
          · simp [h1]
      · simp

/-- **Proposition 16.AA.1** (MWG, pp. 573-574), correction 3. In `aaCounterEconomy` every
assumption of Proposition 16.AA.1 as printed holds (`Xᵢ` closed and bounded below; `Yⱼ` closed;
`Y` convex with `0 ∈ Y`, no free lunch and irreversibility), but `Y` is not closed (so
irreversibility does not yield closedness of `Y`, contrary to p. 574) and the set of feasible
allocations is unbounded. -/
theorem proposition_16_AA_1_counterexample :
    (∀ i, IsClosed (aaCounterEconomy.X i)) ∧
    (∀ i, ∀ x ∈ aaCounterEconomy.X i, ∀ l, -1 < x l) ∧
    (∀ j, IsClosed (aaCounterEconomy.Y j)) ∧
    Convex ℝ (aggregateProduction aaCounterEconomy.Y) ∧
    (0 : Fin 2 → ℝ) ∈ aggregateProduction aaCounterEconomy.Y ∧
    (∀ y ∈ aggregateProduction aaCounterEconomy.Y, (∀ l, 0 ≤ y l) → y = 0) ∧
    (∀ y ∈ aggregateProduction aaCounterEconomy.Y,
      -y ∈ aggregateProduction aaCounterEconomy.Y → y = 0) ∧
    ¬ IsClosed (aggregateProduction aaCounterEconomy.Y) ∧
    ∀ r : ℝ, ∃ a : Allocation Unit (Fin 2) 2, aaCounterEconomy.IsFeasible a ∧ r < a.y 0 0 := by
  refine ⟨fun _ => ?_, fun _ x hx l => by linarith [hx l], fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_nonnegOrthant
  · fin_cases j
    · have : aaY1 = {y : Fin 2 → ℝ | y = 0} ∪ ({y | 0 ≤ y 0} ∩ {y | y 0 * y 1 ≤ -1}) := by
        ext y; simp [aaY1]
      change IsClosed aaY1
      rw [this]
      exact isClosed_singleton.union ((isClosed_le continuous_const (continuous_apply 0)).inter
        (isClosed_le ((continuous_apply 0).mul (continuous_apply 1)) continuous_const))
    · exact isClosed_nonposOrthant
  · intro x hx y hy α β hα hβ hαβ
    rw [aaCounter_agg] at hx hy ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hx with hx | ⟨hx1, hx0⟩ <;> rcases hy with hy | ⟨hy1, hy0⟩
    · left
      rcases hα.lt_or_eq with ha | ha
      · nlinarith [mul_neg_of_pos_of_neg ha hx, mul_nonpos_of_nonneg_of_nonpos hβ hy.le]
      · subst ha; rw [zero_add] at hαβ; subst hαβ; simpa using hy
    · rcases hα.lt_or_eq with ha | ha
      · left; rw [hy1]; nlinarith [mul_neg_of_pos_of_neg ha hx]
      · subst ha; rw [zero_add] at hαβ; subst hαβ; right; simp [hy1, hy0]
    · rcases hβ.lt_or_eq with hb | hb
      · left; rw [hx1]; nlinarith [mul_neg_of_pos_of_neg hb hy]
      · subst hb; rw [add_zero] at hαβ; subst hαβ; right; simp [hx1, hx0]
    · right
      rw [hx1, hy1]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx0, mul_nonpos_of_nonneg_of_nonpos hβ hy0]
  · rw [aaCounter_agg]; right; simp
  · intro y hy hnn
    rw [aaCounter_agg] at hy
    rcases hy with h | ⟨h1, h0⟩
    · linarith [hnn 1]
    · funext l; fin_cases l
      · exact le_antisymm h0 (hnn 0)
      · exact h1
  · intro y hy hny
    rw [aaCounter_agg] at hy hny
    simp only [Pi.neg_apply] at hny
    rcases hy with h | ⟨h1, h0⟩
    · rcases hny with h' | ⟨h', -⟩ <;> linarith
    · rcases hny with h' | ⟨-, h0'⟩
      · linarith
      · funext l; fin_cases l
        · change y 0 = 0; linarith
        · exact h1
  · intro hc
    have hmem : ∀ n : ℕ, (![1, -1 / ((n : ℝ) + 1)] : Fin 2 → ℝ) ∈
        aggregateProduction aaCounterEconomy.Y := fun n => by
      rw [aaCounter_agg]; left
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_neg_of_neg_of_pos (by norm_num) this
    have ht : Tendsto (fun n : ℕ => (![1, -1 / ((n : ℝ) + 1)] : Fin 2 → ℝ)) atTop
        (𝓝 ![1, 0]) := by
      rw [tendsto_pi_nhds]
      intro l
      fin_cases l
      · simp
      · change Tendsto (fun n : ℕ => -1 / ((n : ℝ) + 1)) atTop (𝓝 0)
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
        rw [neg_zero] at this
        exact this.congr fun n => by ring
    have := hc.mem_of_tendsto ht (Eventually.of_forall hmem)
    rw [aaCounter_agg] at this
    norm_num at this
  · intro r
    set t := max r 1 + 1 with ht
    have ht1 : 1 ≤ t := by linarith [le_max_right r 1]
    have ht0 : 0 < t := by linarith
    refine ⟨⟨fun _ => ![1, 1 - 1 / t], ![![t, -1 / t], ![-t, 0]]⟩, ⟨⟨fun _ l => ?_, fun j => ?_⟩,
      ?_⟩, ?_⟩
    · fin_cases l
      · simp
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        have : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht1
        linarith
    · fin_cases j
      · right
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
        refine ⟨ht0.le, ?_⟩
        field_simp
        rfl
      · intro l
        fin_cases l
        · simp; linarith
        · simp
    · funext l
      fin_cases l
      · simp [aaCounterEconomy, Fin.sum_univ_two]
      · simp [aaCounterEconomy, Fin.sum_univ_two]; ring
    · simp only [Matrix.cons_val_zero]
      linarith [le_max_left r 1]

/-! ## Exercise 16.AA.2 -/

/-- **Exercise 16.AA.2** (MWG, p. 577). If `Y` is closed and convex, `0 ∈ Y`, and `Y ∩ ℝ^L₊ ⊆ {0}`,
then `(Y + {ω̄}) ∩ ℝ^L₊` is compact. -/
theorem exercise_16_AA_2 {Y : Set (Fin L → ℝ)} (hc : IsClosed Y) (hconv : Convex ℝ Y)
    (h0 : (0 : Fin L → ℝ) ∈ Y) (hnfl : ∀ y ∈ Y, (∀ l, 0 ≤ y l) → y = 0) (ω : Fin L → ℝ) :
    IsCompact {z | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} := by
  have hclosed : IsClosed {z : Fin L → ℝ | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} :=
    (hc.preimage (continuous_id.sub continuous_const)).inter isClosed_nonnegOrthant
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ z, (z - ω ∈ Y ∧ ∀ l, 0 ≤ z l) ∧ (n : ℝ) + 1 + ‖ω‖ < ‖z‖ := by
    intro n
    obtain ⟨z, hz, hzb⟩ := Set.not_subset.mp (hno ((n : ℝ) + 1 + ‖ω‖))
    refine ⟨z, hz, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hzb
  choose z hz hbig using hex
  set c : ℕ → Fin L → ℝ := fun n => z n - ω with hcdef
  set s : ℕ → ℝ := fun n => ‖c n‖ with hs
  have hs1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ s n := fun n => by
    have h1 := hbig n
    have h2 := norm_sub_norm_le (z n) ω
    simp only [hs, hcdef]
    linarith
  have hs1' : ∀ n, 1 ≤ s n := fun n => by linarith [hs1 n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1' n]
  have hwS : ∀ n, (s n)⁻¹ • c n ∈ Metric.sphere (0 : Fin L → ℝ) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
      (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith [hs1 (φ n)]
  have hdY : d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0 (fun n => (hz (φ n)).1)
    (fun n => hs1' (φ n)) hlim
  have hdnn : ∀ l, 0 ≤ d l := by
    intro l
    have hcoord : Tendsto (fun n => (s (φ n))⁻¹ * c (φ n) l) atTop (𝓝 (d l)) := by
      have := ((continuous_apply l).continuousAt.tendsto).comp hlim
      simpa [Function.comp_def] using this
    have hlow : Tendsto (fun n => (s (φ n))⁻¹ * -ω l) atTop (𝓝 0) := by
      simpa using hinv.mul_const (-ω l)
    refine le_of_tendsto_of_tendsto hlow hcoord (Eventually.of_forall fun n => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (hspos _).le)
    simp only [hcdef, Pi.sub_apply]
    linarith [(hz (φ n)).2 l]
  have := hnfl d hdY hdnn
  rw [this, mem_sphere_zero_iff_norm, norm_zero] at hdS
  exact zero_ne_one hdS

/-- **Exercise 16.AA.2** (MWG, p. 577): closedness of `Y` is indispensable. `Y = (-1, 0] ⊆ ℝ`
is convex, contains `0` and has no free lunch, but `(Y + {1}) ∩ ℝ₊ = (0, 1]` is not compact. -/
theorem exercise_16_AA_2_needs_closed :
    Convex ℝ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧ (0 : Fin 1 → ℝ) ∈ {y | -1 < y 0 ∧ y 0 ≤ 0} ∧
      (∀ y ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0}, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 1 → ℝ | z - ![1] ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧
        ∀ l, 0 ≤ z l} := by
  refine ⟨?_, by simp, fun y hy hnn => funext fun l => ?_, fun hK => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    constructor
    · rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_lt_mul_of_pos_left hx.1 ha', mul_le_mul_of_nonneg_left hy.1.le hb]
      · subst ha'
        have hb1 : b = 1 := by linarith
        subst hb1
        simpa using hy.1
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx.2, mul_nonpos_of_nonneg_of_nonpos hb hy.2]
  · fin_cases l; exact le_antisymm hy.2 (hnn 0)
  · have hmem : ∀ n : ℕ, (![1 / ((n : ℝ) + 1)] : Fin 1 → ℝ) ∈ {z : Fin 1 → ℝ |
        z - ![1] ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧ ∀ l, 0 ≤ z l} := fun n => by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      refine ⟨⟨?_, ?_⟩, fun l => ?_⟩
      · change -1 < 1 / ((n : ℝ) + 1) - 1; linarith
      · change 1 / ((n : ℝ) + 1) - 1 ≤ 0; linarith
      · fin_cases l; exact hpos.le
    have ht : Tendsto (fun n : ℕ => (![1 / ((n : ℝ) + 1)] : Fin 1 → ℝ)) atTop (𝓝 0) := by
      rw [tendsto_pi_nhds]
      intro l; fin_cases l
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have := hK.isClosed.mem_of_tendsto ht (Eventually.of_forall hmem)
    simp at this

/-- **Exercise 16.AA.2** (MWG, p. 577): convexity of `Y` is indispensable. The closed set
`aaY1 = {0} ∪ {(a, b) : a ≥ 0, ab ≤ -1}` contains `0` and has no free lunch, but
`(Y + {(1, 1)}) ∩ ℝ²₊` is unbounded. -/
theorem exercise_16_AA_2_needs_convex :
    IsClosed aaY1 ∧ (0 : Fin 2 → ℝ) ∈ aaY1 ∧ (∀ y ∈ aaY1, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 2 → ℝ | z - ![1, 1] ∈ aaY1 ∧ ∀ l, 0 ≤ z l} := by
  have hclosed := (proposition_16_AA_1_counterexample.2.2.1 0)
  refine ⟨hclosed, Or.inl rfl, fun y hy hnn => ?_, fun hK => ?_⟩
  · rcases hy with h | ⟨-, h⟩
    · exact h
    · nlinarith [mul_nonneg (hnn 0) (hnn 1)]
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    set t := max R 1 + 1 with ht
    have ht1 : 1 < t := by linarith [le_max_right R 1]
    have hmem : (![1 + t, 0] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | z - ![1, 1] ∈ aaY1 ∧
        ∀ l, 0 ≤ z l} := by
      refine ⟨Or.inr ⟨by simp; linarith, by simp; linarith⟩, fun l => ?_⟩
      fin_cases l
      · simp; linarith
      · simp
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |(![1 + t, 0] : Fin 2 → ℝ) 0| ≤ ‖(![1 + t, 0] : Fin 2 → ℝ)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    simp only [Matrix.cons_val_zero] at h2
    rw [abs_of_pos (by linarith)] at h2
    linarith [le_max_left R 1]

/-- **Exercise 16.AA.2** (MWG, p. 577): `0 ∈ Y` is indispensable. `Y = {y : y₂ ≤ -1}` is closed
and convex with `Y ∩ ℝ²₊ = ∅`, but `(Y + {(1, 1)}) ∩ ℝ²₊` is unbounded. -/
theorem exercise_16_AA_2_needs_zero :
    IsClosed {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ Convex ℝ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧
      (0 : Fin 2 → ℝ) ∉ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧
      (∀ y ∈ {y : Fin 2 → ℝ | y 1 ≤ -1}, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 2 → ℝ | z - ![1, 1] ∈ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ ∀ l, 0 ≤ z l} := by
  refine ⟨isClosed_le (continuous_apply 1) continuous_const, ?_, by simp, fun y hy hnn => ?_,
    fun hK => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    nlinarith
  · exact absurd (hnn 1) (by simp only [Set.mem_ofPred_eq] at hy; linarith)
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    set t := max R 1 + 1 with ht
    have hmem : (![t, 0] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ |
        z - ![1, 1] ∈ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ ∀ l, 0 ≤ z l} := by
      refine ⟨by simp, fun l => ?_⟩
      fin_cases l <;> simp; linarith [le_max_right R 1]
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |(![t, 0] : Fin 2 → ℝ) 0| ≤ ‖(![t, 0] : Fin 2 → ℝ)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    simp only [Matrix.cons_val_zero] at h2
    rw [abs_of_pos (by linarith [le_max_right R 1])] at h2
    linarith [le_max_left R 1]

/-- **Exercise 16.AA.2** (MWG, p. 577): no free lunch is indispensable. `Y = ℝ` is closed and
convex with `0 ∈ Y`, and `(Y + {1}) ∩ ℝ₊ = ℝ₊` is unbounded. -/
theorem exercise_16_AA_2_needs_no_free_lunch :
    ¬ IsCompact {z : Fin 1 → ℝ | z - ![1] ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ ∀ l, 0 ≤ z l} := by
  intro hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set t := max R 1 + 1 with ht
  have hmem : (![t] : Fin 1 → ℝ) ∈ {z : Fin 1 → ℝ | z - ![1] ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧
      ∀ l, 0 ≤ z l} := ⟨trivial, fun l => by fin_cases l; simp; linarith [le_max_right R 1]⟩
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : |(![t] : Fin 1 → ℝ) 0| ≤ ‖(![t] : Fin 1 → ℝ)‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
  simp only [Matrix.cons_val_zero] at h2
  rw [abs_of_pos (by linarith [le_max_right R 1])] at h2
  linarith [le_max_left R 1]

/-! ## Exercise 16.AA.3 -/

/-- **Exercise 16.AA.3** (MWG, p. 577). If `Y = Y₁ + Y₂` satisfies the assumptions of Exercise
16.AA.2 (closed, convex, no free lunch), `0 ∈ Y₁`, `0 ∈ Y₂` and `Y` is irreversible, then the set
`{y₁ ∈ Y₁ : y₁ + y₂ + ω̄ ≥ 0 for some y₂ ∈ Y₂}` is bounded. -/
theorem exercise_16_AA_3 {Y₁ Y₂ : Set (Fin L → ℝ)}
    (hc : IsClosed {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂})
    (hconv : Convex ℝ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂})
    (hnfl : ∀ y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂}, (∀ l, 0 ≤ y l) → y = 0)
    (h01 : (0 : Fin L → ℝ) ∈ Y₁) (h02 : (0 : Fin L → ℝ) ∈ Y₂)
    (hirr : ∀ y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂},
      -y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂} → y = 0) (ω : Fin L → ℝ) :
    Bornology.IsBounded {y₁ | y₁ ∈ Y₁ ∧ ∃ y₂ ∈ Y₂, ∀ l, 0 ≤ (y₁ + y₂ + ω) l} := by
  set Y := {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂} with hY
  have h0 : (0 : Fin L → ℝ) ∈ Y := ⟨0, h01, 0, h02, by simp⟩
  -- the aggregate plans are bounded (Exercise 16.AA.2)
  obtain ⟨M, hM⟩ := (exercise_16_AA_2 hc hconv h0 hnfl ω).isBounded.subset_closedBall 0
  rw [Metric.isBounded_iff_subset_closedBall 0]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ y₁, (y₁ ∈ Y₁ ∧ ∃ y₂ ∈ Y₂, ∀ l, 0 ≤ (y₁ + y₂ + ω) l) ∧
      (n : ℝ) + 1 < ‖y₁‖ := by
    intro n
    obtain ⟨y, hy, hyb⟩ := Set.not_subset.mp (hno ((n : ℝ) + 1))
    exact ⟨y, hy, by simpa [Metric.mem_closedBall, dist_zero_right] using hyb⟩
  choose y₁ hy₁ hbig using hex
  choose hy₁Y y₂ hy₂Y hnn using hy₁
  set s : ℕ → ℝ := fun n => ‖y₁ n‖ with hs
  have hs1 : ∀ n, 1 ≤ s n := fun n => by
    have := hbig n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; simp only [hs]; linarith
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1 n]
  have hwS : ∀ n, (s n)⁻¹ • y₁ n ∈ Metric.sphere (0 : Fin L → ℝ) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have := hbig (φ n)
    simp only [hs]
    linarith
  -- the aggregate `y₁ + y₂` stays bounded, so `y₂ / s → -d`
  have hagg : ∀ n, ‖y₁ n + y₂ n‖ ≤ M + ‖ω‖ := by
    intro n
    have hmem : y₁ n + y₂ n + ω ∈ {z | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} :=
      ⟨⟨y₁ n, hy₁Y n, y₂ n, hy₂Y n, by abel⟩, hnn n⟩
    have h1 := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := norm_sub_le (y₁ n + y₂ n + ω) ω
    rw [add_sub_cancel_right] at h2
    linarith [norm_nonneg ω]
  have haggt : Tendsto (fun n => (s (φ n))⁻¹ • (y₁ (φ n) + y₂ (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hinv.mul_const (M + ‖ω‖))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hspos _))]
    exact mul_le_mul_of_nonneg_left (hagg _) (inv_nonneg.mpr (hspos _).le)
  have hy2t : Tendsto (fun n => (s (φ n))⁻¹ • y₂ (φ n)) atTop (𝓝 (-d)) := by
    have := haggt.sub hlim
    rw [zero_sub] at this
    refine this.congr fun n => ?_
    simp [smul_add]
  have hdY : d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0
    (c := fun n => y₁ (φ n)) (fun n => ⟨y₁ (φ n), hy₁Y _, 0, h02, by simp⟩)
    (fun n => hs1 (φ n)) hlim
  have hndY : -d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0
    (c := fun n => y₂ (φ n)) (fun n => ⟨0, h01, y₂ (φ n), hy₂Y _, by simp⟩)
    (fun n => hs1 (φ n)) hy2t
  have := hirr d hdY hndY
  rw [this, mem_sphere_zero_iff_norm, norm_zero] at hdS
  exact zero_ne_one hdS

/-! ## Proposition 16.AA.2 -/

/-- **Proposition 16.AA.2** (MWG, p. 574). If the set `A` of feasible allocations is nonempty
and compact and every `uᵢ` is continuous on `Xᵢ`, the utility possibility set `U` is closed and
bounded above. -/
theorem proposition_16_AA_2 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hA : IsCompact (PrefEconomy.ofUtility X u Y ω).feasiblePairs)
    (hu : ∀ i, ContinuousOn (u i) (X i)) :
    IsClosed (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) ∧
      BddAbove (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  set A := (PrefEconomy.ofUtility X u Y ω).feasiblePairs with hAdef
  set F : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) → ι → ℝ := fun z i => u i (z.1 i) with hF
  have hFc : ContinuousOn F A := by
    refine continuousOn_pi.mpr fun i => ?_
    refine (hu i).comp ((continuous_apply i).comp continuous_fst).continuousOn fun z hz => ?_
    exact hz.1.1 i
  have hU : utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u =
      {v | ∃ z ∈ A, v ≤ F z} := by
    ext v
    constructor
    · rintro ⟨a, ha, hv⟩; exact ⟨(a.x, a.y), ha, hv⟩
    · rintro ⟨z, hz, hv⟩; exact ⟨⟨z.1, z.2⟩, hz, hv⟩
  rw [hU]
  have hK : IsCompact (F '' A) := hA.image_of_continuousOn hFc
  refine ⟨?_, ?_⟩
  · refine IsSeqClosed.isClosed fun v w hv hvw => ?_
    choose z hz hle using hv
    obtain ⟨z', hz', φ, hφ, hlim⟩ := hA.tendsto_subseq hz
    refine ⟨z', hz', fun i => ?_⟩
    have hF' : Tendsto (fun n => F (z (φ n))) atTop (𝓝 (F z')) :=
      ((hFc z' hz').tendsto).comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall fun n => hz (φ n)⟩)
    have h1 : Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i)) :=
      ((continuous_apply i).tendsto w).comp (hvw.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun n => F (z (φ n)) i) atTop (𝓝 (F z' i)) :=
      ((continuous_apply i).tendsto _).comp hF'
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => hle (φ n) i
  · obtain ⟨b, hb⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨fun _ => b, ?_⟩
    rintro v ⟨z, hz, hv⟩ i
    have h1 := hb ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |F z i| ≤ ‖F z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
    exact (hv i).trans ((le_abs_self _).trans (h2.trans h1))

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Fritz John conditions (tool for MWG Section 16.F)

Section 16.F appeals to the Kuhn-Tucker conditions of Section M.K for problem (16.F.1), whose
constraint qualification (footnote 18) is not of the linear-independence form proved in
Chapter 3 (`theorem_M_K_2`): at a solution with `x₁ = 0` the binding constraint gradients can be
dependent. We prove the Fritz John conditions for inequality-constrained problems on any real
normed space, assuming only differentiability at the solution: at a local maximizer `z` of `f` on
`{v : gₖ(v) ≤ 0 ∀ k}` there are `λ₀ ≥ 0`, `λₖ ≥ 0`, not all zero, with `λₖ gₖ(z) = 0` and
`λ₀ Df(z) = ∑ₖ λₖ Dgₖ(z)`. The proof: no direction strictly improves `f` while strictly decreasing
every binding constraint, and Gordan's alternative (separation of the open positive orthant from
the range of the derivative map, Mathlib's geometric Hahn-Banach theorem) gives the multipliers.
Section 16.F's normalization `δ₁ = 1` is derived in `FirstOrder` from the strictly positive
gradients.
-/

namespace MWG.WelfareTheorems

open Filter Topology

/-- No direction `d` strictly raises `f` and strictly lowers every binding constraint at a local
constrained maximizer (all functions differentiable at `z`). -/
theorem no_improving_direction {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Finite K] {f : V → ℝ} {g : K → V → ℝ} {f' : V →L[ℝ] ℝ} {g' : K → V →L[ℝ] ℝ} {z : V}
    (hz : ∀ k, g k z ≤ 0) (hmax : IsLocalMaxOn f {v | ∀ k, g k v ≤ 0} z)
    (hf : HasFDerivAt f f' z) (hg : ∀ k, HasFDerivAt (g k) (g' k) z) (d : V)
    (hfd : 0 < f' d) (hgd : ∀ k, g k z = 0 → g' k d < 0) : False := by
  have hline : ∀ {φ : V → ℝ} {φ' : V →L[ℝ] ℝ}, HasFDerivAt φ φ' z →
      HasDerivAt (fun t : ℝ => φ (z + t • d)) (φ' d) 0 := by
    intro φ φ' hφ
    have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
    have h2 : HasFDerivAt φ φ' (z + (0 : ℝ) • d) := by simpa using hφ
    exact h2.comp_hasDerivAt 0 h1
  -- `f` increases along `d`
  have hup : ∀ᶠ t in 𝓝[>] (0 : ℝ), f z < f (z + t • d) := by
    have := MWG.ClassicalDemand.mk_eventually_gt_of_deriv_pos (hline hf) hfd
    simpa using this
  -- every constraint stays satisfied along `d`
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, g k (z + t • d) ≤ 0 := by
    rw [eventually_all]
    intro k
    rcases (hz k).lt_or_eq with hk | hk
    · have hc : ContinuousAt (fun t : ℝ => g k (z + t • d)) 0 := (hline (hg k)).continuousAt
      have := hc.eventually (gt_mem_nhds (show g k (z + (0 : ℝ) • d) < 0 by simpa using hk))
      exact (eventually_nhdsWithin_of_eventually_nhds this).mono fun t ht => ht.le
    · have hneg : HasDerivAt (fun t : ℝ => -g k (z + t • d)) (-(g' k d)) 0 :=
        (hline (hg k)).neg
      have := MWG.ClassicalDemand.mk_eventually_gt_of_deriv_pos hneg
        (by linarith [hgd k hk])
      refine this.mono fun t ht => ?_
      simp only [zero_smul, add_zero, hk, neg_zero] at ht
      linarith
  -- the path tends to `z` within the constraint set
  have htend : Tendsto (fun t : ℝ => z + t • d) (𝓝[>] 0) (𝓝[{v | ∀ k, g k v ≤ 0}] z) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hfeas⟩
    have : Continuous fun t : ℝ => z + t • d := by fun_prop
    have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h0
  have hle := htend.eventually hmax
  obtain ⟨t, ht1, ht2⟩ := (hup.and hle).exists
  linarith

/-- **The Fritz John conditions.** If `z` is a local maximizer of `f` on `{v : gₖ(v) ≤ 0 ∀ k}`
(finitely many constraints) and `f`, `gₖ` are differentiable at `z`, there are `λ₀ ≥ 0` and
`λₖ ≥ 0`, not all zero, with complementary slackness `λₖ gₖ(z) = 0` and
`λ₀ Df(z) = ∑ₖ λₖ Dgₖ(z)`. -/
theorem fritz_john {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype K]
    {f : V → ℝ} {g : K → V → ℝ} {f' : V →L[ℝ] ℝ} {g' : K → V →L[ℝ] ℝ} {z : V}
    (hz : ∀ k, g k z ≤ 0) (hmax : IsLocalMaxOn f {v | ∀ k, g k v ≤ 0} z)
    (hf : HasFDerivAt f f' z) (hg : ∀ k, HasFDerivAt (g k) (g' k) z) :
    ∃ (l0 : ℝ) (l : K → ℝ), 0 ≤ l0 ∧ (∀ k, 0 ≤ l k) ∧ (l0 ≠ 0 ∨ ∃ k, l k ≠ 0) ∧
      (∀ k, l k * g k z = 0) ∧ l0 • f' = ∑ k, l k • g' k := by
  classical
  -- the derivative map into `ℝ^{1 + A}`, `A` the binding constraints
  set A := {k // g k z = 0}
  set T : V →L[ℝ] (Option A → ℝ) := ContinuousLinearMap.pi fun o => match o with
    | none => f'
    | some k => -g' k.1 with hT
  have hTnone : ∀ d, T d none = f' d := fun d => rfl
  have hTsome : ∀ d (k : A), T d (some k) = -g' k.1 d := fun d k => rfl
  set P : Set (Option A → ℝ) := {w | ∀ o, 0 < w o} with hP
  have hPopen : IsOpen P := by
    have : P = ⋂ o, {w : Option A → ℝ | 0 < w o} := by ext w; simp [hP]
    rw [this]
    exact isOpen_iInter_of_finite fun o => isOpen_lt continuous_const (continuous_apply o)
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab o
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' (hx o), mul_nonneg hb (hy o).le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy o
  have hdisj : Disjoint P (Set.range T) := by
    rw [Set.disjoint_left]
    rintro w hw ⟨d, rfl⟩
    refine no_improving_direction hz hmax hf hg d (by simpa [hTnone] using hw none)
      fun k hk => ?_
    have := hw (some ⟨k, hk⟩)
    rw [hTsome] at this
    change 0 < -(g' k d) at this
    linarith
  have hconvR : Convex ℝ (Set.range T) := by
    have := (convex_univ : Convex ℝ (Set.univ : Set V)).linear_image T.toLinearMap
    simpa [Set.image_univ] using this
  obtain ⟨φ, u, hφP, hφR⟩ := geometric_hahn_banach_open hPconv hPopen hconvR hdisj
  set c : Option A → ℝ := fun o => φ (Pi.single o 1) with hc
  have hφ : ∀ w, φ w = ∑ o, c o * w o := fun w => strongDual_apply_eq_sum φ w
  -- `φ` vanishes on the range of `T`, and `u ≤ 0`
  have hφT : ∀ d, φ (T d) = 0 := by
    intro d
    by_contra hne
    set s := φ (T d) with hs
    have h1 := hφR (T (((u - 1) / s) • d)) ⟨_, rfl⟩
    rw [map_smul, map_smul, smul_eq_mul, ← hs, div_mul_cancel₀ _ hne] at h1
    linarith
  -- `c ≤ 0` and `c ≠ 0`
  have hc_nonpos : ∀ o, c o ≤ 0 := by
    intro o
    by_contra hpos
    push Not at hpos
    set S := ∑ o', |c o'| with hS
    set t := (S + 1) / c o + 1 with ht
    have ht0 : 0 < t := by positivity
    set w : Option A → ℝ := fun o' => if o' = o then t else 1 with hw
    have hwP : w ∈ P := fun o' => by simp only [hw]; split_ifs <;> linarith
    have h1 := hφP w hwP
    rw [hφ] at h1
    have h2 : ∑ o', c o' * w o' = c o * t + ∑ o' ∈ Finset.univ.erase o, c o' := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
      congr 1
      · simp [hw]
      · exact Finset.sum_congr rfl fun o' ho' => by
          simp [hw, Finset.ne_of_mem_erase ho']
    have h3 : -S ≤ ∑ o' ∈ Finset.univ.erase o, c o' := by
      rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
      have : -(∑ o' ∈ Finset.univ.erase o, |c o'|) ≤ ∑ o' ∈ Finset.univ.erase o, c o' := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun o' _ => neg_abs_le _
      linarith [abs_nonneg (c o)]
    have h4 : c o * t = S + 1 + c o := by rw [ht]; field_simp
    have hu0 : u ≤ 0 := by simpa using hφR 0 ⟨0, map_zero T⟩
    rw [h2] at h1
    linarith
  have hc_ne : ∃ o, c o ≠ 0 := by
    by_contra hall
    push Not at hall
    have := hφP (fun _ => 1) (fun _ => one_pos)
    have hu0 : u ≤ 0 := by simpa using hφR 0 ⟨0, map_zero T⟩
    rw [hφ] at this
    simp [hall] at this
    linarith
  set l : K → ℝ := fun k => if h : g k z = 0 then -c (some ⟨k, h⟩) else 0 with hl
  refine ⟨-c none, l, by linarith [hc_nonpos none], fun k => ?_, ?_, fun k => ?_, ?_⟩
  · simp only [hl]
    split_ifs with h
    · linarith [hc_nonpos (some ⟨k, h⟩)]
    · exact le_rfl
  · obtain ⟨o, ho⟩ := hc_ne
    cases o with
    | none => exact Or.inl (neg_ne_zero.mpr ho)
    | some k =>
      right
      refine ⟨k.1, ?_⟩
      simp only [hl, k.2, ↓reduceDIte]
      exact neg_ne_zero.mpr ho
  · simp only [hl]
    split_ifs with h
    · rw [h, mul_zero]
    · rw [zero_mul]
  · -- the multiplier identity from `φ ∘ T = 0`
    ext d
    have h1 := hφT d
    rw [hφ, Fintype.sum_option, hTnone] at h1
    change -c none * f' d = (∑ k, l k • g' k) d
    rw [sum_apply]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h2 : ∑ k, l k * g' k d = ∑ k : A, -c (some k) * g' k.1 d := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun k => g k z = 0) (fun k => l k * g' k d)]
      have h3 : ∑ k : {k // ¬ g k z = 0}, l k.1 * g' k.1 d = 0 :=
        Finset.sum_eq_zero fun k _ => by simp [hl, k.2]
      rw [h3, add_zero]
      exact Finset.sum_congr rfl fun k _ => by simp [hl, k.2]
    rw [h2]
    have h4 : ∀ k : A, c (some k) * T d (some k) = -(c (some k) * g' k.1 d) := fun k => by
      rw [hTsome]; ring
    simp only [h4, Finset.sum_neg_distrib] at h1
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order conditions for Pareto optimality (MWG Section 16.F, pp. 561-566)

The setting of Section 16.F: `Xᵢ = ℝ^L₊`, utilities `uᵢ` with `∇uᵢ ≫ 0`, `uᵢ(0) = 0`, production
sets `Yⱼ = {y : Fⱼ(y) ≤ 0}` with `∇Fⱼ ≫ 0` and `Fⱼ(0) ≤ 0`. Departure: the book takes the `uᵢ`
twice continuously differentiable on `ℝ^L₊`; we take functions on `ℝ^L` and assume exactly the
differentiability each statement uses (often only at the allocation in question).

* With `∇u ≫ 0` everywhere, `u` is strongly monotone (p. 562), and with `∇F ≫ 0` the set
  `{F ≤ 0}` has free disposal (footnote 17).
* Problem (16.F.1) (`Problem16F1`); **Exercise 16.F.1**: its solutions are Pareto optimal, and
  every Pareto optimum solves it for the utility levels it gives (with continuous, strongly
  monotone utilities and `J ≥ 1`).
* **Exercise 16.F.2**: the Kuhn-Tucker conditions (16.F.2)-(16.F.3), with `δ₁ = 1`, at every
  solution of (16.F.1) (`J ≥ 1`, `L ≥ 1`), derived from the Fritz John conditions; footnote 18's
  constraint qualification claim is replaced by a direct argument covering solutions with
  `x₁ = 0`.
* **Exercise 16.F.3**: at interior solutions, (16.F.2)-(16.F.3) give (16.F.4)-(16.F.6).
* The correspondences of (16.F.2)-(16.F.3) with (16.F.10)-(16.F.11) and (16.F.13)-(16.F.14).
* p. 565: with quasiconcave `uᵢ` and convex `Fⱼ`, the first-order conditions make the allocation a
  price equilibrium with transfers at `p = μ` (and conversely by the first welfare theorem).
* **Proposition 16.F.1**: with concave `uᵢ` and convex `Fⱼ`, every Pareto optimum maximizes
  `∑ᵢ λᵢ uᵢ(xᵢ)` subject to the resource and technology constraints, with `λᵢ = δᵢ` the reciprocal
  of `i`'s marginal utility of wealth at the supporting prices (when `δᵢ > 0`; `δᵢ = 0` only for
  consumers with `xᵢ = 0`).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- A linear functional on `ℝ^L` applied to `d` is `∑ₗ dₗ ∂ₗ`. -/
theorem clm_apply_eq_sum_partials (φ : (Fin L → ℝ) →L[ℝ] ℝ) (d : Fin L → ℝ) :
    φ d = ∑ l, φ (Pi.single l 1) * d l :=
  strongDual_apply_eq_sum φ d

/-- A positive gradient gives a positive derivative in every direction `d ≥ 0`, `d ≠ 0`. -/
theorem clm_pos_of_partials_pos {φ : (Fin L → ℝ) →L[ℝ] ℝ} (hφ : ∀ l, 0 < φ (Pi.single l 1))
    {d : Fin L → ℝ} (hd : ∀ l, 0 ≤ d l) (hne : d ≠ 0) : 0 < φ d := by
  rw [clm_apply_eq_sum_partials]
  obtain ⟨l, hl⟩ : ∃ l, d l ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  exact lt_of_lt_of_le (mul_pos (hφ l) (lt_of_le_of_ne (hd l) (Ne.symm hl)))
    (Finset.single_le_sum (f := fun k => φ (Pi.single k 1) * d k)
      (fun k _ => mul_nonneg (hφ k).le (hd k)) (Finset.mem_univ l))

/-- **Section 16.F** (MWG, p. 562). A function on `ℝ^L` with `∇u ≫ 0` everywhere is strictly
increasing: `x ≤ y`, `x ≠ y` imply `u(x) < u(y)` (hence the preference is strongly monotone). -/
theorem strictMono_of_grad_pos {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hpos : ∀ x l, 0 < u' x (Pi.single l 1))
    {x y : Fin L → ℝ} (hxy : x ≤ y) (hne : x ≠ y) : u x < u y := by
  set d := y - x with hd
  have hd0 : ∀ l, 0 ≤ d l := fun l => by simp [hd, hxy l]
  have hdne : d ≠ 0 := fun h => hne (by rw [sub_eq_zero] at h; exact h.symm)
  set g : ℝ → ℝ := fun t => u (x + t • d) with hg
  have hgd : ∀ t, HasDerivAt g (u' (x + t • d) d) t := fun t => mc_line_hasDerivAt_at (hu _)
  have hmono : StrictMonoOn g (Set.Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t _ => (hgd t).continuousAt.continuousWithinAt) fun t _ => ?_
    rw [(hgd t).deriv]
    exact clm_pos_of_partials_pos (hpos _) hd0 hdne
  have := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  simpa [hg, hd] using this

/-- **Footnote 17** (MWG, p. 562). With `∇F ≫ 0` everywhere, `F` is nondecreasing, so
`{F ≤ 0}` satisfies free disposal. -/
theorem mono_of_grad_pos {F : (Fin L → ℝ) → ℝ} {F' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ∀ y, HasFDerivAt F (F' y) y) (hpos : ∀ y l, 0 < F' y (Pi.single l 1))
    {x y : Fin L → ℝ} (hxy : x ≤ y) : F x ≤ F y := by
  by_cases h : x = y
  · rw [h]
  · exact (strictMono_of_grad_pos hF hpos hxy h).le

/-- **Problem (16.F.1)** (MWG, p. 562), its constraint set: utility requirements `uᵢ(xᵢ) ≥ ūᵢ`
for `i ≠ i₀`, resource constraints `∑ᵢ x_{ℓi} ≤ ω̄ₗ + ∑ⱼ y_{ℓj}`, technology `Fⱼ(yⱼ) ≤ 0` and
`xᵢ ≥ 0`. -/
def Problem16F1 (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ) (i₀ : ι)
    (ub : ι → ℝ) : Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) :=
  {v | (∀ i, i ≠ i₀ → ub i ≤ u i (v.1 i)) ∧ (∀ l, ∑ i, v.1 i l ≤ ω l + ∑ j, v.2 j l) ∧
    (∀ j, F j (v.2 j) ≤ 0) ∧ ∀ i l, 0 ≤ v.1 i l}

/-- **Problem (16.F.1)** (MWG, p. 562): `v` maximizes `u_{i₀}(x_{i₀})` on the constraint set. -/
def IsSolution16F1 (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ)
    (i₀ : ι) (ub : ι → ℝ) (v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)) : Prop :=
  v ∈ Problem16F1 u F ω i₀ ub ∧ ∀ v' ∈ Problem16F1 u F ω i₀ ub, u i₀ (v'.1 i₀) ≤ u i₀ (v.1 i₀)

/-- **Section 16.F** (MWG, p. 562). The economy of Section 16.F: `Xᵢ = ℝ^L₊`, utilities `uᵢ`,
production sets `{Fⱼ ≤ 0}`. -/
def economy16F (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ) :
    PrefEconomy ι κ L :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u (fun j => {y | F j y ≤ 0}) ω

/-- Giving `δ` more of good `l` to consumer `i₀` keeps a point of (16.F.1) feasible after the same
amount is freed by another consumer or by slack. -/
theorem single_nonneg_add {x : Fin L → ℝ} (hx : ∀ l, 0 ≤ x l) (l : Fin L) {δ : ℝ}
    (hδ : 0 ≤ δ) : ∀ m, 0 ≤ (x + (Pi.single l δ : Fin L → ℝ)) m := fun m => by
  by_cases hm : m = l
  · subst hm; simp only [Pi.add_apply, Pi.single_eq_same]; linarith [hx m]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hm, add_zero]; exact hx m

/-- **Section 16.F** (MWG, p. 563). With strongly monotone `u_{i₀}`, every solution of (16.F.1)
has binding resource constraints. -/
theorem solution16F1_resources_bind {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    (hmono : PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i₀)))
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v) :
    ∀ l, ∑ i, v.1 i l = ω l + ∑ j, v.2 j l := by
  classical
  intro l
  by_contra hne
  have hlt : ∑ i, v.1 i l < ω l + ∑ j, v.2 j l := lt_of_le_of_ne (hv.1.2.1 l) hne
  set δ := ω l + ∑ j, v.2 j l - ∑ i, v.1 i l with hδ
  have hδ0 : 0 < δ := by linarith
  set x' : ι → Fin L → ℝ := Function.update v.1 i₀ (v.1 i₀ + Pi.single l δ) with hx'
  have hx'i₀ : x' i₀ = v.1 i₀ + Pi.single l δ := by simp [hx']
  have hmem : (x', v.2) ∈ Problem16F1 u F ω i₀ ub := by
    refine ⟨fun i hi => ?_, fun m => ?_, hv.1.2.2.1, fun i m => ?_⟩
    · simpa [hx', hi] using hv.1.1 i hi
    · have hsum : ∑ i, x' i m = ∑ i, v.1 i m + (Pi.single l δ : Fin L → ℝ) m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => v.1 i m) (Finset.mem_univ i₀), hx'i₀]
        have : ∑ i ∈ Finset.univ.erase i₀, x' i m = ∑ i ∈ Finset.univ.erase i₀, v.1 i m :=
          Finset.sum_congr rfl fun i hi => by simp [hx', Finset.ne_of_mem_erase hi]
        rw [this, Pi.add_apply]; ring
      rw [hsum]
      by_cases hm : m = l
      · subst hm; simp [hδ]
      · simpa [hm] using hv.1.2.1 m
    · change 0 ≤ x' i m
      by_cases hi : i = i₀
      · rw [hi, hx'i₀]; exact single_nonneg_add (hv.1.2.2.2 i₀) l hδ0.le m
      · simpa [hx', hi] using hv.1.2.2.2 i m
  have hgt : u i₀ (v.1 i₀) < u i₀ (x' i₀) := by
    rw [hx'i₀]
    refine not_le.mp (hmono _ (hv.1.2.2.2 i₀) _ (single_nonneg_add (hv.1.2.2.2 i₀) l hδ0.le)
      (fun m => ?_) ?_).2
    · by_cases hm : m = l
      · subst hm; simp; linarith
      · simp [hm]
    · intro h
      have := congrFun h l
      simp at this
      linarith
  exact absurd (hv.2 _ hmem) (not_le.mpr hgt)

/-- **Exercise 16.F.1** (MWG, p. 562), first part. With utilities continuous and strongly monotone
on `ℝ^L₊`, every solution of (16.F.1) is a Pareto optimal allocation of the economy of Section
16.F (resource constraints bind, so (16.B.1) holds). -/
theorem exercise_16_F_1_i {u : ι → (Fin L → ℝ) → ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v) :
    (economy16F u F ω).IsParetoOptimal ⟨v.1, v.2⟩ := by
  classical
  have hbind := solution16F1_resources_bind (hmono i₀) hv
  have hfeas : (economy16F u F ω).IsFeasible ⟨v.1, v.2⟩ :=
    ⟨⟨fun i => hv.1.2.2.2 i, fun j => hv.1.2.2.1 j⟩, funext fun l => by
      simpa [Finset.sum_apply, economy16F, PrefEconomy.ofUtility] using hbind l⟩
  refine ⟨hfeas, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hle' : ∀ i, u i (v.1 i) ≤ u i (a'.x i) := hle
  have hlt : u k (v.1 k) < u k (a'.x k) := not_le.mp hk.2
  have hx'X : ∀ i, a'.x i ∈ nonnegOrthant L := hx'
  -- `(x', y')` satisfies the constraints of (16.F.1)
  have hcons : ∀ x'' : ι → Fin L → ℝ, (∀ i, x'' i ∈ nonnegOrthant L) →
      ∑ i, x'' i = ∑ i, a'.x i → (∀ i, i ≠ i₀ → u i (v.1 i) ≤ u i (x'' i)) →
      (x'', a'.y) ∈ Problem16F1 u F ω i₀ ub := by
    intro x'' hx'' hsum hu
    refine ⟨fun i hi => (hv.1.1 i hi).trans (hu i hi), fun l => ?_, hy', fun i l => hx'' i l⟩
    have := congrFun (hsum.trans hc') l
    simp only [Finset.sum_apply, Pi.add_apply, economy16F, PrefEconomy.ofUtility] at this
    rw [this]
  by_cases hk0 : k = i₀
  · subst hk0
    have := hv.2 _ (hcons a'.x hx'X rfl fun i _ => hle' i)
    linarith
  -- move a little of a good from `k` to `i₀`
  obtain ⟨l, hl⟩ : ∃ l, 0 < a'.x k l := by
    by_contra hall
    push Not at hall
    have h0 : a'.x k = 0 := funext fun l => le_antisymm (hall l) (hx'X k l)
    have := utility_mono_of_strongMono (hmono k) (x := 0) (y := v.1 k) (fun _ => le_rfl)
      (fun l => hv.1.2.2.2 k l)
    rw [h0] at hlt
    linarith
  obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single (rationalOn_utilityPref _ (u k))
    (prefContinuous_utilityPref (hcont k)) (hx'X k) (fun m => hv.1.2.2.2 k m) hk hl
  set x'' : ι → Fin L → ℝ := fun i =>
    if i = i₀ then a'.x i + Pi.single l δ else if i = k then a'.x i - Pi.single l δ else a'.x i
    with hx''
  have hx''i₀ : x'' i₀ = a'.x i₀ + Pi.single l δ := by simp [hx'']
  have hx''k : x'' k = a'.x k - Pi.single l δ := by simp [hx'', hk0]
  have hx''X : ∀ i, x'' i ∈ nonnegOrthant L := by
    intro i
    by_cases h1 : i = i₀
    · subst h1; rw [hx''i₀]; exact single_nonneg_add (hx'X _) l hδ.le
    · by_cases h2 : i = k
      · subst h2; rw [hx''k]; exact hmem
      · simpa [hx'', h1, h2] using hx'X i
  have hsum : ∑ i, x'' i = ∑ i, a'.x i := by
    have : ∀ i, x'' i = a'.x i + (if i = i₀ then Pi.single l δ else 0) -
        (if i = k then Pi.single l δ else 0) := fun i => by
      by_cases h1 : i = i₀
      · subst h1; simp [hx'', Ne.symm hk0]
      · by_cases h2 : i = k
        · subst h2; simp [hx'', h1]
        · simp [hx'', h1, h2]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, add_sub_cancel_right]
  have hu : ∀ i, i ≠ i₀ → u i (v.1 i) ≤ u i (x'' i) := by
    intro i hi
    by_cases h2 : i = k
    · subst h2; rw [hx''k]; exact hs.1
    · simpa [hx'', hi, h2] using hle' i
  have hopt := hv.2 _ (hcons x'' hx''X hsum hu)
  have hgt : u i₀ (a'.x i₀) < u i₀ (x'' i₀) := by
    rw [hx''i₀]
    refine not_le.mp (hmono i₀ _ (hx'X i₀) _ (single_nonneg_add (hx'X i₀) l hδ.le)
      (fun m => ?_) ?_).2
    · by_cases hm : m = l
      · subst hm; simp; linarith
      · simp [hm]
    · intro h
      have := congrFun h l
      simp at this
      linarith
  linarith [hle' i₀]

/-- **Exercise 16.F.1** (MWG, p. 562), second part. With `F` nondecreasing (free disposal, e.g.
`∇F ≫ 0`) and at least one firm, every Pareto optimal allocation solves (16.F.1) for the utility
levels `ūᵢ = uᵢ(xᵢ)` it gives. -/
theorem exercise_16_F_1_ii [Nonempty κ] {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι}
    (hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    IsSolution16F1 u F ω i₀ (fun i => u i (a.x i)) (a.x, a.y) := by
  classical
  obtain ⟨⟨⟨hx, hy⟩, hc⟩, hno⟩ := hpo
  refine ⟨⟨fun i _ => le_rfl, fun l => ?_, hy, fun i l => hx i l⟩, ?_⟩
  · have := congrFun hc l
    simp only [Finset.sum_apply, Pi.add_apply] at this
    exact this.le
  rintro v' ⟨hu', hres, hF', hnn⟩
  by_contra hgt
  push Not at hgt
  -- dispose of the slack with one firm
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  set D : Fin L → ℝ := ω + ∑ j, v'.2 j - ∑ i, v'.1 i with hD
  have hD0 : ∀ l, 0 ≤ D l := fun l => by
    simp only [hD, Pi.sub_apply, Pi.add_apply, Finset.sum_apply]; linarith [hres l]
  set y'' : κ → Fin L → ℝ := fun j => if j = j₀ then v'.2 j - D else v'.2 j with hy''
  apply hno
  refine ⟨⟨v'.1, y''⟩, ⟨⟨fun i l => hnn i l, fun j => ?_⟩, ?_⟩, fun i => ?_, i₀, ?_⟩
  · by_cases hj : j = j₀
    · subst hj
      change F j (y'' j) ≤ 0
      simp only [hy'', ↓reduceIte]
      exact (hFmono j _ _ fun l => by simp; linarith [hD0 l]).trans (hF' j)
    · change F j (y'' j) ≤ 0
      simp only [hy'', hj, ↓reduceIte]
      exact hF' j
  · change ∑ i, v'.1 i = ω + ∑ j, y'' j
    have : ∑ j, y'' j = ∑ j, v'.2 j - D := by
      rw [Finset.sum_congr rfl fun j _ => (show y'' j = v'.2 j - if j = j₀ then D else 0 by
        by_cases hj : j = j₀ <;> simp [hy'', hj]), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ j₀ (fun _ => D)]
      simp
    rw [this, hD]
    abel
  · by_cases hi : i = i₀
    · subst hi; exact hgt.le
    · exact hu' i hi
  · exact ⟨hgt.le, not_le.mpr hgt⟩

/-! ## Exercise 16.F.2: the Kuhn-Tucker conditions (16.F.2)-(16.F.3) -/

/-- The coordinate projection `v ↦ xᵢ` on `ℝ^{LI} × ℝ^{LJ}`. -/
def projX (i : ι) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] (Fin L → ℝ) :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The coordinate projection `v ↦ yⱼ` on `ℝ^{LI} × ℝ^{LJ}`. -/
def projY (j : κ) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] (Fin L → ℝ) :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The linear part `∑ᵢ x_{ℓi} - ∑ⱼ y_{ℓj}` of the resource constraint for good `ℓ`. -/
def resLin (l : Fin L) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ :=
  ∑ i : ι, (ContinuousLinearMap.proj l).comp (projX (κ := κ) i) -
    ∑ j : κ, (ContinuousLinearMap.proj l).comp (projY (ι := ι) j)

/-- **Exercise 16.F.2** (MWG, p. 576; (16.F.2)-(16.F.3), p. 563). Let `(x, y)` solve (16.F.1), with
every `uᵢ` differentiable at `xᵢ` with `∇uᵢ(xᵢ) ≫ 0` and every `Fⱼ` differentiable at `yⱼ` with
`∇Fⱼ(yⱼ) ≫ 0` (`J ≥ 1`, `L ≥ 1`). Then there are multipliers `δ ≥ 0` with `δ_{i₀} = 1`, `μ ≥ 0`,
`γ ≥ 0` such that `δᵢ ∂uᵢ/∂x_{ℓi} - μₗ ≤ 0`, with equality if `x_{ℓi} > 0` (16.F.2),
`μₗ - γⱼ ∂Fⱼ/∂y_{ℓj} = 0` (16.F.3), and complementary slackness holds. -/
theorem exercise_16_F_2 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ} {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (v.1 i)) (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j))
    (hupos : ∀ i l, 0 < u' i (Pi.single l 1)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1)) :
    ∃ (δ : ι → ℝ) (μ : Fin L → ℝ) (γ : κ → ℝ), δ i₀ = 1 ∧ (∀ i, 0 ≤ δ i) ∧ (∀ l, 0 ≤ μ l) ∧
      (∀ j, 0 ≤ γ j) ∧ (∀ i l, δ i * u' i (Pi.single l 1) - μ l ≤ 0) ∧
      (∀ i l, 0 < v.1 i l → δ i * u' i (Pi.single l 1) - μ l = 0) ∧
      (∀ j l, μ l - γ j * F' j (Pi.single l 1) = 0) ∧
      (∀ i, i ≠ i₀ → δ i * (u i (v.1 i) - ub i) = 0) ∧
      (∀ l, μ l * (ω l + ∑ j, v.2 j l - ∑ i, v.1 i l) = 0) ∧
      (∀ j, γ j * F j (v.2 j) = 0) := by
  classical
  -- the constraints of (16.F.1) as `gₖ ≤ 0`
  let g : ({i // i ≠ i₀} ⊕ Fin L ⊕ κ ⊕ (ι × Fin L)) → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) → ℝ :=
    fun k w => match k with
    | Sum.inl i => ub i.1 - u i.1 (w.1 i.1)
    | Sum.inr (Sum.inl l) => resLin l w - ω l
    | Sum.inr (Sum.inr (Sum.inl j)) => F j (w.2 j)
    | Sum.inr (Sum.inr (Sum.inr il)) => -(w.1 il.1 il.2)
  let g' : ({i // i ≠ i₀} ⊕ Fin L ⊕ κ ⊕ (ι × Fin L)) →
      ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ :=
    fun k => match k with
    | Sum.inl i => -((u' i.1).comp (projX i.1))
    | Sum.inr (Sum.inl l) => resLin l
    | Sum.inr (Sum.inr (Sum.inl j)) => (F' j).comp (projY j)
    | Sum.inr (Sum.inr (Sum.inr il)) => -((ContinuousLinearMap.proj il.2).comp (projX il.1))
  have hres : ∀ (l : Fin L) (w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)),
      resLin l w = ∑ i, w.1 i l - ∑ j, w.2 j l := by
    intro l w
    simp [resLin, projX, projY]
  have hset : {w | ∀ k, g k w ≤ 0} = Problem16F1 u F ω i₀ ub := by
    ext w
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun l => ?_, fun j => h (Sum.inr (Sum.inr (Sum.inl j))),
        fun i l => ?_⟩
      · have := h (Sum.inl ⟨i, hi⟩); simp only [g] at this; linarith
      · have := h (Sum.inr (Sum.inl l)); simp only [g, hres] at this; linarith
      · have := h (Sum.inr (Sum.inr (Sum.inr (i, l)))); simp only [g] at this; linarith
    · rintro ⟨h1, h2, h3, h4⟩ k
      rcases k with i | l | j | il
      · simp only [g]; linarith [h1 i.1 i.2]
      · simp only [g, hres]; linarith [h2 l]
      · exact h3 j
      · simp only [g]; linarith [h4 il.1 il.2]
  have hz : ∀ k, g k v ≤ 0 := by
    have := hv.1; rw [← hset] at this; exact this
  have hmax : IsLocalMaxOn (fun w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => u i₀ (w.1 i₀))
      {w | ∀ k, g k w ≤ 0} v := by
    rw [hset]
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => hv.2 w hw
  have hf : HasFDerivAt (fun w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => u i₀ (w.1 i₀))
      ((u' i₀).comp (projX i₀)) v := (hu i₀).comp v (projX i₀).hasFDerivAt
  have hg : ∀ k, HasFDerivAt (g k) (g' k) v := by
    intro k
    rcases k with i | l | j | il
    · exact (hasFDerivAt_const _ _).sub ((hu i.1).comp v (projX i.1).hasFDerivAt) |>.congr_fderiv
        (by simp [g'])
    · exact (resLin l).hasFDerivAt.sub_const (ω l)
    · exact (hF j).comp v (projY j).hasFDerivAt
    · exact ((ContinuousLinearMap.proj il.2).comp (projX il.1)).hasFDerivAt.neg
  obtain ⟨l0, lam, hl0, hlam, hne, hcs, heq⟩ := fritz_john hz hmax hf hg
  -- the multipliers
  set δh : ι → ℝ := fun i => if h : i = i₀ then l0 else lam (Sum.inl ⟨i, h⟩) with hδh
  set μ : Fin L → ℝ := fun l => lam (Sum.inr (Sum.inl l)) with hμ
  set γ : κ → ℝ := fun j => lam (Sum.inr (Sum.inr (Sum.inl j))) with hγ
  set ν : ι → Fin L → ℝ := fun i l => lam (Sum.inr (Sum.inr (Sum.inr (i, l)))) with hν
  -- evaluating the multiplier identity in the coordinate directions
  set a : ι → Fin L → ℝ := fun i l => u' i (Pi.single l 1) with ha
  set b : κ → Fin L → ℝ := fun j l => F' j (Pi.single l 1) with hb
  have hpx : ∀ (i i' : ι) (l : Fin L), projX (κ := κ) i'
      ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ)) =
      if i' = i then Pi.single l 1 else 0 := fun i i' l => by
    simp only [projX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply, Pi.single_apply]
  have hpy0 : ∀ (i : ι) (j : κ) (l : Fin L), projY (ι := ι) j
      ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ)) = 0 := by
    intro i j l
    simp [projY]
  have hpx0 : ∀ (i : ι) (j : κ) (l : Fin L), projX (κ := κ) i
      ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ)) = 0 := by
    intro i j l
    simp [projX]
  have hpy : ∀ (j j' : κ) (l : Fin L), projY (ι := ι) j'
      ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ)) =
      if j' = j then Pi.single l 1 else 0 := fun j j' l => by
    simp only [projY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.proj_apply, Pi.single_apply]
  have hsingle : ∀ (l l' : Fin L), (Pi.single l (1 : ℝ) : Fin L → ℝ) l' =
      if l' = l then 1 else 0 := fun l l' => Pi.single_apply l 1 l'
  have hdx : ∀ i l, δh i * a i l - μ l = -ν i l := by
    intro i l
    have h := congrArg (fun φ : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ =>
      φ ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ))) heq
    rw [sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, g', ContinuousLinearMap.comp_apply,
      neg_apply, hpx, hpy0, hres, map_zero, mul_zero,
      Finset.sum_const_zero, zero_add] at h
    -- the four sums
    have e1 : ∑ x : {i // i ≠ i₀}, lam (Sum.inl x) * -(u' x.1 (if x.1 = i then Pi.single l 1
        else 0)) = if h : i = i₀ then 0 else -(lam (Sum.inl ⟨i, h⟩) * a i l) := by
      split_ifs with hi
      · exact Finset.sum_eq_zero fun x _ => by
          have : x.1 ≠ i := fun h' => x.2 (h'.trans hi)
          simp [this]
      · rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp [ha]
        · intro x _ hx
          have : x.1 ≠ i := fun h' => hx (Subtype.ext h')
          simp [this]
        · simp
    have hinner : ∀ x, ∑ x_1, (Pi.single i (Pi.single l 1) : ι → Fin L → ℝ) x_1 x =
        if x = l then 1 else 0 := by
      intro x
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp [Pi.single_apply]
    have e2 : ∑ x : Fin L, lam (Sum.inr (Sum.inl x)) *
        (∑ x_1, (Pi.single i (Pi.single l 1) : ι → Fin L → ℝ) x_1 x -
          ∑ x_1 : κ, (0 : κ → Fin L → ℝ) x_1 x) = μ l := by
      simp only [hinner, Pi.zero_apply, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hμ]
    have e3 : ∑ x : ι × Fin L, lam (Sum.inr (Sum.inr (Sum.inr x))) *
        -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => ℝ) x.2
          (if x.1 = i then Pi.single l 1 else 0)) = -ν i l := by
      rw [Finset.sum_eq_single (i, l)]
      · simp [hν]
      · rintro ⟨i', l'⟩ _ hne
        by_cases hi : i' = i
        · subst hi
          have : l' ≠ l := fun h' => hne (by rw [h'])
          simp [this]
        · simp [hi]
      · simp
    rw [e1, e2, e3] at h
    by_cases hi : i = i₀
    · subst hi
      simp only [↓reduceIte, ↓reduceDIte, hδh] at h ⊢
      simp only [ha]
      linarith
    · have hi' : i₀ ≠ i := Ne.symm hi
      simp only [hi', hi, ↓reduceIte, ↓reduceDIte, map_zero, mul_zero, hδh] at h ⊢
      simp only [ha]
      linarith
  have hdy : ∀ j l, γ j * b j l - μ l = 0 := by
    intro j l
    have h := congrArg (fun φ : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ =>
      φ ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ))) heq
    rw [sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, g', ContinuousLinearMap.comp_apply,
      neg_apply, hpx0, hpy, hres, map_zero, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero, neg_zero] at h
    have hinner : ∀ x, ∑ x_1, (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ) x_1 x =
        if x = l then 1 else 0 := by
      intro x
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp [Pi.single_apply]
    have e2 : ∑ x : Fin L, lam (Sum.inr (Sum.inl x)) *
        (∑ x_1 : ι, (0 : ι → Fin L → ℝ) x_1 x -
          ∑ x_1, (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ) x_1 x) = -μ l := by
      simp only [hinner, Pi.zero_apply, Finset.sum_const_zero, zero_sub, mul_neg, mul_ite,
        mul_one, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, hμ]
    have e4 : ∑ x : κ, lam (Sum.inr (Sum.inr (Sum.inl x))) *
        (F' x) (if x = j then Pi.single l 1 else 0) = γ j * b j l := by
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp [hγ, hb]
    rw [e2, e4] at h
    linarith
  -- complementary slackness, multiplier by multiplier
  have hcsU : ∀ i (h : i ≠ i₀), lam (Sum.inl ⟨i, h⟩) * (ub i - u i (v.1 i)) = 0 :=
    fun i h => hcs (Sum.inl ⟨i, h⟩)
  have hcsR : ∀ l, μ l * (∑ i, v.1 i l - ∑ j, v.2 j l - ω l) = 0 := fun l => by
    have := hcs (Sum.inr (Sum.inl l)); simp only [g, hres] at this; exact this
  have hcsF : ∀ j, γ j * F j (v.2 j) = 0 := fun j => hcs (Sum.inr (Sum.inr (Sum.inl j)))
  have hcsN : ∀ i l, ν i l * v.1 i l = 0 := fun i l => by
    have := hcs (Sum.inr (Sum.inr (Sum.inr (i, l)))); simp only [g] at this
    have h2 : ν i l * -v.1 i l = 0 := this
    linarith
  have hδh0 : ∀ i, 0 ≤ δh i := fun i => by
    simp only [hδh]; split_ifs
    · exact hl0
    · exact hlam _
  have hμ0 : ∀ l, 0 ≤ μ l := fun l => hlam _
  have hγ0 : ∀ j, 0 ≤ γ j := fun j => hlam _
  have hν0 : ∀ i l, 0 ≤ ν i l := fun i l => hlam _
  have ha0 : ∀ i l, 0 < a i l := fun i l => hupos i l
  have hb0 : ∀ j l, 0 < b j l := fun j l => hFpos j l
  have hνz : ∀ i l, 0 < v.1 i l → ν i l = 0 := fun i l hx => by
    rcases mul_eq_zero.mp (hcsN i l) with h | h
    · exact h
    · linarith
  rcases hl0.lt_or_eq with hl0pos | hl0z
  · -- `λ₀ > 0`: normalize
    refine ⟨fun i => δh i / l0, fun l => μ l / l0, fun j => γ j / l0, ?_, fun i => ?_,
      fun l => ?_, fun j => ?_, fun i l => ?_, fun i l hx => ?_, fun j l => ?_, fun i hi => ?_,
      fun l => ?_, fun j => ?_⟩
    · simp [hδh, hl0pos.ne']
    · exact div_nonneg (hδh0 i) hl0
    · exact div_nonneg (hμ0 l) hl0
    · exact div_nonneg (hγ0 j) hl0
    · have h1 := hdx i l
      have h2 : δh i / l0 * a i l - μ l / l0 = -ν i l / l0 := by
        field_simp; linarith
      change δh i / l0 * a i l - μ l / l0 ≤ 0
      rw [h2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hν0 i l]) hl0
    · have h1 := hdx i l
      rw [hνz i l hx] at h1
      change δh i / l0 * a i l - μ l / l0 = 0
      field_simp; linarith
    · have h1 := hdy j l
      change μ l / l0 - γ j / l0 * b j l = 0
      field_simp; linarith
    · have h1 := hcsU i hi
      have hδi : δh i = lam (Sum.inl ⟨i, hi⟩) := by simp [hδh, hi]
      change δh i / l0 * (u i (v.1 i) - ub i) = 0
      rw [hδi]
      field_simp; linarith
    · have h1 := hcsR l
      change μ l / l0 * (ω l + ∑ j, v.2 j l - ∑ i, v.1 i l) = 0
      field_simp; linarith
    · change γ j / l0 * F j (v.2 j) = 0
      rw [div_mul_eq_mul_div, hcsF j, zero_div]
  · -- `λ₀ = 0`: the prices are strictly positive and consumer `i₀` consumes nothing
    subst hl0z
    have hμne : ∃ l, μ l ≠ 0 := by
      by_contra hall
      push Not at hall
      have hγz : ∀ j, γ j = 0 := fun j => by
        have := hdy j ⟨0, hL⟩
        rw [hall] at this
        rcases mul_eq_zero.mp (by linarith : γ j * b j ⟨0, hL⟩ = 0) with h | h
        · exact h
        · exact absurd h (hb0 j _).ne'
      have hδz : ∀ i, δh i = 0 ∧ ∀ l, ν i l = 0 := fun i => by
        refine ⟨?_, fun l => ?_⟩
        · have := hdx i ⟨0, hL⟩
          rw [hall] at this
          have h1 := mul_nonneg (hδh0 i) (ha0 i ⟨0, hL⟩).le
          have h2 : δh i * a i ⟨0, hL⟩ = 0 := by linarith [hν0 i ⟨0, hL⟩]
          rcases mul_eq_zero.mp h2 with h | h
          · exact h
          · exact absurd h (ha0 i _).ne'
        · have := hdx i l
          rw [hall] at this
          have h1 := mul_nonneg (hδh0 i) (ha0 i l).le
          linarith [hν0 i l]
      rcases hne with h | ⟨k, hk⟩
      · exact h rfl
      · rcases k with i | l | j | il
        · have := (hδz i.1).1
          simp only [hδh, i.2, ↓reduceDIte] at this
          exact hk this
        · exact hk (hall l)
        · exact hk (hγz j)
        · exact hk ((hδz il.1).2 il.2)
    obtain ⟨l₁, hl₁⟩ := hμne
    obtain ⟨j₀⟩ := ‹Nonempty κ›
    have hγj₀ : 0 < γ j₀ := by
      have h1 := hdy j₀ l₁
      have h2 : 0 < μ l₁ := lt_of_le_of_ne (hμ0 l₁) (Ne.symm hl₁)
      by_contra h
      have : γ j₀ = 0 := le_antisymm (not_lt.mp h) (hγ0 j₀)
      rw [this] at h1
      linarith
    have hμpos : ∀ l, 0 < μ l := fun l => by
      have := hdy j₀ l
      nlinarith [mul_pos hγj₀ (hb0 j₀ l)]
    have hx₀ : ∀ l, v.1 i₀ l = 0 := fun l => by
      by_contra hne
      have hx : 0 < v.1 i₀ l := lt_of_le_of_ne (hv.1.2.2.2 i₀ l) (Ne.symm hne)
      have := hdx i₀ l
      rw [hνz i₀ l hx] at this
      simp only [hδh, ↓reduceDIte, zero_mul, zero_sub, neg_eq_zero, neg_zero] at this
      linarith [hμpos l]
    set t := ∑ l, a i₀ l / μ l with ht
    have ht0 : 0 ≤ t := Finset.sum_nonneg fun l _ => (div_pos (ha0 i₀ l) (hμpos l)).le
    have hat : ∀ l, a i₀ l ≤ t * μ l := fun l => by
      have h1 : a i₀ l / μ l ≤ t := Finset.single_le_sum
        (f := fun l => a i₀ l / μ l) (fun l _ => (div_pos (ha0 i₀ l) (hμpos l)).le)
        (Finset.mem_univ l)
      rwa [div_le_iff₀ (hμpos l)] at h1
    refine ⟨fun i => if i = i₀ then 1 else t * δh i, fun l => t * μ l, fun j => t * γ j,
      by simp, fun i => ?_, fun l => mul_nonneg ht0 (hμ0 l), fun j => mul_nonneg ht0 (hγ0 j),
      fun i l => ?_, fun i l hx => ?_, fun j l => ?_, fun i hi => ?_, fun l => ?_, fun j => ?_⟩
    · change 0 ≤ if i = i₀ then 1 else t * δh i
      split_ifs
      · exact zero_le_one
      · exact mul_nonneg ht0 (hδh0 i)
    · change (if i = i₀ then 1 else t * δh i) * a i l - t * μ l ≤ 0
      split_ifs with hi
      · subst hi; linarith [hat l]
      · have := hdx i l
        nlinarith [mul_nonneg ht0 (hν0 i l)]
    · change (if i = i₀ then 1 else t * δh i) * a i l - t * μ l = 0
      split_ifs with hi
      · subst hi; linarith [hx₀ l]
      · have h1 := hdx i l
        rw [hνz i l hx] at h1
        have : t * (δh i * a i l - μ l) = 0 := by rw [h1]; ring
        linarith
    · change t * μ l - t * γ j * b j l = 0
      have h1 := hdy j l
      have : t * (γ j * b j l - μ l) = 0 := by rw [h1]; ring
      linarith
    · simp only [hi, ↓reduceIte]
      have h1 := hcsU i hi
      have hδi : δh i = lam (Sum.inl ⟨i, hi⟩) := by simp [hδh, hi]
      rw [hδi]
      have : t * (lam (Sum.inl ⟨i, hi⟩) * (ub i - u i (v.1 i))) = 0 := by rw [h1, mul_zero]
      linarith
    · have h1 := hcsR l
      have : t * (μ l * (∑ i, v.1 i l - ∑ j, v.2 j l - ω l)) = 0 := by rw [h1, mul_zero]
      linarith
    · rw [mul_assoc, hcsF j, mul_zero]


end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order conditions and the welfare theorems (MWG Section 16.F, pp. 563-566)

* p. 563: at a solution of (16.F.1) (`ūᵢ ≥ 0`, `uᵢ(0) = 0`) all constraints bind.
* **Exercise 16.F.3**: at an interior solution, (16.F.2)-(16.F.3) give the ratio conditions
  (16.F.4)-(16.F.6).
* The exact correspondences between (16.F.2)-(16.F.3) and the first-order conditions
  (16.F.10)-(16.F.11) of utility and profit maximization (`μ = p`, `δᵢ = 1/αᵢ`, `γⱼ = βⱼ`), and
  (16.F.13)-(16.F.14) of the weighted welfare problem (16.F.12) (`δᵢ = λᵢ/λ₁`, `μ = ψ/λ₁`,
  `γ = η/λ₁`).
* p. 565: with quasiconcave utilities and convex `Fⱼ`, a Pareto optimum is a price equilibrium
  with transfers at prices `p = μ ≫ 0`, wealth `wᵢ = p·xᵢ`; conversely every price equilibrium
  with transfers is Pareto optimal (first welfare theorem). The consumer and firm sufficiency
  steps are `consumer_max_of_foc` and `firm_max_of_foc`.
* **Proposition 16.F.1**: with concave `uᵢ` and convex `Fⱼ`, every Pareto optimum maximizes
  `∑ᵢ λᵢ uᵢ(xᵢ)` subject to the resource and technology constraints, with `λ_{i₀} = 1`; for
  `λᵢ > 0`, `1/λᵢ` is consumer `i`'s marginal utility of wealth `αᵢ` in (16.F.10) at the
  supporting prices. (The book writes `λ ≫ 0`; a weight can vanish, but only for a consumer with
  `xᵢ = 0`, where `αᵢ` is undefined.)
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- The tangent inequality of a convex function differentiable at `x`:
`F(x) + DF(x)(y - x) ≤ F(y)` for `x, y` in a convex set on which `F` is convex. -/
theorem convexOn_tangent_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} {F : V → ℝ} {F' : V →L[ℝ] ℝ} (hF : ConvexOn ℝ S F) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt F F' x) : F x + F' (y - x) ≤ F y := by
  set d := y - x with hdd
  have hline : HasDerivAt (fun t : ℝ => F (x + t • d)) (F' d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have h2 : HasFDerivAt F F' (x + (0 : ℝ) • d) := by simpa using hd
    exact h2.comp_hasDerivAt 0 h1
  have hslope := hline.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (F (x + (0 + t) • d) - F (x + (0 : ℝ) • d)) ≤
      F y - F x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hconv := hF.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have heq : (1 - t) • x + t • y = x + t • d := by
      simp only [hdd, smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    rw [zero_add, zero_smul, add_zero, smul_eq_mul, inv_mul_le_iff₀ ht.1]
    linarith
  exact (by linarith [le_of_tendsto hslope hbound] : F x + F' d ≤ F y)

/-- The tangent inequality of a concave function: `G(y) ≤ G(x) + DG(x)(y - x)`. -/
theorem concaveOn_le_tangent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} {G : V → ℝ} {G' : V →L[ℝ] ℝ} (hG : ConcaveOn ℝ S G) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt G G' x) : G y ≤ G x + G' (y - x) := by
  have := convexOn_tangent_le hG.neg hx hy hd.neg
  simp only [Pi.neg_apply, neg_apply] at this
  linarith

/-- **Section 16.F** (MWG, p. 565), the consumer's side. Let `u` be quasiconcave, continuous and
nondecreasing on `ℝ^L₊`, differentiable at `x ≥ 0`, and let `p ≫ 0`, `δ > 0` satisfy
`δ ∂u/∂xₗ ≤ pₗ` with equality where `xₗ > 0` (that is, (16.F.10) with `α = 1/δ`). Then `x` is
maximal for `u` in the budget set `{y ≥ 0 : p·y ≤ p·x}`. -/
theorem consumer_max_of_foc {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (hcont : ContinuousOn u (nonnegOrthant L))
    (hmono : ∀ x ∈ nonnegOrthant L, ∀ y, x ≤ y → u x ≤ u y) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) (hu : HasFDerivAt u u' x) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {δ : ℝ} (hδ : 0 < δ)
    (hfoc : ∀ l, δ * u' (Pi.single l 1) - p l ≤ 0)
    (hfoc_eq : ∀ l, 0 < x l → δ * u' (Pi.single l 1) - p l = 0) :
    IsMaximalFor (utilityPref u) (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x)) x := by
  refine ⟨⟨hx, le_rfl⟩, fun y hy => ?_⟩
  change u y ≤ u x
  by_contra hlt
  push Not at hlt
  have hyX : y ∈ nonnegOrthant L := hy.1
  -- `y ≠ 0`, so `p·y > 0`
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact absurd (hmono 0 (fun _ => le_rfl) x hx) (not_le.mpr hlt)
  have hpy : 0 < p ⬝ᵥ y := by
    rw [dotProduct_comm]
    exact dotProduct_pos_of_nonneg_ne_zero hyX hy0 hp
  -- shrink `y` slightly: still better than `x`, now strictly cheaper
  set zs : ℕ → Fin L → ℝ := fun n => (1 - 1 / ((n : ℝ) + 2)) • y with hzs
  have hzsX : ∀ n, zs n ∈ nonnegOrthant L := fun n l => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hzs, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (hyX l)
  have hzst : Tendsto zs atTop (𝓝 y) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    have h2 : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    have := ((continuous_id.smul (continuous_const (y := y))).tendsto (1 : ℝ)).comp h2
    simpa [hzs, Function.comp_def] using this
  obtain ⟨n, hn⟩ := exists_strict_of_tendsto (rationalOn_utilityPref _ u)
    (prefContinuous_utilityPref hcont) hyX hx ⟨hlt.le, not_le.mpr hlt⟩ hzsX hzst
  have hzx : u x ≤ u (zs n) := hn.1
  have hcheap : p ⬝ᵥ zs n < p ⬝ᵥ x := by
    have hs : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hzs, dotProduct_smul, smul_eq_mul]
    nlinarith [hy.2]
  -- quasiconcavity: `∇u(x)·(zₙ - x) ≥ 0`, but the first-order conditions make it negative
  have hgrad := theorem_M_C_3_necessity hq hx (hzsX n) hu hzx
  have hle : u' (zs n - x) ≤ (p ⬝ᵥ zs n - p ⬝ᵥ x) / δ := by
    rw [clm_apply_eq_sum_partials, ← dotProduct_sub, dotProduct, Finset.sum_div]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [mul_div_right_comm]
    rcases (hx l).lt_or_eq with hxl | hxl
    · have := hfoc_eq l hxl
      have : u' (Pi.single l 1) = p l / δ := by field_simp; linarith
      rw [this]
    · have h1 : (zs n - x) l = zs n l := by rw [Pi.sub_apply, ← hxl, sub_zero]
      rw [h1]
      have h2 : u' (Pi.single l 1) ≤ p l / δ := by
        rw [le_div_iff₀ hδ]; linarith [hfoc l]
      exact mul_le_mul_of_nonneg_right h2 (hzsX n l)
  have : (p ⬝ᵥ zs n - p ⬝ᵥ x) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
  linarith

/-- **Section 16.F** (MWG, p. 565), the firm's side. If `F` is convex and differentiable at `y*`,
`F(y*) ≤ 0`, `γ ≥ 0` with `γ F(y*) = 0`, and `pₗ = γ ∂F/∂yₗ(y*)` (16.F.11), then `y*` maximizes
profit on `{y : F(y) ≤ 0}`. -/
theorem firm_max_of_foc {F : (Fin L → ℝ) → ℝ} {F' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ConvexOn ℝ Set.univ F) {ys : Fin L → ℝ} (hys : F ys ≤ 0) (hd : HasFDerivAt F F' ys)
    {p : Fin L → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (hcs : γ * F ys = 0)
    (hfoc : ∀ l, p l - γ * F' (Pi.single l 1) = 0) : ys ∈ supply {y | F y ≤ 0} p := by
  refine ⟨hys, fun y hy => ?_⟩
  have hpl : ∀ l, p l = γ * F' (Pi.single l 1) := fun l => by linarith [hfoc l]
  have hp : ∀ z, p ⬝ᵥ z = γ * F' z := fun z => by
    rw [clm_apply_eq_sum_partials, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hpl l]; ring
  have htan := convexOn_tangent_le hF (Set.mem_univ ys) (Set.mem_univ y) hd
  have : p ⬝ᵥ (y - ys) ≤ 0 := by
    rw [hp]
    have hy' : F y ≤ 0 := hy
    nlinarith [mul_le_mul_of_nonneg_left htan hγ]
  rw [dotProduct_sub] at this
  linarith

/-- **Section 16.F** (MWG, p. 563). Under the assumptions of Exercise 16.F.2, with `uᵢ(0) = 0` and
required utility levels `ūᵢ ≥ 0`, all constraints of (16.F.1) bind at a solution: `uᵢ(xᵢ) = ūᵢ`
for `i ≠ i₀`, the resource constraints hold with equality and `Fⱼ(yⱼ) = 0`. -/
theorem section_16_F_constraints_bind [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ} {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (v.1 i)) (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j))
    (hupos : ∀ i l, 0 < u' i (Pi.single l 1)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1))
    (hu0 : ∀ i, u i 0 = 0) (hub : ∀ i, 0 ≤ ub i) :
    (∀ i, i ≠ i₀ → u i (v.1 i) = ub i) ∧ (∀ l, ∑ i, v.1 i l = ω l + ∑ j, v.2 j l) ∧
      ∀ j, F j (v.2 j) = 0 := by
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, hcsU, hcsR, hcsF⟩ :=
    exercise_16_F_2 hL hv hu hF hupos hFpos
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ l]
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hγpos : ∀ j, 0 < γ j := fun j => by
    have h1 := hfoc_y j ⟨0, hL⟩
    by_contra h
    have : γ j = 0 := le_antisymm (not_lt.mp h) (hγ0 j)
    rw [this, zero_mul, sub_zero] at h1
    linarith [hμpos ⟨0, hL⟩]
  refine ⟨fun i hi => ?_, fun l => ?_, fun j => ?_⟩
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · have := hcsU i hi
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · linarith
    · -- zero weight: consumer `i` consumes nothing
      have hx0 : v.1 i = 0 := funext fun l => by
        by_contra hne
        have hx : 0 < v.1 i l := lt_of_le_of_ne (hv.1.2.2.2 i l) (Ne.symm hne)
        have := hfoc_eq i l hx
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      have h1 := hv.1.1 i hi
      rw [hx0, hu0] at h1 ⊢
      linarith [hub i]
  · have := hcsR l
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hμpos l).ne'
    · linarith
  · rcases mul_eq_zero.mp (hcsF j) with h | h
    · exact absurd h (hγpos j).ne'
    · exact h

omit [Fintype ι] [Fintype κ] in
/-- **Exercise 16.F.3** (MWG, p. 576; (16.F.4)-(16.F.6), p. 564). If the multipliers satisfy
(16.F.2) with equality (interior solution) and (16.F.3), with `δ_{i₀} = 1` and positive partial
derivatives `aᵢₗ = ∂uᵢ/∂x_{ℓi}`, `bⱼₗ = ∂Fⱼ/∂y_{ℓj}`, then all marginal rates of substitution and
transformation coincide: (16.F.4) `aᵢₗ/aᵢₗ' = aᵢ'ₗ/aᵢ'ₗ'`, (16.F.5) `bⱼₗ/bⱼₗ' = bⱼ'ₗ/bⱼ'ₗ'`,
(16.F.6) `aᵢₗ/aᵢₗ' = bⱼₗ/bⱼₗ'`. -/
theorem exercise_16_F_3 {a : ι → Fin L → ℝ} {b : κ → Fin L → ℝ} {δ : ι → ℝ} {μ : Fin L → ℝ}
    {γ : κ → ℝ} {i₀ : ι} (ha : ∀ i l, 0 < a i l) (hb : ∀ j l, 0 < b j l) (hδ1 : δ i₀ = 1)
    (hx : ∀ i l, δ i * a i l - μ l = 0) (hy : ∀ j l, μ l - γ j * b j l = 0) :
    (∀ i i' l l', a i l / a i l' = a i' l / a i' l') ∧
      (∀ j j' l l', b j l / b j l' = b j' l / b j' l') ∧
      (∀ i j l l', a i l / a i l' = b j l / b j l') := by
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hx i₀ l; rw [hδ1, one_mul] at this; linarith [ha i₀ l]
  have key_a : ∀ i l l', a i l / a i l' = μ l / μ l' := by
    intro i l l'
    have hδ : 0 < δ i := by
      by_contra h
      have : δ i * a i l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (ha i l).le
      linarith [hμpos l, hx i l]
    have e1 : a i l = μ l / δ i := by field_simp; linarith [hx i l]
    have e2 : a i l' = μ l' / δ i := by field_simp; linarith [hx i l']
    rw [e1, e2]
    field_simp
  have key_b : ∀ j l l', b j l / b j l' = μ l / μ l' := by
    intro j l l'
    have hγ : 0 < γ j := by
      by_contra h
      have : γ j * b j l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (hb j l).le
      linarith [hμpos l, hy j l]
    have e1 : b j l = μ l / γ j := by field_simp; linarith [hy j l]
    have e2 : b j l' = μ l' / γ j := by field_simp; linarith [hy j l']
    rw [e1, e2]
    field_simp
  exact ⟨fun i i' l l' => by rw [key_a, key_a], fun j j' l l' => by rw [key_b, key_b],
    fun i j l l' => by rw [key_a, key_b]⟩

/-- **Section 16.F** (MWG, p. 565): (16.F.2) for consumer `i` with weight `δᵢ > 0` and prices
`μ` is (16.F.10) with `p = μ` and marginal utility of wealth `αᵢ = 1/δᵢ`. -/
theorem foc_16F2_iff_16F10 {a : Fin L → ℝ} {δ : ℝ} (hδ : 0 < δ) (μ x : Fin L → ℝ) :
    (∀ l, δ * a l - μ l ≤ 0 ∧ (0 < x l → δ * a l - μ l = 0)) ↔
      ∀ l, a l - (1 / δ) * μ l ≤ 0 ∧ (0 < x l → a l - (1 / δ) * μ l = 0) := by
  have key : ∀ l, a l - (1 / δ) * μ l = (δ * a l - μ l) / δ := fun l => by field_simp
  simp only [key, div_nonpos_iff, div_eq_zero_iff, hδ.ne', or_false]
  constructor
  · intro h l
    exact ⟨Or.inr ⟨(h l).1, hδ.le⟩, (h l).2⟩
  · intro h l
    refine ⟨?_, (h l).2⟩
    rcases (h l).1 with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · exact h1

omit [Fintype ι] [Fintype κ] in
/-- **Section 16.F** (MWG, p. 566): with welfare weights `λ` (`λ_{i₀} > 0`), the first-order
conditions (16.F.13)-(16.F.14) of (16.F.12) with multipliers `ψ`, `η` are (16.F.2)-(16.F.3) with
`δᵢ = λᵢ/λ_{i₀}`, `μ = ψ/λ_{i₀}`, `γ = η/λ_{i₀}`. -/
theorem foc_16F13_iff_16F2 {a : ι → Fin L → ℝ} {b : κ → Fin L → ℝ} {lam : ι → ℝ}
    {ψ : Fin L → ℝ} {η : κ → ℝ} {i₀ : ι} (hl : 0 < lam i₀) (x : ι → Fin L → ℝ) :
    ((∀ i l, lam i * a i l - ψ l ≤ 0 ∧ (0 < x i l → lam i * a i l - ψ l = 0)) ∧
      ∀ j l, ψ l - η j * b j l = 0) ↔
    ((∀ i l, lam i / lam i₀ * a i l - ψ l / lam i₀ ≤ 0 ∧
        (0 < x i l → lam i / lam i₀ * a i l - ψ l / lam i₀ = 0)) ∧
      ∀ j l, ψ l / lam i₀ - η j / lam i₀ * b j l = 0) := by
  have k1 : ∀ i l, lam i / lam i₀ * a i l - ψ l / lam i₀ = (lam i * a i l - ψ l) / lam i₀ :=
    fun i l => by field_simp
  have k2 : ∀ j l, ψ l / lam i₀ - η j / lam i₀ * b j l = (ψ l - η j * b j l) / lam i₀ :=
    fun j l => by field_simp
  simp only [k1, k2, div_eq_zero_iff, hl.ne', or_false]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i l => ⟨div_nonpos_of_nonpos_of_nonneg (h1 i l).1 hl.le, (h1 i l).2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i l => ⟨?_, (h1 i l).2⟩, h2⟩
    have := (h1 i l).1
    rwa [div_nonpos_iff, or_iff_right (fun h => absurd h.2 (not_le.mpr hl)), and_iff_left hl.le]
      at this

/-- **Section 16.F** (MWG, p. 565). In the economy of Section 16.F (`J ≥ 1`, `L ≥ 1`, `∇uᵢ ≫ 0`,
`∇Fⱼ ≫ 0` everywhere), with quasiconcave utilities and convex `Fⱼ`, every Pareto optimal
allocation is a price equilibrium with transfers at some prices `p ≫ 0` (the multipliers `μ` of
(16.F.1)), with wealth levels `wᵢ = p·xᵢ`. -/
theorem section_16_F_pareto_isPriceEqm [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) {a : Allocation ι κ L} (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧
      (economy16F u F ω).IsPriceEqmWithTransfers a p (fun i => p ⬝ᵥ a.x i) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, hcsF⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  refine ⟨μ, hμpos, ?_, fun j => ?_, fun i => ?_, hc⟩
  · change ∑ i, μ ⬝ᵥ a.x i = μ ⬝ᵥ ω + ∑ j, μ ⬝ᵥ a.y j
    have hc' : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  · exact firm_max_of_foc (hFc j) (hy j) (hF j (a.y j)) (hγ0 j) (hcsF j) (hfoc_y j)
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · exact consumer_max_of_foc (hq i) (fun x _ => (hu i x).continuousAt.continuousWithinAt)
        (fun x _ y hxy => by
          by_cases h : x = y
          · rw [h]
          · exact (strictMono_of_grad_pos (hu i) (hupos i) hxy h).le)
        (hx i) (hu i (a.x i)) hμpos hpos (hfoc i) (hfoc_eq i)
    · have hx0 : a.x i = 0 := funext fun l => by
        by_contra hne
        have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
        have := hfoc_eq i l hxl
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      refine ⟨⟨hx i, le_rfl⟩, fun y hy => ?_⟩
      have hy0 : y = 0 := by
        by_contra hne
        have := dotProduct_pos_of_nonneg_ne_zero hy.1 hne hμpos
        rw [dotProduct_comm] at this
        have h2 : μ ⬝ᵥ y ≤ μ ⬝ᵥ a.x i := hy.2
        rw [hx0, dotProduct_zero] at h2
        linarith
      rw [hy0, hx0]
      exact le_rfl

/-- **Section 16.F** (MWG, p. 565), both directions: in the economy of Section 16.F with
quasiconcave utilities and convex `Fⱼ`, an allocation is Pareto optimal if and only if it is a
price equilibrium with transfers for some price vector (and wealth levels). -/
theorem section_16_F_pareto_iff_priceEqm [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) (a : Allocation ι κ L) :
    (economy16F u F ω).IsParetoOptimal a ↔
      ∃ p w, (economy16F u F ω).IsPriceEqmWithTransfers a p w := by
  constructor
  · intro hpo
    obtain ⟨p, -, h⟩ := section_16_F_pareto_isPriceEqm hL hu hupos hF hFpos hq hFc i₀ hpo
    exact ⟨p, _, h⟩
  · rintro ⟨p, w, h⟩
    refine proposition_16_C_1 (fun i => rationalOn_utilityPref _ _) (fun i => ?_) h
    have hsm : PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)) :=
      fun x _ y _ hxy hne => by
        have := strictMono_of_grad_pos (hu i) (hupos i) hxy (Ne.symm hne)
        exact ⟨this.le, not_le.mpr this⟩
    exact exercise_3_B_1b_orthant hL (exercise_3_B_1a hL hsm)

/-- **Proposition 16.F.1** (MWG, p. 566). In the economy of Section 16.F with concave utilities and
convex `Fⱼ` (`J ≥ 1`, `L ≥ 1`, `∇uᵢ ≫ 0`, `∇Fⱼ ≫ 0`), every Pareto optimal allocation maximizes a
weighted sum of utilities `∑ᵢ λᵢ uᵢ(xᵢ)` subject to `x ≥ 0`, the resource constraints and the
technology constraints, with `λ ≥ 0`, `λ_{i₀} = 1`. At the supporting prices `p = μ ≫ 0`, every
consumer with `λᵢ > 0` satisfies (16.F.10) with marginal utility of wealth `αᵢ = 1/λᵢ`; a consumer
with `λᵢ = 0` consumes nothing. -/
theorem proposition_16_F_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hcc : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) {a : Allocation ι κ L} (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ lam : ι → ℝ, lam i₀ = 1 ∧ (∀ i, 0 ≤ lam i) ∧
      (∀ (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ), (∀ i l, 0 ≤ x i l) →
        (∀ l, ∑ i, x i l ≤ ω l + ∑ j, y j l) → (∀ j, F j (y j) ≤ 0) →
        ∑ i, lam i * u i (x i) ≤ ∑ i, lam i * u i (a.x i)) ∧
      ∃ p, StrictlyPositive p ∧ (∀ i, lam i = 0 → a.x i = 0) ∧
        ∀ i, 0 < lam i → ∀ l, u' i (a.x i) (Pi.single l 1) - (1 / lam i) * p l ≤ 0 ∧
          (0 < a.x i l → u' i (a.x i) (Pi.single l 1) - (1 / lam i) * p l = 0) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, hcsF⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  have hc' : ∀ l, ∑ i, a.x i l = ω l + ∑ j, a.y j l := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply, economy16F, PrefEconomy.ofUtility] using this
  have hzero : ∀ i, δ i = 0 → a.x i = 0 := fun i hz => funext fun l => by
    by_contra hne
    have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
    have := hfoc_eq i l hxl
    rw [hz, zero_mul, zero_sub, neg_eq_zero] at this
    exact absurd this (hμpos l).ne'
  refine ⟨δ, hδ1, hδ0, fun x y hxnn hres hFy => ?_, μ, hμpos, hzero, fun i hpos l => ?_⟩
  · -- the Lagrangian sufficiency argument
    have hcons : ∀ i, δ i * u i (x i) ≤ δ i * u i (a.x i) + δ i * u' i (a.x i) (x i - a.x i) :=
      fun i => by
        have := concaveOn_le_tangent (hcc i) (hx i) (fun l => hxnn i l) (hu i (a.x i))
        nlinarith [hδ0 i]
    have hgrad : ∀ i, δ i * u' i (a.x i) (x i - a.x i) ≤ ∑ l, μ l * (x i l - a.x i l) :=
      fun i => by
        rw [clm_apply_eq_sum_partials, Finset.mul_sum]
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← mul_assoc, Pi.sub_apply]
        rcases (hx i l).lt_or_eq with hxl | hxl
        · have := hfoc_eq i l hxl
          have h2 : δ i * u' i (a.x i) (Pi.single l 1) = μ l := by linarith
          rw [h2]
        · rw [← hxl, sub_zero]
          exact mul_le_mul_of_nonneg_right (by linarith [hfoc i l]) (hxnn i l)
    have hfirm : ∀ j, ∑ l, μ l * (y j l - a.y j l) ≤ γ j * F j (y j) := fun j => by
      have htan := convexOn_tangent_le (hFc j) (Set.mem_univ (a.y j)) (Set.mem_univ (y j))
        (hF j (a.y j))
      have h1 : ∑ l, μ l * (y j l - a.y j l) = γ j * F' j (a.y j) (y j - a.y j) := by
        rw [clm_apply_eq_sum_partials, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show μ l = γ j * F' j (a.y j) (Pi.single l 1) by linarith [hfoc_y j l], Pi.sub_apply]
        ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_left htan (hγ0 j)
      nlinarith [hcsF j]
    have hres' : ∑ i, ∑ l, μ l * (x i l - a.x i l) ≤ ∑ j, ∑ l, μ l * (y j l - a.y j l) := by
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := κ))]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      refine mul_le_mul_of_nonneg_left ?_ (hμ0 l)
      linarith [hres l, hc' l]
    have h1 : ∑ i, δ i * u i (x i) ≤ ∑ i, δ i * u i (a.x i) +
        ∑ i, ∑ l, μ l * (x i l - a.x i l) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => (hcons i).trans (by linarith [hgrad i])
    have h2 : ∑ j, ∑ l, μ l * (y j l - a.y j l) ≤ 0 :=
      (Finset.sum_le_sum fun j _ => hfirm j).trans (Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hγ0 j) (hFy j))
    linarith
  · exact (foc_16F2_iff_16F10 hpos μ (a.x i)).mp (fun l => ⟨hfoc i l, hfoc_eq i l⟩) l

/-- **Footnote 18** (MWG, p. 563), correction 7: strictly positive gradients do not give the
constraint qualification of Theorem M.K.2 (linear independence of the binding constraint
gradients). Two consumers and one good, `u₁(x) = u₂(x) = x`, one firm `F(y) = y`, `ω̄ = 1`, and the
requirement `ū₂ = 1`: the solution of (16.F.1) is `x₁ = 0`, `x₂ = 1`, `y = 0`; four constraints
bind (consumer 2's utility, the resource constraint, the technology and `x₁ ≥ 0`) and their
gradients sum to zero. (The Kuhn-Tucker conditions still hold: `exercise_16_F_2`.) -/
theorem footnote_18_counterexample :
    IsSolution16F1 (ι := Fin 2) (κ := Unit) (L := 1) (fun _ x => x 0) (fun _ y => y 0) ![1] 0
        ![0, 1] (![![0], ![1]], fun _ => 0) ∧
      ¬ LinearIndependent ℝ ![resLin (ι := Fin 2) (κ := Unit) 0,
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projY ()),
        -((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projX 0)),
        -((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projX 1))] := by
  refine ⟨⟨⟨fun i hi => ?_, fun l => ?_, fun _ => le_rfl, fun i l => ?_⟩, ?_⟩, ?_⟩
  · fin_cases i
    · exact absurd rfl hi
    · simp
  · fin_cases l; simp [Fin.sum_univ_two]
  · fin_cases i <;> fin_cases l <;> simp
  · rintro v' ⟨hu, hres, hF, hnn⟩
    have h1 := hu 1 (by decide)
    have h2 := hres 0
    have h3 := hF ()
    have h4 := hnn 1 0
    simp [Fin.sum_univ_two] at h1 h2 h3 ⊢
    linarith
  · rw [Fintype.not_linearIndependent_iff]
    refine ⟨fun _ => 1, ?_, 0, one_ne_zero⟩
    refine ContinuousLinearMap.ext fun v => ?_
    simp [Fin.sum_univ_succ, resLin, projX, projY]
    ring

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The three efficiency conditions (MWG Exercise 16.F.4, pp. 564-565)

Problems (16.F.7) (allocation of given aggregates across consumers) and (16.F.8) (efficient
production across technologies) and the ratio conditions (16.F.4)-(16.F.6), at interior solutions,
with differentiability at the solution:

* (16.F.7) ⟹ (16.F.4): all consumers' marginal rates of substitution coincide
  (`exercise_16_F_4_i`).
* (16.F.8) ⟹ (16.F.5): all firms' marginal rates of transformation coincide
  (`exercise_16_F_4_ii`).
* (16.F.6): every consumer's marginal rate of substitution equals every firm's marginal rate of
  transformation (`exercise_16_F_4_iii`).

Departure: the book derives the conditions from Lagrangian first-order conditions, and (16.F.6)
from problem (16.F.9) in the value functions `u(x̄)`, `f(ȳ)`, which presupposes that these value
functions are differentiable and obey envelope identities that the book does not establish. We
prove each ratio condition directly by the underlying first-order (perturbation) argument: if two
gradients are not proportional in goods `ℓ, ℓ'`, a small reallocation along a direction in which
one gradient is positive and the other negative is feasible and improves the objective; for
(16.F.6) the reallocation is between consumer `i₀` and a firm in problem (16.F.1).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- If two pairs of positive numbers are not proportional, some direction `(d₁, d₂)` makes the
first linear form positive and the second negative. -/
theorem exists_sep_direction {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) (hne : a₁ * b₂ ≠ a₂ * b₁) :
    ∃ d₁ d₂ : ℝ, 0 < a₁ * d₁ + a₂ * d₂ ∧ b₁ * d₁ + b₂ * d₂ < 0 := by
  set D := a₁ * b₂ - a₂ * b₁ with hD
  set N := a₁ * b₁ + a₂ * b₂ with hN
  have hNpos : 0 < N := by positivity
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hneg | hpos
  · refine ⟨-b₂ - (-D) / (2 * N) * b₁, b₁ - (-D) / (2 * N) * b₂, ?_, ?_⟩
    · have : a₁ * (-b₂ - -D / (2 * N) * b₁) + a₂ * (b₁ - -D / (2 * N) * b₂) = -D / 2 := by
        field_simp; rw [hD, hN]; ring
      rw [this]; linarith
    · have : b₁ * (-b₂ - -D / (2 * N) * b₁) + b₂ * (b₁ - -D / (2 * N) * b₂) =
          -(-D / (2 * N)) * (b₁ ^ 2 + b₂ ^ 2) := by ring
      rw [this]
      have : 0 < -D / (2 * N) := div_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg b₁, mul_pos hb₁ hb₁]
  · refine ⟨b₂ - D / (2 * N) * b₁, -b₁ - D / (2 * N) * b₂, ?_, ?_⟩
    · have : a₁ * (b₂ - D / (2 * N) * b₁) + a₂ * (-b₁ - D / (2 * N) * b₂) = D / 2 := by
        field_simp; rw [hD, hN]; ring
      rw [this]; linarith
    · have : b₁ * (b₂ - D / (2 * N) * b₁) + b₂ * (-b₁ - D / (2 * N) * b₂) =
          -(D / (2 * N)) * (b₁ ^ 2 + b₂ ^ 2) := by ring
      rw [this]
      have : 0 < D / (2 * N) := div_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg b₁, mul_pos hb₁ hb₁]

/-- Along a direction with positive derivative, a function eventually (for small `t > 0`)
exceeds its value. -/
theorem eventually_gt_along {g : (Fin L → ℝ) → ℝ} {g' : (Fin L → ℝ) →L[ℝ] ℝ} {z d : Fin L → ℝ}
    (hg : HasFDerivAt g g' z) (hd : 0 < g' d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g z < g (z + t • d) := by
  have := mk_eventually_gt_of_deriv_pos (mc_line_hasDerivAt hg d) hd
  simpa using this

/-- Strictly positive coordinates stay positive under small perturbations. -/
theorem eventually_pos_along {z d : Fin L → ℝ} (hz : ∀ l, 0 < z l) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ l, 0 < (z + t • d) l := by
  rw [eventually_all]
  intro l
  have hc : Continuous fun t : ℝ => (z + t • d) l := by fun_prop
  have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hz l))
  exact eventually_nhdsWithin_of_eventually_nhds this

/-- The direction `d₁ eₗ + d₂ eₗ'` evaluated by a linear form. -/
theorem single_eq_smul_single (l : Fin L) (c : ℝ) :
    (Pi.single l c : Fin L → ℝ) = c • Pi.single l 1 := by
  funext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

/-- The direction `d₁ eₗ + d₂ eₗ'` evaluated by a linear form. -/
theorem clm_two_dir (φ : (Fin L → ℝ) →L[ℝ] ℝ) (l l' : Fin L) (d₁ d₂ : ℝ) :
    φ (Pi.single l d₁ + Pi.single l' d₂) = φ (Pi.single l 1) * d₁ + φ (Pi.single l' 1) * d₂ := by
  rw [map_add, single_eq_smul_single l d₁, single_eq_smul_single l' d₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **Problem (16.F.7)** (MWG, p. 564): distribute the aggregate `x̄` to maximize `u_{i₀}`
subject to `uᵢ(xᵢ) ≥ ūᵢ` (`i ≠ i₀`), `∑ᵢ xᵢ ≤ x̄` and `x ≥ 0`. -/
def Problem16F7 (u : ι → (Fin L → ℝ) → ℝ) (xb : Fin L → ℝ) (i₀ : ι) (ub : ι → ℝ) :
    Set (ι → Fin L → ℝ) :=
  {x | (∀ i, i ≠ i₀ → ub i ≤ u i (x i)) ∧ (∀ l, ∑ i, x i l ≤ xb l) ∧ ∀ i l, 0 ≤ x i l}

/-- **Exercise 16.F.4**, (16.F.7) ⟹ (16.F.4) (MWG, p. 576). At an interior solution `x ≫ 0` of
(16.F.7), with every `uᵢ` differentiable at `xᵢ` with positive partial derivatives, every
consumer's marginal rate of substitution between goods `ℓ, ℓ'` equals consumer `i₀`'s (hence all
coincide): `∂u_{i₀}/∂xₗ · ∂uᵢ/∂xₗ' = ∂u_{i₀}/∂xₗ' · ∂uᵢ/∂xₗ`. -/
theorem exercise_16_F_4_i {u : ι → (Fin L → ℝ) → ℝ} {xb : Fin L → ℝ} {i₀ : ι}
    {ub : ι → ℝ} {x : ι → Fin L → ℝ} (hx : x ∈ Problem16F7 u xb i₀ ub)
    (hopt : ∀ x' ∈ Problem16F7 u xb i₀ ub, u i₀ (x' i₀) ≤ u i₀ (x i₀))
    (hint : ∀ i l, 0 < x i l) {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (x i)) (hpos : ∀ i l, 0 < u' i (Pi.single l 1))
    (i : ι) (l l' : Fin L) :
    u' i₀ (Pi.single l 1) * u' i (Pi.single l' 1) =
      u' i₀ (Pi.single l' 1) * u' i (Pi.single l 1) := by
  classical
  by_contra hne
  by_cases hii : i = i₀
  · subst hii; exact hne (mul_comm _ _)
  obtain ⟨d₁, d₂, hpos₀, hneg⟩ := exists_sep_direction (hpos i₀ l) (hpos i₀ l') (hpos i l)
    (hpos i l') hne
  set d : Fin L → ℝ := Pi.single l d₁ + Pi.single l' d₂ with hd
  -- consumer `i₀` receives `t d`, consumer `i` gives it up
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i₀ (x i₀) < u i₀ (x i₀ + t • d) :=
    eventually_gt_along (hu i₀) (by rw [hd, clm_two_dir]; exact hpos₀)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i (x i) < u i (x i + t • -d) :=
    eventually_gt_along (hu i) (by rw [map_neg, hd, clm_two_dir]; linarith)
  have h3 := eventually_pos_along (z := x i₀) (d := d) (hint i₀)
  have h4 := eventually_pos_along (z := x i) (d := -d) (hint i)
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := (h1.and (h2.and (h3.and h4))).exists
  set x' : ι → Fin L → ℝ := fun k =>
    if k = i₀ then x i₀ + t • d else if k = i then x i + t • -d else x k with hx'
  have hx'i₀ : x' i₀ = x i₀ + t • d := by simp [hx']
  have hx'i : x' i = x i + t • -d := by simp [hx', hii]
  have hmem : x' ∈ Problem16F7 u xb i₀ ub := by
    refine ⟨fun k hk => ?_, fun m => ?_, fun k m => ?_⟩
    · by_cases hki : k = i
      · subst hki; rw [hx'i]; exact (hx.1 k hk).trans ht2.le
      · simpa [hx', hk, hki] using hx.1 k hk
    · have hsum : ∑ k, x' k = ∑ k, x k := by
        have : ∀ k, x' k = x k + (if k = i₀ then t • d else 0) - (if k = i then t • d else 0) :=
          fun k => by
            by_cases h1 : k = i₀
            · subst h1; simp [hx', Ne.symm hii]
            · by_cases h2 : k = i
              · subst h2; simp [hx', h1, sub_eq_add_neg]
              · simp [hx', h1, h2]
        simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, add_sub_cancel_right]
      have := congrFun hsum m
      simp only [Finset.sum_apply] at this
      rw [this]
      exact hx.2.1 m
    · by_cases h1 : k = i₀
      · subst h1; rw [hx'i₀]; exact (ht3 m).le
      · by_cases h2 : k = i
        · subst h2; rw [hx'i]; exact (ht4 m).le
        · simpa [hx', h1, h2] using hx.2.2 k m
  have := hopt x' hmem
  rw [hx'i₀] at this
  linarith

/-- **Problem (16.F.8)** (MWG, p. 564): maximize the total output `∑ⱼ y₁ⱼ` of good `0` subject to
`∑ⱼ yₗⱼ ≥ ȳₗ` for the other goods and `Fⱼ(yⱼ) ≤ 0`. -/
def Problem16F8 (F : κ → (Fin L → ℝ) → ℝ) (l₀ : Fin L) (yb : Fin L → ℝ) : Set (κ → Fin L → ℝ) :=
  {y | (∀ l, l ≠ l₀ → yb l ≤ ∑ j, y j l) ∧ ∀ j, F j (y j) ≤ 0}

/-- **Exercise 16.F.4**, (16.F.8) ⟹ (16.F.5) (MWG, p. 576). At a solution of (16.F.8), with
every `Fⱼ` differentiable at `yⱼ` with positive partial derivatives, all firms' marginal rates of
transformation between good `l₀` and every good `ℓ` coincide. -/
theorem exercise_16_F_4_ii {F : κ → (Fin L → ℝ) → ℝ} {l₀ : Fin L}
    {yb : Fin L → ℝ} {y : κ → Fin L → ℝ} (hy : y ∈ Problem16F8 F l₀ yb)
    (hopt : ∀ y' ∈ Problem16F8 F l₀ yb, ∑ j, y' j l₀ ≤ ∑ j, y j l₀)
    {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ} (hF : ∀ j, HasFDerivAt (F j) (F' j) (y j))
    (hpos : ∀ j l, 0 < F' j (Pi.single l 1)) (j j' : κ) (l : Fin L) :
    F' j (Pi.single l₀ 1) * F' j' (Pi.single l 1) =
      F' j (Pi.single l 1) * F' j' (Pi.single l₀ 1) := by
  classical
  by_contra hne
  by_cases hjj : j = j'
  · subst hjj; exact hne (mul_comm _ _)
  by_cases hl : l = l₀
  · subst hl; exact hne rfl
  -- a direction `d` with `∇Fⱼ·d > 0 > ∇Fⱼ'·d`: firm `j'` moves along `d` and firm `j` along `-d`
  -- plus a little extra output of good `l₀`; both stay feasible and total output rises
  obtain ⟨d₁, d₂, hposj, hnegj'⟩ := exists_sep_direction (hpos j l₀) (hpos j l) (hpos j' l₀)
    (hpos j' l) (by intro h; exact hne (by linarith))
  set d : Fin L → ℝ := Pi.single l₀ d₁ + Pi.single l d₂ with hd
  have hFj'd : F' j' d < 0 := by rw [hd, clm_two_dir]; exact hnegj'
  have hFjd : F' j (-d) < 0 := by rw [map_neg, hd, clm_two_dir]; linarith
  -- add a little extra output of `l₀` to firm `j` while keeping its derivative negative
  set s : ℝ := -(F' j (-d)) / (2 * F' j (Pi.single l₀ 1)) with hs
  have hs0 : 0 < s := div_pos (by linarith) (by linarith [hpos j l₀])
  set e : Fin L → ℝ := -d + Pi.single l₀ s with he
  have hFje : F' j e < 0 := by
    have h1 : F' j e = F' j (-d) + s * F' j (Pi.single l₀ 1) := by
      rw [he, map_add, single_eq_smul_single l₀ s, map_smul, smul_eq_mul]
    have h2 : s * F' j (Pi.single l₀ 1) = -(F' j (-d)) / 2 := by
      have hne0 := (hpos j l₀).ne'
      rw [hs]; field_simp
    rw [h1, h2]
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j' (y j' + t • d) < F j' (y j') := by
    have := eventually_gt_along (g := fun z => -F j' z) (d := d) (hF j').neg (by
      simp only [neg_apply]; linarith)
    exact this.mono fun t ht => by linarith
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j (y j + t • e) < F j (y j) := by
    have := eventually_gt_along (g := fun z => -F j z) (d := e) (hF j).neg (by
      simp only [neg_apply]; linarith)
    exact this.mono fun t ht => by linarith
  obtain ⟨t, ht1, ht2, ht0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  set y' : κ → Fin L → ℝ := fun k =>
    if k = j then y j + t • e else if k = j' then y j' + t • d else y k with hy'
  have hy'j : y' j = y j + t • e := by simp [hy']
  have hy'j' : y' j' = y j' + t • d := by simp [hy', Ne.symm hjj]
  have hsum : ∑ k, y' k = ∑ k, y k + t • Pi.single l₀ s := by
    have : ∀ k, y' k = y k + (if k = j then t • e else 0) + (if k = j' then t • d else 0) :=
      fun k => by
        by_cases h1 : k = j
        · rw [h1, hy'j]; simp [hjj]
        · by_cases h2 : k = j'
          · rw [h2, hy'j']; simp [Ne.symm hjj]
          · simp [hy', h1, h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [he]
    module
  have hmem : y' ∈ Problem16F8 F l₀ yb := by
    refine ⟨fun m hm => ?_, fun k => ?_⟩
    · have := congrFun hsum m
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_of_ne hm, mul_zero, add_zero] at this
      rw [this]
      exact hy.1 m hm
    · by_cases h1 : k = j
      · subst h1; rw [hy'j]; exact ht2.le.trans (hy.2 k)
      · by_cases h2 : k = j'
        · subst h2; rw [hy'j']; exact ht1.le.trans (hy.2 k)
        · simpa [hy', h1, h2] using hy.2 k
  have := hopt y' hmem
  have h3 := congrFun hsum l₀
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same] at h3
  rw [h3] at this
  have : 0 < t * s := mul_pos ht0 hs0
  linarith

/-- **Exercise 16.F.4**, (16.F.6) (MWG, p. 576). At a solution `(x, y)` of (16.F.1) with
`x_{i₀} ≫ 0`, `u_{i₀}` differentiable at `x_{i₀}` and `Fⱼ` at `yⱼ` with positive partial
derivatives, consumer `i₀`'s marginal rate of substitution between goods `ℓ, ℓ'` equals firm
`j`'s marginal rate of transformation. -/
theorem exercise_16_F_4_iii {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    (hint : ∀ l, 0 < v.1 i₀ l) {u' : (Fin L → ℝ) →L[ℝ] ℝ} (hu : HasFDerivAt (u i₀) u' (v.1 i₀))
    (hupos : ∀ l, 0 < u' (Pi.single l 1)) {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1))
    (j : κ) (l l' : Fin L) :
    u' (Pi.single l 1) * F' j (Pi.single l' 1) = u' (Pi.single l' 1) * F' j (Pi.single l 1) := by
  classical
  by_contra hne
  obtain ⟨d₁, d₂, hposu, hnegF⟩ := exists_sep_direction (hupos l) (hupos l') (hFpos j l)
    (hFpos j l') hne
  set d : Fin L → ℝ := Pi.single l d₁ + Pi.single l' d₂ with hd
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i₀ (v.1 i₀) < u i₀ (v.1 i₀ + t • d) :=
    eventually_gt_along hu (by rw [hd, clm_two_dir]; exact hposu)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j (v.2 j + t • d) < F j (v.2 j) := by
    have := eventually_gt_along (g := fun z => -F j z) (d := d) (hF j).neg (by
      simp only [neg_apply, hd, clm_two_dir]; linarith)
    exact this.mono fun t ht => by linarith
  have h3 := eventually_pos_along (z := v.1 i₀) (d := d) hint
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and h3)).exists
  set x' := Function.update v.1 i₀ (v.1 i₀ + t • d) with hx'
  set y' := Function.update v.2 j (v.2 j + t • d) with hy'
  have hmem : (x', y') ∈ Problem16F1 u F ω i₀ ub := by
    refine ⟨fun i hi => ?_, fun m => ?_, fun k => ?_, fun i m => ?_⟩
    · simpa [hx', hi] using hv.1.1 i hi
    · have hx : ∑ i, x' i m = ∑ i, v.1 i m + t * d m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => v.1 i m) (Finset.mem_univ i₀)]
        have : ∑ i ∈ Finset.univ.erase i₀, x' i m = ∑ i ∈ Finset.univ.erase i₀, v.1 i m :=
          Finset.sum_congr rfl fun i hi => by simp [hx', Finset.ne_of_mem_erase hi]
        rw [this]
        simp [hx']
        ring
      have hy : ∑ k, y' k m = ∑ k, v.2 k m + t * d m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
          ← Finset.add_sum_erase _ (fun k => v.2 k m) (Finset.mem_univ j)]
        have : ∑ k ∈ Finset.univ.erase j, y' k m = ∑ k ∈ Finset.univ.erase j, v.2 k m :=
          Finset.sum_congr rfl fun k hk => by simp [hy', Finset.ne_of_mem_erase hk]
        rw [this]
        simp [hy']
        ring
      rw [hx, hy]
      linarith [hv.1.2.1 m]
    · by_cases hk : k = j
      · subst hk; simp only [hy', Function.update_self]; exact ht2.le.trans (hv.1.2.2.1 k)
      · simpa [hy', hk] using hv.1.2.2.1 k
    · by_cases hi : i = i₀
      · subst hi; simp only [hx', Function.update_self]; exact (ht3 m).le
      · simpa [hx', hi] using hv.1.2.2.2 i m
  have := hv.2 _ hmem
  simp only [hx', Function.update_self] at this
  linarith

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Nonconvex production and marginal cost pricing (MWG Section 16.G, pp. 570-572)

* The marginal cost price equilibrium with transfers (conditions (i)-(iii) of Proposition 16.G.1,
  `PrefEconomy.IsMCPriceEqm`).
* **Proposition 16.G.1** (= **Exercise 16.G.1**): under the assumptions of Section 16.F (no
  convexity of production) and quasiconcave utilities, every Pareto optimum is a marginal cost
  price equilibrium with transfers, with `p ≫ 0`.
* **Exercise 16.G.2**: with one input and one output, (16.G.1) says that the input price is the
  output price times the marginal product, i.e. the output price is marginal cost.
* **Figure 16.G.1**: a Pareto optimum whose only supporting (marginal cost) prices make the firm
  incur a loss, so that shutting down is more profitable.
* **Figure 16.G.2**: a marginal cost price equilibrium that is not Pareto optimal.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Proposition 16.G.1** (MWG, p. 571). A marginal cost price equilibrium with transfers for
production sets `Yⱼ = {Fⱼ ≤ 0}`: wealth levels summing to `p·ω̄ + ∑ⱼ p·yⱼ`, (i) every `yⱼ ∈ Yⱼ`
has `p = γⱼ ∇Fⱼ(yⱼ)` for some `γⱼ > 0` (16.G.1), (ii) every `xᵢ` is maximal in her budget set,
(iii) markets clear. -/
def PrefEconomy.IsMCPriceEqm (E : PrefEconomy ι κ L) (F : κ → (Fin L → ℝ) → ℝ)
    (a : Allocation ι κ L) (p : Fin L → ℝ) (w : ι → ℝ) : Prop :=
  ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧
    (∀ j, a.y j ∈ E.Y j ∧ ∃ F' : (Fin L → ℝ) →L[ℝ] ℝ, HasFDerivAt (F j) F' (a.y j) ∧
      ∃ γ : ℝ, 0 < γ ∧ ∀ l, p l = γ * F' (Pi.single l 1)) ∧
    (∀ i, IsMaximalFor (E.pref i) (budgetSetOn (E.X i) p (w i)) (a.x i)) ∧
    ∑ i, a.x i = E.ω + ∑ j, a.y j

/-- **Proposition 16.G.1** (MWG, p. 571). In the economy of Section 16.F (`J ≥ 1`, `L ≥ 1`,
`∇uᵢ ≫ 0`, `∇Fⱼ ≫ 0` everywhere; no convexity of the `Fⱼ`), with quasiconcave utilities, every
Pareto optimal allocation is a marginal cost price equilibrium with transfers with `p ≫ 0` and
wealth levels `wᵢ = p·xᵢ`. -/
theorem proposition_16_G_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (i₀ : ι) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, -⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  refine ⟨μ, hμpos, ?_, fun j => ⟨hy j, F' j (a.y j), hF j _, γ j, ?_, fun l => ?_⟩,
    fun i => ?_, hc⟩
  · change ∑ i, μ ⬝ᵥ a.x i = μ ⬝ᵥ ω + ∑ j, μ ⬝ᵥ a.y j
    have hc' : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  · by_contra h
    have h0 : γ j = 0 := le_antisymm (not_lt.mp h) (hγ0 j)
    have := hfoc_y j ⟨0, hL⟩
    rw [h0, zero_mul, sub_zero] at this
    linarith [hμpos ⟨0, hL⟩]
  · linarith [hfoc_y j l]
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · exact consumer_max_of_foc (hq i) (fun x _ => (hu i x).continuousAt.continuousWithinAt)
        (fun x _ y hxy => by
          by_cases h : x = y
          · rw [h]
          · exact (strictMono_of_grad_pos (hu i) (hupos i) hxy h).le)
        (hx i) (hu i (a.x i)) hμpos hpos (hfoc i) (hfoc_eq i)
    · have hx0 : a.x i = 0 := funext fun l => by
        by_contra hne
        have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
        have := hfoc_eq i l hxl
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      refine ⟨⟨hx i, le_rfl⟩, fun y hy => ?_⟩
      have hy0 : y = 0 := by
        by_contra hne
        have := dotProduct_pos_of_nonneg_ne_zero hy.1 hne hμpos
        rw [dotProduct_comm] at this
        have h2 : μ ⬝ᵥ y ≤ μ ⬝ᵥ a.x i := hy.2
        rw [hx0, dotProduct_zero] at h2
        linarith
      rw [hy0, hx0]
      exact le_rfl

/-- **Exercise 16.G.1** (MWG, p. 576): Proposition 16.G.1 proved from the first-order conditions
(16.F.2)-(16.F.3) (this is how `proposition_16_G_1` is proved). -/
theorem exercise_16_G_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (i₀ : ι) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) :=
  proposition_16_G_1 hL hu hupos hF hFpos hq i₀ hpo

/-- **Exercise 16.G.2** (MWG, p. 576). Two goods, an input (good 1) and an output (good 2), and
the technology `q ≤ φ(z)`, i.e. `F(y) = y₂ - φ(-y₁)`, at a plan using `z` units of input with
marginal product `φ'(z) > 0`. Condition (16.G.1), `p = γ ∇F(y)` with `γ > 0`, says that the input
price equals the output price times the marginal product, equivalently that the output price
equals marginal cost `p₁/φ'(z)`. -/
theorem exercise_16_G_2 {φ : ℝ → ℝ} {m z q : ℝ} (hφ : HasDerivAt φ m z) (hm : 0 < m)
    {F' : (Fin 2 → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt (fun y : Fin 2 → ℝ => y 1 - φ (-y 0)) F' ![-z, q])
    {p : Fin 2 → ℝ} {γ : ℝ} (hp : ∀ l, p l = γ * F' (Pi.single l 1)) :
    p 0 = p 1 * m ∧ p 1 = p 0 / m := by
  -- the derivative of `F` is `y ↦ y₂ + φ'(z) y₁`
  have hinner : HasFDerivAt (fun y : Fin 2 → ℝ => -y 0)
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)) ![-z, q] :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt.neg
  have hval : -(![-z, q] : Fin 2 → ℝ) 0 = z := by simp
  have hφ' : HasDerivAt φ m (-(![-z, q] : Fin 2 → ℝ) 0) := by rw [hval]; exact hφ
  have hcomp := hφ'.comp_hasFDerivAt (![-z, q] : Fin 2 → ℝ) hinner
  have hG := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt.sub
    hcomp
  have huniq := hF.unique hG
  have h0 : F' (Pi.single 0 1) = m := by rw [huniq]; simp
  have h1 : F' (Pi.single 1 1) = 1 := by rw [huniq]; simp
  have hp0 := hp 0
  have hp1 := hp 1
  rw [h0] at hp0
  rw [h1, mul_one] at hp1
  refine ⟨by rw [hp0, hp1], ?_⟩
  rw [hp0, hp1]
  field_simp

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Marginal cost pricing: examples and exercises (MWG Section 16.G, pp. 571-572, 576)

* **Figure 16.G.1**: one consumer (`u = x₁x₂`), the increasing-returns technology `q ≤ z²` and
  `ω̄ = (3/2, 0)`. The optimum `x* = (1/2, 1)` is a marginal cost price equilibrium only at prices
  proportional to `(2, 1)`, at which the firm makes a loss and would rather shut down.
* **Figure 16.G.2**: with `u = x₁ + x₂` and `ω̄ = (1, 0)`, `x* = (1/2, 1/4)` is a marginal cost
  price equilibrium at `p = (1, 1)` that is not Pareto optimal.
* **Exercise 16.G.3**: a one-consumer, one-firm economy with two inputs and one output and a
  non-quasiconcave production function in which the marginal cost price equilibrium (with
  efficient production) is unique and the inputs are not chosen at minimum cost.
* **Exercise 16.G.4**: with a single consumer, an optimum is a marginal cost price equilibrium
  (Proposition 16.G.1), and an optimum exists when the set of feasible allocations is compact.
  The book's "under the general conditions of Section 16.G" does not guarantee an optimum: in
  `noOptimumEconomy` every assumption of Section 16.F holds and no allocation is Pareto optimal
  (correction 5).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

/-- The technology `q ≤ z²` of Figures 16.G.1-16.G.2 as `F(y) = y₂ - y₁²` on `y₁ ≤ 0`. -/
def sqTechF (y : Fin 2 → ℝ) : ℝ := y 1 - y 0 ^ 2

/-- The production set `{y : y₁ ≤ 0, F(y) ≤ 0}` of Figures 16.G.1-16.G.2 (nonconvex). -/
def sqTechY : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ sqTechF y ≤ 0}

/-- The derivative of `sqTechF` at `y`: `∂F/∂y₁ = -2y₁`, `∂F/∂y₂ = 1`. -/
theorem sqTechF_hasFDerivAt (y : Fin 2 → ℝ) :
    ∃ F' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt sqTechF F' y ∧
      F' (Pi.single 0 1) = -2 * y 0 ∧ F' (Pi.single 1 1) = 1 := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := y)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := y)
  have key := h1.sub (h0.mul h0)
  refine ⟨_, key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_), ?_, ?_⟩
  · simp [sqTechF, sq]
  · simp; ring
  · simp

/-- **Figure 16.G.1** (MWG, p. 571). One consumer with `u(x) = x₁x₂`, the technology `sqTechY`,
`ω̄ = (3/2, 0)`. -/
noncomputable def fig16G1Economy : PrefEconomy Unit Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) (fun _ x => x 0 * x 1) (fun _ => sqTechY)
    ![3 / 2, 0]

/-- The optimum of Figure 16.G.1: `x* = (1/2, 1)`, `y* = (-1, 1)`. -/
noncomputable def fig16G1Alloc : Allocation Unit Unit 2 := ⟨fun _ => ![1 / 2, 1], fun _ => ![-1, 1]⟩

/-- **Figure 16.G.1** (MWG, p. 571). The allocation `x* = (1/2, 1)` is Pareto optimal (it maximizes
the consumer's utility) and is a marginal cost price equilibrium at `p = (2, 1)`; every marginal
cost price equilibrium supporting it has `p₁ = 2p₂` (the only supporting relative prices); at these
prices the firm makes a loss, and shutting down (`0 ∈ Y`) is more profitable. -/
theorem figure_16_G_1 :
    fig16G1Economy.IsParetoOptimal fig16G1Alloc ∧
      fig16G1Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G1Alloc ![2, 1] (fun _ => 2) ∧
      (∀ p w, fig16G1Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G1Alloc p w →
        p 0 = 2 * p 1 ∧ 0 < p 1 ∧ p ⬝ᵥ fig16G1Alloc.y () < p ⬝ᵥ (0 : Fin 2 → ℝ) ∧
          (0 : Fin 2 → ℝ) ∈ sqTechY) := by
  have hfeas : fig16G1Economy.IsFeasible fig16G1Alloc := by
    refine ⟨⟨fun _ l => ?_, fun _ => ⟨by simp [fig16G1Alloc], by
      simp [fig16G1Alloc, sqTechF]⟩⟩, ?_⟩
    · fin_cases l <;> norm_num [fig16G1Alloc]
    · funext l; fin_cases l <;> norm_num [fig16G1Economy, PrefEconomy.ofUtility, fig16G1Alloc]
  refine ⟨⟨hfeas, ?_⟩, ⟨?_, fun _ => ⟨hfeas.1.2 (), ?_⟩, fun _ => ⟨⟨hfeas.1.1 (), ?_⟩,
    fun x hx => ?_⟩, hfeas.2⟩, fun p w h => ?_⟩
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Fin.isValue, Finset.sum_apply,
      Finset.sum_singleton, fig16G1Economy, PrefEconomy.ofUtility, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add] at h0 h1
    obtain ⟨hy0, hy1⟩ := hy' ()
    simp only [sqTechF] at hy1
    have hx0 := hx' () 0
    have hx1 := hx' () 1
    change a'.x () 0 * a'.x () 1 ≤ (fig16G1Alloc.x ()) 0 * (fig16G1Alloc.x ()) 1
    simp only [fig16G1Alloc, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hle : a'.x () 1 ≤ a'.y () 0 ^ 2 := by linarith
    have hcub : (3 / 2 + a'.y () 0) * a'.y () 0 ^ 2 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a'.y () 0 + 1), sq_nonneg (a'.y () 0)]
    calc a'.x () 0 * a'.x () 1 ≤ a'.x () 0 * a'.y () 0 ^ 2 :=
          mul_le_mul_of_nonneg_left hle hx0
      _ = (3 / 2 + a'.y () 0) * a'.y () 0 ^ 2 := by rw [h0]
      _ ≤ 1 / 2 * 1 := by linarith
  · simp [fig16G1Economy, PrefEconomy.ofUtility, fig16G1Alloc]
    norm_num
  · obtain ⟨F', hF', h0, h1⟩ := sqTechF_hasFDerivAt (fig16G1Alloc.y ())
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0, fig16G1Alloc]
    · simp [h1]
  · simp [fig16G1Alloc]
    norm_num
  · change x 0 * x 1 ≤ (fig16G1Alloc.x ()) 0 * (fig16G1Alloc.x ()) 1
    have hb := hx.2
    rw [dot_two] at hb
    simp only [fig16G1Alloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ⊢
    have := hx.1 0
    have := hx.1 1
    nlinarith [sq_nonneg (2 * x 0 - x 1)]
  · obtain ⟨-, F', hF', γ, hγ, hp⟩ := h.2.1 ()
    obtain ⟨G', hG', hG0, hG1⟩ := sqTechF_hasFDerivAt (fig16G1Alloc.y ())
    have huniq := hF'.unique hG'
    have hp0 := hp 0
    have hp1 := hp 1
    rw [huniq, hG0] at hp0
    rw [huniq, hG1] at hp1
    simp only [Fin.isValue, fig16G1Alloc, one_div, Matrix.cons_val_zero, mul_neg, mul_one,
      neg_neg] at hp0
    refine ⟨by rw [hp0, hp1]; ring, by rw [hp1]; linarith, ?_, ⟨le_rfl, by simp [sqTechF]⟩⟩
    rw [dot_two, dot_two]
    simp [fig16G1Alloc, hp0, hp1]
    linarith

/-- **Figure 16.G.2** (MWG, p. 572). One consumer with `u(x) = x₁ + x₂`, the technology `sqTechY`,
`ω̄ = (1, 0)`. -/
def fig16G2Economy : PrefEconomy Unit Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) (fun _ x => x 0 + x 1) (fun _ => sqTechY)
    ![1, 0]

/-- The allocation of Figure 16.G.2: `x* = (1/2, 1/4)`, `y* = (-1/2, 1/4)`. -/
noncomputable def fig16G2Alloc : Allocation Unit Unit 2 :=
  ⟨fun _ => ![1 / 2, 1 / 4], fun _ => ![-1 / 2, 1 / 4]⟩

/-- **Figure 16.G.2** (MWG, p. 572). `x*` is a marginal cost price equilibrium with transfers at
`p = (1, 1)` but is not Pareto optimal: `x' = (0, 1)` (produced with `y' = (-1, 1)`) is better. -/
theorem figure_16_G_2 :
    fig16G2Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G2Alloc ![1, 1] (fun _ => 3 / 4) ∧
      ¬ fig16G2Economy.IsParetoOptimal fig16G2Alloc := by
  have hfeasY : fig16G2Alloc.y () ∈ sqTechY :=
    ⟨by norm_num [fig16G2Alloc], by norm_num [fig16G2Alloc, sqTechF]⟩
  refine ⟨⟨?_, fun _ => ⟨hfeasY, ?_⟩, fun _ => ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · simp [fig16G2Economy, PrefEconomy.ofUtility, fig16G2Alloc]
    norm_num
  · obtain ⟨F', hF', h0, h1⟩ := sqTechF_hasFDerivAt (fig16G2Alloc.y ())
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0, fig16G2Alloc]; norm_num
    · simp [h1]
  · fin_cases l <;> norm_num [fig16G2Alloc]
  · simp [fig16G2Alloc]
    norm_num
  · change x 0 + x 1 ≤ (fig16G2Alloc.x ()) 0 + (fig16G2Alloc.x ()) 1
    have hb := hx.2
    rw [dot_two] at hb
    simp only [fig16G2Alloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ⊢
    linarith
  · funext l; fin_cases l <;> norm_num [fig16G2Economy, PrefEconomy.ofUtility, fig16G2Alloc]
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨fun _ => ![0, 1], fun _ => ![-1, 1]⟩, ⟨⟨fun _ l => ?_, fun _ => ⟨?_, ?_⟩⟩, ?_⟩,
      fun _ => ?_, (), ?_⟩
    · fin_cases l <;> norm_num
    · norm_num
    · norm_num [sqTechF]
    · funext l; fin_cases l <;> norm_num [fig16G2Economy, PrefEconomy.ofUtility]
    · simp only [fig16G2Economy, PrefEconomy.ofUtility, utilityPref, fig16G2Alloc]
      norm_num
    · simp only [fig16G2Economy, PrefEconomy.ofUtility, utilityPref, fig16G2Alloc, Strict]
      norm_num

/-! ## Exercise 16.G.3 -/

/-- **Exercise 16.G.3** (MWG, p. 576). Inputs `z₁, z₂`, output `q ≤ f(z) = z₁ + z₂ + z₁² + z₂²`
(not quasiconcave), written as `F(y) = y₃ + y₁ + y₂ - y₁² - y₂²` on `y₁, y₂ ≤ 0`. -/
def ex16G3F (y : Fin 3 → ℝ) : ℝ := y 2 + y 0 + y 1 - y 0 ^ 2 - y 1 ^ 2

/-- The production set of Exercise 16.G.3. -/
def ex16G3Y : Set (Fin 3 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ 0 ∧ ex16G3F y ≤ 0}

/-- The economy of Exercise 16.G.3: one consumer who values only the output (`u(x) = x₃`), the
endowment `ω̄ = (1, 1, 0)` of inputs, one firm. -/
def ex16G3Economy : PrefEconomy Unit Unit 3 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 3) (fun _ x => x 2) (fun _ => ex16G3Y) ![1, 1, 0]

/-- The derivative of `ex16G3F`. -/
theorem ex16G3F_hasFDerivAt (y : Fin 3 → ℝ) :
    ∃ F' : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt ex16G3F F' y ∧ F' (Pi.single 0 1) = 1 - 2 * y 0 ∧
      F' (Pi.single 1 1) = 1 - 2 * y 1 ∧ F' (Pi.single 2 1) = 1 := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x := y)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt (x := y)
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt (x := y)
  have key := (((h2.add h0).add h1).sub (h0.mul h0)).sub (h1.mul h1)
  refine ⟨_, key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_), ?_, ?_, ?_⟩
  · simp [ex16G3F, sq]
  · simp; ring
  · simp; ring
  · simp

/-- **Exercise 16.G.3** (MWG, p. 576). In `ex16G3Economy`, `x* = (0, 0, 4)`, `y* = (-1, -1, 4)`,
`p = (3, 3, 1)` form a marginal cost price equilibrium; it is the only one with efficient
production (`F(y*) = 0`), up to the scale of `p`; the production function is not quasiconcave;
and the input bundle `(1, 1)` does not minimize the cost of producing `4` at input prices `(3, 3)`
(the bundle `(8/5, 0)` produces more at cost `24/5 < 6`). -/
theorem exercise_16_G_3 :
    ex16G3Economy.IsMCPriceEqm (fun _ => ex16G3F) ⟨fun _ => ![0, 0, 4], fun _ => ![-1, -1, 4]⟩
        ![3, 3, 1] (fun _ => 4) ∧
      (∀ (a : Allocation Unit Unit 3) p w, ex16G3Economy.IsMCPriceEqm (fun _ => ex16G3F) a p w →
        ex16G3F (a.y ()) = 0 →
        a.x () = ![0, 0, 4] ∧ a.y () = ![-1, -1, 4] ∧ ∃ γ : ℝ, 0 < γ ∧ p = γ • ![3, 3, 1]) ∧
      (1 + 1 + 1 ^ 2 + 1 ^ 2 : ℝ) < min (2 + 0 + 2 ^ 2 + 0 ^ 2) (0 + 2 + 0 ^ 2 + 2 ^ 2) ∧
      (![-8 / 5, 0, 4] : Fin 3 → ℝ) ∈ ex16G3Y ∧ (3 * (8 / 5) + 3 * 0 : ℝ) < 3 * 1 + 3 * 1 := by
  have hdot : ∀ p x : Fin 3 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 + p 2 * x 2 := fun p x => by
    simp [dotProduct, Fin.sum_univ_three]
  refine ⟨⟨?_, fun _ => ⟨⟨by norm_num, by norm_num, by norm_num [ex16G3F]⟩, ?_⟩,
    fun _ => ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩, ?_⟩, fun a p w h hF0 => ?_, by norm_num,
    ⟨by norm_num, by norm_num, by norm_num [ex16G3F]⟩, by norm_num⟩
  · simp [ex16G3Economy, PrefEconomy.ofUtility, hdot]
    norm_num
  · obtain ⟨F', hF', h0, h1, h2⟩ := ex16G3F_hasFDerivAt ![-1, -1, 4]
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0]; norm_num
    · simp [h1]; norm_num
    · simp [h2]
  · fin_cases l <;> norm_num
  · simp [hdot]
  · change x 2 ≤ (![0, 0, 4] : Fin 3 → ℝ) 2
    have hb := hx.2
    rw [hdot] at hb
    have := hx.1 0
    have := hx.1 1
    simp at hb ⊢
    linarith
  · funext l; fin_cases l <;> norm_num [ex16G3Economy, PrefEconomy.ofUtility]
  · -- uniqueness
    obtain ⟨⟨hy0, hy1, -⟩, F', hF', γ, hγ, hp⟩ := h.2.1 ()
    obtain ⟨G', hG', hG0, hG1, hG2⟩ := ex16G3F_hasFDerivAt (a.y ())
    have huniq := hF'.unique hG'
    have hp0 : p 0 = γ * (1 - 2 * a.y () 0) := by rw [hp 0, huniq, hG0]
    have hp1 : p 1 = γ * (1 - 2 * a.y () 1) := by rw [hp 1, huniq, hG1]
    have hp2 : p 2 = γ := by rw [hp 2, huniq, hG2, mul_one]
    have hp0pos : 0 < p 0 := by rw [hp0]; nlinarith
    have hp1pos : 0 < p 1 := by rw [hp1]; nlinarith
    have hp2pos : 0 < p 2 := by rw [hp2]; exact hγ
    have hclear : a.x () = ![1, 1, 0] + a.y () := by
      have := h.2.2.2
      simpa [ex16G3Economy, PrefEconomy.ofUtility] using this
    have hmax := h.2.2.1 ()
    have hxX : ∀ l, 0 ≤ a.x () l := hmax.1.1
    have hxb : p ⬝ᵥ a.x () ≤ w () := hmax.1.2
    -- the consumer buys no inputs
    have hin : ∀ l : Fin 3, l ≠ 2 → a.x () l = 0 := by
      intro l hl
      by_contra hne
      have hpos : 0 < a.x () l := lt_of_le_of_ne (hxX l) (Ne.symm hne)
      have hpl : 0 < p l := by
        fin_cases l
        · exact hp0pos
        · exact hp1pos
        · exact absurd rfl hl
      set z : Fin 3 → ℝ := a.x () - Pi.single l (a.x () l) +
        Pi.single 2 (p l * a.x () l / p 2) with hz
      have hzl : z l = 0 := by
        simp [hz, hl]
      have hz2 : z 2 = a.x () 2 + p l * a.x () l / p 2 := by
        simp [hz, Ne.symm hl]
      have hzX : ∀ m, 0 ≤ z m := fun m => by
        by_cases hm : m = l
        · rw [hm, hzl]
        · by_cases hm2 : m = 2
          · rw [hm2, hz2]
            have : 0 ≤ p l * a.x () l / p 2 :=
              div_nonneg (mul_nonneg hpl.le (hxX l)) hp2pos.le
            linarith [hxX 2]
          · simp [hz, hm, hm2, hxX m]
      have hcost : p ⬝ᵥ z = p ⬝ᵥ a.x () := by
        simp only [hz, dotProduct_add, dotProduct_sub, dotProduct_single]
        field_simp
        ring
      have := hmax.2 z ⟨hzX, by rw [hcost]; exact hxb⟩
      change z 2 ≤ a.x () 2 at this
      rw [hz2] at this
      have : 0 < p l * a.x () l / p 2 := div_pos (mul_pos hpl hpos) hp2pos
      linarith
    have hx0 := hin 0 (by decide)
    have hx1 := hin 1 (by decide)
    have hya0 : a.y () 0 = -1 := by
      have := congrFun hclear 0; simp at this; linarith
    have hya1 : a.y () 1 = -1 := by
      have := congrFun hclear 1; simp at this; linarith
    have hya2 : a.y () 2 = 4 := by
      simp only [ex16G3F, hya0, hya1] at hF0; linarith
    have hyeq : a.y () = ![-1, -1, 4] := by
      funext l; fin_cases l
      · simpa using hya0
      · simpa using hya1
      · simpa using hya2
    refine ⟨?_, hyeq, γ, hγ, ?_⟩
    · rw [hclear, hyeq]
      funext l; fin_cases l <;> norm_num
    · funext l
      fin_cases l
      · simp [hp0, hya0]; norm_num
      · simp [hp1, hya1]; norm_num
      · simp [hp2]

/-! ## Exercise 16.G.4 -/

/-- **Exercise 16.G.4** (MWG, p. 576). With a single consumer and the assumptions of Section 16.F
(quasiconcave utility; no convexity of production), if the set of feasible allocations is
nonempty and compact, there is an optimum, and it is a marginal cost price equilibrium. -/
theorem exercise_16_G_4 {L : ℕ} {κ : Type*} [Fintype κ] [Nonempty κ] (hL : 0 < L)
    {u : Unit → (Fin L → ℝ) → ℝ} {u' : Unit → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i))
    (hA : IsCompact (economy16F u F ω).feasiblePairs)
    (hne : (economy16F u F ω).feasiblePairs.Nonempty) :
    ∃ a : Allocation Unit κ L, (economy16F u F ω).IsParetoOptimal a ∧
      ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) := by
  have hcont : ContinuousOn (fun z : (Unit → Fin L → ℝ) × (κ → Fin L → ℝ) => u () (z.1 ()))
      (economy16F u F ω).feasiblePairs := by
    have : Continuous (u ()) := continuous_iff_continuousAt.mpr fun x => (hu () x).continuousAt
    exact (this.comp ((continuous_apply ()).comp continuous_fst)).continuousOn
  obtain ⟨z, hz, hmax⟩ := hA.exists_isMaxOn hne hcont
  have hpo : (economy16F u F ω).IsParetoOptimal ⟨z.1, z.2⟩ := by
    refine ⟨hz, ?_⟩
    rintro ⟨a', ha', -, k, hk⟩
    have h1 : u () (a'.x ()) ≤ u () (z.1 ()) := hmax (show (a'.x, a'.y) ∈ _ from ha')
    exact hk.2 h1
  exact ⟨_, hpo, proposition_16_G_1 hL hu hupos hF hFpos hq () hpo⟩

/-- The utility and technologies of `noOptimumEconomy`: `u(x) = x₁ + x₂`,
`F₁(y) = y₁ + 2y₂`, `F₂(y) = 2y₁ + y₂`. -/
def noOptimumF : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun y => y 0 + 2 * y 1, fun y => 2 * y 0 + y 1]

/-- **Exercise 16.G.4** (MWG, p. 576), correction 5: the assumptions of Section 16.F do not
guarantee an optimum. With one consumer, `u(x) = x₁ + x₂`, two firms `F₁(y) = y₁ + 2y₂`,
`F₂(y) = 2y₁ + y₂` (gradients `≫ 0`, `Fⱼ(0) = 0`) and `ω̄ = 0`, the plans `(2, -1)` and `(-1, 2)`
together produce `(1, 1)` from nothing, so no feasible allocation is Pareto optimal (and there is
no marginal cost price equilibrium that is an optimum). -/
theorem exercise_16_G_4_needs_optimum :
    (∀ j y, ∃ F' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt (noOptimumF j) F' y ∧
      ∀ l, 0 < F' (Pi.single l 1)) ∧ (∀ j, noOptimumF j 0 = 0) ∧
    ∀ a : Allocation Unit (Fin 2) 2,
      ¬ (economy16F (fun _ x => x 0 + x 1) noOptimumF 0).IsParetoOptimal a := by
  refine ⟨fun j y => ?_, fun j => by fin_cases j <;> simp [noOptimumF], fun a hpo => ?_⟩
  · have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := y)
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := y)
    fin_cases j
    · refine ⟨_, (h0.add (h1.const_smul (2 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_), fun l => ?_⟩
      · simp [noOptimumF]
      · fin_cases l <;> simp
    · refine ⟨_, ((h0.const_smul (2 : ℝ)).add h1).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_), fun l => ?_⟩
      · simp [noOptimumF]
      · fin_cases l <;> simp
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  apply hpo.2
  refine ⟨⟨fun _ => a.x () + ![1, 1], ![a.y 0 + ![2, -1], a.y 1 + ![-1, 2]]⟩,
    ⟨⟨fun _ l => ?_, fun j => ?_⟩, ?_⟩, fun _ => ?_, (), ?_⟩
  · have := hx () l; fin_cases l <;> simp at this ⊢ <;> linarith
  · have := hy j
    fin_cases j <;>
      simp [economy16F, PrefEconomy.ofUtility, noOptimumF, Matrix.vecHead, Matrix.vecTail]
        at this ⊢ <;>
      linarith
  · have := hc
    simp only [economy16F, PrefEconomy.ofUtility] at this ⊢
    rw [Fin.sum_univ_two] at this ⊢
    funext l
    have := congrFun this l
    fin_cases l <;> simp [Matrix.vecHead, Matrix.vecTail] at this ⊢ <;> linarith
  · simp only [economy16F, PrefEconomy.ofUtility, utilityPref]
    simp; linarith
  · simp only [economy16F, PrefEconomy.ofUtility, utilityPref, Strict]
    simp; constructor <;> linarith

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Interpretations of the commodity space (MWG Section 16.G, pp. 566-570)

* **Example 16.G.1** (contingent commodities), footnote 20: with `I` consumers who may each be
  sick or healthy there are `2^I` states, and a consumer buying medical care when sick buys
  `2^{I-1}` contingent commodities.
* **Example 16.G.2** (occupational choice): the consumption set
  `Xᵢ = {(cᵢ, t_{ci}, t_{ei}) : cᵢ ≥ 0, t_{ci} ≤ 0, t_{ei} ≤ 0, T̄ᵢ + t_{ei} + αᵢ t_{ci} ≥ 0}` is
  nonempty, closed and convex; a preference increasing in consumption is locally nonsatiated on
  it; the production set of a concave production function is convex. So the first welfare theorem
  applies to every price equilibrium with transfers of such an economy.
* **Example 16.G.3** (public goods), **Definition 16.G.1** (Lindahl equilibrium). As printed, the
  wealth condition `∑ᵢ wᵢ = ∑ᵢ p₁x*₁ᵢ + (∑ᵢ p₂ᵢ)q* - p₁z*` is not the condition
  `∑ᵢ wᵢ = p·ω̄ + p·y*` of a price equilibrium with transfers of the artificial economy, which reads
  `∑ᵢ wᵢ = p₁ω̄₁ + (∑ᵢ p₂ᵢ)q* - p₁z*` (correction 6): with the printed condition and locally
  nonsatiated consumers, `p₁z* = 0`; and the artificial economy's equilibrium of
  `definition_16_G_1_printed_counterexample` satisfies the corrected but not the printed
  definition. With the corrected definition, every Lindahl equilibrium is Pareto optimal (the
  first welfare theorem). Footnote 23: at an interior Lindahl equilibrium with differentiable
  utilities and production function, `∑ᵢ MRSᵢ = MRT` (the Samuelson condition).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

/-! ## Example 16.G.1: contingent commodities -/

/-- **Example 16.G.1, footnote 20** (MWG, p. 567). With `I` consumers, each sick (`true`) or
healthy (`false`), there are `2^I` states, and the states in which a given consumer is sick are
`2^{I-1}` (`I ≥ 1`): the number of contingent medical care commodities she buys. -/
theorem footnote_20 {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Fintype.card (ι → Bool) = 2 ^ Fintype.card ι ∧
      Fintype.card {s : ι → Bool // s i = true} = 2 ^ (Fintype.card ι - 1) := by
  refine ⟨by simp, ?_⟩
  have e : {s : ι → Bool // s i = true} ≃ ({k // k ≠ i} → Bool) :=
    { toFun := fun s k => s.1 k.1
      invFun := fun g => ⟨fun k => if h : k = i then true else g ⟨k, h⟩, by simp⟩
      left_inv := fun s => by
        ext k
        by_cases h : k = i
        · subst h; simp [s.2]
        · simp [h]
      right_inv := fun g => by
        funext k
        simp [k.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

/-! ## Example 16.G.2: occupational choice -/

/-- **Example 16.G.2** (MWG, p. 568). The consumption set of an individual with `T̄` professorial
hours and comparative advantage `α`: bundles `(c, t_c, t_e)` with `c ≥ 0`, `t_c ≤ 0`, `t_e ≤ 0`
and leisure `T̄ + t_e + α t_c ≥ 0`. -/
def occupationalX (T α : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 1 ≤ 0 ∧ x 2 ≤ 0 ∧ 0 ≤ T + x 2 + α * x 1}

/-- **Example 16.G.2** (MWG, p. 568). The occupational consumption set is nonempty (for `T̄ ≥ 0`),
closed and convex. -/
theorem example_16_G_2_X {T α : ℝ} (hT : 0 ≤ T) :
    (0 : Fin 3 → ℝ) ∈ occupationalX T α ∧ IsClosed (occupationalX T α) ∧
      Convex ℝ (occupationalX T α) := by
  refine ⟨⟨le_rfl, le_rfl, le_rfl, by simpa using hT⟩, ?_, ?_⟩
  · have hc0 : Continuous fun x : Fin 3 → ℝ => x 0 := continuous_apply 0
    have hc1 : Continuous fun x : Fin 3 → ℝ => x 1 := continuous_apply 1
    have hc2 : Continuous fun x : Fin 3 → ℝ => x 2 := continuous_apply 2
    exact (isClosed_le continuous_const hc0).inter ((isClosed_le hc1 continuous_const).inter
      ((isClosed_le hc2 continuous_const).inter (isClosed_le continuous_const
        ((continuous_const.add hc2).add (continuous_const.mul hc1)))))
  · intro x hx y hy a b ha hb hab
    obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
    obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
    simp only [occupationalX, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨by positivity, by nlinarith, by nlinarith, ?_⟩
    have : T = a * T + b * T := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha hx3, mul_nonneg hb hy3]

/-- **Example 16.G.2** (MWG, p. 568). "Because the consumption good is desirable, the local
nonsatiation condition is satisfied": a utility strictly increasing in consumption `c` is locally
nonsatiated on the occupational consumption set. -/
theorem example_16_G_2_lns {T α : ℝ} {u : (Fin 3 → ℝ) → ℝ}
    (hu : ∀ x ∈ occupationalX T α, ∀ c : ℝ, 0 < c → u x < u (x + Pi.single 0 c)) :
    LocallyNonsatiated (occupationalX T α) (utilityPref u) := by
  intro x hx ε hε
  refine ⟨x + Pi.single 0 ε, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp; linarith [hx.1]
  · simpa using hx.2.1
  · simpa using hx.2.2.1
  · simpa using hx.2.2.2
  · rw [euclidDist_add_single, abs_of_pos hε]
  · exact (hu x hx ε hε).le
  · exact not_le.mpr (hu x hx ε hε)

/-- **Example 16.G.2** (MWG, p. 568). The production set
`{(q, -z_c, -z_e) : z ≥ 0, q ≤ f(z_c, z_e)}` of a concave production function is convex. -/
theorem example_16_G_2_Y {f : ℝ → ℝ → ℝ}
    (hf : ConcaveOn ℝ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} (fun z => f (z 0) (z 1))) :
    Convex ℝ {y : Fin 3 → ℝ | y 1 ≤ 0 ∧ y 2 ≤ 0 ∧ y 0 ≤ f (-y 1) (-y 2)} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hzx : (![-x 1, -x 2] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} := fun l => by
    fin_cases l <;> simp <;> linarith
  have hzy : (![-y 1, -y 2] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} := fun l => by
    fin_cases l <;> simp <;> linarith
  have := hf.2 hzx hzy ha hb hab
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  have e1 : -(a * x 1 + b * y 1) = a * -x 1 + b * -y 1 := by ring
  have e2 : -(a * x 2 + b * y 2) = a * -x 2 + b * -y 2 := by ring
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

/-! ## Example 16.G.3: public goods and Lindahl equilibrium -/

variable {ι : Type*} [Fintype ι]

/-- **Example 16.G.3** (MWG, p. 569). A feasible allocation of the public goods economy: private
consumptions `x₁ᵢ ≥ 0`, public good `q ≥ 0`, input `z ≥ 0` with `q ≤ f(z)` and
`∑ᵢ x₁ᵢ + z = ω̄₁`. Consumer `i` consumes the pair `(x₁ᵢ, q)`. -/
def PublicFeasible (ω₁ : ℝ) (f : ℝ → ℝ) (x : ι → ℝ) (q z : ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ 0 ≤ q ∧ 0 ≤ z ∧ q ≤ f z ∧ ∑ i, x i + z = ω₁

/-- **Example 16.G.3** (MWG, p. 569). Pareto optimality in the public goods economy, for
preferences `≿ᵢ` on pairs `(x₁ᵢ, x₂)`. -/
def PublicParetoOptimal (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) (x : ι → ℝ) (q z : ℝ) : Prop :=
  PublicFeasible ω₁ f x q z ∧ ¬ ∃ x' q' z', PublicFeasible ω₁ f x' q' z' ∧
    (∀ i, pref i ![x' i, q'] ![x i, q]) ∧ ∃ i, Strict (pref i) ![x' i, q'] ![x i, q]

/-- **Definition 16.G.1** (MWG, pp. 569-570), corrected (correction 6). A Lindahl equilibrium (with
transfers): wealth levels with `∑ᵢ wᵢ = p₁ω̄₁ + (∑ᵢ p₂ᵢ)q* - p₁z*` (the condition
`∑ᵢ wᵢ = p·ω̄ + p·y*` of the artificial economy), (i) `q* ≤ f(z*)`, `z* ≥ 0` and profit
maximization at the personalized prices, (ii) every `(x*₁ᵢ, q*)` maximal in
`{(x₁ᵢ, x₂ᵢ) ≥ 0 : p₁x₁ᵢ + p₂ᵢx₂ᵢ ≤ wᵢ}`, (iii) `∑ᵢ x*₁ᵢ + z* = ω̄₁` (and `x*₂ᵢ = q*`). -/
def IsLindahlEqm (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ) (f : ℝ → ℝ)
    (x : ι → ℝ) (q z p₁ : ℝ) (p₂ w : ι → ℝ) : Prop :=
  ∑ i, w i = p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, IsMaximalFor (pref i) {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i}
      ![x i, q]) ∧
    ∑ i, x i + z = ω₁

/-- **Definition 16.G.1** (MWG, pp. 569-570) as printed: the wealth condition reads
`∑ᵢ wᵢ = ∑ᵢ p₁x*₁ᵢ + (∑ᵢ p₂ᵢ)q* - p₁z*`. -/
def IsLindahlEqmPrinted (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ) (f : ℝ → ℝ)
    (x : ι → ℝ) (q z p₁ : ℝ) (p₂ w : ι → ℝ) : Prop :=
  ∑ i, w i = ∑ i, p₁ * x i + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, IsMaximalFor (pref i) {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i}
      ![x i, q]) ∧
    ∑ i, x i + z = ω₁

/-- **Definition 16.G.1**, correction 6. Given market clearing, the printed wealth condition is
the corrected one minus `p₁z*`: the two agree only when `p₁z* = 0`. -/
theorem definition_16_G_1_wealth_gap {ω₁ p₁ q z : ℝ} {x p₂ : ι → ℝ}
    (hc : ∑ i, x i + z = ω₁) :
    ∑ i, p₁ * x i + (∑ i, p₂ i) * q - p₁ * z =
      (p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z) - p₁ * z := by
  rw [← Finset.mul_sum, ← hc]
  ring

/-- **Definition 16.G.1**, correction 6. Under the printed definition, if every consumer is locally
nonsatiated (on `ℝ²₊`, transitive preferences), then `p₁z* = 0`: the printed definition excludes
every equilibrium that uses a positive amount of a valued input. -/
theorem definition_16_G_1_printed_forces {pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    {x : ι → ℝ} {q z p₁ : ℝ} {p₂ w : ι → ℝ}
    (h : IsLindahlEqmPrinted pref ω₁ f x q z p₁ p₂ w) : p₁ * z = 0 := by
  -- every consumer spends her wealth
  have hspend : ∀ i, p₁ * x i + p₂ i * q = w i := by
    intro i
    have hmax := h.2.2.1 i
    refine le_antisymm hmax.1.2 ?_
    by_contra hlt
    push Not at hlt
    have hmem : (![x i, q] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => hmax.1.1 l
    have hpd : (![p₁, p₂ i] : Fin 2 → ℝ) ⬝ᵥ ![x i, q] < w i := by
      rw [dot_two]; simpa using hlt
    obtain ⟨v, hv, hpv, hs⟩ := lns_exists_better_cheaper (hlns i) _ hmem hpd
    rw [dot_two] at hpv
    exact hs.2 (hmax.2 v ⟨hv, by simpa using hpv.le⟩)
  have h1 := h.1
  have h2 : ∑ i, w i = ∑ i, p₁ * x i + (∑ i, p₂ i) * q := by
    rw [← Finset.sum_congr rfl fun i _ => hspend i, Finset.sum_add_distrib, Finset.sum_mul]
  linarith

/-- The utility `u(x₁, x₂) = x₁ + x₂` of the one-consumer example. -/
def lindahlExampleU : (Fin 2 → ℝ) → ℝ := fun v => v 0 + v 1

/-- **Definition 16.G.1**, correction 6. One consumer with `u = x₁ + x₂`, `ω̄₁ = 1`, `f(z) = z`:
`x*₁ = q* = z* = 1/2`, `p₁ = p₂ = 1`, `w = 1` is a Lindahl equilibrium (the price equilibrium of the
artificial economy), but there is no wealth level for which it satisfies the printed
definition. -/
theorem definition_16_G_1_printed_counterexample :
    IsLindahlEqm (fun _ : Unit => utilityPref lindahlExampleU) 1 id (fun _ => 1 / 2) (1 / 2)
        (1 / 2) 1 (fun _ => 1) (fun _ => 1) ∧
      ∀ w, ¬ IsLindahlEqmPrinted (fun _ : Unit => utilityPref lindahlExampleU) 1 id
        (fun _ => 1 / 2) (1 / 2) (1 / 2) 1 (fun _ => 1) w := by
  refine ⟨⟨by norm_num, ⟨by simp, by norm_num, fun q' z' _ hq => ?_⟩, fun _ => ⟨⟨fun l => ?_,
    by norm_num⟩, fun v hv => ?_⟩, by norm_num⟩, fun w h => ?_⟩
  · simp only [Finset.univ_unique, Finset.sum_singleton, id] at hq ⊢
    linarith
  · fin_cases l <;> norm_num
  · change v 0 + v 1 ≤ (![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 + (![1 / 2, 1 / 2] : Fin 2 → ℝ) 1
    have := hv.2
    norm_num at this ⊢
    linarith
  · have h1 := h.1
    have h2 := (h.2.2.1 ()).1.2
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1 h2
    norm_num at h1 h2
    linarith

/-- **Example 16.G.3** (MWG, p. 570): "every Lindahl equilibrium is Pareto optimal". With locally
nonsatiated, transitive preferences on `ℝ²₊`, every Lindahl equilibrium (Definition 16.G.1,
corrected) is a Pareto optimum of the public goods economy. -/
theorem lindahl_isParetoOptimal {pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant 2) (pref i))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    {x : ι → ℝ} {q z p₁ : ℝ} {p₂ w : ι → ℝ} [Nonempty ι]
    (h : IsLindahlEqm pref ω₁ f x q z p₁ p₂ w) : PublicParetoOptimal pref ω₁ f x q z := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hmax := h.2.2.1
  have hbud : ∀ i v, v ∈ nonnegOrthant 2 → p₁ * v 0 + p₂ i * v 1 =
      (![p₁, p₂ i] : Fin 2 → ℝ) ⬝ᵥ v := fun i v _ => by rw [dot_two]; simp
  have hfeas : PublicFeasible ω₁ f x q z :=
    ⟨fun i => by simpa using (hmax i).1.1 0, by simpa using (hmax i₀).1.1 1, h.2.1.2.1,
      h.2.1.1, h.2.2.2⟩
  refine ⟨hfeas, ?_⟩
  rintro ⟨x', q', z', ⟨hx', hq', hz', hf', hc'⟩, hle, k, hk⟩
  -- the budget-set form of (16.C.1)-(16.C.2) for each consumer
  have hX : ∀ i, (![x' i, q'] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun i l => by
    fin_cases l
    · simpa using hx' i
    · simpa using hq'
  have hbudget : ∀ i, budgetSetOn (nonnegOrthant 2) ![p₁, p₂ i] (w i) =
      {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i} := fun i => by
    ext v
    simp only [budgetSetOn, Set.mem_ofPred_eq, dot_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rfl
  have hge : ∀ i, w i ≤ p₁ * x' i + p₂ i * q' := fun i => by
    have := exercise_16_C_2 (hlns i) (hr i).2 (by rw [hbudget]; exact hmax i) (hX i) (hle i)
    rw [dot_two] at this
    simpa using this
  have hgt : w k < p₁ * x' k + p₂ k * q' := by
    have := equation_16_C_1 (by rw [hbudget]; exact hmax k) (hX k) hk
    rw [dot_two] at this
    simpa using this
  have h1 : ∑ i, w i < ∑ i, (p₁ * x' i + p₂ i * q') :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 := h.2.1.2.2 q' z' hz' hf'
  have h3 : ∑ i, (p₁ * x' i + p₂ i * q') = p₁ * ω₁ - p₁ * z' + (∑ i, p₂ i) * q' := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← hc']
    ring
  linarith [h.1]

/-- **Footnote 23** (MWG, p. 570), the Samuelson condition. At a Lindahl equilibrium with
`p₁ > 0` and an interior input choice `z* > 0`, if `f` is differentiable at `z*` with `f'(z*) > 0`
and each consumer's utility `uᵢ`, differentiable at her interior bundle `(x*₁ᵢ, q*) ≫ 0` with
`∂uᵢ/∂x₁ > 0`, represents `≿ᵢ`, then `p₂ᵢ/p₁ = MRSᵢ = (∂uᵢ/∂x₂)/(∂uᵢ/∂x₁)` for every `i` and
`∑ᵢ p₂ᵢ/p₁ = MRT = 1/f'(z*)`; hence `∑ᵢ MRSᵢ = MRT`. -/
theorem footnote_23 {u : ι → (Fin 2 → ℝ) → ℝ} {ω₁ : ℝ} {f : ℝ → ℝ} {x : ι → ℝ}
    {q z p₁ : ℝ} {p₂ w : ι → ℝ}
    (h : IsLindahlEqm (fun i => utilityPref (u i)) ω₁ f x q z p₁ p₂ w) (hp₁ : 0 < p₁)
    {u' : ι → (Fin 2 → ℝ) →L[ℝ] ℝ} (hu : ∀ i, HasFDerivAt (u i) (u' i) ![x i, q])
    (hu1 : ∀ i, 0 < u' i (Pi.single 0 1)) (hx : ∀ i, 0 < x i) (hq : 0 < q)
    {f' : ℝ} (hf : HasDerivAt f f' z) (hf' : 0 < f') (hz : 0 < z) (hqf : q = f z) :
    (∀ i, p₂ i / p₁ = u' i (Pi.single 1 1) / u' i (Pi.single 0 1)) ∧
      ∑ i, p₂ i / p₁ = 1 / f' ∧
      ∑ i, u' i (Pi.single 1 1) / u' i (Pi.single 0 1) = 1 / f' := by
  -- the consumer's first-order condition along the budget line
  have hmrs : ∀ i, p₂ i / p₁ = u' i (Pi.single 1 1) / u' i (Pi.single 0 1) := by
    intro i
    set d : Fin 2 → ℝ := ![-(p₂ i / p₁), 1] with hd
    have hline : HasDerivAt (fun t : ℝ => u i (![x i, q] + t • d)) (u' i d) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => ![x i, q] + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (![x i, q] : Fin 2 → ℝ)
      have h2 : HasFDerivAt (u i) (u' i) (![x i, q] + (0 : ℝ) • d) := by simpa using hu i
      exact h2.comp_hasDerivAt 0 h1
    -- the line stays in the budget set near `t = 0`, so `t = 0` is a local maximum
    have hloc : IsLocalMax (fun t : ℝ => u i (![x i, q] + t • d)) 0 := by
      have hcont : Continuous fun t : ℝ => (![x i, q] + t • d : Fin 2 → ℝ) := by fun_prop
      have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (![x i, q] + t • d) l := by
        rw [eventually_all]
        intro l
        have := (continuous_apply l |>.comp hcont).continuousAt (x := 0)
        refine this.eventually (lt_mem_nhds ?_)
        fin_cases l
        · simpa using hx i
        · simpa using hq
      filter_upwards [hpos] with t ht
      have hmem : (![x i, q] + t • d : Fin 2 → ℝ) ∈ {v | (∀ l, 0 ≤ v l) ∧
          p₁ * v 0 + p₂ i * v 1 ≤ w i} := by
        refine ⟨fun l => (ht l).le, ?_⟩
        have hb := (h.2.2.1 i).1.2
        simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hb ⊢
        have : p₁ * (x i + t * -(p₂ i / p₁)) + p₂ i * (q + t * 1) =
            p₁ * x i + p₂ i * q := by field_simp; ring
        linarith
      have h3 : u i (![x i, q] + t • d) ≤ u i ![x i, q] := (h.2.2.1 i).2 _ hmem
      simpa using h3
    have hzero := hloc.hasDerivAt_eq_zero hline
    have hlin : u' i d = -(p₂ i / p₁) * u' i (Pi.single 0 1) + u' i (Pi.single 1 1) := by
      rw [clm_apply_eq_sum_partials, Fin.sum_univ_two]
      simp [hd]
      ring
    rw [hlin] at hzero
    have hu0 := hu1 i
    have e : u' i (Pi.single 1 1) = p₂ i / p₁ * u' i (Pi.single 0 1) := by linarith
    rw [e]
    field_simp
  -- the firm's first-order condition
  have hmrt : (∑ i, p₂ i) * f' = p₁ := by
    set P := ∑ i, p₂ i
    have hline : HasDerivAt (fun t : ℝ => P * f t - p₁ * t) (P * f' - p₁) z :=
      (hf.const_mul P).sub ((hasDerivAt_id z).const_mul p₁ |>.congr_deriv (by simp))
    have hloc : IsLocalMax (fun t : ℝ => P * f t - p₁ * t) z := by
      filter_upwards [lt_mem_nhds hz] with t ht
      have := h.2.1.2.2 (f t) t ht.le le_rfl
      rw [hqf] at this
      exact this
    have := hloc.hasDerivAt_eq_zero hline
    linarith
  have hsum : ∑ i, p₂ i / p₁ = 1 / f' := by
    rw [← Finset.sum_div, div_eq_div_iff hp₁.ne' hf'.ne']
    linarith
  exact ⟨hmrs, hsum, by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => (hmrs i).symm⟩

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 16.G.5: education with increasing returns (MWG pp. 576-577)

Education `e = (min{L, T})²` and food `f = (LT)^{1/2}` are produced from labor and land, the
endowment is `(ω_L, ω_T) = (1, 1)`, and utility is `u(e, f) = e^α f^{1-α}` with `α = 1/2`, i.e.
`u = √(ef)`. Food is the numeraire.

* (a) The optimum uses `L_e = T_e = 2/3`, produces `e = 4/9`, `f = 1/3`, `u = √(4/27)`.
* (b) Competitive food production gives factor prices `w_L = w_T = 1/2` (the marginal products at
  `L_f = T_f = 1/3`); the cost-minimizing cost of education is `C(e) = (w_L + w_T)√e`, whose
  marginal cost at `e = 4/9` is `3/4`. At `p_e = 3/4` and income `1 - τ` with the lump-sum tax
  `τ = 1/3` covering the deficit, the consumer demands exactly `e = 4/9` (and `f = 1/3`).
* (c) The tax is `τ = 1/3`.
* (d) Two consumers (one owns the land, one the labor); the deficit of marginal cost pricing,
  `C(e) - C'(e)e = (w_L + w_T)√e/2`, is taxed from the landowner.
* (e) With `w_L = w_T = 1/2` the marginal cost price equilibrium has `e = 4/9`, `f = 1/3`,
  `p_e = 3/4`, landowner transfer `1/3`; the landowner consumes `(1/9, 1/12)` and the laborer
  `(1/3, 1/4)`. It is Pareto optimal: the utilities sum to the maximal `√(4/27)`, which bounds the
  sum of utilities of every feasible allocation.
-/

namespace MWG.WelfareTheorems

/-- **Exercise 16.G.5(a)** (MWG, p. 577). For every division of the endowment `(1, 1)` (labor `L`
and land `T` to education, the rest to food), `ef ≤ 4/27`, with equality at `L = T = 2/3`
(`e = 4/9`, `f = 1/3`). So the optimal allocation of the endowments is `L_e = T_e = 2/3`,
`L_f = T_f = 1/3`. -/
theorem exercise_16_G_5a {L T : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    min L T ^ 2 * Real.sqrt ((1 - L) * (1 - T)) ≤ 4 / 27 ∧
      min (2 / 3 : ℝ) (2 / 3) ^ 2 * Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3)) = 4 / 27 ∧
      min (2 / 3 : ℝ) (2 / 3) ^ 2 = 4 / 9 ∧ Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = 1 / 3 := by
  have hsq : Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = 1 / 3 := by
    rw [show ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = (1 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, by rw [hsq]; norm_num, by norm_num, hsq⟩
  set m := min L T with hm
  have hmL : m ≤ L := min_le_left _ _
  have hmT : m ≤ T := min_le_right _ _
  have hm0 : 0 ≤ m := le_min hL0 hT0
  have hm1 : m ≤ 1 := hmL.trans hL1
  have hroot : Real.sqrt ((1 - L) * (1 - T)) ≤ 1 - m := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [mul_le_mul (by linarith : 1 - L ≤ 1 - m) (by linarith : 1 - T ≤ 1 - m)
      (by linarith) (by linarith)]
  calc m ^ 2 * Real.sqrt ((1 - L) * (1 - T)) ≤ m ^ 2 * (1 - m) :=
        mul_le_mul_of_nonneg_left hroot (sq_nonneg m)
    _ ≤ 4 / 27 := by nlinarith [sq_nonneg (m - 2 / 3), mul_nonneg (sq_nonneg (m - 2 / 3)) hm0]

/-- **Exercise 16.G.5(b)** (MWG, p. 577), factor prices. The marginal products of labor and land in
food production `f = √(LT)` at `L = T = 1/3` are both `1/2`; so competitive food production (food
the numeraire) gives `w_L = w_T = 1/2`. -/
theorem exercise_16_G_5b_wages :
    HasDerivAt (fun L : ℝ => Real.sqrt (L * (1 / 3))) (1 / 2) (1 / 3) ∧
      HasDerivAt (fun T : ℝ => Real.sqrt ((1 / 3) * T)) (1 / 2) (1 / 3) := by
  have h1 : HasDerivAt (fun L : ℝ => L * (1 / 3)) (1 / 3) (1 / 3) := by
    simpa using (hasDerivAt_id (1 / 3 : ℝ)).mul_const (1 / 3 : ℝ)
  have h2 : HasDerivAt (fun T : ℝ => (1 / 3) * T) (1 / 3) (1 / 3) := by
    simpa using (hasDerivAt_id (1 / 3 : ℝ)).const_mul (1 / 3 : ℝ)
  have hval : Real.sqrt ((1 / 3 : ℝ) * (1 / 3)) = 1 / 3 := by
    rw [show (1 / 3 : ℝ) * (1 / 3) = (1 / 3) ^ 2 by ring]
    exact Real.sqrt_sq (by norm_num)
  have hne : ((1 / 3 : ℝ) * (1 / 3)) ≠ 0 := by norm_num
  refine ⟨?_, ?_⟩
  · have := h1.sqrt hne
    rw [hval] at this
    convert this using 1
    norm_num
  · have := h2.sqrt hne
    rw [hval] at this
    convert this using 1
    norm_num

/-- **Exercise 16.G.5(b)** (MWG, p. 577), the cost of education. With factor prices `w_L, w_T ≥ 0`,
producing `e ≥ 0` units costs at least `(w_L + w_T)√e`, attained with `L = T = √e`. -/
theorem exercise_16_G_5b_cost {wL wT e : ℝ} (hwL : 0 ≤ wL) (hwT : 0 ≤ wT) (he : 0 ≤ e) :
    min (Real.sqrt e) (Real.sqrt e) ^ 2 = e ∧
      ∀ L T : ℝ, 0 ≤ L → 0 ≤ T → e ≤ min L T ^ 2 → (wL + wT) * Real.sqrt e ≤ wL * L + wT * T := by
  refine ⟨by rw [min_self, Real.sq_sqrt he], fun L T hL hT hle => ?_⟩
  have hs : Real.sqrt e ≤ min L T := by
    rw [Real.sqrt_le_left (le_min hL hT)]; exact hle
  nlinarith [mul_le_mul_of_nonneg_left (hs.trans (min_le_left L T)) hwL,
    mul_le_mul_of_nonneg_left (hs.trans (min_le_right L T)) hwT]

/-- **Exercise 16.G.5(b)** (MWG, p. 577), marginal cost. With `w_L = w_T = 1/2` the cost
`C(e) = √e` has marginal cost `3/4` at the optimal level `e = 4/9`. -/
theorem exercise_16_G_5b_mc :
    HasDerivAt (fun e : ℝ => (1 / 2 + 1 / 2) * Real.sqrt e) (3 / 4) (4 / 9) := by
  have hs : Real.sqrt (4 / 9 : ℝ) = 2 / 3 := by
    rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have := (Real.hasDerivAt_sqrt (by norm_num : (4 / 9 : ℝ) ≠ 0)).const_mul (1 / 2 + 1 / 2 : ℝ)
  rw [hs] at this
  convert this using 1
  norm_num

/-- **Exercise 16.G.5(b)-(c)** (MWG, p. 577). At `p_e = 3/4`, `p_f = 1`, the education sector's
deficit at `e = 4/9` is `C(4/9) - p_e·(4/9) = 1/3`; with the lump-sum tax `τ = 1/3` the consumer's
income is `w_L + w_T - τ = 2/3`, and on the budget set `{p_e e + f ≤ 2/3}` utility `√(ef)` is
maximized at `e = 4/9`, `f = 1/3`: the consumer chooses the optimal level of education. -/
theorem exercise_16_G_5bc :
    (1 / 2 + 1 / 2 : ℝ) * (2 / 3) - 3 / 4 * (4 / 9) = 1 / 3 ∧
      (1 / 2 + 1 / 2 - 1 / 3 : ℝ) = 2 / 3 ∧
      3 / 4 * (4 / 9) + 1 / 3 ≤ (2 / 3 : ℝ) ∧
      ∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 2 / 3 →
        Real.sqrt (e * f) ≤ Real.sqrt (4 / 9 * (1 / 3)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun e f he hf hb => ?_⟩
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]

/-- **Exercise 16.G.5(d)** (MWG, p. 577). With marginal cost pricing `p_e = C'(e)` and cost
`C(e) = (w_L + w_T)√e`, the deficit of the public education sector, to be covered by a tax on the
landowner, is `C(e) - C'(e)e = (w_L + w_T)√e/2` (for `e > 0`). -/
theorem exercise_16_G_5d {wL wT e : ℝ} (he : 0 < e) :
    HasDerivAt (fun e : ℝ => (wL + wT) * Real.sqrt e) ((wL + wT) / (2 * Real.sqrt e)) e ∧
      (wL + wT) * Real.sqrt e - (wL + wT) / (2 * Real.sqrt e) * e =
        (wL + wT) * Real.sqrt e / 2 := by
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  refine ⟨?_, ?_⟩
  · have := (Real.hasDerivAt_sqrt he.ne').const_mul (wL + wT)
    convert this using 1
    field_simp
  · have key : e = Real.sqrt e * Real.sqrt e := (Real.mul_self_sqrt he.le).symm
    have h2 : (wL + wT) / (2 * Real.sqrt e) * e = (wL + wT) * Real.sqrt e / 2 := by
      calc (wL + wT) / (2 * Real.sqrt e) * e
          = (wL + wT) / (2 * Real.sqrt e) * (Real.sqrt e * Real.sqrt e) := by rw [← key]
        _ = (wL + wT) * Real.sqrt e / 2 := by field_simp
    rw [h2]
    ring

/-- **Exercise 16.G.5(e)** (MWG, p. 577), the equilibrium level. With `w_L = w_T = 1/2`, marginal
cost price `p_e = 1/(2√e)`, the laborer's income `1/2`, the landowner's income `1/2 - √e/2` (after
the transfer of (d)), and each consumer spending half her income on education, market clearing
for education, `e = (1/2)(1 - √e/2)/p_e`, holds (for `e > 0`) exactly when `e = 4/9`. -/
theorem exercise_16_G_5e_level {e : ℝ} (he : 0 < e) :
    e = (1 / 2) * ((1 / 2) + (1 / 2 - Real.sqrt e / 2)) / (1 / (2 * Real.sqrt e)) ↔
      e = 4 / 9 := by
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hse : Real.sqrt e ^ 2 = e := Real.sq_sqrt he.le
  constructor
  · intro h
    field_simp at h
    -- `e = √e (1 - √e/2)`, i.e. `(3/2) e = √e`, so `√e = 2/3`
    have h2 : Real.sqrt e = 2 / 3 := by nlinarith
    rw [← hse, h2]; norm_num
  · intro h
    have h2 : Real.sqrt e = 2 / 3 := by
      rw [h, show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h2, h]
    norm_num

/-- The geometric mean is superadditive: `√(ab) + √(cd) ≤ √((a + c)(b + d))` for nonnegative
reals. -/
theorem sqrt_mul_add_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  rw [Real.le_sqrt (by positivity) (by positivity), add_sq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), mul_assoc, ← Real.sqrt_mul (by positivity)]
  have h : Real.sqrt (a * b * (c * d)) ≤ (a * d + b * c) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (a * d - b * c)]
  nlinarith

/-- **Exercise 16.G.5(e)** (MWG, p. 577). The marginal cost price equilibrium (`e = 4/9`, `f = 1/3`,
`p_e = 3/4`, wages `1/2`, landowner transfer `1/3`) gives the landowner `(1/9, 1/12)` and the
laborer `(1/3, 1/4)`, each maximizing `√(ef)` on her budget set; it is Pareto optimal: for every
allocation of a producible `(E, F)` (`E = (min{L, T})²`, `F = √((1-L)(1-T))`), the sum of the two
utilities is at most `√(4/27)`, the sum at the equilibrium. -/
theorem exercise_16_G_5e :
    (1 / 9 + 1 / 3 : ℝ) = 4 / 9 ∧ (1 / 12 + 1 / 4 : ℝ) = 1 / 3 ∧
    (∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 1 / 2 - 1 / 3 →
      Real.sqrt (e * f) ≤ Real.sqrt (1 / 9 * (1 / 12))) ∧
    (∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 1 / 2 →
      Real.sqrt (e * f) ≤ Real.sqrt (1 / 3 * (1 / 4))) ∧
    Real.sqrt (1 / 9 * (1 / 12)) + Real.sqrt (1 / 3 * (1 / 4)) = Real.sqrt (4 / 27 : ℝ) ∧
    ∀ (L T e₁ f₁ e₂ f₂ : ℝ), 0 ≤ L → L ≤ 1 → 0 ≤ T → T ≤ 1 → 0 ≤ e₁ → 0 ≤ f₁ → 0 ≤ e₂ →
      0 ≤ f₂ → e₁ + e₂ ≤ min L T ^ 2 → f₁ + f₂ ≤ Real.sqrt ((1 - L) * (1 - T)) →
      Real.sqrt (e₁ * f₁) + Real.sqrt (e₂ * f₂) ≤ Real.sqrt (4 / 27) := by
  refine ⟨by norm_num, by norm_num, fun e f he hf hb => ?_, fun e f he hf hb => ?_, ?_,
    fun L T e₁ f₁ e₂ f₂ hL0 hL1 hT0 hT1 he₁ hf₁ he₂ hf₂ hE hF => ?_⟩
  · apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]
  · apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]
  · have h1 : Real.sqrt (1 / 9 * (1 / 12) : ℝ) = Real.sqrt (4 / 27) / 4 := by
      rw [show (1 / 9 * (1 / 12) : ℝ) = 4 / 27 / 4 ^ 2 by norm_num, Real.sqrt_div' _
        (by norm_num : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num)]
    have h2 : Real.sqrt (1 / 3 * (1 / 4) : ℝ) = 3 * Real.sqrt (4 / 27) / 4 := by
      rw [show (1 / 3 * (1 / 4) : ℝ) = 3 ^ 2 * (4 / 27) / 4 ^ 2 by norm_num,
        Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num),
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h1, h2]
    ring
  · have hsum := sqrt_mul_add_le he₁ hf₁ he₂ hf₂
    have hmax := (exercise_16_G_5a hL0 hL1 hT0 hT1).1
    refine hsum.trans (Real.sqrt_le_sqrt ?_)
    have hF0 : 0 ≤ Real.sqrt ((1 - L) * (1 - T)) := Real.sqrt_nonneg _
    calc (e₁ + e₂) * (f₁ + f₂) ≤ min L T ^ 2 * Real.sqrt ((1 - L) * (1 - T)) :=
          mul_le_mul hE hF (by positivity) (sq_nonneg _)
      _ ≤ 4 / 27 := hmax

end MWG.WelfareTheorems

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The second welfare theorem for Lindahl equilibria (MWG Example 16.G.3, p. 570)

"Every Pareto optimal allocation can be implemented using a Lindahl equilibrium (with appropriate
wealth transfers and, perhaps, with the usual quasiequilibrium qualification)." We carry out the
book's reduction. With `n` consumers the artificial economy has `n + 1` commodities: the private
good (coordinate `0`) and one personalized public good per consumer (coordinate `i.succ`).

* Consumer `i`'s consumption set is `{v : v₀ ≥ 0, v_{i+1} ≥ 0, v_{k+1} = 0 for k ≠ i}` and her
  preference compares `(v₀, v_{i+1})` by `≿ᵢ` (`lindahlArtificialEconomy`).
* The firm's technology `{(-z, q, ..., q) : z ≥ 0, q ≤ f(z)}` is convex when `f` is concave.
* A Pareto optimum of the public goods economy is a Pareto optimum of the artificial economy
  (`lindahl_pareto_artificial`); Proposition 16.D.1 gives a price quasiequilibrium with transfers
  there, which translates into a Lindahl quasiequilibrium with transfers (`IsLindahlQuasiEqm`,
  the corrected Definition 16.G.1 with condition (ii) weakened as in Definition 16.D.1):
  `lindahl_second_welfare`.
* A concrete instance: one consumer with `u = x₁ + x₂`, `f(z) = z`, `ω̄₁ = 1`
  (`lindahl_second_welfare_instance`).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {n : ℕ}

/-- Consumer `i`'s bundle `(a, b)` (private good, public good) as a vector of the artificial
economy: `a` in coordinate `0`, `b` in coordinate `i.succ`, zero elsewhere. -/
def lindahlEmb (i : Fin n) (a b : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons a (Pi.single i b : Fin n → ℝ)

/-- Consumer `i`'s view `(v₀, v_{i+1})` of a vector of the artificial economy. -/
def lindahlProj (i : Fin n) (v : Fin (n + 1) → ℝ) : Fin 2 → ℝ := ![v 0, v i.succ]

/-- Consumer `i`'s consumption set in the artificial economy. -/
def lindahlX (i : Fin n) : Set (Fin (n + 1) → ℝ) :=
  {v | 0 ≤ v 0 ∧ 0 ≤ v i.succ ∧ ∀ k : Fin n, k ≠ i → v k.succ = 0}

/-- The firm's technology `{(-z, q, ..., q) : z ≥ 0, q ≤ f(z)}` in the artificial economy. -/
def lindahlY (f : ℝ → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {y | 0 ≤ -y 0 ∧ ∃ q, q ≤ f (-y 0) ∧ ∀ k : Fin n, y k.succ = q}

/-- **Example 16.G.3** (MWG, p. 569). The artificial economy with personalized commodities. -/
def lindahlArtificialEconomy (pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) : PrefEconomy (Fin n) Unit (n + 1) where
  X := lindahlX
  pref := fun i v v' => pref i (lindahlProj i v) (lindahlProj i v')
  Y := fun _ => lindahlY f
  ω := Fin.cons ω₁ 0

/-- **Example 16.G.3** (MWG, p. 570). A Lindahl quasiequilibrium with transfers: Definition
16.G.1 (corrected) with prices not all zero and condition (ii) replaced by "anything strictly
preferred to `(x*₁ᵢ, q*)` costs at least `wᵢ`" (as in Definition 16.D.1). -/
def IsLindahlQuasiEqm (pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) (x : Fin n → ℝ) (q z p₁ : ℝ) (p₂ w : Fin n → ℝ) : Prop :=
  (p₁ ≠ 0 ∨ ∃ i, p₂ i ≠ 0) ∧
    ∑ i, w i = p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, ∀ v : Fin 2 → ℝ, (∀ l, 0 ≤ v l) → Strict (pref i) v ![x i, q] →
      w i ≤ p₁ * v 0 + p₂ i * v 1) ∧
    ∑ i, x i + z = ω₁

theorem lindahlEmb_zero (i : Fin n) (a b : ℝ) : lindahlEmb i a b 0 = a := rfl

theorem lindahlEmb_succ (i k : Fin n) (a b : ℝ) :
    lindahlEmb i a b k.succ = (Pi.single i b : Fin n → ℝ) k := rfl

theorem lindahlProj_emb (i : Fin n) (a b : ℝ) : lindahlProj i (lindahlEmb i a b) = ![a, b] := by
  funext l
  fin_cases l <;> simp [lindahlProj, lindahlEmb_zero, lindahlEmb_succ]

/-- The value of a vector of the artificial economy. -/
theorem dot_succ (p v : Fin (n + 1) → ℝ) :
    p ⬝ᵥ v = p 0 * v 0 + ∑ k : Fin n, p k.succ * v k.succ := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem dot_lindahlEmb (p : Fin (n + 1) → ℝ) (i : Fin n) (a b : ℝ) :
    p ⬝ᵥ lindahlEmb i a b = p 0 * a + p i.succ * b := by
  rw [dot_succ, lindahlEmb_zero]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [lindahlEmb_succ, hk]) (by simp)]
  simp [lindahlEmb_succ]

/-- A vector of consumer `i`'s consumption set is the embedding of its projection. -/
theorem emb_proj {i : Fin n} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ lindahlX i) :
    v = lindahlEmb i (v 0) (v i.succ) := by
  funext l
  refine Fin.cases ?_ (fun k => ?_) l
  · rfl
  · rw [lindahlEmb_succ]
    by_cases hk : k = i
    · subst hk; simp
    · rw [hv.2.2 k hk]; simp [hk]

theorem emb_mem (i : Fin n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lindahlEmb i a b ∈ lindahlX i :=
  ⟨ha, by simpa [lindahlEmb_succ] using hb, fun k hk => by simp [lindahlEmb_succ, hk]⟩

theorem proj_mem {i : Fin n} {v : Fin (n + 1) → ℝ} (hv : v ∈ lindahlX i) :
    lindahlProj i v ∈ nonnegOrthant 2 := fun l => by
  fin_cases l
  · exact hv.1
  · exact hv.2.1

/-- Embedding preserves Euclidean distances between bundles of consumer `i`. -/
theorem euclidDist_emb (i : Fin n) (a b c d : ℝ) :
    euclidDist (lindahlEmb i a b) (lindahlEmb i c d) = euclidDist ![a, b] ![c, d] := by
  unfold euclidDist
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  simp only [lindahlEmb_zero, lindahlEmb_succ, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- The artificial allocation of a public goods allocation. -/
def lindahlAlloc (x : Fin n → ℝ) (q z : ℝ) : Allocation (Fin n) Unit (n + 1) :=
  ⟨fun i => lindahlEmb i (x i) q, fun _ => Fin.cons (-z) (fun _ => q)⟩

/-- **Example 16.G.3** (MWG, p. 569). A Pareto optimum of the public goods economy (with `n ≥ 1`
consumers) is a Pareto optimum of the artificial economy. -/
theorem lindahl_pareto_artificial [NeZero n] {pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    {ω₁ : ℝ} {f : ℝ → ℝ} {x : Fin n → ℝ} {q z : ℝ}
    (hpo : PublicParetoOptimal pref ω₁ f x q z) :
    (lindahlArtificialEconomy pref ω₁ f).IsParetoOptimal (lindahlAlloc x q z) := by
  obtain ⟨⟨hx, hq, hz, hf, hc⟩, hno⟩ := hpo
  refine ⟨⟨⟨fun i => emb_mem i (hx i) hq, fun _ => ⟨by simpa [lindahlAlloc] using hz, q,
    by simpa [lindahlAlloc] using hf, fun k => by simp [lindahlAlloc]⟩⟩, ?_⟩, ?_⟩
  · funext l
    refine Fin.cases ?_ (fun k => ?_) l
    · change (∑ i, lindahlEmb i (x i) q) 0 = (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) 0 +
        (∑ _j : Unit, (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ)) 0
      simp only [Finset.sum_apply, lindahlEmb_zero, Fin.cons_zero, Finset.univ_unique,
        Finset.sum_singleton]
      linarith
    · change (∑ i, lindahlEmb i (x i) q) k.succ = (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) k.succ +
        (∑ _j : Unit, (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ)) k.succ
      simp only [Finset.sum_apply, lindahlEmb_succ, Fin.cons_succ, Finset.univ_unique,
        Finset.sum_singleton, Pi.zero_apply, zero_add]
      rw [Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
      simp
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    obtain ⟨hz', q', hq'f, hq'⟩ := hy' ()
    -- consumer `i`'s public good is the common output `q'`
    have hpub : ∀ i, a'.x i i.succ = q' := by
      intro i
      have h1 := congrFun hc' i.succ
      simp only [Finset.sum_apply, Pi.add_apply, lindahlArtificialEconomy, Fin.cons_succ,
        Pi.zero_apply, zero_add, Finset.univ_unique, Finset.sum_singleton, hq'] at h1
      rw [← h1, Finset.sum_eq_single i (fun j _ hj => (hx' j).2.2 i (Ne.symm hj)) (by simp)]
    have hproj : ∀ i, lindahlProj i (a'.x i) = ![a'.x i 0, q'] := fun i => by
      simp [lindahlProj, hpub i]
    have hproj0 : ∀ i, lindahlProj i ((lindahlAlloc x q z).x i) = ![x i, q] := fun i =>
      lindahlProj_emb i (x i) q
    apply hno
    refine ⟨fun i => a'.x i 0, q', -a'.y () 0, ⟨fun i => (hx' i).1, ?_, hz', hq'f, ?_⟩,
      fun i => ?_, k, ?_⟩
    · have := (hx' (0 : Fin n)).2.1; rwa [hpub] at this
    · have h1 := congrFun hc' 0
      simp only [Finset.sum_apply, Pi.add_apply, lindahlArtificialEconomy, Fin.cons_zero,
        Finset.univ_unique, Finset.sum_singleton] at h1
      linarith
    · have h1 : pref i (lindahlProj i (a'.x i)) (lindahlProj i ((lindahlAlloc x q z).x i)) :=
        hle i
      rwa [hproj, hproj0] at h1
    · have h1 : Strict (pref k) (lindahlProj k (a'.x k))
          (lindahlProj k ((lindahlAlloc x q z).x k)) := hk
      rwa [hproj, hproj0] at h1

/-- **Example 16.G.3** (MWG, p. 570): the second welfare theorem for Lindahl equilibria. With
`n ≥ 1` consumers whose preferences on `ℝ²₊` are rational, convex and locally nonsatiated and a
concave production function `f` on `[0, ∞)`, every Pareto optimal allocation of the public goods
economy is a Lindahl quasiequilibrium with transfers for some personalized prices
`(p₁, p₂₁, ..., p₂ₙ) ≠ 0`, with wealth levels `wᵢ = p₁x*₁ᵢ + p₂ᵢq*`. -/
theorem lindahl_second_welfare [NeZero n] {pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant 2) (pref i))
    (hc : ∀ i, PrefConvex (nonnegOrthant 2) (pref i))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {x : Fin n → ℝ} {q z : ℝ}
    (hpo : PublicParetoOptimal pref ω₁ f x q z) :
    ∃ (p₁ : ℝ) (p₂ : Fin n → ℝ), IsLindahlQuasiEqm pref ω₁ f x q z p₁ p₂
      (fun i => p₁ * x i + p₂ i * q) := by
  set E := lindahlArtificialEconomy pref ω₁ f with hE
  -- hypotheses of Proposition 16.D.1 for the artificial economy
  have hY : ∀ j, Convex ℝ (E.Y j) := by
    intro _ y ⟨hy0, qy, hqy, hyq⟩ y' ⟨hy0', qy', hqy', hyq'⟩ a b ha hb hab
    refine ⟨by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith, a * qy + b * qy',
      ?_, fun k => by simp [hyq, hyq']⟩
    have hcon := hf.2 (Set.mem_Ici.mpr hy0) (Set.mem_Ici.mpr hy0') ha hb hab
    simp only [smul_eq_mul] at hcon
    have h0 : -(a • y + b • y') 0 = a * -y 0 + b * -y' 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h0]
    nlinarith [mul_le_mul_of_nonneg_left hqy ha, mul_le_mul_of_nonneg_left hqy' hb]
  have hvec : ∀ w : Fin 2 → ℝ, (![w 0, w 1] : Fin 2 → ℝ) = w := fun w => by
    funext l; fin_cases l <;> rfl
  have hrat : ∀ i, RationalOn (E.X i) (E.pref i) := fun i =>
    ⟨fun v hv v' hv' => (hr i).1 _ (proj_mem hv) _ (proj_mem hv'),
      fun v hv v' hv' v'' hv'' h1 h2 => (hr i).2 _ (proj_mem hv) _ (proj_mem hv') _
        (proj_mem hv'') h1 h2⟩
  have hprojlin : ∀ (i : Fin n) (v v' : Fin (n + 1) → ℝ) (a b : ℝ),
      lindahlProj i (a • v + b • v') = a • lindahlProj i v + b • lindahlProj i v' := by
    intro i v v' a b; funext l; fin_cases l <;> simp [lindahlProj]
  have hconvE : ∀ i, PrefConvex (E.X i) (E.pref i) := by
    intro i v0 hv0 v ⟨hv, hvr⟩ v' ⟨hv', hvr'⟩ a b ha hb hab
    refine ⟨⟨?_, ?_, fun k hk => ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha hv.1, mul_nonneg hb hv'.1]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha hv.2.1, mul_nonneg hb hv'.2.1]
    · simp [hv.2.2 k hk, hv'.2.2 k hk]
    · change pref i (lindahlProj i (a • v + b • v')) (lindahlProj i v0)
      rw [hprojlin]
      exact (hc i _ (proj_mem hv0) ⟨proj_mem hv, hvr⟩ ⟨proj_mem hv', hvr'⟩ ha hb hab).2
  have hlnsE : ∀ i, LocallyNonsatiated (E.X i) (E.pref i) := by
    intro i v hv ε hε
    obtain ⟨w, hw, hd, hs⟩ := hlns i (lindahlProj i v) (proj_mem hv) ε hε
    refine ⟨lindahlEmb i (w 0) (w 1), emb_mem i (hw 0) (hw 1), ?_, ?_⟩
    · rw [emb_proj hv, euclidDist_emb, hvec]
      exact hd
    · change Strict (pref i) (lindahlProj i (lindahlEmb i (w 0) (w 1))) (lindahlProj i v)
      rw [lindahlProj_emb, hvec]
      exact hs
  obtain ⟨p, hp, hq⟩ := proposition_16_D_1 hY hrat hconvE hlnsE (lindahl_pareto_artificial hpo)
  obtain ⟨⟨hx, hq0, hz, hf', hc'⟩, -⟩ := hpo
  have hdotω : p ⬝ᵥ E.ω = p 0 * ω₁ := by
    change p ⬝ᵥ (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) = _
    simp [dot_succ]
  have hdoty : ∀ q' z' : ℝ, p ⬝ᵥ (Fin.cons (-z') (fun _ => q') : Fin (n + 1) → ℝ) =
      (∑ i : Fin n, p i.succ) * q' - p 0 * z' := fun q' z' => by
    rw [dot_succ, Finset.sum_mul]; simp; ring
  have hwx : ∀ i, p ⬝ᵥ (lindahlAlloc x q z).x i = p 0 * x i + p i.succ * q := fun i =>
    dot_lindahlEmb p i (x i) q
  refine ⟨p 0, fun i => p i.succ, ⟨?_, ?_, ⟨hf', hz, fun q' z' hz' hq' => ?_⟩, fun i v hv hs => ?_,
    hc'⟩⟩
  · by_contra h
    push Not at h
    apply hp
    funext l
    refine Fin.cases ?_ (fun k => ?_) l
    · exact h.1
    · exact h.2 k
  · have := hq.2.1
    simp only [hwx, hdotω, Finset.univ_unique, Finset.sum_singleton] at this
    change ∑ i, (p 0 * x i + p i.succ * q) = _
    rw [this]
    change p 0 * ω₁ + p ⬝ᵥ (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ) = _
    rw [hdoty]; ring
  · have := (hq.2.2.1 ()).2 (Fin.cons (-z') (fun _ => q'))
      ⟨by simpa using hz', q', by simpa using hq', fun k => by simp⟩
    change p ⬝ᵥ _ ≤ p ⬝ᵥ (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ) at this
    rw [hdoty, hdoty] at this
    exact this
  · have h1 := (hq.2.2.2.1 i).2 (lindahlEmb i (v 0) (v 1)) (emb_mem i (hv 0) (hv 1)) (by
      change Strict (pref i) (lindahlProj i (lindahlEmb i (v 0) (v 1)))
        (lindahlProj i (lindahlEmb i (x i) q))
      rw [lindahlProj_emb, lindahlProj_emb, hvec]
      exact hs)
    have h2 : p ⬝ᵥ (lindahlAlloc x q z).x i ≤ p ⬝ᵥ lindahlEmb i (v 0) (v 1) := h1
    rw [hwx, dot_lindahlEmb] at h2
    exact h2

/-- **Example 16.G.3** (MWG, p. 570), a concrete instance of `lindahl_second_welfare`: one
consumer with `u(x₁, x₂) = x₁ + x₂` (rational, convex, locally nonsatiated), `f(z) = z`,
`ω̄₁ = 1`. The allocation `x₁ = q = z = 1/2` is Pareto optimal and hence a Lindahl
quasiequilibrium with transfers. -/
theorem lindahl_second_welfare_instance :
    PublicParetoOptimal (fun _ : Fin 1 => utilityPref lindahlExampleU) 1 id (fun _ => 1 / 2)
        (1 / 2) (1 / 2) ∧
      ∃ (p₁ : ℝ) (p₂ : Fin 1 → ℝ), IsLindahlQuasiEqm (fun _ => utilityPref lindahlExampleU) 1 id
        (fun _ => 1 / 2) (1 / 2) (1 / 2) p₁ p₂ (fun i => p₁ * (1 / 2) + p₂ i * (1 / 2)) := by
  have hpo : PublicParetoOptimal (fun _ : Fin 1 => utilityPref lindahlExampleU) 1 id
      (fun _ => 1 / 2) (1 / 2) (1 / 2) := by
    refine ⟨⟨fun _ => by norm_num, by norm_num, by norm_num, le_rfl, by simp; norm_num⟩, ?_⟩
    rintro ⟨x', q', z', ⟨hx', hq', hz', hf', hc'⟩, -, k, hk⟩
    apply hk.2
    change lindahlExampleU ![x' k, q'] ≤ lindahlExampleU ![1 / 2, 1 / 2]
    simp only [lindahlExampleU, Matrix.cons_val_zero, Matrix.cons_val_one, id] at hf' ⊢
    simp only [Finset.univ_unique, Finset.sum_singleton] at hc'
    have : k = default := Subsingleton.elim _ _
    subst this
    rw [Fin.default_eq_zero] at hc'
    norm_num
    linarith
  refine ⟨hpo, lindahl_second_welfare (fun _ => rationalOn_utilityPref _ _) (fun _ => ?_)
    (fun _ => lns_of_strictMono_coord 0 fun x _ c hc => by simp [lindahlExampleU]; linarith)
    (concaveOn_id (convex_Ici 0)) hpo⟩
  intro y _ v hv w hw a b ha hb hab
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hv.1 l), mul_nonneg hb (hw.1 l)]
  · have h1 : lindahlExampleU y ≤ lindahlExampleU v := hv.2
    have h2 : lindahlExampleU y ≤ lindahlExampleU w := hw.2
    change lindahlExampleU y ≤ lindahlExampleU (a • v + b • w)
    simp only [lindahlExampleU, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have : y 0 + y 1 = a * (y 0 + y 1) + b * (y 0 + y 1) := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end MWG.WelfareTheorems

set_option linter.style.longLine false
#print axioms MWG.WelfareTheorems.PrefEconomy
#print axioms MWG.WelfareTheorems.PrefEconomy.mk
#print axioms MWG.WelfareTheorems.PrefEconomy.X
#print axioms MWG.WelfareTheorems.PrefEconomy.pref
#print axioms MWG.WelfareTheorems.PrefEconomy.Y
#print axioms MWG.WelfareTheorems.PrefEconomy.ω
#print axioms MWG.WelfareTheorems.PrivPrefEconomy
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.mk
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.X
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.pref
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.Y
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.ωi
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.θ
#print axioms MWG.WelfareTheorems.nonposOrthant
#print axioms MWG.WelfareTheorems.PrefEconomy.IsAllocation
#print axioms MWG.WelfareTheorems.PrefEconomy.IsFeasible
#print axioms MWG.WelfareTheorems.PrefEconomy.feasibleSet
#print axioms MWG.WelfareTheorems.PrefEconomy.ParetoDominates
#print axioms MWG.WelfareTheorems.PrefEconomy.IsParetoOptimal
#print axioms MWG.WelfareTheorems.IsMaximalFor
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceEqmWithTransfers
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceQuasiEqmWithTransfers
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPureExchange
#print axioms MWG.WelfareTheorems.PrefEconomy.ofUtility
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.toEconomy
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.SharesValid
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.wealth
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.IsWalrasEqm
#print axioms MWG.WelfareTheorems.definition_16_B_1
#print axioms MWG.WelfareTheorems.definition_16_B_2
#print axioms MWG.WelfareTheorems.definition_16_B_3
#print axioms MWG.WelfareTheorems.definition_16_B_4
#print axioms MWG.WelfareTheorems.definition_16_C_1
#print axioms MWG.WelfareTheorems.definition_16_D_1
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceEqmWithTransfers.isFeasible
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceQuasiEqmWithTransfers.isFeasible
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.sum_wealth
#print axioms MWG.WelfareTheorems.PrivPrefEconomy.IsWalrasEqm.isPriceEqmWithTransfers
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm
#print axioms MWG.WelfareTheorems.priceEqmCounterEconomy
#print axioms MWG.WelfareTheorems.priceEqmCounterEconomy_counterexample
#print axioms MWG.WelfareTheorems.dotProduct_finset_sum
#print axioms MWG.WelfareTheorems.abs_dotProduct_sub_le
#print axioms MWG.WelfareTheorems.lns_exists_better_cheaper
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm_of_lns
#print axioms MWG.WelfareTheorems.PrefEconomy.IsPriceQuasiEqmWithTransfers.wealth_eq
#print axioms MWG.WelfareTheorems.footnote_3
#print axioms MWG.WelfareTheorems.footnote_4
#print axioms MWG.WelfareTheorems.paretoOptimal_all_to_one
#print axioms MWG.WelfareTheorems.exchangeToPrefEconomy
#print axioms MWG.WelfareTheorems.exchangeToPrefEconomy_isPureExchange
#print axioms MWG.WelfareTheorems.exchange_isFeasible_iff
#print axioms MWG.WelfareTheorems.exchange_isDemandEqm_isPriceEqm
#print axioms MWG.WelfareTheorems.isWalrasEqm_iff_competitiveEqm
#print axioms MWG.WelfareTheorems.equation_16_C_1
#print axioms MWG.WelfareTheorems.exercise_16_C_2
#print axioms MWG.WelfareTheorems.proposition_16_C_1
#print axioms MWG.WelfareTheorems.proposition_16_C_1_walras
#print axioms MWG.WelfareTheorems.fig16C1u1
#print axioms MWG.WelfareTheorems.fig16C1u2
#print axioms MWG.WelfareTheorems.fig16C1Economy
#print axioms MWG.WelfareTheorems.fig16C1Eqm
#print axioms MWG.WelfareTheorems.dot_two
#print axioms MWG.WelfareTheorems.zero_mem_supply_nonpos
#print axioms MWG.WelfareTheorems.figure_16_C_1
#print axioms MWG.WelfareTheorems.exercise_16_C_1
#print axioms MWG.WelfareTheorems.unbounded_of_lns
#print axioms MWG.WelfareTheorems.StrictlyConvexC3
#print axioms MWG.WelfareTheorems.strictlyConvexC3_of_prefStrictlyConvex
#print axioms MWG.WelfareTheorems.prefStrictlyConvex_of_strictlyConvexC3
#print axioms MWG.WelfareTheorems.euclidDist_segment
#print axioms MWG.WelfareTheorems.exercise_16_C_3a_unique
#print axioms MWG.WelfareTheorems.exercise_16_C_3a_lns
#print axioms MWG.WelfareTheorems.exercise_16_C_3b
#print axioms MWG.WelfareTheorems.PrefEconomy.IsParetoOptimalWrt
#print axioms MWG.WelfareTheorems.exercise_16_C_4
#print axioms MWG.WelfareTheorems.altruismPleasure
#print axioms MWG.WelfareTheorems.altruismW
#print axioms MWG.WelfareTheorems.exercise_16_C_4_converse_fails
#print axioms MWG.WelfareTheorems.strict_of_strict_of_pref
#print axioms MWG.WelfareTheorems.strict_of_pref_of_strict
#print axioms MWG.WelfareTheorems.preferredSet
#print axioms MWG.WelfareTheorems.PrefEconomy.aggPreferredSet
#print axioms MWG.WelfareTheorems.PrefEconomy.availableSet
#print axioms MWG.WelfareTheorems.proposition_16_D_1_step1
#print axioms MWG.WelfareTheorems.proposition_16_D_1_step2_V
#print axioms MWG.WelfareTheorems.proposition_16_D_1_step2_Y
#print axioms MWG.WelfareTheorems.proposition_16_D_1_step3
#print axioms MWG.WelfareTheorems.proposition_16_D_1_step5
#print axioms MWG.WelfareTheorems.proposition_16_D_1
#print axioms MWG.WelfareTheorems.exercise_16_D_1
#print axioms MWG.WelfareTheorems.ex16D2u
#print axioms MWG.WelfareTheorems.ex16D2Economy
#print axioms MWG.WelfareTheorems.exercise_16_D_2
#print axioms MWG.WelfareTheorems.proposition_16_D_2
#print axioms MWG.WelfareTheorems.isMaximalFor_of_strict_gt
#print axioms MWG.WelfareTheorems.footnote_6
#print axioms MWG.WelfareTheorems.footnote_7
#print axioms MWG.WelfareTheorems.footnote_8
#print axioms MWG.WelfareTheorems.proposition_16_D_3
#print axioms MWG.WelfareTheorems.satiatedEconomy
#print axioms MWG.WelfareTheorems.proposition_16_D_3_needs_lns
#print axioms MWG.WelfareTheorems.footnote_9
#print axioms MWG.WelfareTheorems.dotProduct_pos_of_nonneg_ne_zero
#print axioms MWG.WelfareTheorems.pureExchange_quasiEqm_isPriceEqm_of_interior
#print axioms MWG.WelfareTheorems.exercise_16_D_3
#print axioms MWG.WelfareTheorems.euclidDist_add_single
#print axioms MWG.WelfareTheorems.lns_of_strictMono_coord
#print axioms MWG.WelfareTheorems.fig16D2u1
#print axioms MWG.WelfareTheorems.fig16D2u2
#print axioms MWG.WelfareTheorems.fig16D2Economy
#print axioms MWG.WelfareTheorems.fig16D2Alloc
#print axioms MWG.WelfareTheorems.fig16D2_lns
#print axioms MWG.WelfareTheorems.figure_16_D_2_quasi
#print axioms MWG.WelfareTheorems.figure_16_D_2_unique_price
#print axioms MWG.WelfareTheorems.figure_16_D_2_not_eqm
#print axioms MWG.WelfareTheorems.pureExchange_quasiEqm_isPriceEqm_of_strongMono
#print axioms MWG.WelfareTheorems.replicaEconomy
#print axioms MWG.WelfareTheorems.symmetricAlloc
#print axioms MWG.WelfareTheorems.exists_strict_of_tendsto
#print axioms MWG.WelfareTheorems.exists_strict_sub_single
#print axioms MWG.WelfareTheorems.exists_nat_combination_neg
#print axioms MWG.WelfareTheorems.exercise_16_D_4
#print axioms MWG.WelfareTheorems.rationalOn_utilityPref
#print axioms MWG.WelfareTheorems.prefContinuous_utilityPref
#print axioms MWG.WelfareTheorems.sqNormU
#print axioms MWG.WelfareTheorems.sqNormU_stronglyMonotone
#print axioms MWG.WelfareTheorems.figure_16_D_4
#print axioms MWG.WelfareTheorems.figure_16_D_5
#print axioms MWG.WelfareTheorems.utilityPossibilitySet
#print axioms MWG.WelfareTheorems.achievedUtilitySet
#print axioms MWG.WelfareTheorems.paretoFrontier
#print axioms MWG.WelfareTheorems.achievedUtilitySet_subset
#print axioms MWG.WelfareTheorems.utilityPossibilitySet_down
#print axioms MWG.WelfareTheorems.proposition_16_E_1
#print axioms MWG.WelfareTheorems.exercise_16_E_2
#print axioms MWG.WelfareTheorems.proposition_16_E_2_i
#print axioms MWG.WelfareTheorems.strongDual_apply_eq_sum
#print axioms MWG.WelfareTheorems.proposition_16_E_2_ii
#print axioms MWG.WelfareTheorems.pareto_isWelfareOptimum
#print axioms MWG.WelfareTheorems.welfareOptimum_isPareto
#print axioms MWG.WelfareTheorems.fig16C1Utilities
#print axioms MWG.WelfareTheorems.footnote_12
#print axioms MWG.WelfareTheorems.squareUtility
#print axioms MWG.WelfareTheorems.fig16E1Economy
#print axioms MWG.WelfareTheorems.figure_16_E_1
#print axioms MWG.WelfareTheorems.repUtility
#print axioms MWG.WelfareTheorems.representative_consumer
#print axioms MWG.WelfareTheorems.utility_mono_of_strongMono
#print axioms MWG.WelfareTheorems.exercise_16_E_1b_interior
#print axioms MWG.WelfareTheorems.exercise_16_E_1b
#print axioms MWG.WelfareTheorems.exercise_16_E_1b_hint
#print axioms MWG.WelfareTheorems.exercise_16_E_1c
#print axioms MWG.WelfareTheorems.aggregateProduction
#print axioms MWG.WelfareTheorems.PrefEconomy.feasiblePairs
#print axioms MWG.WelfareTheorems.isClosed_nonnegOrthant
#print axioms MWG.WelfareTheorems.isClosed_nonposOrthant
#print axioms MWG.WelfareTheorems.exercise_16_AA_1
#print axioms MWG.WelfareTheorems.proposition_16_AA_1_nonempty
#print axioms MWG.WelfareTheorems.mem_of_tendsto_inv_smul
#print axioms MWG.WelfareTheorems.proposition_16_AA_1
#print axioms MWG.WelfareTheorems.aaY1
#print axioms MWG.WelfareTheorems.aaCounterEconomy
#print axioms MWG.WelfareTheorems.aaCounter_agg
#print axioms MWG.WelfareTheorems.proposition_16_AA_1_counterexample
#print axioms MWG.WelfareTheorems.exercise_16_AA_2
#print axioms MWG.WelfareTheorems.exercise_16_AA_2_needs_closed
#print axioms MWG.WelfareTheorems.exercise_16_AA_2_needs_convex
#print axioms MWG.WelfareTheorems.exercise_16_AA_2_needs_zero
#print axioms MWG.WelfareTheorems.exercise_16_AA_2_needs_no_free_lunch
#print axioms MWG.WelfareTheorems.exercise_16_AA_3
#print axioms MWG.WelfareTheorems.proposition_16_AA_2
#print axioms MWG.WelfareTheorems.no_improving_direction
#print axioms MWG.WelfareTheorems.fritz_john
#print axioms MWG.WelfareTheorems.clm_apply_eq_sum_partials
#print axioms MWG.WelfareTheorems.clm_pos_of_partials_pos
#print axioms MWG.WelfareTheorems.strictMono_of_grad_pos
#print axioms MWG.WelfareTheorems.mono_of_grad_pos
#print axioms MWG.WelfareTheorems.Problem16F1
#print axioms MWG.WelfareTheorems.IsSolution16F1
#print axioms MWG.WelfareTheorems.economy16F
#print axioms MWG.WelfareTheorems.single_nonneg_add
#print axioms MWG.WelfareTheorems.solution16F1_resources_bind
#print axioms MWG.WelfareTheorems.exercise_16_F_1_i
#print axioms MWG.WelfareTheorems.exercise_16_F_1_ii
#print axioms MWG.WelfareTheorems.projX
#print axioms MWG.WelfareTheorems.projY
#print axioms MWG.WelfareTheorems.resLin
#print axioms MWG.WelfareTheorems.exercise_16_F_2
#print axioms MWG.WelfareTheorems.convexOn_tangent_le
#print axioms MWG.WelfareTheorems.concaveOn_le_tangent
#print axioms MWG.WelfareTheorems.consumer_max_of_foc
#print axioms MWG.WelfareTheorems.firm_max_of_foc
#print axioms MWG.WelfareTheorems.section_16_F_constraints_bind
#print axioms MWG.WelfareTheorems.exercise_16_F_3
#print axioms MWG.WelfareTheorems.foc_16F2_iff_16F10
#print axioms MWG.WelfareTheorems.foc_16F13_iff_16F2
#print axioms MWG.WelfareTheorems.section_16_F_pareto_isPriceEqm
#print axioms MWG.WelfareTheorems.section_16_F_pareto_iff_priceEqm
#print axioms MWG.WelfareTheorems.proposition_16_F_1
#print axioms MWG.WelfareTheorems.footnote_18_counterexample
#print axioms MWG.WelfareTheorems.exists_sep_direction
#print axioms MWG.WelfareTheorems.eventually_gt_along
#print axioms MWG.WelfareTheorems.eventually_pos_along
#print axioms MWG.WelfareTheorems.single_eq_smul_single
#print axioms MWG.WelfareTheorems.clm_two_dir
#print axioms MWG.WelfareTheorems.Problem16F7
#print axioms MWG.WelfareTheorems.exercise_16_F_4_i
#print axioms MWG.WelfareTheorems.Problem16F8
#print axioms MWG.WelfareTheorems.exercise_16_F_4_ii
#print axioms MWG.WelfareTheorems.exercise_16_F_4_iii
#print axioms MWG.WelfareTheorems.PrefEconomy.IsMCPriceEqm
#print axioms MWG.WelfareTheorems.proposition_16_G_1
#print axioms MWG.WelfareTheorems.exercise_16_G_1
#print axioms MWG.WelfareTheorems.exercise_16_G_2
#print axioms MWG.WelfareTheorems.sqTechF
#print axioms MWG.WelfareTheorems.sqTechY
#print axioms MWG.WelfareTheorems.sqTechF_hasFDerivAt
#print axioms MWG.WelfareTheorems.fig16G1Economy
#print axioms MWG.WelfareTheorems.fig16G1Alloc
#print axioms MWG.WelfareTheorems.figure_16_G_1
#print axioms MWG.WelfareTheorems.fig16G2Economy
#print axioms MWG.WelfareTheorems.fig16G2Alloc
#print axioms MWG.WelfareTheorems.figure_16_G_2
#print axioms MWG.WelfareTheorems.ex16G3F
#print axioms MWG.WelfareTheorems.ex16G3Y
#print axioms MWG.WelfareTheorems.ex16G3Economy
#print axioms MWG.WelfareTheorems.ex16G3F_hasFDerivAt
#print axioms MWG.WelfareTheorems.exercise_16_G_3
#print axioms MWG.WelfareTheorems.exercise_16_G_4
#print axioms MWG.WelfareTheorems.noOptimumF
#print axioms MWG.WelfareTheorems.exercise_16_G_4_needs_optimum
#print axioms MWG.WelfareTheorems.footnote_20
#print axioms MWG.WelfareTheorems.occupationalX
#print axioms MWG.WelfareTheorems.example_16_G_2_X
#print axioms MWG.WelfareTheorems.example_16_G_2_lns
#print axioms MWG.WelfareTheorems.example_16_G_2_Y
#print axioms MWG.WelfareTheorems.PublicFeasible
#print axioms MWG.WelfareTheorems.PublicParetoOptimal
#print axioms MWG.WelfareTheorems.IsLindahlEqm
#print axioms MWG.WelfareTheorems.IsLindahlEqmPrinted
#print axioms MWG.WelfareTheorems.definition_16_G_1_wealth_gap
#print axioms MWG.WelfareTheorems.definition_16_G_1_printed_forces
#print axioms MWG.WelfareTheorems.lindahlExampleU
#print axioms MWG.WelfareTheorems.definition_16_G_1_printed_counterexample
#print axioms MWG.WelfareTheorems.lindahl_isParetoOptimal
#print axioms MWG.WelfareTheorems.footnote_23
#print axioms MWG.WelfareTheorems.exercise_16_G_5a
#print axioms MWG.WelfareTheorems.exercise_16_G_5b_wages
#print axioms MWG.WelfareTheorems.exercise_16_G_5b_cost
#print axioms MWG.WelfareTheorems.exercise_16_G_5b_mc
#print axioms MWG.WelfareTheorems.exercise_16_G_5bc
#print axioms MWG.WelfareTheorems.exercise_16_G_5d
#print axioms MWG.WelfareTheorems.exercise_16_G_5e_level
#print axioms MWG.WelfareTheorems.sqrt_mul_add_le
#print axioms MWG.WelfareTheorems.exercise_16_G_5e
#print axioms MWG.WelfareTheorems.lindahlEmb
#print axioms MWG.WelfareTheorems.lindahlProj
#print axioms MWG.WelfareTheorems.lindahlX
#print axioms MWG.WelfareTheorems.lindahlY
#print axioms MWG.WelfareTheorems.lindahlArtificialEconomy
#print axioms MWG.WelfareTheorems.IsLindahlQuasiEqm
#print axioms MWG.WelfareTheorems.lindahlEmb_zero
#print axioms MWG.WelfareTheorems.lindahlEmb_succ
#print axioms MWG.WelfareTheorems.lindahlProj_emb
#print axioms MWG.WelfareTheorems.dot_succ
#print axioms MWG.WelfareTheorems.dot_lindahlEmb
#print axioms MWG.WelfareTheorems.emb_proj
#print axioms MWG.WelfareTheorems.emb_mem
#print axioms MWG.WelfareTheorems.proj_mem
#print axioms MWG.WelfareTheorems.euclidDist_emb
#print axioms MWG.WelfareTheorems.lindahlAlloc
#print axioms MWG.WelfareTheorems.lindahl_pareto_artificial
#print axioms MWG.WelfareTheorems.lindahl_second_welfare
#print axioms MWG.WelfareTheorems.lindahl_second_welfare_instance
