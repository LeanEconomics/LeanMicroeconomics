/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Exchange

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
