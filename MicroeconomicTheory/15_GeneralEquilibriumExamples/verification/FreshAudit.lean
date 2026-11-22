import MWGCompetitiveMarkets.ParetoEquilibrium
import MWGClassicalDemand.UMPBasic
import MWGClassicalDemand.PrefProperties
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import MWGClassicalDemand.ExpCobbDouglas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Function
import MWGCompetitiveMarkets.FOCTools
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pure exchange economies and the Edgeworth box (MWG Section 15.B, pp. 515-519)

A pure exchange economy has consumers `i : ι`, `L` goods, consumption sets `Xᵢ`, utility functions
`uᵢ` and endowments `ωᵢ`. Section 15.B works with `I = L = 2` and `Xᵢ = ℝ²₊` (the *Edgeworth box
economy*, `EdgeworthEconomy`); we keep `ι`, `L` and `Xᵢ` general so that Chapters 16-17 can build on
the same structure, and state the book's results for the Edgeworth box where the book does.
Preferences are represented by utility functions throughout (as in Chapter 10).

* (15.B.1): feasible allocations (`ExchangeEconomy.IsFeasible`); nonwasteful allocations, the points
  of the Edgeworth box (`ExchangeEconomy.InBox`).
* The budget set `Bᵢ(p) = {xᵢ ∈ Xᵢ : p·xᵢ ≤ p·ωᵢ}` (p. 517), demand `xᵢ(p, p·ωᵢ)` and the offer
  curve `OCᵢ` (p. 517).
* **Definition 15.B.1** (literal: `IsWalrasEqm`), its demand form (`IsDemandEqm`) and their
  equivalence under local nonsatiation (`isWalrasEqm_iff_isDemandEqm`); the bridge to Chapter 10's
  Definition 10.B.3 (`isDemandEqm_iff_competitiveEqm`).
* **Definition 15.B.2** (Pareto optimality in the box), the Pareto set and the contract curve
  (p. 523); the bridge to Chapter 10's Definition 10.B.2 for monotone utilities.
* **Definition 15.B.3** (equilibrium with transfers).
* The text's claims on pp. 517-519: only allocations on the budget line are affordable to both
  consumers; every point of an offer curve is weakly preferred to the endowment; equilibria are
  invariant to scaling prices; at an equilibrium the offer curves intersect, and (two goods) every
  intersection of the offer curves other than the endowment point is an equilibrium.
* **Exercise 15.B.1** (Walras' law, and clearing of one market implies clearing of the other).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.CompetitiveMarkets Kreps.PreferenceProperties

/-- **Section 15.B** (MWG, p. 515). A pure exchange economy: consumption sets `Xᵢ`, utility
functions `uᵢ` and endowments `ωᵢ`. -/
structure ExchangeEconomy (ι : Type*) (L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (Fin L → ℝ)
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Endowments. -/
  ω : ι → Fin L → ℝ

/-- **Section 15.B** (MWG, p. 516). The Edgeworth box economy: two consumers and two goods. -/
abbrev EdgeworthEconomy := ExchangeEconomy (Fin 2) 2

/-- **Section 15.B** (MWG, p. 516). The exchange economy with consumption sets `ℝ^L₊`. -/
def ExchangeEconomy.ofOrthant {ι : Type*} {L : ℕ} (u : ι → (Fin L → ℝ) → ℝ)
    (ω : ι → Fin L → ℝ) : ExchangeEconomy ι L where
  X := fun _ => nonnegOrthant L
  u := u
  ω := ω

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- **Section 15.B** (MWG, p. 516). The total endowment `ω̄ = ∑ᵢ ωᵢ`. -/
def ExchangeEconomy.totalEndowment (E : ExchangeEconomy ι L) : Fin L → ℝ := ∑ i, E.ω i

/-- An allocation assigns every consumer a bundle in his consumption set. -/
def ExchangeEconomy.IsAllocation (E : ExchangeEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∀ i, x i ∈ E.X i

/-- **(15.B.1)** (MWG, p. 516). A feasible allocation: `∑ᵢ x_{ℓi} ≤ ω̄_ℓ` for every good. -/
def ExchangeEconomy.IsFeasible (E : ExchangeEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  E.IsAllocation x ∧ ∀ l, ∑ i, x i l ≤ E.totalEndowment l

/-- **Section 15.B** (MWG, p. 516). A nonwasteful allocation (equality in (15.B.1)): for `I = L = 2`
the points of the Edgeworth box. -/
def ExchangeEconomy.InBox (E : ExchangeEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  E.IsAllocation x ∧ ∑ i, x i = E.totalEndowment

/-- **Section 15.B** (MWG, p. 517). Consumer `i`'s budget set `Bᵢ(p) = {xᵢ ∈ Xᵢ : p·xᵢ ≤ p·ωᵢ}`. -/
def ExchangeEconomy.budget (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  budgetSetOn (E.X i) p (p ⬝ᵥ E.ω i)

/-- **Section 15.B** (MWG, p. 517). Consumer `i`'s demand `xᵢ(p, p·ωᵢ)`, Chapter 3's Walrasian
demand with wealth `p·ωᵢ`. -/
def ExchangeEconomy.demand (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  walrasianDemandOn (E.X i) (E.u i) p (p ⬝ᵥ E.ω i)

/-- **Section 15.B** (MWG, p. 517). The offer curve `OCᵢ`: the bundles demanded at some strictly
positive price vector. -/
def ExchangeEconomy.offerCurve (E : ExchangeEconomy ι L) (i : ι) : Set (Fin L → ℝ) :=
  {x | ∃ p, StrictlyPositive p ∧ x ∈ E.demand i p}

/-- **Definition 15.B.1** (MWG, p. 519), as printed: `p*` and an allocation `x*` in the box with
`x*ᵢ ≿ᵢ x'ᵢ` for all `x'ᵢ ∈ Bᵢ(p*)`. (Affordability of `x*ᵢ` is not required; under local
nonsatiation it follows, `isWalrasEqm_iff_isDemandEqm`.) -/
def ExchangeEconomy.IsWalrasEqm (E : ExchangeEconomy ι L) (p : Fin L → ℝ)
    (x : ι → Fin L → ℝ) : Prop :=
  E.InBox x ∧ ∀ i, ∀ y ∈ E.budget i p, E.u i y ≤ E.u i (x i)

/-- **Definition 15.B.1** (MWG, p. 519) in demand form: every `x*ᵢ` is demanded at `p*`. -/
def ExchangeEconomy.IsDemandEqm (E : ExchangeEconomy ι L) (p : Fin L → ℝ)
    (x : ι → Fin L → ℝ) : Prop :=
  E.InBox x ∧ ∀ i, x i ∈ E.demand i p

/-- **Definition 15.B.2** (MWG, p. 523). `x` in the box is Pareto optimal if no `x'` in the box
makes every consumer weakly and some consumer strictly better off. -/
def ExchangeEconomy.IsParetoOptimal (E : ExchangeEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  E.InBox x ∧ ¬ ∃ x', E.InBox x' ∧ (∀ i, E.u i (x i) ≤ E.u i (x' i)) ∧
    ∃ i, E.u i (x i) < E.u i (x' i)

/-- **Section 15.B** (MWG, p. 523). The Pareto set. -/
def ExchangeEconomy.paretoSet (E : ExchangeEconomy ι L) : Set (ι → Fin L → ℝ) :=
  {x | E.IsParetoOptimal x}

/-- **Section 15.B** (MWG, pp. 523-524). The contract curve: the Pareto optimal allocations at
which every consumer is at least as well off as at his endowment. -/
def ExchangeEconomy.contractCurve (E : ExchangeEconomy ι L) : Set (ι → Fin L → ℝ) :=
  {x | E.IsParetoOptimal x ∧ ∀ i, E.u i (E.ω i) ≤ E.u i (x i)}

/-- **Definition 15.B.3** (MWG, p. 524), for given prices and transfers: the transfers sum to zero
and `x*ᵢ ≿ᵢ x'ᵢ` for all `x'ᵢ ∈ Xᵢ` with `p*·x'ᵢ ≤ p*·ωᵢ + Tᵢ`. -/
def ExchangeEconomy.IsEqmWithTransfers (E : ExchangeEconomy ι L) (p : Fin L → ℝ) (T : ι → ℝ)
    (x : ι → Fin L → ℝ) : Prop :=
  E.InBox x ∧ ∑ i, T i = 0 ∧
    ∀ i, ∀ y ∈ E.X i, p ⬝ᵥ y ≤ p ⬝ᵥ E.ω i + T i → E.u i y ≤ E.u i (x i)

/-- **Definition 15.B.3** (MWG, p. 524). `x*` is supportable as an equilibrium with transfers. -/
def ExchangeEconomy.IsSupportable (E : ExchangeEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∃ p T, E.IsEqmWithTransfers p T x

/-- Box allocations are feasible. -/
theorem ExchangeEconomy.InBox.isFeasible {E : ExchangeEconomy ι L} {x : ι → Fin L → ℝ}
    (h : E.InBox x) : E.IsFeasible x := by
  refine ⟨h.1, fun l => ?_⟩
  rw [← h.2, Finset.sum_apply]

/-- The endowment allocation is in the box (when endowments are in the consumption sets). -/
theorem ExchangeEconomy.inBox_endowment (E : ExchangeEconomy ι L) (h : ∀ i, E.ω i ∈ E.X i) :
    E.InBox E.ω :=
  ⟨h, rfl⟩

/-- A demand equilibrium satisfies Definition 15.B.1. -/
theorem ExchangeEconomy.IsDemandEqm.isWalrasEqm {E : ExchangeEconomy ι L} {p : Fin L → ℝ}
    {x : ι → Fin L → ℝ} (h : E.IsDemandEqm p x) : E.IsWalrasEqm p x :=
  ⟨h.1, fun i y hy => (h.2 i).2 y hy⟩

/-- **Section 15.B** (MWG, p. 517). Only allocations on the budget line are affordable to all
consumers simultaneously: if `x` is in the box and `p·xᵢ ≤ p·ωᵢ` for every `i`, then
`p·xᵢ = p·ωᵢ` for every `i`. -/
theorem budget_line_of_inBox {E : ExchangeEconomy ι L} {x : ι → Fin L → ℝ} (hx : E.InBox x)
    {p : Fin L → ℝ} (hb : ∀ i, p ⬝ᵥ x i ≤ p ⬝ᵥ E.ω i) (i : ι) : p ⬝ᵥ x i = p ⬝ᵥ E.ω i := by
  have hsum : ∑ k, p ⬝ᵥ x k = ∑ k, p ⬝ᵥ E.ω k := by
    rw [← dotProduct_sum, ← dotProduct_sum, hx.2, ExchangeEconomy.totalEndowment]
  exact (Finset.sum_eq_sum_iff_of_le fun k _ => hb k).1 hsum i (Finset.mem_univ i)

omit [Fintype ι] in
/-- **Section 15.B** (MWG, p. 517). Every point of consumer `i`'s offer curve is weakly preferred
to his endowment (the endowment is always affordable). -/
theorem offerCurve_ge_endowment {E : ExchangeEconomy ι L} {i : ι} (hω : E.ω i ∈ E.X i)
    {x : Fin L → ℝ} (hx : x ∈ E.offerCurve i) : E.u i (E.ω i) ≤ E.u i x := by
  obtain ⟨p, -, hd⟩ := hx
  exact hd.2 _ ⟨hω, le_rfl⟩

omit [Fintype ι] in
/-- Budget sets are invariant to scaling prices by `α > 0`. -/
theorem ExchangeEconomy.budget_smul (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) {α : ℝ}
    (hα : 0 < α) : E.budget i (α • p) = E.budget i p := by
  ext y
  simp only [ExchangeEconomy.budget, budgetSetOn, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, le_of_mul_le_mul_left h hα⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, mul_le_mul_of_nonneg_left h hα.le⟩

omit [Fintype ι] in
/-- Demand is homogeneous of degree zero in prices (p. 519). -/
theorem ExchangeEconomy.demand_smul (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) {α : ℝ}
    (hα : 0 < α) : E.demand i (α • p) = E.demand i p := by
  have h := E.budget_smul i p hα
  simp only [ExchangeEconomy.budget] at h
  simp only [ExchangeEconomy.demand, walrasianDemandOn, h]

/-- **Section 15.B** (MWG, p. 519). If `p*` is a Walrasian equilibrium price vector, so is `αp*` for
every `α > 0`: only relative prices are determined. -/
theorem isWalrasEqm_smul {E : ExchangeEconomy ι L} {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsWalrasEqm p x) {α : ℝ} (hα : 0 < α) : E.IsWalrasEqm (α • p) x := by
  refine ⟨h.1, fun i y hy => h.2 i y ?_⟩
  rwa [E.budget_smul i p hα] at hy

/-- **Section 15.B** (MWG, p. 519), demand form of `isWalrasEqm_smul`. -/
theorem isDemandEqm_smul {E : ExchangeEconomy ι L} {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsDemandEqm p x) {α : ℝ} (hα : 0 < α) : E.IsDemandEqm (α • p) x :=
  ⟨h.1, fun i => by rw [E.demand_smul i p hα]; exact h.2 i⟩

/-- Local nonsatiation of a utility function on `ℝ^L₊` (Definition 3.B.3 for the preference it
represents). -/
abbrev UtilityLNS (u : (Fin L → ℝ) → ℝ) : Prop :=
  LocallyNonsatiated (nonnegOrthant L) (utilityPref u)

/-- Strong monotonicity of a utility function on `ℝ^L₊` (Definition 3.B.2). -/
abbrev UtilityStronglyMonotone (u : (Fin L → ℝ) → ℝ) : Prop :=
  PrefStronglyMonotone (nonnegOrthant L) (utilityPref u)

/-- Strong monotonicity in utility form: `x ≤ y`, `x ≠ y` imply `u(x) < u(y)`. -/
theorem UtilityStronglyMonotone.lt {u : (Fin L → ℝ) → ℝ} (h : UtilityStronglyMonotone u)
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y) (hne : y ≠ x) : u x < u y :=
  (h x hx y (fun l => (hx l).trans (hxy l)) hxy hne).2 |> not_le.1

/-- With at least one good, strong monotonicity implies local nonsatiation (Exercise 3.B.1). -/
theorem UtilityStronglyMonotone.lns (hL : 0 < L) {u : (Fin L → ℝ) → ℝ}
    (h : UtilityStronglyMonotone u) : UtilityLNS u :=
  exercise_3_B_1b_orthant hL (exercise_3_B_1a hL h)

/-- Below the budget line a locally nonsatiated consumer finds a strictly better affordable
bundle. -/
theorem UtilityLNS.exists_better {u : (Fin L → ℝ) → ℝ} (h : UtilityLNS u) (p : Fin L → ℝ)
    {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) {w : ℝ} (hlt : p ⬝ᵥ x < w) :
    ∃ y ∈ nonnegOrthant L, p ⬝ᵥ y < w ∧ u x < u y := by
  obtain ⟨y, hy, hpy, hs⟩ := exists_better_affordable h p hx hlt
  exact ⟨y, hy, hpy, not_le.1 hs.2⟩

/-- A demanded bundle of a locally nonsatiated consumer exhausts wealth (Proposition 3.D.2(ii)). -/
theorem UtilityLNS.budget_eq {u : (Fin L → ℝ) → ℝ} (h : UtilityLNS u) {p : Fin L → ℝ} {w : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemandOn (nonnegOrthant L) u p w) : p ⬝ᵥ x = w :=
  proposition_3_D_2_ii (representsOn_utilityPref _ u) h hx

/-- Under local nonsatiation (consumption sets `ℝ^L₊`), Definition 15.B.1 as printed is equivalent
to its demand form: equilibrium bundles are affordable. -/
theorem isWalrasEqm_iff_isDemandEqm {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i)) (p : Fin L → ℝ)
    (x : ι → Fin L → ℝ) : E.IsWalrasEqm p x ↔ E.IsDemandEqm p x := by
  refine ⟨fun h => ?_, fun h => h.isWalrasEqm⟩
  have hx : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1 i
  have hb : ∀ i, p ⬝ᵥ x i ≤ p ⬝ᵥ E.ω i := by
    by_contra hne
    simp only [not_forall, not_le] at hne
    obtain ⟨i, hi⟩ := hne
    have hsum : ∑ k, p ⬝ᵥ x k = ∑ k, p ⬝ᵥ E.ω k := by
      rw [← dotProduct_sum, ← dotProduct_sum, h.1.2, ExchangeEconomy.totalEndowment]
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, p ⬝ᵥ x k < p ⬝ᵥ E.ω k := by
      by_contra hall
      simp only [Finset.mem_univ, true_and, not_exists, not_lt] at hall
      have := Finset.sum_lt_sum (fun k _ => hall k) ⟨i, Finset.mem_univ i, hi⟩
      linarith
    obtain ⟨y, hy, hpy, hu⟩ := (hlns k).exists_better p (hx k) hk
    have := h.2 k y ⟨hX k ▸ hy, hpy.le⟩
    linarith
  exact ⟨h.1, fun i => ⟨⟨h.1.1 i, hb i⟩, h.2 i⟩⟩

/-- The private ownership economy of Chapter 10 (Section 10.B) with no firms, whose competitive
equilibria are the Walrasian equilibria of the exchange economy. -/
def ExchangeEconomy.toPrivEconomy (E : ExchangeEconomy ι L) : PrivEconomy ι Empty L where
  X := E.X
  u := E.u
  Y := fun e => e.elim
  ωi := E.ω
  θ := fun _ e => e.elim

/-- **Definition 15.B.1 and Definition 10.B.3**. A Walrasian equilibrium of the exchange economy is
a competitive equilibrium (Chapter 10) of the private ownership economy with no firms. -/
theorem isDemandEqm_iff_competitiveEqm (E : ExchangeEconomy ι L) (p : Fin L → ℝ)
    (x : ι → Fin L → ℝ) :
    E.IsDemandEqm p x ↔ E.toPrivEconomy.IsCompetitiveEqm ⟨x, fun e => e.elim⟩ p := by
  have hw : ∀ i, E.toPrivEconomy.wealth ⟨x, fun e => e.elim⟩ p i = p ⬝ᵥ E.ω i := by
    intro i
    simp [PrivEconomy.wealth, ExchangeEconomy.toPrivEconomy]
  simp only [PrivEconomy.IsCompetitiveEqm, hw, ExchangeEconomy.IsDemandEqm,
    ExchangeEconomy.InBox, ExchangeEconomy.demand, ExchangeEconomy.IsAllocation,
    ExchangeEconomy.totalEndowment]
  constructor
  · rintro ⟨⟨-, hsum⟩, hd⟩
    refine ⟨fun e => e.elim, hd, fun l => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [← Finset.sum_apply, hsum, Finset.sum_apply]
    rfl
  · rintro ⟨-, hd, hc⟩
    refine ⟨⟨fun i => (hd i).1.1, ?_⟩, hd⟩
    funext l
    have := hc l
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at this
    rw [Finset.sum_apply, this, Finset.sum_apply]
    rfl

/-- Chapter 10's economy (Section 10.B) underlying the exchange economy. -/
def ExchangeEconomy.toEconomy (E : ExchangeEconomy ι L) : Economy ι Empty L :=
  E.toPrivEconomy.toEconomy

/-- **Definition 15.B.2 and Definition 10.B.2**. For utilities that are nondecreasing on `ℝ^L₊`,
Pareto optimality in the Edgeworth box (Definition 15.B.2) coincides with Pareto optimality among
feasible allocations (Definition 10.B.2), for box allocations. -/
theorem isParetoOptimal_iff_economy {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L)
    (hmono : ∀ i, ∀ x ∈ nonnegOrthant L, ∀ y, x ≤ y → E.u i x ≤ E.u i y)
    {x : ι → Fin L → ℝ} (hx : E.InBox x) :
    E.IsParetoOptimal x ↔ E.toEconomy.IsParetoOptimal ⟨x, fun e => e.elim⟩ := by
  classical
  have hfeas : ∀ x' : ι → Fin L → ℝ, E.toEconomy.IsFeasible ⟨x', fun e => e.elim⟩ ↔
      E.IsFeasible x' := by
    intro x'
    simp [Economy.IsFeasible, Economy.IsAllocation, ExchangeEconomy.toEconomy,
      PrivEconomy.toEconomy, ExchangeEconomy.toPrivEconomy, ExchangeEconomy.IsFeasible,
      ExchangeEconomy.IsAllocation, ExchangeEconomy.totalEndowment]
  constructor
  · rintro ⟨-, hno⟩
    refine ⟨(hfeas x).2 hx.isFeasible, ?_⟩
    rintro ⟨a', ha', hle, i, hi⟩
    -- give the slack to consumer `i`
    have ha'' : a' = ⟨a'.x, fun e => e.elim⟩ := by
      cases a'
      congr
      funext e
      exact e.elim
    have hf := (hfeas a'.x).1 (ha'' ▸ ha')
    set s : Fin L → ℝ := E.totalEndowment - ∑ k, a'.x k with hs
    have hs0 : ∀ l, 0 ≤ s l := fun l => by
      simp only [hs, Pi.sub_apply, Finset.sum_apply]
      linarith [hf.2 l]
    set x'' : ι → Fin L → ℝ := fun k => a'.x k + if k = i then s else 0 with hx''
    have hmem : ∀ k, a'.x k ∈ nonnegOrthant L := fun k => hX k ▸ hf.1 k
    have hge : ∀ k, E.u k (a'.x k) ≤ E.u k (x'' k) := by
      intro k
      refine hmono k _ (hmem k) _ fun l => ?_
      simp only [hx'', Pi.add_apply]
      split_ifs
      · linarith [hs0 l]
      · simp
    refine hno ⟨x'', ⟨fun k => ?_, ?_⟩, fun k => (hle k).trans (hge k),
      i, lt_of_lt_of_le hi (hge i)⟩
    · rw [hX k]
      intro l
      simp only [hx'', Pi.add_apply]
      split_ifs
      · exact add_nonneg (hmem k l) (hs0 l)
      · simpa using hmem k l
    · have : ∑ k, x'' k = ∑ k, a'.x k + s := by
        simp only [hx'', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
      rw [this, hs]
      abel
  · rintro ⟨-, hno⟩
    refine ⟨hx, ?_⟩
    rintro ⟨x', hx', hle, i, hi⟩
    exact hno ⟨⟨x', fun e => e.elim⟩, (hfeas x').2 hx'.isFeasible, hle, i, hi⟩

/-- **Section 15.B** (MWG, p. 519). At a Walrasian equilibrium with strictly positive prices the
offer curves of all consumers pass through the equilibrium bundles. -/
theorem offerCurve_of_isDemandEqm {E : ExchangeEconomy ι L} {p : Fin L → ℝ}
    {x : ι → Fin L → ℝ} (h : E.IsDemandEqm p x) (hp : StrictlyPositive p) (i : ι) :
    x i ∈ E.offerCurve i :=
  ⟨p, hp, h.2 i⟩

/-- Two vectors of `ℝ²` orthogonal to the same nonzero vector are proportional. -/
theorem proportional_of_orthogonal {p q d : Fin 2 → ℝ} (hd : d ≠ 0) (hp : p ⬝ᵥ d = 0)
    (hq : q ⬝ᵥ d = 0) : p 0 * q 1 = p 1 * q 0 := by
  simp only [dotProduct, Fin.sum_univ_two] at hp hq
  by_contra hne
  apply hd
  funext l
  fin_cases l
  · have : (p 0 * q 1 - p 1 * q 0) * d 0 = 0 := by linear_combination q 1 * hp - p 1 * hq
    simpa [sub_ne_zero.2 hne] using this
  · have : (p 0 * q 1 - p 1 * q 0) * d 1 = 0 := by linear_combination p 0 * hq - q 0 * hp
    simpa [sub_ne_zero.2 hne] using this

/-- **Section 15.B** (MWG, p. 519). In an Edgeworth box with locally nonsatiated consumers, any
intersection `x*` of the two offer curves other than the endowment point is a Walrasian
equilibrium allocation: each `x*ᵢ` is optimal for the budget line through `ω` and `x*`. -/
theorem isDemandEqm_of_offerCurves {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x)
    (hne : x 0 ≠ E.ω 0) (h0 : x 0 ∈ E.offerCurve 0) (h1 : x 1 ∈ E.offerCurve 1) :
    ∃ p, StrictlyPositive p ∧ E.IsDemandEqm p x := by
  obtain ⟨p, hp, hd0⟩ := h0
  obtain ⟨q, hq, hd1⟩ := h1
  have hb0 : p ⬝ᵥ x 0 = p ⬝ᵥ E.ω 0 := (hlns 0).budget_eq (by rw [← hX 0]; exact hd0)
  have hb1 : q ⬝ᵥ x 1 = q ⬝ᵥ E.ω 1 := (hlns 1).budget_eq (by rw [← hX 1]; exact hd1)
  have hsum : x 0 + x 1 = E.ω 0 + E.ω 1 := by
    have := hx.2
    simpa [ExchangeEconomy.totalEndowment, Fin.sum_univ_two] using this
  set d := x 0 - E.ω 0 with hdd
  have hd : d ≠ 0 := sub_ne_zero.2 hne
  have hpd : p ⬝ᵥ d = 0 := by rw [hdd, dotProduct_sub, hb0, sub_self]
  have hqd : q ⬝ᵥ d = 0 := by
    have : d = -(x 1 - E.ω 1) := by
      rw [hdd]
      have : x 0 - E.ω 0 = E.ω 1 - x 1 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm (E.ω 1), ← hsum, add_comm]
      rw [this]
      abel
    rw [this, dotProduct_neg, dotProduct_sub, hb1, sub_self, neg_zero]
  have hprop := proportional_of_orthogonal hd hpd hqd
  set α := q 0 / p 0 with hα
  have hα0 : 0 < α := div_pos (hq 0) (hp 0)
  have hqα : q = α • p := by
    funext l
    fin_cases l
    · simp [hα, (hp 0).ne']
    · simp only [hα, Pi.smul_apply, smul_eq_mul]
      field_simp [(hp 0).ne']
      simp only [Fin.isValue, Fin.mk_one] at hprop ⊢
      linarith
  refine ⟨p, hp, hx, fun i => ?_⟩
  fin_cases i
  · exact hd0
  · have := hd1
    rw [hqα, E.demand_smul 1 p hα0] at this
    exact this

/-- **Exercise 15.B.1(a)** (MWG, p. 540). With locally nonsatiated consumers (consumption sets
`ℝ^L₊`), the value of aggregate excess demand is zero at every price vector:
`∑_ℓ p_ℓ (∑ᵢ x_{ℓi}(p) - ω̄_ℓ) = 0`. -/
theorem exercise_15_B_1a {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (hx : ∀ i, x i ∈ E.demand i p) :
    ∑ l, p l * (∑ i, x i l - E.totalEndowment l) = 0 := by
  have hb : ∀ i, p ⬝ᵥ x i = p ⬝ᵥ E.ω i := fun i =>
    (hlns i).budget_eq (by rw [← hX i]; exact hx i)
  have : p ⬝ᵥ (∑ i, x i - E.totalEndowment) = 0 := by
    rw [dotProduct_sub, dotProduct_sum, ExchangeEconomy.totalEndowment, dotProduct_sum,
      Finset.sum_congr rfl fun i _ => hb i, sub_self]
  simpa [dotProduct, Finset.sum_apply] using this

/-- **Exercise 15.B.1(b)** (MWG, p. 540). In an Edgeworth box with locally nonsatiated consumers,
if the market for good 1 clears at `p* ≫ 0`, so does the market for good 2, and `p*` is a
Walrasian equilibrium price vector. -/
theorem exercise_15_B_1b {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {x : Fin 2 → Fin 2 → ℝ} (hx : ∀ i, x i ∈ E.demand i p)
    (h1 : ∑ i, x i 0 = E.totalEndowment 0) : E.IsDemandEqm p x := by
  have hw := exercise_15_B_1a hX hlns hx
  simp only [Fin.sum_univ_two] at hw h1 ⊢
  have h2 : x 0 1 + x 1 1 = E.totalEndowment 1 := by
    have : p 1 * (x 0 1 + x 1 1 - E.totalEndowment 1) = 0 := by
      rw [h1, sub_self, mul_zero, zero_add] at hw
      exact hw
    have := (mul_eq_zero.1 this).resolve_left (hp 1).ne'
    linarith
  refine ⟨⟨fun i => (hx i).1.1, ?_⟩, hx⟩
  funext l
  fin_cases l
  · simpa [Fin.sum_univ_two] using h1
  · simpa [Fin.sum_univ_two] using h2

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Analytic tools for Chapter 15

Small lemmas used throughout the chapter.

* `exists_pos_continuous_lt`: along a continuous path in `ℝ^L₊` starting at a point where a
  continuous utility exceeds `c`, the utility still exceeds `c` a little way along the path.
* `eventually_gt_of_deriv_pos`, `exists_pos_deriv_pos`: a function with positive derivative at
  `0` exceeds its value at `0` at small `t > 0` satisfying any eventual side condition.
* `quasiconcave_of_prefConvex`: convex preferences (Definition 3.B.4) give quasiconcave
  utilities in the form `min (u y) (u z) ≤ u (a y + b z)`.
* `dotProduct_pos_of_strictlyPositive`: `p ≫ 0`, `x ≥ 0`, `x ≠ 0` imply `p·x > 0`.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- Along a continuous path `g` in `ℝ^L₊` (on `[0, 1]`) starting at `a`, a utility that is
continuous on `ℝ^L₊` and exceeds `c` at `a` still exceeds `c` at some `g t`, `0 < t ≤ 1`. -/
theorem exists_pos_continuous_lt {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    {g : ℝ → Fin L → ℝ} (hg : Continuous g)
    (hgmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L) {c : ℝ} (hca : c < u (g 0)) :
    ∃ t, 0 < t ∧ t ≤ 1 ∧ c < u (g t) := by
  have h1 : ContinuousWithinAt (u ∘ g) (Set.Icc 0 1) 0 :=
    (hc.comp hg.continuousOn fun t ht => hgmem t ht) 0 ⟨le_rfl, zero_le_one⟩
  have h2 : ∀ᶠ t in 𝓝[Set.Icc 0 1] (0 : ℝ), c < (u ∘ g) t := h1.eventually (lt_mem_nhds hca)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, hball⟩ := h2
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, ?_⟩
  refine hball ?_ ⟨(lt_min (half_pos hε) one_pos).le, min_le_right _ _⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (half_pos hε) one_pos)]
  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

/-- A function with positive derivative at `0` exceeds `f 0` at all small `t > 0`. -/
theorem eventually_gt_of_deriv_pos {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 < f t := by
  have hs := hf.tendsto_slope_zero_right
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (f (0 + t) - f 0) := hs.eventually (lt_mem_nhds hd)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [h1, h2] with t ht1 ht2
  rw [zero_add, smul_eq_mul] at ht1
  have := (mul_pos_iff_of_pos_left (inv_pos.2 ht2)).1 ht1
  linarith

/-- A function with positive derivative at `0` exceeds `f 0` at some small `t > 0` at which a
given eventual property also holds. -/
theorem exists_pos_deriv_pos {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : 0 < d)
    {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ t, 0 < t ∧ P t ∧ f 0 < f t := by
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht1, ht2, ht3⟩ := ((eventually_gt_of_deriv_pos hf hd).and (h2.and hP)).exists
  exact ⟨t, ht2, ht3, ht1⟩

/-- A function with negative derivative at `0` falls below `f 0` at some small `t > 0` at which a
given eventual property also holds. -/
theorem exists_pos_deriv_neg {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : d < 0)
    {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ t, 0 < t ∧ P t ∧ f t < f 0 := by
  obtain ⟨t, ht, hPt, hlt⟩ := exists_pos_deriv_pos hf.neg (neg_pos.2 hd) hP
  exact ⟨t, ht, hPt, by simpa using hlt⟩

/-- Convex preferences (Definition 3.B.4) represented by `u` on `ℝ^L₊`: `u` is quasiconcave,
`min (u y) (u z) ≤ u (a y + b z)` for `a, b ≥ 0`, `a + b = 1`. -/
theorem quasiconcave_of_prefConvex {u : (Fin L → ℝ) → ℝ}
    (h : PrefConvex (nonnegOrthant L) (utilityPref u)) {y z : Fin L → ℝ}
    (hy : y ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : min (u y) (u z) ≤ u (a • y + b • z) := by
  rcases le_total (u y) (u z) with hyz | hyz
  · rw [min_eq_left hyz]
    have := h y hy (⟨hy, le_refl (u y)⟩ : y ∈ upperContour _ (utilityPref u) y)
      (⟨hz, hyz⟩ : z ∈ upperContour _ (utilityPref u) y) ha hb hab
    exact this.2
  · rw [min_eq_right hyz]
    have := h z hz (⟨hy, hyz⟩ : y ∈ upperContour _ (utilityPref u) z)
      (⟨hz, le_refl (u z)⟩ : z ∈ upperContour _ (utilityPref u) z) ha hb hab
    exact this.2

/-- `p ≫ 0`, `x ≥ 0` and `x ≠ 0` imply `p·x > 0`. -/
theorem dotProduct_pos_of_strictlyPositive {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (hne : x ≠ 0) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ : ∃ l, x l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (funext h)
  have hpos : 0 < p l * x l := mul_pos (hp l) (lt_of_le_of_ne (hx l) (Ne.symm hl))
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => p k * x k)
    (fun k _ => mul_nonneg (hp k).le (hx k)) (Finset.mem_univ l))

/-- `p ≥ 0` and `x ≥ 0` imply `p·x ≥ 0`. -/
theorem dotProduct_nonneg_of_nonneg {p x : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l)
    (hx : x ∈ nonnegOrthant L) : 0 ≤ p ⬝ᵥ x :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (hx l)

/-- `p ≫ 0`, `x ≥ 0` and `p·x ≤ 0` imply `x = 0`. -/
theorem eq_zero_of_dotProduct_nonpos {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (h : p ⬝ᵥ x ≤ 0) : x = 0 := by
  by_contra hne
  exact absurd h (not_le.2 (dotProduct_pos_of_strictlyPositive hp hx hne))

/-- The tangent line of a concave function lies above its graph: if `f` is concave on `S` and
differentiable at `a ∈ S`, then `f z ≤ f a + f'(a) (z - a)` for `z ∈ S`. -/
theorem concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} {f' a z : ℝ} (hfc : ConcaveOn ℝ S f)
    (ha : a ∈ S) (hz : z ∈ S) (hf : HasDerivAt f f' a) : f z ≤ f a + f' * (z - a) := by
  rcases lt_trichotomy z a with hlt | heq | hgt
  · have h := hfc.le_slope_of_hasDerivAt hz ha hlt hf
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · rw [heq]; simp
  · have h := hfc.slope_le_of_hasDerivAt ha hz hgt hf
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Welfare properties of Walrasian equilibria in exchange economies (MWG Section 15.B, pp. 522-525)

* **First welfare theorem** (p. 524, Exercise 15.B.3): with locally nonsatiated preferences every
  Walrasian equilibrium allocation is Pareto optimal (`first_welfare_theorem`), and it lies on the
  contract curve (`walrasEqm_mem_contractCurve`). Both are proved for any number of consumers and
  goods, and for Definition 15.B.1 as printed.
* **Tangency** (p. 523): at an interior Pareto optimum of the Edgeworth box with differentiable
  utilities the gradients are proportional (`paretoOptimal_interior_tangency`).
* **Second welfare theorem** (p. 524): with continuous, convex and strongly monotone preferences
  and a strictly positive total endowment, every Pareto optimal allocation is supportable as an
  equilibrium with transfers (`second_welfare_theorem`, any number of consumers and goods; the
  proof separates the endowment from the set of aggregate bundles that make everybody better off
  by the Hahn-Banach theorem). The supporting prices are strictly positive.
* Figure 15.B.13(b): the transfers can be made by moving endowments on the budget line, in
  particular to the allocation itself, which is then a no-trade Walrasian equilibrium
  (`walrasEqm_of_endowment_transfer`, `walrasEqm_at_allocation`).
* **Footnote 4** (p. 525): after endowments are moved to a Pareto optimal `x*`, `x*` is the unique
  Walrasian equilibrium allocation under strictly convex preferences (`footnote_4_unique`); without
  strict convexity it need not be (`footnote_4_needs_strict_convexity`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- **First fundamental welfare theorem** (MWG, p. 524; Exercise 15.B.3, p. 540). With consumption
sets `ℝ^L₊` and locally nonsatiated preferences, every Walrasian equilibrium allocation
(Definition 15.B.1 as printed) is Pareto optimal (Definition 15.B.2). -/
theorem first_welfare_theorem {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsWalrasEqm p x) : E.IsParetoOptimal x := by
  have hd := (isWalrasEqm_iff_isDemandEqm hX hlns p x).1 h
  refine ⟨h.1, ?_⟩
  rintro ⟨x', hx', hle, i, hi⟩
  have hx'm : ∀ k, x' k ∈ nonnegOrthant L := fun k => hX k ▸ hx'.1 k
  -- weakly preferred bundles cost at least the endowment value, strictly preferred ones more
  have hge : ∀ k, p ⬝ᵥ E.ω k ≤ p ⬝ᵥ x' k := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hpy, hu⟩ := (hlns k).exists_better p (hx'm k) hlt
    have := (hd.2 k).2 y ⟨hX k ▸ hy, hpy.le⟩
    linarith [hle k]
  have hgt : p ⬝ᵥ E.ω i < p ⬝ᵥ x' i := by
    by_contra hle'
    rw [not_lt] at hle'
    have := (hd.2 i).2 (x' i) ⟨hx'.1 i, hle'⟩
    linarith
  have hsum : ∑ k, p ⬝ᵥ x' k = ∑ k, p ⬝ᵥ E.ω k := by
    rw [← dotProduct_sum, ← dotProduct_sum, hx'.2, ExchangeEconomy.totalEndowment]
  have := Finset.sum_lt_sum (fun k _ => hge k) ⟨i, Finset.mem_univ i, hgt⟩
  linarith

/-- **Exercise 15.B.3** (MWG, p. 540). In an Edgeworth box economy with locally nonsatiated
preferences a Walrasian equilibrium is Pareto optimal (the book asks for a graphical argument). -/
theorem exercise_15_B_3 {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : E.IsWalrasEqm p x) : E.IsParetoOptimal x :=
  first_welfare_theorem hX hlns h

/-- **Section 15.B** (MWG, p. 524). Every Walrasian equilibrium allocation lies on the contract
curve: it is Pareto optimal and each consumer is at least as well off as at his endowment. -/
theorem walrasEqm_mem_contractCurve {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i))
    (hω : ∀ i, E.ω i ∈ E.X i) {p : Fin L → ℝ} {x : ι → Fin L → ℝ} (h : E.IsWalrasEqm p x) :
    x ∈ E.contractCurve :=
  ⟨first_welfare_theorem hX hlns h, fun i => h.2 i _ ⟨hω i, le_rfl⟩⟩

/-- **Section 15.B** (MWG, p. 523). At a Pareto optimal allocation in the interior of the
Edgeworth box at which both utilities are differentiable, the indifference curves are tangent:
the gradients `∇u₁(x₁)` and `∇u₂(x₂)` are parallel. -/
theorem paretoOptimal_interior_tangency {E : EdgeworthEconomy}
    (hX : ∀ i, E.X i = nonnegOrthant 2) {x : Fin 2 → Fin 2 → ℝ} (hpo : E.IsParetoOptimal x)
    (hint : ∀ i l, 0 < x i l) {g₁ g₂ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (h₁ : HasFDerivAt (E.u 0) g₁ (x 0)) (h₂ : HasFDerivAt (E.u 1) g₂ (x 1)) :
    g₁ (Pi.single 0 1) * g₂ (Pi.single 1 1) = g₁ (Pi.single 1 1) * g₂ (Pi.single 0 1) := by
  by_contra hne
  set a0 := g₁ (Pi.single 0 1)
  set a1 := g₁ (Pi.single 1 1)
  set b0 := g₂ (Pi.single 0 1)
  set b1 := g₂ (Pi.single 1 1)
  set D := a0 * b1 - a1 * b0 with hD
  have hD0 : D ≠ 0 := sub_ne_zero.2 hne
  set d : Fin 2 → ℝ := ![(b1 + a1) / D, -(a0 + b0) / D] with hd
  have hg : ∀ g : (Fin 2 → ℝ) →L[ℝ] ℝ, g d = d 0 * g (Pi.single 0 1) + d 1 * g (Pi.single 1 1) :=
    by
    intro g
    have := LinearMap.pi_apply_eq_sum_univ g.toLinearMap d
    simp only [ContinuousLinearMap.coe_coe, Fin.sum_univ_two, smul_eq_mul] at this
    rw [this]
    congr 2 <;> congr 1 <;> funext j <;> fin_cases j <;> simp
  have hg1 : g₁ d = 1 := by
    rw [hg]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hD]
    ring
  have hg2 : g₂ d = -1 := by
    rw [hg]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hD]
    ring
  -- move along `d` for consumer 1 and along `-d` for consumer 2
  have hl1 : HasDerivAt (fun t : ℝ => x 0 + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (x 0)
  have hl2 : HasDerivAt (fun t : ℝ => x 1 - t • d) (-d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_sub (x 1)
  have hc1 : HasDerivAt (fun t : ℝ => E.u 0 (x 0 + t • d)) 1 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using h₁) hl1
    simpa [Function.comp_def, hg1] using this
  have hc2 : HasDerivAt (fun t : ℝ => E.u 1 (x 1 - t • d)) 1 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using h₂) hl2
    simpa [Function.comp_def, hg2] using this
  have hint1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (x 0 + t • d) l := by
    refine eventually_all.2 fun l => ?_
    have hc : Continuous fun t : ℝ => (x 0 + t • d) l := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hint 0 l))
  have hint2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (x 1 - t • d) l := by
    refine eventually_all.2 fun l => ?_
    have hc : Continuous fun t : ℝ => (x 1 - t • d) l := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hint 1 l))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ l, 0 < (x 0 + t • d) l) ∧ (∀ l, 0 < (x 1 - t • d) l) ∧
      E.u 1 (x 1 - (0 : ℝ) • d) < E.u 1 (x 1 - t • d) :=
    (hint1.filter_mono nhdsWithin_le_nhds).and ((hint2.filter_mono nhdsWithin_le_nhds).and
      (eventually_gt_of_deriv_pos hc2 one_pos))
  obtain ⟨t, -, ⟨hm1, hm2, hu2⟩, hu1⟩ := exists_pos_deriv_pos hc1 one_pos hev
  simp only [zero_smul, add_zero, sub_zero] at hu1 hu2
  set x' : Fin 2 → Fin 2 → ℝ := ![x 0 + t • d, x 1 - t • d] with hx'
  apply hpo.2
  refine ⟨x', ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, by simpa [hx'] using hu1⟩
  · rw [hX i]
    fin_cases i
    · exact fun l => (hm1 l).le
    · exact fun l => (hm2 l).le
  · rw [← hpo.1.2]
    simp [hx', Fin.sum_univ_two]
  · fin_cases i
    · simpa [hx'] using hu1.le
    · simpa [hx'] using hu2.le

/-- Strong monotonicity gives weak monotonicity: `x ≤ y` implies `u(x) ≤ u(y)`. -/
theorem UtilityStronglyMonotone.le {u : (Fin L → ℝ) → ℝ} (h : UtilityStronglyMonotone u)
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y) : u x ≤ u y := by
  by_cases he : y = x
  · rw [he]
  · exact (h.lt hx hxy he).le

/-- Adding a bundle to one consumer's consumption adds it to the aggregate. -/
theorem sum_add_ite_eq [DecidableEq ι] (y : ι → Fin L → ℝ) (i : ι) (d : Fin L → ℝ) :
    ∑ k, (y k + if k = i then d else 0) = ∑ k, y k + d := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The constant vector with entries `1`. -/
def onesVec (L : ℕ) : Fin L → ℝ := fun _ => 1

/-- `p·(c·𝟙) = c ∑_ℓ p_ℓ`. -/
theorem dotProduct_smul_onesVec (p : Fin L → ℝ) (c : ℝ) :
    p ⬝ᵥ (c • onesVec L) = c * ∑ l, p l := by
  simp only [dotProduct, onesVec, Pi.smul_apply, smul_eq_mul, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- With at least one good, strong monotonicity makes `x + c𝟙` (`c > 0`) strictly better. -/
theorem UtilityStronglyMonotone.lt_add_ones (hL : 0 < L) {u : (Fin L → ℝ) → ℝ}
    (h : UtilityStronglyMonotone u) {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) {c : ℝ}
    (hc : 0 < c) : u x < u (x + c • onesVec L) := by
  refine h.lt hx (fun l => by simp [onesVec, hc.le]) fun he => ?_
  have := congrFun he ⟨0, hL⟩
  simp [onesVec, hc.ne'] at this

/-- **Second fundamental welfare theorem** (MWG, p. 524). If consumption sets are `ℝ^L₊`,
preferences are represented by continuous utilities and are convex (Definition 3.B.4) and strongly
monotone (Definition 3.B.2), and the total endowment is strictly positive, then every Pareto
optimal allocation `x*` is supportable as an equilibrium with transfers (Definition 15.B.3), with
strictly positive prices `p*` and transfers `Tᵢ = p*·x*ᵢ - p*·ωᵢ`. (The book states it for the
Edgeworth box; the proof works for any number of consumers and goods.) -/
theorem second_welfare_theorem (hL : 0 < L) {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hconv : ∀ i, PrefConvex (nonnegOrthant L) (utilityPref (E.u i)))
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ l, 0 < E.totalEndowment l)
    {x : ι → Fin L → ℝ} (hpo : E.IsParetoOptimal x) :
    ∃ p, StrictlyPositive p ∧ E.IsEqmWithTransfers p (fun i => p ⬝ᵥ x i - p ⬝ᵥ E.ω i) x := by
  classical
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ hpo.1.1 i
  have hsumx : ∑ i, x i = E.totalEndowment := hpo.1.2
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hω ⟨0, hL⟩
    simp [ExchangeEconomy.totalEndowment] at this
  -- the aggregate bundles that make everybody strictly better off, and their upper set `W`
  set V : Set (Fin L → ℝ) := {v | ∃ y : ι → Fin L → ℝ,
    (∀ i, y i ∈ nonnegOrthant L ∧ E.u i (x i) < E.u i (y i)) ∧ v = ∑ i, y i} with hV
  set W : Set (Fin L → ℝ) := {z | ∃ v ∈ V, ∀ l, v l < z l} with hW
  have hWconv : Convex ℝ W := by
    rintro z ⟨v, ⟨y, hy, rfl⟩, hvz⟩ z' ⟨v', ⟨y', hy', rfl⟩, hvz'⟩ a b ha hb hab
    refine ⟨∑ i, (a • y i + b • y' i), ⟨fun i => a • y i + b • y' i, fun i => ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact fun l => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha ((hy i).1 l)) (mul_nonneg hb ((hy' i).1 l))
    · exact lt_of_lt_of_le (lt_min (hy i).2 (hy' i).2)
        (quasiconcave_of_prefConvex (hconv i) (hy i).1 (hy' i).1 ha hb hab)
    · intro l
      simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      have h1 := hvz l
      have h2 := hvz' l
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        linarith
      · nlinarith [mul_lt_mul_of_pos_left h1 ha0, mul_le_mul_of_nonneg_left h2.le hb]
  have hWopen : IsOpen W := by
    have : W = ⋃ v ∈ V, ⋂ l, {z : Fin L → ℝ | v l < z l} := by
      ext z
      simp only [hW, Set.mem_iUnion, Set.mem_iInter, exists_prop]
      rfl
    rw [this]
    exact isOpen_biUnion fun v _ =>
      isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)
  have hnot : E.totalEndowment ∉ W := by
    rintro ⟨v, ⟨y, hy, rfl⟩, hlt⟩
    set d := E.totalEndowment - ∑ i, y i with hd
    have hdpos : ∀ l, 0 < d l := fun l => by
      simp only [hd, Pi.sub_apply]
      linarith [hlt l]
    set y' : ι → Fin L → ℝ := fun k => y k + if k = i₀ then d else 0 with hy'
    apply hpo.2
    refine ⟨y', ⟨fun k => ?_, ?_⟩, fun k => ?_, i₀, ?_⟩
    · rw [hX k]
      intro l
      simp only [hy', Pi.add_apply]
      split_ifs
      · exact add_nonneg ((hy k).1 l) (hdpos l).le
      · simpa using (hy k).1 l
    · rw [hy', sum_add_ite_eq, hd]
      abel
    · refine ((hy k).2.trans_le ?_).le
      refine (hmono k).le (hy k).1 fun l => ?_
      simp only [hy', Pi.add_apply]
      split_ifs
      · linarith [hdpos l]
      · simp
    · refine lt_of_lt_of_le (hy i₀).2 ((hmono i₀).le (hy i₀).1 fun l => ?_)
      simp only [hy', ↓reduceIte, Pi.add_apply]
      linarith [hdpos l]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hWconv hWopen hnot
  set p : Fin L → ℝ := fun l => -f (Pi.single l 1) with hp
  have hfp : ∀ z, f z = -(p ⬝ᵥ z) := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap z
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have he : (fun j => if l = j then (1 : ℝ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [he, hp]
    ring
  have hWp : ∀ z ∈ W, p ⬝ᵥ E.totalEndowment < p ⬝ᵥ z := by
    intro z hz
    have := hf z hz
    rw [hfp, hfp] at this
    linarith
  set S := ∑ l, |p l| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hpone : ∀ c : ℝ, 0 ≤ c → p ⬝ᵥ (c • onesVec L) ≤ c * S := by
    intro c hc
    rw [dotProduct_smul_onesVec]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => le_abs_self _) hc
  -- (5) aggregate bundles making everybody strictly better off cost at least `p·ω̄`
  have hP : ∀ y : ι → Fin L → ℝ, (∀ i, y i ∈ nonnegOrthant L ∧ E.u i (x i) < E.u i (y i)) →
      p ⬝ᵥ E.totalEndowment ≤ p ⬝ᵥ ∑ i, y i := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    set gap := p ⬝ᵥ E.totalEndowment - p ⬝ᵥ ∑ i, y i with hgap
    have hgap0 : 0 < gap := by linarith
    set ε := gap / (S + 1) with hε
    have hε0 : 0 < ε := div_pos hgap0 (by linarith)
    have hmem : ∑ i, y i + ε • onesVec L ∈ W :=
      ⟨∑ i, y i, ⟨y, hy, rfl⟩, fun l => by simp [onesVec, hε0]⟩
    have h1 := hWp _ hmem
    have h2 := hpone ε hε0.le
    rw [dotProduct_add] at h1
    have h3 : ε * S < gap := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  -- (6) prices are nonnegative
  have hpnn : ∀ l, 0 ≤ p l := by
    intro l
    by_contra hneg
    rw [not_le] at hneg
    set y : ι → Fin L → ℝ := fun k => x k + (1 : ℝ) • onesVec L with hy
    have hyb : ∀ k, y k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (y k) := fun k =>
      ⟨fun l => by simp [hy, onesVec, add_nonneg (hxm k l)],
        (hmono k).lt_add_ones hL (hxm k) one_pos⟩
    set M := (|p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment| + 1) / (-p l) with hM
    have hM0 : 0 < M := div_pos (by positivity) (by linarith)
    set y' : ι → Fin L → ℝ := fun k => y k + if k = i₀ then M • Pi.single l 1 else 0 with hy'
    have hy'b : ∀ k, y' k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (y' k) := by
      intro k
      have hle : y k ≤ y' k := fun j => by
        simp only [hy', Pi.add_apply]
        split_ifs
        · simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          split_ifs <;> linarith
        · simp
      exact ⟨fun j => le_trans ((hyb k).1 j) (hle j),
        lt_of_lt_of_le (hyb k).2 ((hmono k).le (hyb k).1 hle)⟩
    have := hP y' hy'b
    rw [hy', sum_add_ite_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hpl : p ⬝ᵥ Pi.single l 1 = p l := by simp
    rw [hpl] at this
    have hMp : M * p l = -(|p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment| + 1) := by
      rw [hM, div_mul_eq_mul_div, div_eq_iff (by linarith)]
      ring
    rw [hMp] at this
    have := le_abs_self (p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment)
    linarith
  have hS' : S = ∑ l, p l := Finset.sum_congr rfl fun l _ => abs_of_nonneg (hpnn l)
  -- (7) quasi-equilibrium: strictly preferred bundles cost at least as much
  have hq : ∀ i, ∀ y ∈ nonnegOrthant L, E.u i (x i) < E.u i y → p ⬝ᵥ x i ≤ p ⬝ᵥ y := by
    intro i y hy hu
    by_contra hlt
    rw [not_le] at hlt
    set gap := p ⬝ᵥ x i - p ⬝ᵥ y with hgap
    have hgap0 : 0 < gap := by linarith
    set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    set δ := gap / (2 * (n * S + 1)) with hδ
    have hnS : 0 ≤ n * S := mul_nonneg hn0 hS0
    have hδ0 : 0 < δ := div_pos hgap0 (by linarith)
    set Y : ι → Fin L → ℝ := fun k =>
      (x k + δ • onesVec L) + if k = i then y - x i - δ • onesVec L else 0 with hY
    have hYb : ∀ k, Y k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (Y k) := by
      intro k
      by_cases hk : k = i
      · have : Y k = y := by
          simp only [hY, hk, ↓reduceIte]
          abel
        rw [this, hk]
        exact ⟨hy, hu⟩
      · have : Y k = x k + δ • onesVec L := by simp [hY, hk]
        rw [this]
        exact ⟨fun l => by simp [onesVec, add_nonneg (hxm k l) hδ0.le],
          (hmono k).lt_add_ones hL (hxm k) hδ0⟩
    have h1 := hP Y hYb
    rw [hY, sum_add_ite_eq, Finset.sum_add_distrib, hsumx] at h1
    simp only [Finset.sum_const, Finset.card_univ, dotProduct_add, dotProduct_sub] at h1
    have e1 : p ⬝ᵥ (Fintype.card ι • (δ • onesVec L)) = n * (δ * S) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, dotProduct_smul, dotProduct_smul_onesVec, hS', hn,
        smul_eq_mul]
    have e2 : p ⬝ᵥ (δ • onesVec L) = δ * S := by rw [dotProduct_smul_onesVec, hS']
    rw [e1, e2] at h1
    have h2 : n * (δ * S) < gap := by
      have : n * (δ * S) = δ * (n * S) := by ring
      rw [this, hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have h3 : 0 ≤ δ * S := mul_nonneg hδ0.le hS0
    linarith
  -- (8) prices are strictly positive
  have hpne : ∃ k, p k ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    set y : ι → Fin L → ℝ := fun k => x k + (1 : ℝ) • onesVec L
    have hmem : ∑ k, y k + (1 : ℝ) • onesVec L ∈ W :=
      ⟨∑ k, y k, ⟨y, fun k => ⟨fun l => by simp [y, onesVec, add_nonneg (hxm k l)],
        (hmono k).lt_add_ones hL (hxm k) one_pos⟩, rfl⟩, fun l => by simp [onesVec]⟩
    have := hWp _ hmem
    simp [dotProduct, hall] at this
  have hppos : StrictlyPositive p := by
    intro l
    rcases eq_or_lt_of_le (hpnn l) with h0 | h0
    · exfalso
      obtain ⟨k, hk⟩ := hpne
      have hpk : 0 < p k := lt_of_le_of_ne (hpnn k) (Ne.symm hk)
      have hkl : k ≠ l := fun h => by rw [h] at hk; exact hk h0.symm
      obtain ⟨i, hi⟩ : ∃ i, 0 < x i k := by
        by_contra hall
        simp only [not_exists, not_lt] at hall
        have h1 : ∑ i, x i k ≤ 0 := Finset.sum_nonpos fun i _ => hall i
        have h2 := hω k
        rw [← hsumx, Finset.sum_apply] at h2
        linarith
      set g : ℝ → Fin L → ℝ := fun t => x i + Pi.single l 1 - (t * x i k) • Pi.single k 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L := by
        intro t ht j
        simp only [g, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hjk : j = k
        · subst hjk
          simp only [hkl, ↓reduceIte, add_zero, mul_one]
          nlinarith [ht.2, hi]
        · simp only [hjk, ↓reduceIte, mul_zero, sub_zero]
          split_ifs <;> linarith [hxm i j]
      have hg0 : E.u i (x i) < E.u i (g 0) := by
        refine (hmono i).lt (hxm i) (fun j => ?_) fun he => ?_
        · simp only [g, zero_mul, zero_smul, sub_zero, Pi.add_apply, Pi.single_apply]
          split_ifs <;> linarith
        · have := congrFun he l
          simp [g] at this
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt (hcont i) hgc hgm hg0
      have := hq i (g t) (hgm t ⟨ht0.le, ht1⟩) ht
      simp only [g, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
      have e1 : p ⬝ᵥ Pi.single l 1 = p l := by simp
      have e2 : p ⬝ᵥ Pi.single k 1 = p k := by simp
      rw [e1, e2, ← h0] at this
      nlinarith [mul_pos (mul_pos ht0 hi) hpk]
    · exact h0
  -- (9) the equilibrium with transfers
  refine ⟨p, hppos, hpo.1, ?_, fun i y hyX hb => ?_⟩
  · rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsumx,
      ExchangeEconomy.totalEndowment, sub_self]
  · have hy : y ∈ nonnegOrthant L := hX i ▸ hyX
    simp only [add_sub_cancel] at hb
    by_contra hlt
    rw [not_le] at hlt
    have hge := hq i y hy hlt
    by_cases hpy : p ⬝ᵥ y ≤ 0
    · have hy0 := eq_zero_of_dotProduct_nonpos hppos hy hpy
      have hx0 := eq_zero_of_dotProduct_nonpos hppos (hxm i) (hge.trans hpy)
      rw [hy0, hx0] at hlt
      exact lt_irrefl _ hlt
    · rw [not_le] at hpy
      set g : ℝ → Fin L → ℝ := fun t => (1 - t / 2) • y
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L := by
        intro t ht j
        simp only [g, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith [ht.2]) (hy j)
      have hg0 : E.u i (x i) < E.u i (g 0) := by simpa [g] using hlt
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt (hcont i) hgc hgm hg0
      have := hq i (g t) (hgm t ⟨ht0.le, ht1⟩) ht
      simp only [g, dotProduct_smul, smul_eq_mul] at this
      nlinarith

/-- **Second fundamental welfare theorem** (MWG, p. 524), the Edgeworth box statement: with
continuous, convex and strongly monotone preferences (and `ω̄ ≫ 0`), every Pareto optimal
allocation is supportable as an equilibrium with transfers. -/
theorem second_welfare_theorem_edgeworth {E : EdgeworthEconomy}
    (hX : ∀ i, E.X i = nonnegOrthant 2) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant 2))
    (hconv : ∀ i, PrefConvex (nonnegOrthant 2) (utilityPref (E.u i)))
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ l, 0 < E.totalEndowment l)
    {x : Fin 2 → Fin 2 → ℝ} (hpo : E.IsParetoOptimal x) : E.IsSupportable x := by
  obtain ⟨p, -, h⟩ := second_welfare_theorem two_pos hX hcont hconv hmono hω hpo
  exact ⟨p, _, h⟩

/-- Under local nonsatiation, an equilibrium with transfers exhausts every consumer's wealth:
`p·x*ᵢ = p·ωᵢ + Tᵢ`. -/
theorem ExchangeEconomy.IsEqmWithTransfers.wealth_eq {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ}
    {T : ι → ℝ} {x : ι → Fin L → ℝ} (h : E.IsEqmWithTransfers p T x) (i : ι) :
    p ⬝ᵥ x i = p ⬝ᵥ E.ω i + T i := by
  have hge : ∀ k, p ⬝ᵥ E.ω k + T k ≤ p ⬝ᵥ x k := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hpy, hu⟩ := (hlns k).exists_better p (hX k ▸ h.1.1 k) hlt
    have := h.2.2 k y (hX k ▸ hy) hpy.le
    linarith
  have hsum : ∑ k, (p ⬝ᵥ E.ω k + T k) = ∑ k, p ⬝ᵥ x k := by
    rw [Finset.sum_add_distrib, h.2.1, add_zero, ← dotProduct_sum, ← dotProduct_sum, h.1.2,
      ExchangeEconomy.totalEndowment]
  exact ((Finset.sum_eq_sum_iff_of_le fun k _ => hge k).1 hsum i (Finset.mem_univ i)).symm

/-- **Figure 15.B.13(b)** (MWG, p. 525). Wealth transfers can be replaced by transfers of
endowments: if `(p*, T)` supports `x*` and the new endowments `ω'ᵢ` (with the same total) satisfy
`p*·ω'ᵢ = p*·ωᵢ + Tᵢ`, then `(p*, x*)` is a Walrasian equilibrium of the economy with
endowments `ω'`. -/
theorem walrasEqm_of_endowment_transfer {E : ExchangeEconomy ι L} {p : Fin L → ℝ}
    {T : ι → ℝ} {x : ι → Fin L → ℝ} (h : E.IsEqmWithTransfers p T x) (ω' : ι → Fin L → ℝ)
    (hsum : ∑ i, ω' i = ∑ i, E.ω i) (hval : ∀ i, p ⬝ᵥ ω' i = p ⬝ᵥ E.ω i + T i) :
    ({ E with ω := ω' } : ExchangeEconomy ι L).IsWalrasEqm p x := by
  refine ⟨⟨h.1.1, ?_⟩, fun i y hy => h.2.2 i y hy.1 ?_⟩
  · change ∑ i, x i = ∑ i, ω' i
    rw [hsum]
    exact h.1.2
  · rw [← hval i]
    exact hy.2

/-- **Figure 15.B.13(b)** (MWG, p. 525). Under local nonsatiation, moving the endowments directly to
an allocation supported with transfers makes it a Walrasian equilibrium with no trade. -/
theorem walrasEqm_at_allocation {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} {T : ι → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsEqmWithTransfers p T x) :
    ({ E with ω := x } : ExchangeEconomy ι L).IsWalrasEqm p x :=
  walrasEqm_of_endowment_transfer h x h.1.2 fun i => h.wealth_eq hX hlns i

/-- **Footnote 4** (MWG, p. 525). If the endowments are the Pareto optimal allocation `x*` itself
and preferences are strictly convex (Definition 3.B.5), then `x*` is the unique Walrasian
equilibrium allocation. -/
theorem footnote_4_unique {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (utilityPref (E.u i)))
    (hpo : E.IsParetoOptimal E.ω) {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsDemandEqm p x) : x = E.ω := by
  classical
  have hωm : ∀ i, E.ω i ∈ nonnegOrthant L := fun i => hX i ▸ hpo.1.1 i
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1 i
  have hge : ∀ i, E.u i (E.ω i) ≤ E.u i (x i) := fun i => (h.2 i).2 _ ⟨hpo.1.1 i, le_rfl⟩
  have heq : ∀ i, E.u i (x i) = E.u i (E.ω i) := by
    intro i
    refine le_antisymm ?_ (hge i)
    by_contra hlt
    exact hpo.2 ⟨x, h.1, hge, i, not_le.1 hlt⟩
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ E.ω i := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (funext hall)
  set m : ι → Fin L → ℝ := fun k => (1 / 2 : ℝ) • x k + (1 - 1 / 2 : ℝ) • E.ω k with hm
  have hmm : ∀ k, m k ∈ nonnegOrthant L := fun k l => by
    simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hxm k l, hωm k l]
  have hmge : ∀ k, E.u k (E.ω k) ≤ E.u k (m k) := by
    intro k
    by_cases hk : x k = E.ω k
    · simp [hm, hk, ← add_smul]
    · exact (hsc k (E.ω k) (hωm k) (x k) (hxm k) (E.ω k) (hωm k) (heq k).ge le_rfl hk
        (1 / 2) (by norm_num) (by norm_num)).1
  have hmgt : E.u i (E.ω i) < E.u i (m i) :=
    not_le.1 (hsc i (E.ω i) (hωm i) (x i) (hxm i) (E.ω i) (hωm i) (heq i).ge le_rfl hi
      (1 / 2) (by norm_num) (by norm_num)).2
  apply hpo.2
  refine ⟨m, ⟨fun k => hX k ▸ hmm k, ?_⟩, hmge, i, hmgt⟩
  simp only [hm, Finset.sum_add_distrib, ← Finset.smul_sum, h.1.2]
  change (1 / 2 : ℝ) • E.totalEndowment + (1 - 1 / 2 : ℝ) • E.totalEndowment = E.totalEndowment
  rw [← add_smul]
  norm_num

/-- The linear utility `u(x) = x₁ + x₂`. -/
def linearUtility (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- The Edgeworth box economy of `footnote_4_needs_strict_convexity`: both consumers have the
linear utility `x₁ + x₂` and endowment `(1, 1)`. -/
def footnote4Economy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ => linearUtility) (fun _ => ![1, 1])

/-- **Footnote 4** (MWG, p. 525): strict convexity is needed. With linear (convex, not strictly
convex) preferences, the endowment `((1,1),(1,1))` is Pareto optimal, yet `((2,0),(0,2))` is also
a Walrasian equilibrium allocation (at `p = (1, 1)`). -/
theorem footnote_4_needs_strict_convexity :
    footnote4Economy.IsParetoOptimal footnote4Economy.ω ∧
      footnote4Economy.IsDemandEqm ![1, 1] ![![2, 0], ![0, 2]] ∧
      (![![2, 0], ![0, 2]] : Fin 2 → Fin 2 → ℝ) ≠ footnote4Economy.ω := by
  have hsumω : footnote4Economy.totalEndowment = ![2, 2] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, footnote4Economy,
      ExchangeEconomy.ofOrthant]
  refine ⟨⟨⟨fun i l => ?_, rfl⟩, ?_⟩, ⟨⟨fun i l => ?_, ?_⟩, fun i => ⟨⟨fun l => ?_, ?_⟩, ?_⟩⟩, ?_⟩
  · fin_cases l <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant]
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    rw [hsumω] at hs hs1
    simp only [Fin.sum_univ_two, Finset.sum_apply] at hs hs1
    simp only [footnote4Economy, ExchangeEconomy.ofOrthant, linearUtility] at hle hi
    have h0 := hle 0
    have h1 := hle 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 hi hs hs1
    fin_cases i <;> simp at hi <;> linarith
  · fin_cases i <;> fin_cases l <;> simp
  · rw [hsumω]
    funext l
    fin_cases l <;> simp [Fin.sum_univ_two]
  · fin_cases i <;> fin_cases l <;> simp
  · fin_cases i <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant, dotProduct,
      Fin.sum_univ_two] <;> norm_num
  · intro y hy
    have hb := hy.2
    fin_cases i <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant, dotProduct,
      Fin.sum_univ_two, linearUtility] at hb ⊢ <;> norm_num at hb ⊢ <;> linarith
  · intro he
    have := congrFun (congrFun he 0) 1
    simp [footnote4Economy, ExchangeEconomy.ofOrthant] at this

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cobb-Douglas Edgeworth boxes (MWG Example 15.B.1 and Exercise 15.B.2, pp. 519-520, 540)

Consumer `i` has the Cobb-Douglas utility `x_{1i}^{αᵢ} x_{2i}^{1-αᵢ}` (Chapter 3's
`cobbDouglasUtility 1 αᵢ`) and endowment `ωᵢ ≫ 0`.

* `cd_demand_eq`: at `p ≫ 0` consumer `i`'s offer curve is Chapter 3's Cobb-Douglas demand
  (Example 3.D.1) with wealth `p·ωᵢ`; `cd_demand_empty`: no bundle is demanded if some price is
  `≤ 0`.
* **Exercise 15.B.2**: the Walrasian equilibria are exactly the price vectors `p ≫ 0` with
  `p₁/p₂ = (αω₂₁ + βω₂₂)/((1-α)ω₁₁ + (1-β)ω₁₂)` and the demanded allocation (`exercise_15_B_2`);
  comparative statics in `ω₁₁` (`exercise_15_B_2_statics`): the price ratio falls, both consumers
  consume more of good 1, consumer 1 more and consumer 2 less of good 2.
* **Example 15.B.1** (`α = β`, `ω₁ = (1, 2)`, `ω₂ = (2, 1)`): the offer curves, the monotonicity of
  consumer 1's demands in `p₁`, and the equilibrium condition (15.B.2), `p₁/p₂ = α/(1-α)`.
* The offer curve of a Cobb-Douglas consumer passes through his endowment (p. 517), at
  `p = (α/ω₁ᵢ, (1-α)/ω₂ᵢ)` (`cd_endowment_mem_offerCurve`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-- **Exercise 15.B.2** (MWG, p. 540). The Cobb-Douglas Edgeworth box economy with exponents
`α, β` and endowments `ω`. -/
noncomputable def cdEconomy (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![cobbDouglasUtility 1 α, cobbDouglasUtility 1 β] ω

/-- The exponent of consumer `i`. -/
def cdExponent (α β : ℝ) : Fin 2 → ℝ := ![α, β]

theorem cdEconomy_u (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    (cdEconomy α β ω).u i = cobbDouglasUtility 1 (cdExponent α β i) := by
  fin_cases i <;> rfl

/-- A Cobb-Douglas consumer demands nothing when the price of good 1 is `≤ 0`, provided some
affordable bundle has a positive amount of good 2. -/
theorem cd_no_demand_0 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ} (hp : p 0 ≤ 0)
    {w : ℝ} {z : Fin 2 → ℝ} (hz : z ∈ budgetSet p w) (hz1 : 0 < z 1) :
    walrasianDemand (cobbDouglasUtility 1 α) p w = ∅ := by
  have h1 : 0 < 1 - α := by linarith
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hx0 := hx.1.1 0
  have hx1 := hx.1.1 1
  set y : Fin 2 → ℝ := (if 0 < x 1 then x else z) + Pi.single 0 1 with hy
  have hyb : y ∈ budgetSet p w := by
    have hb : (if 0 < x 1 then x else z) ∈ budgetSet p w := by split_ifs; exacts [hx.1, hz]
    refine ⟨fun l => add_nonneg (hb.1 l) (by simp [Pi.single_apply]; split_ifs <;> norm_num),
      ?_⟩
    have : p ⬝ᵥ y = p ⬝ᵥ (if 0 < x 1 then x else z) + p 0 := by simp [hy, dotProduct_add]
    rw [this]
    linarith [hb.2]
  have := hx.2 y hyb
  simp only [cobbDouglasUtility, one_mul, hy, Pi.add_apply] at this
  split_ifs at this with hpos
  · simp only [Pi.single_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have a1 : x 0 ^ α < (x 0 + 1) ^ α := Real.rpow_lt_rpow hx0 (by linarith) hα0
    have a2 : 0 < x 1 ^ (1 - α) := Real.rpow_pos_of_pos hpos _
    nlinarith
  · simp only [Pi.single_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have hx1' : x 1 = 0 := le_antisymm (not_lt.1 hpos) hx1
    rw [hx1', Real.zero_rpow h1.ne', mul_zero] at this
    have a1 : 0 < (z 0 + 1) ^ α := Real.rpow_pos_of_pos (by linarith [hz.1 0]) _
    have a2 : 0 < z 1 ^ (1 - α) := Real.rpow_pos_of_pos hz1 _
    nlinarith [mul_pos a1 a2]

/-- The Cobb-Douglas utility with the goods swapped. -/
theorem cobbDouglas_swap (α : ℝ) (x : Fin 2 → ℝ) :
    cobbDouglasUtility 1 α x = cobbDouglasUtility 1 (1 - α) ![x 1, x 0] := by
  simp [cobbDouglasUtility, mul_comm]

/-- A Cobb-Douglas consumer demands nothing when the price of good 2 is `≤ 0`, provided some
affordable bundle has a positive amount of good 1. -/
theorem cd_no_demand_1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ} (hp : p 1 ≤ 0)
    {w : ℝ} {z : Fin 2 → ℝ} (hz : z ∈ budgetSet p w) (hz0 : 0 < z 0) :
    walrasianDemand (cobbDouglasUtility 1 α) p w = ∅ := by
  have hswap : ∀ v : Fin 2 → ℝ, ![(![v 1, v 0] : Fin 2 → ℝ) 1, ![v 1, v 0] 0] = v := by
    intro v
    funext l
    fin_cases l <;> rfl
  have hdot : ∀ v : Fin 2 → ℝ, (![p 1, p 0] : Fin 2 → ℝ) ⬝ᵥ ![v 1, v 0] = p ⬝ᵥ v := by
    intro v
    simp [dotProduct, Fin.sum_univ_two, add_comm]
  have hz' : (![z 1, z 0] : Fin 2 → ℝ) ∈ budgetSet ![p 1, p 0] w := by
    refine ⟨fun l => ?_, by rw [hdot]; exact hz.2⟩
    fin_cases l
    · exact hz.1 1
    · exact hz.1 0
  have hempty := cd_no_demand_0 (α := 1 - α) (by linarith) (by linarith)
    (p := ![p 1, p 0]) (by simpa using hp) hz' (by simpa using hz0)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hmem : (![x 1, x 0] : Fin 2 → ℝ) ∈ walrasianDemand (cobbDouglasUtility 1 (1 - α))
      ![p 1, p 0] w := by
    refine ⟨⟨fun l => ?_, by rw [hdot]; exact hx.1.2⟩, fun y hy => ?_⟩
    · fin_cases l
      · exact hx.1.1 1
      · exact hx.1.1 0
    · have hy' : (![y 1, y 0] : Fin 2 → ℝ) ∈ budgetSet p w := by
        refine ⟨fun l => ?_, ?_⟩
        · fin_cases l
          · exact hy.1 1
          · exact hy.1 0
        · have := hy.2
          rw [← hdot, hswap]
          exact this
      have h1 := hx.2 _ hy'
      rw [cobbDouglas_swap α, cobbDouglas_swap α x, hswap] at h1
      simpa using h1
  rw [hempty] at hmem
  exact hmem

variable {α β : ℝ} {ω : Fin 2 → Fin 2 → ℝ} {i : Fin 2}

/-- Consumer `i`'s demand in the Cobb-Douglas box at `p ≫ 0` (Example 3.D.1, p. 519): the single
bundle `(αᵢ p·ωᵢ / p₁, (1-αᵢ) p·ωᵢ / p₂)`. -/
theorem cd_demand_eq (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hω : ∀ l, 0 ≤ ω i l) :
    (cdEconomy α β ω).demand i p = {cobbDouglasDemand (cdExponent α β i) p (p ⬝ᵥ ω i)} := by
  have hw : 0 ≤ p ⬝ᵥ ω i := dotProduct_nonneg_of_nonneg (fun l => (hp l).le) hω
  have := example_3_D_1 one_pos hα.1 hα.2 hp hw
  rw [← this]
  unfold ExchangeEconomy.demand
  rw [cdEconomy_u]
  rfl

/-- If some price is `≤ 0`, a Cobb-Douglas consumer with `ωᵢ ≫ 0` demands nothing. -/
theorem cd_demand_empty (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1) {p : Fin 2 → ℝ}
    (hp : ¬ StrictlyPositive p) (hω : ∀ l, 0 < ω i l) : (cdEconomy α β ω).demand i p = ∅ := by
  have hb : ω i ∈ budgetSet p (p ⬝ᵥ ω i) := ⟨fun l => (hω l).le, le_rfl⟩
  have heq : (cdEconomy α β ω).demand i p =
      walrasianDemand (cobbDouglasUtility 1 (cdExponent α β i)) p (p ⬝ᵥ ω i) := by
    unfold ExchangeEconomy.demand
    rw [cdEconomy_u]
    rfl
  rw [heq]
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · exact cd_no_demand_0 hα.1 hα.2 hl hb (hω 1)
  · exact cd_no_demand_1 hα.1 hα.2 hl hb (hω 0)

/-- The equilibrium allocation of the Cobb-Douglas box at prices `p`. -/
noncomputable def cdAllocation (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i => cobbDouglasDemand (cdExponent α β i) p (p ⬝ᵥ ω i)

/-- **Exercise 15.B.2** (MWG, p. 540). In the Cobb-Douglas Edgeworth box with `α, β ∈ (0, 1)` and
`ωᵢ ≫ 0`, `(p, x)` is a Walrasian equilibrium if and only if `p ≫ 0`,
`p₁ ((1-α)ω₁₁ + (1-β)ω₁₂) = p₂ (αω₂₁ + βω₂₂)` and `x` is the demanded allocation. Hence the
equilibrium price ratio and allocation are unique. -/
theorem exercise_15_B_2 (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hω : ∀ i l, 0 < ω i l) (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (cdEconomy α β ω).IsDemandEqm p x ↔ StrictlyPositive p ∧
      p 0 * ((1 - α) * ω 0 0 + (1 - β) * ω 1 0) = p 1 * (α * ω 0 1 + β * ω 1 1) ∧
      x = cdAllocation α β ω p := by
  have hex : ∀ i, 0 < cdExponent α β i ∧ cdExponent α β i < 1 := by
    intro i
    fin_cases i
    · exact ⟨hα0, hα1⟩
    · exact ⟨hβ0, hβ1⟩
  have htot : ∀ l, (cdEconomy α β ω).totalEndowment l = ω 0 l + ω 1 l := by
    intro l
    simp [ExchangeEconomy.totalEndowment, cdEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two]
  constructor
  · rintro ⟨hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      have := hd 0
      rw [cd_demand_empty (hex 0) hp (hω 0)] at this
      exact this
    have hx : x = cdAllocation α β ω p := by
      funext i
      have := hd i
      rw [cd_demand_eq (hex i) hp fun l => (hω i l).le] at this
      exact this
    refine ⟨hp, ?_, hx⟩
    have h1 := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx] at h1
    simp only [cdAllocation, cobbDouglasDemand, cdExponent, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have hp0 := (hp 0).ne'
    field_simp at h1
    linarith
  · rintro ⟨hp, hrel, rfl⟩
    have hd : ∀ i, cdAllocation α β ω p i ∈ (cdEconomy α β ω).demand i p := by
      intro i
      rw [cd_demand_eq (hex i) hp fun l => (hω i l).le]
      rfl
    refine exercise_15_B_1b (fun i => rfl) (fun i => ?_) hp hd ?_
    · rw [cdEconomy_u]
      exact cobbDouglas_lns (hex i).1 (hex i).2
    · rw [htot, Fin.sum_univ_two]
      simp only [cdAllocation, cobbDouglasDemand, cdExponent, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      have hp0 := (hp 0).ne'
      field_simp
      linarith

/-- The equilibrium price ratio `p₁/p₂` of Exercise 15.B.2 as a function of `ω₁₁`. -/
noncomputable def cdPriceRatio (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (a : ℝ) : ℝ :=
  (α * ω 0 1 + β * ω 1 1) / ((1 - α) * a + (1 - β) * ω 1 0)

/-- **Exercise 15.B.2** (MWG, p. 540), comparative statics. With `p₂ = 1` and `q(ω₁₁)` the
equilibrium price of good 1, a differential increase in `ω₁₁` lowers `q`, raises both consumers'
consumption of good 1 (`x₁₁ = α(ω₁₁ + ω₂₁/q)`, `x₁₂ = β(ω₁₂ + ω₂₂/q)`), raises consumer 1's and
lowers consumer 2's consumption of good 2 (`x₂₁ = (1-α)(qω₁₁ + ω₂₁)`, `x₂₂ = (1-β)(qω₁₂ + ω₂₂)`). -/
theorem exercise_15_B_2_statics (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hω : ∀ i l, 0 < ω i l) {a : ℝ} (ha : 0 < a) :
    ∃ q' x11' x21' x12' x22' : ℝ, HasDerivAt (cdPriceRatio α β ω) q' a ∧ q' < 0 ∧
      HasDerivAt (fun t => α * (t + ω 0 1 / cdPriceRatio α β ω t)) x11' a ∧ 0 < x11' ∧
      HasDerivAt (fun t => (1 - α) * (cdPriceRatio α β ω t * t + ω 0 1)) x21' a ∧ 0 < x21' ∧
      HasDerivAt (fun t => β * (ω 1 0 + ω 1 1 / cdPriceRatio α β ω t)) x12' a ∧ 0 < x12' ∧
      HasDerivAt (fun t => (1 - β) * (cdPriceRatio α β ω t * ω 1 0 + ω 1 1)) x22' a ∧
        x22' < 0 := by
  set N := α * ω 0 1 + β * ω 1 1 with hN
  set D := (1 - α) * a + (1 - β) * ω 1 0 with hD
  have hN0 : 0 < N := by nlinarith [hω 0 1, hω 1 1]
  have hD0 : 0 < D := by nlinarith [hω 1 0]
  have hDf : HasDerivAt (fun t => (1 - α) * t + (1 - β) * ω 1 0) (1 - α) a := by
    simpa using ((hasDerivAt_id a).const_mul (1 - α)).add_const ((1 - β) * ω 1 0)
  have hq : HasDerivAt (cdPriceRatio α β ω) (-(N * (1 - α)) / D ^ 2) a := by
    have := (hasDerivAt_const a N).div hDf hD0.ne'
    have h2 : cdPriceRatio α β ω = (fun _ => N) / fun t => (1 - α) * t + (1 - β) * ω 1 0 := by
      funext t
      simp [cdPriceRatio, hN]
    rw [h2]
    convert this using 1
    simp [hD]
  set q := N / D with hqdef
  have hqa : cdPriceRatio α β ω a = q := rfl
  have hq0 : 0 < q := div_pos hN0 hD0
  have hinv : HasDerivAt (fun t => (cdPriceRatio α β ω t)⁻¹) (-(-(N * (1 - α)) / D ^ 2) / q ^ 2)
      a := by
    have := hq.inv (by rw [hqa]; exact hq0.ne')
    rw [hqa] at this
    exact this
  set r := -(-(N * (1 - α)) / D ^ 2) / q ^ 2 with hr
  have hr0 : 0 < r := by
    rw [hr, neg_div (D ^ 2), neg_neg]
    have : 0 < 1 - α := by linarith
    positivity
  have hq'0 : -(N * (1 - α)) / D ^ 2 < 0 := by
    have : 0 < 1 - α := by linarith
    have : 0 < N * (1 - α) / D ^ 2 := by positivity
    rw [neg_div]
    linarith
  have d11 : HasDerivAt (fun t => α * (t + ω 0 1 / cdPriceRatio α β ω t))
      (α * (1 + ω 0 1 * r)) a := by
    have := ((hasDerivAt_id a).add (hinv.const_mul (ω 0 1))).const_mul α
    convert this using 1
    funext t
    simp [div_eq_mul_inv]
  have d21 : HasDerivAt (fun t => (1 - α) * (cdPriceRatio α β ω t * t + ω 0 1))
      ((1 - α) * (-(N * (1 - α)) / D ^ 2 * a + q)) a := by
    have := ((hq.mul (hasDerivAt_id a)).add_const (ω 0 1)).const_mul (1 - α)
    convert this using 1
    · funext t
      simp [id]
    · rw [hqa]
      simp [id]
  have d12 : HasDerivAt (fun t => β * (ω 1 0 + ω 1 1 / cdPriceRatio α β ω t))
      (β * (ω 1 1 * r)) a := by
    have := ((hinv.const_mul (ω 1 1)).const_add (ω 1 0)).const_mul β
    convert this using 1
    funext t
    simp [div_eq_mul_inv]
  have d22 : HasDerivAt (fun t => (1 - β) * (cdPriceRatio α β ω t * ω 1 0 + ω 1 1))
      ((1 - β) * (-(N * (1 - α)) / D ^ 2 * ω 1 0)) a :=
    ((hq.mul_const (ω 1 0)).add_const (ω 1 1)).const_mul (1 - β)
  refine ⟨_, _, _, _, _, hq, hq'0, d11, ?_, d21, ?_, d12, ?_, d22, ?_⟩
  · have h01 := hω 0 1
    nlinarith [mul_pos h01 hr0]
  · rw [hqdef]
    have h10 := hω 1 0
    have key : -(N * (1 - α)) / D ^ 2 * a + N / D = N * ((1 - β) * ω 1 0) / D ^ 2 := by
      field_simp
      rw [hD]
      ring
    rw [key]
    have h1a : 0 < 1 - α := by linarith
    have h1b : 0 < 1 - β := by linarith
    have : 0 < N * ((1 - β) * ω 1 0) / D ^ 2 := by positivity
    nlinarith
  · have h11 := hω 1 1
    nlinarith [mul_pos h11 hr0]
  · have h10 := hω 1 0
    have h1b : 0 < 1 - β := by linarith
    nlinarith [mul_pos h1b h10]

/-- **Example 15.B.1** (MWG, p. 519): equal exponents `α` and endowments `ω₁ = (1, 2)`,
`ω₂ = (2, 1)`. -/
def example15B1Endowment : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

/-- **Example 15.B.1** (MWG, p. 519). At `p ≫ 0` consumer 1's offer curve is
`OC₁(p) = (α(p₁ + 2p₂)/p₁, (1-α)(p₁ + 2p₂)/p₂)` and consumer 2's is
`OC₂(p) = (α(2p₁ + p₂)/p₁, (1-α)(2p₁ + p₂)/p₂)` (p. 520). -/
theorem example_15_B_1_offerCurves (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) :
    (cdEconomy α α example15B1Endowment).demand 0 p =
        {![α * (p 0 + 2 * p 1) / p 0, (1 - α) * (p 0 + 2 * p 1) / p 1]} ∧
      (cdEconomy α α example15B1Endowment).demand 1 p =
        {![α * (2 * p 0 + p 1) / p 0, (1 - α) * (2 * p 0 + p 1) / p 1]} := by
  constructor
  · rw [cd_demand_eq (i := 0) ⟨hα0, hα1⟩ hp
      (fun l => by fin_cases l <;> norm_num [example15B1Endowment])]
    congr 1
    funext l
    fin_cases l <;> simp [cobbDouglasDemand, cdExponent, example15B1Endowment, dotProduct,
      Fin.sum_univ_two, mul_comm]
  · rw [cd_demand_eq (i := 1) ⟨hα0, hα1⟩ hp
      (fun l => by fin_cases l <;> norm_num [example15B1Endowment])]
    congr 1
    funext l
    fin_cases l <;> simp [cobbDouglasDemand, cdExponent, example15B1Endowment, dotProduct,
      Fin.sum_univ_two, mul_comm]

/-- **Example 15.B.1** (MWG, p. 520). Consumer 1's demand for good 1, `α(p₁ + 2p₂)/p₁`, is strictly
decreasing and his demand for good 2, `(1-α)(p₁ + 2p₂)/p₂`, strictly increasing in `p₁`
(for fixed `p₂ > 0`). -/
theorem example_15_B_1_monotone (hα0 : 0 < α) (hα1 : α < 1) {p₂ : ℝ} (hp₂ : 0 < p₂) :
    StrictAntiOn (fun p₁ => α * (p₁ + 2 * p₂) / p₁) (Set.Ioi 0) ∧
      StrictMonoOn (fun p₁ => (1 - α) * (p₁ + 2 * p₂) / p₂) (Set.Ioi 0) := by
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    simp only
    rw [div_lt_div_iff₀ hb ha]
    nlinarith [mul_pos hα0 hp₂]
  · intro a _ b _ hab
    simp only
    rw [div_lt_div_iff_of_pos_right hp₂]
    nlinarith

/-- **Example 15.B.1** (MWG, p. 520), equation (15.B.2): the Walrasian equilibria are exactly the
prices `p ≫ 0` with `p₁/p₂ = α/(1-α)`, i.e. `p₁(1-α) = p₂α`, with the demanded allocation. -/
theorem example_15_B_1 (hα0 : 0 < α) (hα1 : α < 1) (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (cdEconomy α α example15B1Endowment).IsDemandEqm p x ↔
      StrictlyPositive p ∧ p 0 * (1 - α) = p 1 * α ∧
        x = cdAllocation α α example15B1Endowment p := by
  rw [exercise_15_B_2 hα0 hα1 hα0 hα1 (fun i l => by
    fin_cases i <;> fin_cases l <;> norm_num [example15B1Endowment])]
  have e : ∀ q : ℝ, (q * ((1 - α) * example15B1Endowment 0 0 + (1 - α) *
      example15B1Endowment 1 0) = p 1 * (α * example15B1Endowment 0 1 + α *
      example15B1Endowment 1 1)) ↔ q * (1 - α) = p 1 * α := by
    intro q
    simp only [example15B1Endowment, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith
  rw [e]

/-- **Section 15.B** (MWG, p. 517), for Cobb-Douglas consumers: the offer curve of consumer `i`
(with `ωᵢ ≫ 0`) passes through his endowment, which is demanded at `p = (αᵢ/ω₁ᵢ, (1-αᵢ)/ω₂ᵢ)`. -/
theorem cd_endowment_mem_offerCurve (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1)
    (hω : ∀ l, 0 < ω i l) : ω i ∈ (cdEconomy α β ω).offerCurve i := by
  set a := cdExponent α β i
  set p : Fin 2 → ℝ := ![a / ω i 0, (1 - a) / ω i 1] with hp
  have hpp : StrictlyPositive p := by
    intro l
    have : 0 < 1 - a := by linarith [hα.2]
    fin_cases l
    · exact div_pos hα.1 (hω 0)
    · exact div_pos this (hω 1)
  refine ⟨p, hpp, ?_⟩
  rw [cd_demand_eq hα hpp fun l => (hω l).le]
  have hw : p ⬝ᵥ ω i = 1 := by
    simp only [hp, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [(hω 0).ne', (hω 1).ne']
    ring
  rw [Set.mem_singleton_iff, hw]
  have h1a : 0 < 1 - a := by linarith [hα.2]
  funext l
  fin_cases l
  · change ω i 0 = a * 1 / (a / ω i 0)
    field_simp [(hω 0).ne', hα.1.ne']
  · change ω i 1 = (1 - a) * 1 / ((1 - a) / ω i 1)
    field_simp [(hω 1).ne', h1a.ne']

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Multiple Walrasian equilibria (MWG Example 15.B.2 and Exercise 15.B.5, pp. 521-522, 541)

The utilities are `u₁ = x₁₁ - x₂₁⁻⁸/8` and `u₂ = -x₁₂⁻⁸/8 + x₂₂`, quasilinear with respect to
different numeraires, and the endowments are `ω₁ = (2, r)`, `ω₂ = (r, 2)` with
`r = 2^{8/9} - 2^{1/9}`. Since `x⁻⁸ → ∞` as `x → 0`, utility is `-∞` on the face where the
non-numeraire good is zero; we model this by the consumption sets
`X₁ = {x : x₁ ≥ 0, x₂ > 0}` and `X₂ = {x : x₁ > 0, x₂ ≥ 0}` (the bundles of `ℝ²₊` with finite
utility).

* `ql8_optimal`: the demand of a consumer with utility `x_n - x_o⁻⁸/8` (prices `p_n, p_o > 0`): the
  unique optimum has `x_o = t` with `p_o t⁹ = p_n`.
* **Exercise 15.B.5**: the offer curves are as printed (`exercise_15_B_5_offerCurves`, with the
  book's `rpow` formulas in `exercise_15_B_5_printed`), they are strictly positive, and the
  equilibrium price ratios are exactly `p₁/p₂ ∈ {1/2, 1, 2}` (`example_15_B_2`): the market
  clearing equation `r t⁹ - t⁸ + t - r = 0` (`t⁹ = p₁/p₂`) has exactly the positive roots
  `1, 2^{1/9}, 2^{-1/9}` (`ex15B2_roots`).
* Consumer 1's demand for good 1 may increase with `p₁` (`example_15_B_2_increasing`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The key inequality `t⁹ - 9 t s⁸ + 8 s⁹ = (s - t)² ∑_{k=0}^{7} (k+1) s^k t^{7-k} ≥ 0`. -/
theorem ql8_poly (s t : ℝ) : t ^ 9 - 9 * t * s ^ 8 + 8 * s ^ 9 = (s - t) ^ 2 *
    (t ^ 7 + 2 * s * t ^ 6 + 3 * s ^ 2 * t ^ 5 + 4 * s ^ 3 * t ^ 4 + 5 * s ^ 4 * t ^ 3 +
      6 * s ^ 5 * t ^ 2 + 7 * s ^ 6 * t + 8 * s ^ 7) := by
  ring

/-- **Exercise 15.B.5** (MWG, p. 541), the demand computation. A consumer with utility
`x_n - x_o⁻⁸/8` on `{x_n ≥ 0, x_o > 0}`, prices `p_n, p_o > 0` and wealth `w`: if `t > 0` solves the
first-order condition `p_o t⁹ = p_n`, every affordable bundle gives at most the utility of
`((w - p_o t)/p_n, t)`, with equality only at that bundle. -/
theorem ql8_optimal {pn po w t : ℝ} (hpn : 0 < pn) (hpo : 0 < po) (ht : 0 < t)
    (hfoc : po * t ^ 9 = pn) {xn xo : ℝ} (hxo : 0 < xo) (hb : pn * xn + po * xo ≤ w) :
    xn - 1 / (8 * xo ^ 8) ≤ (w - po * t) / pn - 1 / (8 * t ^ 8) ∧
      (xn - 1 / (8 * xo ^ 8) = (w - po * t) / pn - 1 / (8 * t ^ 8) →
        xo = t ∧ xn = (w - po * t) / pn) := by
  have hS : 0 < t ^ 7 + 2 * xo * t ^ 6 + 3 * xo ^ 2 * t ^ 5 + 4 * xo ^ 3 * t ^ 4 +
      5 * xo ^ 4 * t ^ 3 + 6 * xo ^ 5 * t ^ 2 + 7 * xo ^ 6 * t + 8 * xo ^ 7 := by positivity
  have hxn : xn ≤ (w - po * xo) / pn := by
    rw [le_div_iff₀ hpn]
    linarith
  -- the reduced inequality `po (t - xo)/pn ≤ 1/(8 xo⁸) - 1/(8 t⁸)`
  have key : po * (t - xo) / pn ≤ 1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8) := by
    rw [← hfoc]
    have h1 : 0 ≤ t ^ 9 - 9 * t * xo ^ 8 + 8 * xo ^ 9 := by
      rw [ql8_poly]
      positivity
    rw [div_le_iff₀ (by positivity)]
    have e : (1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8)) * (po * t ^ 9) =
        po * (t ^ 9 - t * xo ^ 8) / (8 * xo ^ 8) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hpo.le h1]
  have hsplit : (w - po * xo) / pn - (w - po * t) / pn = po * (t - xo) / pn := by
    field_simp
    ring
  refine ⟨by linarith, fun heq => ?_⟩
  have hxo' : xo = t := by
    by_contra hne
    have h2 : 0 < t ^ 9 - 9 * t * xo ^ 8 + 8 * xo ^ 9 := by
      rw [ql8_poly]
      exact mul_pos (pow_pos (sub_ne_zero.2 hne |> fun h => abs_pos.2 h |>
        fun h => by simpa [sq_abs] using pow_pos h 2) 1 |> fun h => by simpa using h) hS
    have key' : po * (t - xo) / pn < 1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8) := by
      rw [← hfoc, div_lt_iff₀ (by positivity)]
      have e : (1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8)) * (po * t ^ 9) =
          po * (t ^ 9 - t * xo ^ 8) / (8 * xo ^ 8) := by
        field_simp
      rw [e, lt_div_iff₀ (by positivity)]
      nlinarith [mul_pos hpo h2]
    linarith
  refine ⟨hxo', ?_⟩
  subst hxo'
  linarith

/-- The number `a = 2^{1/9}`. -/
noncomputable def ex15B2a : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 9)

/-- **Example 15.B.2** (MWG, p. 521). The number `r = 2^{8/9} - 2^{1/9}`. -/
noncomputable def ex15B2r : ℝ := (2 : ℝ) ^ ((8 : ℝ) / 9) - (2 : ℝ) ^ ((1 : ℝ) / 9)

theorem ex15B2a_pow : ex15B2a ^ 9 = 2 := by
  rw [ex15B2a, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem ex15B2r_eq : ex15B2r = ex15B2a ^ 8 - ex15B2a := by
  rw [ex15B2r, ex15B2a, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem ex15B2a_bounds : 1.08 < ex15B2a ∧ ex15B2a < 1.081 := by
  have h := ex15B2a_pow
  have hpos : 0 < ex15B2a := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · by_contra hle
    rw [not_lt] at hle
    have : ex15B2a ^ 9 ≤ (1.08 : ℝ) ^ 9 := pow_le_pow_left₀ hpos.le hle 9
    norm_num at this
    linarith
  · by_contra hle
    rw [not_lt] at hle
    have : (1.081 : ℝ) ^ 9 ≤ ex15B2a ^ 9 := pow_le_pow_left₀ (by norm_num) hle 9
    norm_num at this
    linarith

/-- **Example 15.B.2** (MWG, p. 521): `r > 0`; in fact `0.769 < r`. -/
theorem ex15B2r_bounds : 0.769 < ex15B2r := by
  rw [ex15B2r_eq]
  obtain ⟨h1, h2⟩ := ex15B2a_bounds
  have h9 := ex15B2a_pow
  have hpos : 0 < ex15B2a := by linarith
  have h8 : ex15B2a ^ 8 = 2 / ex15B2a := by
    rw [eq_div_iff hpos.ne', ← h9]
    ring
  rw [h8, lt_sub_iff_add_lt, lt_div_iff₀ hpos]
  nlinarith

/-- **Example 15.B.2** (MWG, p. 521). The economy: consumption sets `X₁ = {x₁₁ ≥ 0, x₂₁ > 0}`,
`X₂ = {x₁₂ > 0, x₂₂ ≥ 0}`, utilities `x₁₁ - x₂₁⁻⁸/8` and `-x₁₂⁻⁸/8 + x₂₂`, endowments `(2, r)` and
`(r, 2)`. -/
noncomputable def ex15B2Economy : EdgeworthEconomy where
  X := ![{x | 0 ≤ x 0 ∧ 0 < x 1}, {x | 0 < x 0 ∧ 0 ≤ x 1}]
  u := ![fun x => x 0 - 1 / (8 * x 1 ^ 8), fun x => -(1 / (8 * x 0 ^ 8)) + x 1]
  ω := ![![2, ex15B2r], ![ex15B2r, 2]]

/-- The positivity behind `OCᵢ ≫ 0`: `2s⁹ - s + r > 0` for `s ≥ 0`. -/
theorem ex15B2_pos_aux {s : ℝ} (hs : 0 ≤ s) : 0 < 2 * s ^ 9 - s + ex15B2r := by
  have hr := ex15B2r_bounds
  -- the tangent inequality for `s⁹` at `7/10`
  have h := ql8_poly (7 / 10) s
  have hS : 0 ≤ s ^ 7 + 2 * (7 / 10) * s ^ 6 + 3 * (7 / 10) ^ 2 * s ^ 5 +
      4 * (7 / 10) ^ 3 * s ^ 4 + 5 * (7 / 10) ^ 4 * s ^ 3 + 6 * (7 / 10) ^ 5 * s ^ 2 +
      7 * (7 / 10) ^ 6 * s + 8 * (7 / 10 : ℝ) ^ 7 := by positivity
  have h2 : 0 ≤ s ^ 9 - 9 * s * (7 / 10) ^ 8 + 8 * (7 / 10 : ℝ) ^ 9 := by
    rw [h]
    positivity
  norm_num at h2
  nlinarith

/-- The offer curve of consumer 1 at `p ≫ 0`, in terms of `t > 0` with `t⁹ = p₁/p₂`:
`(2 + r/t⁹ - 1/t⁸, t)`. -/
noncomputable def ex15B2OC1 (t : ℝ) : Fin 2 → ℝ :=
  ![2 + ex15B2r / t ^ 9 - 1 / t ^ 8, t]

/-- The offer curve of consumer 2 at `p ≫ 0` (`t⁹ = p₁/p₂`): `(1/t, 2 + r t⁹ - t⁸)`. -/
noncomputable def ex15B2OC2 (t : ℝ) : Fin 2 → ℝ :=
  ![1 / t, 2 + ex15B2r * t ^ 9 - t ^ 8]

/-- **Exercise 15.B.5** (MWG, p. 541). At `p ≫ 0`, with `t > 0` and `t⁹ = p₁/p₂`, consumer 1
demands exactly `(2 + r/t⁹ - 1/t⁸, t)` and consumer 2 exactly `(1/t, 2 + r t⁹ - t⁸)`; both bundles
are strictly positive. -/
theorem exercise_15_B_5_offerCurves {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {t : ℝ}
    (ht : 0 < t) (ht9 : t ^ 9 = p 0 / p 1) :
    ex15B2Economy.demand 0 p = {ex15B2OC1 t} ∧ ex15B2Economy.demand 1 p = {ex15B2OC2 t} ∧
      (∀ l, 0 < ex15B2OC1 t l) ∧ ∀ l, 0 < ex15B2OC2 t l := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hr := ex15B2r_bounds
  have hpos1 : 0 < 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 := by
    have := ex15B2_pos_aux ht.le
    have e : 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 = (2 * t ^ 9 - t + ex15B2r) / t ^ 9 := by
      field_simp
      ring
    rw [e]
    positivity
  have hpos2 : 0 < 2 + ex15B2r * t ^ 9 - t ^ 8 := by
    have := ex15B2_pos_aux (inv_pos.2 ht).le
    have e : 2 + ex15B2r * t ^ 9 - t ^ 8 = (2 * t⁻¹ ^ 9 - t⁻¹ + ex15B2r) * t ^ 9 := by
      field_simp
      ring
    rw [e]
    positivity
  have hfoc1 : p 1 * t ^ 9 = p 0 := by rw [ht9]; field_simp
  have hfoc2 : p 0 * (1 / t) ^ 9 = p 1 := by
    rw [div_pow, one_pow, ht9]
    field_simp
  have hw1 : p ⬝ᵥ ex15B2Economy.ω 0 = 2 * p 0 + ex15B2r * p 1 := by
    simp [ex15B2Economy, dotProduct, Fin.sum_univ_two, mul_comm]
  have hw2 : p ⬝ᵥ ex15B2Economy.ω 1 = ex15B2r * p 0 + 2 * p 1 := by
    simp [ex15B2Economy, dotProduct, Fin.sum_univ_two, mul_comm]
  have hx1 : (2 * p 0 + ex15B2r * p 1 - p 1 * t) / p 0 = 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 := by
    rw [← hfoc1]
    field_simp
  have hx2 : (ex15B2r * p 0 + 2 * p 1 - p 0 * (1 / t)) / p 1 = 2 + ex15B2r * t ^ 9 - t ^ 8 := by
    rw [← hfoc2]
    field_simp
    ring
  refine ⟨?_, ?_, fun l => ?_, fun l => ?_⟩
  · ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 0 * y 0 + p 1 * y 1 ≤ 2 * p 0 + ex15B2r * p 1 := by
        rw [← hw1]
        simpa [dotProduct, Fin.sum_univ_two] using hb
      have hy' : y 0 ≥ 0 ∧ 0 < y 1 := hy
      have hopt := ql8_optimal hp0 hp1 ht hfoc1 hy'.2 hb'
      have hmem : ex15B2OC1 t ∈ budgetSetOn (ex15B2Economy.X 0) p
          (p ⬝ᵥ ex15B2Economy.ω 0) := by
        refine ⟨⟨hpos1.le, ht⟩, ?_⟩
        rw [hw1]
        simp only [ex15B2OC1, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx1, mul_div_cancel₀ _ hp0.ne']
        linarith
      have h2 := hmax _ hmem
      simp only [ex15B2Economy, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx1] at h2
      have := hopt.2 (le_antisymm hopt.1 h2)
      have e0 : y 0 = ex15B2OC1 t 0 := this.2.trans hx1
      have e1 : y 1 = ex15B2OC1 t 1 := this.1
      funext l
      fin_cases l
      exacts [e0, e1]
    · rintro rfl
      refine ⟨⟨⟨hpos1.le, ht⟩, ?_⟩, fun y hy => ?_⟩
      · rw [hw1]
        simp only [ex15B2OC1, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx1]
        field_simp
        linarith
      · have hb' : p 0 * y 0 + p 1 * y 1 ≤ 2 * p 0 + ex15B2r * p 1 := by
          rw [← hw1]
          simpa [dotProduct, Fin.sum_univ_two] using hy.2
        have := (ql8_optimal hp0 hp1 ht hfoc1 hy.1.2 hb').1
        simp only [ex15B2Economy, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hx1]
        exact this
  · ext y
    simp only [Set.mem_singleton_iff]
    have hti : 0 < 1 / t := one_div_pos.2 ht
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 1 * y 1 + p 0 * y 0 ≤ ex15B2r * p 0 + 2 * p 1 := by
        rw [hw2] at hb
        simp only [dotProduct, Fin.sum_univ_two] at hb
        linarith
      have hy' : 0 < y 0 ∧ 0 ≤ y 1 := hy
      have hopt := ql8_optimal hp1 hp0 hti hfoc2 hy'.1 hb'
      have hmem : ex15B2OC2 t ∈ budgetSetOn (ex15B2Economy.X 1) p
          (p ⬝ᵥ ex15B2Economy.ω 1) := by
        refine ⟨⟨hti, hpos2.le⟩, ?_⟩
        rw [hw2]
        simp only [ex15B2OC2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx2, mul_div_cancel₀ _ hp1.ne']
        linarith
      have h2 := hmax _ hmem
      simp only [ex15B2Economy, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx2] at h2
      have := hopt.2 (by linarith [hopt.1])
      have e0 : y 0 = ex15B2OC2 t 0 := this.1
      have e1 : y 1 = ex15B2OC2 t 1 := this.2.trans hx2
      funext l
      fin_cases l
      exacts [e0, e1]
    · rintro rfl
      refine ⟨⟨⟨hti, hpos2.le⟩, ?_⟩, fun y hy => ?_⟩
      · rw [hw2]
        simp only [ex15B2OC2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx2]
        field_simp
        linarith
      · have hb' : p 1 * y 1 + p 0 * y 0 ≤ ex15B2r * p 0 + 2 * p 1 := by
          have := hy.2
          rw [hw2] at this
          simp only [dotProduct, Fin.sum_univ_two] at this
          linarith
        have := (ql8_optimal hp1 hp0 hti hfoc2 hy.1.1 hb').1
        simp only [ex15B2Economy, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hx2]
        linarith
  · fin_cases l
    · exact hpos1
    · exact ht
  · fin_cases l
    · exact one_div_pos.2 ht
    · exact hpos2

/-- The market-clearing polynomial `P(t) = r t⁹ - t⁸ + t - r` factors as
`(t - 1)(t - a)(t - 1/a) Q(t)` with `a = 2^{1/9}` and `Q` having positive coefficients. -/
theorem ex15B2_factor (t : ℝ) : ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r =
    (t - 1) * (t - ex15B2a) * (t - ex15B2a ^ 8 / 2) *
      ((ex15B2a ^ 8 - ex15B2a) * t ^ 6 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 - ex15B2a ^ 2 - ex15B2a) * t ^ 5 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 - ex15B2a ^ 3 - ex15B2a ^ 2 - ex15B2a) * t ^ 4 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 + ex15B2a ^ 5 - ex15B2a ^ 4 - ex15B2a ^ 3 -
          ex15B2a ^ 2 - ex15B2a) * t ^ 3 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 - ex15B2a ^ 3 - ex15B2a ^ 2 - ex15B2a) * t ^ 2 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 - ex15B2a ^ 2 - ex15B2a) * t + (ex15B2a ^ 8 - ex15B2a)) := by
  rw [ex15B2r_eq]
  set a := ex15B2a
  linear_combination ((-1/2) * a + (1/2) * a ^ 8 + (-1/2) * t + (-1/2) * t * a ^ 2 +
    (1/2) * t ^ 2 * a + (-1/2) * t ^ 2 * a ^ 3 + (1/2) * t ^ 3 * a ^ 2 + (-1/2) * t ^ 3 * a ^ 4 +
    (1/2) * t ^ 4 * a ^ 3 + (-1/2) * t ^ 4 * a ^ 5 + (1/2) * t ^ 5 * a ^ 4 +
    (-1/2) * t ^ 5 * a ^ 6 + (1/2) * t ^ 6 * a ^ 5 + (-1/2) * t ^ 6 * a ^ 7 +
    (1/2) * t ^ 7 * a ^ 6 + (-1/2) * t ^ 7 * a ^ 8 + (1/2) * t ^ 8 + (1/2) * t ^ 8 * a ^ 7) *
    ex15B2a_pow

/-- **Example 15.B.2** (MWG, p. 522; Exercise 15.B.5). The positive roots of the market-clearing
equation `r t⁹ - t⁸ + t - r = 0` are exactly `t = 1`, `t = 2^{1/9}` and `t = 2^{-1/9}`
(`2^{-1/9} = 2^{8/9}/2`). -/
theorem ex15B2_roots {t : ℝ} (ht : 0 < t) :
    ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 ↔
      t = 1 ∨ t = ex15B2a ∨ t = ex15B2a ^ 8 / 2 := by
  have ha := ex15B2a_bounds
  have ha1 : 1 < ex15B2a := by linarith [ha.1]
  rw [ex15B2_factor]
  set a := ex15B2a
  have hp : ∀ k m : ℕ, k < m → a ^ k < a ^ m := fun k m h => pow_lt_pow_right₀ ha1 h
  have q6 : 0 < a ^ 8 - a := by have := hp 1 8 (by norm_num); simp at this; linarith
  have q5 : 0 < a ^ 8 + a ^ 7 - a ^ 2 - a := by
    have := hp 2 7 (by norm_num); linarith
  have q4 : 0 < a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a := by
    have := hp 3 6 (by norm_num); linarith
  have q3 : 0 < a ^ 8 + a ^ 7 + a ^ 6 + a ^ 5 - a ^ 4 - a ^ 3 - a ^ 2 - a := by
    have := hp 4 5 (by norm_num); linarith
  have hQ : 0 < (a ^ 8 - a) * t ^ 6 + (a ^ 8 + a ^ 7 - a ^ 2 - a) * t ^ 5 +
      (a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a) * t ^ 4 +
      (a ^ 8 + a ^ 7 + a ^ 6 + a ^ 5 - a ^ 4 - a ^ 3 - a ^ 2 - a) * t ^ 3 +
      (a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a) * t ^ 2 + (a ^ 8 + a ^ 7 - a ^ 2 - a) * t +
      (a ^ 8 - a) := by positivity
  rw [mul_eq_zero, or_iff_left hQ.ne', mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    sub_eq_zero]
  tauto

/-- `2^{-1/9}` in the form `2^{8/9}/2`: `(2^{8/9}/2)⁹ = 1/2`. -/
theorem ex15B2a_inv_pow : (ex15B2a ^ 8 / 2) ^ 9 = 1 / 2 := by
  have h := ex15B2a_pow
  have : (ex15B2a ^ 8 / 2) ^ 9 = (ex15B2a ^ 9) ^ 8 / 2 ^ 9 := by ring
  rw [this, h]
  norm_num

/-- Equilibrium prices have `p ≫ 0` in Example 15.B.2: if a price is `≤ 0`, consumer 1 (if
`p₁ ≤ 0`) or consumer 1 (if `p₂ ≤ 0`, via good 2) demands nothing. -/
theorem ex15B2_demand0_empty {p : Fin 2 → ℝ} (hp : ¬ StrictlyPositive p) :
    ex15B2Economy.demand 0 p = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hy, hb⟩, hmax⟩
  have hy' : 0 ≤ y 0 ∧ 0 < y 1 := hy
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · -- more of good 1 is affordable and better
    have hmem : y + Pi.single 0 1 ∈ budgetSetOn (ex15B2Economy.X 0) p
        (p ⬝ᵥ ex15B2Economy.ω 0) := by
      refine ⟨⟨by simp; linarith [hy'.1], by simpa using hy'.2⟩, ?_⟩
      rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      simp at hl
      linarith
    have := hmax _ hmem
    simp only [ex15B2Economy, Matrix.cons_val_zero, Pi.add_apply, Pi.single_eq_same] at this
    simp only [ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    linarith
  · have hmem : y + Pi.single 1 1 ∈ budgetSetOn (ex15B2Economy.X 0) p
        (p ⬝ᵥ ex15B2Economy.ω 0) := by
      refine ⟨⟨by simpa using hy'.1, by simp; linarith [hy'.2]⟩, ?_⟩
      rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      simp at hl
      linarith
    have := hmax _ hmem
    simp only [ex15B2Economy, Matrix.cons_val_zero, Pi.add_apply, Pi.single_eq_same] at this
    simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have hy1 := hy'.2
    have h1 : y 1 ^ 8 < (y 1 + 1) ^ 8 := pow_lt_pow_left₀ (by linarith) hy'.2.le (by norm_num)
    have h2 : 1 / (8 * (y 1 + 1) ^ 8) < 1 / (8 * y 1 ^ 8) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    linarith

/-- **Example 15.B.2** (MWG, pp. 521-522). The Walrasian equilibrium price vectors are exactly the
`p ≫ 0` with `p₁/p₂ ∈ {1, 2, 1/2}`. -/
theorem example_15_B_2 (p : Fin 2 → ℝ) :
    (∃ x, ex15B2Economy.IsDemandEqm p x) ↔
      StrictlyPositive p ∧ (p 0 = p 1 ∨ p 0 = 2 * p 1 ∨ 2 * p 0 = p 1) := by
  have hr := ex15B2r_bounds
  have htot : ex15B2Economy.totalEndowment = ![2 + ex15B2r, ex15B2r + 2] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B2Economy, Fin.sum_univ_two]
  constructor
  · rintro ⟨x, hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      have := hd 0
      rw [ex15B2_demand0_empty hp] at this
      exact this
    refine ⟨hp, ?_⟩
    set t := (p 0 / p 1) ^ ((1 : ℝ) / 9) with htdef
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    have ht : 0 < t := Real.rpow_pos_of_pos hq _
    have ht9 : t ^ 9 = p 0 / p 1 := by
      rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      norm_num
    obtain ⟨hd1, hd2, -, -⟩ := exercise_15_B_5_offerCurves hp ht ht9
    have hx0 := hd 0
    have hx1 := hd 1
    rw [hd1, Set.mem_singleton_iff] at hx0
    rw [hd2, Set.mem_singleton_iff] at hx1
    have hc := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx0, hx1] at hc
    simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_one, Matrix.cons_val_zero] at hc
    have hP : ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 := by linarith
    rcases (ex15B2_roots ht).1 hP with h | h | h
    · left
      rw [h, one_pow, eq_comm, div_eq_one_iff_eq (hp 1).ne'] at ht9
      exact ht9
    · right; left
      rw [h, ex15B2a_pow, eq_div_iff (hp 1).ne'] at ht9
      exact ht9.symm
    · right; right
      rw [h, ex15B2a_inv_pow, eq_div_iff (hp 1).ne'] at ht9
      linarith
  · rintro ⟨hp, hrel⟩
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    obtain ⟨t, ht, ht9, hP⟩ : ∃ t, 0 < t ∧ t ^ 9 = p 0 / p 1 ∧
        ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 := by
      have ha := ex15B2a_bounds
      rcases hrel with h | h | h
      · refine ⟨1, one_pos, ?_, (ex15B2_roots one_pos).2 (Or.inl rfl)⟩
        rw [h, div_self (hp 1).ne', one_pow]
      · refine ⟨ex15B2a, by linarith, ?_, (ex15B2_roots (by linarith)).2 (Or.inr (Or.inl rfl))⟩
        rw [h, ex15B2a_pow, mul_div_cancel_right₀ _ (hp 1).ne']
      · have hpos : 0 < ex15B2a ^ 8 / 2 := div_pos (pow_pos (by linarith [ha.1]) 8) two_pos
        refine ⟨ex15B2a ^ 8 / 2, hpos, ?_, (ex15B2_roots hpos).2 (Or.inr (Or.inr rfl))⟩
        rw [ex15B2a_inv_pow, ← h]
        field_simp [(hp 0).ne']
    obtain ⟨hd1, hd2, hpos1, hpos2⟩ := exercise_15_B_5_offerCurves hp ht ht9
    refine ⟨![ex15B2OC1 t, ex15B2OC2 t], ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩⟩
    · fin_cases i
      · exact ⟨(hpos1 0).le, hpos1 1⟩
      · exact ⟨hpos2 0, (hpos2 1).le⟩
    · rw [htot]
      have h9 : t ^ 9 ≠ 0 := by positivity
      have e0 : ex15B2OC1 t 0 + ex15B2OC2 t 0 = 2 + ex15B2r := by
        simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_zero]
        field_simp
        linear_combination (-1 : ℝ) * hP
      have e1 : ex15B2OC1 t 1 + ex15B2OC2 t 1 = ex15B2r + 2 := by
        simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_one, Matrix.cons_val_zero]
        linear_combination hP
      funext l
      fin_cases l
      · simpa [Fin.sum_univ_two] using e0
      · simpa [Fin.sum_univ_two] using e1
    · fin_cases i
      · exact (hd1 ▸ Set.mem_singleton (ex15B2OC1 t) : ex15B2OC1 t ∈ ex15B2Economy.demand 0 p)
      · exact (hd2 ▸ Set.mem_singleton (ex15B2OC2 t) : ex15B2OC2 t ∈ ex15B2Economy.demand 1 p)

/-- **Exercise 15.B.5** (MWG, p. 541): the offer curves in the book's `rpow` form,
`OC₁(p) = (2 + r(p₂/p₁) - (p₂/p₁)^{8/9}, (p₂/p₁)^{-1/9})` and
`OC₂(p) = ((p₁/p₂)^{-1/9}, 2 + r(p₁/p₂) - (p₁/p₂)^{8/9})`. -/
theorem exercise_15_B_5_printed {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    ex15B2Economy.demand 0 p = {![2 + ex15B2r * (p 1 / p 0) - (p 1 / p 0) ^ ((8 : ℝ) / 9),
      (p 1 / p 0) ^ (-(1 : ℝ) / 9)]} ∧
    ex15B2Economy.demand 1 p = {![(p 0 / p 1) ^ (-(1 : ℝ) / 9),
      2 + ex15B2r * (p 0 / p 1) - (p 0 / p 1) ^ ((8 : ℝ) / 9)]} := by
  set q := p 0 / p 1 with hqd
  have hq : 0 < q := div_pos (hp 0) (hp 1)
  set t := q ^ ((1 : ℝ) / 9) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hq _
  have ht9 : t ^ 9 = q := by
    rw [htdef, ← Real.rpow_mul_natCast hq.le]
    norm_num
  have hinv : p 1 / p 0 = q⁻¹ := by rw [hqd, inv_div]
  obtain ⟨hd1, hd2, -, -⟩ := exercise_15_B_5_offerCurves hp ht ht9
  have e1 : (q⁻¹) ^ ((8 : ℝ) / 9) = 1 / t ^ 8 := by
    rw [Real.inv_rpow hq.le, show (8 : ℝ) / 9 = (1 / 9) * ((8 : ℕ) : ℝ) by norm_num,
      Real.rpow_mul_natCast hq.le]
    exact (one_div (t ^ 8)).symm
  have e2 : (q⁻¹) ^ (-(1 : ℝ) / 9) = t := by
    rw [Real.inv_rpow hq.le, show -(1 : ℝ) / 9 = -((1 : ℝ) / 9) by ring,
      Real.rpow_neg hq.le, inv_inv]
  have e3 : q ^ (-(1 : ℝ) / 9) = 1 / t := by
    rw [show -(1 : ℝ) / 9 = -((1 : ℝ) / 9) by ring, Real.rpow_neg hq.le]
    exact (one_div t).symm
  have e4 : q ^ ((8 : ℝ) / 9) = t ^ 8 := by
    rw [show (8 : ℝ) / 9 = (1 / 9) * ((8 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hq.le]
  constructor
  · rw [hd1, hinv, e1, e2, ← ht9]
    congr 1
  · rw [hd2, e3, e4, ← ht9]
    rfl

/-- **Example 15.B.2** (MWG, p. 521): consumer 1's demand for good 1 may increase with `p₁`. At
`p = (1, 1)` it is `1 + r`, at `p = (2, 1)` it is `2 + 2^{-1/9} - 2^{1/9}`, which is larger. -/
theorem example_15_B_2_increasing :
    ex15B2OC1 1 0 < ex15B2OC1 ex15B2a 0 ∧ (1 : ℝ) ^ 9 = 1 / 1 ∧ ex15B2a ^ 9 = 2 / 1 := by
  have ha := ex15B2a_bounds
  have h9 := ex15B2a_pow
  have hpos : 0 < ex15B2a := by linarith
  refine ⟨?_, by norm_num, by rw [h9]; norm_num⟩
  simp only [ex15B2OC1, Matrix.cons_val_zero, one_pow, div_one]
  rw [h9, ex15B2r_eq]
  have h8 : ex15B2a ^ 8 = 2 / ex15B2a := by
    rw [eq_div_iff hpos.ne', ← h9]
    ring
  rw [h8]
  rw [← sub_pos]
  have : 2 + (2 / ex15B2a - ex15B2a) / 2 - 1 / (2 / ex15B2a) - (2 + (2 / ex15B2a - ex15B2a) - 1)
      = 1 - 1 / ex15B2a := by
    field_simp
    ring
  rw [this, sub_pos, div_lt_one hpos]
  linarith

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Blair's CES economy (MWG Exercise 15.B.6, p. 541)

The utilities are CES with exponent `-2`, `u(x) = (A x₁⁻² + B x₂⁻²)^{-1/2}`. We use the form
`x₁x₂ / √(A x₂² + B x₁²)` (`cesNeg2`), which equals it on `ℝ²₊₊` (`cesNeg2_eq`) and is its
continuous extension by `0` to the boundary of `ℝ²₊`.

* `cesNeg2_optimal`: the bundle `x ≫ 0` satisfying the first-order condition `A p₂ x₂³ = B p₁ x₁³`
  and `p·x = w` is the unique utility maximizer on the budget set (the proof is the convexity of
  `s ↦ s⁻²`).
* **Exercise 15.B.6**: with `u₁ = (x₁₁⁻² + (12/37)³ x₂₁⁻²)^{-1/2}`, `ω₁ = (1, 0)`,
  `u₂ = ((12/37)³ x₁₂⁻² + x₂₂⁻²)^{-1/2}`, `ω₂ = (0, 1)`, the Walrasian equilibrium price ratios are
  exactly `p₁/p₂ ∈ {27/64, 1, 64/27}` (`exercise_15_B_6`), with the equilibrium allocations
  given by `blairAlloc`.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Exercise 15.B.6** (MWG, p. 541). The CES utility with exponent `-2` and weights `A, B`,
written `x₁x₂/√(A x₂² + B x₁²)`. -/
noncomputable def cesNeg2 (A B : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  x 0 * x 1 / Real.sqrt (A * x 1 ^ 2 + B * x 0 ^ 2)

/-- On `ℝ²₊₊`, `cesNeg2 A B x = (A x₁⁻² + B x₂⁻²)^{-1/2}`. -/
theorem cesNeg2_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (h0 : 0 < x 0)
    (h1 : 0 < x 1) : cesNeg2 A B x = (A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) := by
  have hS : 0 < A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹ := by positivity
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hS.le, ← Real.sqrt_eq_rpow,
    cesNeg2]
  have e : A * x 1 ^ 2 + B * x 0 ^ 2 = (x 0 * x 1) ^ 2 * (A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- The value of `cesNeg2` on `ℝ²₊₊` through `S(x) = A/x₁² + B/x₂²`: `u = 1/√S`. -/
theorem cesNeg2_eq_inv_sqrt {A B : ℝ} {x : Fin 2 → ℝ} (h0 : 0 < x 0) (h1 : 0 < x 1) :
    cesNeg2 A B x = 1 / Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := by
  have e : A * x 1 ^ 2 + B * x 0 ^ 2 = (x 0 * x 1) ^ 2 * (A / x 0 ^ 2 + B / x 1 ^ 2) := by
    field_simp
  rw [cesNeg2, e]
  by_cases hS : 0 ≤ A / x 0 ^ 2 + B / x 1 ^ 2
  · rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    by_cases hS0 : Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) = 0
    · rw [hS0]
      simp
    · field_simp
  · rw [not_le] at hS
    rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hS.le),
      Real.sqrt_eq_zero'.2 hS.le]
    simp

/-- The convexity inequality `1/y² ≥ 3/x² - 2y/x³` for `x, y > 0`, strict unless `y = x`. -/
theorem inv_sq_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    3 / x ^ 2 - 2 * y / x ^ 3 ≤ 1 / y ^ 2 ∧ (y ≠ x → 3 / x ^ 2 - 2 * y / x ^ 3 < 1 / y ^ 2) := by
  have key : 1 / y ^ 2 - (3 / x ^ 2 - 2 * y / x ^ 3) =
      (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by
    field_simp
    ring
  constructor
  · have : 0 ≤ (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by positivity
    linarith
  · intro hne
    have h2 : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      positivity
    have : 0 < (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by positivity
    linarith

/-- **Exercise 15.B.6** (MWG, p. 541), the demand computation. Let `A, B > 0`, `p ≫ 0` and
`x ≫ 0` satisfy the first-order condition `A p₂ x₂³ = B p₁ x₁³`. Then every `y ≫ 0` with
`p·y ≤ p·x` has `A/y₁² + B/y₂² ≥ A/x₁² + B/x₂²`, strictly unless `y = x`. -/
theorem cesNeg2_optimal {A B p0 p1 x0 x1 y0 y1 : ℝ} (hA : 0 < A) (hB : 0 < B) (hp0 : 0 < p0)
    (hx0 : 0 < x0) (hx1 : 0 < x1) (hfoc : A * p1 * x1 ^ 3 = B * p0 * x0 ^ 3)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hb : p0 * y0 + p1 * y1 ≤ p0 * x0 + p1 * x1) :
    A / x0 ^ 2 + B / x1 ^ 2 ≤ A / y0 ^ 2 + B / y1 ^ 2 ∧
      ((y0 ≠ x0 ∨ y1 ≠ x1) → A / x0 ^ 2 + B / x1 ^ 2 < A / y0 ^ 2 + B / y1 ^ 2) := by
  -- the Lagrange multiplier `λ = A/(p₁ x₁³) = B/(p₂ x₂³)`
  set lam := A / (p0 * x0 ^ 3) with hlam
  have hlam1 : B / x1 ^ 3 = lam * p1 := by
    rw [hlam]
    field_simp
    linear_combination (-1 : ℝ) * hfoc
  have hlam0 : A / x0 ^ 3 = lam * p0 := by
    rw [hlam]
    field_simp
  have hlampos : 0 < lam := by positivity
  obtain ⟨t0, s0⟩ := inv_sq_tangent hx0 hy0
  obtain ⟨t1, s1⟩ := inv_sq_tangent hx1 hy1
  have e0 : A / y0 ^ 2 = A * (1 / y0 ^ 2) := by ring
  have e1 : B / y1 ^ 2 = B * (1 / y1 ^ 2) := by ring
  have lin : A * (3 / x0 ^ 2 - 2 * y0 / x0 ^ 3) + B * (3 / x1 ^ 2 - 2 * y1 / x1 ^ 3) =
      3 * (A / x0 ^ 2 + B / x1 ^ 2) - 2 * lam * (p0 * y0 + p1 * y1) := by
    have : A * (2 * y0 / x0 ^ 3) + B * (2 * y1 / x1 ^ 3) = 2 * lam * (p0 * y0 + p1 * y1) := by
      have h1 : A * (2 * y0 / x0 ^ 3) = 2 * y0 * (A / x0 ^ 3) := by ring
      have h2 : B * (2 * y1 / x1 ^ 3) = 2 * y1 * (B / x1 ^ 3) := by ring
      rw [h1, h2, hlam0, hlam1]
      ring
    linear_combination (-1 : ℝ) * this
  have linx : 2 * lam * (p0 * x0 + p1 * x1) = 2 * (A / x0 ^ 2 + B / x1 ^ 2) := by
    have h1 : lam * p0 * x0 = A / x0 ^ 2 := by
      rw [← hlam0]
      field_simp
    have h2 : lam * p1 * x1 = B / x1 ^ 2 := by
      rw [← hlam1]
      field_simp
    linear_combination 2 * h1 + 2 * h2
  have hcost : 2 * lam * (p0 * y0 + p1 * y1) ≤ 2 * lam * (p0 * x0 + p1 * x1) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left t0 hA.le, mul_le_mul_of_nonneg_left t1 hB.le]
  · rintro (h | h)
    · nlinarith [mul_lt_mul_of_pos_left (s0 h) hA, mul_le_mul_of_nonneg_left t1 hB.le]
    · nlinarith [mul_le_mul_of_nonneg_left t0 hA.le, mul_lt_mul_of_pos_left (s1 h) hB]

/-- The demand of a `cesNeg2 A B` consumer at `p ≫ 0` with wealth `p·x`, where `x ≫ 0` satisfies
the first-order condition: exactly `{x}`. -/
theorem cesNeg2_demand {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {p x : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hx0 : 0 < x 0) (hx1 : 0 < x 1)
    (hfoc : A * p 1 * x 1 ^ 3 = B * p 0 * x 0 ^ 3) :
    walrasianDemand (cesNeg2 A B) p (p ⬝ᵥ x) = {x} := by
  have hux : 0 < cesNeg2 A B x := by
    rw [cesNeg2_eq_inv_sqrt hx0 hx1]
    have : 0 < A / x 0 ^ 2 + B / x 1 ^ 2 := by positivity
    positivity
  have hxb : x ∈ budgetSet p (p ⬝ᵥ x) := ⟨fun l => by fin_cases l; exacts [hx0.le, hx1.le],
    le_rfl⟩
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  -- utility comparison for affordable bundles
  have hcmp : ∀ y ∈ budgetSet p (p ⬝ᵥ x), cesNeg2 A B y ≤ cesNeg2 A B x ∧
      (cesNeg2 A B y = cesNeg2 A B x → y = x) := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ p 0 * x 0 + p 1 * x 1 := by
      rw [← hdot, ← hdot]
      exact hy.2
    by_cases hpos : 0 < y 0 ∧ 0 < y 1
    · obtain ⟨h1, h2⟩ := cesNeg2_optimal hA hB (hp 0) hx0 hx1 hfoc hpos.1 hpos.2 hb
      have hSx : 0 < A / x 0 ^ 2 + B / x 1 ^ 2 := by positivity
      rw [cesNeg2_eq_inv_sqrt hx0 hx1, cesNeg2_eq_inv_sqrt hpos.1 hpos.2]
      have hsq : Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) ≤ Real.sqrt (A / y 0 ^ 2 + B / y 1 ^ 2) :=
        Real.sqrt_le_sqrt h1
      have hsx : 0 < Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := Real.sqrt_pos.2 hSx
      refine ⟨one_div_le_one_div_of_le hsx hsq, fun heq => ?_⟩
      by_contra hne
      have hne' : y 0 ≠ x 0 ∨ y 1 ≠ x 1 := by
        by_contra hall
        simp only [not_or, not_not] at hall
        exact hne (funext fun l => by fin_cases l; exacts [hall.1, hall.2])
      have hlt := Real.sqrt_lt_sqrt hSx.le (h2 hne')
      have : 1 / Real.sqrt (A / y 0 ^ 2 + B / y 1 ^ 2) <
          1 / Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := one_div_lt_one_div_of_lt hsx hlt
      linarith
    · have hzero : cesNeg2 A B y = 0 := by
        have hy0 := hy.1 0
        have hy1 := hy.1 1
        have : y 0 * y 1 = 0 := by
          by_contra hne
          apply hpos
          rcases mul_ne_zero_iff.1 hne with ⟨a, b⟩
          exact ⟨lt_of_le_of_ne hy0 (Ne.symm a), lt_of_le_of_ne hy1 (Ne.symm b)⟩
        simp [cesNeg2, this]
      rw [hzero]
      exact ⟨hux.le, fun h => absurd h hux.ne⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact (hcmp y hy.1).2 (le_antisymm (hcmp y hy.1).1 (hy.2 x hxb))
  · rintro rfl
    exact ⟨hxb, fun y hy => (hcmp y hy).1⟩

/-- `cesNeg2` with `B > 0` is strictly increasing in `x₁` when `x₂ > 0`. -/
theorem cesNeg2_lt_add0 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (hx0 : 0 ≤ x 0)
    (hx1 : 0 < x 1) : cesNeg2 A B x < cesNeg2 A B (x + Pi.single 0 1) := by
  have hy0 : 0 < (x + Pi.single 0 1 : Fin 2 → ℝ) 0 := by simp; linarith
  have hy1 : (x + Pi.single 0 1 : Fin 2 → ℝ) 1 = x 1 := by simp
  rw [cesNeg2_eq_inv_sqrt hy0 (by rw [hy1]; exact hx1)]
  rcases eq_or_lt_of_le hx0 with h | h
  · have : cesNeg2 A B x = 0 := by simp [cesNeg2, ← h]
    rw [this]
    have : 0 < A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 +
        B / (x + Pi.single 0 1 : Fin 2 → ℝ) 1 ^ 2 := by
      rw [hy1]
      positivity
    positivity
  · rw [cesNeg2_eq_inv_sqrt h hx1, hy1]
    have hlt : A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 < A / x 0 ^ 2 := by
      apply div_lt_div_of_pos_left hA (by positivity)
      simp only [Pi.add_apply, Pi.single_eq_same]
      nlinarith
    have hS : 0 < A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 + B / x 1 ^ 2 := by positivity
    exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hS) (Real.sqrt_lt_sqrt hS.le (by linarith))

/-- `cesNeg2` with the weights and goods swapped. -/
theorem cesNeg2_swap (A B : ℝ) (x : Fin 2 → ℝ) :
    cesNeg2 A B x = cesNeg2 B A ![x 1, x 0] := by
  simp [cesNeg2, mul_comm, add_comm]

/-- `cesNeg2` is strictly increasing in `x₂` when `x₁ > 0`. -/
theorem cesNeg2_lt_add1 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (hx0 : 0 < x 0)
    (hx1 : 0 ≤ x 1) : cesNeg2 A B x < cesNeg2 A B (x + Pi.single 1 1) := by
  rw [cesNeg2_swap A B x, cesNeg2_swap A B (x + Pi.single 1 1)]
  have h := cesNeg2_lt_add0 hB hA (x := ![x 1, x 0]) (by simpa using hx1) (by simpa using hx0)
  convert h using 2
  funext l
  fin_cases l <;> simp

/-- The constant `c = 12/37` of Exercise 15.B.6. -/
noncomputable def blairC : ℝ := 12 / 37

/-- **Exercise 15.B.6** (MWG, p. 541). Blair's economy:
`u₁ = (x₁₁⁻² + c³x₂₁⁻²)^{-1/2}`, `u₂ = (c³x₁₂⁻² + x₂₂⁻²)^{-1/2}` (`c = 12/37`), `ω₁ = (1, 0)`,
`ω₂ = (0, 1)`. -/
noncomputable def blairEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![cesNeg2 1 (blairC ^ 3), cesNeg2 (blairC ^ 3) 1] ![![1, 0], ![0, 1]]

/-- The equilibrium allocation of Blair's economy at `p = (t³, 1)`:
consumer 1 gets `(t²/(t² + c), ct³/(t² + c))`, consumer 2 gets `(c/(ct³ + t), t/(ct³ + t)·t/c·c)`
in the form `(c/(t(ct² + 1)), 1/(ct² + 1))`. -/
noncomputable def blairAlloc (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![t ^ 2 / (t ^ 2 + blairC), blairC * t ^ 3 / (t ^ 2 + blairC)],
    ![blairC / (t * (blairC * t ^ 2 + 1)), 1 / (blairC * t ^ 2 + 1)]]

/-- Blair's economy: at `p ≫ 0` with `t³ = p₁/p₂`, the demands are the bundles of
`blairAlloc t`. -/
theorem blair_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {t : ℝ} (ht : 0 < t)
    (ht3 : t ^ 3 = p 0 / p 1) :
    blairEconomy.demand 0 p = {blairAlloc t 0} ∧ blairEconomy.demand 1 p = {blairAlloc t 1} := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  have hp0 := hp 0
  have hp1 := hp 1
  have hq : p 0 = t ^ 3 * p 1 := by rw [ht3]; field_simp
  constructor
  · have hx0 : 0 < blairAlloc t 0 0 := by
      simp only [blairAlloc, Matrix.cons_val_zero]; positivity
    have hx1 : 0 < blairAlloc t 0 1 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hw : p ⬝ᵥ blairEconomy.ω 0 = p ⬝ᵥ blairAlloc t 0 := by
      simp only [blairEconomy, ExchangeEconomy.ofOrthant, blairAlloc, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
      ring
    have hfoc : 1 * p 1 * blairAlloc t 0 1 ^ 3 = blairC ^ 3 * p 0 * blairAlloc t 0 0 ^ 3 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
    have := cesNeg2_demand one_pos (pow_pos hc 3) hp hx0 hx1 hfoc
    unfold ExchangeEconomy.demand
    rw [hw]
    exact this
  · have hx0 : 0 < blairAlloc t 1 0 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hx1 : 0 < blairAlloc t 1 1 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hw : p ⬝ᵥ blairEconomy.ω 1 = p ⬝ᵥ blairAlloc t 1 := by
      simp only [blairEconomy, ExchangeEconomy.ofOrthant, blairAlloc, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
      ring
    have hfoc : blairC ^ 3 * p 1 * blairAlloc t 1 1 ^ 3 = 1 * p 0 * blairAlloc t 1 0 ^ 3 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
    have := cesNeg2_demand (pow_pos hc 3) one_pos hp hx0 hx1 hfoc
    unfold ExchangeEconomy.demand
    rw [hw]
    exact this

/-- In Blair's economy no consumer's demand exists unless `p ≫ 0`. -/
theorem blair_demand_empty {p : Fin 2 → ℝ} (hp : ¬ StrictlyPositive p) :
    blairEconomy.demand 0 p = ∅ ∨ blairEconomy.demand 1 p = ∅ := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · -- consumer 2 can add good 1 for free
    right
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx, hb⟩, hmax⟩
    have hb' : p 0 * x 0 + p 1 * x 1 ≤ p 1 := by
      simpa [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] using hb
    simp at hl
    by_cases hx1 : 0 < x 1
    · have hmem : x + Pi.single 0 1 ∈ budgetSetOn (blairEconomy.X 1) p
          (p ⬝ᵥ blairEconomy.ω 1) := by
        refine ⟨fun j => ?_, ?_⟩
        · fin_cases j
          · simp; linarith [hx 0]
          · simpa using hx 1
        · simp only [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two,
            Pi.add_apply]
          simp
          linarith
      have h1 := hmax _ hmem
      have h2 := cesNeg2_lt_add0 (pow_pos hc 3) one_pos (hx 0) hx1
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
    · have hx1' : x 1 = 0 := le_antisymm (not_lt.1 hx1) (hx 1)
      have hmem : (![1, 1] : Fin 2 → ℝ) ∈ budgetSetOn (blairEconomy.X 1) p
          (p ⬝ᵥ blairEconomy.ω 1) := by
        refine ⟨fun j => by fin_cases j <;> simp, ?_⟩
        simp [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        linarith
      have h1 := hmax _ hmem
      have hz : cesNeg2 (blairC ^ 3) 1 x = 0 := by simp [cesNeg2, hx1']
      have hpos : 0 < cesNeg2 (blairC ^ 3) 1 ![1, 1] := by
        rw [cesNeg2_eq_inv_sqrt (by simp) (by simp)]
        have : 0 < blairC ^ 3 / (![1, 1] : Fin 2 → ℝ) 0 ^ 2 + 1 / (![1, 1] : Fin 2 → ℝ) 1 ^ 2 := by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          positivity
        positivity
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
  · -- consumer 1 can add good 2 for free
    left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx, hb⟩, hmax⟩
    have hb' : p 0 * x 0 + p 1 * x 1 ≤ p 0 := by
      simpa [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] using hb
    simp at hl
    by_cases hx0 : 0 < x 0
    · have hmem : x + Pi.single 1 1 ∈ budgetSetOn (blairEconomy.X 0) p
          (p ⬝ᵥ blairEconomy.ω 0) := by
        refine ⟨fun j => ?_, ?_⟩
        · fin_cases j
          · simpa using hx 0
          · simp; linarith [hx 1]
        · simp only [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two,
            Pi.add_apply]
          simp
          linarith
      have h1 := hmax _ hmem
      have h2 := cesNeg2_lt_add1 one_pos (pow_pos hc 3) hx0 (hx 1)
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
    · have hx0' : x 0 = 0 := le_antisymm (not_lt.1 hx0) (hx 0)
      have hmem : (![1, 1] : Fin 2 → ℝ) ∈ budgetSetOn (blairEconomy.X 0) p
          (p ⬝ᵥ blairEconomy.ω 0) := by
        refine ⟨fun j => by fin_cases j <;> simp, ?_⟩
        simp [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        linarith
      have h1 := hmax _ hmem
      have hz : cesNeg2 1 (blairC ^ 3) x = 0 := by simp [cesNeg2, hx0']
      have hpos : 0 < cesNeg2 1 (blairC ^ 3) ![1, 1] := by
        rw [cesNeg2_eq_inv_sqrt (by simp) (by simp)]
        have : 0 < 1 / (![1, 1] : Fin 2 → ℝ) 0 ^ 2 + blairC ^ 3 / (![1, 1] : Fin 2 → ℝ) 1 ^ 2 := by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          positivity
        positivity
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith

/-- The market-clearing equation of Blair's economy, `c t³ - t² + t - c = 0`, factors as
`(t - 1)(3t - 4)(4t - 3)/37 = 0` for `c = 12/37`. -/
theorem blair_factor (t : ℝ) :
    blairC * t ^ 3 - t ^ 2 + t - blairC = (t - 1) * (3 * t - 4) * (4 * t - 3) / 37 := by
  rw [blairC]
  ring

/-- **Exercise 15.B.6** (MWG, p. 541). The Walrasian equilibrium price vectors of Blair's economy
are exactly the `p ≫ 0` with `p₁/p₂ ∈ {1, 64/27, 27/64}`; at `p₁/p₂ = t³` the equilibrium
allocation is `blairAlloc t`. -/
theorem exercise_15_B_6 (p : Fin 2 → ℝ) :
    (∃ x, blairEconomy.IsDemandEqm p x) ↔
      StrictlyPositive p ∧ (p 0 = p 1 ∨ 27 * p 0 = 64 * p 1 ∨ 64 * p 0 = 27 * p 1) := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  have htot : blairEconomy.totalEndowment = ![1, 1] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, blairEconomy,
      ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
  -- market clearing for good 1 at `t`
  have hclear : ∀ t : ℝ, 0 < t → (blairAlloc t 0 0 + blairAlloc t 1 0 = 1 ↔
      blairC * t ^ 3 - t ^ 2 + t - blairC = 0) := by
    intro t ht
    simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : 0 < t ^ 2 + blairC := by positivity
    have h2 : 0 < t * (blairC * t ^ 2 + 1) := by positivity
    rw [div_add_div _ _ h1.ne' h2.ne', div_eq_one_iff_eq (by positivity)]
    constructor <;> intro h <;> nlinarith [h]
  have hclear2 : ∀ t : ℝ, 0 < t → blairAlloc t 0 0 + blairAlloc t 1 0 = 1 →
      blairAlloc t 0 1 + blairAlloc t 1 1 = 1 := by
    intro t ht h
    have hP := (hclear t ht).1 h
    simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    have h1 : 0 < t ^ 2 + blairC := by positivity
    have h2 : 0 < blairC * t ^ 2 + 1 := by positivity
    rw [div_add_div _ _ h1.ne' h2.ne', div_eq_one_iff_eq (by positivity)]
    nlinarith [hP]
  constructor
  · rintro ⟨x, hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      rcases blair_demand_empty hp with h | h
      · have := hd 0; rw [h] at this; exact this
      · have := hd 1; rw [h] at this; exact this
    refine ⟨hp, ?_⟩
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    set t := (p 0 / p 1) ^ ((1 : ℝ) / 3) with htdef
    have ht : 0 < t := Real.rpow_pos_of_pos hq _
    have ht3 : t ^ 3 = p 0 / p 1 := by
      rw [htdef, ← Real.rpow_mul_natCast hq.le]
      norm_num
    obtain ⟨hd0, hd1⟩ := blair_demand hp ht ht3
    have hx0 := hd 0
    have hx1 := hd 1
    rw [hd0, Set.mem_singleton_iff] at hx0
    rw [hd1, Set.mem_singleton_iff] at hx1
    have hc1 := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx0, hx1] at hc1
    have hP := (hclear t ht).1 hc1
    rw [blair_factor] at hP
    have : (t - 1) * (3 * t - 4) * (4 * t - 3) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left
        have : t = 1 := by linarith
        rw [this, one_pow, eq_comm, div_eq_one_iff_eq (hp 1).ne'] at ht3
        exact ht3
      · right; left
        have : t = 4 / 3 := by linarith
        rw [this, eq_div_iff (hp 1).ne'] at ht3
        linarith
    · right; right
      have : t = 3 / 4 := by linarith
      rw [this, eq_div_iff (hp 1).ne'] at ht3
      linarith
  · rintro ⟨hp, hrel⟩
    obtain ⟨t, ht, ht3, hP⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 3 = p 0 / p 1 ∧
        blairC * t ^ 3 - t ^ 2 + t - blairC = 0 := by
      rcases hrel with h | h | h
      · refine ⟨1, one_pos, ?_, by rw [blair_factor]; ring⟩
        rw [h, div_self (hp 1).ne', one_pow]
      · refine ⟨4 / 3, by norm_num, ?_, by rw [blair_factor]; ring⟩
        rw [eq_div_iff (hp 1).ne']
        linarith
      · refine ⟨3 / 4, by norm_num, ?_, by rw [blair_factor]; ring⟩
        rw [eq_div_iff (hp 1).ne']
        linarith
    obtain ⟨hd0, hd1⟩ := blair_demand hp ht ht3
    have hc1 := (hclear t ht).2 hP
    have hc2 := hclear2 t ht hc1
    refine ⟨blairAlloc t, ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩⟩
    · fin_cases i
      · exact (hd0 ▸ Set.mem_singleton _ : blairAlloc t 0 ∈ blairEconomy.demand 0 p).1.1
      · exact (hd1 ▸ Set.mem_singleton _ : blairAlloc t 1 ∈ blairEconomy.demand 1 p).1.1
    · rw [htot]
      funext l
      fin_cases l
      · simpa [Fin.sum_univ_two] using hc1
      · simpa [Fin.sum_univ_two] using hc2
    · fin_cases i
      · exact (hd0 ▸ Set.mem_singleton _ : blairAlloc t 0 ∈ blairEconomy.demand 0 p)
      · exact (hd1 ▸ Set.mem_singleton _ : blairAlloc t 1 ∈ blairEconomy.demand 1 p)

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Offer curves (MWG Section 15.B, pp. 517-518, and Exercise 15.B.4, p. 541)

* p. 517-518: if preferences are convex and represented by a continuous utility that is
  differentiable at `ωᵢ ≫ 0` with `∇u(ωᵢ) ≫ 0`, the endowment is demanded at the prices
  `p = ∇u(ωᵢ)`: the offer curve passes through the endowment point, where the budget line is
  tangent to the indifference curve (`endowment_mem_offerCurve`).
* **Exercise 15.B.4**. An offer curve is described by the demand `d(q)` at prices `(q, 1)`,
  `q = p₁/p₂` (demand is homogeneous of degree zero). (b) If both offer curves have the gross
  substitute property there is at most one equilibrium price ratio (`exercise_15_B_4b`), so in an
  Edgeworth box with single-valued demands the offer curves intersect at most once besides the
  endowment (`exercise_15_B_4b_offerCurves`). (e) The same holds if one offer curve is normal and
  the other has the gross substitute property (`exercise_15_B_4e`). (f) Two normal offer curves can
  intersect several times: the offer curves of Example 15.B.2 are normal
  (`exercise_15_B_4f`). (d) A strictly non-normal offer curve requires an inferior good, by the
  Slutsky decomposition along the offer curve (`exercise_15_B_4d`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-- **Section 15.B** (MWG, pp. 517-518). Let `u` be continuous on `ℝ^L₊`, represent convex
preferences, and be differentiable at `ω ≫ 0` with gradient `g = ∇u(ω) ≫ 0`. Then `ω` is demanded
at prices `g` (with wealth `g·ω`): the offer curve passes through the endowment, with the budget
line tangent to the indifference curve there. -/
theorem endowment_mem_offerCurve {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hconv : PrefConvex (nonnegOrthant L) (utilityPref u))
    {ω : Fin L → ℝ} (hω : StrictlyPositive ω) {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hd : HasFDerivAt u u' ω) (hg : StrictlyPositive fun l => u' (Pi.single l 1)) :
    ω ∈ walrasianDemand u (fun l => u' (Pi.single l 1)) ((fun l => u' (Pi.single l 1)) ⬝ᵥ ω) := by
  set g : Fin L → ℝ := fun l => u' (Pi.single l 1) with hgd
  have hωm : ω ∈ nonnegOrthant L := fun l => (hω l).le
  have hlin : ∀ v, u' v = g ⬝ᵥ v := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ u'.toLinearMap v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    have he : (fun j => if l = j then (1 : ℝ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [he, hgd, mul_comm]
  refine ⟨⟨hωm, le_rfl⟩, fun y hy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  -- a strictly better bundle strictly inside the budget set
  obtain ⟨y', hy'm, hy'c, hy'u⟩ : ∃ y' ∈ nonnegOrthant L, g ⬝ᵥ y' < g ⬝ᵥ ω ∧ u ω < u y' := by
    by_cases hin : g ⬝ᵥ y < g ⬝ᵥ ω
    · exact ⟨y, hy.1, hin, hlt⟩
    · have heq : g ⬝ᵥ y = g ⬝ᵥ ω := le_antisymm hy.2 (not_lt.1 hin)
      have hpos : 0 < g ⬝ᵥ ω := by
        by_cases hL : Nonempty (Fin L)
        · obtain ⟨l⟩ := hL
          exact dotProduct_pos_of_strictlyPositive hg hωm (fun h => by
            have := congrFun h l; simp at this; linarith [hω l])
        · exfalso
          rw [not_nonempty_iff] at hL
          have : y = ω := funext fun l => isEmptyElim l
          rw [this] at hlt
          exact lt_irrefl _ hlt
      set γ : ℝ → Fin L → ℝ := fun t => (1 - t / 2) • y
      have hγc : Continuous γ := by fun_prop
      have hγm : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ nonnegOrthant L := by
        intro t ht l
        simp only [γ, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith [ht.2]) (hy.1 l)
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hc hγc hγm (by simpa [γ] using hlt)
      refine ⟨γ t, hγm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      simp only [γ, dotProduct_smul, smul_eq_mul, heq]
      nlinarith
  -- along the segment from `ω` towards `y'` utility first falls (the derivative is negative)
  set h : ℝ → ℝ := fun t => u (ω + t • (y' - ω)) with hh
  have hline : HasDerivAt (fun t : ℝ => ω + t • (y' - ω)) (y' - ω) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y' - ω)).const_add ω
  have hhd : HasDerivAt h (u' (y' - ω)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hd) hline
    simpa [Function.comp_def, hh] using this
  have hneg : u' (y' - ω) < 0 := by
    rw [hlin, dotProduct_sub]
    linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 :=
    (nhdsWithin_le_nhds (Iic_mem_nhds one_pos))
  obtain ⟨t, ht0, ht1, hlow⟩ := exists_pos_deriv_neg hhd hneg hev
  -- but quasiconcavity keeps utility at least `u(ω)` on the segment
  have hq := quasiconcave_of_prefConvex hconv hωm hy'm (a := 1 - t) (b := t) (by linarith)
    ht0.le (by ring)
  rw [min_eq_left hy'u.le] at hq
  have e : (1 - t) • ω + t • y' = ω + t • (y' - ω) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [e] at hq
  simp only [hh, zero_smul, add_zero] at hlow
  linarith

/-! ### Exercise 15.B.4 -/

/-- **Exercise 15.B.4** (MWG, p. 541). An offer curve, given by demands `d(q)` at prices `(q, 1)`,
has the gross substitute property if raising the relative price of good 1 lowers the demand for
good 1 and raises the demand for good 2. -/
def GrossSubstitute (d : ℝ → Fin 2 → ℝ) : Prop :=
  ∀ q q', 0 < q → q < q' → d q' 0 < d q 0 ∧ d q 1 < d q' 1

/-- **Exercise 15.B.4** (MWG, p. 541). An offer curve is normal if an increase in the relative price
of a commodity raises the demand for that commodity only if the demands for both commodities
rise. -/
def NormalOfferCurve (d : ℝ → Fin 2 → ℝ) : Prop :=
  (∀ q q', 0 < q → q < q' → d q 0 < d q' 0 → d q 1 < d q' 1) ∧
    ∀ q q', 0 < q' → q' < q → d q 1 < d q' 1 → d q 0 < d q' 0

/-- **Exercise 15.B.4(b)** (MWG, p. 541). If both offer curves have the gross substitute property,
the market for good 1 clears at most at one relative price. -/
theorem exercise_15_B_4b {d₁ d₂ : ℝ → Fin 2 → ℝ} (h₁ : GrossSubstitute d₁)
    (h₂ : GrossSubstitute d₂) {ω₁ q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (hc : d₁ q 0 + d₂ q 0 = ω₁) (hc' : d₁ q' 0 + d₂ q' 0 = ω₁) : q = q' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · linarith [(h₁ q q' hq hlt).1, (h₂ q q' hq hlt).1]
  · linarith [(h₁ q' q hq' hlt).1, (h₂ q' q hq' hlt).1]

/-- **Exercise 15.B.4(b)** (MWG, p. 541), for offer curves. In an Edgeworth box with locally
nonsatiated consumers whose demands at prices `(q, 1)` are the single bundles `dᵢ(q)`, if both
offer curves have the gross substitute property then any two intersections of the offer curves
other than the endowment point coincide. -/
theorem exercise_15_B_4b_offerCurves {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {d : Fin 2 → ℝ → Fin 2 → ℝ}
    (hd : ∀ i q, 0 < q → E.demand i ![q, 1] = {d i q}) (hgs : ∀ i, GrossSubstitute (d i))
    {x x' : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hx' : E.InBox x') (hne : x 0 ≠ E.ω 0)
    (hne' : x' 0 ≠ E.ω 0) (h0 : x 0 ∈ E.offerCurve 0) (h1 : x 1 ∈ E.offerCurve 1)
    (h0' : x' 0 ∈ E.offerCurve 0) (h1' : x' 1 ∈ E.offerCurve 1) : x = x' := by
  -- each intersection is an equilibrium; normalize its prices to `(q, 1)`
  have key : ∀ y : Fin 2 → Fin 2 → ℝ, E.InBox y → y 0 ≠ E.ω 0 → y 0 ∈ E.offerCurve 0 →
      y 1 ∈ E.offerCurve 1 → ∃ q, 0 < q ∧ y = fun i => d i q := by
    intro y hy hyne hy0 hy1
    obtain ⟨p, hp, heq⟩ := isDemandEqm_of_offerCurves hX hlns hy hyne hy0 hy1
    have hp1 := hp 1
    refine ⟨p 0 / p 1, div_pos (hp 0) hp1, funext fun i => ?_⟩
    have hs : (p 1)⁻¹ • p = ![p 0 / p 1, 1] := by
      funext l
      fin_cases l
      · simp [div_eq_inv_mul]
      · simp [inv_mul_cancel₀ hp1.ne']
    have := heq.2 i
    rw [← E.demand_smul i p (inv_pos.2 hp1), hs, hd i _ (div_pos (hp 0) hp1)] at this
    exact this
  obtain ⟨q, hq, rfl⟩ := key x hx hne h0 h1
  obtain ⟨q', hq', rfl⟩ := key x' hx' hne' h0' h1'
  have hc := congrFun hx.2 0
  have hc' := congrFun hx'.2 0
  simp only [Finset.sum_apply, Fin.sum_univ_two] at hc hc'
  rw [exercise_15_B_4b (hgs 0) (hgs 1) hq hq' hc (hc'.trans hc.symm |>.symm ▸ hc')]

/-- **Exercise 15.B.4(e)** (MWG, p. 541). If one offer curve is normal and the other has the gross
substitute property, both markets clear at most at one relative price. -/
theorem exercise_15_B_4e {d₁ d₂ : ℝ → Fin 2 → ℝ} (h₁ : GrossSubstitute d₁)
    (h₂ : NormalOfferCurve d₂) {ω : Fin 2 → ℝ} {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (hc : ∀ l, d₁ q l + d₂ q l = ω l) (hc' : ∀ l, d₁ q' l + d₂ q' l = ω l) : q = q' := by
  by_contra hne
  -- order the two prices
  wlog hlt : q < q' generalizing q q'
  · exact this hq' hq hc' hc (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  obtain ⟨g0, g1⟩ := h₁ q q' hq hlt
  -- good 1: consumer 1 buys less, so consumer 2 buys more; normality then forces more good 2
  have hd20 : d₂ q 0 < d₂ q' 0 := by linarith [hc 0, hc' 0]
  have hd21 := h₂.1 q q' hq hlt hd20
  linarith [hc 1, hc' 1]

/-- **Exercise 15.B.4(d)** (MWG, p. 541). Along an offer curve, with endowment `ω₁` of good 1 and
demand `x`, raising `p₁` changes demands by `dx_ℓ = s_{ℓ1} + (ω₁ - x₁) ∂x_ℓ/∂w` (Slutsky), where
`s₁₁ ≤ 0 ≤ s₂₁` (negative semidefiniteness, Chapter 3). If the offer curve is (strictly) not
normal there, `dx₁ > 0 > dx₂`, then one good is inferior: `∂x₁/∂w < 0` or `∂x₂/∂w < 0`. -/
theorem exercise_15_B_4d {s₁₁ s₂₁ b₁ b₂ ω₁ x₁ : ℝ} (hs₁₁ : s₁₁ ≤ 0) (hs₂₁ : 0 ≤ s₂₁)
    (hdx₁ : 0 < s₁₁ + (ω₁ - x₁) * b₁) (hdx₂ : s₂₁ + (ω₁ - x₁) * b₂ < 0) : b₁ < 0 ∨ b₂ < 0 := by
  rcases lt_trichotomy (ω₁ - x₁) 0 with h | h | h
  · left
    by_contra hb
    rw [not_lt] at hb
    nlinarith
  · rw [h] at hdx₁; linarith
  · right
    by_contra hb
    rw [not_lt] at hb
    nlinarith

/-- The offer curves of Example 15.B.2 as functions of `q = p₁/p₂`, with `t = q^{1/9}`. -/
noncomputable def ex15B2d (i : Fin 2) (q : ℝ) : Fin 2 → ℝ :=
  ![ex15B2OC1 (q ^ ((1 : ℝ) / 9)), ex15B2OC2 (q ^ ((1 : ℝ) / 9))] i

/-- **Exercise 15.B.4(f)** (MWG, p. 541). Two normal offer curves can intersect several times: the
offer curves of Example 15.B.2 are normal (consumer 1's demand for good 2, `q^{1/9}`, rises with
`q`; consumer 2's demand for good 1, `q^{-1/9}`, falls), and they intersect at the three
equilibria `p₁/p₂ ∈ {1/2, 1, 2}` (`example_15_B_2`). -/
theorem exercise_15_B_4f : NormalOfferCurve (ex15B2d 0) ∧ NormalOfferCurve (ex15B2d 1) := by
  have hmono : ∀ q q' : ℝ, 0 < q → q < q' → q ^ ((1 : ℝ) / 9) < q' ^ ((1 : ℝ) / 9) :=
    fun q q' hq hlt => Real.rpow_lt_rpow hq.le hlt (by norm_num)
  refine ⟨⟨fun q q' hq hlt _ => ?_, fun q q' hq' hlt h => ?_⟩,
    ⟨fun q q' hq hlt h => ?_, fun q q' hq' hlt _ => ?_⟩⟩
  · simpa [ex15B2d, ex15B2OC1] using hmono q q' hq hlt
  · exfalso
    simp only [ex15B2d, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith [hmono q' q hq' hlt]
  · exfalso
    simp only [ex15B2d, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h1 := hmono q q' hq hlt
    have h0 : 0 < q ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hq _
    have : 1 / q' ^ ((1 : ℝ) / 9) < 1 / q ^ ((1 : ℝ) / 9) := one_div_lt_one_div_of_lt h0 h1
    linarith
  · simp only [ex15B2d, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 := hmono q' q hq' hlt
    have h0 : 0 < q' ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hq' _
    exact one_div_lt_one_div_of_lt h0 h1

/-- An instance of `endowment_mem_offerCurve`: the linear utility `x₁ + x₂` (continuous, convex,
gradient `(1, 1) ≫ 0`) at `ω = (1, 1)`. -/
theorem endowment_mem_offerCurve_instance :
    ContinuousOn linearUtility (nonnegOrthant 2) ∧
      PrefConvex (nonnegOrthant 2) (utilityPref linearUtility) ∧
      ∃ u' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt linearUtility u' ![1, 1] ∧
        StrictlyPositive fun l => u' (Pi.single l 1) := by
  refine ⟨by unfold linearUtility; fun_prop, fun x _ y hy z hz a b ha hb hab => ⟨?_, ?_⟩,
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2), ?_, ?_⟩
  · exact convex_nonnegOrthant 2 hy.1 hz.1 ha hb hab
  · have h1 := hy.2
    have h2 := hz.2
    simp only [utilityPref, linearUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have : linearUtility x = a * linearUtility x + b * linearUtility x := by
      rw [← add_mul, hab, one_mul]
    simp only [linearUtility] at this
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (![1, 1] : Fin 2 → ℝ)).add
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (![1, 1] : Fin 2 → ℝ))
    exact h
  · intro l
    fin_cases l <;> simp

/-- The Cobb-Douglas offer curve at prices `(q, 1)` with endowment `ω ≫ 0`. -/
noncomputable def cdOffer (α : ℝ) (ω : Fin 2 → ℝ) (q : ℝ) : Fin 2 → ℝ :=
  cobbDouglasDemand α ![q, 1] (q * ω 0 + ω 1)

/-- Instances of the gross substitute property (Exercise 15.B.4): Cobb-Douglas offer curves with
`ω ≫ 0`, `α ∈ (0, 1)`. -/
theorem cdOffer_grossSubstitute {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ω : Fin 2 → ℝ}
    (hω : ∀ l, 0 < ω l) : GrossSubstitute (cdOffer α ω) := by
  intro q q' hq hlt
  have hq' : 0 < q' := by linarith
  have h1 : 0 < 1 - α := by linarith
  simp only [cdOffer, cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one, div_one]
  constructor
  · rw [div_lt_div_iff₀ hq' hq]
    nlinarith [mul_pos hα0 (hω 1), hω 0]
  · nlinarith [mul_pos h1 (hω 0)]

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Nonexistence of equilibrium and failures of the second welfare theorem (MWG pp. 522, 525)

The book's Figures 15.B.10 and 15.B.14 are drawn without formulas; we give concrete economies with
the features described in the text and prove the claims.

* **Figure 15.B.10(a)** (`fig10aEconomy`): `u₁ = √x₁₁ + x₂₁`, `ω₁ = (0, 1)` (the indifference curve
  through `ω₁` has infinite slope there, yet more good 1 is strictly preferred) and `u₂ = x₁₂`,
  `ω₂ = (1, 0)`. There is no Walrasian equilibrium (`fig_15_B_10a_no_eqm`); at `p ≫ 0` consumer 2
  keeps `ω₂` and `ω₁` is never optimal for consumer 1; consumer 1 has no demand when `p₂ = 0`;
  consumer 2's preferences are not strongly monotone. The endowment is Pareto optimal but not
  supportable as an equilibrium with transfers (p. 525, `fig_15_B_10a_po_not_supportable`).
* **Figure 15.B.10(b)** (`fig10bEconomy`): consumer 1 has the nonconvex (strongly monotone,
  continuous) utility `x₁₁² + x₂₁²`, consumer 2 the Cobb-Douglas utility `x₁₂^{1/2}x₂₂^{1/2}`,
  `ω₁ = ω₂ = (1, 1)`: consumer 1 only demands corner bundles, and there is no Walrasian
  equilibrium (`fig_15_B_10b_no_eqm`).
* **Figure 15.B.14** (`fig14Economy`): `u₁ = x₁₁² + x₂₁²` and the convex, continuous and strongly
  monotone `u₂ = min(3x₁₂ + x₂₂, x₁₂ + 3x₂₂)`, `ω₁ = ω₂ = (1, 1)`: the allocation `((1,1),(1,1))`
  is Pareto optimal but not supportable as an equilibrium with transfers (`fig_15_B_14`).
* **Exercise 15.B.9** (Alphanse and Betatrix): the unique equilibrium
  (`exercise_15_B_9`: `p_P/(p_P + p_B) = a/30`, `a = (39 - √41)/2`), and with 5 units of Perrier the
  equilibria have Brie free and a continuum of allocations (`exercise_15_B_9_second`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-! ### Figure 15.B.10(a) -/

/-- Consumer 1's utility in Figure 15.B.10(a): `√x₁ + x₂`. -/
noncomputable def fig10aU1 (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + x 1

/-- Consumer 2's utility in Figure 15.B.10(a): `x₁` (he desires only good 1). -/
def fig10aU2 (x : Fin 2 → ℝ) : ℝ := x 0

/-- **Figure 15.B.10(a)** (MWG, p. 522): `u₁ = √x₁₁ + x₂₁`, `u₂ = x₁₂`, `ω₁ = (0, 1)`,
`ω₂ = (1, 0)`. -/
noncomputable def fig10aEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![fig10aU1, fig10aU2] ![![0, 1], ![1, 0]]

theorem fig10a_u0 : fig10aEconomy.u 0 = fig10aU1 := rfl
theorem fig10a_u1 : fig10aEconomy.u 1 = fig10aU2 := rfl
theorem fig10a_ω0 : fig10aEconomy.ω 0 = ![0, 1] := rfl
theorem fig10a_ω1 : fig10aEconomy.ω 1 = ![1, 0] := rfl

/-- Consumer 1's utility in Figure 15.B.10(a) is locally nonsatiated. -/
theorem fig10a_lns0 : UtilityLNS fig10aU1 :=
  exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => by
    refine ⟨?_, ?_⟩ <;> simp only [utilityPref, fig10aU1, not_le] <;>
      linarith [Real.sqrt_le_sqrt (hxy 0).le, hxy 1]

/-- Consumer 2's utility in Figure 15.B.10(a) is locally nonsatiated. -/
theorem fig10a_lns1 : UtilityLNS fig10aU2 :=
  exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => by
    refine ⟨?_, ?_⟩ <;> simp only [utilityPref, fig10aU2, not_le] <;> linarith [hxy 0]

/-- The utilities of `fig10aEconomy` are locally nonsatiated. -/
theorem fig10a_lns (i : Fin 2) : UtilityLNS (fig10aEconomy.u i) := by
  fin_cases i
  · exact fig10a_lns0
  · exact fig10a_lns1

/-- **Figure 15.B.10(a)** (MWG, p. 522): consumer 2's preferences are not strongly monotone. -/
theorem fig_15_B_10a_not_stronglyMonotone : ¬ UtilityStronglyMonotone (fig10aEconomy.u 1) := by
  intro h
  have := h.lt (x := 0) (y := Pi.single 1 1) (fun l => le_refl _) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  simp [fig10a_u1, fig10aU2] at this

theorem fig10a_dot (p z : Fin 2 → ℝ) : p ⬝ᵥ z = p 0 * z 0 + p 1 * z 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- **Figure 15.B.10(a)** (MWG, p. 522): at `p ≫ 0` consumer 2's demand is his endowment. -/
theorem fig_15_B_10a_demand1 {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    fig10aEconomy.demand 1 p = {![1, 0]} := by
  have hω : p ⬝ᵥ fig10aEconomy.ω 1 = p 0 := by simp [fig10a_ω1, Matrix.vecHead]
  have hp0 := hp 0
  have hp1 := hp 1
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hb⟩, hmax⟩
    rw [hω, fig10a_dot] at hb
    have hmem : (![1, 0] : Fin 2 → ℝ) ∈ budgetSetOn (fig10aEconomy.X 1) p
        (p ⬝ᵥ fig10aEconomy.ω 1) := ⟨fun l => by fin_cases l <;> simp, by
          rw [hω, fig10a_dot]; simp⟩
    have h1 := hmax _ hmem
    simp only [fig10a_u1, fig10aU2, Matrix.cons_val_zero] at h1
    have hy0 := hy 0
    have hy1 := hy 1
    have e0 : y 0 = 1 := by nlinarith
    have e1 : y 1 = 0 := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨⟨fun l => by fin_cases l <;> simp, by rw [hω, fig10a_dot]; simp⟩, fun z hz => ?_⟩
    have hb := hz.2
    rw [hω, fig10a_dot] at hb
    simp only [fig10a_u1, fig10aU2, Matrix.cons_val_zero]
    nlinarith [hz.1 1]

/-- **Figure 15.B.10(a)** (MWG, p. 522): at `p ≫ 0` consumer 1's endowment `(0, 1)` is not optimal:
`(ε, 1 - kε)`, `k = p₁/p₂`, `ε = 1/(4(k+1)²)`, is affordable and strictly better. -/
theorem fig_15_B_10a_endowment_not_optimal {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    fig10aEconomy.ω 0 ∉ fig10aEconomy.demand 0 p := by
  rintro ⟨-, hmax⟩
  set k := p 0 / p 1 with hk
  have hk0 : 0 < k := div_pos (hp 0) (hp 1)
  set ε := 1 / (4 * (k + 1) ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hsq : Real.sqrt ε = 1 / (2 * (k + 1)) := by
    rw [hε, show 4 * (k + 1) ^ 2 = (2 * (k + 1)) ^ 2 by ring, one_div, Real.sqrt_inv,
      Real.sqrt_sq (by positivity), one_div]
  have hkε : k * ε ≤ 1 / 4 := by
    rw [hε, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcost : p 1 * (k * ε) = p 0 * ε := by
    rw [hk]
    field_simp [(hp 1).ne']
  set y : Fin 2 → ℝ := ![ε, 1 - k * ε] with hy
  have hmem : y ∈ budgetSetOn (fig10aEconomy.X 0) p (p ⬝ᵥ fig10aEconomy.ω 0) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa [hy] using hε0.le
      · simp only [hy]
        simp
        linarith
    · rw [fig10a_dot, fig10a_dot, fig10a_ω0, hy]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith
  have h1 := hmax y hmem
  rw [fig10a_u0, fig10a_ω0, hy] at h1
  simp only [fig10aU1, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_zero,
    zero_add] at h1
  rw [hsq] at h1
  have : k * ε < 1 / (2 * (k + 1)) := by
    rw [hε, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **Figure 15.B.10(a)** (MWG, p. 522): consumer 1's demand for good 2 is unbounded when
`p₂ = 0`: for `p₂ ≤ 0` he has no demand. -/
theorem fig_15_B_10a_no_demand0 {p : Fin 2 → ℝ} (hp1 : p 1 ≤ 0) :
    fig10aEconomy.demand 0 p = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hy, hb⟩, hmax⟩
  have hmem : y + Pi.single 1 1 ∈ budgetSetOn (fig10aEconomy.X 0) p
      (p ⬝ᵥ fig10aEconomy.ω 0) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hy 0
      · simp; linarith [hy 1]
    · rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      linarith
  have := hmax _ hmem
  simp [fig10a_u0, fig10aU1] at this
  linarith

/-- **Figure 15.B.10(a)** (MWG, p. 522): there is no Walrasian equilibrium (Definition 15.B.1). -/
theorem fig_15_B_10a_no_eqm (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    ¬ fig10aEconomy.IsWalrasEqm p x := by
  intro h
  rw [isWalrasEqm_iff_isDemandEqm (fun _ => rfl) fig10a_lns] at h
  obtain ⟨hbox, hd⟩ := h
  by_cases hp0 : 0 < p 0
  · by_cases hp1 : 0 < p 1
    · have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
      have h1 := hd 1
      rw [fig_15_B_10a_demand1 hp, Set.mem_singleton_iff] at h1
      have h0 : x 0 = fig10aEconomy.ω 0 := by
        have hs := hbox.2
        simp only [Fin.sum_univ_two, ExchangeEconomy.totalEndowment] at hs
        rw [h1, fig10a_ω0, fig10a_ω1] at hs
        rw [fig10a_ω0]
        funext l
        have := congrFun hs l
        fin_cases l <;> simp at this ⊢ <;> linarith
      exact fig_15_B_10a_endowment_not_optimal hp (h0 ▸ hd 0)
    · have := hd 0
      rw [fig_15_B_10a_no_demand0 (not_lt.1 hp1)] at this
      exact this
  · -- good 1 is free for consumer 2
    rw [not_lt] at hp0
    obtain ⟨⟨hy, hb⟩, hmax⟩ := hd 1
    have hmem : x 1 + Pi.single 0 1 ∈ budgetSetOn (fig10aEconomy.X 1) p
        (p ⬝ᵥ fig10aEconomy.ω 1) := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simp; linarith [hy 0]
        · simpa using hy 1
      · rw [dotProduct_add]
        simp only [dotProduct_single, mul_one]
        linarith
    have := hmax _ hmem
    simp [fig10a_u1, fig10aU2] at this
    linarith

/-- **Section 15.B** (MWG, p. 525), Figure 15.B.10(a): the endowment allocation is Pareto optimal
but cannot be supported as an equilibrium with transfers. -/
theorem fig_15_B_10a_po_not_supportable :
    fig10aEconomy.IsParetoOptimal fig10aEconomy.ω ∧
      ¬ fig10aEconomy.IsSupportable fig10aEconomy.ω := by
  have hbox : fig10aEconomy.InBox fig10aEconomy.ω :=
    ⟨fun i l => by fin_cases i <;> fin_cases l <;> simp [fig10aEconomy,
      ExchangeEconomy.ofOrthant], rfl⟩
  refine ⟨⟨hbox, ?_⟩, ?_⟩
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs := hx'.2
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
      fig10a_ω0, fig10a_ω1] at hs0 hs1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h1 := hle 1
    have h0 := hle 0
    rw [fig10a_u1, fig10a_ω1] at h1
    rw [fig10a_u0, fig10a_ω0] at h0
    simp only [fig10aU1, fig10aU2, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_zero,
      zero_add] at h0 h1
    have e : x' 0 0 = 0 := by linarith [hm 0 0]
    have hsq : Real.sqrt (x' 0 0) = 0 := by rw [e, Real.sqrt_zero]
    fin_cases i
    · simp only [Fin.zero_eta, fig10a_u0, fig10a_ω0, fig10aU1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Real.sqrt_zero, zero_add, hsq] at hi
      linarith [hm 1 1]
    · simp only [Fin.mk_one, fig10a_u1, fig10a_ω1, fig10aU2, Matrix.cons_val_zero] at hi
      linarith [hm 0 0]
  · rintro ⟨p, T, h⟩
    have hT : ∀ i, T i = 0 := fun i => by
      have := h.wealth_eq (fun _ => rfl) fig10a_lns i
      linarith
    apply fig_15_B_10a_no_eqm p fig10aEconomy.ω
    refine ⟨hbox, fun i y hy => h.2.2 i y hy.1 ?_⟩
    rw [hT i, add_zero]
    exact hy.2

/-! ### Figure 15.B.10(b) and Figure 15.B.14: a nonconvex consumer -/

/-- The nonconvex utility `x₁² + x₂²`. -/
def sqUtility (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- On `ℝ²₊`, `x₁² + x₂²` is continuous and strongly monotone but not quasiconcave. -/
theorem sqUtility_props : ContinuousOn sqUtility (nonnegOrthant 2) ∧
    UtilityStronglyMonotone sqUtility ∧ ¬ PrefConvex (nonnegOrthant 2) (utilityPref sqUtility) :=
  by
  refine ⟨by unfold sqUtility; fun_prop, fun x hx y hy hxy hne => ⟨?_, ?_⟩, fun h => ?_⟩
  · simp only [utilityPref, sqUtility]
    nlinarith [hxy 0, hxy 1, hx 0, hx 1]
  · simp only [utilityPref, sqUtility, not_le]
    have hl : x 0 < y 0 ∨ x 1 < y 1 := by
      by_contra hall
      simp only [not_or, not_lt] at hall
      exact hne (funext fun l => by
        fin_cases l
        · exact le_antisymm hall.1 (hxy 0)
        · exact le_antisymm hall.2 (hxy 1))
    rcases hl with hl | hl
    · nlinarith [hxy 0, hxy 1, hx 0, hx 1]
    · nlinarith [hxy 0, hxy 1, hx 0, hx 1]
  · have := quasiconcave_of_prefConvex h (y := ![1, 0]) (z := ![0, 1])
      (fun l => by fin_cases l <;> simp) (fun l => by fin_cases l <;> simp)
      (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    simp [sqUtility] at this
    norm_num at this

/-- The demand of the `x₁² + x₂²` consumer at `p ≫ 0` and wealth `w ≥ 0` consists of corner
bundles: `x₁x₂ = 0` and `x₁ + x₂ = w / min p`. -/
theorem sqUtility_demand_corner {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w)
    {x : Fin 2 → ℝ} (hx : x ∈ walrasianDemand sqUtility p w) :
    x 0 * x 1 = 0 ∧ x 0 + x 1 = w / min (p 0) (p 1) := by
  set m := min (p 0) (p 1) with hm
  have hm0 : 0 < m := lt_min (hp 0) (hp 1)
  obtain ⟨⟨hx0, hb⟩, hmax⟩ := hx
  have hb' : p 0 * x 0 + p 1 * x 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hb
  -- the corner of the cheaper good
  have hcorner : (w / m) ^ 2 ≤ sqUtility x := by
    rcases le_total (p 0) (p 1) with h | h
    · have hmeq : m = p 0 := min_eq_left h
      have := hmax ![w / m, 0] ⟨fun l => by fin_cases l <;> simp [div_nonneg hw hm0.le],
        by simp [dotProduct, Fin.sum_univ_two, hmeq, mul_div_cancel₀ _ (hp 0).ne']⟩
      simpa [sqUtility] using this
    · have hmeq : m = p 1 := min_eq_right h
      have := hmax ![0, w / m] ⟨fun l => by fin_cases l <;> simp [div_nonneg hw hm0.le],
        by simp [dotProduct, Fin.sum_univ_two, hmeq, mul_div_cancel₀ _ (hp 1).ne']⟩
      simpa [sqUtility] using this
  have hsum : x 0 + x 1 ≤ w / m := by
    rw [le_div_iff₀ hm0]
    have h0 : m ≤ p 0 := min_le_left _ _
    have h1 : m ≤ p 1 := min_le_right _ _
    nlinarith [hx0 0, hx0 1]
  have hsq : sqUtility x ≤ (x 0 + x 1) ^ 2 := by
    simp only [sqUtility]
    nlinarith [hx0 0, hx0 1]
  have hpow : (x 0 + x 1) ^ 2 ≤ (w / m) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg (hx0 0) (hx0 1)) hsum 2
  have heq : (x 0 + x 1) ^ 2 = (w / m) ^ 2 := le_antisymm hpow (hcorner.trans hsq)
  refine ⟨?_, ?_⟩
  · simp only [sqUtility] at hsq hcorner
    nlinarith [hx0 0, hx0 1]
  · exact (pow_left_inj₀ (add_nonneg (hx0 0) (hx0 1)) (div_nonneg hw hm0.le)
      two_ne_zero).1 heq

/-- **Figure 15.B.10(b)** (MWG, p. 522): a nonconvex consumer 1 (`x₁₁² + x₂₁²`) and a Cobb-Douglas
consumer 2 (`x₁₂^{1/2}x₂₂^{1/2}`), both with endowment `(1, 1)`. -/
noncomputable def fig10bEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![sqUtility, cobbDouglasUtility 1 (1 / 2)] ![![1, 1], ![1, 1]]

/-- **Figure 15.B.10(b)** (MWG, p. 522): the economy with a nonconvex consumer has no Walrasian
equilibrium. -/
theorem fig_15_B_10b_no_eqm (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    ¬ fig10bEconomy.IsDemandEqm p x := by
  rintro ⟨hbox, hd⟩
  have hω : ∀ l, (0 : ℝ) < fig10bEconomy.ω 1 l := fun l => by
    fin_cases l <;> simp [fig10bEconomy, ExchangeEconomy.ofOrthant]
  have hd1 := hd 1
  have hdem1 : fig10bEconomy.demand 1 p = walrasianDemand (cobbDouglasUtility 1 (1 / 2)) p
      (p ⬝ᵥ fig10bEconomy.ω 1) := rfl
  by_cases hp : StrictlyPositive p
  · have hw : p ⬝ᵥ fig10bEconomy.ω 1 = p 0 + p 1 := by
      simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
    have hw0 : p ⬝ᵥ fig10bEconomy.ω 0 = p 0 + p 1 := by
      simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
    rw [hdem1, example_3_D_1 one_pos (by norm_num) (by norm_num) hp
      (by rw [hw]; linarith [hp 0, hp 1]), Set.mem_singleton_iff, hw] at hd1
    have hd0 : x 0 ∈ walrasianDemand sqUtility p (p 0 + p 1) := by
      rw [← hw0]
      exact hd 0
    obtain ⟨hc0, hc1⟩ := sqUtility_demand_corner hp (by linarith [hp 0, hp 1]) hd0
    have hs := hbox.2
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
      fig10bEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hs0 hs1
    rw [hd1] at hs0 hs1
    simp only [cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hp0 := hp 0
    have hp1 := hp 1
    have hx := (hd 0).1.1
    have hbud : p 0 * x 0 0 + p 1 * x 0 1 ≤ p 0 + p 1 := by
      have := hd0.1.2
      simpa [dotProduct, Fin.sum_univ_two] using this
    rcases le_total (p 0) (p 1) with h | h
    · rw [min_eq_left h] at hc1
      rcases mul_eq_zero.1 hc0 with h0 | h0
      · -- consumer 1 takes only good 2
        rw [h0, zero_add] at hc1
        rw [h0, zero_add] at hs0
        rw [h0] at hbud
        field_simp at hs0
        rw [hc1] at hbud
        have : p 1 * ((p 0 + p 1) / p 0) * p 0 ≤ (p 0 + p 1) * p 0 := by nlinarith
        rw [mul_assoc, div_mul_cancel₀ _ hp0.ne'] at this
        nlinarith
      · rw [h0, add_zero] at hc1
        rw [hc1] at hs0
        field_simp at hs0
        nlinarith
    · rw [min_eq_right h] at hc1
      rcases mul_eq_zero.1 hc0 with h0 | h0
      · rw [h0, zero_add] at hc1
        rw [hc1] at hs1
        field_simp at hs1
        nlinarith
      · rw [h0, add_zero] at hc1
        rw [h0, zero_add] at hs1
        rw [h0] at hbud
        field_simp at hs1
        rw [hc1] at hbud
        have : p 0 * ((p 0 + p 1) / p 1) * p 1 ≤ (p 0 + p 1) * p 1 := by nlinarith
        rw [mul_assoc, div_mul_cancel₀ _ hp1.ne'] at this
        nlinarith
  · rcases cd_demand_empty (α := 1 / 2) (β := 1 / 2) (ω := fig10bEconomy.ω) (i := 1)
      ⟨by norm_num [cdExponent], by norm_num [cdExponent]⟩ hp hω |> fun h => (by
        have e : (cdEconomy (1 / 2) (1 / 2) fig10bEconomy.ω).demand 1 p =
            fig10bEconomy.demand 1 p := rfl
        rw [← e, h] at hd1
        exact hd1 : False) with ⟨⟩

/-- **Figure 15.B.14** (MWG, p. 525): consumer 1 is nonconvex (`x₁₁² + x₂₁²`), consumer 2 has the
convex, kinked utility `min(3x₁₂ + x₂₂, x₁₂ + 3x₂₂)`; both endowments are `(1, 1)`. -/
noncomputable def fig14Economy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![sqUtility, fun x => min (3 * x 0 + x 1) (x 0 + 3 * x 1)]
    ![![1, 1], ![1, 1]]

/-- Consumer 2 of Figure 15.B.14 has continuous, convex and strongly monotone preferences. -/
theorem fig14_u2_props :
    ContinuousOn (fig14Economy.u 1) (nonnegOrthant 2) ∧
      PrefConvex (nonnegOrthant 2) (utilityPref (fig14Economy.u 1)) ∧
      UtilityStronglyMonotone (fig14Economy.u 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    fun_prop
  · intro z _ a ha b hb s t hs ht hst
    refine ⟨convex_nonnegOrthant 2 ha.1 hb.1 hs ht hst, ?_⟩
    have h1 := ha.2
    have h2 := hb.2
    simp only [utilityPref, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, le_min_iff] at h1 h2 ⊢
    set m := min (3 * z 0 + z 1) (z 0 + 3 * z 1)
    have hm : m = s * m + t * m := by rw [← add_mul, hst, one_mul]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1.1 hs, mul_le_mul_of_nonneg_left h1.2 hs,
      mul_le_mul_of_nonneg_left h2.1 ht, mul_le_mul_of_nonneg_left h2.2 ht]
  · intro x hx y hy hxy hne
    simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    have hl : x 0 < y 0 ∨ x 1 < y 1 := by
      by_contra hall
      simp only [not_or, not_lt] at hall
      exact hne (funext fun l => by
        fin_cases l
        · exact le_antisymm hall.1 (hxy 0)
        · exact le_antisymm hall.2 (hxy 1))
    have h0 := hxy 0
    have h1 := hxy 1
    refine ⟨min_le_min (by linarith) (by linarith), ?_⟩
    exact not_le.2 <| lt_min (min_lt_of_left_lt (by rcases hl with hl | hl <;> linarith :
        3 * x 0 + x 1 < 3 * y 0 + y 1))
      (min_lt_of_right_lt (by rcases hl with hl | hl <;> linarith :
        x 0 + 3 * x 1 < y 0 + 3 * y 1))

/-- The utilities of Figure 15.B.14 are locally nonsatiated. -/
theorem fig14_lns (i : Fin 2) : UtilityLNS (fig14Economy.u i) := by
  fin_cases i
  · exact sqUtility_props.2.1.lns two_pos
  · exact fig14_u2_props.2.2.lns two_pos

/-- **Figure 15.B.14** (MWG, p. 525). The allocation `x* = ((1,1),(1,1))` is Pareto optimal, but it
is not supportable as an equilibrium with transfers: at every supporting budget line the
nonconvex consumer 1 prefers a corner bundle. All preferences are continuous and strongly
monotone and consumer 2's are convex; only the convexity of consumer 1's fails. -/
theorem fig_15_B_14 : fig14Economy.IsParetoOptimal fig14Economy.ω ∧
    ¬ fig14Economy.IsSupportable fig14Economy.ω := by
  have hω0 : fig14Economy.ω 0 = ![1, 1] := rfl
  have hω1 : fig14Economy.ω 1 = ![1, 1] := rfl
  have hu0 : fig14Economy.u 0 = sqUtility := rfl
  have hbox : fig14Economy.InBox fig14Economy.ω :=
    ⟨fun i l => by fin_cases i <;> fin_cases l <;> simp [fig14Economy,
      ExchangeEconomy.ofOrthant], rfl⟩
  refine ⟨⟨hbox, ?_⟩, ?_⟩
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs0 := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment, hω0, hω1,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h1 := hle 1
    have h0 := hle 0
    simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one, sqUtility, le_min_iff] at h0 h1
    norm_num at h0 h1
    set a := x' 0 0
    set b := x' 0 1
    have ha := hm 0 0
    have hb := hm 0 1
    have c1 : 3 * a + b ≤ 4 := by nlinarith [h1.1]
    have c2 : a + 3 * b ≤ 4 := by nlinarith [h1.2]
    have hu : (a + b - 2) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - 3 * a - b) ha,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - a - 3 * b) hb]
    have hab : a + b = 2 := by nlinarith [sq_nonneg (a + b - 2)]
    have hd : (a - b) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - 3 * a - b) ha,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - a - 3 * b) hb]
    have hab' : a = b := by nlinarith [sq_nonneg (a - b)]
    have e0 : a = 1 := by linarith
    have e1 : b = 1 := by linarith
    have f0 : x' 1 0 = 1 := by linarith
    have f1 : x' 1 1 = 1 := by linarith
    fin_cases i
    · simp only [Fin.zero_eta, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        sqUtility] at hi
      rw [show x' 0 0 = a from rfl, show x' 0 1 = b from rfl, e0, e1] at hi
      norm_num at hi
    · simp only [Fin.mk_one, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hi
      rw [f0, f1] at hi
      norm_num at hi
  · rintro ⟨p, T, h⟩
    have hT : T 0 = 0 := by
      have := h.wealth_eq (fun _ => rfl) fig14_lns 0
      linarith
    have hopt : ∀ y ∈ nonnegOrthant 2, p 0 * y 0 + p 1 * y 1 ≤ p 0 + p 1 → sqUtility y ≤ 2 := by
      intro y hy hb
      have := h.2.2 0 y hy (by
        rw [hT, add_zero, hω0]
        simpa [dotProduct, Fin.sum_univ_two] using hb)
      rw [hu0, hω0] at this
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      norm_num at this
      simpa [sqUtility] using this
    by_cases hp0 : p 0 ≤ 0
    · have := hopt ![2, 1] (fun l => by fin_cases l <;> norm_num) (by simp; linarith)
      norm_num [sqUtility] at this
    by_cases hp1 : p 1 ≤ 0
    · have := hopt ![1, 2] (fun l => by fin_cases l <;> norm_num) (by simp; linarith)
      norm_num [sqUtility] at this
    rw [not_le] at hp0 hp1
    rcases le_total (p 0) (p 1) with hle | hle
    · have hk : 2 ≤ (p 0 + p 1) / p 0 := by rw [le_div_iff₀ hp0]; linarith
      have := hopt ![(p 0 + p 1) / p 0, 0]
        (fun l => by
          fin_cases l <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> positivity)
        (by simp [mul_div_cancel₀ _ hp0.ne'])
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      nlinarith
    · have hk : 2 ≤ (p 0 + p 1) / p 1 := by rw [le_div_iff₀ hp1]; linarith
      have := hopt ![0, (p 0 + p 1) / p 1]
        (fun l => by
          fin_cases l <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> positivity)
        (by simp [mul_div_cancel₀ _ hp1.ne'])
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      nlinarith

/-! ### Exercise 15.B.9 -/

/-- Alphanse's utility `min(x_P, x_B)` (goods: Perrier, Brie). -/
def alphanseU (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1)

/-- Betatrix's utility `min(x_B, √x_P)`. -/
noncomputable def betatrixU (x : Fin 2 → ℝ) : ℝ := min (x 1) (Real.sqrt (x 0))

/-- **Exercise 15.B.9** (MWG, p. 541). Alphanse owns `e` units of Perrier, Betatrix 20 units of
Brie. -/
noncomputable def ex15B9Economy (e : ℝ) : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![alphanseU, betatrixU] ![![e, 0], ![0, 20]]

/-- Alphanse's demand at `p ≫ 0` and wealth `w ≥ 0`: the single bundle `(k, k)`,
`k = w/(p_P + p_B)`. -/
theorem alphanse_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand alphanseU p w = {![w / (p 0 + p 1), w / (p 0 + p 1)]} := by
  have hp0 := hp 0
  have hp1 := hp 1
  set k := w / (p 0 + p 1) with hk
  have hk0 : 0 ≤ k := div_nonneg hw (by linarith)
  have hkw : (p 0 + p 1) * k = w := by rw [hk]; field_simp
  have hmem : (![k, k] : Fin 2 → ℝ) ∈ budgetSet p w :=
    ⟨fun l => by fin_cases l <;> simpa, by simp [dotProduct, Fin.sum_univ_two]; linarith⟩
  have hbound : ∀ y ∈ budgetSet p w, alphanseU y ≤ k := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.2
    by_contra hlt
    rw [not_le, alphanseU, lt_min_iff] at hlt
    nlinarith
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    have h1 := hy.2 _ hmem
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.1.2
    simp only [alphanseU, Matrix.cons_val_zero, Matrix.cons_val_one, min_self, le_min_iff] at h1
    have e0 : y 0 = k := by nlinarith
    have e1 : y 1 = k := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    have hval : alphanseU ![k, k] = k := by simp [alphanseU]
    exact ⟨hmem, fun z hz => by rw [hval]; exact hbound z hz⟩

/-- Betatrix's demand at `p ≫ 0` and wealth `w`, where `s ≥ 0` solves `p_P s² + p_B s = w`: the
single bundle `(s², s)`. -/
theorem betatrix_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w s : ℝ} (hs : 0 ≤ s)
    (hsw : p 0 * s ^ 2 + p 1 * s = w) : walrasianDemand betatrixU p w = {![s ^ 2, s]} := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hmem : (![s ^ 2, s] : Fin 2 → ℝ) ∈ budgetSet p w :=
    ⟨fun l => by fin_cases l <;> simp [hs], by
      simp [dotProduct, Fin.sum_univ_two]; linarith⟩
  have husx : betatrixU ![s ^ 2, s] = s := by
    simp [betatrixU, Real.sqrt_sq hs]
  -- every affordable bundle has `m = min(y_B, √y_P) ≤ s`
  have hbound : ∀ y ∈ budgetSet p w, betatrixU y ≤ s ∧ (betatrixU y = s → y = ![s ^ 2, s]) := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.2
    have hy0 := hy.1 0
    have hy1 := hy.1 1
    set m := betatrixU y with hm
    have hm1 : m ≤ y 1 := min_le_left _ _
    have hm2 : m ≤ Real.sqrt (y 0) := min_le_right _ _
    have hm0 : 0 ≤ m := le_min hy1 (Real.sqrt_nonneg _)
    have hm2' : m ^ 2 ≤ y 0 := by
      calc m ^ 2 ≤ Real.sqrt (y 0) ^ 2 := pow_le_pow_left₀ hm0 hm2 2
        _ = y 0 := Real.sq_sqrt hy0
    have hcost : p 0 * m ^ 2 + p 1 * m ≤ p 0 * s ^ 2 + p 1 * s := by nlinarith
    have hms : m ≤ s := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos hp0 (mul_pos (by linarith : (0 : ℝ) < m - s) (by linarith : 0 < m + s))]
    refine ⟨hms, fun heq => ?_⟩
    rw [heq] at hm1 hm2'
    have e1 : y 1 = s := by nlinarith
    have e0 : y 0 = s ^ 2 := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    have h1 := hy.2 _ hmem
    rw [husx] at h1
    exact (hbound y hy.1).2 (le_antisymm (hbound y hy.1).1 h1)
  · rintro rfl
    exact ⟨hmem, fun z hz => by rw [husx]; exact (hbound z hz).1⟩

/-- Alphanse's and Betatrix's preferences are locally nonsatiated. -/
theorem ex15B9_lns (e : ℝ) (i : Fin 2) : UtilityLNS ((ex15B9Economy e).u i) := by
  fin_cases i
  · exact exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => ⟨by
      simp only [utilityPref]
      exact min_le_min (hxy 0).le (hxy 1).le, by
      simp only [utilityPref, not_le]
      exact lt_min (min_lt_of_left_lt (hxy 0)) (min_lt_of_right_lt (hxy 1))⟩
  · exact exercise_3_B_1b_orthant two_pos fun x hx y _ hxy => ⟨by
      simp only [utilityPref]
      exact min_le_min (hxy 1).le (Real.sqrt_le_sqrt (hxy 0).le), by
      simp only [utilityPref, not_le]
      exact lt_min (min_lt_of_left_lt (hxy 1))
        (min_lt_of_right_lt (Real.sqrt_lt_sqrt (hx 0) (hxy 0)))⟩

/-- In the Alphanse-Betatrix economy with `e ≤ 30` units of Perrier, equilibrium prices of
Perrier are positive: otherwise Betatrix affords `(401, 20)`, worth `20 > √30`. -/
theorem ex15B9_p0_pos {e : ℝ} (he : e ≤ 30) {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : (ex15B9Economy e).IsDemandEqm p x) : 0 < p 0 := by
  by_contra hp0
  rw [not_lt] at hp0
  obtain ⟨hbox, hd⟩ := h
  have hs0 := congrFun hbox.2 0
  simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
    ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero, Matrix.cons_val_one] at hs0
  have hxa := (hd 0).1.1 0
  have hmem : (![401, 20] : Fin 2 → ℝ) ∈ budgetSetOn ((ex15B9Economy e).X 1) p
      (p ⬝ᵥ (ex15B9Economy e).ω 1) :=
    ⟨fun l => by fin_cases l <;> norm_num, by
      simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
      nlinarith⟩
  have h1 := (hd 1).2 _ hmem
  have hsq : Real.sqrt 401 ≥ 20 := by
    rw [ge_iff_le, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hval : (ex15B9Economy e).u 1 ![401, 20] = 20 := by
    simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero, betatrixU]
    exact min_eq_left hsq
  rw [hval] at h1
  have hle : (ex15B9Economy e).u 1 (x 1) ≤ Real.sqrt (x 1 0) := min_le_right _ _
  have h30 : Real.sqrt (x 1 0) ≤ Real.sqrt 30 := Real.sqrt_le_sqrt (by linarith)
  have : Real.sqrt 30 < 20 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- A nonnegative root of `a r² + b r = w` for `a > 0`, `b, w ≥ 0`. -/
theorem quad_root_nonneg {a b w : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    ∃ r, 0 ≤ r ∧ a * r ^ 2 + b * r = w := by
  set D := b ^ 2 + 4 * a * w with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨(-b + Real.sqrt D) / (2 * a), ?_, ?_⟩
  · apply div_nonneg _ (by linarith)
    have : b ≤ Real.sqrt D := by
      rw [Real.le_sqrt hb hD0]
      nlinarith
    linarith
  · have hsD := Real.sq_sqrt hD0
    field_simp
    nlinarith [hsD]

/-- **Exercise 15.B.9** (MWG, p. 541). With 30 units of Perrier for Alphanse the equilibrium is
unique: with `a = (39 - √41)/2 ≈ 16.3`, `p_P/(p_P + p_B) = a/30`, Alphanse consumes `(a, a)` and
Betatrix `(30 - a, 20 - a)` (where `20 - a = √(30 - a) = (1 + √41)/2`). -/
theorem exercise_15_B_9 (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (ex15B9Economy 30).IsDemandEqm p x ↔ StrictlyPositive p ∧
      30 * p 0 = (39 - Real.sqrt 41) / 2 * (p 0 + p 1) ∧
      x = ![![(39 - Real.sqrt 41) / 2, (39 - Real.sqrt 41) / 2],
        ![30 - (39 - Real.sqrt 41) / 2, 20 - (39 - Real.sqrt 41) / 2]] := by
  set a := (39 - Real.sqrt 41) / 2 with ha
  have h41 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have h41b : 6 < Real.sqrt 41 ∧ Real.sqrt 41 < 7 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; norm_num
    · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set s := (1 + Real.sqrt 41) / 2 with hsd
  have hs0 : 0 ≤ s := by rw [hsd]; linarith [h41b.1]
  have hsq : s ^ 2 = s + 10 := by rw [hsd]; nlinarith [h41]
  have has : a = 20 - s := by rw [ha, hsd]; ring
  have hu0 : (ex15B9Economy 30).demand 0 p = walrasianDemand alphanseU p (30 * p 0) := by
    unfold ExchangeEconomy.demand
    congr 1
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hu1 : (ex15B9Economy 30).demand 1 p = walrasianDemand betatrixU p (20 * p 1) := by
    unfold ExchangeEconomy.demand
    congr 1
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have htot : (ex15B9Economy 30).totalEndowment = ![30, 20] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B9Economy,
      ExchangeEconomy.ofOrthant]
  constructor
  · intro h
    have hp0 := ex15B9_p0_pos (by norm_num) h
    obtain ⟨hbox, hd⟩ := h
    have hs1 := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs1
    have hs0' := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs0'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs0'
    have hp1 : 0 < p 1 := by
      by_contra hp1
      rw [not_lt] at hp1
      have h1 := (hd 0).2 ![30, 30] ⟨fun l => by fin_cases l <;> norm_num, by
        simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        nlinarith⟩
      have hb1 := (hd 1).1.1 1
      have : (ex15B9Economy 30).u 0 (x 0) ≤ x 0 1 := min_le_right _ _
      simp [ex15B9Economy, ExchangeEconomy.ofOrthant, alphanseU] at h1 this
      linarith
    have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
    have hd0 := hd 0
    rw [hu0, alphanse_demand hp (by linarith), Set.mem_singleton_iff] at hd0
    -- Betatrix's demand: solve for `t = x_B,B`
    have hd1 := hd 1
    rw [hu1] at hd1
    have ht0 := hd1.1.1 1
    obtain ⟨t, ht, hteq⟩ : ∃ t, 0 ≤ t ∧ x 1 = ![t ^ 2, t] := by
      refine ⟨x 1 1, ht0, ?_⟩
      have hopt := hd1
      -- the optimal bundle is `(t², t)` for the root `t` of `p_P t² + p_B t = 20 p_B`
      obtain ⟨r, hr, hreq⟩ := quad_root_nonneg hp0 hp1.le (by linarith : (0 : ℝ) ≤ 20 * p 1)
      rw [betatrix_demand hp hr hreq, Set.mem_singleton_iff] at hopt
      rw [hopt]
      simp
    rw [hd0, hteq] at hs1 hs0'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs0'
    -- `k + t = 20`, `k + t² = 30`
    have htq : t ^ 2 - t - 10 = 0 := by linarith
    have hts : t = s := by
      have : (t - s) * (t - (1 - Real.sqrt 41) / 2) = 0 := by
        rw [hsd]; nlinarith [h41]
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · have : t = (1 - Real.sqrt 41) / 2 := by linarith
        linarith [h41b.1]
    have hk : 30 * p 0 / (p 0 + p 1) = a := by rw [has]; linarith
    refine ⟨hp, ?_, ?_⟩
    · rw [← hk]
      field_simp
    · funext i l
      fin_cases i <;> fin_cases l <;> simp [hd0, hteq, hts] <;> linarith [hk, has, hsq]
  · rintro ⟨hp, hrel, rfl⟩
    have hp0 := hp 0
    have hp1 := hp 1
    have hk : 30 * p 0 / (p 0 + p 1) = a := by
      rw [div_eq_iff (by linarith)]
      linarith
    have hreq : p 0 * s ^ 2 + p 1 * s = 20 * p 1 := by
      rw [hsq]
      have : s = 20 - a := by linarith
      rw [this]
      nlinarith
    refine ⟨⟨fun i l => ?_, ?_⟩, fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp <;> nlinarith [h41b.1, h41b.2]
    · rw [htot]
      funext l
      fin_cases l <;> simp [Fin.sum_univ_two]
    · fin_cases i
      · change ![a, a] ∈ (ex15B9Economy 30).demand 0 p
        rw [hu0, alphanse_demand hp (by linarith), hk]
        rfl
      · change ![30 - a, 20 - a] ∈ (ex15B9Economy 30).demand 1 p
        rw [hu1, betatrix_demand hp hs0 hreq, Set.mem_singleton_iff]
        funext l
        fin_cases l
        · simp [hsq, has]; ring
        · simp [has]

/-- **Exercise 15.B.9** (MWG, p. 542), second part. If Alphanse owns only 5 units of Perrier, Brie
becomes a free good: the equilibria are exactly `p_B = 0 < p_P` with Alphanse consuming `(5, b)`
and Betatrix `(0, 20 - b)` for any `b ∈ [5, 20]` (Betatrix gets utility 0). -/
theorem exercise_15_B_9_second (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (ex15B9Economy 5).IsDemandEqm p x ↔ p 1 = 0 ∧ 0 < p 0 ∧
      ∃ b, 5 ≤ b ∧ b ≤ 20 ∧ x = ![![5, b], ![0, 20 - b]] := by
  have htot : (ex15B9Economy 5).totalEndowment = ![5, 20] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B9Economy,
      ExchangeEconomy.ofOrthant]
  have hw0 : p ⬝ᵥ (ex15B9Economy 5).ω 0 = 5 * p 0 := by
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hw1 : p ⬝ᵥ (ex15B9Economy 5).ω 1 = 20 * p 1 := by
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have hp0 := ex15B9_p0_pos (by norm_num) h
    obtain ⟨hbox, hd⟩ := h
    have hs0 := congrFun hbox.2 0
    have hs1 := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs0 hs1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hA := hd 0
    have hB := hd 1
    have hxA0 := hA.1.1 0
    have hxA1 := hA.1.1 1
    have hxB0 := hB.1.1 0
    have hxB1 := hB.1.1 1
    have huA : (ex15B9Economy 5).u 0 (x 0) ≤ x 0 0 := min_le_left _ _
    -- the price of Brie is not negative: otherwise Alphanse affords `(6, M)`
    have hp1n : 0 ≤ p 1 := by
      by_contra hp1
      rw [not_le] at hp1
      set M := 6 + p 0 / (-p 1) with hM
      have hM0 : 6 ≤ M := by rw [hM]; have : 0 < p 0 / (-p 1) := div_pos hp0 (by linarith); linarith
      have hcost : p 0 * 6 + p 1 * M ≤ 5 * p 0 := by
        have hne : p 1 ≠ 0 := hp1.ne
        have : p 1 * M = 6 * p 1 - p 0 := by rw [hM]; field_simp; ring
        rw [this]
        linarith
      have h1 := hA.2 ![6, M] ⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
        rw [hw0, hdot]; simpa using hcost⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1 huA
      rw [min_eq_left hM0] at h1
      linarith
    -- and not positive: otherwise `k + t = 20`, `k + t² = 5` is impossible
    have hp1 : p 1 = 0 := by
      by_contra hne
      have hp1 : 0 < p 1 := lt_of_le_of_ne hp1n (Ne.symm hne)
      have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
      obtain ⟨r, hr, hreq⟩ := quad_root_nonneg hp0 hp1.le (by linarith : (0 : ℝ) ≤ 20 * p 1)
      have hd1 := hB
      have hu1 : (ex15B9Economy 5).demand 1 p = walrasianDemand betatrixU p (20 * p 1) := by
        unfold ExchangeEconomy.demand
        rw [hw1]
        rfl
      rw [hu1, betatrix_demand hp hr hreq, Set.mem_singleton_iff] at hd1
      have e10 : x 1 0 = r ^ 2 := by rw [hd1]; rfl
      have e11 : x 1 1 = r := by rw [hd1]; rfl
      rw [e10] at hs0
      rw [e11] at hs1
      have hd0 := hA
      have hu0 : (ex15B9Economy 5).demand 0 p = walrasianDemand alphanseU p (5 * p 0) := by
        unfold ExchangeEconomy.demand
        rw [hw0]
        rfl
      rw [hu0, alphanse_demand hp (by linarith), Set.mem_singleton_iff] at hd0
      have e00 : x 0 0 = x 0 1 := by rw [hd0]; rfl
      nlinarith [sq_nonneg (r - 1 / 2)]
    refine ⟨hp1, hp0, x 0 1, ?_, ?_, ?_⟩
    · -- Alphanse can afford `(5, 20)`
      have h1 := hA.2 ![5, 20] ⟨fun l => by fin_cases l <;> norm_num, by
        rw [hw0, hdot, hp1]; simp [mul_comm]⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1
      norm_num at h1
      exact h1.2
    · linarith
    · have hb := hA.1.2
      rw [hw0, hdot, hp1] at hb
      have hA0 : x 0 0 ≤ 5 := by nlinarith
      have h1 := hA.2 ![5, 20] ⟨fun l => by fin_cases l <;> norm_num, by
        rw [hw0, hdot, hp1]; simp [mul_comm]⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1
      norm_num at h1
      have e00 : x 0 0 = 5 := le_antisymm hA0 h1.1
      have e10 : x 1 0 = 0 := by linarith
      have e11 : x 1 1 = 20 - x 0 1 := by linarith
      funext i l
      fin_cases i <;> fin_cases l <;> simp [e00, e10, e11]
  · rintro ⟨hp1, hp0, b, hb5, hb20, rfl⟩
    refine ⟨⟨fun i l => ?_, ?_⟩, fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp <;> linarith
    · rw [htot]
      funext l
      fin_cases l <;> simp [Fin.sum_univ_two]
    · fin_cases i
      · change ![5, b] ∈ (ex15B9Economy 5).demand 0 p
        refine ⟨⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
          rw [hw0, hdot, hp1]; simp [mul_comm]⟩, fun y hy => ?_⟩
        have hb := hy.2
        rw [hw0, hdot, hp1] at hb
        have hy0 : y 0 ≤ 5 := by nlinarith
        change min (y 0) (y 1) ≤ min 5 b
        rw [min_eq_left hb5]
        exact (min_le_left _ _).trans hy0
      · change ![0, 20 - b] ∈ (ex15B9Economy 5).demand 1 p
        refine ⟨⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
          rw [hw1, hdot, hp1]; simp⟩, fun y hy => ?_⟩
        have hb := hy.2
        rw [hw1, hdot, hp1] at hb
        have hy0 : y 0 = 0 := by nlinarith [hy.1 0]
        change min (y 1) (Real.sqrt (y 0)) ≤ min (20 - b) (Real.sqrt 0)
        rw [hy0, Real.sqrt_zero, min_eq_right (hy.1 1),
          min_eq_right (by linarith : (0 : ℝ) ≤ 20 - b)]

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quasilinear Edgeworth boxes (MWG Exercises 15.B.8 and 15.B.10, pp. 541-542)

* **Exercise 15.B.8**: with continuous, strictly convex preferences quasilinear in good 1
  (`uᵢ = x₁ᵢ + φᵢ(x₂ᵢ)`, `φᵢ` strictly concave, `quasilinear_strictConcave` derives this from strict
  convexity of the preferences), all interior Pareto optimal allocations give each consumer the
  same amount of good 2: it maximizes `φ₁(t) + φ₂(ω̄₂ - t)` (`exercise_15_B_8`), as in Chapter 10
  (the Pareto optimal allocation of the non-numeraire good is independent of the distribution of
  the numeraire).
* **Exercise 15.B.10(a)**: with quasilinear preferences (same numeraire) an increase of consumer
  1's endowment can lower his equilibrium utility (`exercise_15_B_10a`; an example with the
  inelastic demand of `φ(x) = -α/x`).
* **Exercise 15.B.10(b)**: for a transfer `z ≥ 0` from consumer 2 to consumer 1, every equilibrium
  before the transfer gives, at the same prices, an equilibrium after it in which consumer 1 is
  better off by `p·z/p₂` (`exercise_15_B_10b`, with the numeraire unrestricted in sign as in
  Definition 3.B.7). The printed claim that consumer 1's utility cannot decrease is false when the
  equilibrium price is not unique (`exercise_15_B_10b_counterexample`, kinked `φ`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-! ### Exercise 15.B.8 -/

/-- **Exercise 15.B.8** (MWG, p. 541). If preferences on `ℝ²₊` represented by `x₁ + φ(x₂)` are
strictly convex (Definition 3.B.5), then `φ` is strictly concave on `[0, ∞)`. -/
theorem quasilinear_strictConcave {φ : ℝ → ℝ}
    (h : PrefStrictlyConvex (nonnegOrthant 2) (utilityPref fun x => x 0 + φ (x 1))) :
    StrictConcaveOn ℝ (Set.Ici 0) φ := by
  refine ⟨convex_Ici 0, fun a ha b hb hab θ η hθ hη hθη => ?_⟩
  set c := max (φ a) (φ b) with hc
  set y : Fin 2 → ℝ := ![c - φ a, a] with hy
  set z : Fin 2 → ℝ := ![c - φ b, b] with hz
  have hym : y ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hy, hc]
    · simpa [hy] using ha
  have hzm : z ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hz, hc]
    · simpa [hz] using hb
  have hyz : y ≠ z := fun he => hab (by simpa [hy, hz] using congrFun he 1)
  have huy : y 0 + φ (y 1) = c := by simp [hy]
  have huz : z 0 + φ (z 1) = c := by simp [hz]
  have := (h y hym y hym z hzm (le_refl _) (by simp only [utilityPref]; rw [huy, huz]) hyz θ hθ
    (by linarith)).2
  simp only [utilityPref, not_le] at this
  have hη' : η = 1 - θ := by linarith
  subst hη'
  simp only [hy, hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  simp only [smul_eq_mul]
  linarith

/-- **Exercise 15.B.8** (MWG, p. 541). Let `uᵢ(x) = x₁ + φᵢ(x₂)` on `ℝ²₊` with `φᵢ` continuous and
strictly concave on `[0, ∞)`. If `x` and `x'` are Pareto optimal allocations in the interior of the
Edgeworth box, then both consumers consume the same amount of good 2 in `x` and `x'`. -/
theorem exercise_15_B_8 {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    {φ : Fin 2 → ℝ → ℝ} (hu : ∀ i, E.u i = fun x => x 0 + φ i (x 1))
    (hφc : ∀ i, Continuous (φ i)) (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i))
    {x x' : Fin 2 → Fin 2 → ℝ} (hx : E.IsParetoOptimal x) (hx' : E.IsParetoOptimal x')
    (hint : ∀ i l, 0 < x i l) (hint' : ∀ i l, 0 < x' i l) : ∀ i, x i 1 = x' i 1 := by
  set W := E.totalEndowment with hW
  -- the surplus from good 2 when consumer 1 gets `t`
  set S : ℝ → ℝ := fun t => φ 0 t + φ 1 (W 1 - t) with hS
  have hSc : StrictConcaveOn ℝ (Set.Icc 0 (W 1)) S := by
    refine ⟨convex_Icc 0 (W 1), fun a ha b hb hab θ η hθ hη hθη => ?_⟩
    have h0 := (hφ 0).2 (Set.mem_Ici.2 ha.1) (Set.mem_Ici.2 hb.1) hab hθ hη hθη
    have h1 := (hφ 1).concaveOn.2 (Set.mem_Ici.2 (by linarith [ha.2] : (0 : ℝ) ≤ W 1 - a))
      (Set.mem_Ici.2 (by linarith [hb.2] : (0 : ℝ) ≤ W 1 - b)) hθ.le hη.le hθη
    have e : θ • (W 1 - a) + η • (W 1 - b) = W 1 - (θ • a + η • b) := by
      simp only [smul_eq_mul]
      have : W 1 = θ * W 1 + η * W 1 := by rw [← add_mul, hθη, one_mul]
      linarith
    rw [e] at h1
    simp only [hS, smul_eq_mul] at h0 h1 ⊢
    linarith
  -- an interior Pareto optimum maximizes `S`
  have hmax : ∀ y : Fin 2 → Fin 2 → ℝ, E.IsParetoOptimal y → (∀ i l, 0 < y i l) →
      IsMaxOn S (Set.Icc 0 (W 1)) (y 0 1) := by
    intro y hy hyint
    have hs0 : y 0 0 + y 1 0 = W 0 := by
      have := congrFun hy.1.2 0; simpa [Fin.sum_univ_two] using this
    have hs1 : y 0 1 + y 1 1 = W 1 := by
      have := congrFun hy.1.2 1; simpa [Fin.sum_univ_two] using this
    have hmem : y 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hyint 0 1).le, by linarith [hyint 1 1]⟩
    refine IsMaxOn.of_isLocalMaxOn_of_concaveOn hmem ?_ hSc.concaveOn
    -- reallocate good 2 to `(t, W₂ - t)` keeping consumer 2's utility constant
    set g : ℝ → ℝ := fun t => y 1 0 + φ 1 (y 1 1) - φ 1 (W 1 - t) with hg
    have hgc : Continuous g := by fun_prop
    have hg0 : g (y 0 1) = y 1 0 := by simp [hg, ← hs1]
    have hev1 : ∀ᶠ t in 𝓝 (y 0 1), 0 < g t :=
      hgc.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; exact hyint 1 0))
    have hev2 : ∀ᶠ t in 𝓝 (y 0 1), g t < W 0 :=
      hgc.continuousAt.eventually (gt_mem_nhds (by rw [hg0]; linarith [hyint 0 0]))
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
      with t ht1 ht2 htm
    by_contra hlt
    rw [not_le] at hlt
    set y' : Fin 2 → Fin 2 → ℝ := ![![W 0 - g t, t], ![g t, W 1 - t]] with hy'
    apply hy.2
    refine ⟨y', ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, ?_⟩
    · rw [hX i]
      intro l
      fin_cases i <;> fin_cases l <;> simp [hy'] <;> linarith [htm.1, htm.2]
    · funext l
      fin_cases l <;> simp [hy', Fin.sum_univ_two, hW]
    · fin_cases i
      · change E.u 0 (y 0) ≤ E.u 0 (y' 0)
        rw [hu 0]
        simp only [hy', Matrix.cons_val_zero, Matrix.cons_val_one, hg]
        simp only [hS] at hlt
        linarith
      · change E.u 1 (y 1) ≤ E.u 1 (y' 1)
        rw [hu 1]
        simp [hy', hg]
    · rw [hu 0]
      simp only [hy', Matrix.cons_val_zero, Matrix.cons_val_one, hg]
      simp only [hS] at hlt
      linarith
  have h1 := hmax x hx hint
  have h2 := hmax x' hx' hint'
  have hm1 : x 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hint 0 1).le, by
    have := congrFun hx.1.2 1; simp [Fin.sum_univ_two] at this; linarith [hint 1 1]⟩
  have hm2 : x' 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hint' 0 1).le, by
    have := congrFun hx'.1.2 1; simp [Fin.sum_univ_two] at this; linarith [hint' 1 1]⟩
  -- a strictly concave function has at most one maximizer
  have heq : x 0 1 = x' 0 1 := by
    by_contra hne
    have := hSc.2 hm1 hm2 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    have hmid := h1 (hSc.1 hm1 hm2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    have hle : S (x 0 1) ≤ S (x' 0 1) := h2 hm1
    have hle' : S (x' 0 1) ≤ S (x 0 1) := h1 hm2
    have hmid' : S (1 / 2 * x 0 1 + 1 / 2 * x' 0 1) ≤ S (x 0 1) := by
      simpa [smul_eq_mul] using hmid
    simp only [smul_eq_mul] at this
    linarith
  intro i
  fin_cases i
  · exact heq
  · have a := congrFun hx.1.2 1
    have b := congrFun hx'.1.2 1
    simp [Fin.sum_univ_two] at a b
    simp only [Fin.mk_one]
    linarith

/-- An instance of the hypotheses of `exercise_15_B_8`: `uᵢ = x₁ + √x₂`, endowments `(1, 1)` each;
the allocation `((1, 1), (1, 1))` is Pareto optimal and interior. -/
noncomputable def sqrtQLEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ x => x 0 + Real.sqrt (x 1)) (fun _ => ![1, 1])

theorem sqrtQLEconomy_instance : sqrtQLEconomy.IsParetoOptimal (fun _ => ![1, 1]) ∧
    StrictConcaveOn ℝ (Set.Ici 0) Real.sqrt ∧ Continuous Real.sqrt := by
  refine ⟨⟨⟨fun i l => by fin_cases l <;> simp, ?_⟩,
    ?_⟩, Real.strictConcaveOn_sqrt, Real.continuous_sqrt⟩
  · rfl
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs0 := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    simp [ExchangeEconomy.totalEndowment, sqrtQLEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h0 := hle 0
    have h1 := hle 1
    simp only [sqrtQLEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.sqrt_one] at h0 h1 hi
    -- `√t + √(2 - t) ≤ 2`
    have hsq := Real.sq_sqrt (hm 0 1)
    have hsq' := Real.sq_sqrt (hm 1 1)
    have hkey : Real.sqrt (x' 0 1) + Real.sqrt (x' 1 1) ≤ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (x' 0 1) - Real.sqrt (x' 1 1)),
        Real.sqrt_nonneg (x' 0 1), Real.sqrt_nonneg (x' 1 1)]
    fin_cases i <;> simp at hi <;> linarith

/-! ### Exercise 15.B.10 -/

/-- Demand of the quasilinear consumer `u = -α/x₁ + x₂` on `{x₁ > 0, x₂ ≥ 0}` at prices `(p, 1)`:
if `c > 0` solves `p c² = α` and `w ≥ p c`, the unique demanded bundle is `(c, w - p c)`. -/
theorem invQL_demand {α p w c : ℝ} (hp : 0 < p) (hc : 0 < c) (hfoc : p * c ^ 2 = α)
    (hw : p * c ≤ w) :
    walrasianDemandOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1} (fun x => -(α / x 0) + x 1) ![p, 1] w =
      {![c, w - p * c]} := by
  have hα : 0 < α := by rw [← hfoc]; positivity
  have hdot : ∀ y : Fin 2 → ℝ, (![p, 1] : Fin 2 → ℝ) ⬝ᵥ y = p * y 0 + y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  -- `α/y + p y ≥ α/c + p c`, with equality only at `y = c`
  have key : ∀ y : ℝ, 0 < y → α / c + p * c ≤ α / y + p * y ∧
      (α / y + p * y = α / c + p * c → y = c) := by
    intro y hy
    have e : α / y + p * y - (α / c + p * c) = p * (c - y) ^ 2 / y := by
      rw [← hfoc]; field_simp; ring
    refine ⟨by have : 0 ≤ p * (c - y) ^ 2 / y := by positivity
               linarith, fun heq => ?_⟩
    have : p * (c - y) ^ 2 / y = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · have := (mul_eq_zero.1 h).resolve_left hp.ne'
      nlinarith [sq_nonneg (c - y)]
    · linarith
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hb⟩, hmax⟩
    rw [hdot] at hb
    have hmem : (![c, w - p * c] : Fin 2 → ℝ) ∈ budgetSetOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1}
        ![p, 1] w := ⟨⟨by simpa using hc, by simp; linarith⟩, by rw [hdot]; simp⟩
    have h1 := hmax _ hmem
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    obtain ⟨k1, k2⟩ := key (y 0) hy.1
    have e0 : y 0 = c := k2 (by linarith)
    have e1 : y 1 = w - p * c := by
      rw [e0] at hb h1; linarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨⟨⟨by simpa using hc, by simp; linarith⟩, by rw [hdot]; simp⟩, fun z hz => ?_⟩
    have hb := hz.2
    rw [hdot] at hb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [(key (z 0) hz.1.1).1]

/-- Membership form of `invQL_demand` with endowment `(e₀, e₁)`. -/
theorem invQL_mem {α p e0 e1 c : ℝ} (hp : 0 < p) (hc : 0 < c) (hfoc : p * c ^ 2 = α)
    (hw : p * c ≤ p * e0 + e1) :
    (![c, e1 + p * (e0 - c)] : Fin 2 → ℝ) ∈ walrasianDemandOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1}
      (fun x => -(α / x 0) + x 1) ![p, 1] ((![p, 1] : Fin 2 → ℝ) ⬝ᵥ ![e0, e1]) := by
  have hdot : (![p, 1] : Fin 2 → ℝ) ⬝ᵥ ![e0, e1] = p * e0 + e1 := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hdot, invQL_demand hp hc hfoc hw, Set.mem_singleton_iff]
  funext l
  fin_cases l
  · rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring

/-- The economy of `exercise_15_B_10a`: utilities `-α/x₁ + x₂` with `α₁ = 1/16`, `α₂ = 1`
(quasilinear with the same numeraire, good 2), consumption sets `{x₁ > 0, x₂ ≥ 0}`, and
endowments `ω`. -/
noncomputable def ex15B10aEconomy (ω : Fin 2 → Fin 2 → ℝ) : EdgeworthEconomy where
  X := fun _ => {x | 0 < x 0 ∧ 0 ≤ x 1}
  u := ![fun x => -(1 / 16 / x 0) + x 1, fun x => -(1 / x 0) + x 1]
  ω := ω

/-- **Exercise 15.B.10(a)** (MWG, p. 542). With quasilinear preferences (same numeraire) an increase
in consumer 1's endowments from `ω₁ = (1, 1)` to `ω'₁ = (2, 101/100) ≫ ω₁` (consumer 2 keeps
`(1/10, 10)`) lowers consumer 1's equilibrium utility, from `-(1/16)/(11/50) + x₂₁` to a smaller
value: the equilibrium price of good 1 falls from `625/484` to `625/1764`, and consumer 1, a seller
of good 1 facing inelastic demand, loses (as a quantity-setting monopolist would by selling
more). -/
theorem exercise_15_B_10a :
    (ex15B10aEconomy ![![1, 1], ![1 / 10, 10]]).IsDemandEqm ![625 / 484, 1]
      ![![11 / 50, 1 + 625 / 484 * (1 - 11 / 50)],
        ![22 / 25, 10 + 625 / 484 * (1 / 10 - 22 / 25)]] ∧
    (ex15B10aEconomy ![![2, 101 / 100], ![1 / 10, 10]]).IsDemandEqm ![625 / 1764, 1]
      ![![21 / 50, 101 / 100 + 625 / 1764 * (2 - 21 / 50)],
        ![42 / 25, 10 + 625 / 1764 * (1 / 10 - 42 / 25)]] ∧
    -(1 / 16 / (21 / 50)) + (101 / 100 + 625 / 1764 * (2 - 21 / 50)) <
      -(1 / 16 / (11 / 50)) + (1 + 625 / 484 * (1 - 11 / 50) : ℝ) := by
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, by norm_num⟩
  · fin_cases i <;> norm_num [ex15B10aEconomy]
  · funext l
    fin_cases l <;> norm_num [ex15B10aEconomy, ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
  · fin_cases i
    · exact invQL_mem (α := 1 / 16) (e0 := 1) (e1 := 1) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact invQL_mem (α := 1) (e0 := 1 / 10) (e1 := 10) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · fin_cases i <;> norm_num [ex15B10aEconomy]
  · funext l
    fin_cases l <;> norm_num [ex15B10aEconomy, ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
  · fin_cases i
    · exact invQL_mem (α := 1 / 16) (e0 := 2) (e1 := 101 / 100) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact invQL_mem (α := 1) (e0 := 1 / 10) (e1 := 10) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)

/-- With a numeraire whose consumption may be of either sign (Definition 3.B.7's domain
`quasilinearDomain`), quasilinear demand shifts with wealth along the numeraire:
`x ∈ x(p, w)` implies `x + (Δ/p₂) e₂ ∈ x(p, w + Δ)` for every `Δ` (`p₂ > 0`). -/
theorem quasilinear_demand_shift {φ : ℝ → ℝ} {p : Fin 2 → ℝ} (hp : 0 < p 1) {w Δ : ℝ}
    {x : Fin 2 → ℝ}
    (hx : x ∈ walrasianDemandOn (quasilinearDomain 1) (fun y => φ (y 0) + y 1) p w) :
    x + (Δ / p 1) • Pi.single 1 1 ∈
      walrasianDemandOn (quasilinearDomain 1) (fun y => φ (y 0) + y 1) p (w + Δ) := by
  have hcost : ∀ y : Fin 2 → ℝ, p ⬝ᵥ (y + (Δ / p 1) • Pi.single 1 1) = p ⬝ᵥ y + Δ := by
    intro y
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one,
      div_mul_cancel₀ _ hp.ne']
  have hdom : ∀ y : Fin 2 → ℝ, y ∈ quasilinearDomain 1 → ∀ c : ℝ,
      y + c • Pi.single 1 1 ∈ quasilinearDomain 1 := by
    intro y hy c l hl
    simp [hl, hy l hl]
  refine ⟨⟨hdom x hx.1.1 _, by rw [hcost]; linarith [hx.1.2]⟩, fun y hy => ?_⟩
  have hy' : y + (-(Δ / p 1)) • Pi.single 1 1 ∈ budgetSetOn (quasilinearDomain 1) p w := by
    refine ⟨hdom y hy.1 _, ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, neg_mul,
      div_mul_cancel₀ _ hp.ne']
    linarith [hy.2]
  have h := hx.2 _ hy'
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h ⊢
  simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
    add_zero] at h ⊢
  linarith

/-- **Exercise 15.B.10(b)** (MWG, p. 542), corrected. Quasilinear preferences with the same
numeraire (good 2, unrestricted in sign as in Definition 3.B.7). If `(p, x)` is a Walrasian
equilibrium (`p₂ > 0`) and consumer 2 transfers `z` to consumer 1, then at the same prices the
allocation in which consumer 1 gets `p·z/p₂` more and consumer 2 `p·z/p₂` less of the numeraire
is an equilibrium of the new economy, and consumer 1's utility rises by `p·z/p₂ ≥ 0` (`p, z ≥ 0`).
(With several equilibrium prices the printed claim fails: `exercise_15_B_10b_counterexample`.) -/
theorem exercise_15_B_10b {φ : Fin 2 → ℝ → ℝ} {ω : Fin 2 → Fin 2 → ℝ} {z p : Fin 2 → ℝ}
    (hp1 : 0 < p 1) {x : Fin 2 → Fin 2 → ℝ}
    (h : (⟨fun _ => quasilinearDomain 1, fun i y => φ i (y 0) + y 1, ω⟩ :
      EdgeworthEconomy).IsDemandEqm p x) :
    (⟨fun _ => quasilinearDomain 1, fun i y => φ i (y 0) + y 1, ![ω 0 + z, ω 1 - z]⟩ :
      EdgeworthEconomy).IsDemandEqm p
        ![x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1, x 1 + (-(p ⬝ᵥ z / p 1)) • Pi.single 1 1] ∧
      φ 0 ((x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1 : Fin 2 → ℝ) 0) +
        (x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1 : Fin 2 → ℝ) 1 =
        φ 0 (x 0 0) + x 0 1 + p ⬝ᵥ z / p 1 := by
  obtain ⟨hbox, hd⟩ := h
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, ?_⟩
  · fin_cases i
    · intro l hl; simp [hl, (hd 0).1.1 l hl]
    · intro l hl; simp [hl, (hd 1).1.1 l hl]
  · have h2 := hbox.2
    simp only [ExchangeEconomy.totalEndowment, Fin.sum_univ_two] at h2 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    funext l
    have := congrFun h2 l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    linarith
  · fin_cases i
    · have := quasilinear_demand_shift (φ := φ 0) (Δ := p ⬝ᵥ z) hp1 (hd 0)
      change _ ∈ walrasianDemandOn _ _ p (p ⬝ᵥ (ω 0 + z))
      rw [dotProduct_add]
      exact this
    · have := quasilinear_demand_shift (φ := φ 1) (Δ := -(p ⬝ᵥ z)) hp1 (hd 1)
      change _ ∈ walrasianDemandOn _ _ p (p ⬝ᵥ (ω 1 - z))
      rw [dotProduct_sub, sub_eq_add_neg, ← neg_div]
      exact this
  · simp
    ring

/-- The kinked, strictly concave and strictly increasing `φ(x) = min(2x, x + 1) + √x` of
`exercise_15_B_10b_counterexample`. -/
noncomputable def kinkedPhi (x : ℝ) : ℝ := min (2 * x) (x + 1) + Real.sqrt x

/-- `φ(y) - q y ≤ φ(1) - q - (√y - 1)²/2` for `q ∈ [3/2, 5/2]`, `y ≥ 0`: the superdifferential of
`φ` at `1` is `[3/2, 5/2]`. -/
theorem kinkedPhi_le {q y : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2) (hy : 0 ≤ y) :
    kinkedPhi y - q * y ≤ kinkedPhi 1 - q - (Real.sqrt y - 1) ^ 2 / 2 := by
  have hs := Real.sq_sqrt hy
  have hs0 := Real.sqrt_nonneg y
  have h1 : kinkedPhi 1 = 3 := by norm_num [kinkedPhi]
  rw [h1, kinkedPhi]
  rcases le_total y 1 with h | h
  · rw [min_eq_left (by linarith)]
    nlinarith
  · rw [min_eq_right (by linarith)]
    nlinarith

/-- The kinked quasilinear consumer's demand at prices `(q, 1)` with `q ∈ [3/2, 5/2]` and wealth
`w ≥ q` is the single bundle `(1, w - q)`. -/
theorem kinked_demand {q w : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2) (hw : q ≤ w) :
    walrasianDemand (fun y => kinkedPhi (y 0) + y 1) ![q, 1] w = {![1, w - q]} := by
  have hdot : ∀ y : Fin 2 → ℝ, (![q, 1] : Fin 2 → ℝ) ⬝ᵥ y = q * y 0 + y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hmem : (![1, w - q] : Fin 2 → ℝ) ∈ budgetSet ![q, 1] w :=
    ⟨fun l => by
      fin_cases l
      · norm_num
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith, by rw [hdot]; simp⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hmax⟩
    have hb := hy.2
    rw [hdot] at hb
    have h1 := hmax _ hmem
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have h2 := kinkedPhi_le hq1 hq2 (hy.1 0)
    have hsq : (Real.sqrt (y 0) - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]
    have hs1 : Real.sqrt (y 0) = 1 := by nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]
    have e0 : y 0 = 1 := by rw [← Real.sq_sqrt (hy.1 0), hs1]; norm_num
    have e1 : y 1 = w - q := by
      rw [e0] at hb h1 h2
      linarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    have hb := hy.2
    rw [hdot] at hb
    have h2 := kinkedPhi_le hq1 hq2 (hy.1 0)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]

/-- The kinked `φ` is strictly concave and strictly increasing on `[0, ∞)`. -/
theorem kinkedPhi_props : StrictConcaveOn ℝ (Set.Ici 0) kinkedPhi ∧
    StrictMonoOn kinkedPhi (Set.Ici 0) := by
  constructor
  · refine ⟨convex_Ici 0, fun a ha b hb hab θ η hθ hη hθη => ?_⟩
    have hs := Real.strictConcaveOn_sqrt.2 ha hb hab hθ hη hθη
    simp only [smul_eq_mul] at hs ⊢
    simp only [kinkedPhi]
    have hmin : θ * min (2 * a) (a + 1) + η * min (2 * b) (b + 1) ≤
        min (2 * (θ * a + η * b)) (θ * a + η * b + 1) := by
      refine le_min ?_ ?_
      · nlinarith [min_le_left (2 * a) (a + 1), min_le_left (2 * b) (b + 1)]
      · nlinarith [min_le_right (2 * a) (a + 1), min_le_right (2 * b) (b + 1)]
    linarith
  · intro a ha b hb hab
    simp only [kinkedPhi]
    have := Real.sqrt_lt_sqrt ha hab
    have : min (2 * a) (a + 1) ≤ min (2 * b) (b + 1) :=
      min_le_min (by linarith) (by linarith)
    linarith

/-- The equilibria of the kinked quasilinear Edgeworth box with endowments `e₁, e₂` (total of
good 1 equal to `2`): at any `q ∈ [3/2, 5/2]`, each consumer consumes one unit of good 1. -/
theorem kinked_isDemandEqm {e₁ e₂ : Fin 2 → ℝ} {q : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2)
    (hw₁ : q ≤ q * e₁ 0 + e₁ 1) (hw₂ : q ≤ q * e₂ 0 + e₂ 1) (htot : e₁ 0 + e₂ 0 = 2) :
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1) ![e₁, e₂] :
      EdgeworthEconomy).IsDemandEqm ![q, 1]
      ![![1, q * e₁ 0 + e₁ 1 - q], ![1, q * e₂ 0 + e₂ 1 - q]] := by
  have hd : ∀ e : Fin 2 → ℝ, q ≤ q * e 0 + e 1 →
      (![1, q * e 0 + e 1 - q] : Fin 2 → ℝ) ∈ walrasianDemand (fun y => kinkedPhi (y 0) + y 1)
        ![q, 1] ((![q, 1] : Fin 2 → ℝ) ⬝ᵥ e) := by
    intro e hw
    have h : (![q, 1] : Fin 2 → ℝ) ⬝ᵥ e = q * e 0 + e 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [h, kinked_demand hq1 hq2 hw]
    rfl
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i
    · exact (hd e₁ hw₁).1.1
    · exact (hd e₂ hw₂).1.1
  · funext l
    fin_cases l
    · simp [ExchangeEconomy.totalEndowment, ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
      linarith
    · simp [ExchangeEconomy.totalEndowment, ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
      nlinarith
  · fin_cases i
    · exact hd e₁ hw₁
    · exact hd e₂ hw₂

/-- **Exercise 15.B.10(b)** (MWG, p. 542): the claim as printed is false. Both consumers have the
continuous, strictly convex, strongly monotone quasilinear utility `φ(x₁) + x₂` with the kinked
`φ = kinkedPhi` (same numeraire). Before the transfer, endowments `(3/2, 10)` and `(1/2, 10)`:
`p = (5/2, 1)` with `x₁ = (1, 45/4)` is an equilibrium. After consumer 2 transfers `z = (1/10, 0)`
to consumer 1 (endowments `(8/5, 10)`, `(2/5, 10)`): `p = (3/2, 1)` with `x'₁ = (1, 109/10)` is an
equilibrium, and consumer 1 is worse off. (Every price in `[3/2, 5/2]` is an equilibrium price in
both economies; consistently with Exercise 15.B.10(d), before the transfer `p = (3/2, 1)` gives
consumer 1 the even lower utility `φ(1) + 43/4`.) -/
theorem exercise_15_B_10b_counterexample :
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![3 / 2, 10], ![1 / 2, 10]] : EdgeworthEconomy).IsDemandEqm ![5 / 2, 1]
      ![![1, 45 / 4], ![1, 35 / 4]] ∧
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![8 / 5, 10], ![2 / 5, 10]] : EdgeworthEconomy).IsDemandEqm ![3 / 2, 1]
      ![![1, 109 / 10], ![1, 91 / 10]] ∧
    kinkedPhi 1 + 109 / 10 < kinkedPhi 1 + 45 / 4 ∧
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![3 / 2, 10], ![1 / 2, 10]] : EdgeworthEconomy).IsDemandEqm ![3 / 2, 1]
      ![![1, 43 / 4], ![1, 37 / 4]] ∧ kinkedPhi 1 + 43 / 4 < kinkedPhi 1 + 109 / 10 := by
  refine ⟨?_, ?_, by norm_num, ?_, by norm_num⟩
  · convert kinked_isDemandEqm (e₁ := ![3 / 2, 10]) (e₂ := ![1 / 2, 10]) (q := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num
  · convert kinked_isDemandEqm (e₁ := ![8 / 5, 10]) (e₂ := ![2 / 5, 10]) (q := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num
  · convert kinked_isDemandEqm (e₁ := ![3 / 2, 10]) (e₂ := ![1 / 2, 10]) (q := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The one-consumer, one-producer economy (MWG Section 15.C, pp. 525-529)

Goods are leisure (good 1, index `0`) and a consumption good (good 2, index `1`). The consumer has
utility `u` on `ℝ²₊` and `L̄` units of time; the firm turns labor `z ≥ 0` into `f(z)` units of the
consumption good; the consumer owns the firm.

* (15.C.1): profit maximization (`RCEconomy.IsProfitMax`); (15.C.2): the consumer's problem with
  budget `p x₂ ≤ w(L̄ - x₁) + π` (`RCEconomy.IsConsumerOpt`); the Walrasian equilibrium
  (15.C.3)-(15.C.4) (`RCEconomy.IsWalrasEqm`).
* p. 527: the budget line is the firm's isoprofit line (`budgetLine_eq_isoprofit`).
* p. 528 (Figure 15.C.2, Figure 15.C.3(b)): **first welfare theorem**: every Walrasian equilibrium
  allocation maximizes utility over the feasible set, with no convexity assumption
  (`rc_first_welfare`); footnote 7: in a one-consumer economy Pareto optimality (Definition 10.B.2)
  is utility maximization over the feasible set (`pareto_one_consumer_iff`).
* p. 528: **second welfare theorem**: with a concave production function, differentiable at the
  optimum, and continuous, convex, strongly monotone preferences, the welfare optimum is a Walrasian
  equilibrium allocation at `w/p = f'(z*)` (`rc_second_welfare`; differentiability at the optimum is
  an assumption we add, see `docs/corrections.md`).
* Footnote 7: with convex, strongly monotone preferences and a strictly concave production
  function the optimal consumption vector is unique, hence so is the equilibrium allocation
  (`footnote_7_unique`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.CompetitiveMarkets Kreps.PreferenceProperties

/-- **Section 15.C** (MWG, p. 526). The one-consumer, one-producer (Robinson Crusoe) economy:
utility `u` over (leisure, consumption), time endowment `L̄`, production function `f`. -/
structure RCEconomy where
  /-- The consumer's utility over (leisure, consumption good). -/
  u : (Fin 2 → ℝ) → ℝ
  /-- The time endowment `L̄`. -/
  Lbar : ℝ
  /-- The production function `f(z)`. -/
  f : ℝ → ℝ

/-- **(15.C.1)** (MWG, p. 526). `z` maximizes the firm's profit `p f(z) - w z` over `z ≥ 0`. -/
def RCEconomy.IsProfitMax (E : RCEconomy) (p w z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ z', 0 ≤ z' → p * E.f z' - w * z' ≤ p * E.f z - w * z

/-- **(15.C.2)** (MWG, p. 526). The consumer's budget set at prices `(p, w)` and profit income `π`:
`x ∈ ℝ²₊` with `p x₂ ≤ w(L̄ - x₁) + π`. -/
def RCEconomy.budget (E : RCEconomy) (p w π₀ : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ p * x 1 ≤ w * (E.Lbar - x 0) + π₀}

/-- **(15.C.2)** (MWG, p. 526). `x` solves the consumer's problem. -/
def RCEconomy.IsConsumerOpt (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.budget p w π₀ ∧ ∀ y ∈ E.budget p w π₀, E.u y ≤ E.u x

/-- **Section 15.C** (MWG, p. 527, (15.C.3)-(15.C.4)). A Walrasian equilibrium: prices `(p, w)`, the
firm's labor demand `z` (profit maximizing), the consumer's bundle `x` (utility maximizing with
profit income `π = p f(z) - w z`), and market clearing `x₂ = f(z)`, `z = L̄ - x₁`. -/
def RCEconomy.IsWalrasEqm (E : RCEconomy) (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) : Prop :=
  E.IsProfitMax p w z ∧ E.IsConsumerOpt p w (p * E.f z - w * z) x ∧ x 1 = E.f z ∧
    z = E.Lbar - x 0

/-- **Section 15.C** (MWG, p. 528). The bundles feasible given the technology and the endowment:
`x ∈ ℝ²₊`, `x₁ ≤ L̄`, `x₂ ≤ f(L̄ - x₁)`. -/
def RCEconomy.feasible (E : RCEconomy) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ x 0 ≤ E.Lbar ∧ x 1 ≤ E.f (E.Lbar - x 0)}

/-- **Section 15.C** (MWG, p. 528 and footnote 7). `x` maximizes the consumer's utility subject to
the technological and endowment constraints (the planner's problem). -/
def RCEconomy.IsOptimal (E : RCEconomy) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.feasible ∧ ∀ y ∈ E.feasible, E.u y ≤ E.u x

/-- **Section 15.C** (MWG, p. 527). The consumer's budget line is the firm's isoprofit line: with
`z = L̄ - x₁` and `q = x₂`, `p x₂ = w(L̄ - x₁) + π` if and only if `p q - w z = π`. -/
theorem budgetLine_eq_isoprofit (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) :
    p * x 1 = w * (E.Lbar - x 0) + π₀ ↔ p * x 1 - w * (E.Lbar - x 0) = π₀ := by
  constructor <;> intro h <;> linarith

/-- **Section 15.C** (MWG, p. 527). The budget line cuts the consumption axis at `π/p` (when the
consumer consumes all his time as leisure) and has slope `-w/p`. -/
theorem budgetLine_intercept_slope (E : RCEconomy) {p : ℝ} (hp : p ≠ 0) (w π₀ x₁ : ℝ) :
    (w * (E.Lbar - E.Lbar) + π₀) / p = π₀ / p ∧
      (w * (E.Lbar - (x₁ + 1)) + π₀) / p - (w * (E.Lbar - x₁) + π₀) / p = -(w / p) := by
  constructor
  · simp
  · field_simp
    ring

/-- **First welfare theorem in the one-consumer economy** (MWG, p. 528, Figure 15.C.2 and
Figure 15.C.3(b)). If `(p, w)` with `p ≥ 0` is a Walrasian equilibrium with allocation `(x, z)`,
then `x` maximizes utility over the feasible set; no convexity of the technology is needed. -/
theorem rc_first_welfare {E : RCEconomy} {p w : ℝ} {x : Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (hp : 0 ≤ p) : E.IsOptimal x := by
  obtain ⟨hz, hx, h1, h2⟩ := h
  refine ⟨⟨hx.1.1, by linarith [hz.1], by rw [h1, ← h2]⟩, fun y hy => ?_⟩
  refine hx.2 y ⟨hy.1, ?_⟩
  -- a feasible bundle is affordable: its cost is the profit of the plan producing it
  have hz' : 0 ≤ E.Lbar - y 0 := by linarith [hy.2.1]
  have hprof := hz.2 _ hz'
  have : p * y 1 ≤ p * E.f (E.Lbar - y 0) := mul_le_mul_of_nonneg_left hy.2.2 hp
  linarith

/-- In a Walrasian equilibrium of the one-consumer economy with strongly monotone preferences the
price of the consumption good is positive (otherwise more of it is free). -/
theorem rc_eqm_price_pos {E : RCEconomy} (hmono : UtilityStronglyMonotone E.u) {p w : ℝ}
    {x : Fin 2 → ℝ} {z : ℝ} (h : E.IsWalrasEqm p w x z) : 0 < p := by
  by_contra hp
  rw [not_lt] at hp
  obtain ⟨-, hx, -, -⟩ := h
  have hmem : x + Pi.single 1 1 ∈ E.budget p w (p * E.f z - w * z) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hx.1.1 0
      · simp; linarith [hx.1.1 1]
    · have := hx.1.2
      simp only [Pi.add_apply, Pi.single_eq_same]
      simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
      nlinarith
  have h1 := hx.2 _ hmem
  have h2 := hmono.lt hx.1.1 (y := x + Pi.single 1 1) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  linarith

/-- **Footnote 7** (MWG, p. 528). In a one-consumer economy (Chapter 10's `Economy` with a single
consumer), an allocation is Pareto optimal (Definition 10.B.2) if and only if it is feasible and
maximizes the consumer's utility among feasible allocations. -/
theorem pareto_one_consumer_iff {ι κ : Type*} [Fintype ι] [Unique ι] [Fintype κ] {L : ℕ}
    (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsParetoOptimal a ↔ E.IsFeasible a ∧ ∀ a', E.IsFeasible a' →
      E.u default (a'.x default) ≤ E.u default (a.x default) := by
  rw [definition_10_B_2]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun a' ha' => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have := h a' ha' (fun i => by rw [Unique.eq_default i]; exact hlt.le) default
    linarith
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun a' ha' _ i => ?_⟩
    rw [Unique.eq_default i]
    exact h a' ha'

/-- **Second welfare theorem in the one-consumer economy** (MWG, p. 528, Figure 15.C.2). Suppose
`u` is continuous, quasiconcave (convex preferences) and strongly monotone on `ℝ²₊`, `f` is concave
and strictly increasing on `[0, ∞)` and differentiable at `z* = L̄ - x*₁ > 0`, and `x*` maximizes
utility over the feasible set. Then `x*` with `z*` is a Walrasian equilibrium at `p = 1`,
`w = f'(z*) > 0`. -/
theorem rc_second_welfare {E : RCEconomy} (hcont : ContinuousOn E.u (nonnegOrthant 2))
    (hconv : PrefConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : ConcaveOn ℝ (Set.Ici 0) E.f)
    (hfm : StrictMonoOn E.f (Set.Ici 0)) {x : Fin 2 → ℝ} (hopt : E.IsOptimal x)
    (hz : 0 < E.Lbar - x 0) {f' : ℝ} (hf' : HasDerivAt E.f f' (E.Lbar - x 0)) :
    0 < f' ∧ E.IsWalrasEqm 1 f' x (E.Lbar - x 0) := by
  set zs := E.Lbar - x 0 with hzs
  have hx := hopt.1
  have hxm : x ∈ nonnegOrthant 2 := hx.1
  have hzs0 : zs ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hz.le
  have htan : ∀ z, 0 ≤ z → E.f z ≤ E.f zs + f' * (z - zs) := fun z hz0 =>
    concave_le_tangent hfc hzs0 (Set.mem_Ici.2 hz0) hf'
  -- `f' > 0`
  have hf'pos : 0 < f' := by
    have h1 := hfm hzs0 (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ zs + 1)) (by linarith)
    have h2 := htan (zs + 1) (by linarith)
    linarith
  -- the optimum lies on the frontier: `x₂ = f(z*)`
  have hx1 : x 1 = E.f zs := by
    by_contra hne
    have hlt : x 1 < E.f zs := lt_of_le_of_ne hx.2.2 hne
    set y : Fin 2 → ℝ := x + Pi.single 1 (E.f zs - x 1) with hy
    have hyx : x ≤ y := fun l => by
      fin_cases l <;> simp [hy] ; linarith
    have hyf : y ∈ E.feasible := by
      refine ⟨fun l => (hxm l).trans (hyx l), by simpa [hy] using hx.2.1, ?_⟩
      simp [hy, hzs]
    have hne' : y ≠ x := fun he => by
      have := congrFun he 1
      simp [hy] at this
      linarith
    have := hopt.2 y hyf
    have := hmono.lt hxm hyx hne'
    linarith
  set π₀ := 1 * E.f zs - f' * zs with hπ
  -- the consumer's budget line passes through `x`
  have hxline : 1 * x 1 = f' * (E.Lbar - x 0) + π₀ := by rw [hπ, hx1]; ring
  refine ⟨hf'pos, ⟨hz.le, fun z hz0 => ?_⟩, ⟨⟨hxm, hxline.le⟩, fun y hy => ?_⟩, by
    rw [hx1], rfl⟩
  · have := htan z hz0
    linarith
  -- the consumer: a strictly better affordable bundle leads to a strictly better feasible one
  by_contra hlt
  rw [not_le] at hlt
  -- Step A: a strictly better bundle strictly inside the budget set
  obtain ⟨y', hy'm, hy'in, hy'u⟩ : ∃ y' ∈ nonnegOrthant 2,
      1 * y' 1 < f' * (E.Lbar - y' 0) + π₀ ∧ E.u x < E.u y' := by
    by_cases hin : 1 * y 1 < f' * (E.Lbar - y 0) + π₀
    · exact ⟨y, hy.1, hin, hlt⟩
    by_cases hy1 : 0 < y 1
    · set g : ℝ → Fin 2 → ℝ := fun t => y - (t * y 1) • Pi.single 1 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant 2 := by
        intro t ht l
        fin_cases l
        · simpa [g] using hy.1 0
        · simp [g]; nlinarith [ht.2, hy.1 1]
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hcont hgc hgm (by simpa [g] using hlt)
      refine ⟨g t, hgm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      have hb := hy.2
      simp [g]
      nlinarith [mul_pos ht0 hy1]
    by_cases hy0 : 0 < y 0
    · set g : ℝ → Fin 2 → ℝ := fun t => y - (t * y 0) • Pi.single 0 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant 2 := by
        intro t ht l
        fin_cases l
        · simp [g]; nlinarith [ht.2, hy.1 0]
        · simpa [g] using hy.1 1
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hcont hgc hgm (by simpa [g] using hlt)
      refine ⟨g t, hgm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      have hb := hy.2
      simp [g]
      rw [not_lt] at hin
      nlinarith [mul_pos (mul_pos ht0 hy0) hf'pos]
    · exfalso
      have hy00 : y = 0 := funext fun l => by
        fin_cases l
        · exact le_antisymm (not_lt.1 hy0) (hy.1 0)
        · exact le_antisymm (not_lt.1 hy1) (hy.1 1)
      have := hmono.le (x := 0) (y := x) (fun l => le_refl _) hxm
      rw [hy00] at hlt
      linarith
  -- Step B: move from `x` towards `y'`; nearby points are feasible and inside the frontier
  set c := f' * (E.Lbar - y' 0) + π₀ - 1 * y' 1 with hc
  have hc0 : 0 < c := by linarith
  set d := x 0 - y' 0 with hd
  have hline : HasDerivAt (fun t : ℝ => zs + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add zs
  have hcomp : HasDerivAt (fun t : ℝ => E.f (zs + t * d)) (f' * d) 0 := by
    have := HasDerivAt.comp (0 : ℝ) (by simpa using hf') hline
    simpa [Function.comp_def] using this
  have hgap : HasDerivAt (fun t : ℝ => E.f (zs + t * d) - (E.f zs + f' * (t * d)) + t * c) c 0 := by
    have h1 := (hcomp.sub ((hasDerivAt_id (0 : ℝ)).mul_const d |>.const_mul f' |>.const_add
      (E.f zs))).add ((hasDerivAt_id (0 : ℝ)).mul_const c)
    convert h1 using 1
    · funext t; simp
    · ring
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t ≤ 1 ∧ 0 ≤ zs + t * d := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), t < 1 := gt_mem_nhds one_pos
    have h2 : ∀ᶠ t in nhds (0 : ℝ), 0 < zs + t * d := by
      have hc : Continuous fun t : ℝ => zs + t * d := by fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hz))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with t ht1 ht2
    exact ⟨ht1.le, ht2.le⟩
  obtain ⟨t, ht0, ⟨ht1, htz⟩, hpos⟩ := exists_pos_deriv_pos hgap hc0 hev
  simp only [zero_mul, add_zero, mul_zero, sub_self] at hpos
  set xt : Fin 2 → ℝ := x + t • (y' - x) with hxt
  have hxtm : xt ∈ nonnegOrthant 2 := by
    have := convex_nonnegOrthant 2 hxm hy'm (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    convert this using 1
    rw [hxt]
    funext l
    simp
    ring
  have hxtu : E.u x ≤ E.u xt := by
    have := quasiconcave_of_prefConvex hconv hxm hy'm (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    have e : (1 - t) • x + t • y' = xt := by
      rw [hxt]; funext l; simp; ring
    rw [e, min_eq_left hy'u.le] at this
    exact this
  have hxt0 : E.Lbar - xt 0 = zs + t * d := by simp [hxt, hd, hzs]; ring
  have hxt1 : xt 1 < E.f (E.Lbar - xt 0) := by
    rw [hxt0]
    have : xt 1 = E.f zs + f' * (t * d) - t * c := by
      simp only [hxt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hc, hd]
      have := hxline
      rw [hx1] at this ⊢
      nlinarith
    linarith
  set y'' : Fin 2 → ℝ := xt + Pi.single 1 (E.f (E.Lbar - xt 0) - xt 1) with hy''
  have hle : xt ≤ y'' := fun l => by
    fin_cases l <;> simp [hy''] ; linarith
  have hne : y'' ≠ xt := fun he => by
    have := congrFun he 1
    simp [hy''] at this
    linarith
  have hfeas : y'' ∈ E.feasible := by
    refine ⟨fun l => (hxtm l).trans (hle l), ?_, ?_⟩
    · simp [hy'']; linarith
    · simp [hy'']
  have h1 := hopt.2 y'' hfeas
  have h2 := hmono.lt hxtm hle hne
  linarith

/-- With strongly monotone preferences an optimum lies on the production frontier:
`x₂ = f(L̄ - x₁)`. -/
theorem rc_optimal_frontier {E : RCEconomy} (hmono : UtilityStronglyMonotone E.u)
    {x : Fin 2 → ℝ} (hopt : E.IsOptimal x) : x 1 = E.f (E.Lbar - x 0) := by
  have hx := hopt.1
  by_contra hne
  have hlt : x 1 < E.f (E.Lbar - x 0) := lt_of_le_of_ne hx.2.2 hne
  set y : Fin 2 → ℝ := x + Pi.single 1 (E.f (E.Lbar - x 0) - x 1) with hy
  have hyx : x ≤ y := fun l => by
    fin_cases l <;> simp [hy] ; linarith
  have hyf : y ∈ E.feasible := by
    refine ⟨fun l => (hx.1 l).trans (hyx l), by simpa [hy] using hx.2.1, ?_⟩
    simp [hy]
  have hne' : y ≠ x := fun he => by
    have := congrFun he 1
    simp [hy] at this
    linarith
  have := hopt.2 y hyf
  have := hmono.lt hx.1 hyx hne'
  linarith

/-- **Footnote 7** (MWG, p. 528). With convex, strongly monotone preferences and a strictly concave
production function there is a unique optimal consumption vector. -/
theorem footnote_7_unique {E : RCEconomy}
    (hconv : PrefConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : StrictConcaveOn ℝ (Set.Ici 0) E.f)
    {x y : Fin 2 → ℝ} (hx : E.IsOptimal x) (hy : E.IsOptimal y) : x = y := by
  by_contra hne
  have hxy : E.u x = E.u y := le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)
  have hfx := rc_optimal_frontier hmono hx
  have hfy := rc_optimal_frontier hmono hy
  have h0 : x 0 ≠ y 0 := by
    intro h0
    apply hne
    funext l
    fin_cases l
    · exact h0
    · change x 1 = y 1
      rw [hfx, hfy, h0]
  set m : Fin 2 → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hm
  have hmm : m ∈ nonnegOrthant 2 :=
    convex_nonnegOrthant 2 hx.1.1 hy.1.1 (by norm_num) (by norm_num) (by norm_num)
  have hmu : E.u x ≤ E.u m := by
    have := quasiconcave_of_prefConvex hconv hx.1.1 hy.1.1 (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [← hxy, min_self] at this
    exact this
  have hzx : E.Lbar - x 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hx.1.2.1])
  have hzy : E.Lbar - y 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hy.1.2.1])
  have hstrict := hfc.2 hzx hzy (fun h => h0 (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hm0 : E.Lbar - m 0 = (1 / 2 : ℝ) • (E.Lbar - x 0) + (1 / 2 : ℝ) • (E.Lbar - y 0) := by
    simp [hm]; ring
  have hm1 : m 1 = 1 / 2 * x 1 + 1 / 2 * y 1 := by simp [hm]
  have hlt : m 1 < E.f (E.Lbar - m 0) := by
    rw [hm0, hm1, hfx, hfy]
    simpa using hstrict
  have hmf : m ∈ E.feasible := ⟨hmm, by
    simp [hm]; linarith [hx.1.2.1, hy.1.2.1], hlt.le⟩
  have hmopt : E.IsOptimal m := ⟨hmf, fun z hz => (hx.2 z hz).trans hmu⟩
  have := rc_optimal_frontier hmono hmopt
  linarith

/-- **Exercise 15.C.1(a)** (MWG, p. 542). In the one-consumer, one-firm economy with strictly convex
(and, as throughout Section 15.C, strongly monotone) preferences and a strictly concave production
function, the equilibrium allocation, and so the equilibrium level of production, is unique. -/
theorem exercise_15_C_1a {E : RCEconomy}
    (hsc : PrefStrictlyConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : StrictConcaveOn ℝ (Set.Ici 0) E.f)
    {p w p' w' z z' : ℝ} {x x' : Fin 2 → ℝ} (h : E.IsWalrasEqm p w x z)
    (h' : E.IsWalrasEqm p' w' x' z') : x = x' ∧ z = z' ∧ E.f z = E.f z' := by
  have hconv := hsc.prefConvex (convex_nonnegOrthant 2)
  have hx := rc_first_welfare h (rc_eqm_price_pos hmono h).le
  have hx' := rc_first_welfare h' (rc_eqm_price_pos hmono h').le
  have heq := footnote_7_unique hconv hmono hfc hx hx'
  have hz : z = z' := by rw [h.2.2.2, h'.2.2.2, heq]
  exact ⟨heq, hz, by rw [hz]⟩

/-! ### Figure 15.C.3(a): failure of the second welfare theorem with a nonconvex technology -/

/-- **Figure 15.C.3(a)** (MWG, p. 529): `u = √x₁ + √x₂`, `L̄ = 1`, and the increasing-returns
production function `f(z) = z²` (a nonconvex production set). -/
noncomputable def fig15C3aEconomy : RCEconomy where
  u := fun x => Real.sqrt (x 0) + Real.sqrt (x 1)
  Lbar := 1
  f := fun z => z ^ 2

/-- `√a ≤ (a + c²)/(2c)` for `c > 0` (the tangent line of `√` at `c²`). -/
theorem sqrt_le_tangent {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    Real.sqrt a ≤ (a + c ^ 2) / (2 * c) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt a - c), Real.sq_sqrt ha]

/-- **Figure 15.C.3(a)** (MWG, p. 529): `x* = (1/4, 9/16)` (`z* = 3/4`) maximizes the consumer's
utility over the feasible set. -/
theorem fig_15_C_3a_optimal : fig15C3aEconomy.IsOptimal ![1 / 4, 9 / 16] := by
  refine ⟨⟨fun l => by fin_cases l <;> norm_num, by norm_num [fig15C3aEconomy],
    by norm_num [fig15C3aEconomy]⟩, fun y hy => ?_⟩
  obtain ⟨hy0, hyL, hyf⟩ := hy
  simp only [fig15C3aEconomy] at hyL hyf ⊢
  have h1 : Real.sqrt (y 1) ≤ 1 - y 0 := by
    rw [Real.sqrt_le_left (by linarith)]
    exact hyf
  have h2 := sqrt_le_tangent (hy0 0) (by norm_num : (0 : ℝ) < 1 / 2)
  have e1 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
  have : (y 0 + (1 / 2) ^ 2) / (2 * (1 / 2)) = y 0 + 1 / 4 := by ring
  linarith

/-- **Figure 15.C.3(a)** (MWG, p. 529): the economy has no Walrasian equilibrium, so the optimum is
not supportable: with `p > 0` profits `p z² - w z` are unbounded, and with `p ≤ 0` the consumption
good is free. -/
theorem fig_15_C_3a_no_eqm (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) :
    ¬ fig15C3aEconomy.IsWalrasEqm p w x z := by
  rintro ⟨hz, hx, -, -⟩
  by_cases hp : 0 < p
  · -- unbounded profits
    set M := (|w| + |p * z ^ 2 - w * z| + 1) / p + 1 with hM
    have hM1 : 1 ≤ M := by
      have : 0 ≤ (|w| + |p * z ^ 2 - w * z| + 1) / p := by positivity
      linarith
    have h := hz.2 M (by linarith)
    simp only [fig15C3aEconomy] at h
    have hpM : p * M ^ 2 ≥ p * M * M := by nlinarith
    have hkey : p * M ≥ |w| + |p * z ^ 2 - w * z| + 1 := by
      have : p * ((|w| + |p * z ^ 2 - w * z| + 1) / p) = |w| + |p * z ^ 2 - w * z| + 1 := by
        field_simp
      nlinarith
    have hw : w * M ≤ |w| * M := mul_le_mul_of_nonneg_right (le_abs_self w) (by linarith)
    have habs := le_abs_self (p * z ^ 2 - w * z)
    nlinarith [abs_nonneg w, abs_nonneg (p * z ^ 2 - w * z)]
  · rw [not_lt] at hp
    have hmem : x + Pi.single 1 1 ∈ fig15C3aEconomy.budget p w
        (p * fig15C3aEconomy.f z - w * z) := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simpa using hx.1.1 0
        · simp; linarith [hx.1.1 1]
      · have := hx.1.2
        simp only [Pi.add_apply, Pi.single_eq_same]
        simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
        nlinarith
    have h1 := hx.2 _ hmem
    simp only [fig15C3aEconomy, Pi.add_apply, Pi.single_eq_same] at h1
    simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at h1
    have : Real.sqrt (x 1) < Real.sqrt (x 1 + 1) :=
      Real.sqrt_lt_sqrt (hx.1.1 1) (by linarith)
    linarith

/-- **Figure 15.C.3(a)** (MWG, p. 529): at the relative price `w/p = 3/2` the optimum `x*` maximizes
utility on the budget set through it (profit income `π = (3/4)² - (3/2)(3/4)`), but `z* = 3/4`
does not maximize profit even locally: it is the minimizer of `z² - (3/2) z`, and every other
input level gives higher profit. -/
theorem fig_15_C_3a_prices :
    fig15C3aEconomy.IsConsumerOpt 1 (3 / 2) (1 * fig15C3aEconomy.f (3 / 4) - 3 / 2 * (3 / 4))
        ![1 / 4, 9 / 16] ∧
      ∀ z, z ≠ 3 / 4 → 1 * fig15C3aEconomy.f (3 / 4) - 3 / 2 * (3 / 4) <
        1 * fig15C3aEconomy.f z - 3 / 2 * z := by
  have e1 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨⟨⟨fun l => by fin_cases l <;> norm_num, by norm_num [fig15C3aEconomy]⟩,
    fun y hy => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨hy0, hb⟩ := hy
    simp only [fig15C3aEconomy] at hb ⊢
    have h1 := sqrt_le_tangent (hy0 0) (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 := sqrt_le_tangent (hy0 1) (by norm_num : (0 : ℝ) < 3 / 4)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
    have : (y 0 + (1 / 2) ^ 2) / (2 * (1 / 2)) = y 0 + 1 / 4 := by ring
    have : (y 1 + (3 / 4) ^ 2) / (2 * (3 / 4)) = 2 / 3 * (y 1 + 9 / 16) := by ring
    nlinarith
  · simp only [fig15C3aEconomy]
    have : 0 < (z - 3 / 4) ^ 2 := by
      have : z - 3 / 4 ≠ 0 := sub_ne_zero.2 hz
      positivity
    nlinarith

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 15.C.1(b) and 15.C.2 (MWG p. 542)

* `rc_budget_eq`: the budget set of (15.C.2) is the Walrasian budget set at prices `(w, p)` and
  wealth `w L̄ + π`.
* `sqrt_firm_profit`: profit maximization for the firm with `f(z) = √z`.
* **Exercise 15.C.2** (`exercise_15_C_2`): with `f(z) = z^{1/2}`, `u = ln x₁ + ln x₂`
  (represented by `x₁^{1/2}x₂^{1/2}`, which ranks bundles of `ℝ²₊₊` identically and gives the
  boundary the lowest value, as `ln 0 = -∞` does) and `L̄ = 1`, the equilibria are `w/p = √3/2`
  with `x = (2/3, √3/3)`, `z = 1/3`, `q = √3/3` and profits `π = p√3/6`.
* **Exercise 15.C.1(b)**: at an equilibrium the slope of the excess demand for labor is the
  compensated (Slutsky) own-price effect on leisure plus the slope of the firm's labor demand, hence
  nonpositive (`exercise_15_C_1b`, with an instance from Exercise 15.C.2); and the slope need not
  have one sign globally (`exercise_15_C_1b_not_monotone`, a CES consumer with `f = √z`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The budget set (15.C.2) is the Walrasian budget set at prices `(w, p)` and wealth `w L̄ + π`. -/
theorem rc_budget_eq (E : RCEconomy) (p w π₀ : ℝ) :
    E.budget p w π₀ = budgetSet ![w, p] (w * E.Lbar + π₀) := by
  ext x
  simp only [RCEconomy.budget, budgetSet, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- The consumer's problem (15.C.2) is Chapter 3's utility maximization problem at prices `(w, p)`
and wealth `w L̄ + π`. -/
theorem rc_consumerOpt_iff (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) :
    E.IsConsumerOpt p w π₀ x ↔ x ∈ walrasianDemand E.u ![w, p] (w * E.Lbar + π₀) := by
  unfold RCEconomy.IsConsumerOpt
  rw [rc_budget_eq]
  rfl

/-- The firm with `f(z) = √z`: for `p, w > 0`, `p√z - wz ≤ p²/(4w)` on `z ≥ 0`, with equality
exactly at `z = p²/(4w²)`. -/
theorem sqrt_firm_profit {p w : ℝ} (hp : 0 < p) (hw : 0 < w) {z : ℝ} (hz : 0 ≤ z) :
    p * Real.sqrt z - w * z ≤ p ^ 2 / (4 * w) ∧
      (p * Real.sqrt z - w * z = p ^ 2 / (4 * w) ↔ z = p ^ 2 / (4 * w ^ 2)) := by
  have hs := Real.sq_sqrt hz
  have key : p * Real.sqrt z - w * z = p ^ 2 / (4 * w) - w * (Real.sqrt z - p / (2 * w)) ^ 2 := by
    field_simp
    linear_combination 16 * w ^ 2 * hs
  rw [key]
  have hsq : 0 ≤ w * (Real.sqrt z - p / (2 * w)) ^ 2 := by positivity
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : w * (Real.sqrt z - p / (2 * w)) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · have h1 : Real.sqrt z = p / (2 * w) := by nlinarith [sq_nonneg (Real.sqrt z - p / (2 * w))]
      rw [← hs, h1]
      field_simp
      ring
  · have h1 : Real.sqrt z = p / (2 * w) := by
      rw [h, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le,
        show (4 : ℝ) * w ^ 2 = (2 * w) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h1]
    ring

/-- **Exercise 15.C.2** (MWG, p. 542). The economy: `u = x₁^{1/2}x₂^{1/2}` (representing
`ln x₁ + ln x₂`), `L̄ = 1`, `f(z) = z^{1/2}`. -/
noncomputable def ex15C2Economy : RCEconomy where
  u := cobbDouglasUtility 1 (1 / 2)
  Lbar := 1
  f := Real.sqrt

/-- **Exercise 15.C.2** (MWG, p. 542). The Walrasian equilibria are exactly: `p > 0`,
`w = (√3/2) p`, consumption `x = (2/3, √3/3)`, labor `z = 1/3`; output is `q = √3/3` and profits
are `π = p √3/6`. -/
theorem exercise_15_C_2 (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) :
    ex15C2Economy.IsWalrasEqm p w x z ↔
      0 < p ∧ w = Real.sqrt 3 / 2 * p ∧ x = ![2 / 3, Real.sqrt 3 / 3] ∧ z = 1 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq13 : Real.sqrt (1 / 3) = Real.sqrt 3 / 3 := by
    rw [show (1 / 3 : ℝ) = (Real.sqrt 3 / 3) ^ 2 by rw [div_pow, h3]; norm_num,
      Real.sqrt_sq (by positivity)]
  constructor
  · rintro ⟨hz, hx, hx1, hzx⟩
    have hπ0 : 0 ≤ p * ex15C2Economy.f z - w * z := by
      have := hz.2 0 le_rfl
      simpa [ex15C2Economy] using this
    rw [rc_consumerOpt_iff] at hx
    -- `p > 0`: otherwise the consumption good is free
    have hp : 0 < p := by
      by_contra hp
      rw [not_lt] at hp
      have hb : (![1, 0] : Fin 2 → ℝ) ∈ budgetSet ![w, p]
          (w * ex15C2Economy.Lbar + (p * ex15C2Economy.f z - w * z)) :=
        ⟨fun l => by fin_cases l <;> norm_num, by
          simp only [ex15C2Economy] at hπ0
          simp [dotProduct, Fin.sum_univ_two, ex15C2Economy]; linarith⟩
      have := cd_no_demand_1 (α := 1 / 2) (by norm_num) (by norm_num)
        (p := ![w, p]) (by simpa using hp) hb (by simp)
      have hx' : x ∈ walrasianDemand (cobbDouglasUtility 1 (1 / 2)) ![w, p]
          (w * ex15C2Economy.Lbar + (p * ex15C2Economy.f z - w * z)) := hx
      rw [this] at hx'
      exact hx'
    -- `w > 0`: otherwise profits are unbounded
    have hw : 0 < w := by
      by_contra hw
      rw [not_lt] at hw
      set s := (|p * Real.sqrt z - w * z| + 1) / p with hs
      have hs0 : 0 ≤ s := by positivity
      have h := hz.2 (s ^ 2) (sq_nonneg s)
      simp only [ex15C2Economy, Real.sqrt_sq hs0] at h
      have : p * s = |p * Real.sqrt z - w * z| + 1 := by rw [hs]; field_simp
      nlinarith [le_abs_self (p * Real.sqrt z - w * z), sq_nonneg s]
    -- the firm's demand for labor
    have hzval : z = p ^ 2 / (4 * w ^ 2) := by
      have h1 := (sqrt_firm_profit hp hw hz.1).1
      have h2 := hz.2 (p ^ 2 / (4 * w ^ 2)) (by positivity)
      have h3' := ((sqrt_firm_profit hp hw (by positivity : (0 : ℝ) ≤ p ^ 2 / (4 * w ^ 2))).2).2
        rfl
      simp only [ex15C2Economy] at h2
      exact ((sqrt_firm_profit hp hw hz.1).2).1 (le_antisymm h1 (by linarith))
    have hsz : Real.sqrt z = p / (2 * w) := by
      rw [hzval, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le,
        show (4 : ℝ) * w ^ 2 = (2 * w) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hπ : p * ex15C2Economy.f z - w * z = p ^ 2 / (4 * w) := by
      simp only [ex15C2Economy]
      rw [hsz, hzval]
      field_simp
      ring
    -- the consumer's Cobb-Douglas demand
    have hpp : StrictlyPositive ![w, p] := fun l => by fin_cases l; exacts [hw, hp]
    have hm : 0 ≤ w * ex15C2Economy.Lbar + p ^ 2 / (4 * w) := by
      simp only [ex15C2Economy]; positivity
    rw [hπ] at hx
    have hx' : x ∈ walrasianDemand (cobbDouglasUtility 1 (1 / 2)) ![w, p]
        (w * ex15C2Economy.Lbar + p ^ 2 / (4 * w)) := hx
    rw [example_3_D_1 one_pos (by norm_num) (by norm_num) hpp hm, Set.mem_singleton_iff] at hx'
    have ex0 : x 0 = 1 / 2 * (w + p ^ 2 / (4 * w)) / w := by
      rw [hx']; simp [cobbDouglasDemand, ex15C2Economy]
    have ex1 : x 1 = (1 - 1 / 2) * (w + p ^ 2 / (4 * w)) / p := by
      rw [hx']; simp [cobbDouglasDemand, ex15C2Economy]
    -- goods-market clearing gives `w² = (3/4) p²`
    have hx1' : x 1 = Real.sqrt z := hx1
    rw [ex1, hsz] at hx1'
    have hw2 : w ^ 2 = 3 / 4 * p ^ 2 := by
      field_simp at hx1'
      nlinarith
    have hwv : w = Real.sqrt 3 / 2 * p := by
      have : (w - Real.sqrt 3 / 2 * p) * (w + Real.sqrt 3 / 2 * p) = 0 := by nlinarith [h3]
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · nlinarith [mul_pos h3pos hp]
    refine ⟨hp, hwv, ?_, ?_⟩
    · funext l
      fin_cases l
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        rw [ex0, hwv]
        field_simp
        nlinarith [h3]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [ex1, hwv]
        field_simp
        nlinarith [h3]
    · rw [hzval, hwv]
      field_simp
      nlinarith [h3]
  · rintro ⟨hp, hwv, rfl, rfl⟩
    have hw : 0 < w := by rw [hwv]; positivity
    have hzval : (1 / 3 : ℝ) = p ^ 2 / (4 * w ^ 2) := by
      rw [hwv]; field_simp; nlinarith [h3]
    have hfirm : ∀ z', 0 ≤ z' → p * Real.sqrt z' - w * z' ≤
        p * Real.sqrt (1 / 3) - w * (1 / 3) := by
      intro z' hz'
      have h1 := (sqrt_firm_profit hp hw hz').1
      have h2 := ((sqrt_firm_profit hp hw (by norm_num : (0 : ℝ) ≤ 1 / 3)).2).2 hzval
      linarith
    have hπ : p * Real.sqrt (1 / 3) - w * (1 / 3) = p ^ 2 / (4 * w) :=
      ((sqrt_firm_profit hp hw (by norm_num : (0 : ℝ) ≤ 1 / 3)).2).2 hzval
    refine ⟨⟨by norm_num, fun z' hz' => hfirm z' hz'⟩, ?_, ?_, by norm_num [ex15C2Economy]⟩
    · rw [rc_consumerOpt_iff]
      have hpp : StrictlyPositive ![w, p] := fun l => by fin_cases l; exacts [hw, hp]
      simp only [ex15C2Economy] at hπ ⊢
      rw [hπ, example_3_D_1 one_pos (by norm_num) (by norm_num) hpp (by positivity),
        Set.mem_singleton_iff]
      funext l
      fin_cases l
      · simp only [cobbDouglasDemand, Fin.zero_eta, Matrix.cons_val_zero]
        rw [hwv]
        field_simp
        nlinarith [h3]
      · simp only [cobbDouglasDemand, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hwv]
        field_simp
        nlinarith [h3]
    · simp only [ex15C2Economy, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hsq13]

/-- **Exercise 15.C.1(b)** (MWG, p. 542). Fix `p = 1`. Let `x₁(w, m)` be the leisure demand,
differentiable at `(w, wL̄ + π(w))` with partial derivatives `∂x₁/∂w = L'(1,0)`,
`∂x₁/∂m = L'(0,1)`; let the profit function satisfy Hotelling's lemma `π'(w) = -ℓ(w)` and let the
labor demand `ℓ` have derivative `ℓ'`. At an equilibrium wage (`ℓ(w) = L̄ - x₁`), the excess demand
for labor `x₁(w, wL̄ + π(w)) + ℓ(w) - L̄` has derivative `s₁₁ + ℓ'(w)`, where
`s₁₁ = ∂x₁/∂w + x₁ ∂x₁/∂m` is the compensated (Slutsky) own-price effect on leisure. -/
theorem exercise_15_C_1b {x₁ : ℝ × ℝ → ℝ} {L' : ℝ × ℝ →L[ℝ] ℝ} {ℓ π₀ : ℝ → ℝ} {Lbar w ℓ' : ℝ}
    (hx : HasFDerivAt x₁ L' (w, w * Lbar + π₀ w)) (hπ : HasDerivAt π₀ (-ℓ w) w)
    (hℓ : HasDerivAt ℓ ℓ' w) (heq : ℓ w = Lbar - x₁ (w, w * Lbar + π₀ w)) :
    HasDerivAt (fun v => x₁ (v, v * Lbar + π₀ v) + ℓ v - Lbar)
      ((L' (1, 0) + x₁ (w, w * Lbar + π₀ w) * L' (0, 1)) + ℓ') w := by
  have hg : HasDerivAt (fun v : ℝ => (v, v * Lbar + π₀ v)) (1, Lbar + -ℓ w) w :=
    (hasDerivAt_id w).prodMk (((hasDerivAt_id w).mul_const Lbar).add hπ |>.congr_deriv
      (by simp))
  have hc := hx.comp_hasDerivAt w hg
  have hL : L' (1, Lbar + -ℓ w) = L' (1, 0) + x₁ (w, w * Lbar + π₀ w) * L' (0, 1) := by
    have e : ((1 : ℝ), Lbar + -ℓ w) = ((1 : ℝ), (0 : ℝ)) +
        x₁ (w, w * Lbar + π₀ w) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp [heq]
    rw [e, map_add, map_smul, smul_eq_mul]
  rw [hL] at hc
  exact (hc.add hℓ).sub_const Lbar

/-- **Exercise 15.C.1(b)** (MWG, p. 542). Consequently, if the compensated own-price effect on
leisure is `≤ 0` (Chapter 3, negative semidefiniteness of the Slutsky matrix) and labor demand is
nonincreasing, the excess demand for labor has nonpositive slope at the equilibrium, and negative
slope if labor demand is strictly decreasing there. -/
theorem exercise_15_C_1b_sign {s ℓ' : ℝ} (hs : s ≤ 0) (hℓ : ℓ' ≤ 0) :
    s + ℓ' ≤ 0 ∧ (ℓ' < 0 → s + ℓ' < 0) :=
  ⟨by linarith, fun h => by linarith⟩

/-- **Exercise 15.C.1(b)** (MWG, p. 542), an instance (the economy of Exercise 15.C.2 with `p = 1`):
leisure demand `x₁(w, m) = m/(2w)`, labor demand `ℓ(w) = 1/(4w²)`, profits `π(w) = 1/(4w)`. At the
equilibrium wage `w* = √3/2` the hypotheses of `exercise_15_C_1b` hold and the slope of the excess
demand for labor, `s₁₁ + ℓ'(w*) = -(w* + π(w*))/(4w*²) - 1/(2w*³)`, is negative. -/
theorem exercise_15_C_1b_instance :
    let w := Real.sqrt 3 / 2
    let x₁ : ℝ × ℝ → ℝ := fun q => q.2 / (2 * q.1)
    let ℓ : ℝ → ℝ := fun v => 1 / (4 * v ^ 2)
    let π₀ : ℝ → ℝ := fun v => 1 / (4 * v)
    ∃ L' : ℝ × ℝ →L[ℝ] ℝ, ∃ ℓ' : ℝ, HasFDerivAt x₁ L' (w, w * 1 + π₀ w) ∧
      HasDerivAt π₀ (-ℓ w) w ∧ HasDerivAt ℓ ℓ' w ∧ ℓ w = 1 - x₁ (w, w * 1 + π₀ w) ∧
      L' (1, 0) + x₁ (w, w * 1 + π₀ w) * L' (0, 1) < 0 ∧ ℓ' < 0 := by
  intro w x₁ ℓ π₀
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hw : 0 < w := by positivity
  have hw2 : w ^ 2 = 3 / 4 := by simp only [w]; rw [div_pow, h3]; norm_num
  set m := w * 1 + π₀ w with hm
  have hm0 : 0 < m := by simp only [hm, π₀]; positivity
  -- the derivative of `x₁(q) = q₂/(2q₁)`
  have hd : HasFDerivAt x₁ ((1 / (2 * w)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
      (m / (2 * w ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (w, m) := by
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (w, m) :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => (2 * q.1)⁻¹)
        (-(1 / (2 * w ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (w, m) := by
      have := (hasDerivAt_inv (by positivity : (2 * w) ≠ 0)).comp_hasFDerivAt (w, m)
        ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (w, m))).const_mul 2)
      convert this using 1
      · rfl
      · rw [smul_smul]
        congr 1
        field_simp
    have := h1.mul h2
    convert this using 1
    · funext q
      simp [x₁, div_eq_mul_inv]
    · ext <;> first | (simp; done) | (simp; field_simp)
  refine ⟨_, -(1 / (2 * w ^ 3)), hd, ?_, ?_, ?_, ?_, by
    have : 0 < 1 / (2 * w ^ 3) := by positivity
    linarith⟩
  · have := (hasDerivAt_inv (by positivity : (4 * w) ≠ 0)).comp w
      ((hasDerivAt_id w).const_mul 4)
    convert this using 1
    · funext v; simp [π₀]
    · simp [ℓ]; field_simp
  · have := (hasDerivAt_inv (by positivity : (4 * w ^ 2) ≠ 0)).comp w
      (((hasDerivAt_id w).pow 2).const_mul 4)
    convert this using 1
    · funext v; simp [ℓ]
    · simp; field_simp; ring
  · simp only [ℓ, x₁, hm, π₀]
    field_simp
    nlinarith [hw2]
  · simp only [x₁, one_div, mul_inv_rev, sub_apply, smul_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul, mul_zero, ContinuousLinearMap.coe_fst', mul_one, zero_sub, sub_zero,
      neg_add_lt_iff_lt_add, add_zero]
    have e : m / (2 * w) * (w⁻¹ * 2⁻¹) = m / (4 * w ^ 2) := by field_simp; ring
    rw [e]
    have : m / (4 * w ^ 2) < m / (2 * w ^ 2) :=
      div_lt_div_of_pos_left hm0 (by positivity) (by nlinarith [pow_pos hw 2])
    exact this

/-- The economy of `exercise_15_C_1b_not_monotone`: the CES consumer
`u = (x₁⁻² + x₂⁻²)^{-1/2}`, `L̄ = 1`, `f(z) = √z`. -/
noncomputable def ces15C1Economy : RCEconomy where
  u := cesNeg2 1 1
  Lbar := 1
  f := Real.sqrt

/-- Leisure demanded by the CES consumer at `p = 1`, wage `w = c³` and profit income
`π = 1/(4w)`: `(w + 1/(4w))/(w + c)`. -/
noncomputable def cesLeisure (c : ℝ) : ℝ := (c ^ 3 + 1 / (4 * c ^ 3)) / (c ^ 3 + c)

/-- In `ces15C1Economy`, at `p = 1` and wage `w = c³` (`c > 0`): the firm's unique profit maximizing
labor input is `1/(4w²)`, with profit `1/(4w)`, and the consumer's unique optimum (with that
profit income) is `(ℓ, cℓ)`, `ℓ = cesLeisure c`. -/
theorem ces15C1_demands {c : ℝ} (hc : 0 < c) :
    (∀ z, ces15C1Economy.IsProfitMax 1 (c ^ 3) z ↔ z = 1 / (4 * (c ^ 3) ^ 2)) ∧
      1 * Real.sqrt (1 / (4 * (c ^ 3) ^ 2)) - c ^ 3 * (1 / (4 * (c ^ 3) ^ 2)) = 1 / (4 * c ^ 3) ∧
      ∀ x, ces15C1Economy.IsConsumerOpt 1 (c ^ 3) (1 / (4 * c ^ 3)) x ↔
        x = ![cesLeisure c, c * cesLeisure c] := by
  have hw : 0 < c ^ 3 := by positivity
  have hz0 : (1 : ℝ) / (4 * (c ^ 3) ^ 2) = 1 ^ 2 / (4 * (c ^ 3) ^ 2) := by ring
  have hprof : 1 * Real.sqrt (1 / (4 * (c ^ 3) ^ 2)) - c ^ 3 * (1 / (4 * (c ^ 3) ^ 2)) =
      1 / (4 * c ^ 3) := by
    have := ((sqrt_firm_profit one_pos hw (by positivity : (0 : ℝ) ≤ 1 / (4 * (c ^ 3) ^ 2))).2).2
      hz0
    rw [this]
    ring
  refine ⟨fun z => ⟨fun h => ?_, fun h => ?_⟩, hprof, fun x => ?_⟩
  · have h1 := (sqrt_firm_profit one_pos hw h.1).1
    have h2 := h.2 (1 / (4 * (c ^ 3) ^ 2)) (by positivity)
    simp only [ces15C1Economy] at h2
    rw [hprof] at h2
    rw [hz0]
    exact ((sqrt_firm_profit one_pos hw h.1).2).1 (le_antisymm h1 (by
      have : (1 : ℝ) ^ 2 / (4 * c ^ 3) = 1 / (4 * c ^ 3) := by ring
      linarith))
  · refine ⟨by rw [h]; positivity, fun z' hz' => ?_⟩
    simp only [ces15C1Economy]
    rw [h, hprof]
    have := (sqrt_firm_profit one_pos hw hz').1
    have e : (1 : ℝ) ^ 2 / (4 * c ^ 3) = 1 / (4 * c ^ 3) := by ring
    linarith
  · rw [rc_consumerOpt_iff]
    have hl0 : 0 < cesLeisure c := by unfold cesLeisure; positivity
    have hp : StrictlyPositive ![c ^ 3, (1 : ℝ)] := fun l => by
      fin_cases l
      · exact hw
      · exact one_pos
    have hdem := cesNeg2_demand one_pos one_pos hp (x := ![cesLeisure c, c * cesLeisure c])
      (by simpa using hl0) (by simpa using mul_pos hc hl0) (by simp; ring)
    have hwealth : (![c ^ 3, (1 : ℝ)] : Fin 2 → ℝ) ⬝ᵥ ![cesLeisure c, c * cesLeisure c] =
        c ^ 3 * ces15C1Economy.Lbar + 1 / (4 * c ^ 3) := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ces15C1Economy, cesLeisure]
      field_simp
    rw [hwealth] at hdem
    change x ∈ walrasianDemand (cesNeg2 1 1) _ _ ↔ _
    rw [hdem, Set.mem_singleton_iff]

/-- **Exercise 15.C.1(b)** (MWG, p. 542). The slope of the excess demand for labor
`z(w) = x₁(w, w + π(w)) + ℓ(w) - 1` is not of one sign over all wages: in `ces15C1Economy`,
`z(1/8) = 92/5 > z(1) = -1/8` (falling) but `z(8) = -247/1280 < z(27)` (rising). -/
theorem exercise_15_C_1b_not_monotone :
    let z : ℝ → ℝ := fun c => cesLeisure c + 1 / (4 * (c ^ 3) ^ 2) - 1
    z 1 < z (1 / 2) ∧ z 2 < z 3 ∧ z (1 / 2) = 92 / 5 ∧ z 1 = -1 / 8 ∧ z 2 = -247 / 1280 := by
  intro z
  simp only [z, cesLeisure]
  norm_num

/-- **Footnote 8** (MWG, p. 529). If identical consumers have an indirect utility of wealth `v` that
is concave, and the social welfare function `W` is concave, nondecreasing and symmetric (invariant
under permutations of the consumers), then the equal distribution of a given aggregate wealth
maximizes social welfare: `W(v(m₁), …, v(mₙ)) ≤ W(v(M/n), …, v(M/n))`, `M = ∑ mᵢ`. -/
theorem footnote_8 {n : ℕ} [NeZero n] {W : (Fin n → ℝ) → ℝ} {v : ℝ → ℝ}
    (hW : ConcaveOn ℝ Set.univ W) (hsym : ∀ (σ : Equiv.Perm (Fin n)) (a : Fin n → ℝ),
      W (a ∘ σ) = W a) (hmono : Monotone W) (hv : ConcaveOn ℝ Set.univ v) (m : Fin n → ℝ) :
    W (fun i => v (m i)) ≤ W (fun _ => v ((∑ i, m i) / n)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  set a : Fin n → ℝ := fun i => v (m i) with ha
  -- average over the cyclic shifts `i ↦ i + k`
  have hshift : ∀ k : Fin n, W (a ∘ (Equiv.addRight k)) = W a := fun k => hsym _ a
  have hsum : ∀ i : Fin n, ∑ k : Fin n, a (i + k) = ∑ j, a j := fun i =>
    Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun k => rfl)
  have hJ := hW.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ) / n)
    (p := fun k : Fin n => a ∘ (Equiv.addRight k)) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]) (fun _ _ => Set.mem_univ _)
  have hlhs : ∑ k : Fin n, ((1 : ℝ) / n) • W (a ∘ (Equiv.addRight k)) = W a := by
    simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      smul_eq_mul]
    field_simp
  have hrhs : ∑ k : Fin n, ((1 : ℝ) / n) • (a ∘ (Equiv.addRight k)) =
      fun _ => (∑ j, a j) / n := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Equiv.coe_addRight,
      smul_eq_mul, ← Finset.mul_sum, hsum i]
    ring
  rw [hlhs, hrhs] at hJ
  -- Jensen for `v`: the mean utility is at most the utility of the mean wealth
  have hv' := hv.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ) / n)
    (p := m) (fun _ _ => by positivity) (by simp [Finset.card_univ])
    (fun _ _ => Set.mem_univ _)
  have hmean : (∑ j, a j) / n ≤ v ((∑ i, m i) / n) := by
    simp only [smul_eq_mul, ← Finset.mul_sum] at hv'
    rw [ha]
    calc (∑ j, v (m j)) / n = 1 / n * ∑ i, v (m i) := by ring
      _ ≤ v (1 / n * ∑ i, m i) := hv'
      _ = v ((∑ i, m i) / n) := by ring_nf
  exact hJ.trans (hmono fun _ => hmean)

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Factor markets with fixed output prices (MWG Section 15.D, pp. 529-532)

Firms `j : κ` produce good `j` from `L` primary factors with production functions `fⱼ` on `ℝ^L₊`;
output prices `p` are fixed (a small open economy) and the factor endowment is `z̄`.

* p. 530: profit maximization `max pⱼ fⱼ(zⱼ) - w·zⱼ` (`IsOptimalInput`) and the factor market
  equilibrium (`IsFactorEqm`: `w ≫ 0`, optimal inputs, `∑ⱼ zⱼ = z̄`).
* (15.D.1)-(15.D.2): with concave production functions, differentiable at an interior allocation,
  an allocation with `w ≫ 0` is an equilibrium if and only if `pⱼ ∂fⱼ/∂z_{ℓj} = w_ℓ` and the factor
  markets clear (`factorEqm_iff_foc`).
* (15.D.5)-(15.D.6), p. 531: the equilibrium allocation maximizes the economy's revenue
  `∑ pⱼ fⱼ(zⱼ)` subject to `∑ zⱼ = z̄` (`factorEqm_revenue_max`).
* p. 532: the equilibrium factor prices are a supergradient of the aggregate revenue function
  (`factorEqm_supergradient`); hence an increase in the endowment of one factor cannot raise its
  equilibrium price (`factor_price_endowment_opposite`).
* **Exercise 15.D.2** (in general form): with concave production functions the production
  possibility set is convex (`exercise_15_D_2`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

variable {κ : Type*} [Fintype κ] {L : ℕ}

/-- **Section 15.D** (MWG, p. 530). Firm `j`'s profit maximization at output prices `p` and factor
prices `w`: `zⱼ ∈ ℝ^L₊` maximizes `pⱼ fⱼ(z) - w·z`. -/
def IsOptimalInput (f : κ → (Fin L → ℝ) → ℝ) (p : κ → ℝ) (w : Fin L → ℝ) (j : κ)
    (z : Fin L → ℝ) : Prop :=
  z ∈ nonnegOrthant L ∧ ∀ z' ∈ nonnegOrthant L, p j * f j z' - w ⬝ᵥ z' ≤ p j * f j z - w ⬝ᵥ z

/-- **Section 15.D** (MWG, p. 530). An equilibrium of the factor markets given output prices `p`:
factor prices `w ≫ 0` and an allocation `(z₁, …, z_J)` with every `zⱼ` profit maximizing and
`∑ⱼ zⱼ = z̄`. -/
def IsFactorEqm (f : κ → (Fin L → ℝ) → ℝ) (p : κ → ℝ) (zbar : Fin L → ℝ) (w : Fin L → ℝ)
    (z : κ → Fin L → ℝ) : Prop :=
  StrictlyPositive w ∧ (∀ j, IsOptimalInput f p w j (z j)) ∧ ∑ j, z j = zbar

/-- The tangent hyperplane of a concave function lies above it: if `f` is concave on the convex set
`S` and has derivative `f'` at `x ∈ S`, then `f y ≤ f x + f'(y - x)` for `y ∈ S`. -/
theorem concave_le_fderiv {S : Set (Fin L → ℝ)} {f : (Fin L → ℝ) → ℝ}
    {f' : (Fin L → ℝ) →L[ℝ] ℝ} {x y : Fin L → ℝ} (hfc : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hf : HasFDerivAt f f' x) : f y ≤ f x + f' (y - x) := by
  set g : ℝ → ℝ := fun t => f (x + t • (y - x)) with hg
  have hgc : ConcaveOn ℝ (Set.Icc 0 1) g := by
    have h := hfc.comp_affineMap (AffineMap.lineMap x y)
    refine h.subset (fun t ht => ?_) (convex_Icc 0 1) |>.congr fun t _ => ?_
    · simp only [Set.mem_preimage, AffineMap.lineMap_apply_module']
      have := hfc.1 hy hx ht.1 (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) (by ring)
      convert this using 1
      module
    · simp only [Function.comp_apply, AffineMap.lineMap_apply_module', hg]
      congr 1
      module
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hgd : HasDerivAt g (f' (y - x)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hf) hline
    simpa [Function.comp_def, hg] using this
  have := concave_le_tangent hgc (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) hgd
  simpa [hg] using this

/-- **(15.D.1)-(15.D.2)** (MWG, p. 530). Let the production functions be concave on `ℝ^L₊`, the
output prices nonnegative, `w ≫ 0`, and the allocation interior (`zⱼ ≫ 0`) with `fⱼ` differentiable
at `zⱼ`. Then `(w, z)` is a factor market equilibrium if and only if
`pⱼ ∂fⱼ(zⱼ)/∂z_{ℓj} = w_ℓ` for all `j, ℓ` (15.D.1) and `∑ⱼ zⱼ = z̄` (15.D.2): first-order
conditions are necessary and sufficient. -/
theorem factorEqm_iff_foc {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (hfc : ∀ j, ConcaveOn ℝ (nonnegOrthant L) (f j)) (hp : ∀ j, 0 ≤ p j)
    (hw : StrictlyPositive w) (hint : ∀ j l, 0 < z j l) {f' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hf : ∀ j, HasFDerivAt (f j) (f' j) (z j)) :
    IsFactorEqm f p zbar w z ↔
      (∀ j l, p j * f' j (Pi.single l 1) = w l) ∧ ∑ j, z j = zbar := by
  have hzm : ∀ j, z j ∈ nonnegOrthant L := fun j l => (hint j l).le
  -- the derivative of profit along a coordinate direction
  have hprof : ∀ j l, HasDerivAt (fun t : ℝ => p j * f j (z j + t • Pi.single l 1) -
      w ⬝ᵥ (z j + t • Pi.single l 1)) (p j * f' j (Pi.single l 1) - w l) 0 := by
    intro j l
    have hline : HasDerivAt (fun t : ℝ => z j + t • Pi.single l (1 : ℝ)) (Pi.single l 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l (1 : ℝ))).const_add (z j)
    have h1 := (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hf j) hline).const_mul (p j)
    have h2 : HasDerivAt (fun t : ℝ => w ⬝ᵥ (z j + t • Pi.single l 1)) (w l) 0 := by
      have : (fun t : ℝ => w ⬝ᵥ (z j + t • Pi.single l 1)) =
          fun t => w ⬝ᵥ z j + t * w l := by
        funext t
        simp [dotProduct_add, dotProduct_smul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w l)).const_add (w ⬝ᵥ z j)
    exact h1.sub h2
  constructor
  · rintro ⟨-, hopt, hsum⟩
    refine ⟨fun j l => ?_, hsum⟩
    -- an interior maximum: the derivative of profit vanishes
    have hmax : IsLocalMax (fun t : ℝ => p j * f j (z j + t • Pi.single l 1) -
        w ⬝ᵥ (z j + t • Pi.single l 1)) 0 := by
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), z j + t • Pi.single l 1 ∈ nonnegOrthant L := by
        have hc : Continuous fun t : ℝ => z j + t • Pi.single l (1 : ℝ) := by fun_prop
        have hopen : IsOpen (⋂ k, {v : Fin L → ℝ | 0 < v k}) :=
          isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
        have hmem : z j + (0 : ℝ) • Pi.single l (1 : ℝ) ∈ ⋂ k, {v : Fin L → ℝ | 0 < v k} := by
          rw [zero_smul, add_zero, Set.mem_iInter]
          exact hint j
        have := hc.continuousAt.eventually (hopen.mem_nhds hmem)
        filter_upwards [this] with t ht k
        exact (Set.mem_iInter.1 ht k).le
      filter_upwards [hev] with t ht
      have := (hopt j).2 _ ht
      simpa using this
    have := hmax.hasDerivAt_eq_zero (hprof j l)
    linarith
  · rintro ⟨hfoc, hsum⟩
    refine ⟨hw, fun j => ⟨hzm j, fun z' hz' => ?_⟩, hsum⟩
    have htan := concave_le_fderiv (hfc j) (hzm j) hz' (hf j)
    -- `pⱼ f'ⱼ(v) = w·v` for every direction `v`
    have hlin : ∀ v, p j * f' j v = w ⬝ᵥ v := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ (f' j).toLinearMap v
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this, Finset.mul_sum, dotProduct]
      refine Finset.sum_congr rfl fun l _ => ?_
      have he : (fun k => if l = k then (1 : ℝ) else 0) = Pi.single l 1 := by
        funext k
        simp [Pi.single_apply, eq_comm]
      rw [he, ← hfoc j l]
      ring
    have h1 := mul_le_mul_of_nonneg_left htan (hp j)
    rw [mul_add, hlin, dotProduct_sub] at h1
    linarith

/-- **(15.D.5)-(15.D.6)** (MWG, p. 531). The equilibrium factor allocation solves the revenue
maximizing planner's problem: `∑ⱼ pⱼ fⱼ(z'ⱼ) ≤ ∑ⱼ pⱼ fⱼ(zⱼ)` for every allocation `z'` of `z̄`
(the first welfare theorem in this model). -/
theorem factorEqm_revenue_max {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) {z' : κ → Fin L → ℝ}
    (hz' : ∀ j, z' j ∈ nonnegOrthant L) (hsum : ∑ j, z' j = zbar) :
    ∑ j, p j * f j (z' j) ≤ ∑ j, p j * f j (z j) := by
  have hle : ∑ j, (p j * f j (z' j) - w ⬝ᵥ z' j) ≤ ∑ j, (p j * f j (z j) - w ⬝ᵥ z j) :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 _ (hz' j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsum,
    h.2.2] at hle
  linarith

/-- **Section 15.D** (MWG, p. 532). The equilibrium factor prices are a supergradient of the
aggregate revenue function: for every endowment `z̃` and every allocation `z'` of `z̃`,
`∑ⱼ pⱼ fⱼ(z'ⱼ) - w·z̃ ≤ ∑ⱼ pⱼ fⱼ(zⱼ) - w·z̄` (the aggregate profit maximization (15.D.6)). -/
theorem factorEqm_supergradient {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) {z' : κ → Fin L → ℝ}
    (hz' : ∀ j, z' j ∈ nonnegOrthant L) :
    ∑ j, p j * f j (z' j) - w ⬝ᵥ ∑ j, z' j ≤ ∑ j, p j * f j (z j) - w ⬝ᵥ zbar := by
  have hle : ∑ j, (p j * f j (z' j) - w ⬝ᵥ z' j) ≤ ∑ j, (p j * f j (z j) - w ⬝ᵥ z j) :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 _ (hz' j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum,
    h.2.2] at hle
  exact hle

/-- **Section 15.D** (MWG, p. 532). Comparing two equilibria at the same output prices with
endowments `z̄` and `z̄'`, `(w' - w)·(z̄' - z̄) ≤ 0`. In particular
(`factor_price_endowment_opposite`) an increase in the endowment of a single factor cannot raise
its equilibrium price. -/
theorem factorEqm_monotone {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar zbar' w w' : Fin L → ℝ}
    {z z' : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) (h' : IsFactorEqm f p zbar' w' z') :
    (w' - w) ⬝ᵥ (zbar' - zbar) ≤ 0 := by
  have h1 := factorEqm_supergradient h (fun j => (h'.2.1 j).1)
  have h2 := factorEqm_supergradient h' (fun j => (h.2.1 j).1)
  rw [h'.2.2] at h1
  rw [h.2.2] at h2
  simp only [sub_dotProduct, dotProduct_sub] at h1 h2 ⊢
  linarith

/-- **Section 15.D** (MWG, p. 532). An increase `δ > 0` in the endowment of factor `ℓ` alone
changes its equilibrium price in the opposite direction (weakly): `w'_ℓ ≤ w_ℓ`. -/
theorem factor_price_endowment_opposite {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ}
    {zbar w w' : Fin L → ℝ} {z z' : κ → Fin L → ℝ} {l : Fin L} {δ : ℝ} (hδ : 0 < δ)
    (h : IsFactorEqm f p zbar w z) (h' : IsFactorEqm f p (zbar + δ • Pi.single l 1) w' z') :
    w' l ≤ w l := by
  have := factorEqm_monotone h h'
  simp only [add_sub_cancel_left, dotProduct_smul, smul_eq_mul, sub_dotProduct] at this
  simp only [dotProduct_single, mul_one] at this
  nlinarith

/-- **Exercise 15.D.2** (MWG, p. 542), general form: the production possibility set
`{q ≥ 0 : ∃ zⱼ ≥ 0, ∑ zⱼ ≤ z̄, qⱼ ≤ fⱼ(zⱼ)}` (with free disposal) is convex when every production
function is concave on `ℝ^L₊`. -/
def productionPossibilitySet (f : κ → (Fin L → ℝ) → ℝ) (zbar : Fin L → ℝ) : Set (κ → ℝ) :=
  {q | (∀ j, 0 ≤ q j) ∧ ∃ z : κ → Fin L → ℝ, (∀ j, z j ∈ nonnegOrthant L) ∧
    (∀ l, ∑ j, z j l ≤ zbar l) ∧ ∀ j, q j ≤ f j (z j)}

/-- **Exercise 15.D.2** (MWG, p. 542). With concave production functions the production
possibility set is convex. -/
theorem exercise_15_D_2 {f : κ → (Fin L → ℝ) → ℝ}
    (hfc : ∀ j, ConcaveOn ℝ (nonnegOrthant L) (f j)) (zbar : Fin L → ℝ) :
    Convex ℝ (productionPossibilitySet f zbar) := by
  rintro q ⟨hq0, z, hz, hzs, hqz⟩ q' ⟨hq0', z', hz', hzs', hqz'⟩ a b ha hb hab
  refine ⟨fun j => ?_, fun j => a • z j + b • z' j, fun j => ?_, fun l => ?_, fun j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hq0 j)) (mul_nonneg hb (hq0' j))
  · exact (hfc j).1 (hz j) (hz' j) ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hzs l) ha
    have h2 := mul_le_mul_of_nonneg_left (hzs' l) hb
    have h3 : a * zbar l + b * zbar l = zbar l := by rw [← add_mul, hab, one_mul]
    linarith
  · have := (hfc j).2 (hz j) (hz' j) ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    nlinarith [hqz j, hqz' j]

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The 2 × 2 production model (MWG Section 15.D, pp. 532-538)

Two constant-returns firms produce goods 1 and 2 (indices `0`, `1`) from two factors. The model is
described by the production functions `fⱼ` together with the cost-minimizing unit input vectors
`aⱼ(w) = (a_{1j}(w), a_{2j}(w))` (assumed unique, as in the book), whose standing properties are
collected in `TwoByTwo.IsModel`; the unit cost is `cⱼ(w) = w·aⱼ(w)`. We assume in addition that the
unit input vectors are continuous in `w` (true in every example, and a consequence of uniqueness
by the maximum theorem); differentiability of `cⱼ` (Shephard's lemma `∇cⱼ = aⱼ`, used by the book)
is then proved (`unitCost_hasDerivAt`).

* **Definition 15.D.1** (`TwoByTwo.FactorIntensity`).
* Constant returns: profit maximization means zero profit, `pⱼ ≤ cⱼ(w)` with equality when
  `qⱼ > 0`, and `zⱼ = qⱼ aⱼ(w)` (`crs_profitMax_iff`); the equilibrium conditions allowing for
  specialization (**Exercise 15.D.6(a)**, `exercise_15_D_6a`), (15.D.7) and (15.D.3)-(15.D.4) in
  their constant-returns form (`interior_eqm_iff`), and the equilibrium factor allocation of
  Figure 15.D.5 (`interior_eqm_allocation`).
* Under factor intensity the curves `c₁(w) = p₁` and `c₂(w) = p₂` cross at most once
  (`unitCost_ratio_strictMono`, footnote 14): the **factor price equalization theorem**
  (`factor_price_equalization`).
* **Proposition 15.D.1** (Stolper-Samuelson; `proposition_15_D_1`, global form) and its
  differential proof (`proposition_15_D_1_differential`); **Exercise 15.D.3**: the factor price
  rises proportionally more than the good's price and the owner of that factor is better off.
* **Proposition 15.D.2** (Rybczynski) and **Exercise 15.D.5** (magnification).
* **Exercise 15.D.6(b)** and footnote 15: the economy is diversified exactly when the endowment
  lies in the diversification cone.
* An instance: the Leontief model (`leontiefModel`) satisfies all standing assumptions and the
  factor intensity condition.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.CompetitiveMarkets Filter Topology

/-- **Section 15.D** (MWG, p. 532). The 2 × 2 production model: production functions `fⱼ` and
unit input vectors `aⱼ(w)` (`a j w ℓ` is the amount of factor `ℓ` per unit of good `j`). -/
structure TwoByTwo where
  /-- The production functions. -/
  f : Fin 2 → (Fin 2 → ℝ) → ℝ
  /-- The cost-minimizing unit input vectors. -/
  a : Fin 2 → (Fin 2 → ℝ) → Fin 2 → ℝ

/-- **Section 15.D** (MWG, p. 532). The standing assumptions: `fⱼ ≥ 0`, homogeneous of degree one
on `ℝ²₊`; `aⱼ(w)` (for `w ≫ 0`) produces one unit, is the unique cost minimizer among bundles
producing at least one unit, is strictly positive and continuous in the relative factor price. -/
structure TwoByTwo.IsModel (M : TwoByTwo) : Prop where
  f_nonneg : ∀ j, ∀ z ∈ nonnegOrthant 2, 0 ≤ M.f j z
  hom : ∀ j, ∀ z ∈ nonnegOrthant 2, ∀ t : ℝ, 0 ≤ t → M.f j (t • z) = t * M.f j z
  a_mem : ∀ j w, StrictlyPositive w → M.a j w ∈ nonnegOrthant 2 ∧ M.f j (M.a j w) = 1
  a_min : ∀ j w, StrictlyPositive w → ∀ z ∈ nonnegOrthant 2, 1 ≤ M.f j z →
    w ⬝ᵥ M.a j w ≤ w ⬝ᵥ z
  a_unique : ∀ j w, StrictlyPositive w → ∀ z ∈ nonnegOrthant 2, 1 ≤ M.f j z →
    w ⬝ᵥ z ≤ w ⬝ᵥ M.a j w → z = M.a j w
  a_pos : ∀ j w l, StrictlyPositive w → 0 < M.a j w l
  a_cont : ∀ j l, ContinuousOn (fun t : ℝ => M.a j ![t, 1] l) (Set.Ioi 0)

/-- **Section 15.D** (MWG, p. 532). The unit cost `cⱼ(w) = w·aⱼ(w)`. -/
def TwoByTwo.c (M : TwoByTwo) (j : Fin 2) (w : Fin 2 → ℝ) : ℝ := w ⬝ᵥ M.a j w

/-- **Definition 15.D.1** (MWG, p. 534). The production of good 1 is relatively more intensive in
factor 1 than that of good 2: `a₁₁(w)/a₂₁(w) > a₁₂(w)/a₂₂(w)` at all factor prices `w ≫ 0`. -/
def TwoByTwo.FactorIntensity (M : TwoByTwo) : Prop :=
  ∀ w, StrictlyPositive w → M.a 1 w 0 / M.a 1 w 1 < M.a 0 w 0 / M.a 0 w 1

namespace TwoByTwo

variable {M : TwoByTwo}

theorem dot_two (u v : Fin 2 → ℝ) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The relative-price vector `(ω, 1)` is strictly positive for `ω > 0`. -/
theorem relPrice_pos {ω : ℝ} (hω : 0 < ω) : StrictlyPositive ![ω, 1] := fun l => by
  fin_cases l
  · exact hω
  · exact one_pos

/-- Factor intensity in determinant form: `a₁₁a₂₂ - a₁₂a₂₁ > 0`. -/
theorem FactorIntensity.det_pos (hM : M.IsModel) (hFI : M.FactorIntensity) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) : 0 < M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 := by
  have h := hFI w hw
  have h01 := hM.a_pos 0 w 1 hw
  have h11 := hM.a_pos 1 w 1 hw
  rw [div_lt_div_iff₀ h11 h01] at h
  linarith

/-- The unit cost is positive. -/
theorem c_pos (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < M.c j w := by
  rw [c, dot_two]
  have := hM.a_pos j w 0 hw
  have := hM.a_pos j w 1 hw
  nlinarith [hw 0, hw 1]

/-- Cost minimization: `cⱼ(w') ≤ w'·aⱼ(w)` (the unit cost is concave with supergradient `aⱼ`). -/
theorem c_le (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') : M.c j w' ≤ w' ⬝ᵥ M.a j w :=
  hM.a_min j w' hw' _ (hM.a_mem j w hw).1 (hM.a_mem j w hw).2.ge

/-- The unit cost is homogeneous of degree one: `cⱼ(t w) = t cⱼ(w)` for `t > 0`. -/
theorem c_smul (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {t : ℝ}
    (ht : 0 < t) : M.c j (t • w) = t * M.c j w := by
  have htw : StrictlyPositive (t • w) := fun l => by simpa using mul_pos ht (hw l)
  apply le_antisymm
  · have := c_le hM j hw htw
    rw [smul_dotProduct, smul_eq_mul] at this
    exact this
  · have := c_le hM j htw hw
    unfold c at this ⊢
    simp only [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left this ht.le

/-- The unit input vector is homogeneous of degree zero in factor prices. -/
theorem a_smul (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {t : ℝ}
    (ht : 0 < t) : M.a j (t • w) = M.a j w := by
  have htw : StrictlyPositive (t • w) := fun l => by simpa using mul_pos ht (hw l)
  symm
  refine hM.a_unique j (t • w) htw _ (hM.a_mem j w hw).1 (hM.a_mem j w hw).2.ge ?_
  have h2 := c_smul hM j hw ht
  unfold c at h2
  rw [h2, smul_dotProduct, smul_eq_mul]

/-- The unit cost along relative prices: `gⱼ(ω) = cⱼ(ω, 1)`. -/
def g (M : TwoByTwo) (j : Fin 2) (ω : ℝ) : ℝ := M.c j ![ω, 1]

/-- `cⱼ(w) = w₂ gⱼ(w₁/w₂)`. -/
theorem c_eq_g (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.c j w = w 1 * M.g j (w 0 / w 1) := by
  have h1 := hw 1
  have e : w = w 1 • ![w 0 / w 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  rw [g, ← c_smul hM j (relPrice_pos (div_pos (hw 0) h1)) h1, ← e]

/-- `aⱼ(w) = aⱼ(w₁/w₂, 1)`. -/
theorem a_eq_rel (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.a j w = M.a j ![w 0 / w 1, 1] := by
  have h1 := hw 1
  have e : w = w 1 • ![w 0 / w 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  conv_lhs => rw [e]
  exact a_smul hM j (relPrice_pos (div_pos (hw 0) h1)) h1

/-- **Shephard's lemma along relative prices** (MWG, p. 532, Proposition 5.C.2): `gⱼ` is
differentiable with `gⱼ'(ω) = a_{1j}(ω, 1)`. -/
theorem unitCost_hasDerivAt (hM : M.IsModel) (j : Fin 2) {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (M.g j) (M.a j ![ω, 1] 0) ω := by
  have hcont : ContinuousAt (fun t : ℝ => M.a j ![t, 1] 0) ω :=
    (hM.a_cont j 0).continuousAt (Ioi_mem_nhds hω)
  -- `gⱼ(y) - gⱼ(ω) - (y - ω) aⱼ₁(ω)` lies between `(y - ω)(aⱼ₁(y) - aⱼ₁(ω))` and `0`
  refine hasDerivAt_of_sandwich (e₁ := fun y => (y - ω) * (M.a j ![y, 1] 0 - M.a j ![ω, 1] 0))
    (e₂ := fun _ => 0) ?_ (Asymptotics.isLittleO_zero _ _) ?_
  · have h0 : (fun y => M.a j ![y, 1] 0 - M.a j ![ω, 1] 0) =o[𝓝 ω] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      have := hcont.tendsto.sub_const (M.a j ![ω, 1] 0)
      simpa using this
    have := h0.mul_isBigO (Asymptotics.isBigO_refl (fun y : ℝ => y - ω) (𝓝 ω))
    simpa [mul_comm] using this
  · filter_upwards [Ioi_mem_nhds hω] with y hy
    have hy' : StrictlyPositive ![y, 1] := relPrice_pos hy
    have hω' : StrictlyPositive ![ω, 1] := relPrice_pos hω
    have h1 := c_le hM j hω' hy'
    have h2 := c_le hM j hy' hω'
    simp only [g, c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 ⊢
    constructor <;> nlinarith

/-- The unit cost `gⱼ` is continuous on `(0, ∞)`. -/
theorem g_continuousOn (hM : M.IsModel) (j : Fin 2) : ContinuousOn (M.g j) (Set.Ioi 0) :=
  fun _ hω => (unitCost_hasDerivAt hM j hω).continuousAt.continuousWithinAt

/-- `gⱼ(ω) = ω a_{1j}(ω, 1) + a_{2j}(ω, 1)`. -/
theorem g_eq (j : Fin 2) (ω : ℝ) :
    M.g j ω = ω * M.a j ![ω, 1] 0 + M.a j ![ω, 1] 1 := by
  simp only [g, c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]

/-- **Footnote 14** (MWG, p. 534). Under factor intensity the ratio `g₁(ω)/g₂(ω)` of unit costs is
strictly increasing in the relative factor price `ω = w₁/w₂`; hence the curves `c₁(w) = p₁` and
`c₂(w) = p₂` cross at most once. Its derivative is `(a₁₁a₂₂ - a₁₂a₂₁)/g₂² > 0`. -/
theorem unitCost_ratio_strictMono (hM : M.IsModel) (hFI : M.FactorIntensity) :
    StrictMonoOn (fun ω => M.g 0 ω / M.g 1 ω) (Set.Ioi 0) := by
  have hderiv : ∀ ω ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun ω => M.g 0 ω / M.g 1 ω)
      ((M.a 0 ![ω, 1] 0 * M.g 1 ω - M.g 0 ω * M.a 1 ![ω, 1] 0) / M.g 1 ω ^ 2) ω := by
    intro ω hω
    exact (unitCost_hasDerivAt hM 0 hω).div (unitCost_hasDerivAt hM 1 hω)
      (c_pos hM 1 (relPrice_pos hω)).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ fun ω hω => ?_
  · exact fun ω hω => (hderiv ω hω).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hω
    rw [(hderiv ω hω).deriv]
    have hpos := (relPrice_pos hω)
    have hdet := hFI.det_pos hM hpos
    have hg1 := c_pos hM 1 hpos
    apply div_pos _ (pow_pos hg1 2)
    rw [g_eq, g_eq]
    nlinarith

/-- `g₂` is strictly increasing (its derivative is `a₁₂ > 0`). -/
theorem g_strictMono (hM : M.IsModel) (j : Fin 2) : StrictMonoOn (M.g j) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (g_continuousOn hM j) fun ω hω => ?_
  rw [interior_Ioi] at hω
  rw [(unitCost_hasDerivAt hM j hω).deriv]
  exact hM.a_pos j _ 0 (relPrice_pos hω)

/-- `ω/gⱼ(ω)` is strictly increasing (its derivative is `a_{2j}/gⱼ² > 0`). -/
theorem div_g_strictMono (hM : M.IsModel) (j : Fin 2) :
    StrictMonoOn (fun ω => ω / M.g j ω) (Set.Ioi 0) := by
  have hderiv : ∀ ω ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun ω => ω / M.g j ω)
      ((1 * M.g j ω - ω * M.a j ![ω, 1] 0) / M.g j ω ^ 2) ω := fun ω hω =>
    (hasDerivAt_id ω).div (unitCost_hasDerivAt hM j hω) (c_pos hM j (relPrice_pos hω)).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun ω hω => (hderiv ω hω).continuousAt.continuousWithinAt) fun ω hω => ?_
  rw [interior_Ioi] at hω
  rw [(hderiv ω hω).deriv]
  apply div_pos _ (pow_pos (c_pos hM j (relPrice_pos hω)) 2)
  rw [g_eq]
  have := hM.a_pos j ![ω, 1] 1 (relPrice_pos hω)
  linarith

/-- Revealed cost minimization: as the relative price `ω` of factor 1 rises, each firm uses less of
factor 1 relative to factor 2: `0 < ω ≤ ω'` implies `a_{1j}(ω')/a_{2j}(ω') ≤ a_{1j}(ω)/a_{2j}(ω)`
(MWG, p. 532). -/
theorem intensity_antitone (hM : M.IsModel) (j : Fin 2) {ω ω' : ℝ} (hω : 0 < ω) (hωω : ω ≤ ω') :
    M.a j ![ω', 1] 0 / M.a j ![ω', 1] 1 ≤ M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 := by
  have hp := relPrice_pos hω
  have hp' := relPrice_pos (lt_of_lt_of_le hω hωω)
  have h1 := c_le hM j hp' hp
  have h2 := c_le hM j hp hp'
  simp only [c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h1 h2
  have ha0 := hM.a_pos j ![ω, 1] 0 hp
  have ha1 := hM.a_pos j ![ω, 1] 1 hp
  have ha0' := hM.a_pos j ![ω', 1] 0 hp'
  have ha1' := hM.a_pos j ![ω', 1] 1 hp'
  rcases eq_or_lt_of_le hωω with h | h
  · rw [h]
  have hA0 : M.a j ![ω', 1] 0 ≤ M.a j ![ω, 1] 0 := by nlinarith
  have hA1 : M.a j ![ω, 1] 1 ≤ M.a j ![ω', 1] 1 := by nlinarith
  rw [div_le_div_iff₀ ha1' ha1]
  nlinarith

/-- **Section 15.D** (MWG, p. 534), constant returns. With `w ≫ 0`, `zⱼ` maximizes firm `j`'s profit
if and only if `pⱼ ≤ cⱼ(w)` and `zⱼ = qⱼ aⱼ(w)` for some `qⱼ ≥ 0` with `pⱼ = cⱼ(w)` if `qⱼ > 0`
(profits are zero at the optimum). -/
theorem crs_profitMax_iff (hM : M.IsModel) {p : Fin 2 → ℝ} {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (j : Fin 2) (z : Fin 2 → ℝ) :
    IsOptimalInput M.f p w j z ↔ p j ≤ M.c j w ∧ ∃ q : ℝ, 0 ≤ q ∧ z = q • M.a j w ∧
      (0 < q → p j = M.c j w) := by
  have hf0 : M.f j 0 = 0 := by
    have := hM.hom j 0 (fun _ => le_refl _) 0 le_rfl
    simpa using this
  have ham := hM.a_mem j w hw
  constructor
  · rintro ⟨hz, hopt⟩
    have hq0 := hM.f_nonneg j z hz
    -- zero profit
    have hπle : p j * M.f j z - w ⬝ᵥ z ≤ 0 := by
      have h2z : (2 : ℝ) • z ∈ nonnegOrthant 2 := fun l => by simp; linarith [hz l]
      have := hopt _ h2z
      rw [hM.hom j z hz 2 (by norm_num), dotProduct_smul, smul_eq_mul] at this
      linarith
    have hπge : 0 ≤ p j * M.f j z - w ⬝ᵥ z := by
      have := hopt 0 (fun _ => le_refl _)
      simpa [hf0] using this
    have hpc : p j ≤ M.c j w := by
      have := hopt _ ham.1
      rw [ham.2] at this
      unfold c
      linarith
    refine ⟨hpc, M.f j z, hq0, ?_, fun hq => ?_⟩
    · rcases eq_or_lt_of_le hq0 with hq | hq
      · -- no output: no inputs
        have hwz : w ⬝ᵥ z ≤ 0 := by rw [← hq] at hπge; linarith
        have hz0 := eq_zero_of_dotProduct_nonpos hw hz hwz
        rw [← hq, zero_smul]
        exact hz0
      · have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
          simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hq0) (hz l)
        have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
          rw [hM.hom j z hz _ (inv_nonneg.2 hq0), inv_mul_cancel₀ hq.ne']
        have hcost : w ⬝ᵥ ((M.f j z)⁻¹ • z) ≤ w ⬝ᵥ M.a j w := by
          rw [dotProduct_smul, smul_eq_mul]
          have : w ⬝ᵥ z = p j * M.f j z := by linarith
          rw [this, mul_comm (p j), ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
          exact hpc
        have := hM.a_unique j w hw _ hz' hf1 hcost
        rw [← this, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
    · have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
        rw [hM.hom j z hz _ (inv_nonneg.2 hq0), inv_mul_cancel₀ hq.ne']
      have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hq0) (hz l)
      have := hM.a_min j w hw _ hz' hf1
      rw [dotProduct_smul, smul_eq_mul] at this
      have hwz : w ⬝ᵥ z = p j * M.f j z := by linarith
      rw [hwz, mul_comm (p j), ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul] at this
      exact le_antisymm hpc this
  · rintro ⟨hpc, q, hq, rfl, hqp⟩
    refine ⟨fun l => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hq (ham.1 l),
      fun z' hz' => ?_⟩
    have hval : p j * M.f j (q • M.a j w) - w ⬝ᵥ (q • M.a j w) = 0 := by
      rw [hM.hom j _ ham.1 q hq, ham.2, dotProduct_smul, smul_eq_mul]
      rcases eq_or_lt_of_le hq with h | h
      · rw [← h]; ring
      · rw [hqp h]; unfold c; ring
    rw [hval]
    have hs := hM.f_nonneg j z' hz'
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, mul_zero, zero_sub, neg_nonpos]
      exact dotProduct_nonneg_of_nonneg (fun l => (hw l).le) hz'
    · have hz'' : (M.f j z')⁻¹ • z' ∈ nonnegOrthant 2 := fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hs) (hz' l)
      have hf1 : 1 ≤ M.f j ((M.f j z')⁻¹ • z') := by
        rw [hM.hom j z' hz' _ (inv_nonneg.2 hs), inv_mul_cancel₀ h.ne']
      have := hM.a_min j w hw _ hz'' hf1
      rw [dotProduct_smul, smul_eq_mul] at this
      have h2 : M.f j z' * M.c j w ≤ w ⬝ᵥ z' := by
        unfold c
        have := mul_le_mul_of_nonneg_left this hs
        rwa [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at this
      have h3 := mul_le_mul_of_nonneg_left hpc hs
      nlinarith

/-- **Exercise 15.D.6(a)** (MWG, p. 543). The equilibrium conditions allowing for specialization:
`(w, z)` is a factor market equilibrium if and only if `w ≫ 0` and there are outputs `q ≥ 0` with
`pⱼ ≤ cⱼ(w)` (equality if `qⱼ > 0`), `zⱼ = qⱼ aⱼ(w)` and full employment
`∑ⱼ qⱼ aⱼ(w) = z̄`. -/
theorem exercise_15_D_6a (hM : M.IsModel) (p zbar w : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    IsFactorEqm M.f p zbar w z ↔ StrictlyPositive w ∧ ∃ q : Fin 2 → ℝ, (∀ j, 0 ≤ q j) ∧
      (∀ j, p j ≤ M.c j w) ∧ (∀ j, 0 < q j → p j = M.c j w) ∧ (∀ j, z j = q j • M.a j w) ∧
      ∑ j, q j • M.a j w = zbar := by
  constructor
  · rintro ⟨hw, hopt, hsum⟩
    have h := fun j => (crs_profitMax_iff hM hw j (z j)).1 (hopt j)
    choose hpc q hq hz hqp using h
    refine ⟨hw, q, hq, hpc, hqp, hz, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => (hz j).symm
  · rintro ⟨hw, q, hq, hpc, hqp, hz, hsum⟩
    refine ⟨hw, fun j => (crs_profitMax_iff hM hw j (z j)).2 ⟨hpc j, q j, hq j, hz j, hqp j⟩, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => hz j

/-- **(15.D.7) and (15.D.3)-(15.D.4)** (MWG, pp. 531, 534), constant returns: with `w ≫ 0` and
outputs `q ≫ 0`, the allocation `zⱼ = qⱼ aⱼ(w)` is an equilibrium if and only if every price equals
unit cost, `pⱼ = cⱼ(w)` (15.D.7), and the factor markets clear, `∑ⱼ qⱼ a_{ℓj}(w) = z̄_ℓ` (15.D.4,
with Shephard's lemma `∂cⱼ(w, qⱼ)/∂w_ℓ = qⱼ a_{ℓj}(w)`). -/
theorem interior_eqm_iff (hM : M.IsModel) {p zbar w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {q : Fin 2 → ℝ} (hq : ∀ j, 0 < q j) :
    IsFactorEqm M.f p zbar w (fun j => q j • M.a j w) ↔
      (∀ j, p j = M.c j w) ∧ ∑ j, q j • M.a j w = zbar := by
  rw [exercise_15_D_6a hM]
  constructor
  · rintro ⟨-, q', hq', hpc, hqp, hz, hsum⟩
    have hqq : ∀ j, q' j = q j := by
      intro j
      have := congrFun (hz j) 0
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have ha := hM.a_pos j w 0 hw
      exact (mul_right_cancel₀ ha.ne' this).symm
    refine ⟨fun j => hqp j (by rw [hqq]; exact hq j), ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [hqq]
  · rintro ⟨hpc, hsum⟩
    exact ⟨hw, q, fun j => (hq j).le, fun j => (hpc j).le, fun j _ => hpc j, fun j => rfl, hsum⟩

/-- **Figure 15.D.5** (MWG, p. 535). In an equilibrium with positive outputs each firm uses the
factors in the proportions `a_{1j}(w*)/a_{2j}(w*)`: `z*_{1j}/z*_{2j} = a_{1j}(w*)/a_{2j}(w*)`. -/
theorem interior_eqm_allocation (hM : M.IsModel) {p zbar w : Fin 2 → ℝ}
    {z : Fin 2 → Fin 2 → ℝ} (h : IsFactorEqm M.f p zbar w z) (j : Fin 2)
    (hq : 0 < M.f j (z j)) : z j 0 / z j 1 = M.a j w 0 / M.a j w 1 := by
  obtain ⟨hw, q, hq0, -, -, hz, -⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hqpos : 0 < q j := by
    rcases eq_or_lt_of_le (hq0 j) with h0 | h0
    · rw [hz j, ← h0, zero_smul, show M.f j 0 = 0 by
        simpa using hM.hom j 0 (fun _ => le_refl _) 0 le_rfl] at hq
      exact absurd hq (lt_irrefl 0)
    · exact h0
  rw [hz j]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hqpos.ne']

/-- **Factor price equalization theorem** (MWG, p. 535). Under factor intensity, there is at most
one factor price vector `w ≫ 0` solving (15.D.7), `c₁(w) = p₁`, `c₂(w) = p₂`: interior
equilibrium factor prices depend only on the technologies and the output prices. -/
theorem factor_price_equalization (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (h : ∀ j, M.c j w = p j) (h' : ∀ j, M.c j w' = p j) : w = w' := by
  have hω := div_pos (hw 0) (hw 1)
  have hω' := div_pos (hw' 0) (hw' 1)
  have hg0 : 0 < M.g 0 (w 0 / w 1) := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 (w 0 / w 1) := c_pos hM 1 (relPrice_pos hω)
  have hratio : M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) =
      M.g 0 (w' 0 / w' 1) / M.g 1 (w' 0 / w' 1) := by
    have e1 := c_eq_g hM 0 hw
    have e2 := c_eq_g hM 1 hw
    have e3 := c_eq_g hM 0 hw'
    have e4 := c_eq_g hM 1 hw'
    have hg1' : 0 < M.g 1 (w' 0 / w' 1) := c_pos hM 1 (relPrice_pos hω')
    rw [h 0] at e1; rw [h 1] at e2; rw [h' 0] at e3; rw [h' 1] at e4
    rw [div_eq_div_iff hg1.ne' hg1'.ne']
    have hw1 := hw 1
    have hw1' := hw' 1
    have : w 1 * M.g 0 (w 0 / w 1) * (w' 1 * M.g 1 (w' 0 / w' 1)) =
        w' 1 * M.g 0 (w' 0 / w' 1) * (w 1 * M.g 1 (w 0 / w 1)) := by
      rw [← e1, ← e4, ← e3, ← e2]
    have hpos : 0 < w 1 * w' 1 := mul_pos hw1 hw1'
    nlinarith
  have hωeq : w 0 / w 1 = w' 0 / w' 1 :=
    (unitCost_ratio_strictMono hM hFI).injOn hω hω' hratio
  have hw1eq : w 1 = w' 1 := by
    have e1 := c_eq_g hM 0 hw
    have e3 := c_eq_g hM 0 hw'
    rw [h 0] at e1
    rw [h' 0, ← hωeq] at e3
    have := e1.symm.trans e3
    exact mul_right_cancel₀ hg0.ne' this
  funext l
  fin_cases l
  · have := hωeq
    rw [hw1eq] at this
    exact (div_left_inj' (hw' 1).ne').1 this
  · exact hw1eq

/-- **Proposition 15.D.1** (Stolper-Samuelson theorem; MWG, p. 536), global form. Under factor
intensity, if `w` and `w'` are the (interior equilibrium) factor prices solving (15.D.7) at output
prices `p` and `p'` with `p'₁ > p₁` and `p'₂ = p₂`, then the price of factor 1 (used intensively
in good 1) rises and the price of factor 2 falls. -/
theorem proposition_15_D_1 (hM : M.IsModel) (hFI : M.FactorIntensity) {p p' w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : ∀ j, M.c j w = p j)
    (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1) :
    w 0 < w' 0 ∧ w' 1 < w 1 := by
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [← h 0, c_eq_g hM 0 hw, hωd]
  have e1 : p 1 = w 1 * M.g 1 ω := by rw [← h 1, c_eq_g hM 1 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [← h' 0, c_eq_g hM 0 hw', hωd']
  have e1' : p 1 = w' 1 * M.g 1 ω' := by rw [← hp1, ← h' 1, c_eq_g hM 1 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hg1' : 0 < M.g 1 ω' := c_pos hM 1 (relPrice_pos hω')
  have hw1 := hw 1
  have hw1' := hw' 1
  have hp1pos : 0 < p 1 := by rw [e1]; positivity
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  -- the relative factor price rises
  have hlt : ω < ω' := by
    have hmono := unitCost_ratio_strictMono hM hFI
    rw [← hmono.lt_iff_lt hω hω', div_lt_div_iff₀ hg1 hg1']
    have h1 : M.g 0 ω * M.g 1 ω' * (w 1 * w' 1) = p 0 * p 1 := by rw [e0, e1']; ring
    have h2 : M.g 0 ω' * M.g 1 ω * (w 1 * w' 1) = p' 0 * p 1 := by rw [e0', e1]; ring
    have : M.g 0 ω * M.g 1 ω' * (w 1 * w' 1) < M.g 0 ω' * M.g 1 ω * (w 1 * w' 1) := by
      rw [h1, h2]
      exact mul_lt_mul_of_pos_right hp0 hp1pos
    exact lt_of_mul_lt_mul_right this (by positivity)
  constructor
  · -- `w₁ = p₁ (ω/g₁(ω))` with `ω ↦ ω/g₁(ω)` increasing
    have hm := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hlt
    have hw0 : w 0 = p 0 * (ω / M.g 0 ω) := by
      have : w 1 * M.g 0 ω * (ω / M.g 0 ω) = w 1 * ω := by field_simp
      rw [e0, this, hωd]; field_simp
    have hw0' : w' 0 = p' 0 * (ω' / M.g 0 ω') := by
      have : w' 1 * M.g 0 ω' * (ω' / M.g 0 ω') = w' 1 * ω' := by field_simp
      rw [e0', this, hωd']; field_simp
    rw [hw0, hw0']
    have : 0 < ω / M.g 0 ω := div_pos hω hg0
    have : ω / M.g 0 ω < ω' / M.g 0 ω' := hm
    nlinarith
  · -- `w₂ = p₂/g₂(ω)` with `g₂` increasing
    have hgm := (g_strictMono hM 1).lt_iff_lt hω hω' |>.2 hlt
    have hw1e : w 1 = p 1 / M.g 1 ω := by rw [e1]; field_simp
    have hw1e' : w' 1 = p 1 / M.g 1 ω' := by rw [e1']; field_simp
    rw [hw1e, hw1e']
    exact div_lt_div_of_pos_left hp1pos hg1 hgm

/-- **Exercise 15.D.3** (MWG, p. 543). In the setting of Proposition 15.D.1 the price of the
intensive factor rises proportionally more than the price of the good: `w'₁/w₁ > p'₁/p₁`. -/
theorem exercise_15_D_3 (hM : M.IsModel) (hFI : M.FactorIntensity) {p p' w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : ∀ j, M.c j w = p j)
    (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1) :
    p' 0 / p 0 < w' 0 / w 0 := by
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have hlt := proposition_15_D_1 hM hFI hw hw' h h' hp0 hp1
  have hωlt : ω < ω' := by
    rw [hωd, hωd', div_lt_div_iff₀ (hw 1) (hw' 1)]
    nlinarith [hw 0, hw' 1]
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [← h 0, c_eq_g hM 0 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [← h' 0, c_eq_g hM 0 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hm : ω / M.g 0 ω < ω' / M.g 0 ω' := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hωlt
  have hw1 := hw 1
  have hw1' := hw' 1
  have hw0 : w 0 = p 0 * (ω / M.g 0 ω) := by
    have : w 1 * M.g 0 ω * (ω / M.g 0 ω) = w 1 * ω := by field_simp
    rw [e0, this, hωd]; field_simp
  have hw0' : w' 0 = p' 0 * (ω' / M.g 0 ω') := by
    have : w' 1 * M.g 0 ω' * (ω' / M.g 0 ω') = w' 1 * ω' := by field_simp
    rw [e0', this, hωd']; field_simp
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  have hp0' : 0 < p' 0 := by linarith
  have hr : 0 < ω / M.g 0 ω := div_pos hω hg0
  have hr' : 0 < ω' / M.g 0 ω' := div_pos hω' hg0'
  rw [hw0, hw0', div_lt_div_iff₀ hp0pos (mul_pos hp0pos hr)]
  nlinarith [mul_pos hp0' hp0pos]

/-- **Exercise 15.D.3** (MWG, p. 543). A consumer who owns one unit of the intensive factor only is
strictly better off after the price increase, whatever his (locally nonsatiated) preferences:
every bundle affordable before is strictly inside the new budget set, so some bundle affordable
afterwards is strictly preferred. -/
theorem exercise_15_D_3_welfare (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p p' w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (h : ∀ j, M.c j w = p j) (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1)
    {u : (Fin 2 → ℝ) → ℝ} (hlns : UtilityLNS u) {x : Fin 2 → ℝ}
    (hx : x ∈ budgetSet p (w 0)) : ∃ y ∈ budgetSet p' (w' 0), u x < u y := by
  have hmag := exercise_15_D_3 hM hFI hw hw' h h' hp0 hp1
  have hp0pos : 0 < p 0 := by
    rw [← h 0]; exact c_pos hM 0 hw
  have hp1pos : 0 < p 1 := by
    rw [← h 1]; exact c_pos hM 1 hw
  have hb := hx.2
  rw [dot_two] at hb
  have hx0 := hx.1 0
  have hx1 := hx.1 1
  have hcost : p' ⬝ᵥ x < w' 0 := by
    rw [dot_two, hp1]
    rw [div_lt_div_iff₀ hp0pos (hw 0)] at hmag
    have h1 : p' 0 * x 0 + p 1 * x 1 ≤ p' 0 / p 0 * (p 0 * x 0 + p 1 * x 1) := by
      rw [mul_add, ← mul_assoc, div_mul_cancel₀ _ hp0pos.ne']
      have : p 1 * x 1 ≤ p' 0 / p 0 * (p 1 * x 1) := by
        have : 1 ≤ p' 0 / p 0 := by rw [le_div_iff₀ hp0pos]; linarith
        nlinarith [mul_nonneg hp1pos.le hx1]
      linarith
    have h2 : p' 0 / p 0 * (p 0 * x 0 + p 1 * x 1) ≤ p' 0 / p 0 * w 0 :=
      mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) hp0pos.le)
    have h3 : p' 0 / p 0 * w 0 < w' 0 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp0pos]
      linarith
    linarith
  obtain ⟨y, hy, hpy, hu⟩ := hlns.exists_better p' hx.1 hcost
  exact ⟨y, ⟨hy, hpy.le⟩, hu⟩

/-- **Proposition 15.D.1** (MWG, pp. 536-537), the book's differential proof. With
`A = [[a₁₁, a₂₁], [a₁₂, a₂₂]]` (rows: `dpⱼ = ∇cⱼ·dw`) and `|A| = a₁₁a₂₂ - a₁₂a₂₁ > 0` (factor
intensity), `A⁻¹ = |A|⁻¹ [[a₂₂, -a₂₁], [-a₁₂, a₁₁]]` has positive diagonal and negative off-diagonal
entries, and the response to `dp = (1, 0)` is `dw = (a₂₂/|A|, -a₁₂/|A|)`, so `dw₁ > 0 > dw₂`. -/
theorem proposition_15_D_1_differential {a₁₁ a₂₁ a₁₂ a₂₂ : ℝ} (h₁₂ : 0 < a₁₂) (h₂₂ : 0 < a₂₂)
    (hdet : 0 < a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    !![a₁₁, a₂₁; a₁₂, a₂₂] * ((a₁₁ * a₂₂ - a₁₂ * a₂₁)⁻¹ • !![a₂₂, -a₂₁; -a₁₂, a₁₁]) = 1 ∧
      (∀ dw₁ dw₂ : ℝ, (a₁₁ * dw₁ + a₂₁ * dw₂ = 1 ∧ a₁₂ * dw₁ + a₂₂ * dw₂ = 0) ↔
        (dw₁ = a₂₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) ∧ dw₂ = -a₁₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁))) ∧
      0 < a₂₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) ∧ -a₁₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0 := by
  have hD := hdet.ne'
  refine ⟨?_, fun dw₁ dw₂ => ⟨fun ⟨e1, e2⟩ => ⟨?_, ?_⟩, fun ⟨e1, e2⟩ => ⟨?_, ?_⟩⟩, by positivity,
    div_neg_of_neg_of_pos (by linarith) hdet⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  · rw [eq_div_iff hD]; linear_combination a₂₂ * e1 - a₂₁ * e2
  · rw [eq_div_iff hD]; linear_combination -a₁₂ * e1 + a₁₁ * e2
  · rw [e1, e2]; field_simp; ring
  · rw [e1, e2]; field_simp; ring

/-- The outputs supporting an interior allocation at given factor prices solve
`∑ⱼ qⱼ aⱼ = z̄` (Cramer's rule): `q₁ = (a₂₂z̄₁ - a₁₂z̄₂)/|A|`, `q₂ = (a₁₁z̄₂ - a₂₁z̄₁)/|A|`. -/
theorem outputs_cramer {a : Fin 2 → Fin 2 → ℝ} {q zbar : Fin 2 → ℝ}
    (hD : a 0 0 * a 1 1 - a 1 0 * a 0 1 ≠ 0) (h : ∑ j, q j • a j = zbar) :
    q 0 = (a 1 1 * zbar 0 - a 1 0 * zbar 1) / (a 0 0 * a 1 1 - a 1 0 * a 0 1) ∧
      q 1 = (a 0 0 * zbar 1 - a 0 1 * zbar 0) / (a 0 0 * a 1 1 - a 1 0 * a 0 1) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
  constructor
  · rw [eq_div_iff hD, ← h0, ← h1]; ring
  · rw [eq_div_iff hD, ← h0, ← h1]; ring

/-- **Proposition 15.D.2** (Rybczynski theorem; MWG, p. 537). Under factor intensity, compare
interior equilibria (`q ≫ 0`, `q' ≫ 0`) at the same output prices with endowments `z̄` and
`z̄' = z̄ + (δ, 0)`, `δ > 0`: the output of good 1 (intensive in factor 1) rises and that of good 2
falls. -/
theorem proposition_15_D_2 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w w' q q' : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p (zbar + ![δ, 0]) w' (fun j => q' j • M.a j w')) :
    q 0 < q' 0 ∧ q' 1 < q 1 := by
  obtain ⟨hpc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hpc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hww : w = w' := factor_price_equalization hM hFI hw hw' (fun j => (hpc j).symm)
    (fun j => (hpc' j).symm)
  subst hww
  have hdet := hFI.det_pos hM hw
  obtain ⟨c0, c1⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum
  obtain ⟨c0', c1'⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum'
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at c0' c1'
  have ha11 := hM.a_pos 1 w 1 hw
  have ha01 := hM.a_pos 0 w 1 hw
  constructor
  · rw [c0, c0', div_lt_div_iff_of_pos_right hdet]
    nlinarith
  · rw [c1, c1', div_lt_div_iff_of_pos_right hdet]
    nlinarith

/-- **Exercise 15.D.5** (MWG, p. 543). In the Rybczynski setting the output of good 1 rises
proportionally more than the endowment of factor 1: `q'₁/q₁ > z̄'₁/z̄₁`. -/
theorem exercise_15_D_5 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w w' q q' : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p (zbar + ![δ, 0]) w' (fun j => q' j • M.a j w')) :
    (zbar 0 + δ) / zbar 0 < q' 0 / q 0 := by
  obtain ⟨hpc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hpc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hww : w = w' := factor_price_equalization hM hFI hw hw' (fun j => (hpc j).symm)
    (fun j => (hpc' j).symm)
  subst hww
  have hdet := hFI.det_pos hM hw
  obtain ⟨c0, -⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum
  obtain ⟨c0', -⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum'
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at c0'
  have hz := congrFun hsum 0
  have hz1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz hz1
  have hz0pos : 0 < zbar 0 := by
    rw [← hz]
    have := hM.a_pos 0 w 0 hw
    have := hM.a_pos 1 w 0 hw
    nlinarith [hq 0, hq 1]
  have hz1pos : 0 < zbar 1 := by
    rw [← hz1]
    have := hM.a_pos 0 w 1 hw
    have := hM.a_pos 1 w 1 hw
    nlinarith [hq 0, hq 1]
  have ha10 := hM.a_pos 1 w 0 hw
  rw [div_lt_div_iff₀ hz0pos (hq 0), c0, c0']
  rw [div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff_of_pos_right hdet]
  nlinarith [mul_pos (mul_pos ha10 hz1pos) hδ]

/-- **Exercise 15.D.6(b)** and **footnote 15** (MWG, pp. 535, 543). Let `ŵ ≫ 0` solve (15.D.7),
`cⱼ(ŵ) = pⱼ`, let `z̄ ≫ 0`, and let `w` with outputs `q` satisfy the equilibrium conditions of
Exercise 15.D.6(a). Under factor
intensity both outputs are positive if and only if `z̄` lies in the diversification cone,
`a₁₂(ŵ)/a₂₂(ŵ) < z̄₁/z̄₂ < a₁₁(ŵ)/a₂₁(ŵ)`. -/
theorem exercise_15_D_6b (hM : M.IsModel) (hFI : M.FactorIntensity) {p zbar w what : Fin 2 → ℝ}
    {q : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hq : ∀ j, 0 ≤ q j) (hpc : ∀ j, p j ≤ M.c j w) (hqp : ∀ j, 0 < q j → p j = M.c j w)
    (hw : StrictlyPositive w) (hsum : ∑ j, q j • M.a j w = zbar) :
    (∀ j, 0 < q j) ↔ M.a 1 what 0 / M.a 1 what 1 < zbar 0 / zbar 1 ∧
      zbar 0 / zbar 1 < M.a 0 what 0 / M.a 0 what 1 := by
  have hz0 := congrFun hsum 0
  have hz1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz0 hz1
  constructor
  · intro hqpos
    have hww : w = what := factor_price_equalization hM hFI hw hwhat
      (fun j => (hqp j (hqpos j)).symm) hc
    subst hww
    have a00 := hM.a_pos 0 w 0 hw
    have a01 := hM.a_pos 0 w 1 hw
    have a10 := hM.a_pos 1 w 0 hw
    have a11 := hM.a_pos 1 w 1 hw
    have hdet := hFI.det_pos hM hw
    have hq0 := hqpos 0
    have hq1 := hqpos 1
    rw [← hz0, ← hz1]
    constructor
    · rw [div_lt_div_iff₀ a11 (by positivity)]
      nlinarith [mul_pos hq0 hdet]
    · rw [div_lt_div_iff₀ (by positivity) a01]
      nlinarith [mul_pos hq1 hdet]
  · rintro ⟨hlo, hhi⟩
    have hω := div_pos (hw 0) (hw 1)
    have hωh := div_pos (hwhat 0) (hwhat 1)
    have hratio := unitCost_ratio_strictMono hM hFI
    have eg : ∀ j, M.c j w = w 1 * M.g j (w 0 / w 1) := fun j => c_eq_g hM j hw
    have egh : ∀ j, M.c j what = what 1 * M.g j (what 0 / what 1) := fun j => c_eq_g hM j hwhat
    have hgpos : ∀ j, 0 < M.g j (w 0 / w 1) := fun j => c_pos hM j (relPrice_pos hω)
    have hghpos : ∀ j, 0 < M.g j (what 0 / what 1) := fun j => c_pos hM j (relPrice_pos hωh)
    have hrel : M.a 0 w = M.a 0 ![w 0 / w 1, 1] ∧ M.a 1 w = M.a 1 ![w 0 / w 1, 1] :=
      ⟨a_eq_rel hM 0 hw, a_eq_rel hM 1 hw⟩
    have hrelh : M.a 0 what = M.a 0 ![what 0 / what 1, 1] ∧
        M.a 1 what = M.a 1 ![what 0 / what 1, 1] :=
      ⟨a_eq_rel hM 0 hwhat, a_eq_rel hM 1 hwhat⟩
    by_contra hnot
    simp only [not_forall, not_lt] at hnot
    obtain ⟨j, hj⟩ := hnot
    have hqj : q j = 0 := le_antisymm hj (hq j)
    fin_cases j
    · -- specialization in good 2: `z̄ = q₂ a₂(w)`, `c₂(w) = p₂`, `c₁(w) ≥ p₁`
      have hq1 : 0 < q 1 := by
        rcases eq_or_lt_of_le (hq 1) with h | h
        · exfalso
          simp only [Fin.zero_eta] at hqj
          rw [hqj, ← h] at hz0
          simp at hz0
          linarith [hz 0]
        · exact h
      have hp1 := hqp 1 hq1
      have hp0 := hpc 0
      -- the relative factor price is at least `ŵ₁/ŵ₂`
      have hge : what 0 / what 1 ≤ w 0 / w 1 := by
        by_contra hlt
        rw [not_le] at hlt
        have := (hratio.lt_iff_lt hω hωh).2 hlt
        rw [div_lt_div_iff₀ (hgpos 1) (hghpos 1)] at this
        have h1 := hc 0
        have h2 := hc 1
        rw [egh 0] at h1
        rw [egh 1] at h2
        rw [eg 1] at hp1
        rw [eg 0] at hp0
        have hw1 := hw 1
        have hwh1 := hwhat 1
        have key := mul_lt_mul_of_pos_left this (mul_pos hwh1 hw1)
        have key2 : (w 1 * M.g 0 (w 0 / w 1)) * (what 1 * M.g 1 (what 0 / what 1)) <
            (what 1 * M.g 0 (what 0 / what 1)) * (w 1 * M.g 1 (w 0 / w 1)) := by
          linarith [key]
        rw [h1, h2, ← hp1] at key2
        have hp1pos : 0 < p 1 := by rw [← h2]; exact mul_pos hwh1 (hghpos 1)
        have := lt_of_mul_lt_mul_right key2 hp1pos.le
        linarith
      have hint := intensity_antitone hM 1 hωh hge
      rw [← hrel.2, ← hrelh.2] at hint
      simp only [Fin.zero_eta] at hqj
      rw [hqj, zero_mul, zero_add] at hz0 hz1
      have : zbar 0 / zbar 1 = M.a 1 w 0 / M.a 1 w 1 := by
        rw [← hz0, ← hz1, mul_div_mul_left _ _ hq1.ne']
      linarith
    · -- specialization in good 1
      have hq0 : 0 < q 0 := by
        rcases eq_or_lt_of_le (hq 0) with h | h
        · exfalso
          simp only [Fin.mk_one] at hqj
          rw [hqj, ← h] at hz0
          simp at hz0
          linarith [hz 0]
        · exact h
      have hp0 := hqp 0 hq0
      have hp1 := hpc 1
      have hle : w 0 / w 1 ≤ what 0 / what 1 := by
        by_contra hlt
        rw [not_le] at hlt
        have := (hratio.lt_iff_lt hωh hω).2 hlt
        rw [div_lt_div_iff₀ (hghpos 1) (hgpos 1)] at this
        have h1 := hc 0
        have h2 := hc 1
        rw [egh 0] at h1
        rw [egh 1] at h2
        rw [eg 0] at hp0
        rw [eg 1] at hp1
        have hw1 := hw 1
        have hwh1 := hwhat 1
        have key := mul_lt_mul_of_pos_left this (mul_pos hwh1 hw1)
        have key2 : (what 1 * M.g 0 (what 0 / what 1)) * (w 1 * M.g 1 (w 0 / w 1)) <
            (w 1 * M.g 0 (w 0 / w 1)) * (what 1 * M.g 1 (what 0 / what 1)) := by
          linarith [key]
        rw [h1, h2, ← hp0] at key2
        have hp0pos : 0 < p 0 := by rw [← h1]; exact mul_pos hwh1 (hghpos 0)
        have := lt_of_mul_lt_mul_left key2 hp0pos.le
        linarith
      have hint := intensity_antitone hM 0 hω hle
      rw [← hrel.1, ← hrelh.1] at hint
      simp only [Fin.mk_one] at hqj
      rw [hqj, zero_mul, add_zero] at hz0 hz1
      have : zbar 0 / zbar 1 = M.a 0 w 0 / M.a 0 w 1 := by
        rw [← hz0, ← hz1, mul_div_mul_left _ _ hq0.ne']
      linarith

end TwoByTwo

/-- An instance of the 2 × 2 model: Leontief technologies `f₁(z) = min(z₁/2, z₂)`,
`f₂(z) = min(z₁, z₂/2)` with unit input vectors `a₁ = (2, 1)` and `a₂ = (1, 2)`. -/
noncomputable def leontiefModel : TwoByTwo where
  f := ![fun z => min (z 0 / 2) (z 1), fun z => min (z 0) (z 1 / 2)]
  a := fun j _ => ![![2, 1], ![1, 2]] j

/-- The Leontief model satisfies the standing assumptions of the 2 × 2 model. -/
theorem leontiefModel_isModel : leontiefModel.IsModel where
  f_nonneg := by
    intro j z hz
    fin_cases j
    · exact le_min (by linarith [hz 0]) (hz 1)
    · exact le_min (hz 0) (by linarith [hz 1])
  hom := by
    intro j z _ t ht
    fin_cases j
    · change min (t * z 0 / 2) (t * z 1) = t * min (z 0 / 2) (z 1)
      rw [mul_min_of_nonneg _ _ ht, mul_div_assoc]
    · change min (t * z 0) (t * z 1 / 2) = t * min (z 0) (z 1 / 2)
      rw [mul_min_of_nonneg _ _ ht, mul_div_assoc]
  a_mem := by
    intro j w _
    fin_cases j
    · refine ⟨fun l => by fin_cases l <;> norm_num [leontiefModel], ?_⟩
      norm_num [leontiefModel]
    · refine ⟨fun l => by fin_cases l <;> norm_num [leontiefModel], ?_⟩
      norm_num [leontiefModel]
  a_min := by
    intro j w hw z _ hz
    have hw0 := hw 0
    have hw1 := hw 1
    fin_cases j
    · change 1 ≤ min (z 0 / 2) (z 1) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail]
      nlinarith [hz.1, hz.2]
    · change 1 ≤ min (z 0) (z 1 / 2) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail]
      nlinarith [hz.1, hz.2]
  a_unique := by
    intro j w hw z _ hz hle
    have hw0 := hw 0
    have hw1 := hw 1
    fin_cases j
    · change 1 ≤ min (z 0 / 2) (z 1) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail] at hle
      have e0 : z 0 = 2 := by nlinarith [hz.1, hz.2]
      have e1 : z 1 = 1 := by nlinarith [hz.1, hz.2]
      funext l
      fin_cases l
      · simpa [leontiefModel] using e0
      · simpa [leontiefModel] using e1
    · change 1 ≤ min (z 0) (z 1 / 2) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail] at hle
      have e0 : z 0 = 1 := by nlinarith [hz.1, hz.2]
      have e1 : z 1 = 2 := by nlinarith [hz.1, hz.2]
      funext l
      fin_cases l
      · simpa [leontiefModel] using e0
      · simpa [leontiefModel] using e1
  a_pos := by
    intro j w l _
    fin_cases j <;> fin_cases l <;> norm_num [leontiefModel]
  a_cont := fun _ _ => continuousOn_const

/-- The Leontief model satisfies the factor intensity condition: `2/1 > 1/2`. -/
theorem leontiefModel_factorIntensity : leontiefModel.FactorIntensity := by
  intro w _
  norm_num [leontiefModel]

/-- Non-vacuity of Propositions 15.D.1-15.D.2 in the Leontief model: `w = (1, 1)` solves (15.D.7)
at `p = (3, 3)`, `w' = (5/3, 2/3)` at `p' = (4, 3)` (Stolper-Samuelson: `w₁` rises, `w₂` falls),
and at `w = (1, 1)` the endowments `(3, 3)` and `(4, 3)` are produced with outputs `(1, 1)` and
`(5/3, 2/3)` (Rybczynski: `q₁` rises, `q₂` falls). -/
theorem leontief_instances :
    (∀ j, leontiefModel.c j ![1, 1] = ![3, 3] j) ∧
      (∀ j, leontiefModel.c j ![5 / 3, 2 / 3] = ![4, 3] j) ∧
      IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) ∧
      IsFactorEqm leontiefModel.f ![3, 3] (![3, 3] + ![1, 0]) ![1, 1]
        (fun j => (![5 / 3, 2 / 3] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) := by
  have hc1 : ∀ j, leontiefModel.c j ![1, 1] = ![3, 3] j := by
    intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two]
  have hw : StrictlyPositive (![1, 1] : Fin 2 → ℝ) := fun l => by fin_cases l <;> norm_num
  refine ⟨hc1, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two]
  · refine (TwoByTwo.interior_eqm_iff (p := ![3, 3]) (zbar := ![3, 3]) (q := ![1, 1])
      leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num)).2 ⟨fun j => (hc1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]
  · refine (TwoByTwo.interior_eqm_iff (p := ![3, 3]) (zbar := ![3, 3] + ![1, 0])
      (q := ![5 / 3, 2 / 3]) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num)).2 ⟨fun j => (hc1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 15.D.7 and 15.D.9 (MWG p. 544)

* **Exercise 15.D.7**: `f₁ = 2√z₁₁ + √z₂₁`, `f₂ = √z₁₂ + 2√z₂₂`, `p = (1, 1)`, endowment
  `z̄ ≫ 0`. The unique equilibrium is `z₁ = (4z̄₁/5, z̄₂/5)`, `z₂ = (z̄₁/5, 4z̄₂/5)`,
  `w = (√5/(2√z̄₁), √5/(2√z̄₂))` (`exercise_15_D_7`); the same allocation is the unique solution
  of the revenue maximization problem (15.D.5) (`exercise_15_D_7_revenue`) and satisfies the
  first-order conditions (15.D.1)-(15.D.2), from which `factorEqm_iff_foc` recovers the equilibrium
  (`exercise_15_D_7_foc`).
* **Exercise 15.D.9** (Heckscher-Ohlin): as printed the claim is false: with linear (homogeneous,
  concave, increasing) utilities demand is not unique, and in a Leontief world with nonspecialized
  countries the factor-1-abundant country can import good 1 (`exercise_15_D_9_counterexample`).
  It holds when the countries' consumption vectors are proportional, e.g. when demand is
  unique (`exercise_15_D_9`, `exercise_15_D_9_unique_demand`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-! ### Exercise 15.D.7 -/

/-- **Exercise 15.D.7** (MWG, p. 544). The production functions `f₁(z) = 2√z₁ + √z₂` and
`f₂(z) = √z₁ + 2√z₂`, written `k₁₁√z₁ + k₂₁√z₂` with coefficients `k`. -/
noncomputable def ex15D7f : Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun j z => ![![2, 1], ![1, 2]] j 0 * Real.sqrt (z 0) + ![![2, 1], ![1, 2]] j 1 * Real.sqrt (z 1)

/-- The coefficients `k` of Exercise 15.D.7. -/
def ex15D7k : Fin 2 → Fin 2 → ℝ := ![![2, 1], ![1, 2]]

theorem ex15D7k_pos (j l : Fin 2) : 0 < ex15D7k j l := by
  fin_cases j <;> fin_cases l <;> norm_num [ex15D7k]

/-- Profit maximization in Exercise 15.D.7: at `w ≫ 0` (output price 1) firm `j` demands exactly
`z_ℓ = k_{jℓ}²/(4w_ℓ²)`. -/
theorem ex15D7_optimal_iff {w : Fin 2 → ℝ} (hw : StrictlyPositive w) (j : Fin 2)
    (z : Fin 2 → ℝ) : IsOptimalInput ex15D7f ![1, 1] w j z ↔
      z = fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) := by
  have hk := ex15D7k_pos j
  set zs : Fin 2 → ℝ := fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) with hzs
  have hone : (![1, 1] : Fin 2 → ℝ) j = 1 := by fin_cases j <;> rfl
  have hprof : ∀ v ∈ nonnegOrthant 2, (![1, 1] : Fin 2 → ℝ) j * ex15D7f j v - w ⬝ᵥ v =
      (ex15D7k j 0 * Real.sqrt (v 0) - w 0 * v 0) +
        (ex15D7k j 1 * Real.sqrt (v 1) - w 1 * v 1) := by
    intro v _
    rw [hone]
    simp only [ex15D7f, ex15D7k, dotProduct, Fin.sum_univ_two, one_mul]
    ring
  have hzsm : zs ∈ nonnegOrthant 2 := fun l => by simp only [hzs]; positivity
  have hb : ∀ l, ∀ v : ℝ, 0 ≤ v → ex15D7k j l * Real.sqrt v - w l * v ≤
      ex15D7k j l ^ 2 / (4 * w l) ∧
      (ex15D7k j l * Real.sqrt v - w l * v = ex15D7k j l ^ 2 / (4 * w l) ↔ v = zs l) :=
    fun l v hv => sqrt_firm_profit (hk l) (hw l) hv
  have hzsval : (![1, 1] : Fin 2 → ℝ) j * ex15D7f j zs - w ⬝ᵥ zs =
      ex15D7k j 0 ^ 2 / (4 * w 0) + ex15D7k j 1 ^ 2 / (4 * w 1) := by
    rw [hprof zs hzsm, ((hb 0 _ (hzsm 0)).2).2 rfl, ((hb 1 _ (hzsm 1)).2).2 rfl]
  constructor
  · rintro ⟨hz, hopt⟩
    have h1 := hopt zs hzsm
    rw [hprof z hz, hzsval] at h1
    have b0 := (hb 0 _ (hz 0)).1
    have b1 := (hb 1 _ (hz 1)).1
    funext l
    fin_cases l
    · exact ((hb 0 _ (hz 0)).2).1 (by linarith)
    · exact ((hb 1 _ (hz 1)).2).1 (by linarith)
  · rintro rfl
    refine ⟨hzsm, fun v hv => ?_⟩
    rw [hprof v hv, hzsval]
    linarith [(hb 0 _ (hv 0)).1, (hb 1 _ (hv 1)).1]

/-- **Exercise 15.D.7** (MWG, p. 544). The equilibrium factor allocation. -/
noncomputable def ex15D7alloc (zbar : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![4 * zbar 0 / 5, zbar 1 / 5], ![zbar 0 / 5, 4 * zbar 1 / 5]]

/-- **Exercise 15.D.7** (MWG, p. 544). The equilibrium factor prices. -/
noncomputable def ex15D7w (zbar : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt 5 / (2 * Real.sqrt (zbar 0)), Real.sqrt 5 / (2 * Real.sqrt (zbar 1))]

/-- **Exercise 15.D.7** (MWG, p. 544). For `z̄ ≫ 0` and `p = (1, 1)` the unique factor market
equilibrium is `z₁* = (4z̄₁/5, z̄₂/5)`, `z₂* = (z̄₁/5, 4z̄₂/5)` with
`w* = (√5/(2√z̄₁), √5/(2√z̄₂))`. -/
theorem exercise_15_D_7 {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) (w : Fin 2 → ℝ)
    (z : Fin 2 → Fin 2 → ℝ) :
    IsFactorEqm ex15D7f ![1, 1] zbar w z ↔ w = ex15D7w zbar ∧ z = ex15D7alloc zbar := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : ∀ l, Real.sqrt (zbar l) ^ 2 = zbar l := fun l => Real.sq_sqrt (hz l).le
  have hspos : ∀ l, 0 < Real.sqrt (zbar l) := fun l => Real.sqrt_pos.2 (hz l)
  have hwpos : StrictlyPositive (ex15D7w zbar) := fun l => by
    have h5p : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    fin_cases l
    · exact div_pos h5p (mul_pos two_pos (hspos 0))
    · exact div_pos h5p (mul_pos two_pos (hspos 1))
  have hwsq : ∀ l, 4 * ex15D7w zbar l ^ 2 = 5 / zbar l := by
    intro l
    fin_cases l <;> simp only [ex15D7w, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> (rw [div_pow, mul_pow, h5, hs]; field_simp; ring)
  constructor
  · rintro ⟨hw, hopt, hsum⟩
    have hz' : ∀ j, z j = fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) := fun j =>
      (ex15D7_optimal_iff hw j (z j)).1 (hopt j)
    -- market clearing gives `4 w_ℓ² = 5/z̄_ℓ`
    have hclear : ∀ l, 4 * w l ^ 2 = 5 / zbar l := by
      intro l
      have := congrFun hsum l
      rw [Finset.sum_apply, Fin.sum_univ_two, hz' 0, hz' 1] at this
      have hwl := hw l
      have hk : ex15D7k 0 l ^ 2 + ex15D7k 1 l ^ 2 = 5 := by
        fin_cases l <;> norm_num [ex15D7k]
      simp only at this
      rw [← add_div, hk] at this
      rw [eq_div_iff (hz l).ne', ← this]
      field_simp
    have hweq : w = ex15D7w zbar := by
      funext l
      have h1 := hclear l
      have h2 := hwsq l
      have hwl := hw l
      have hwl' := hwpos l
      nlinarith [sq_nonneg (w l - ex15D7w zbar l), sq_nonneg (w l + ex15D7w zbar l)]
    refine ⟨hweq, ?_⟩
    funext j l
    rw [hz' j, hweq]
    simp only
    rw [hwsq l]
    fin_cases j <;> fin_cases l <;> simp [ex15D7alloc, ex15D7k] <;> field_simp <;> ring
  · rintro ⟨rfl, rfl⟩
    refine ⟨hwpos, fun j => (ex15D7_optimal_iff hwpos j _).2 ?_, ?_⟩
    · funext l
      rw [hwsq l]
      fin_cases j <;> fin_cases l <;> simp [ex15D7alloc, ex15D7k] <;> field_simp <;> ring
    · funext l
      fin_cases l <;> simp [ex15D7alloc, Fin.sum_univ_two] <;> ring

/-- The Cauchy-Schwarz step of (15.D.5): `2√a + √b ≤ √5 √(a + b)`, with equality only if
`a = 4b`. -/
theorem two_sqrt_add_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a + Real.sqrt b ≤ Real.sqrt 5 * Real.sqrt (a + b) ∧
      (2 * Real.sqrt a + Real.sqrt b = Real.sqrt 5 * Real.sqrt (a + b) → a = 4 * b) := by
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsab := Real.sq_sqrt (add_nonneg ha hb)
  have n5 := Real.sqrt_nonneg 5
  have na := Real.sqrt_nonneg a
  have nb := Real.sqrt_nonneg b
  have nab := Real.sqrt_nonneg (a + b)
  have hsq : (Real.sqrt 5 * Real.sqrt (a + b)) ^ 2 - (2 * Real.sqrt a + Real.sqrt b) ^ 2 =
      (Real.sqrt a - 2 * Real.sqrt b) ^ 2 := by
    rw [mul_pow, h5, hsab]
    nlinarith [hsa, hsb]
  constructor
  · nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b), mul_nonneg n5 nab]
  · intro heq
    have h0 : (Real.sqrt a - 2 * Real.sqrt b) ^ 2 = 0 := by rw [← hsq, heq]; ring
    have h1 : Real.sqrt a = 2 * Real.sqrt b := by
      nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b)]
    rw [← hsa, ← hsb, h1]
    ring

/-- **Exercise 15.D.7** (MWG, p. 544), via (15.D.5): `z*` maximizes revenue `∑ⱼ fⱼ(zⱼ)` among
the allocations of `z̄`, and it is the only maximizer. -/
theorem exercise_15_D_7_revenue {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar)
    {z : Fin 2 → Fin 2 → ℝ} (hzm : ∀ j, z j ∈ nonnegOrthant 2) (hsum : ∑ j, z j = zbar) :
    ∑ j, (1 : ℝ) * ex15D7f j (z j) ≤ ∑ j, (1 : ℝ) * ex15D7f j (ex15D7alloc zbar j) ∧
      (∑ j, (1 : ℝ) * ex15D7f j (z j) = ∑ j, (1 : ℝ) * ex15D7f j (ex15D7alloc zbar j) →
        z = ex15D7alloc zbar) := by
  have heqm := (exercise_15_D_7 hz _ _).2 ⟨rfl, rfl⟩
  have hle := factorEqm_revenue_max (p := ![1, 1]) heqm hzm hsum
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hle ⊢
  refine ⟨hle, fun heq => ?_⟩
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Finset.sum_apply, Fin.sum_univ_two] at s0 s1
  obtain ⟨c0, e0⟩ := two_sqrt_add_sqrt_le (hzm 0 0) (hzm 1 0)
  obtain ⟨c1, e1⟩ := two_sqrt_add_sqrt_le (hzm 1 1) (hzm 0 1)
  -- the value at `z*` is `√5(√z̄₁ + √z̄₂)`
  have hval : (1 : ℝ) * ex15D7f 0 (ex15D7alloc zbar 0) + 1 * ex15D7f 1 (ex15D7alloc zbar 1) =
      Real.sqrt 5 * Real.sqrt (zbar 0) + Real.sqrt 5 * Real.sqrt (zbar 1) := by
    have k0 : Real.sqrt (4 * zbar 0 / 5) = 2 * Real.sqrt (zbar 0 / 5) := by
      rw [show 4 * zbar 0 / 5 = 2 ^ 2 * (zbar 0 / 5) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have k1 : Real.sqrt (4 * zbar 1 / 5) = 2 * Real.sqrt (zbar 1 / 5) := by
      rw [show 4 * zbar 1 / 5 = 2 ^ 2 * (zbar 1 / 5) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have m0 : Real.sqrt 5 * Real.sqrt (zbar 0) = 5 * Real.sqrt (zbar 0 / 5) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
      have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    have m1 : Real.sqrt 5 * Real.sqrt (zbar 1) = 5 * Real.sqrt (zbar 1 / 5) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
      have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    simp only [ex15D7f, ex15D7alloc, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    rw [k0, k1, m0, m1]
    ring
  rw [hval] at heq
  have hv : ex15D7f 0 (z 0) + ex15D7f 1 (z 1) = (2 * Real.sqrt (z 0 0) + Real.sqrt (z 1 0)) +
      (2 * Real.sqrt (z 1 1) + Real.sqrt (z 0 1)) := by
    simp only [ex15D7f, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [one_mul] at heq
  rw [hv] at heq
  rw [s0] at c0 e0
  rw [add_comm (z 1 1), s1] at c1 e1
  have q0 := e0 (by linarith)
  have q1 := e1 (by linarith)
  funext j l
  fin_cases j <;> fin_cases l <;> simp [ex15D7alloc] <;> linarith

/-- A function `k₁√z₁ + k₂√z₂` (`k ≥ 0`) is concave on `ℝ²₊`. -/
theorem concaveOn_sqrt_sum {k0 k1 : ℝ} (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) :
    ConcaveOn ℝ (nonnegOrthant 2) (fun z => k0 * Real.sqrt (z 0) + k1 * Real.sqrt (z 1)) := by
  refine ⟨convex_nonnegOrthant 2, fun x hx y hy a b ha hb hab => ?_⟩
  have h := Real.strictConcaveOn_sqrt.concaveOn.2
  have h0 := h (Set.mem_Ici.2 (hx 0)) (Set.mem_Ici.2 (hy 0)) ha hb hab
  have h1 := h (Set.mem_Ici.2 (hx 1)) (Set.mem_Ici.2 (hy 1)) ha hb hab
  simp only [smul_eq_mul] at h0 h1 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h0 hk0, mul_le_mul_of_nonneg_left h1 hk1]

/-- The derivative of `k₁√z₁ + k₂√z₂` at `(z₁, z₂)`. -/
noncomputable def sqrtSumDeriv (k0 k1 z0 z1 : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  k0 • ((1 / (2 * Real.sqrt z0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ)
    (0 : Fin 2)) + k1 • ((1 / (2 * Real.sqrt z1)) •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2))

/-- The derivative of `k₁√z₁ + k₂√z₂` at `z ≫ 0`. -/
theorem hasFDerivAt_sqrt_sum (k0 k1 : ℝ) {z : Fin 2 → ℝ} (h0 : 0 < z 0) (h1 : 0 < z 1) :
    HasFDerivAt (fun z : Fin 2 → ℝ => k0 * Real.sqrt (z 0) + k1 * Real.sqrt (z 1))
      (sqrtSumDeriv k0 k1 (z 0) (z 1)) z := by
  have d0 := (Real.hasDerivAt_sqrt h0.ne').comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z)
  have d1 := (Real.hasDerivAt_sqrt h1.ne').comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  exact (d0.const_mul k0).add (d1.const_mul k1)

/-- **Exercise 15.D.7** (MWG, p. 544), via (15.D.1)-(15.D.2): the production functions are concave
and differentiable at the interior allocation `z*`, where `pⱼ ∂fⱼ/∂z_{ℓj} = w*_ℓ`; by
`factorEqm_iff_foc` this recovers the equilibrium. -/
theorem exercise_15_D_7_foc {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) :
    (∀ j l, (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
      (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) = ex15D7w zbar l) ∧
      IsFactorEqm ex15D7f ![1, 1] zbar (ex15D7w zbar) (ex15D7alloc zbar) := by
  have hint : ∀ j l, 0 < ex15D7alloc zbar j l := fun j l => by
    fin_cases j <;> fin_cases l <;> simp [ex15D7alloc] <;> linarith [hz 0, hz 1]
  have hwpos : StrictlyPositive (ex15D7w zbar) := fun l => by
    have h5p : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    fin_cases l
    · exact div_pos h5p (mul_pos two_pos (Real.sqrt_pos.2 (hz 0)))
    · exact div_pos h5p (mul_pos two_pos (Real.sqrt_pos.2 (hz 1)))
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- the first-order conditions, checked by comparing squares of positive numbers
  have hfoc : ∀ j l, (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
      (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) = ex15D7w zbar l := by
    intro j l
    have hsj := Real.sq_sqrt (hint j l).le
    have hsjp := Real.sqrt_pos.2 (hint j l)
    have hsz := Real.sq_sqrt (hz l).le
    have hszp := Real.sqrt_pos.2 (hz l)
    have hlhs : (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
        (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) =
        ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) := by
      fin_cases j <;> fin_cases l <;> simp [ex15D7k, sqrtSumDeriv] <;> ring
    rw [hlhs]
    have hkpos := ex15D7k_pos j l
    have hpos1 : 0 < ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) := by positivity
    have hpos2 := hwpos l
    have hsq : (ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l))) ^ 2 =
        ex15D7w zbar l ^ 2 := by
      rw [div_pow, mul_pow, hsj]
      fin_cases j <;> fin_cases l <;>
        simp [ex15D7k, ex15D7alloc, ex15D7w, div_pow, mul_pow, h5,
          Real.sq_sqrt (hz 0).le, Real.sq_sqrt (hz 1).le] <;>
        field_simp <;> ring
    nlinarith [sq_nonneg (ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) - ex15D7w zbar l)]
  refine ⟨hfoc, (factorEqm_iff_foc (fun j => ?_) (fun j => by fin_cases j <;> norm_num) hwpos
    hint (fun j => ?_)).2 ⟨hfoc, ?_⟩⟩
  · exact concaveOn_sqrt_sum (ex15D7k_pos j 0).le (ex15D7k_pos j 1).le
  · exact hasFDerivAt_sqrt_sum _ _ (hint j 0) (hint j 1)
  · funext l
    fin_cases l <;> simp [ex15D7alloc, Fin.sum_univ_two] <;> ring

/-! ### Exercise 15.D.9: the Heckscher-Ohlin theorem -/

/-- With common unit input vectors `a`, endowment ratios and output ratios are ordered alike:
`z^A₁z^B₂ - z^B₁z^A₂ = |A|(q^A₁q^B₂ - q^A₂q^B₁)` for `z^k = ∑ⱼ q^k_j aⱼ`. -/
theorem endowment_output_identity (a : Fin 2 → Fin 2 → ℝ) (qA qB : Fin 2 → ℝ) :
    (qA 0 * a 0 0 + qA 1 * a 1 0) * (qB 0 * a 0 1 + qB 1 * a 1 1) -
      (qB 0 * a 0 0 + qB 1 * a 1 0) * (qA 0 * a 0 1 + qA 1 * a 1 1) =
    (a 0 0 * a 1 1 - a 1 0 * a 0 1) * (qA 0 * qB 1 - qA 1 * qB 0) := by
  ring

/-- **Exercise 15.D.9** (Heckscher-Ohlin; MWG, p. 544), corrected form. Two countries share the
2 × 2 technologies (with factor intensity), face output prices `p`, and are both diversified
(`qᵏ ≫ 0`, `c(wᵏ) = p`, `∑ⱼ qᵏⱼ aⱼ(wᵏ) = z̄ᵏ`); country A is relatively abundant in factor 1.
If the countries' consumption vectors are proportional (`xᵏ = λₖ d`; this is what identical
homothetic preferences give when demand is unique), each country's spending equals its income
`p·xᵏ = p·qᵏ`, and world markets clear, then country A exports good 1: `x^A₁ < q^A₁`. -/
theorem exercise_15_D_9 {M : TwoByTwo} (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p wA wB zA zB qA qB xA xB d : Fin 2 → ℝ} (hwA : StrictlyPositive wA)
    (hwB : StrictlyPositive wB) (hcA : ∀ j, M.c j wA = p j) (hcB : ∀ j, M.c j wB = p j)
    (hqA : ∀ j, 0 < qA j) (hqB : ∀ j, 0 < qB j) (hzA : ∑ j, qA j • M.a j wA = zA)
    (hzB : ∑ j, qB j • M.a j wB = zB) (habund : zB 0 / zB 1 < zA 0 / zA 1) {lA lB : ℝ}
    (hlA : 0 < lA) (hlB : 0 < lB) (hxA : xA = lA • d) (hxB : xB = lB • d)
    (hbud : p ⬝ᵥ xA = p ⬝ᵥ qA) (hclear : xA + xB = qA + qB) : xA 0 < qA 0 := by
  have hww : wA = wB := TwoByTwo.factor_price_equalization hM hFI hwA hwB hcA
    (fun j => (hcB j))
  subst hww
  have hdet := hFI.det_pos hM hwA
  have a00 := hM.a_pos 0 wA 0 hwA
  have a01 := hM.a_pos 0 wA 1 hwA
  have a10 := hM.a_pos 1 wA 0 hwA
  have a11 := hM.a_pos 1 wA 1 hwA
  have zA0 := congrFun hzA 0
  have zA1 := congrFun hzA 1
  have zB0 := congrFun hzB 0
  have zB1 := congrFun hzB 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at zA0 zA1 zB0 zB1
  have hzA1 : 0 < zA 1 := by rw [← zA1]; nlinarith [hqA 0, hqA 1]
  have hzB1 : 0 < zB 1 := by rw [← zB1]; nlinarith [hqB 0, hqB 1]
  rw [div_lt_div_iff₀ hzB1 hzA1] at habund
  -- output ratios inherit the ordering
  have hq : qA 1 * qB 0 < qA 0 * qB 1 := by
    have := endowment_output_identity (fun j => M.a j wA) qA qB
    rw [zA0, zA1, zB0, zB1] at this
    nlinarith
  -- consumption is the share `s = lA/(lA + lB)` of world output
  have hp0 : 0 < p 0 := by rw [← hcA 0]; exact TwoByTwo.c_pos hM 0 hwA
  have hp1 : 0 < p 1 := by rw [← hcA 1]; exact TwoByTwo.c_pos hM 1 hwA
  have hc0 := congrFun hclear 0
  have hc1 := congrFun hclear 1
  rw [hxA, hxB] at hc0 hc1
  rw [hxA] at hbud
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc0 hc1
  simp only [TwoByTwo.dot_two, Pi.smul_apply, smul_eq_mul] at hbud
  rw [hxA]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_contra hge
  rw [not_lt] at hge
  -- then good 2 is consumed at most as produced, and the output ratios would be reversed
  have h1 : lA * d 1 ≤ qA 1 := by nlinarith
  have hd0 : (lA + lB) * d 0 = qA 0 + qB 0 := by linarith
  have hd1 : (lA + lB) * d 1 = qA 1 + qB 1 := by linarith
  have e0 : lB * qA 0 ≤ lA * qB 0 := by nlinarith
  have e1 : lA * qB 1 ≤ lB * qA 1 := by nlinarith
  have f0 := mul_le_mul_of_nonneg_right e0 (hqB 1).le
  have f1 := mul_le_mul_of_nonneg_right e1 (hqB 0).le
  have f2 := mul_lt_mul_of_pos_left hq hlB
  nlinarith

/-- Demand of a utility homogeneous of degree `r > 0` scales with wealth: if `x` is demanded at
`(p, I)` then `t x` is demanded at `(p, t I)`, `t > 0`. -/
theorem homogeneous_demand_scale {L : ℕ} {u : (Fin L → ℝ) → ℝ} {r : ℝ}
    (hu : ∀ x ∈ nonnegOrthant L, ∀ t : ℝ, 0 < t → u (t • x) = t ^ r * u x) {p : Fin L → ℝ}
    {I t : ℝ} (ht : 0 < t) {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p I) :
    t • x ∈ walrasianDemand u p (t * I) := by
  have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  refine ⟨⟨fun l => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht.le (hx.1.1 l),
    ?_⟩, fun y hy => ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
  · have hy' : t⁻¹ • y ∈ budgetSet p I := by
      refine ⟨fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 ht.le) (hy.1 l), ?_⟩
      rw [dotProduct_smul, smul_eq_mul]
      have := hy.2
      rw [inv_mul_le_iff₀ ht]
      exact this
    have h1 := hx.2 _ hy'
    have h2 := hu _ hy'.1 t ht
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at h2
    rw [h2, hu x hx.1.1 t ht]
    exact mul_le_mul_of_nonneg_left h1 htr.le

/-- **Exercise 15.D.9** (MWG, p. 544), with identical preferences represented by a utility that is
homogeneous of degree `r > 0` and has a unique demand (e.g. strictly quasiconcave), the
Heckscher-Ohlin conclusion holds. -/
theorem exercise_15_D_9_unique_demand {M : TwoByTwo} (hM : M.IsModel)
    (hFI : M.FactorIntensity) {p wA wB zA zB qA qB xA xB : Fin 2 → ℝ}
    (hwA : StrictlyPositive wA) (hwB : StrictlyPositive wB) (hcA : ∀ j, M.c j wA = p j)
    (hcB : ∀ j, M.c j wB = p j) (hqA : ∀ j, 0 < qA j) (hqB : ∀ j, 0 < qB j)
    (hzA : ∑ j, qA j • M.a j wA = zA) (hzB : ∑ j, qB j • M.a j wB = zB)
    (habund : zB 0 / zB 1 < zA 0 / zA 1) {u : (Fin 2 → ℝ) → ℝ} {r : ℝ}
    (hu : ∀ x ∈ nonnegOrthant 2, ∀ t : ℝ, 0 < t → u (t • x) = t ^ r * u x)
    (huniq : ∀ I, (walrasianDemand u p I).Subsingleton)
    (hxA : xA ∈ walrasianDemand u p (p ⬝ᵥ qA)) (hxB : xB ∈ walrasianDemand u p (p ⬝ᵥ qB))
    (hclear : xA + xB = qA + qB) : xA 0 < qA 0 := by
  have hp : StrictlyPositive p := fun j => by rw [← hcA j]; exact TwoByTwo.c_pos hM j hwA
  have hIA : 0 < p ⬝ᵥ qA := dotProduct_pos_of_strictlyPositive hp (fun j => (hqA j).le)
    (fun h => by have := congrFun h 0; simp at this; linarith [hqA 0])
  have hIB : 0 < p ⬝ᵥ qB := dotProduct_pos_of_strictlyPositive hp (fun j => (hqB j).le)
    (fun h => by have := congrFun h 0; simp at this; linarith [hqB 0])
  set t := p ⬝ᵥ qB / p ⬝ᵥ qA with htd
  have ht : 0 < t := div_pos hIB hIA
  have hscale := homogeneous_demand_scale hu ht hxA
  rw [htd, div_mul_cancel₀ _ hIA.ne'] at hscale
  have hxB' : xB = t • xA := huniq _ hxB hscale
  have hbud : p ⬝ᵥ xA = p ⬝ᵥ qA := by
    -- the demand of a strictly increasing direction exhausts wealth
    have hle := hxA.1.2
    by_contra hne
    have hlt : p ⬝ᵥ xA < p ⬝ᵥ qA := lt_of_le_of_ne hle hne
    -- spending of B is then also below income, so world spending is below world income
    have hltB : p ⬝ᵥ xB < p ⬝ᵥ qB := by
      rw [hxB', dotProduct_smul, smul_eq_mul, htd, div_mul_eq_mul_div, div_lt_iff₀ hIA]
      nlinarith
    have : p ⬝ᵥ (xA + xB) = p ⬝ᵥ (qA + qB) := by rw [hclear]
    rw [dotProduct_add, dotProduct_add] at this
    linarith
  exact exercise_15_D_9 hM hFI hwA hwB hcA hcB hqA hqB hzA hzB habund one_pos ht
    (one_smul ℝ xA).symm hxB' hbud hclear

/-- **Exercise 15.D.9** (MWG, p. 544): the claim as printed is false. In the Leontief model
(factor intensity holds), at `p = (3, 3)`, `w = (1, 1)`, country A with endowment `(5, 4)`
(factor-1 abundant) produces `(2, 1)` and country B with `(4, 5)` produces `(1, 2)`; both are
diversified. Consumers have the linear utility `x₁ + x₂` (homogeneous, concave, increasing), so
any bundle on the budget line is demanded: A consumes `(3, 0)` and B `(0, 3)`, world markets
clear, and country A imports good 1. -/
theorem exercise_15_D_9_counterexample :
    let p : Fin 2 → ℝ := ![3, 3]
    let w : Fin 2 → ℝ := ![1, 1]
    let qA : Fin 2 → ℝ := ![2, 1]
    let qB : Fin 2 → ℝ := ![1, 2]
    let xA : Fin 2 → ℝ := ![3, 0]
    let xB : Fin 2 → ℝ := ![0, 3]
    IsFactorEqm leontiefModel.f p ![5, 4] w (fun j => qA j • leontiefModel.a j w) ∧
      IsFactorEqm leontiefModel.f p ![4, 5] w (fun j => qB j • leontiefModel.a j w) ∧
      (∀ j, 0 < qA j) ∧ (∀ j, 0 < qB j) ∧ (4 : ℝ) / 5 < 5 / 4 ∧
      (∀ x ∈ nonnegOrthant 2, ∀ t : ℝ, 0 < t → linearUtility (t • x) = t * linearUtility x) ∧
      ConcaveOn ℝ (nonnegOrthant 2) linearUtility ∧
      xA ∈ walrasianDemand linearUtility p (p ⬝ᵥ qA) ∧
      xB ∈ walrasianDemand linearUtility p (p ⬝ᵥ qB) ∧ xA + xB = qA + qB ∧ qA 0 < xA 0 := by
  intro p w qA qB xA xB
  have hw : StrictlyPositive w := fun l => by fin_cases l <;> norm_num [w]
  have hc : ∀ j, p j = leontiefModel.c j w := by
    intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two, p, w]
  have hdem : ∀ x : Fin 2 → ℝ, x ∈ nonnegOrthant 2 → x 0 + x 1 = 3 →
      x ∈ walrasianDemand linearUtility p 9 := by
    intro x hx hs
    refine ⟨⟨hx, by
      rw [TwoByTwo.dot_two]; simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one]; linarith⟩,
      fun y hy => ?_⟩
    have := hy.2
    simp only [p, TwoByTwo.dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [linearUtility]
    linarith
  refine ⟨?_, ?_, fun j => by fin_cases j <;> norm_num [qA],
    fun j => by fin_cases j <;> norm_num [qB], by norm_num, ?_, ?_, ?_, ?_, ?_,
    by norm_num [qA, xA]⟩
  · refine (TwoByTwo.interior_eqm_iff (q := qA) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num [qA])).2 ⟨hc, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two, qA]
  · refine (TwoByTwo.interior_eqm_iff (q := qB) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num [qB])).2 ⟨hc, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two, qB]
  · intro x _ t _
    simp [linearUtility]
    ring
  · refine ⟨convex_nonnegOrthant 2, fun x _ y _ a b _ _ _ => ?_⟩
    simp [linearUtility]
    ring_nf
    rfl
  · have : p ⬝ᵥ qA = 9 := by norm_num [p, qA, TwoByTwo.dot_two]
    rw [this]
    exact hdem _ (fun l => by fin_cases l <;> norm_num [xA]) (by norm_num [xA])
  · have : p ⬝ᵥ qB = 9 := by norm_num [p, qB, TwoByTwo.dot_two]
    rw [this]
    exact hdem _ (fun l => by fin_cases l <;> norm_num [xB]) (by norm_num [xB])
  · funext l
    fin_cases l <;> norm_num [xA, xB, qA, qB]

end MWG.GeneralEquilibriumExamples


/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 15.D.4: a closed 2 × 2 economy (MWG p. 543)

Two consumers, two constant-returns firms and two factors; consumer `i` owns `ownᵢ` of the factors
and consumes only the produced goods.

* **Exercise 15.D.4(a)** (`IsClosedEqm`): prices `p ≫ 0` and `w ≥ 0`, outputs `q ≥ 0` with
  `pⱼ ≤ cⱼ(w)` (equality if `qⱼ > 0`; constant-returns profit maximization, `crs_profitMax_iff`),
  factor demand `∑ⱼ qⱼ aⱼ(w)` at most the endowment with equality for factors with a positive
  price, consumers demanding with incomes `w·ownᵢ`, and goods markets clearing.
* For the Leontief technologies of `leontiefModel` (factor 1 intensive in good 1), consumer 1 owning
  one unit of factor 1 and consumer 2 one unit of factor 2:
  **Exercise 15.D.4(b)**: if consumer 1 only values good 2 and consumer 2 only good 1, there is a
  unique equilibrium (`exercise_15_D_4b`);
  **Exercise 15.D.4(c)**: if consumer 1 only values good 1 and consumer 2 only good 2, there are
  three equilibria with different allocations (`exercise_15_D_4c`).
  (The book's parts (b) and (c) are general graphical arguments; we prove them for this economy.)
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Exercise 15.D.4(a)** (MWG, p. 543). An equilibrium of the closed 2 × 2 economy. -/
def IsClosedEqm (M : TwoByTwo) (u : Fin 2 → (Fin 2 → ℝ) → ℝ) (own : Fin 2 → Fin 2 → ℝ)
    (p w q : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ j, 0 < p j) ∧ (∀ l, 0 ≤ w l) ∧ (∀ j, 0 ≤ q j) ∧ (∀ j, p j ≤ M.c j w) ∧
    (∀ j, 0 < q j → p j = M.c j w) ∧ (∀ l, ∑ j, q j * M.a j w l ≤ ∑ i, own i l) ∧
    (∀ l, 0 < w l → ∑ j, q j * M.a j w l = ∑ i, own i l) ∧
    (∀ i, x i ∈ walrasianDemand (u i) p (w ⬝ᵥ own i)) ∧ ∀ j, ∑ i, x i j = q j

/-- A consumer who values only good `k`: `u(x) = x_k`. -/
def onlyGood (k : Fin 2) (x : Fin 2 → ℝ) : ℝ := x k

/-- The demand of a consumer who values only good `k`, at `p ≫ 0` and wealth `m ≥ 0`: all wealth
is spent on good `k`. -/
theorem onlyGood_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {m : ℝ} (hm : 0 ≤ m)
    (k : Fin 2) : walrasianDemand (onlyGood k) p m = {Pi.single k (m / p k)} := by
  have hpk := hp k
  ext x
  simp only [Set.mem_singleton_iff]
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := TwoByTwo.dot_two p
  have hmem : Pi.single k (m / p k) ∈ budgetSet p m := by
    refine ⟨fun l => ?_, ?_⟩
    · simp only [Pi.single_apply]
      split_ifs
      · positivity
      · exact le_refl _
    · rw [dotProduct_single, mul_div_cancel₀ _ hpk.ne']
  have hval : onlyGood k (Pi.single k (m / p k)) = m / p k := by simp [onlyGood]
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    have h1 := hmax _ hmem
    rw [hval] at h1
    simp only [onlyGood] at h1
    rw [hdot] at hb
    have hp0 := hp 0
    have hp1 := hp 1
    have hx0 := hx 0
    have hx1 := hx 1
    rw [div_le_iff₀ hpk] at h1
    funext l
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue] at h1
      have e1 : x 1 = 0 := by nlinarith
      have e0 : x 0 = m / p 0 := by rw [eq_div_iff hp0.ne']; nlinarith
      fin_cases l
      · simpa using e0
      · simpa using e1
    · simp only [Fin.mk_one, Fin.isValue] at h1
      have e0 : x 0 = 0 := by nlinarith
      have e1 : x 1 = m / p 1 := by rw [eq_div_iff hp1.ne']; nlinarith
      fin_cases l
      · simpa using e0
      · simpa using e1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    rw [hval]
    simp only [onlyGood]
    have hb := hy.2
    rw [hdot] at hb
    rw [le_div_iff₀ hpk]
    have hp0 := hp 0
    have hp1 := hp 1
    have hy0 := hy.1 0
    have hy1 := hy.1 1
    fin_cases k <;> simp <;> nlinarith

/-- The ownership pattern of Exercise 15.D.4: consumer 1 owns one unit of factor 1, consumer 2 one
unit of factor 2. -/
def ex15D4own : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- **Exercise 15.D.4(c)** (MWG, p. 543). With consumer 1 caring only for good 1 and consumer 2 only
for good 2, the Leontief economy has (at least) three equilibria with different allocations:
`w = (1, 1)`, `q = (1/3, 1/3)`; `w = (1, 0)` (factor 2 free), `q = (1/2, 0)`; and `w = (0, 1)`,
`q = (0, 1/2)`. -/
theorem leontief_c0 (w : Fin 2 → ℝ) : leontiefModel.c 0 w = 2 * w 0 + w 1 := by
  simp [TwoByTwo.c, leontiefModel, Matrix.vecHead, Matrix.vecTail]; ring

theorem leontief_c1 (w : Fin 2 → ℝ) : leontiefModel.c 1 w = w 0 + 2 * w 1 := by
  simp [TwoByTwo.c, leontiefModel, Matrix.vecHead, Matrix.vecTail]; ring

/-- A sufficient set of numerical conditions for an equilibrium of the Leontief closed economy
in which consumer `i` values only good `kᵢ`. -/
theorem leontief_closedEqm_of {k : Fin 2 → Fin 2} {p w q : Fin 2 → ℝ}
    {x : Fin 2 → Fin 2 → ℝ} (hp : StrictlyPositive p) (hw : ∀ l, 0 ≤ w l) (hq : ∀ j, 0 ≤ q j)
    (hc0 : p 0 ≤ 2 * w 0 + w 1) (hc1 : p 1 ≤ w 0 + 2 * w 1)
    (hq0 : 0 < q 0 → p 0 = 2 * w 0 + w 1) (hq1 : 0 < q 1 → p 1 = w 0 + 2 * w 1)
    (hf0 : 2 * q 0 + q 1 ≤ 1) (hf1 : q 0 + 2 * q 1 ≤ 1)
    (hb0 : 0 < w 0 → 2 * q 0 + q 1 = 1) (hb1 : 0 < w 1 → q 0 + 2 * q 1 = 1)
    (hx0 : x 0 = Pi.single (k 0) (w 0 / p (k 0))) (hx1 : x 1 = Pi.single (k 1) (w 1 / p (k 1)))
    (hg : ∀ j, x 0 j + x 1 j = q j) :
    IsClosedEqm leontiefModel (fun i => onlyGood (k i)) ex15D4own p w q x := by
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hsum : ∀ l, ∑ j, q j * leontiefModel.a j w l = ![2 * q 0 + q 1, q 0 + 2 * q 1] l := by
    intro l
    fin_cases l <;> simp [leontiefModel, Fin.sum_univ_two] <;> ring
  have hownsum : ∀ l, ∑ i, ex15D4own i l = 1 := fun l => by
    fin_cases l <;> simp [ex15D4own, Fin.sum_univ_two]
  refine ⟨hp, hw, hq, fun j => ?_, fun j hj => ?_, fun l => ?_, fun l hl => ?_, fun i => ?_,
    fun j => ?_⟩
  · fin_cases j
    · exact hc0.trans (leontief_c0 w).ge
    · exact hc1.trans (leontief_c1 w).ge
  · fin_cases j
    · exact (hq0 hj).trans (leontief_c0 w).symm
    · exact (hq1 hj).trans (leontief_c1 w).symm
  · rw [hsum, hownsum]
    fin_cases l
    · exact hf0
    · exact hf1
  · rw [hsum, hownsum]
    fin_cases l
    · exact hb0 hl
    · exact hb1 hl
  · rw [hown, onlyGood_demand hp (hw i)]
    fin_cases i
    · exact hx0
    · exact hx1
  · rw [Fin.sum_univ_two]
    exact hg j

/-- **Exercise 15.D.4(c)** (MWG, p. 543). With consumer 1 caring only for good 1 and consumer 2 only
for good 2, the Leontief economy has (at least) three equilibria with different allocations:
`w = (1, 1)`, `q = (1/3, 1/3)`; `w = (1, 0)` (factor 2 free), `q = (1/2, 0)`; and `w = (0, 1)`,
`q = (0, 1/2)`. -/
theorem exercise_15_D_4c :
    IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![3, 3] ![1, 1]
        ![1 / 3, 1 / 3] ![![1 / 3, 0], ![0, 1 / 3]] ∧
      IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![2, 1] ![1, 0]
        ![1 / 2, 0] ![![1 / 2, 0], ![0, 0]] ∧
      IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![1, 2] ![0, 1]
        ![0, 1 / 2] ![![0, 0], ![0, 1 / 2]] := by
  refine ⟨leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)
      (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) ?_ ?_
      (fun j => by fin_cases j <;> norm_num),
    leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun h => by norm_num at h)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun h => by norm_num at h) ?_ ?_
      (fun j => by fin_cases j <;> norm_num),
    leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun h => by norm_num at h) (fun _ => by norm_num)
      (by norm_num) (by norm_num) (fun h => by norm_num at h) (fun _ => by norm_num) ?_ ?_
      (fun j => by fin_cases j <;> norm_num)⟩ <;>
    (funext l; fin_cases l <;> simp)

/-- **Exercise 15.D.4(b)** (MWG, p. 543). With consumer 1 (owner of factor 1) caring only for
good 2 and consumer 2 only for good 1, every equilibrium of the Leontief economy has equal factor
prices, outputs `q = (1/3, 1/3)` and allocation `x₁ = (0, 1/3)`, `x₂ = (1/3, 0)`: the equilibrium
is unique (up to the scale of prices). -/
theorem exercise_15_D_4b {p w q : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm leontiefModel (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x) :
    w 0 = w 1 ∧ q = ![1 / 3, 1 / 3] ∧ x = ![![0, 1 / 3], ![1 / 3, 0]] := by
  obtain ⟨hp, hw, hq, hpc, hqp, hf, hb, hx, hg⟩ := h
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hsum0 : ∑ j, q j * leontiefModel.a j w 0 = 2 * q 0 + q 1 := by
    simp [leontiefModel, Fin.sum_univ_two]; ring
  have hsum1 : ∑ j, q j * leontiefModel.a j w 1 = q 0 + 2 * q 1 := by
    simp [leontiefModel, Fin.sum_univ_two]; ring
  have hown0 : ∑ i, ex15D4own i 0 = 1 := by simp [ex15D4own, Fin.sum_univ_two]
  have hown1 : ∑ i, ex15D4own i 1 = 1 := by simp [ex15D4own, Fin.sum_univ_two]
  -- consumer 1 spends `w₁` on good 2, consumer 2 spends `w₂` on good 1
  have hx0 := hx 0
  have hx1 := hx 1
  simp only [hown] at hx0 hx1
  rw [onlyGood_demand hp (hw 0)] at hx0
  rw [onlyGood_demand hp (hw 1)] at hx1
  have hx0' : x 0 = Pi.single 1 (w 0 / p 1) := hx0
  have hx1' : x 1 = Pi.single 0 (w 1 / p 0) := hx1
  have hq0 : q 0 = w 1 / p 0 := by
    have := hg 0; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hq1 : q 1 = w 0 / p 1 := by
    have := hg 1; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hp0 := hp 0
  have hp1 := hp 1
  have hf0 := hf 0
  have hf1 := hf 1
  rw [hsum0, hown0] at hf0
  rw [hsum1, hown1] at hf1
  have hc0 := hpc 0
  have hc1 := hpc 1
  rw [leontief_c0] at hc0
  rw [leontief_c1] at hc1
  -- both factor prices are positive
  have hw0 : 0 < w 0 := by
    rcases eq_or_lt_of_le (hw 0) with h0 | h0
    · exfalso
      -- then good 1 is bought by consumer 2 with income `w₂` and costs `w₂`
      have hw1 : 0 < w 1 := by
        rcases eq_or_lt_of_le (hw 1) with h1 | h1
        · rw [← h0, ← h1] at hc0; linarith
        · exact h1
      have hq0pos : 0 < q 0 := by rw [hq0]; positivity
      have := hqp 0 hq0pos
      rw [leontief_c0, ← h0] at this
      have hq0one : q 0 = 1 := by rw [hq0, this]; field_simp; ring
      nlinarith [hq 1]
    · exact h0
  have hw1 : 0 < w 1 := by
    rcases eq_or_lt_of_le (hw 1) with h1 | h1
    · exfalso
      have hq1pos : 0 < q 1 := by rw [hq1]; positivity
      have := hqp 1 hq1pos
      rw [leontief_c1, ← h1] at this
      have hq1one : q 1 = 1 := by rw [hq1, this]; field_simp; ring
      nlinarith [hq 0]
    · exact h1
  have hb0 := hb 0 hw0
  have hb1 := hb 1 hw1
  rw [hsum0, hown0] at hb0
  rw [hsum1, hown1] at hb1
  have e0 : q 0 = 1 / 3 := by linarith
  have e1 : q 1 = 1 / 3 := by linarith
  have hpc1 : p 1 = w 0 + 2 * w 1 := by
    have := hqp 1 (by rw [e1]; norm_num); rwa [leontief_c1] at this
  have hww : w 0 = w 1 := by
    rw [hq1, hpc1, div_eq_iff (by positivity)] at e1
    linarith
  refine ⟨hww, ?_, ?_⟩
  · funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · have g00 : x 0 0 = 0 := by rw [hx0']; simp
    have g01 : x 0 1 = 1 / 3 := by rw [hx0']; simp; linarith
    have g10 : x 1 0 = 1 / 3 := by rw [hx1']; simp; linarith
    have g11 : x 1 1 = 0 := by rw [hx1']; simp
    funext i l
    fin_cases i <;> fin_cases l <;> simp [g00, g01, g10, g11]

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# General versus partial equilibrium: a tax incidence example (MWG Section 15.E, pp. 538-540)

`N` towns, each with one price-taking firm with production function `f`; `M` units of labor move
freely between towns; the consumption good is the numeraire. Town 1 taxes labor at rate `t`.

* p. 539: without the tax the equilibrium has `z = M/N` in every town and `w̄ = f'(M/N)`
  (`no_tax_eqm`, unique when `f'` is strictly decreasing).
* The partial equilibrium view: with the wage fixed at `w̄`, town 1's employment falls
  (`partial_eqm_employment_falls`).
* (15.E.1)-(15.E.5): along any differentiable path of general equilibria `w'(0) = -1/N` and
  `z'(0) = -1/(N f''(M/N))` (`general_eqm_wage_derivative`); the wage effect vanishes as `N → ∞`
  (`wage_effect_vanishes`).
* p. 540, footnote 17: aggregate profits `(N - 1)π(w(t)) + π(w(t) + t)` have zero derivative at
  `t = 0` (`aggregate_profit_derivative`): the burden of a small tax falls on labor, whose income
  falls at the rate at which tax revenue rises (`labor_bears_burden`).
* An instance: the quadratic technology `f(z) = a z - b z²/2` has explicit equilibrium paths
  (`quadratic_eqm_path`).
-/

namespace MWG.GeneralEquilibriumExamples

open Filter Topology

/-- **Section 15.E** (MWG, p. 539). The general equilibrium conditions (15.E.1)-(15.E.3) at tax
rate `t` in town 1, for the common wage `w`, the employment `z` of each untaxed firm and the
employment `z₁` of the taxed firm (with marginal product `f'`). -/
def IsTaxEqm (f' : ℝ → ℝ) (N M t w z z₁ : ℝ) : Prop :=
  (N - 1) * z + z₁ = M ∧ f' z = w ∧ f' z₁ = w + t

/-- **Section 15.E** (MWG, p. 539). Without the tax, `z = z₁ = M/N` and `w̄ = f'(M/N)` is an
equilibrium; if `f'` is strictly decreasing (strictly concave `f`) it is the only one. -/
theorem no_tax_eqm {f' : ℝ → ℝ} {N M : ℝ} (hN : 0 < N) :
    IsTaxEqm f' N M 0 (f' (M / N)) (M / N) (M / N) ∧
      (StrictAnti f' → ∀ w z z₁, IsTaxEqm f' N M 0 w z z₁ →
        z = M / N ∧ z₁ = M / N ∧ w = f' (M / N)) := by
  refine ⟨⟨by field_simp; ring, rfl, by ring⟩, fun hf w z z₁ ⟨h1, h2, h3⟩ => ?_⟩
  have hzz : z = z₁ := hf.injective (by rw [h2, h3, add_zero])
  have hz : z = M / N := by
    rw [eq_div_iff hN.ne']
    rw [← hzz] at h1
    linarith
  exact ⟨hz, hzz ▸ hz, by rw [← h2, hz]⟩

/-- **Section 15.E** (MWG, p. 539). The partial equilibrium view: with the wage in town 1 held at
`w̄`, the taxed firm's labor demand `z₁` solves `f'(z₁) = t + w̄`; for `t > 0` and `f'` strictly
decreasing, it falls below `M/N`. -/
theorem partial_eqm_employment_falls {f' : ℝ → ℝ} (hf : StrictAnti f') {N M t z₁ : ℝ}
    (ht : 0 < t) (h : f' z₁ = t + f' (M / N)) : z₁ < M / N := by
  by_contra hle
  rw [not_lt] at hle
  have := hf.antitone hle
  linarith

/-- **(15.E.4)-(15.E.5)** (MWG, p. 539). Let `w, z, z₁` be paths of general equilibria (15.E.1)-
(15.E.3) for small taxes `t`, differentiable at `t = 0` with `z(0) = z₁(0) = M/N`, and let `f'` be
differentiable at `M/N` with `f''(M/N) ≠ 0`. Then `w'(0) = -1/N` and `z'(0) = -1/(N f''(M/N))`. -/
theorem general_eqm_wage_derivative {f' : ℝ → ℝ} {f'' N M : ℝ} (hN : 0 < N)
    (hf' : HasDerivAt f' f'' (M / N)) (hf'' : f'' ≠ 0) {w z z₁ : ℝ → ℝ} {w' z' z₁' : ℝ}
    (hw : HasDerivAt w w' 0) (hz : HasDerivAt z z' 0) (hz₁ : HasDerivAt z₁ z₁' 0)
    (hz0 : z 0 = M / N) (hz₁0 : z₁ 0 = M / N)
    (heq : ∀ᶠ t in 𝓝 (0 : ℝ), IsTaxEqm f' N M t (w t) (z t) (z₁ t)) :
    w' = -1 / N ∧ z' = -1 / (N * f'') := by
  -- differentiate (15.E.1)
  have h1 : (N - 1) * z' + z₁' = 0 := by
    have hd := (hz.const_mul (N - 1)).add hz₁
    have hc : HasDerivAt (fun t => (N - 1) * z t + z₁ t) 0 0 :=
      (hasDerivAt_const (0 : ℝ) M).congr_of_eventuallyEq
        (heq.mono fun t ht => ht.1)
    exact hd.unique hc
  -- differentiate (15.E.2)
  have h2 : f'' * z' = w' := by
    have hd := HasDerivAt.comp (0 : ℝ) (by rwa [hz0]) hz
    have hc : HasDerivAt (f' ∘ z) w' 0 := hw.congr_of_eventuallyEq (heq.mono fun t ht => ht.2.1)
    exact hd.unique hc
  -- differentiate (15.E.3)
  have h3 : f'' * z₁' = w' + 1 := by
    have hd := HasDerivAt.comp (0 : ℝ) (by rwa [hz₁0]) hz₁
    have hc : HasDerivAt (f' ∘ z₁) (w' + 1) 0 :=
      (hw.add (hasDerivAt_id (0 : ℝ))).congr_of_eventuallyEq
        (heq.mono fun t ht => by simp [ht.2.2])
    exact hd.unique hc
  -- (15.E.4): `-f''(N - 1) z' = w' + 1`, and (15.E.5)
  have hw' : w' = -1 / N := by
    rw [eq_div_iff hN.ne']
    have : z₁' = -((N - 1) * z') := by linarith
    rw [this] at h3
    nlinarith
  refine ⟨hw', ?_⟩
  have h4 : f'' * z' * N = -1 := by rw [h2, hw']; field_simp
  rw [eq_div_iff (mul_ne_zero hN.ne' hf'')]
  linear_combination h4

/-- **Section 15.E** (MWG, p. 540). The general equilibrium fall in the wage, `-1/N`, vanishes as
the number of towns grows. -/
theorem wage_effect_vanishes : Tendsto (fun N : ℕ => -1 / (N : ℝ)) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop
    (𝓝 0)).neg
  rw [neg_zero] at this
  convert this using 2 with n
  ring

/-- **Section 15.E** (MWG, p. 540, footnote 17). Let `π` be the profit function of a firm,
differentiable at `w̄ = w(0)`, and let `w'(0) = -1/N`. Aggregate profits
`(N - 1)π(w(t)) + π(w(t) + t)` (the taxed firm's profit is `π(w(t) + t)`) have derivative
`(N - 1)π'(w̄)w'(0) + π'(w̄)(w'(0) + 1) = π'(w̄)(-(N-1)/N + (N-1)/N) = 0` at `t = 0`. -/
theorem aggregate_profit_derivative {π₀ w : ℝ → ℝ} {π' N : ℝ} (hN : 0 < N)
    (hπ : HasDerivAt π₀ π' (w 0)) (hw : HasDerivAt w (-1 / N) 0) :
    HasDerivAt (fun t => (N - 1) * π₀ (w t) + π₀ (w t + t)) 0 0 ∧
      (N - 1) * π' * (-1 / N) + π' * (-1 / N + 1) = π' * (-(N - 1) / N + (N - 1) / N) := by
  have h1 := (HasDerivAt.comp (0 : ℝ) hπ hw).const_mul (N - 1)
  have h2 := HasDerivAt.comp (0 : ℝ) (by simpa using hπ) (hw.add (hasDerivAt_id (0 : ℝ)))
  have hsum := h1.add h2
  refine ⟨?_, by field_simp; ring⟩
  convert hsum using 1
  · funext t
    simp
  · field_simp
    ring

/-- **Section 15.E** (MWG, p. 540). At the margin labor bears the whole tax: labor income `M w(t)`
falls at the rate `M/N` at which tax revenue `t z₁(t)` rises (`z₁(0) = M/N`). -/
theorem labor_bears_burden {w z₁ : ℝ → ℝ} {z₁' N M : ℝ} (hN : 0 < N)
    (hw : HasDerivAt w (-1 / N) 0) (hz₁ : HasDerivAt z₁ z₁' 0) (hz₁0 : z₁ 0 = M / N) :
    HasDerivAt (fun t => M * w t) (-(M / N)) 0 ∧ HasDerivAt (fun t => t * z₁ t) (M / N) 0 := by
  constructor
  · convert hw.const_mul M using 1
    field_simp
  · convert (hasDerivAt_id (0 : ℝ)).mul hz₁ using 1
    · rfl
    · rw [hz₁0]
      simp

/-- **Section 15.E** (MWG, pp. 539-540), an instance. With the quadratic technology
`f(z) = a z - b z²/2` (`b > 0`, marginal product `f'(z) = a - b z`), the paths
`z(t) = (M + t/b)/N`, `z₁(t) = z(t) - t/b`, `w(t) = a - b z(t)` are general equilibria for every
`t`, with `w'(0) = -1/N`, and `z(0) = z₁(0) = M/N`. -/
theorem quadratic_eqm_path {a b N M : ℝ} (hb : 0 < b) (hN : 0 < N) :
    (∀ t, IsTaxEqm (fun z => a - b * z) N M t (a - b * ((M + t / b) / N)) ((M + t / b) / N)
      ((M + t / b) / N - t / b)) ∧
    HasDerivAt (fun t => a - b * ((M + t / b) / N)) (-1 / N) 0 ∧
    (M + 0 / b) / N = M / N ∧ (M + 0 / b) / N - 0 / b = M / N := by
  refine ⟨fun t => ⟨?_, rfl, ?_⟩, ?_, by simp, by simp⟩
  · field_simp; ring
  · field_simp; ring
  · have h := ((((hasDerivAt_id (0 : ℝ)).div_const b).const_add M).div_const N).const_mul b
    have h2 := h.const_sub a
    convert h2 using 1
    · funext t
      simp
    · field_simp

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One firm, two consumers: multiple equilibria (MWG Exercise 15.C.1(c), p. 542)

Exercise 15.C.1(c) asks for an example of multiple equilibria in a strictly convex economy with
one firm and two consumers, each endowed with labor alone, who split the profits equally, and
whether this can happen under constant returns to scale.

* The economy (`TCEconomy`): utilities over (leisure, consumption good), labor endowments `L̄ᵢ`,
  a production function `f`; profit maximization, the consumers' budgets with half the profit
  each, and Walrasian equilibrium (`TCEconomy.IsWalrasEqm`), mirroring Section 15.C.
* Tools: the utility index `v(s) = -(a/5)(a/(s + e))⁵` (`tcpPowFive`) is strictly concave and
  strictly increasing on `s ≥ 0`, with the tangent inequality `tcpPowFive_tangent` (from
  `x⁶ - 6xy⁵ + 5y⁶ ≥ 0`); utilities `c·x + φ(d·x)` (`tcpAffineUtility`) are continuous, strongly
  monotone and strictly convex under simple conditions; strictly convex preferences have at most
  one maximizer on a convex set (`tcp_eq_of_strictlyConvex`).
* **The example** (`ex15C1cEconomy`): `f(z) = 7 z^{1/7}` (strictly concave), consumer 1
  quasilinear in leisure, consumer 2 quasilinear in consumption. At `p = 1` both `w = 1` and
  `w = (8/9)⁶ = 262144/531441` are equilibrium wages, with different allocations
  (`exercise_15_C_1c`); the economy is strictly convex (`ex15C1c_strictlyConvex`).
* **Constant returns** `f(z) = αz`: with strongly monotone, strictly convex preferences, all
  equilibria have the same allocation (`exercise_15_C_1c_crs`), the real wage is `w/p = α`
  whenever production is positive (`exercise_15_C_1c_crs_wage`), and there is no equilibrium with
  `w < αp` (`exercise_15_C_1c_crs_no_low_wage`). (Equilibrium price ratios can differ only when
  nothing is produced.)
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-! ### Tools -/

/-- `x⁶ - 6xy⁵ + 5y⁶ = (x - y)²(x⁴ + 2x³y + 3x²y² + 4xy³ + 5y⁴) ≥ 0` for `x, y ≥ 0`. -/
theorem tcp_six_poly_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 := by
  have e : x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 =
      (x - y) ^ 2 * (x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4) := by
    ring
  rw [e]
  positivity

/-- `x⁶ - 6xy⁵ + 5y⁶ > 0` for `x, y > 0`, `x ≠ y`. -/
theorem tcp_six_poly_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    0 < x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 := by
  have e : x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 =
      (x - y) ^ 2 * (x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4) := by
    ring
  rw [e]
  have h1 : 0 < (x - y) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have h2 : 0 < x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4 := by
    positivity
  exact mul_pos h1 h2

/-- The utility index `v(s) = -(a/5)(a/(s + e))⁵`, with `v'(s) = (a/(s + e))⁶`. -/
noncomputable def tcpPowFive (a e s : ℝ) : ℝ := -(a / 5) * (a / (s + e)) ^ 5

/-- The difference between the tangent line of `tcpPowFive` at `s` and its value at `t`. -/
theorem tcpPowFive_gap {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e) :
    tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) - tcpPowFive a e t =
      a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 - 6 * (a / (t + e)) * (a / (s + e)) ^ 5 +
        5 * (a / (s + e)) ^ 6) := by
  unfold tcpPowFive
  field_simp
  ring

/-- The tangent inequality for `v = tcpPowFive a e` (concavity): for `s, t > -e`,
`v(t) ≤ v(s) + v'(s)(t - s)`. -/
theorem tcpPowFive_tangent {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e) :
    tcpPowFive a e t ≤ tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) := by
  have hg := tcpPowFive_gap ha hs ht
  have hr : 0 < a / (t + e) := div_pos ha ht
  have hm : 0 < a / (s + e) := div_pos ha hs
  have key := tcp_six_poly_nonneg hr.le hm.le
  have : 0 ≤ a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 -
      6 * (a / (t + e)) * (a / (s + e)) ^ 5 + 5 * (a / (s + e)) ^ 6) :=
    mul_nonneg (by positivity) key
  linarith

/-- The strict tangent inequality for `v = tcpPowFive a e`: for `s, t > -e`, `t ≠ s`,
`v(t) < v(s) + v'(s)(t - s)`. -/
theorem tcpPowFive_tangent_strict {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e)
    (hne : t ≠ s) : tcpPowFive a e t < tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) := by
  have hg := tcpPowFive_gap ha hs ht
  have hr : 0 < a / (t + e) := div_pos ha ht
  have hm : 0 < a / (s + e) := div_pos ha hs
  have hrm : a / (t + e) ≠ a / (s + e) := by
    intro h
    rw [div_eq_div_iff ht.ne' hs.ne'] at h
    apply hne
    have := mul_left_cancel₀ ha.ne' h
    linarith
  have key := tcp_six_poly_pos hr hm hrm
  have : 0 < a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 -
      6 * (a / (t + e)) * (a / (s + e)) ^ 5 + 5 * (a / (s + e)) ^ 6) :=
    mul_pos (by positivity) key
  linarith

/-- `v = tcpPowFive a e` (`a, e > 0`) is strictly concave on `[0, ∞)`. -/
theorem tcpPowFive_strictConcaveOn {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    StrictConcaveOn ℝ (Set.Ici 0) (tcpPowFive a e) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy α β hα hβ hαβ => ?_⟩
  have hx' : (0 : ℝ) ≤ x := hx
  have hy' : (0 : ℝ) ≤ y := hy
  simp only [smul_eq_mul]
  have hb : β = 1 - α := by linarith
  subst hb
  have hm0 : 0 < α * x + (1 - α) * y + e := by
    have : 0 ≤ α * x := mul_nonneg hα.le hx'
    have : 0 ≤ (1 - α) * y := mul_nonneg hβ.le hy'
    linarith
  have hxm : x ≠ α * x + (1 - α) * y := by
    intro h
    apply hxy
    have : (1 - α) * (x - y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  have hym : y ≠ α * x + (1 - α) * y := by
    intro h
    apply hxy
    have : α * (x - y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  have h1 := tcpPowFive_tangent_strict ha hm0 (by linarith) hxm
  have h2 := tcpPowFive_tangent_strict ha hm0 (by linarith) hym
  set D := (a / (α * x + (1 - α) * y + e)) ^ 6
  set m := α * x + (1 - α) * y
  have hz : α * (D * (x - m)) + (1 - α) * (D * (y - m)) = 0 := by
    simp only [m]
    ring
  nlinarith [mul_lt_mul_of_pos_left h1 hα, mul_lt_mul_of_pos_left h2 hβ]

/-- `v = tcpPowFive a e` (`a, e > 0`) is strictly increasing on `[0, ∞)`. -/
theorem tcpPowFive_strictMonoOn {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    StrictMonoOn (tcpPowFive a e) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) ≤ s := hs
  have ht' : (0 : ℝ) ≤ t := ht
  have h := tcpPowFive_tangent_strict ha (s := t) (t := s) (e := e) (by linarith)
    (by linarith) hst.ne
  have hD : 0 < (a / (t + e)) ^ 6 := by
    have : 0 < t + e := by linarith
    positivity
  have : (a / (t + e)) ^ 6 * (s - t) < 0 := mul_neg_of_pos_of_neg hD (by linarith)
  linarith

/-- `v = tcpPowFive a e` (`e > 0`) is continuous on `[0, ∞)`. -/
theorem tcpPowFive_continuousOn {a e : ℝ} (he : 0 < e) :
    ContinuousOn (tcpPowFive a e) (Set.Ici 0) := by
  intro s hs
  have hs' : (0 : ℝ) ≤ s := hs
  have hne : s + e ≠ 0 := by linarith
  have : ContinuousAt (fun s : ℝ => -(a / 5) * (a / (s + e)) ^ 5) s := by
    fun_prop (disch := exact hne)
  exact this.continuousWithinAt

/-- A utility `u(x) = c₀x₁ + c₁x₂ + φ(d₀x₁ + d₁x₂)`: a linear part plus an index of a linear
form (quasilinear utilities are the cases `c = e₁, d = e₂` and `c = e₂, d = e₁`). -/
def tcpAffineUtility (c₀ c₁ d₀ d₁ : ℝ) (φ : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  c₀ * x 0 + c₁ * x 1 + φ (d₀ * x 0 + d₁ * x 1)

/-- `c·x + φ(d·x)` is continuous on `ℝ²₊` when `d ≥ 0` and `φ` is continuous on `[0, ∞)`. -/
theorem tcpAffineUtility_continuousOn {c₀ c₁ d₀ d₁ : ℝ} (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0)) :
    ContinuousOn (tcpAffineUtility c₀ c₁ d₀ d₁ φ) (nonnegOrthant 2) := by
  have hlin : Continuous fun x : Fin 2 → ℝ => d₀ * x 0 + d₁ * x 1 := by fun_prop
  have hmaps : Set.MapsTo (fun x : Fin 2 → ℝ => d₀ * x 0 + d₁ * x 1) (nonnegOrthant 2)
      (Set.Ici 0) :=
    fun x hx => Set.mem_Ici.2 (add_nonneg (mul_nonneg hd₀ (hx 0)) (mul_nonneg hd₁ (hx 1)))
  have h2 := hφ.comp hlin.continuousOn hmaps
  have h1 : Continuous fun x : Fin 2 → ℝ => c₀ * x 0 + c₁ * x 1 := by fun_prop
  exact h1.continuousOn.add h2

/-- `c·x + φ(d·x)` is strongly monotone on `ℝ²₊` when `c, d ≥ 0`, every good enters `c` or `d`
with a positive weight, and `φ` is strictly increasing on `[0, ∞)`. -/
theorem tcpAffineUtility_stronglyMonotone {c₀ c₁ d₀ d₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (h₀ : 0 < c₀ ∨ 0 < d₀) (h₁ : 0 < c₁ ∨ 0 < d₁) {φ : ℝ → ℝ}
    (hφ : StrictMonoOn φ (Set.Ici 0)) :
    UtilityStronglyMonotone (tcpAffineUtility c₀ c₁ d₀ d₁ φ) := by
  intro x hx y _ hxy hne
  have hx0 := hx 0
  have hx1 := hx 1
  have hle0 := hxy 0
  have hle1 := hxy 1
  have hsx : (0 : ℝ) ≤ d₀ * x 0 + d₁ * x 1 :=
    add_nonneg (mul_nonneg hd₀ hx0) (mul_nonneg hd₁ hx1)
  have hsy : (0 : ℝ) ≤ d₀ * y 0 + d₁ * y 1 :=
    add_nonneg (mul_nonneg hd₀ (hx0.trans hle0)) (mul_nonneg hd₁ (hx1.trans hle1))
  have m0 := mul_le_mul_of_nonneg_left hle0 hd₀
  have m1 := mul_le_mul_of_nonneg_left hle1 hd₁
  have n0 := mul_le_mul_of_nonneg_left hle0 hc₀
  have n1 := mul_le_mul_of_nonneg_left hle1 hc₁
  have hsle : d₀ * x 0 + d₁ * x 1 ≤ d₀ * y 0 + d₁ * y 1 := by linarith
  have hφle : φ (d₀ * x 0 + d₁ * x 1) ≤ φ (d₀ * y 0 + d₁ * y 1) :=
    (hφ.le_iff_le (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy)).2 hsle
  have hl : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra hall
    simp only [not_or, not_lt] at hall
    exact hne (funext fun l => by
      fin_cases l
      · exact le_antisymm hall.1 (hxy 0)
      · exact le_antisymm hall.2 (hxy 1))
  have hlt : tcpAffineUtility c₀ c₁ d₀ d₁ φ x < tcpAffineUtility c₀ c₁ d₀ d₁ φ y := by
    simp only [tcpAffineUtility]
    rcases hl with hl | hl
    · rcases h₀ with hc | hd
      · have := mul_lt_mul_of_pos_left hl hc
        linarith
      · have hs : d₀ * x 0 + d₁ * x 1 < d₀ * y 0 + d₁ * y 1 := by
          have := mul_lt_mul_of_pos_left hl hd
          linarith
        have := hφ (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy) hs
        linarith
    · rcases h₁ with hc | hd
      · have := mul_lt_mul_of_pos_left hl hc
        linarith
      · have hs : d₀ * x 0 + d₁ * x 1 < d₀ * y 0 + d₁ * y 1 := by
          have := mul_lt_mul_of_pos_left hl hd
          linarith
        have := hφ (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy) hs
        linarith
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- `c·x + φ(d·x)` represents strictly convex preferences on `ℝ²₊` when `d ≥ 0`, `c` and `d` are
linearly independent, and `φ` is strictly concave on `[0, ∞)`: bundles with different `d·x` gain
from the strict concavity of `φ`; bundles with the same `d·x` differ in `c·x`, hence in utility. -/
theorem tcpAffineUtility_strictlyConvex {c₀ c₁ d₀ d₁ : ℝ} (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hdet : c₀ * d₁ - c₁ * d₀ ≠ 0) {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) :
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (tcpAffineUtility c₀ c₁ d₀ d₁ φ)) := by
  intro x _ y hy z hz hyx hzx hne α hα0 hα1
  change tcpAffineUtility c₀ c₁ d₀ d₁ φ x ≤ tcpAffineUtility c₀ c₁ d₀ d₁ φ y at hyx
  change tcpAffineUtility c₀ c₁ d₀ d₁ φ x ≤ tcpAffineUtility c₀ c₁ d₀ d₁ φ z at hzx
  suffices h : tcpAffineUtility c₀ c₁ d₀ d₁ φ x <
      tcpAffineUtility c₀ c₁ d₀ d₁ φ (α • y + (1 - α) • z) from ⟨h.le, not_le.2 h⟩
  have hm : tcpAffineUtility c₀ c₁ d₀ d₁ φ (α • y + (1 - α) • z) =
      α * (c₀ * y 0 + c₁ * y 1) + (1 - α) * (c₀ * z 0 + c₁ * z 1) +
        φ (α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1)) := by
    simp only [tcpAffineUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : d₀ * (α * y 0 + (1 - α) * z 0) + d₁ * (α * y 1 + (1 - α) * z 1) =
        α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1) := by ring
    rw [this]
    ring
  have huy : tcpAffineUtility c₀ c₁ d₀ d₁ φ y =
      c₀ * y 0 + c₁ * y 1 + φ (d₀ * y 0 + d₁ * y 1) := rfl
  have huz : tcpAffineUtility c₀ c₁ d₀ d₁ φ z =
      c₀ * z 0 + c₁ * z 1 + φ (d₀ * z 0 + d₁ * z 1) := rfl
  rw [hm]
  rw [huy] at hyx
  rw [huz] at hzx
  have hsy : (0 : ℝ) ≤ d₀ * y 0 + d₁ * y 1 :=
    add_nonneg (mul_nonneg hd₀ (hy 0)) (mul_nonneg hd₁ (hy 1))
  have hsz : (0 : ℝ) ≤ d₀ * z 0 + d₁ * z 1 :=
    add_nonneg (mul_nonneg hd₀ (hz 0)) (mul_nonneg hd₁ (hz 1))
  by_cases hs : d₀ * y 0 + d₁ * y 1 = d₀ * z 0 + d₁ * z 1
  · -- same index: the linear parts differ
    have hc : c₀ * y 0 + c₁ * y 1 ≠ c₀ * z 0 + c₁ * z 1 := by
      intro hc
      apply hne
      have h0 : (c₀ * d₁ - c₁ * d₀) * (y 0 - z 0) = 0 := by linear_combination d₁ * hc - c₁ * hs
      have h1 : (c₀ * d₁ - c₁ * d₀) * (y 1 - z 1) = 0 := by linear_combination c₀ * hs - d₀ * hc
      have e0 := (mul_eq_zero.1 h0).resolve_left hdet
      have e1 := (mul_eq_zero.1 h1).resolve_left hdet
      funext l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue]
        linarith
      · simp only [Fin.mk_one, Fin.isValue]
        linarith
    have hφ' : α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1) =
        d₀ * z 0 + d₁ * z 1 := by rw [hs]; ring
    rw [hφ']
    rw [hs] at hyx
    rcases lt_or_gt_of_ne hc with h | h
    · nlinarith [mul_lt_mul_of_pos_left h hα0]
    · have h1α : 0 < 1 - α := by linarith
      nlinarith [mul_lt_mul_of_pos_left h h1α]
  · have h := hφ.2 (Set.mem_Ici.2 hsy) (Set.mem_Ici.2 hsz) hs hα0
      (by linarith : (0 : ℝ) < 1 - α) (by ring : α + (1 - α) = 1)
    simp only [smul_eq_mul] at h
    nlinarith

/-- Strictly convex preferences have at most one maximizer on a convex subset of `ℝ^L₊`: the
midpoint of two maximizers would be strictly better. -/
theorem tcp_eq_of_strictlyConvex {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (utilityPref u)) {B : Set (Fin L → ℝ)}
    (hB : Convex ℝ B) (hBX : B ⊆ nonnegOrthant L) {x y : Fin L → ℝ} (hx : x ∈ B) (hy : y ∈ B)
    (hxo : ∀ z ∈ B, u z ≤ u x) (hyo : ∀ z ∈ B, u z ≤ u y) : x = y := by
  by_contra hne
  have hmB : (1 / 2 : ℝ) • x + ((1 : ℝ) - 1 / 2) • y ∈ B :=
    hB hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
      (by norm_num)
  have h := hsc x (hBX hx) x (hBX hx) y (hBX hy) (le_refl (u x)) (hyo x hx) hne (1 / 2)
    (by norm_num) (by norm_num)
  exact h.2 (hxo _ hmB)

/-! ### The economy -/

/-- **Exercise 15.C.1(c)** (MWG, p. 542). One firm and two consumers `i : Fin 2`, each endowed
with labor alone: utilities `uᵢ` over (leisure, consumption good), time endowments `L̄ᵢ`, and the
production function `f`; each consumer owns half of the firm. -/
structure TCEconomy where
  /-- The consumers' utilities over (leisure, consumption good). -/
  u : Fin 2 → (Fin 2 → ℝ) → ℝ
  /-- The time endowments `L̄ᵢ`. -/
  Lbar : Fin 2 → ℝ
  /-- The production function `f(z)`. -/
  f : ℝ → ℝ

/-- **Exercise 15.C.1(c)** (MWG, p. 542), as (15.C.1). `z` maximizes the firm's profit
`p f(z) - w z` over `z ≥ 0`. -/
def TCEconomy.IsProfitMax (E : TCEconomy) (p w z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ z', 0 ≤ z' → p * E.f z' - w * z' ≤ p * E.f z - w * z

/-- **Exercise 15.C.1(c)** (MWG, p. 542), as (15.C.2). Consumer `i`'s budget set at prices
`(p, w)` with nonlabor income `m`: `x ∈ ℝ²₊` with `p x₂ ≤ w(L̄ᵢ - x₁) + m`. -/
def TCEconomy.budget (E : TCEconomy) (i : Fin 2) (p w m : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ p * x 1 ≤ w * (E.Lbar i - x 0) + m}

/-- **Exercise 15.C.1(c)** (MWG, p. 542). `x` solves consumer `i`'s problem. -/
def TCEconomy.IsConsumerOpt (E : TCEconomy) (i : Fin 2) (p w m : ℝ) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.budget i p w m ∧ ∀ y ∈ E.budget i p w m, E.u i y ≤ E.u i x

/-- **Exercise 15.C.1(c)** (MWG, p. 542). A Walrasian equilibrium: prices `(p, w)`, labor demand
`z` maximizing profit, bundles `xᵢ` maximizing utility with income `w L̄ᵢ + π/2`,
`π = p f(z) - w z`, and market clearing `x₂₁ + x₂₂ = f(z)`, `z = (L̄₁ - x₁₁) + (L̄₂ - x₁₂)`. -/
def TCEconomy.IsWalrasEqm (E : TCEconomy) (p w : ℝ) (x : Fin 2 → Fin 2 → ℝ) (z : ℝ) : Prop :=
  E.IsProfitMax p w z ∧ (∀ i, E.IsConsumerOpt i p w ((p * E.f z - w * z) / 2) (x i)) ∧
    x 0 1 + x 1 1 = E.f z ∧ z = (E.Lbar 0 - x 0 0) + (E.Lbar 1 - x 1 0)

/-! ### The example with strictly decreasing returns -/

/-- **Exercise 15.C.1(c)** (MWG, p. 542). The example: `f(z) = 7 z^{1/7}`; consumer 1 has
`u₁(x) = x₁ + v_A(x₂)`, `v_A = tcpPowFive (15841/2175) (3/10)`, `L̄₁ = 6`; consumer 2 has
`u₂(x) = x₂ + v_B(x₁)`, `v_B = tcpPowFive (7141/2175) (1/10)`, `L̄₂ = 1/5`. -/
noncomputable def ex15C1cEconomy : TCEconomy where
  u := ![tcpAffineUtility 1 0 0 1 (tcpPowFive (15841 / 2175) (3 / 10)),
    tcpAffineUtility 0 1 1 0 (tcpPowFive (7141 / 2175) (1 / 10))]
  Lbar := ![6, 1 / 5]
  f := fun z => 7 * z ^ (1 / 7 : ℝ)

/-- Consumer 1 of `ex15C1cEconomy`, quasilinear in leisure. -/
theorem ex15C1c_u0 :
    ex15C1cEconomy.u 0 = tcpAffineUtility 1 0 0 1 (tcpPowFive (15841 / 2175) (3 / 10)) := rfl

/-- Consumer 2 of `ex15C1cEconomy`, quasilinear in consumption. -/
theorem ex15C1c_u1 :
    ex15C1cEconomy.u 1 = tcpAffineUtility 0 1 1 0 (tcpPowFive (7141 / 2175) (1 / 10)) := rfl

/-- Consumer 1 of `ex15C1cEconomy` has six units of time. -/
theorem ex15C1c_Lbar0 : ex15C1cEconomy.Lbar 0 = 6 := rfl

/-- Consumer 2 of `ex15C1cEconomy` has one fifth of a unit of time. -/
theorem ex15C1c_Lbar1 : ex15C1cEconomy.Lbar 1 = 1 / 5 := rfl

/-- Consumer 1 (quasilinear in leisure, `u = x₁ + v(x₂)`, `v = tcpPowFive a e`) at the wage
`w = θ⁶` (`p = 1`): a bundle on the budget line with `x₂ + e = aθ` (so `v'(x₂) = 1/w`) is
optimal in the budget set, whatever the income. -/
theorem tcp_consumerA_opt {a e θ L m : ℝ} (ha : 0 < a) (he : 0 < e) (hθ : 0 < θ)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hc : x 1 + e = a * θ)
    (hbud : x 1 = θ ^ 6 * (L - x 0) + m) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : 1 * y 1 ≤ θ ^ 6 * (L - y 0) + m) :
    tcpAffineUtility 1 0 0 1 (tcpPowFive a e) y ≤ tcpAffineUtility 1 0 0 1 (tcpPowFive a e) x := by
  simp only [tcpAffineUtility, one_mul, zero_mul, add_zero, zero_add]
  have ht := tcpPowFive_tangent ha (s := x 1) (t := y 1) (e := e) (by linarith [hx 1])
    (by linarith [hy 1])
  have hD : (a / (x 1 + e)) ^ 6 = 1 / θ ^ 6 := by
    rw [hc]
    field_simp
  rw [hD] at ht
  have hw : 0 < θ ^ 6 := by positivity
  have h1 : (y 1 - x 1) / θ ^ 6 ≤ x 0 - y 0 := by
    rw [div_le_iff₀ hw]
    nlinarith
  have h2 : 1 / θ ^ 6 * (y 1 - x 1) = (y 1 - x 1) / θ ^ 6 := by ring
  linarith

/-- Consumer 2 (quasilinear in consumption, `u = x₂ + v(x₁)`, `v = tcpPowFive b e`) at the wage
`w = θ⁶` (`p = 1`): a bundle on the budget line with `x₁ + e = b/θ` (so `v'(x₁) = w`) is optimal
in the budget set, whatever the income. -/
theorem tcp_consumerB_opt {b e θ L m : ℝ} (hb : 0 < b) (he : 0 < e) (hθ : 0 < θ)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hl : x 0 + e = b / θ)
    (hbud : x 1 = θ ^ 6 * (L - x 0) + m) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : 1 * y 1 ≤ θ ^ 6 * (L - y 0) + m) :
    tcpAffineUtility 0 1 1 0 (tcpPowFive b e) y ≤ tcpAffineUtility 0 1 1 0 (tcpPowFive b e) x := by
  simp only [tcpAffineUtility, one_mul, zero_mul, add_zero, zero_add]
  have ht := tcpPowFive_tangent hb (s := x 0) (t := y 0) (e := e) (by linarith [hx 0])
    (by linarith [hy 0])
  have hD : (b / (x 0 + e)) ^ 6 = θ ^ 6 := by
    rw [hl]
    field_simp
  rw [hD] at ht
  nlinarith

/-- The firm of the example at the wage `w = θ⁶` (`p = 1`): `z* = θ⁻⁷` maximizes
`7 z^{1/7} - θ⁶ z` (with `u = θ z^{1/7}`: `u⁷ - 7u + 6 = (u - 1)²(u⁵ + 2u⁴ + ⋯ + 6) ≥ 0`), with
output `7/θ` and profit `6/θ`. -/
theorem ex15C1c_profitMax {θ : ℝ} (hθ : 0 < θ) :
    ex15C1cEconomy.IsProfitMax 1 (θ ^ 6) ((θ⁻¹) ^ 7) ∧
      ex15C1cEconomy.f ((θ⁻¹) ^ 7) = 7 / θ := by
  have h7 : (1 / 7 : ℝ) = ((7 : ℕ) : ℝ)⁻¹ := by norm_num
  have hf : ex15C1cEconomy.f ((θ⁻¹) ^ 7) = 7 / θ := by
    change 7 * ((θ⁻¹) ^ 7) ^ (1 / 7 : ℝ) = 7 / θ
    rw [h7, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
    ring
  refine ⟨⟨by positivity, fun z hz => ?_⟩, hf⟩
  rw [hf]
  change 1 * (7 * z ^ (1 / 7 : ℝ)) - θ ^ 6 * z ≤ 1 * (7 / θ) - θ ^ 6 * θ⁻¹ ^ 7
  set t := z ^ (1 / 7 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hz _
  have htz : t ^ 7 = z := by
    rw [ht, h7]
    exact Real.rpow_inv_natCast_pow hz (by norm_num)
  rw [← htz]
  have hv : 0 ≤ θ * t := mul_nonneg hθ.le ht0
  have key : 0 ≤ (θ * t) ^ 7 - 7 * (θ * t) + 6 := by
    have e : (θ * t) ^ 7 - 7 * (θ * t) + 6 = (θ * t - 1) ^ 2 * ((θ * t) ^ 5 + 2 * (θ * t) ^ 4 +
        3 * (θ * t) ^ 3 + 4 * (θ * t) ^ 2 + 5 * (θ * t) + 6) := by ring
    rw [e]
    positivity
  have hr : 1 * (7 / θ) - θ ^ 6 * θ⁻¹ ^ 7 = 6 / θ := by
    field_simp
    ring
  rw [hr, le_div_iff₀ hθ]
  nlinarith [key]

/-- The example at the wage `w = θ⁶`, `p = 1`, labor `z = θ⁻⁷`: an allocation `x ≥ 0` with
consumer 1 at `x₂₁ + 3/10 = (15841/2175)θ`, consumer 2 at `x₁₂ + 1/10 = (7141/2175)/θ`, both on
their budget lines with profit share `3/θ`, and clearing markets, is a Walrasian equilibrium. -/
theorem ex15C1c_eqm_of {θ : ℝ} (hθ : 0 < θ) {x : Fin 2 → Fin 2 → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant 2) (hA : x 0 1 + 3 / 10 = 15841 / 2175 * θ)
    (hB : x 1 0 + 1 / 10 = 7141 / 2175 / θ) (hbA : x 0 1 = θ ^ 6 * (6 - x 0 0) + 3 / θ)
    (hbB : x 1 1 = θ ^ 6 * (1 / 5 - x 1 0) + 3 / θ) (hgoods : x 0 1 + x 1 1 = 7 / θ)
    (hlabor : (θ⁻¹) ^ 7 = (6 - x 0 0) + (1 / 5 - x 1 0)) :
    ex15C1cEconomy.IsWalrasEqm 1 (θ ^ 6) x ((θ⁻¹) ^ 7) := by
  obtain ⟨hpm, hf⟩ := ex15C1c_profitMax hθ
  have hm : (1 * ex15C1cEconomy.f ((θ⁻¹) ^ 7) - θ ^ 6 * (θ⁻¹) ^ 7) / 2 = 3 / θ := by
    rw [hf]
    field_simp
    ring
  refine ⟨hpm, Fin.forall_fin_two.2 ⟨?_, ?_⟩, by rw [hf]; exact hgoods, hlabor⟩
  · rw [hm]
    refine ⟨⟨hx 0, ?_⟩, fun y hy => ?_⟩
    · rw [ex15C1c_Lbar0]
      linarith
    · rw [ex15C1c_u0]
      have hyb := hy.2
      rw [ex15C1c_Lbar0] at hyb
      exact tcp_consumerA_opt (by norm_num) (by norm_num) hθ (hx 0) hA hbA hy.1 hyb
  · rw [hm]
    refine ⟨⟨hx 1, ?_⟩, fun y hy => ?_⟩
    · rw [ex15C1c_Lbar1]
      linarith
    · rw [ex15C1c_u1]
      have hyb := hy.2
      rw [ex15C1c_Lbar1] at hyb
      exact tcp_consumerB_opt (by norm_num) (by norm_num) hθ (hx 1) hB hbB hy.1 hyb

/-- The equilibrium allocation of the example at `w = 1`. -/
noncomputable def ex15C1cAlloc1 : Fin 2 → Fin 2 → ℝ :=
  ![![8773 / 4350, 30377 / 4350], ![13847 / 4350, 73 / 4350]]

/-- The equilibrium allocation of the example at `w = (8/9)⁶`. -/
noncomputable def ex15C1cAlloc2 : Fin 2 → Fin 2 → ℝ :=
  ![![495178323 / 1520435200, 241711 / 39150], ![20843 / 5800, 266381 / 156600]]

/-- **Exercise 15.C.1(c)** (MWG, p. 542). Multiple equilibria with one firm and two consumers
endowed with labor alone, profits split equally: in `ex15C1cEconomy` (strictly convex, see
`ex15C1c_strictlyConvex`), at `p = 1` both `w = 1` (labor `z = 1`, output `7`) and
`w = 262144/531441 = (8/9)⁶` (labor `z = (9/8)⁷`, output `63/8`) are equilibrium wages; the real
wages and the allocations differ. -/
theorem exercise_15_C_1c :
    ex15C1cEconomy.IsWalrasEqm 1 1 ex15C1cAlloc1 1 ∧
      ex15C1cEconomy.IsWalrasEqm 1 (262144 / 531441) ex15C1cAlloc2 (4782969 / 2097152) ∧
      (1 : ℝ) / 1 ≠ (262144 / 531441) / 1 ∧ ex15C1cAlloc1 ≠ ex15C1cAlloc2 ∧
      (1 : ℝ) ≠ 4782969 / 2097152 := by
  refine ⟨?_, ?_, by norm_num, fun h => ?_, by norm_num⟩
  · have h := ex15C1c_eqm_of (θ := 1) one_pos (x := ex15C1cAlloc1)
      (fun i => by fin_cases i <;> intro l <;> fin_cases l <;> norm_num [ex15C1cAlloc1])
      (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1])
      (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1])
    rwa [one_pow, inv_one, one_pow] at h
  · have h := ex15C1c_eqm_of (θ := 8 / 9) (by norm_num) (x := ex15C1cAlloc2)
      (fun i => by fin_cases i <;> intro l <;> fin_cases l <;> norm_num [ex15C1cAlloc2])
      (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2])
      (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2])
    rwa [show ((8 : ℝ) / 9) ^ 6 = 262144 / 531441 by norm_num,
      show ((8 / 9 : ℝ)⁻¹) ^ 7 = 4782969 / 2097152 by norm_num] at h
  · have := congrFun (congrFun h 0) 1
    norm_num [ex15C1cAlloc1, ex15C1cAlloc2] at this

/-- **Exercise 15.C.1(c)** (MWG, p. 542). The example economy is strictly convex: each utility is
continuous on `ℝ²₊`, strongly monotone and strictly convex, and `f(z) = 7 z^{1/7}` is strictly
concave on `[0, ∞)` (strictly decreasing returns to scale). -/
theorem ex15C1c_strictlyConvex :
    (∀ i, ContinuousOn (ex15C1cEconomy.u i) (nonnegOrthant 2) ∧
      UtilityStronglyMonotone (ex15C1cEconomy.u i) ∧
      PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (ex15C1cEconomy.u i))) ∧
      StrictConcaveOn ℝ (Set.Ici 0) ex15C1cEconomy.f := by
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
  · rw [ex15C1c_u0]
    have ha : (0 : ℝ) < 15841 / 2175 := by norm_num
    have he : (0 : ℝ) < 3 / 10 := by norm_num
    exact ⟨tcpAffineUtility_continuousOn le_rfl zero_le_one (tcpPowFive_continuousOn he),
      tcpAffineUtility_stronglyMonotone zero_le_one le_rfl le_rfl zero_le_one
        (Or.inl one_pos) (Or.inr one_pos) (tcpPowFive_strictMonoOn ha he),
      tcpAffineUtility_strictlyConvex le_rfl zero_le_one (by norm_num)
        (tcpPowFive_strictConcaveOn ha he)⟩
  · rw [ex15C1c_u1]
    have hb : (0 : ℝ) < 7141 / 2175 := by norm_num
    have he : (0 : ℝ) < 1 / 10 := by norm_num
    exact ⟨tcpAffineUtility_continuousOn zero_le_one le_rfl (tcpPowFive_continuousOn he),
      tcpAffineUtility_stronglyMonotone le_rfl zero_le_one zero_le_one le_rfl
        (Or.inr one_pos) (Or.inl one_pos) (tcpPowFive_strictMonoOn hb he),
      tcpAffineUtility_strictlyConvex zero_le_one le_rfl (by norm_num)
        (tcpPowFive_strictConcaveOn hb he)⟩
  · refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (Real.strictConcaveOn_rpow (p := 1 / 7) (by norm_num) (by norm_num)).2 hx hy hxy
      ha hb hab
    simp only [smul_eq_mul] at this ⊢
    change a * (7 * x ^ (1 / 7 : ℝ)) + b * (7 * y ^ (1 / 7 : ℝ)) < 7 * (a * x + b * y) ^ (1 / 7 : ℝ)
    nlinarith

/-! ### Constant returns to scale -/

/-- In an equilibrium with consumer 1's preferences strongly monotone, the price of the
consumption good is positive (otherwise more of it is free). -/
theorem tcp_eqm_price_pos {E : TCEconomy} (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ}
    {x : Fin 2 → Fin 2 → ℝ} {z : ℝ} (h : E.IsWalrasEqm p w x z) : 0 < p := by
  by_contra hp
  rw [not_lt] at hp
  have hx := h.2.1 0
  have hmem : x 0 + Pi.single 1 1 ∈ E.budget 0 p w ((p * E.f z - w * z) / 2) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hx.1.1 0
      · simp; linarith [hx.1.1 1]
    · have := hx.1.2
      simp only [Pi.add_apply, Pi.single_eq_same]
      simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
      nlinarith
  have h1 := hx.2 _ hmem
  have h2 := hmono.lt hx.1.1 (y := x 0 + Pi.single 1 1) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  linarith

/-- Profit maximization with `f(z) = αz`: the wage is at least `αp` and profit is zero. -/
theorem tcp_crs_profitMax {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z) {p w z : ℝ}
    (h : E.IsProfitMax p w z) : α * p ≤ w ∧ p * E.f z - w * z = 0 := by
  obtain ⟨hz, hmax⟩ := h
  rw [hf] at hmax ⊢
  have h1 := hmax (z + 1) (by linarith)
  have h0 := hmax 0 le_rfl
  simp only at h1 h0 ⊢
  have hw : α * p ≤ w := by nlinarith
  refine ⟨hw, ?_⟩
  have : (α * p - w) * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hz
  nlinarith

/-- **Exercise 15.C.1(c)** (MWG, p. 542), constant returns `f(z) = αz`: there is no equilibrium
with `w < αp` (profits would be unbounded). -/
theorem exercise_15_C_1c_crs_no_low_wage {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z)
    {p w : ℝ} (hw : w < α * p) (x : Fin 2 → Fin 2 → ℝ) (z : ℝ) : ¬ E.IsWalrasEqm p w x z :=
  fun h => absurd (tcp_crs_profitMax hf h.1).1 (not_le.2 hw)

/-- With constant returns `f(z) = αz` (`α > 0`) and strongly monotone preferences, each consumer's
equilibrium bundle solves his problem at the prices `(p, w) = (1, α)` with zero profit. -/
theorem tcp_crs_consumerOpt {E : TCEconomy} {α : ℝ} (hα : 0 < α) (hf : E.f = fun z => α * z)
    (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ} {x : Fin 2 → Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (i : Fin 2) : E.IsConsumerOpt i 1 α 0 (x i) := by
  have hp := tcp_eqm_price_pos hmono h
  obtain ⟨hw, hπ⟩ := tcp_crs_profitMax hf h.1
  obtain ⟨hpm, hopt, hgoods, hlabor⟩ := h
  rw [hπ, zero_div] at hopt
  -- the budget set at `(1, α)` lies in the equilibrium budget set
  have hsub : E.budget i 1 α 0 ⊆ E.budget i p w 0 := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hb := hy.2
    have hy1 := hy.1 1
    have hL : 0 ≤ E.Lbar i - y 0 := by
      by_contra hneg
      rw [not_le] at hneg
      have : α * (E.Lbar i - y 0) < 0 := mul_neg_of_pos_of_neg hα hneg
      linarith
    have : α * p * (E.Lbar i - y 0) ≤ w * (E.Lbar i - y 0) := mul_le_mul_of_nonneg_right hw hL
    nlinarith
  -- the equilibrium bundle is affordable at `(1, α)`
  have hmem : x i ∈ E.budget i 1 α 0 := by
    refine ⟨(hopt i).1.1, ?_⟩
    rcases eq_or_lt_of_le hw with hweq | hwlt
    · have hb := (hopt i).1.2
      rw [← hweq] at hb
      have : p * x i 1 ≤ p * (α * (E.Lbar i - x i 0) + 0) := by nlinarith
      have := le_of_mul_le_mul_left this hp
      linarith
    · -- `w > αp`: nothing is produced and every consumer stays at his endowment point
      have hz : z = 0 := by
        have hfz : p * E.f z - w * z = (α * p - w) * z := by rw [hf]; ring
        rw [hfz] at hπ
        rcases mul_eq_zero.1 hπ with h1 | h1
        · linarith
        · exact h1
      have hf0 : E.f z = 0 := by rw [hf, hz]; ring
      have hw0 : 0 < w := by nlinarith
      have hL : ∀ j, 0 ≤ E.Lbar j - x j 0 := by
        intro j
        have hb := (hopt j).1.2
        have := (hopt j).1.1 1
        by_contra hneg
        rw [not_le] at hneg
        have : w * (E.Lbar j - x j 0) < 0 := mul_neg_of_pos_of_neg hw0 hneg
        nlinarith
      have hL0 := hL 0
      have hL1 := hL 1
      have hc0 := (hopt 0).1.1 1
      have hc1 := (hopt 1).1.1 1
      rw [hf0] at hgoods
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]
        nlinarith
      · simp only [Fin.mk_one, Fin.isValue]
        nlinarith
  exact ⟨hmem, fun y hy => (hopt i).2 y (hsub hy)⟩

/-- The budget set `{x ∈ ℝ²₊ : p x₂ ≤ w(L̄ᵢ - x₁) + m}` is convex. -/
theorem TCEconomy.convex_budget (E : TCEconomy) (i : Fin 2) (p w m : ℝ) :
    Convex ℝ (E.budget i p w m) := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_nonnegOrthant 2 hy.1 hz.1 ha hb hab, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hy.2 ha
  have h2 := mul_le_mul_of_nonneg_left hz.2 hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : m = (a + b) * m := by rw [hab, one_mul]
  have e2 : w * E.Lbar i = (a + b) * (w * E.Lbar i) := by rw [hab, one_mul]
  nlinarith

/-- **Exercise 15.C.1(c)** (MWG, p. 542), second question. With constant returns `f(z) = αz`
(`α > 0`) and strongly monotone, strictly convex preferences, the equilibrium allocation is
unique: any two equilibria have the same consumption bundles and the same level of production.
(Every equilibrium bundle is the unique demand at `(p, w) = (1, α)` with zero profit.) -/
theorem exercise_15_C_1c_crs {E : TCEconomy} {α : ℝ} (hα : 0 < α) (hf : E.f = fun z => α * z)
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (E.u i))) {p w p' w' z z' : ℝ}
    {x x' : Fin 2 → Fin 2 → ℝ} (h : E.IsWalrasEqm p w x z) (h' : E.IsWalrasEqm p' w' x' z') :
    x = x' ∧ z = z' := by
  have hx : ∀ i, x i = x' i := by
    intro i
    have o := tcp_crs_consumerOpt hα hf (hmono 0) h i
    have o' := tcp_crs_consumerOpt hα hf (hmono 0) h' i
    exact tcp_eq_of_strictlyConvex (hsc i) (E.convex_budget i 1 α 0) (fun y hy => hy.1) o.1 o'.1
      o.2 o'.2
  have hxx : x = x' := funext hx
  refine ⟨hxx, ?_⟩
  rw [h.2.2.2, h'.2.2.2, hxx]

/-- **Exercise 15.C.1(c)** (MWG, p. 542), constant returns `f(z) = αz`: in an equilibrium with
positive production the real wage is `w/p = α`. -/
theorem exercise_15_C_1c_crs_wage {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z)
    (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ} {x : Fin 2 → Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (hz : 0 < z) : w / p = α := by
  have hp := tcp_eqm_price_pos hmono h
  have hπ := (tcp_crs_profitMax hf h.1).2
  rw [hf] at hπ
  simp only at hπ
  have : (α * p - w) * z = 0 := by linarith
  have hw : α * p - w = 0 := (mul_eq_zero.1 this).resolve_right hz.ne'
  rw [div_eq_iff hp.ne']
  linarith

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Offer curve examples (MWG Exercise 15.B.4(d), p. 541; Figure 15.B.10(b), p. 522)

* **Exercise 15.B.4(d)**, first sentence: preferences whose offer curve is not normal. The consumer
  has endowment `ω = (10, 0)` and the continuous, strongly monotone, strictly convex utility
  `u(x) = x₁ + v(4x₁ + x₂)`, `v = tcpPowFive (1595/32) (19/32)` (`ex15B4dUtility`,
  `ex15B4d_props`). At prices `(q, 1)` demand is the single bundle `(3/4, 185/4)` for `q = 5` and
  `(7, 2955/64)` for `q = 985/64` (`ex15B4d_demand_five`, `ex15B4d_demand_high`): raising the
  relative price of good 1 raises the demand for good 1 but lowers the demand for good 2, so every
  selection from this consumer's demand is a non-normal offer curve (`exercise_15_B_4d_exists`).
  Good 2 is inferior, as `exercise_15_B_4d` requires: at `q = 5` an extra unit of wealth moves
  demand by `(1, -4)` (`ex15B4d_inferior`).
* **Figure 15.B.10(b)**: the offer curve of the nonconvex consumer 1 (`x₁² + x₂²`, endowment
  `(1, 1)`) is the union of the two half-lines `{(t, 0) : t ≥ 2}` and `{(0, t) : t ≥ 2}`
  (`fig_15_B_10b_offerCurve`), which is disconnected (`fig_15_B_10b_offerCurve_not_preconnected`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-! ### Exercise 15.B.4(d): a non-normal offer curve -/

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The utility `u(x) = x₁ + v(4x₁ + x₂)` with
`v(s) = -(K/5)(K/(s + e))⁵`, `K = 1595/32`, `e = 19/32`. -/
noncomputable def ex15B4dUtility : (Fin 2 → ℝ) → ℝ :=
  tcpAffineUtility 1 0 4 1 (tcpPowFive (1595 / 32) (19 / 32))

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The consumer's demand at prices `(q, 1)` with the
endowment `ω = (10, 0)`, i.e. wealth `10q`. -/
noncomputable def ex15B4dDemand (q : ℝ) : Set (Fin 2 → ℝ) :=
  walrasianDemand ex15B4dUtility ![q, 1] (![q, 1] ⬝ᵥ ![10, 0])

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The utility `ex15B4dUtility` is continuous on `ℝ²₊`,
strongly monotone and strictly convex. -/
theorem ex15B4d_props : ContinuousOn ex15B4dUtility (nonnegOrthant 2) ∧
    UtilityStronglyMonotone ex15B4dUtility ∧
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref ex15B4dUtility) := by
  have ha : (0 : ℝ) < 1595 / 32 := by norm_num
  have he : (0 : ℝ) < 19 / 32 := by norm_num
  exact ⟨tcpAffineUtility_continuousOn (by norm_num) zero_le_one (tcpPowFive_continuousOn he),
    tcpAffineUtility_stronglyMonotone zero_le_one le_rfl (by norm_num) zero_le_one
      (Or.inl one_pos) (Or.inr one_pos) (tcpPowFive_strictMonoOn ha he),
    tcpAffineUtility_strictlyConvex (by norm_num) zero_le_one (by norm_num)
      (tcpPowFive_strictConcaveOn ha he)⟩

/-- `(q, 1)·y = q y₁ + y₂`. -/
theorem ex15B4d_dot (q : ℝ) (y : Fin 2 → ℝ) : ![q, 1] ⬝ᵥ y = q * y 0 + y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The first-order condition is sufficient: at prices `(q, 1)`, `q > 4`, a bundle `x ≥ 0` on the
budget line `q x₁ + x₂ = W` with `v'(4x₁ + x₂) = 1/(q - 4)` maximizes utility on the budget set
(tangent inequality: `u(y) - u(x) ≤ v'(s)(q(y₁ - x₁) + (y₂ - x₂)) ≤ 0`). -/
theorem ex15B4d_opt {q W : ℝ} (hq : 4 < q) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2)
    (hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / (q - 4))
    (hb : q * x 0 + x 1 = W) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : q * y 0 + y 1 ≤ W) : ex15B4dUtility y ≤ ex15B4dUtility x := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hy0 := hy 0
  have hy1 := hy 1
  have ht := tcpPowFive_tangent (a := 1595 / 32) (e := 19 / 32) (s := 4 * x 0 + 1 * x 1)
    (t := 4 * y 0 + 1 * y 1) (by norm_num) (by linarith) (by linarith)
  rw [hfoc] at ht
  simp only [ex15B4dUtility, tcpAffineUtility, one_mul, zero_mul, add_zero]
  simp only [one_mul] at ht
  have hq4 : 0 < q - 4 := by linarith
  have h1 : (4 * y 0 + y 1) - (4 * x 0 + x 1) ≤ (q - 4) * (x 0 - y 0) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (one_div_pos.2 hq4).le
  have h3 : 1 / (q - 4) * ((q - 4) * (x 0 - y 0)) = x 0 - y 0 := by
    field_simp
  linarith

/-- The demand at prices `(q, 1)`, `q > 4`, is the single bundle `x` satisfying the first-order
condition and the budget identity (uniqueness from strict convexity). -/
theorem ex15B4d_demand_eq {q : ℝ} (hq : 4 < q) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2)
    (hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / (q - 4))
    (hb : q * x 0 + x 1 = 10 * q) : ex15B4dDemand q = {x} := by
  have hW : ![q, 1] ⬝ᵥ ![10, 0] = 10 * q := by rw [ex15B4d_dot]; norm_num; ring
  have hxd : x ∈ ex15B4dDemand q := by
    refine ⟨⟨hx, ?_⟩, fun y hy => ?_⟩
    · rw [ex15B4d_dot, hW, hb]
    · have hyb := hy.2
      rw [ex15B4d_dot, hW] at hyb
      exact ex15B4d_opt hq hx hfoc hb hy.1 hyb
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact tcp_eq_of_strictlyConvex ex15B4d_props.2.2 (convex_budgetSet _ _) (fun z hz => hz.1)
      hy.1 hxd.1 hy.2 hxd.2
  · rintro rfl
    exact hxd

/-- **Exercise 15.B.4(d)** (MWG, p. 541): at `q = 5` the demand is `(3/4, 185/4)`
(`4x₁ + x₂ + e = K`, so `v' = 1 = 1/(q - 4)`). -/
theorem ex15B4d_demand_five : ex15B4dDemand 5 = {![3 / 4, 185 / 4]} :=
  ex15B4d_demand_eq (by norm_num) (fun l => by fin_cases l <;> norm_num) (by norm_num)
    (by norm_num)

/-- **Exercise 15.B.4(d)** (MWG, p. 541): at `q = 985/64` the demand is `(7, 2955/64)`
(`4x₁ + x₂ + e = 3K/2`, so `v' = (2/3)⁶ = 64/729 = 1/(q - 4)`). -/
theorem ex15B4d_demand_high : ex15B4dDemand (985 / 64) = {![7, 2955 / 64]} :=
  ex15B4d_demand_eq (by norm_num) (fun l => by fin_cases l <;> norm_num) (by norm_num)
    (by norm_num)

/-- **Exercise 15.B.4(d)** (MWG, p. 541): there are preferences giving rise to offer curves that
are not normal. For the continuous, strongly monotone, strictly convex `ex15B4dUtility` with
endowment `(10, 0)`, raising the relative price of good 1 from `5` to `985/64` raises the demand
for good 1 (`3/4 → 7`) but lowers the demand for good 2 (`2960/64 → 2955/64`); so every
selection `d` of the demand at prices `(q, 1)` is not a normal offer curve. -/
theorem exercise_15_B_4d_exists (d : ℝ → Fin 2 → ℝ) (h5 : d 5 ∈ ex15B4dDemand 5)
    (hh : d (985 / 64) ∈ ex15B4dDemand (985 / 64)) : ¬ NormalOfferCurve d := by
  rw [ex15B4d_demand_five, Set.mem_singleton_iff] at h5
  rw [ex15B4d_demand_high, Set.mem_singleton_iff] at hh
  intro hN
  have h := hN.1 5 (985 / 64) (by norm_num) (by norm_num) (by rw [h5, hh]; norm_num)
  rw [h5, hh] at h
  norm_num at h

/-- **Exercise 15.B.4(d)** (MWG, p. 541), second sentence for this example: good 2 is inferior.
At prices `(5, 1)`, wealth `50 + δ` (`-3/4 ≤ δ ≤ 185/16`) gives the demand
`(3/4 + δ, 185/4 - 4δ)`, so raising wealth lowers the demand for good 2. -/
theorem ex15B4d_inferior {δ : ℝ} (hδ : -(3 / 4) ≤ δ) (hδ' : δ ≤ 185 / 16) :
    walrasianDemand ex15B4dUtility ![5, 1] (50 + δ) = {![3 / 4 + δ, 185 / 4 - 4 * δ]} := by
  set x : Fin 2 → ℝ := ![3 / 4 + δ, 185 / 4 - 4 * δ] with hxdef
  have hx : x ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hxdef]; linarith
    · simp [hxdef]; linarith
  have hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / ((5 : ℝ) - 4) := by
    simp only [hxdef, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e : 4 * (3 / 4 + δ) + 1 * (185 / 4 - 4 * δ) + 19 / 32 = (1595 / 32 : ℝ) := by
      ring
    rw [e]
    norm_num
  have hb : 5 * x 0 + x 1 = 50 + δ := by
    simp only [hxdef, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hxd : x ∈ walrasianDemand ex15B4dUtility ![5, 1] (50 + δ) := by
    refine ⟨⟨hx, ?_⟩, fun y hy => ?_⟩
    · rw [ex15B4d_dot, hb]
    · have hyb := hy.2
      rw [ex15B4d_dot] at hyb
      exact ex15B4d_opt (by norm_num) hx hfoc hb hy.1 hyb
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact tcp_eq_of_strictlyConvex ex15B4d_props.2.2 (convex_budgetSet _ _) (fun z hz => hz.1)
      hy.1 hxd.1 hy.2 hxd.2
  · rintro rfl
    exact hxd

/-! ### Figure 15.B.10(b): a disconnected offer curve -/

/-- Consumer 1's demand in `fig10bEconomy` is the demand of `x₁² + x₂²` with wealth `p₁ + p₂`. -/
theorem fig10b_demand0 (p : Fin 2 → ℝ) :
    fig10bEconomy.demand 0 p = walrasianDemand sqUtility p (p 0 + p 1) := by
  have hw0 : p ⬝ᵥ fig10bEconomy.ω 0 = p 0 + p 1 := by
    simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
  rw [← hw0]
  rfl

/-- At `p = (1, t - 1)`, `t ≥ 2`, the `x₁² + x₂²` consumer with wealth `t` demands `(t, 0)`. -/
theorem fig10b_corner_mem {t : ℝ} (ht : 2 ≤ t) :
    ![t, 0] ∈ walrasianDemand sqUtility ![1, t - 1] (![1, t - 1] 0 + ![1, t - 1] 1) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
  · fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · simp
  · simp [dotProduct, Fin.sum_univ_two]
  · obtain ⟨hy0, hb⟩ := hy
    have hb' : y 0 + (t - 1) * y 1 ≤ 1 + (t - 1) := by
      simpa [dotProduct, Fin.sum_univ_two] using hb
    have h0 := hy0 0
    have h1 := hy0 1
    have hs : y 0 + y 1 ≤ t := by nlinarith
    simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith

/-- **Figure 15.B.10(b)** (MWG, p. 522): the offer curve of consumer 1 (`x₁² + x₂²`, endowment
`(1, 1)`) consists of the two half-lines `{(t, 0) : t ≥ 2}` and `{(0, t) : t ≥ 2}`: demand at
`p ≫ 0` is a corner with `x₁ + x₂ = (p₁ + p₂)/min(p₁, p₂) ≥ 2`, and `p = (1, t - 1)` gives
`(t, 0)`, `p = (t - 1, 1)` gives `(0, t)`. -/
theorem fig_15_B_10b_offerCurve : fig10bEconomy.offerCurve 0 =
    {x | x 1 = 0 ∧ 2 ≤ x 0} ∪ {x | x 0 = 0 ∧ 2 ≤ x 1} := by
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [fig10b_demand0] at hx
    have hp0 := hp 0
    have hp1 := hp 1
    obtain ⟨hc0, hc1⟩ := sqUtility_demand_corner hp (by linarith) hx
    have hm0 : 0 < min (p 0) (p 1) := lt_min hp0 hp1
    have h2 : 2 ≤ (p 0 + p 1) / min (p 0) (p 1) := by
      rw [le_div_iff₀ hm0]
      linarith [min_le_left (p 0) (p 1), min_le_right (p 0) (p 1)]
    rcases mul_eq_zero.1 hc0 with h | h
    · right
      refine ⟨h, ?_⟩
      rw [h, zero_add] at hc1
      linarith
    · left
      refine ⟨h, ?_⟩
      rw [h, add_zero] at hc1
      linarith
  · rintro (⟨h1, h0⟩ | ⟨h0, h1⟩)
    · refine ⟨![1, x 0 - 1], fun l => ?_, ?_⟩
      · fin_cases l
        · simp
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          linarith
      rw [fig10b_demand0]
      have hx : x = ![x 0, 0] := by
        funext l
        fin_cases l
        · rfl
        · simpa using h1
      rw [hx]
      simpa using fig10b_corner_mem h0
    · refine ⟨![x 1 - 1, 1], fun l => ?_, ?_⟩
      · fin_cases l
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          linarith
        · simp
      rw [fig10b_demand0]
      have hx : x = ![0, x 1] := by
        funext l
        fin_cases l
        · simpa using h0
        · rfl
      -- swap the two goods
      have hm := fig10b_corner_mem h1
      obtain ⟨-, hmax⟩ := hm
      rw [hx]
      refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
      · fin_cases l
        · simp
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          linarith
      · simp [dotProduct, Fin.sum_univ_two]
      · have := hmax ![y 1, y 0] ⟨fun l => by fin_cases l <;> simp [hy.1 0, hy.1 1], by
          have hb := hy.2
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one] at hb ⊢
          linarith⟩
        simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        linarith

/-- **Figure 15.B.10(b)** (MWG, p. 522): consumer 1's offer curve is disconnected. On it
`x₁ - x₂ ≥ 2` or `x₁ - x₂ ≤ -2`, and both signs occur, so `x₁ - x₂` would have to take the value
`0` on a preconnected offer curve (intermediate value theorem). -/
theorem fig_15_B_10b_offerCurve_not_preconnected :
    ¬ IsPreconnected (fig10bEconomy.offerCurve 0) := by
  intro hc
  rw [fig_15_B_10b_offerCurve] at hc
  have ha : (![0, 2] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪
      {x | x 0 = 0 ∧ 2 ≤ x 1} := Or.inr ⟨by simp, by simp⟩
  have hb : (![2, 0] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪
      {x | x 0 = 0 ∧ 2 ≤ x 1} := Or.inl ⟨by simp, by simp⟩
  have hf : ContinuousOn (fun x : Fin 2 → ℝ => x 0 - x 1)
      ({x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪ {x | x 0 = 0 ∧ 2 ≤ x 1}) :=
    (by fun_prop : Continuous fun x : Fin 2 → ℝ => x 0 - x 1).continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : Fin 2 → ℝ => x 0 - x 1) ![0, 2])
      ((fun x : Fin 2 → ℝ => x 0 - x 1) ![2, 0]) := by
    simp
  obtain ⟨x, hx, hx0⟩ := hc.intermediate_value ha hb hf h0
  simp only at hx0
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hx0
    linarith
  · rw [h1] at hx0
    linarith

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cobb-Douglas 2 × 2 model; Exercises 15.D.6(c), 15.D.6(d), 15.D.8 (MWG pp. 532-544)

The 2 × 2 production model of Section 15.D (`TwoByTwo`) with Cobb-Douglas technologies, and the
remaining parts of Exercise 15.D.6.

* The Cobb-Douglas technology `f(z) = z₁^α z₂^(1-α)`, `0 < α < 1`, with unit input vector
  `a(w) = (r^(1-α), r^(-α))`, `r = α w₂/((1-α) w₁)`, and unit cost
  `c(w) = (w₁/α)^α (w₂/(1-α))^(1-α)`: cost minimization and uniqueness of the minimizer by the
  weighted AM-GM inequality and its equality case (`cdtA_min`, `cdtA_unique`); the general
  Cobb-Douglas 2 × 2 model satisfies the standing assumptions (`cdtModel_isModel`) and factor
  intensity when `α₂ < α₁` (`cdtModel_factorIntensity`). The model of **Exercise 15.D.8** is
  `cdModel` (`α = (2/3, 1/3)`).
* **Exercise 15.D.8**: at `p = (1, 1)`, for every `z̄ ≫ 0` the equilibrium exists and is unique
  (`exercise_15_D_8`), with the three regions of `ρ = z̄₁/z̄₂`: diversified for `1/2 < ρ < 2`
  (`exercise_15_D_8_diversified`, `exercise_15_D_8_outputs`), specialized in good 1 for `ρ ≥ 2`
  (`exercise_15_D_8_spec0`) and in good 2 for `ρ ≤ 1/2` (`exercise_15_D_8_spec1`).
* **Exercise 15.D.6(c)**: as printed the claim is false for the model as formalized (the
  Leontief model, which satisfies all standing assumptions and factor intensity, has
  unit-dollar isoquants meeting in two points: `exercise_15_D_6c_counterexample`). Corrected
  statement (`TwoByTwo.exercise_15_D_6c`): with ray-surjectivity (every factor ratio is
  cost-minimizing at some factor prices) and differentiability of `fⱼ` along rays, the
  isoquants meet at most once in the interior of `ℝ²₊`; it applies to `cdModel`
  (`exercise_15_D_6c_cdModel`). The graphical construction of the cone is not a claim.
* **Exercise 15.D.6(d)**: outside the diversification cone the equilibrium is specialized in the
  good intensive in the abundant factor, with factor prices `w = (pⱼ/gⱼ(ω))(ω, 1)` where `ω`
  makes good `j`'s cost-minimizing ratio equal to `z̄₁/z̄₂` (sufficiency:
  `TwoByTwo.exercise_15_D_6d_spec0`, `…_spec1`, `…_of_ray`, existence `…_exists`; every
  equilibrium has this form: `…_spec0_unique`, `…_spec1_unique`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas production function
`f(z) = z₁^α z₂^(1-α)` (real powers; `0` on the axes when `0 < α < 1`). -/
noncomputable def cdtF (α : ℝ) (z : Fin 2 → ℝ) : ℝ := z 0 ^ α * z 1 ^ (1 - α)

/-- **Exercise 15.D.8** (MWG, p. 544). The cost-minimizing factor ratio of the Cobb-Douglas
technology, `r(w) = α w₂ / ((1 - α) w₁)`. -/
noncomputable def cdtRatio (α : ℝ) (w : Fin 2 → ℝ) : ℝ := α * w 1 / ((1 - α) * w 0)

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas unit input vector
`a(w) = (r^(1-α), r^(-α))` with `r = r(w)`. -/
noncomputable def cdtA (α : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![cdtRatio α w ^ (1 - α), cdtRatio α w ^ (-α)]

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas unit cost
`c(w) = (w₁/α)^α (w₂/(1-α))^(1-α)`. -/
noncomputable def cdtCost (α : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  (w 0 / α) ^ α * (w 1 / (1 - α)) ^ (1 - α)

variable {α : ℝ}

theorem cdtRatio_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < cdtRatio α w := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  unfold cdtRatio
  positivity

/-- The Cobb-Douglas unit input vector is strictly positive. -/
theorem cdtA_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (l : Fin 2) : 0 < cdtA α w l := by
  have hr := cdtRatio_pos hα0 hα1 hw
  fin_cases l
  · exact Real.rpow_pos_of_pos hr _
  · exact Real.rpow_pos_of_pos hr _

/-- The factor ratio of the Cobb-Douglas unit input vector is `a₁(w)/a₂(w) = r(w)`. -/
theorem cdtA_ratio (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdtA α w 0 / cdtA α w 1 = cdtRatio α w := by
  have hr := cdtRatio_pos hα0 hα1 hw
  simp only [cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Real.rpow_sub hr, show 1 - α - -α = 1 by ring, Real.rpow_one]

/-- `f(a(w)) = 1`: the Cobb-Douglas unit input vector produces one unit. -/
theorem cdtF_cdtA (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdtF α (cdtA α w) = 1 := by
  have hr := cdtRatio_pos hα0 hα1 hw
  simp only [cdtF, cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le, ← Real.rpow_add hr,
    show (1 - α) * α + -α * (1 - α) = 0 by ring, Real.rpow_zero]

/-- The Cobb-Douglas production function is nonnegative on `ℝ²₊`. -/
theorem cdtF_nonneg {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : 0 ≤ cdtF α z :=
  mul_nonneg (Real.rpow_nonneg (hz 0) _) (Real.rpow_nonneg (hz 1) _)

/-- The Cobb-Douglas production function is homogeneous of degree one on `ℝ²₊`. -/
theorem cdtF_smul {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 ≤ t) :
    cdtF α (t • z) = t * cdtF α z := by
  simp only [cdtF, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow ht (hz 0), Real.mul_rpow ht (hz 1)]
  have h : t ^ α * t ^ (1 - α) = t := by
    rw [← Real.rpow_add' ht (by ring_nf; norm_num), show α + (1 - α) = 1 by ring,
      Real.rpow_one]
  calc t ^ α * z 0 ^ α * (t ^ (1 - α) * z 1 ^ (1 - α))
      = (t ^ α * t ^ (1 - α)) * (z 0 ^ α * z 1 ^ (1 - α)) := by ring
    _ = t * (z 0 ^ α * z 1 ^ (1 - α)) := by rw [h]

/-- The unit cost is positive. -/
theorem cdtCost_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < cdtCost α w := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  unfold cdtCost
  positivity

/-- The weighted AM-GM rewriting: `(w₁z₁/α)^α (w₂z₂/(1-α))^(1-α) = c(w) f(z)`. -/
theorem cdt_geom (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) :
    (w 0 / α * z 0) ^ α * (w 1 / (1 - α) * z 1) ^ (1 - α) = cdtCost α w * cdtF α z := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  rw [Real.mul_rpow (by positivity) (hz 0), Real.mul_rpow (by positivity) (hz 1)]
  unfold cdtCost cdtF
  ring

/-- The arithmetic side: `α (w₁z₁/α) + (1-α)(w₂z₂/(1-α)) = w·z`. -/
theorem cdt_arith (hα0 : 0 < α) (hα1 : α < 1) (w z : Fin 2 → ℝ) :
    α * (w 0 / α * z 0) + (1 - α) * (w 1 / (1 - α) * z 1) = w ⬝ᵥ z := by
  have : (1 - α) ≠ 0 := by linarith
  rw [TwoByTwo.dot_two]
  field_simp

/-- **Cost minimization** (weighted AM-GM): `c(w) f(z) ≤ w·z` for `z ∈ ℝ²₊`, `w ≫ 0`. -/
theorem cdtCost_mul_le (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : cdtCost α w * cdtF α z ≤ w ⬝ᵥ z := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  rw [← cdt_geom hα0 hα1 hw hz, ← cdt_arith hα0 hα1 w z]
  exact Real.geom_mean_le_arith_mean2_weighted hα0.le this.le
    (mul_nonneg (by positivity) (hz 0)) (mul_nonneg (by positivity) (hz 1)) (by ring)

/-- At the unit input vector the two AM-GM terms agree: `w₁a₁/α = w₂a₂/(1-α)`. -/
theorem cdtA_balanced (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    w 0 / α * cdtA α w 0 = w 1 / (1 - α) * cdtA α w 1 := by
  have hr := cdtRatio_pos hα0 hα1 hw
  have h0 := hw 0
  have : (1 - α) ≠ 0 := by linarith
  have key : cdtRatio α w ^ (1 - α) = cdtRatio α w * cdtRatio α w ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  simp only [cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key]
  unfold cdtRatio
  field_simp

/-- `w·a(w) = c(w)`: the unit input vector costs exactly the unit cost. -/
theorem cdt_dot_A (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    w ⬝ᵥ cdtA α w = cdtCost α w := by
  have hbal := cdtA_balanced hα0 hα1 hw
  have hg := cdt_geom hα0 hα1 hw (fun l => (cdtA_pos hα0 hα1 hw l).le)
  rw [cdtF_cdtA hα0 hα1 hw, mul_one, ← hbal] at hg
  have hs : 0 < w 0 / α * cdtA α w 0 :=
    mul_pos (div_pos (hw 0) hα0) (cdtA_pos hα0 hα1 hw 0)
  rw [← Real.rpow_add hs, show α + (1 - α) = 1 by ring, Real.rpow_one] at hg
  rw [← cdt_arith hα0 hα1 w, ← hbal, ← hg]
  ring

/-- **Cost minimization**: `w·a(w) ≤ w·z` whenever `f(z) ≥ 1`, `z ∈ ℝ²₊`. -/
theorem cdtA_min (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) (hf : 1 ≤ cdtF α z) :
    w ⬝ᵥ cdtA α w ≤ w ⬝ᵥ z := by
  rw [cdt_dot_A hα0 hα1 hw]
  have hc := cdtCost_pos hα0 hα1 hw
  calc cdtCost α w = cdtCost α w * 1 := (mul_one _).symm
    _ ≤ cdtCost α w * cdtF α z := mul_le_mul_of_nonneg_left hf hc.le
    _ ≤ w ⬝ᵥ z := cdtCost_mul_le hα0 hα1 hw hz

/-- **Uniqueness of the cost minimizer** (equality case of weighted AM-GM). -/
theorem cdtA_unique (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) (hf : 1 ≤ cdtF α z)
    (hle : w ⬝ᵥ z ≤ w ⬝ᵥ cdtA α w) : z = cdtA α w := by
  have h0 := hw 0
  have h1 := hw 1
  have hβ : 0 < 1 - α := by linarith
  have hc := cdtCost_pos hα0 hα1 hw
  rw [cdt_dot_A hα0 hα1 hw] at hle
  have hx : 0 ≤ w 0 / α * z 0 := mul_nonneg (by positivity) (hz 0)
  have hy : 0 ≤ w 1 / (1 - α) * z 1 := mul_nonneg (by positivity) (hz 1)
  have hgm := Real.geom_mean_le_arith_mean2_weighted hα0.le hβ.le hx hy (by ring)
  rw [cdt_geom hα0 hα1 hw hz, cdt_arith hα0 hα1 w z] at hgm
  have hcf : cdtCost α w ≤ cdtCost α w * cdtF α z := by
    calc cdtCost α w = cdtCost α w * 1 := (mul_one _).symm
      _ ≤ cdtCost α w * cdtF α z := mul_le_mul_of_nonneg_left hf hc.le
  have heq : (w 0 / α * z 0) ^ α * (w 1 / (1 - α) * z 1) ^ (1 - α) =
      α * (w 0 / α * z 0) + (1 - α) * (w 1 / (1 - α) * z 1) := by
    rw [cdt_geom hα0 hα1 hw hz, cdt_arith hα0 hα1 w z]
    linarith
  have hxy := (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hα0 hβ hx hy (by ring)).1 heq
  have hsum := cdt_arith hα0 hα1 w z
  rw [← hxy] at hsum
  -- both terms equal the unit cost
  have hxc : w 0 / α * z 0 = cdtCost α w := by
    have : w 0 / α * z 0 = w ⬝ᵥ z := by linarith
    linarith
  have hbal := cdtA_balanced hα0 hα1 hw
  have hdA := cdt_arith hα0 hα1 w (cdtA α w)
  rw [← hbal, cdt_dot_A hα0 hα1 hw] at hdA
  have hxa : w 0 / α * cdtA α w 0 = cdtCost α w := by linarith
  funext l
  fin_cases l
  · have : w 0 / α * z 0 = w 0 / α * cdtA α w 0 := by rw [hxc, hxa]
    exact mul_left_cancel₀ (div_pos h0 hα0).ne' this
  · have : w 1 / (1 - α) * z 1 = w 1 / (1 - α) * cdtA α w 1 := by rw [← hxy, hxc, ← hbal, hxa]
    exact mul_left_cancel₀ (div_pos h1 hβ).ne' this

/-- The Cobb-Douglas unit input vector is continuous in the relative factor price. -/
theorem cdtA_continuousOn (hα0 : 0 < α) (hα1 : α < 1) (l : Fin 2) :
    ContinuousOn (fun t : ℝ => cdtA α ![t, 1] l) (Set.Ioi 0) := by
  have hβ : 0 < 1 - α := by linarith
  have hbase : ContinuousOn (fun t : ℝ => cdtRatio α ![t, 1]) (Set.Ioi 0) := by
    simp only [cdtRatio, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    exact (mul_pos hβ (Set.mem_Ioi.1 ht)).ne'
  have hne : ∀ t ∈ Set.Ioi (0 : ℝ), cdtRatio α ![t, 1] ≠ 0 := fun t ht =>
    (cdtRatio_pos hα0 hα1 (TwoByTwo.relPrice_pos (Set.mem_Ioi.1 ht))).ne'
  fin_cases l
  · exact hbase.rpow_const fun t ht => Or.inl (hne t ht)
  · exact hbase.rpow_const fun t ht => Or.inl (hne t ht)

/-- **Exercise 15.D.8** (MWG, p. 544), general form. The 2 × 2 model with Cobb-Douglas
technologies `fⱼ(z) = z₁^{αⱼ} z₂^{1-αⱼ}`. -/
noncomputable def cdtModel (α : Fin 2 → ℝ) : TwoByTwo where
  f := fun j => cdtF (α j)
  a := fun j => cdtA (α j)

/-- The Cobb-Douglas model with exponents in `(0, 1)` satisfies the standing assumptions of the
2 × 2 model. -/
theorem cdtModel_isModel {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) :
    (cdtModel α).IsModel where
  f_nonneg := fun _ _ hz => cdtF_nonneg hz
  hom := fun _ _ hz _ ht => cdtF_smul hz ht
  a_mem := fun j _ hw =>
    ⟨fun l => (cdtA_pos (hα j).1 (hα j).2 hw l).le, cdtF_cdtA (hα j).1 (hα j).2 hw⟩
  a_min := fun j _ hw _ hz hf => cdtA_min (hα j).1 (hα j).2 hw hz hf
  a_unique := fun j _ hw _ hz hf hle => cdtA_unique (hα j).1 (hα j).2 hw hz hf hle
  a_pos := fun j _ l hw => cdtA_pos (hα j).1 (hα j).2 hw l
  a_cont := fun j l => cdtA_continuousOn (hα j).1 (hα j).2 l

/-- The unit cost of the Cobb-Douglas model is `cⱼ(w) = (w₁/αⱼ)^{αⱼ} (w₂/(1-αⱼ))^{1-αⱼ}`. -/
theorem cdtModel_c {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) (j : Fin 2)
    {w : Fin 2 → ℝ} (hw : StrictlyPositive w) : (cdtModel α).c j w = cdtCost (α j) w :=
  cdt_dot_A (hα j).1 (hα j).2 hw

/-- The factor intensity condition holds in the Cobb-Douglas model when `α₂ < α₁`. -/
theorem cdtModel_factorIntensity {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1)
    (h : α 1 < α 0) : (cdtModel α).FactorIntensity := by
  intro w hw
  change cdtA (α 1) w 0 / cdtA (α 1) w 1 < cdtA (α 0) w 0 / cdtA (α 0) w 1
  rw [cdtA_ratio (hα 1).1 (hα 1).2 hw, cdtA_ratio (hα 0).1 (hα 0).2 hw]
  unfold cdtRatio
  have h0 := hw 0
  have h1 := hw 1
  have hb0 : 0 < 1 - α 0 := by linarith [(hα 0).2]
  have hb1 : 0 < 1 - α 1 := by linarith [(hα 1).2]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos h0 h1) (mul_pos h1 (sub_pos.2 h))]

/-- **Exercise 15.D.8** (MWG, p. 544). The model of the exercise:
`f₁(z) = z₁^{2/3} z₂^{1/3}` and `f₂(z) = z₁^{1/3} z₂^{2/3}`. -/
noncomputable def cdModel : TwoByTwo := cdtModel ![2 / 3, 1 / 3]

theorem cdModel_alpha : ∀ j, 0 < (![2 / 3, 1 / 3] : Fin 2 → ℝ) j ∧
    (![2 / 3, 1 / 3] : Fin 2 → ℝ) j < 1 := by
  intro j
  fin_cases j <;> norm_num

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas model of the exercise satisfies the
standing assumptions of the 2 × 2 model. -/
theorem cdModel_isModel : cdModel.IsModel := cdtModel_isModel cdModel_alpha

/-- **Exercise 15.D.8** (MWG, p. 544). The factor ratios in the exercise's model:
`a₁₁/a₂₁ = 2w₂/w₁` and `a₁₂/a₂₂ = w₂/(2w₁)`. -/
theorem cdModel_ratio {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.a 0 w 0 / cdModel.a 0 w 1 = 2 * w 1 / w 0 ∧
      cdModel.a 1 w 0 / cdModel.a 1 w 1 = w 1 / (2 * w 0) := by
  have h0 := (hw 0).ne'
  constructor
  · change cdtA (2 / 3) w 0 / cdtA (2 / 3) w 1 = _
    rw [cdtA_ratio (by norm_num) (by norm_num) hw]
    unfold cdtRatio
    field_simp
    ring
  · change cdtA (1 / 3) w 0 / cdtA (1 / 3) w 1 = _
    rw [cdtA_ratio (by norm_num) (by norm_num) hw]
    unfold cdtRatio
    field_simp
    ring

/-- **Exercise 15.D.8** (MWG, p. 544). The exercise's model satisfies the factor intensity
condition (good 1 is relatively intensive in factor 1: `2w₂/w₁ > w₂/(2w₁)`). -/
theorem cdModel_factorIntensity : cdModel.FactorIntensity :=
  cdtModel_factorIntensity cdModel_alpha (by norm_num)

namespace TwoByTwo

variable {M : TwoByTwo}

/-! ### Exercise 15.D.6(d): specialization -/

/-- The ratio of unit costs depends only on the relative factor price:
`c₁(w)/c₂(w) = g₁(w₁/w₂)/g₂(w₁/w₂)`. -/
theorem c_ratio_eq_g (hM : M.IsModel) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.c 0 w / M.c 1 w = M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) := by
  rw [c_eq_g hM 0 hw, c_eq_g hM 1 hw, mul_div_mul_left _ _ (hw 1).ne']

/-- Two strictly positive factor price vectors with the same relative price and the same unit
cost of some good are equal. -/
theorem eq_of_relPrice_eq_of_c_eq (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (hr : w 0 / w 1 = w' 0 / w' 1)
    (hc : M.c j w = M.c j w') : w = w' := by
  rw [c_eq_g hM j hw, c_eq_g hM j hw', hr] at hc
  have hg := c_pos hM j (relPrice_pos (div_pos (hw' 0) (hw' 1)))
  have h1 : w 1 = w' 1 := mul_right_cancel₀ hg.ne' hc
  have h0 : w 0 = w' 0 := by
    rw [h1] at hr
    exact (div_left_inj' (hw' 1).ne').1 hr
  funext l
  fin_cases l
  · exact h0
  · exact h1

/-- If good 1 breaks even at `w` and good 2 makes no profit, the relative price of factor 1 is
at most its value `ŵ₁/ŵ₂` at the factor prices `ŵ` solving (15.D.7). -/
theorem relPrice_le_of_spec0 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hw : StrictlyPositive w) (h0 : M.c 0 w = p 0) (h1 : p 1 ≤ M.c 1 w) :
    w 0 / w 1 ≤ what 0 / what 1 := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  rw [← (unitCost_ratio_strictMono hM hFI).le_iff_le hω hωh]
  change M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) ≤ M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1)
  rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, h0]
  have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  exact div_le_div_of_nonneg_left hp0.le hp1 h1

/-- If good 2 breaks even at `w` and good 1 makes no profit, the relative price of factor 1 is
at least `ŵ₁/ŵ₂`. -/
theorem relPrice_ge_of_spec1 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hw : StrictlyPositive w) (h0 : p 0 ≤ M.c 0 w) (h1 : M.c 1 w = p 1) :
    what 0 / what 1 ≤ w 0 / w 1 := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  rw [← (unitCost_ratio_strictMono hM hFI).le_iff_le hωh hω]
  change M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) ≤ M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1)
  rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, h1]
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  exact div_le_div_of_nonneg_right h0 hp1.le

/-- **Exercise 15.D.6(d)** (MWG, p. 543), sufficiency, specialization in good 1. Let `ŵ ≫ 0` solve
(15.D.7), `cⱼ(ŵ) = pⱼ`, and `z̄ ≫ 0`. If `w ≫ 0` has `c₁(w) = p₁`, the factor ratio of good 1 at
`w` equals the endowment ratio, `a₁₁(w)/a₂₁(w) = z̄₁/z̄₂`, and `w₁/w₂ ≤ ŵ₁/ŵ₂`, then the economy
specialized in good 1, `z = (z̄, 0)`, is a factor market equilibrium at `w` (with output
`q₁ = z̄₁/a₁₁(w)`, and `c₂(w) ≥ p₂`). -/
theorem exercise_15_D_6d_spec0 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hw : StrictlyPositive w) (hc0 : M.c 0 w = p 0)
    (hk : M.a 0 w 0 / M.a 0 w 1 = zbar 0 / zbar 1) (hle : w 0 / w 1 ≤ what 0 / what 1) :
    IsFactorEqm M.f p zbar w ![zbar, 0] := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  have a00 := hM.a_pos 0 w 0 hw
  have a01 := hM.a_pos 0 w 1 hw
  have hz0 := hz 0
  have hz1 := hz 1
  -- the second good makes no profit
  have hc1 : p 1 ≤ M.c 1 w := by
    have hmono := ((unitCost_ratio_strictMono hM hFI).le_iff_le hω hωh).2 hle
    change M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) ≤
      M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) at hmono
    rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, hc0] at hmono
    have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
    have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
    exact (div_le_div_iff_of_pos_left hp0 (c_pos hM 1 hw) hp1).1 hmono
  have hzq : zbar = (zbar 0 / M.a 0 w 0) • M.a 0 w := by
    rw [div_eq_div_iff a01.ne' hz1.ne'] at hk
    have e0 : zbar 0 = zbar 0 / M.a 0 w 0 * M.a 0 w 0 := by field_simp
    have e1 : zbar 1 = zbar 0 / M.a 0 w 0 * M.a 0 w 1 := by field_simp; linarith
    funext l
    fin_cases l
    · exact e0
    · exact e1
  rw [exercise_15_D_6a hM]
  refine ⟨hw, ![zbar 0 / M.a 0 w 0, 0], fun j => ?_, fun j => ?_, fun j hj => ?_, fun j => ?_, ?_⟩
  · fin_cases j
    · exact (div_pos hz0 a00).le
    · exact le_rfl
  · fin_cases j
    · exact hc0.ge
    · exact hc1
  · fin_cases j
    · exact hc0.symm
    · exact absurd hj (lt_irrefl 0)
  · fin_cases j
    · exact hzq
    · simp
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero]
    exact hzq.symm

/-- **Exercise 15.D.6(d)** (MWG, p. 543), sufficiency, specialization in good 2: if `c₂(w) = p₂`,
`a₁₂(w)/a₂₂(w) = z̄₁/z̄₂` and `w₁/w₂ ≥ ŵ₁/ŵ₂`, then `z = (0, z̄)` is a factor market equilibrium
at `w`. -/
theorem exercise_15_D_6d_spec1 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hw : StrictlyPositive w) (hc1 : M.c 1 w = p 1)
    (hk : M.a 1 w 0 / M.a 1 w 1 = zbar 0 / zbar 1) (hge : what 0 / what 1 ≤ w 0 / w 1) :
    IsFactorEqm M.f p zbar w ![0, zbar] := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  have a10 := hM.a_pos 1 w 0 hw
  have a11 := hM.a_pos 1 w 1 hw
  have hz0 := hz 0
  have hz1 := hz 1
  have hc0 : p 0 ≤ M.c 0 w := by
    have hmono := ((unitCost_ratio_strictMono hM hFI).le_iff_le hωh hω).2 hge
    change M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) ≤
      M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) at hmono
    rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, hc1] at hmono
    have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
    exact (div_le_div_iff_of_pos_right hp1).1 hmono
  have hzq : zbar = (zbar 0 / M.a 1 w 0) • M.a 1 w := by
    rw [div_eq_div_iff a11.ne' hz1.ne'] at hk
    have e0 : zbar 0 = zbar 0 / M.a 1 w 0 * M.a 1 w 0 := by field_simp
    have e1 : zbar 1 = zbar 0 / M.a 1 w 0 * M.a 1 w 1 := by field_simp; linarith
    funext l
    fin_cases l
    · exact e0
    · exact e1
  rw [exercise_15_D_6a hM]
  refine ⟨hw, ![0, zbar 0 / M.a 1 w 0], fun j => ?_, fun j => ?_, fun j hj => ?_, fun j => ?_, ?_⟩
  · fin_cases j
    · exact le_rfl
    · exact (div_pos hz0 a10).le
  · fin_cases j
    · exact hc0
    · exact hc1.ge
  · fin_cases j
    · exact absurd hj (lt_irrefl 0)
    · exact hc1.symm
  · fin_cases j
    · simp
    · exact hzq
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, zero_add]
    exact hzq.symm

/-- Strictly above the diversification cone, a relative factor price at which good 1's factor
ratio equals the endowment ratio is below `ŵ₁/ŵ₂`. -/
theorem relPrice_lt_of_above_cone (hM : M.IsModel) {w what : Fin 2 → ℝ}
    (hwhat : StrictlyPositive what) (hw : StrictlyPositive w) {ρ : ℝ}
    (hρ : M.a 0 what 0 / M.a 0 what 1 < ρ) (hk : M.a 0 w 0 / M.a 0 w 1 = ρ) :
    w 0 / w 1 < what 0 / what 1 := by
  by_contra h
  rw [not_lt] at h
  have hint := intensity_antitone hM 0 (div_pos (hwhat 0) (hwhat 1)) h
  rw [← a_eq_rel hM 0 hw, ← a_eq_rel hM 0 hwhat] at hint
  linarith

/-- Strictly below the diversification cone, a relative factor price at which good 2's factor
ratio equals the endowment ratio is above `ŵ₁/ŵ₂`. -/
theorem relPrice_gt_of_below_cone (hM : M.IsModel) {w what : Fin 2 → ℝ}
    (hwhat : StrictlyPositive what) (hw : StrictlyPositive w) {ρ : ℝ}
    (hρ : ρ < M.a 1 what 0 / M.a 1 what 1) (hk : M.a 1 w 0 / M.a 1 w 1 = ρ) :
    what 0 / what 1 < w 0 / w 1 := by
  by_contra h
  rw [not_lt] at h
  have hint := intensity_antitone hM 1 (div_pos (hw 0) (hw 1)) h
  rw [← a_eq_rel hM 1 hw, ← a_eq_rel hM 1 hwhat] at hint
  linarith

/-- Ray-surjectivity of good `j`'s technology: every factor ratio `ρ > 0` is the
cost-minimizing ratio `a_{1j}(ω, 1)/a_{2j}(ω, 1)` at some relative factor price `ω > 0`. -/
def RaySurjective (M : TwoByTwo) (j : Fin 2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ ω : ℝ, 0 < ω ∧ M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ

/-- The factor prices of the specialized equilibrium: `(p₁/g₁(ω)) (ω, 1)`; its unit cost of good
1 is `p₁` and its unit input vector of good 1 is `a₁(ω, 1)`. -/
theorem smul_relPrice_facts (hM : M.IsModel) (j : Fin 2) {ω t : ℝ} (hω : 0 < ω) (ht : 0 < t) :
    StrictlyPositive (t • ![ω, 1]) ∧ M.c j (t • ![ω, 1]) = t * M.g j ω ∧
      M.a j (t • ![ω, 1]) = M.a j ![ω, 1] ∧
      (t • ![ω, 1]) 0 / (t • ![ω, 1]) 1 = ω := by
  refine ⟨fun l => ?_, c_smul hM j (relPrice_pos hω) ht, a_smul hM j (relPrice_pos hω) ht, ?_⟩
  · simpa using mul_pos ht (relPrice_pos hω l)
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp

/-- **Exercise 15.D.6(d)** (MWG, p. 543), the factor prices of the economy specialized in good 1.
Strictly above the cone, `z̄₁/z̄₂ > a₁₁(ŵ)/a₂₁(ŵ)`, let `ω > 0` make good 1's factor ratio equal
to `z̄₁/z̄₂`. Then `w = (p₁/g₁(ω)) (ω, 1)` and `z = (z̄, 0)` form a factor market equilibrium. -/
theorem exercise_15_D_6d_spec0_of_ray (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hρ : M.a 0 what 0 / M.a 0 what 1 < zbar 0 / zbar 1)
    {ω : ℝ} (hω : 0 < ω) (hk : M.a 0 ![ω, 1] 0 / M.a 0 ![ω, 1] 1 = zbar 0 / zbar 1) :
    IsFactorEqm M.f p zbar ((p 0 / M.g 0 ω) • ![ω, 1]) ![zbar, 0] := by
  have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
  have hg : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  obtain ⟨hw, hcw, haw, hrw⟩ := smul_relPrice_facts hM 0 hω (div_pos hp0 hg)
  have hk' : M.a 0 ((p 0 / M.g 0 ω) • ![ω, 1]) 0 / M.a 0 ((p 0 / M.g 0 ω) • ![ω, 1]) 1 =
      zbar 0 / zbar 1 := by rw [haw]; exact hk
  refine exercise_15_D_6d_spec0 hM hFI hwhat hc hz hw ?_ hk'
    (relPrice_lt_of_above_cone hM hwhat hw hρ hk').le
  rw [hcw]
  exact div_mul_cancel₀ _ hg.ne'

/-- **Exercise 15.D.6(d)** (MWG, p. 543), the factor prices of the economy specialized in good 2:
strictly below the cone, with `ω > 0` making good 2's factor ratio equal to `z̄₁/z̄₂`,
`w = (p₂/g₂(ω)) (ω, 1)` and `z = (0, z̄)` form a factor market equilibrium. -/
theorem exercise_15_D_6d_spec1_of_ray (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hρ : zbar 0 / zbar 1 < M.a 1 what 0 / M.a 1 what 1)
    {ω : ℝ} (hω : 0 < ω) (hk : M.a 1 ![ω, 1] 0 / M.a 1 ![ω, 1] 1 = zbar 0 / zbar 1) :
    IsFactorEqm M.f p zbar ((p 1 / M.g 1 ω) • ![ω, 1]) ![0, zbar] := by
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  have hg : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  obtain ⟨hw, hcw, haw, hrw⟩ := smul_relPrice_facts hM 1 hω (div_pos hp1 hg)
  have hk' : M.a 1 ((p 1 / M.g 1 ω) • ![ω, 1]) 0 / M.a 1 ((p 1 / M.g 1 ω) • ![ω, 1]) 1 =
      zbar 0 / zbar 1 := by rw [haw]; exact hk
  refine exercise_15_D_6d_spec1 hM hFI hwhat hc hz hw ?_ hk'
    (relPrice_gt_of_below_cone hM hwhat hw hρ hk').le
  rw [hcw]
  exact div_mul_cancel₀ _ hg.ne'

/-- **Exercise 15.D.6(d)** (MWG, p. 543), existence. With ray-surjectivity of good 1's technology,
for every endowment `z̄ ≫ 0` on or above the diversification cone there is an equilibrium
specialized in good 1. -/
theorem exercise_15_D_6d_spec0_exists (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : M.RaySurjective 0) {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : M.a 0 what 0 / M.a 0 what 1 ≤ zbar 0 / zbar 1) :
    ∃ w, IsFactorEqm M.f p zbar w ![zbar, 0] := by
  rcases eq_or_lt_of_le hρ with h | h
  · exact ⟨what, exercise_15_D_6d_spec0 hM hFI hwhat hc hz hwhat (hc 0) h le_rfl⟩
  · obtain ⟨ω, hω, hk⟩ := hs _ (div_pos (hz 0) (hz 1))
    exact ⟨_, exercise_15_D_6d_spec0_of_ray hM hFI hwhat hc hz h hω hk⟩

/-- **Exercise 15.D.6(d)** (MWG, p. 543), existence: with ray-surjectivity of good 2's technology,
for every `z̄ ≫ 0` on or below the cone there is an equilibrium specialized in good 2. -/
theorem exercise_15_D_6d_spec1_exists (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : M.RaySurjective 1) {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : zbar 0 / zbar 1 ≤ M.a 1 what 0 / M.a 1 what 1) :
    ∃ w, IsFactorEqm M.f p zbar w ![0, zbar] := by
  rcases eq_or_lt_of_le hρ with h | h
  · exact ⟨what, exercise_15_D_6d_spec1 hM hFI hwhat hc hz hwhat (hc 1) h.symm le_rfl⟩
  · obtain ⟨ω, hω, hk⟩ := hs _ (div_pos (hz 0) (hz 1))
    exact ⟨_, exercise_15_D_6d_spec1_of_ray hM hFI hwhat hc hz h hω hk⟩

/-- **Exercise 15.D.6(d)** (MWG, p. 543), uniqueness. If `z̄ ≫ 0` lies on or above the
diversification cone, `z̄₁/z̄₂ ≥ a₁₁(ŵ)/a₂₁(ŵ)`, then every factor market equilibrium is
specialized in good 1, `z = (z̄, 0)`, with `c₁(w) = p₁` and good 1's factor ratio at `w` equal to
the endowment ratio (which, with `c₁(w) = p₁`, pins down `w` when that ratio determines the
relative factor price). -/
theorem exercise_15_D_6d_spec0_unique (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : M.a 0 what 0 / M.a 0 what 1 ≤ zbar 0 / zbar 1) (h : IsFactorEqm M.f p zbar w z) :
    z = ![zbar, 0] ∧ M.c 0 w = p 0 ∧ M.a 0 w 0 / M.a 0 w 1 = zbar 0 / zbar 1 := by
  obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hnot : ¬ ∀ j, 0 < q j := fun hall => by
    have := (exercise_15_D_6b hM hFI hwhat hc hz hq hpc hqp hw hsum).1 hall
    linarith [this.2]
  have hs0 := congrFun hsum 0
  have hs1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs0 hs1
  have hz0 := hz 0
  have hz1 := hz 1
  rcases eq_or_lt_of_le (hq 0) with hq0 | hq0
  · -- specialization in good 2 is impossible above the cone
    exfalso
    rw [← hq0, zero_mul, zero_add] at hs0 hs1
    have hq1 : 0 < q 1 := by
      rcases eq_or_lt_of_le (hq 1) with h1 | h1
      · rw [← h1, zero_mul] at hs0
        linarith
      · exact h1
    have hge := relPrice_ge_of_spec1 hM hFI hwhat hc hw (hpc 0) (hqp 1 hq1).symm
    have hint := intensity_antitone hM 1 (div_pos (hwhat 0) (hwhat 1)) hge
    rw [← a_eq_rel hM 1 hw, ← a_eq_rel hM 1 hwhat] at hint
    have hk : zbar 0 / zbar 1 = M.a 1 w 0 / M.a 1 w 1 := by
      rw [← hs0, ← hs1, mul_div_mul_left _ _ hq1.ne']
    have := hFI what hwhat
    linarith
  · have hq1 : q 1 = 0 := by
      by_contra h1
      exact hnot fun j => by
        fin_cases j
        · exact hq0
        · exact lt_of_le_of_ne (hq 1) (Ne.symm h1)
    rw [hq1, zero_mul, add_zero] at hs0 hs1
    have hsum' := hsum
    rw [Fin.sum_univ_two, hq1, zero_smul, add_zero] at hsum'
    have e0 : z 0 = zbar := (hzq 0).trans hsum'
    have e1 : z 1 = 0 := by rw [hzq 1, hq1, zero_smul]
    refine ⟨?_, (hqp 0 hq0).symm, ?_⟩
    · funext j
      fin_cases j
      · exact e0
      · exact e1
    · rw [← hs0, ← hs1, mul_div_mul_left _ _ hq0.ne']

/-- **Exercise 15.D.6(d)** (MWG, p. 543), uniqueness below the cone: if
`z̄₁/z̄₂ ≤ a₁₂(ŵ)/a₂₂(ŵ)`, every equilibrium is specialized in good 2, `z = (0, z̄)`, with
`c₂(w) = p₂` and good 2's factor ratio at `w` equal to the endowment ratio. -/
theorem exercise_15_D_6d_spec1_unique (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : zbar 0 / zbar 1 ≤ M.a 1 what 0 / M.a 1 what 1) (h : IsFactorEqm M.f p zbar w z) :
    z = ![0, zbar] ∧ M.c 1 w = p 1 ∧ M.a 1 w 0 / M.a 1 w 1 = zbar 0 / zbar 1 := by
  obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hnot : ¬ ∀ j, 0 < q j := fun hall => by
    have := (exercise_15_D_6b hM hFI hwhat hc hz hq hpc hqp hw hsum).1 hall
    linarith [this.1]
  have hs0 := congrFun hsum 0
  have hs1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs0 hs1
  have hz0 := hz 0
  have hz1 := hz 1
  rcases eq_or_lt_of_le (hq 1) with hq1 | hq1
  · exfalso
    rw [← hq1, zero_mul, add_zero] at hs0 hs1
    have hq0 : 0 < q 0 := by
      rcases eq_or_lt_of_le (hq 0) with h0 | h0
      · rw [← h0, zero_mul] at hs0
        linarith
      · exact h0
    have hle := relPrice_le_of_spec0 hM hFI hwhat hc hw (hqp 0 hq0).symm (hpc 1)
    have hint := intensity_antitone hM 0 (div_pos (hw 0) (hw 1)) hle
    rw [← a_eq_rel hM 0 hw, ← a_eq_rel hM 0 hwhat] at hint
    have hk : zbar 0 / zbar 1 = M.a 0 w 0 / M.a 0 w 1 := by
      rw [← hs0, ← hs1, mul_div_mul_left _ _ hq0.ne']
    have := hFI what hwhat
    linarith
  · have hq0 : q 0 = 0 := by
      by_contra h0
      exact hnot fun j => by
        fin_cases j
        · exact lt_of_le_of_ne (hq 0) (Ne.symm h0)
        · exact hq1
    rw [hq0, zero_mul, zero_add] at hs0 hs1
    have hsum' := hsum
    rw [Fin.sum_univ_two, hq0, zero_smul, zero_add] at hsum'
    have e0 : z 0 = 0 := by rw [hzq 0, hq0, zero_smul]
    have e1 : z 1 = zbar := (hzq 1).trans hsum'
    refine ⟨?_, (hqp 1 hq1).symm, ?_⟩
    · funext j
      fin_cases j
      · exact e0
      · exact e1
    · rw [← hs0, ← hs1, mul_div_mul_left _ _ hq1.ne']

/-! ### Exercise 15.D.6(c): unit-dollar isoquants -/

/-- **Exercise 15.D.6(c)** (MWG, p. 543). The unit-dollar isoquant of good `j`: the factor
combinations `z ∈ ℝ²₊` producing one dollar's worth of good `j`, `pⱼ fⱼ(z) = 1`. -/
def unitDollarIsoquant (M : TwoByTwo) (p : Fin 2 → ℝ) (j : Fin 2) : Set (Fin 2 → ℝ) :=
  {z | z ∈ nonnegOrthant 2 ∧ p j * M.f j z = 1}

/-- Differentiability of good `j`'s production function along the ray `t ↦ fⱼ(t, 1)`, `t > 0`. -/
def RayDifferentiable (M : TwoByTwo) (j : Fin 2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → DifferentiableAt ℝ (fun t : ℝ => M.f j ![t, 1]) ρ

/-- Duality between production and unit cost: `fⱼ(z) cⱼ(w) ≤ w·z` for `z ∈ ℝ²₊`, `w ≫ 0`. -/
theorem f_mul_c_le (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : M.f j z * M.c j w ≤ w ⬝ᵥ z := by
  have hs := hM.f_nonneg j z hz
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, zero_mul]
    exact dotProduct_nonneg_of_nonneg (fun l => (hw l).le) hz
  · have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hs) (hz l)
    have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
      rw [hM.hom j z hz _ (inv_nonneg.2 hs), inv_mul_cancel₀ h.ne']
    have := hM.a_min j w hw _ hz' hf1
    rw [dotProduct_smul, smul_eq_mul] at this
    unfold c
    have := mul_le_mul_of_nonneg_left this hs
    rwa [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at this

/-- Homogeneity along rays: `fⱼ(z) = z₂ fⱼ(z₁/z₂, 1)` for `z ≫ 0`. -/
theorem f_eq_ray (hM : M.IsModel) (j : Fin 2) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    M.f j z = z 1 * M.f j ![z 0 / z 1, 1] := by
  have h1 := hz 1
  have e : z = z 1 • ![z 0 / z 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  conv_lhs => rw [e]
  exact hM.hom j _ (fun l => (relPrice_pos (div_pos (hz 0) h1) l).le) _ h1.le

/-- Along the ray of good `j`'s cost-minimizing factor ratio `ρ = a_{1j}(ω, 1)/a_{2j}(ω, 1)`:
`fⱼ(ρ, 1) a_{2j}(ω, 1) = 1`. -/
theorem rayF_mul_a (hM : M.IsModel) (j : Fin 2) {ω ρ : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ) : M.f j ![ρ, 1] * M.a j ![ω, 1] 1 = 1 := by
  have hp := relPrice_pos hω
  have a0 := hM.a_pos j _ 0 hp
  have a1 := hM.a_pos j _ 1 hp
  have hρ : 0 < ρ := hk ▸ div_pos a0 a1
  have e : M.a j ![ω, 1] = M.a j ![ω, 1] 1 • ![ρ, 1] := by
    rw [← hk]
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  have h1 := (hM.a_mem j _ hp).2
  rw [e, hM.hom j _ (fun l => (relPrice_pos hρ l).le) _ a1.le] at h1
  linarith

/-- The line `(ωt + 1)/gⱼ(ω)` lies above `t ↦ fⱼ(t, 1)` on `t ≥ 0`:
`fⱼ(t, 1) gⱼ(ω) ≤ ωt + 1`. -/
theorem rayF_mul_g_le (hM : M.IsModel) (j : Fin 2) {ω t : ℝ} (hω : 0 < ω) (ht : 0 ≤ t) :
    M.f j ![t, 1] * M.g j ω ≤ ω * t + 1 := by
  have hz : (![t, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · exact ht
    · exact zero_le_one
  have := f_mul_c_le hM j (relPrice_pos hω) hz
  simpa [g, dot_two] using this

/-- ... with equality at the cost-minimizing ratio: `fⱼ(ρ, 1) gⱼ(ω) = ωρ + 1`. -/
theorem rayF_mul_g_eq (hM : M.IsModel) (j : Fin 2) {ω ρ : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ) : M.f j ![ρ, 1] * M.g j ω = ω * ρ + 1 := by
  have hp := relPrice_pos hω
  have a1 := hM.a_pos j _ 1 hp
  have hF := rayF_mul_a hM j hω hk
  have ha0 : M.a j ![ω, 1] 0 = ρ * M.a j ![ω, 1] 1 := by
    rw [← hk]; field_simp
  rw [g_eq, ha0]
  linear_combination (ω * ρ + 1) * hF

/-- With ray-surjectivity, `fⱼ(ρ, 1) > 0` for every `ρ > 0`. -/
theorem rayF_pos (hM : M.IsModel) {j : Fin 2} (hs : M.RaySurjective j) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < M.f j ![ρ, 1] := by
  obtain ⟨ω, hω, hk⟩ := hs ρ hρ
  have hF := rayF_mul_a hM j hω hk
  have a1 := hM.a_pos j _ 1 (relPrice_pos hω)
  by_contra h
  rw [not_lt] at h
  nlinarith

/-- The slope of the isoquant along the ray: if `fⱼ(·, 1)` has derivative `F'` at the
cost-minimizing ratio `ρ` of the relative factor price `ω`, then `F' = ω/gⱼ(ω)` (the line of
`rayF_mul_g_le` touches the graph at `ρ`, so the difference has a local maximum there). -/
theorem rayF_deriv_eq (hM : M.IsModel) (j : Fin 2) {ω ρ F' : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ)
    (hd : HasDerivAt (fun t : ℝ => M.f j ![t, 1]) F' ρ) : F' = ω / M.g j ω := by
  have hp := relPrice_pos hω
  have hg : 0 < M.g j ω := c_pos hM j hp
  have hρ : 0 < ρ := hk ▸ div_pos (hM.a_pos j _ 0 hp) (hM.a_pos j _ 1 hp)
  have hder : HasDerivAt (fun t : ℝ => M.f j ![t, 1] - (ω * t + 1) / M.g j ω)
      (F' - ω * 1 / M.g j ω) ρ :=
    hd.sub ((((hasDerivAt_id ρ).const_mul ω).add_const 1).div_const (M.g j ω))
  have hmax : IsLocalMax (fun t : ℝ => M.f j ![t, 1] - (ω * t + 1) / M.g j ω) ρ := by
    filter_upwards [Ioi_mem_nhds hρ] with t ht
    have h1 := rayF_mul_g_le hM j hω (Set.mem_Ioi.1 ht).le
    have h2 := rayF_mul_g_eq hM j hω hk
    have e1 : M.f j ![t, 1] ≤ (ω * t + 1) / M.g j ω := by rw [le_div_iff₀ hg]; exact h1
    have e2 : M.f j ![ρ, 1] = (ω * ρ + 1) / M.g j ω := by rw [eq_div_iff hg.ne']; exact h2
    linarith
  have := hmax.hasDerivAt_eq_zero hder
  rw [mul_one] at this
  linarith

/-- Under factor intensity, at a common ratio `ρ` the relative factor price making `ρ`
cost-minimizing for good 1 exceeds the one for good 2. -/
theorem rayPrice_lt (hM : M.IsModel) (hFI : M.FactorIntensity) {ω₀ ω₁ ρ : ℝ} (hω₀ : 0 < ω₀)
    (hω₁ : 0 < ω₁) (hk₀ : M.a 0 ![ω₀, 1] 0 / M.a 0 ![ω₀, 1] 1 = ρ)
    (hk₁ : M.a 1 ![ω₁, 1] 0 / M.a 1 ![ω₁, 1] 1 = ρ) : ω₁ < ω₀ := by
  by_contra h
  rw [not_lt] at h
  have h1 := intensity_antitone hM 0 hω₀ h
  have h2 := hFI _ (relPrice_pos hω₁)
  linarith

/-- **Exercise 15.D.6(c)** (MWG, p. 543), key step. Under factor intensity, ray-surjectivity and
ray-differentiability, `ρ ↦ f₁(ρ, 1)/f₂(ρ, 1)` is strictly increasing on `(0, ∞)`: its derivative
is `F₁F₂ (ω₁/(ω₁ρ+1) - ω₂/(ω₂ρ+1))/F₂² > 0` because `ω₁(ρ) > ω₂(ρ)`. -/
theorem rayF_ratio_strictMono (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : ∀ j, M.RaySurjective j) (hd : ∀ j, M.RayDifferentiable j) :
    StrictMonoOn (fun t => M.f 0 ![t, 1] / M.f 1 ![t, 1]) (Set.Ioi 0) := by
  have hder : ∀ ρ ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => M.f 0 ![t, 1] / M.f 1 ![t, 1])
      ((deriv (fun t : ℝ => M.f 0 ![t, 1]) ρ * M.f 1 ![ρ, 1] -
        M.f 0 ![ρ, 1] * deriv (fun t : ℝ => M.f 1 ![t, 1]) ρ) / M.f 1 ![ρ, 1] ^ 2) ρ :=
    fun ρ hρ => ((hd 0 ρ hρ).hasDerivAt).div ((hd 1 ρ hρ).hasDerivAt)
      (rayF_pos hM (hs 1) hρ).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun ρ hρ => (hder ρ hρ).continuousAt.continuousWithinAt) fun ρ hρ => ?_
  rw [interior_Ioi] at hρ
  rw [(hder ρ hρ).deriv]
  apply div_pos _ (pow_pos (rayF_pos hM (hs 1) hρ) 2)
  obtain ⟨ω₀, hω₀, hk₀⟩ := hs 0 ρ hρ
  obtain ⟨ω₁, hω₁, hk₁⟩ := hs 1 ρ hρ
  have hρ' : 0 < ρ := hρ
  have d0 := rayF_deriv_eq hM 0 hω₀ hk₀ (hd 0 ρ hρ).hasDerivAt
  have d1 := rayF_deriv_eq hM 1 hω₁ hk₁ (hd 1 ρ hρ).hasDerivAt
  have F0 := rayF_mul_g_eq hM 0 hω₀ hk₀
  have F1 := rayF_mul_g_eq hM 1 hω₁ hk₁
  have hg0 : 0 < M.g 0 ω₀ := c_pos hM 0 (relPrice_pos hω₀)
  have hg1 : 0 < M.g 1 ω₁ := c_pos hM 1 (relPrice_pos hω₁)
  have hlt := rayPrice_lt hM hFI hω₀ hω₁ hk₀ hk₁
  rw [d0, d1]
  rw [eq_comm, ← div_eq_iff hg0.ne'] at F0
  rw [eq_comm, ← div_eq_iff hg1.ne'] at F1
  rw [← F0, ← F1]
  have : ω₀ / M.g 0 ω₀ * ((ω₁ * ρ + 1) / M.g 1 ω₁) -
      (ω₀ * ρ + 1) / M.g 0 ω₀ * (ω₁ / M.g 1 ω₁) = (ω₀ - ω₁) / (M.g 0 ω₀ * M.g 1 ω₁) := by
    field_simp
    ring
  rw [this]
  exact div_pos (sub_pos.2 hlt) (mul_pos hg0 hg1)

/-- **Exercise 15.D.6(c)** (MWG, p. 543), corrected. Under factor intensity, and if every factor
ratio `ρ > 0` is cost-minimizing for each good at some relative factor price (ray-surjectivity)
and each `fⱼ(·, 1)` is differentiable on `(0, ∞)`, the unit-dollar isoquants of the two goods
intersect at most once in the interior of `ℝ²₊`. -/
theorem exercise_15_D_6c (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : ∀ j, M.RaySurjective j) (hd : ∀ j, M.RayDifferentiable j) {p z z' : Fin 2 → ℝ}
    (hz : StrictlyPositive z) (hz' : StrictlyPositive z')
    (h0 : z ∈ M.unitDollarIsoquant p 0) (h1 : z ∈ M.unitDollarIsoquant p 1)
    (h0' : z' ∈ M.unitDollarIsoquant p 0) (h1' : z' ∈ M.unitDollarIsoquant p 1) : z = z' := by
  have hρ := div_pos (hz 0) (hz 1)
  have hρ' := div_pos (hz' 0) (hz' 1)
  have e0 := h0.2
  have e1 := h1.2
  have e0' := h0'.2
  have e1' := h1'.2
  rw [f_eq_ray hM 0 hz] at e0
  rw [f_eq_ray hM 1 hz] at e1
  rw [f_eq_ray hM 0 hz'] at e0'
  rw [f_eq_ray hM 1 hz'] at e1'
  have hF1 := rayF_pos hM (hs 1) hρ
  have hF1' := rayF_pos hM (hs 1) hρ'
  have hp0 : p 0 ≠ 0 := by rintro h; rw [h, zero_mul] at e0; exact zero_ne_one e0
  -- the ratio `F₁/F₂` equals `p₂/p₁` on both rays
  have hr : M.f 0 ![z 0 / z 1, 1] / M.f 1 ![z 0 / z 1, 1] = p 1 / p 0 := by
    rw [div_eq_div_iff hF1.ne' hp0]
    have := hz 1
    have : z 1 * (M.f 0 ![z 0 / z 1, 1] * p 0 - p 1 * M.f 1 ![z 0 / z 1, 1]) = 0 := by
      linear_combination e0 - e1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hr' : M.f 0 ![z' 0 / z' 1, 1] / M.f 1 ![z' 0 / z' 1, 1] = p 1 / p 0 := by
    rw [div_eq_div_iff hF1'.ne' hp0]
    have := hz' 1
    have : z' 1 * (M.f 0 ![z' 0 / z' 1, 1] * p 0 - p 1 * M.f 1 ![z' 0 / z' 1, 1]) = 0 := by
      linear_combination e0' - e1'
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hρeq : z 0 / z 1 = z' 0 / z' 1 :=
    (rayF_ratio_strictMono hM hFI hs hd).injOn hρ hρ' (hr.trans hr'.symm)
  rw [← hρeq] at e0'
  have hz1 : z 1 = z' 1 := by
    have hne : p 0 * M.f 0 ![z 0 / z 1, 1] ≠ 0 := by
      intro h
      have : p 0 * (z 1 * M.f 0 ![z 0 / z 1, 1]) = z 1 * (p 0 * M.f 0 ![z 0 / z 1, 1]) := by ring
      rw [this, h, mul_zero] at e0
      exact zero_ne_one e0
    have : (p 0 * M.f 0 ![z 0 / z 1, 1]) * z 1 = (p 0 * M.f 0 ![z 0 / z 1, 1]) * z' 1 := by
      linear_combination e0 - e0'
    exact mul_left_cancel₀ hne this
  have hz0 : z 0 = z' 0 := by
    rw [hz1] at hρeq
    exact (div_left_inj' (hz' 1).ne').1 hρeq
  funext l
  fin_cases l
  · exact hz0
  · exact hz1

end TwoByTwo

/-- **Exercise 15.D.6(c)** (MWG, p. 543), as printed, is false for the 2 × 2 model as formalized
(`TwoByTwo.IsModel` with factor intensity): in the Leontief model at prices `p = (1, 2)` both
unit-dollar isoquants contain the distinct points `(2, 1)` and `(3, 1)`. -/
theorem exercise_15_D_6c_counterexample :
    leontiefModel.IsModel ∧ leontiefModel.FactorIntensity ∧
      (![2, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 0 ∧
      (![2, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 1 ∧
      (![3, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 0 ∧
      (![3, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 1 ∧
      StrictlyPositive (![2, 1] : Fin 2 → ℝ) ∧ StrictlyPositive (![3, 1] : Fin 2 → ℝ) ∧
      (![2, 1] : Fin 2 → ℝ) ≠ ![3, 1] := by
  refine ⟨leontiefModel_isModel, leontiefModel_factorIntensity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · intro l; fin_cases l <;> norm_num
  · intro l; fin_cases l <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The Cobb-Douglas model satisfies ray-surjectivity: the cost-minimizing ratio
`αⱼ/((1-αⱼ)ω)` takes every value `ρ > 0` (at `ω = αⱼ/((1-αⱼ)ρ)`). -/
theorem cdtModel_raySurjective {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) (j : Fin 2) :
    (cdtModel α).RaySurjective j := by
  intro ρ hρ
  have ha := (hα j).1
  have hb : 0 < 1 - α j := by linarith [(hα j).2]
  refine ⟨α j / ((1 - α j) * ρ), by positivity, ?_⟩
  change cdtA (α j) _ 0 / cdtA (α j) _ 1 = ρ
  rw [cdtA_ratio (hα j).1 (hα j).2 (TwoByTwo.relPrice_pos (by positivity))]
  simp only [cdtRatio, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-- The Cobb-Douglas model is differentiable along rays: `fⱼ(t, 1) = t^{αⱼ}`. -/
theorem cdtModel_rayDifferentiable (α : Fin 2 → ℝ) (j : Fin 2) :
    (cdtModel α).RayDifferentiable j := by
  intro ρ hρ
  have e : (fun t : ℝ => (cdtModel α).f j ![t, 1]) = fun t => t ^ (α j) := by
    funext t
    simp [cdtModel, cdtF]
  rw [e]
  exact (Real.hasDerivAt_rpow_const (Or.inl hρ.ne')).differentiableAt

/-- **Exercise 15.D.6(c)** (MWG, p. 543), non-vacuity of the corrected statement: in the
Cobb-Douglas model of Exercise 15.D.8 the unit-dollar isoquants of the two goods intersect at
most once in the interior of `ℝ²₊`, at any output prices. -/
theorem exercise_15_D_6c_cdModel {p z z' : Fin 2 → ℝ} (hz : StrictlyPositive z)
    (hz' : StrictlyPositive z') (h0 : z ∈ cdModel.unitDollarIsoquant p 0)
    (h1 : z ∈ cdModel.unitDollarIsoquant p 1) (h0' : z' ∈ cdModel.unitDollarIsoquant p 0)
    (h1' : z' ∈ cdModel.unitDollarIsoquant p 1) : z = z' :=
  TwoByTwo.exercise_15_D_6c cdModel_isModel cdModel_factorIntensity
    (cdtModel_raySurjective cdModel_alpha) (cdtModel_rayDifferentiable _) hz hz' h0 h1 h0' h1'

/-! ### Exercise 15.D.8: the equilibria of the Cobb-Douglas model at `p = (1, 1)` -/

/-- Exponent bookkeeping: `(x^a)^b (x^c)^d = 1` when `ab + cd = 0`, `x > 0`. -/
theorem cd8_rpow_pair {x a b c d : ℝ} (hx : 0 < x) (h : a * b + c * d = 0) :
    (x ^ a) ^ b * (x ^ c) ^ d = 1 := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx, h, Real.rpow_zero]

/-- The unit cost of good 1 in Exercise 15.D.8: `c₁(w) = (3w₁/2)^{2/3} (3w₂)^{1/3}`. -/
theorem cd8_c0 {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.c 0 w = (w 0 / (2 / 3)) ^ ((2 : ℝ) / 3) * (w 1 / (1 / 3)) ^ ((1 : ℝ) / 3) := by
  change (cdtModel ![2 / 3, 1 / 3]).c 0 w = _
  rw [cdtModel_c cdModel_alpha 0 hw]
  simp only [cdtCost, Matrix.cons_val_zero]
  norm_num

/-- The unit cost of good 2 in Exercise 15.D.8: `c₂(w) = (3w₁)^{1/3} (3w₂/2)^{2/3}`. -/
theorem cd8_c1 {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.c 1 w = (w 0 / (1 / 3)) ^ ((1 : ℝ) / 3) * (w 1 / (2 / 3)) ^ ((2 : ℝ) / 3) := by
  change (cdtModel ![2 / 3, 1 / 3]).c 1 w = _
  rw [cdtModel_c cdModel_alpha 1 hw]
  simp only [cdtCost, Matrix.cons_val_one, Matrix.cons_val_zero]
  norm_num

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices solving (15.D.7) at `p = (1, 1)`:
`ŵ = (2^{2/3}/3) (1, 1)`. -/
noncomputable def cd8What : Fin 2 → ℝ := ![(2 : ℝ) ^ ((2 : ℝ) / 3) / 3, (2 : ℝ) ^ ((2 : ℝ) / 3) / 3]

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices when the economy specializes in good 1
(`ρ = z̄₁/z̄₂ ≥ 2`): `w = ∇f₁(z̄) = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`. -/
noncomputable def cd8WSpec0 (ρ : ℝ) : Fin 2 → ℝ :=
  ![2 / 3 * ρ ^ (-(1 : ℝ) / 3), 1 / 3 * ρ ^ ((2 : ℝ) / 3)]

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices when the economy specializes in good 2
(`ρ = z̄₁/z̄₂ ≤ 1/2`): `w = ∇f₂(z̄) = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`. -/
noncomputable def cd8WSpec1 (ρ : ℝ) : Fin 2 → ℝ :=
  ![1 / 3 * ρ ^ (-(2 : ℝ) / 3), 2 / 3 * ρ ^ ((1 : ℝ) / 3)]

/-- **Exercise 15.D.8** (MWG, p. 544). The diversified factor allocation:
`z₁ = ((2z̄₁ - z̄₂)/3) (2, 1)` and `z₂ = ((2z̄₂ - z̄₁)/3) (1, 2)`. -/
noncomputable def cd8ZDiv (zbar : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![((2 * zbar 0 - zbar 1) / 3) • ![2, 1], ((2 * zbar 1 - zbar 0) / 3) • ![1, 2]]

theorem cd8What_pos : StrictlyPositive cd8What := fun l => by
  have : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos two_pos _
  fin_cases l <;> simp [cd8What, this]

/-- At `ŵ` both unit costs equal the output prices `p = (1, 1)`. -/
theorem cd8What_c : ∀ j, cdModel.c j cd8What = (![1, 1] : Fin 2 → ℝ) j := by
  have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 / (2 / 3) = (2 : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [show -(1 : ℝ) / 3 = 2 / 3 - 1 by norm_num, Real.rpow_sub_one two_ne_zero]
    ring
  have h3 : (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 / (1 / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by ring
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [cd8_c0 cd8What_pos]
    simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h2, h3]
    exact cd8_rpow_pair two_pos (by norm_num)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [cd8_c1 cd8What_pos]
    simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h2, h3]
    exact cd8_rpow_pair two_pos (by norm_num)

/-- The diversification cone at `ŵ` is `1/2 < z̄₁/z̄₂ < 2`. -/
theorem cd8What_ratio : cdModel.a 0 cd8What 0 / cdModel.a 0 cd8What 1 = 2 ∧
    cdModel.a 1 cd8What 0 / cdModel.a 1 cd8What 1 = 1 / 2 := by
  obtain ⟨h0, h1⟩ := cdModel_ratio cd8What_pos
  have hs : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 := by positivity
  rw [h0, h1]
  simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · field_simp
  · field_simp

theorem cd8WSpec0_pos {ρ : ℝ} (hρ : 0 < ρ) : StrictlyPositive (cd8WSpec0 ρ) := fun l => by
  have h1 : 0 < ρ ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  have h2 : 0 < ρ ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  fin_cases l
  · simp only [cd8WSpec0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
  · simp only [cd8WSpec0, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    positivity

theorem cd8WSpec1_pos {ρ : ℝ} (hρ : 0 < ρ) : StrictlyPositive (cd8WSpec1 ρ) := fun l => by
  have h1 : 0 < ρ ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  have h2 : 0 < ρ ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  fin_cases l
  · simp only [cd8WSpec1, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
  · simp only [cd8WSpec1, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    positivity

/-- At `w = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`, `c₁(w) = 1`. -/
theorem cd8WSpec0_c0 {ρ : ℝ} (hρ : 0 < ρ) : cdModel.c 0 (cd8WSpec0 ρ) = 1 := by
  rw [cd8_c0 (cd8WSpec0_pos hρ)]
  simp only [cd8WSpec0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show 2 / 3 * ρ ^ (-(1 : ℝ) / 3) / (2 / 3) = ρ ^ (-(1 : ℝ) / 3) by ring,
    show 1 / 3 * ρ ^ ((2 : ℝ) / 3) / (1 / 3) = ρ ^ ((2 : ℝ) / 3) by ring]
  exact cd8_rpow_pair hρ (by norm_num)

/-- At `w = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`, `c₂(w) = 1`. -/
theorem cd8WSpec1_c1 {ρ : ℝ} (hρ : 0 < ρ) : cdModel.c 1 (cd8WSpec1 ρ) = 1 := by
  rw [cd8_c1 (cd8WSpec1_pos hρ)]
  simp only [cd8WSpec1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show 1 / 3 * ρ ^ (-(2 : ℝ) / 3) / (1 / 3) = ρ ^ (-(2 : ℝ) / 3) by ring,
    show 2 / 3 * ρ ^ ((1 : ℝ) / 3) / (2 / 3) = ρ ^ ((1 : ℝ) / 3) by ring]
  exact cd8_rpow_pair hρ (by norm_num)

/-- The relative factor price of the good-1 specialization prices is `2/ρ`. -/
theorem cd8WSpec0_rel {ρ : ℝ} (hρ : 0 < ρ) : cd8WSpec0 ρ 0 / cd8WSpec0 ρ 1 = 2 / ρ := by
  have h : ρ ^ ((2 : ℝ) / 3) = ρ * ρ ^ (-(1 : ℝ) / 3) := by
    rw [show (2 : ℝ) / 3 = 1 + -(1 : ℝ) / 3 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h1 : 0 < ρ ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  simp only [cd8WSpec0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  field_simp

/-- The relative factor price of the good-2 specialization prices is `1/(2ρ)`. -/
theorem cd8WSpec1_rel {ρ : ℝ} (hρ : 0 < ρ) : cd8WSpec1 ρ 0 / cd8WSpec1 ρ 1 = 1 / (2 * ρ) := by
  have h : ρ ^ ((1 : ℝ) / 3) = ρ * ρ ^ (-(2 : ℝ) / 3) := by
    rw [show (1 : ℝ) / 3 = 1 + -(2 : ℝ) / 3 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h1 : 0 < ρ ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  simp only [cd8WSpec1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  field_simp

/-- **Exercise 15.D.8** (MWG, p. 544), diversified region. For `z̄ ≫ 0` with
`1/2 < z̄₁/z̄₂ < 2`, the factor market equilibria at `p = (1, 1)` are exactly
`w = (2^{2/3}/3)(1, 1)`, `z₁ = ((2z̄₁ - z̄₂)/3)(2, 1)`, `z₂ = ((2z̄₂ - z̄₁)/3)(1, 2)`. -/
theorem exercise_15_D_8_diversified {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hlo : 1 / 2 < zbar 0 / zbar 1) (hhi : zbar 0 / zbar 1 < 2) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔ w = cd8What ∧ z = cd8ZDiv zbar := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hz0 := hz 0
  have hz1 := hz 1
  obtain ⟨hk0, hk1⟩ := cd8What_ratio
  have a01 := hM.a_pos 0 cd8What 1 cd8What_pos
  have a10 := hM.a_pos 1 cd8What 0 cd8What_pos
  -- `a₁(ŵ) = a₂₁(ŵ) (2, 1)` and `a₂(ŵ) = a₁₂(ŵ) (1, 2)`
  have ha0 : cdModel.a 0 cd8What = cdModel.a 0 cd8What 1 • ![2, 1] := by
    have e : cdModel.a 0 cd8What 0 = 2 * cdModel.a 0 cd8What 1 := by
      rw [div_eq_iff a01.ne'] at hk0; exact hk0
    funext l
    fin_cases l
    · simp [e, mul_comm]
    · simp
  have ha1 : cdModel.a 1 cd8What = cdModel.a 1 cd8What 0 • ![1, 2] := by
    have e : cdModel.a 1 cd8What 1 = 2 * cdModel.a 1 cd8What 0 := by
      have a11 := hM.a_pos 1 cd8What 1 cd8What_pos
      rw [div_eq_iff a11.ne'] at hk1; linarith
    funext l
    fin_cases l
    · simp
    · simp [e, mul_comm]
  have hX : 0 < 2 * zbar 0 - zbar 1 := by
    rw [lt_div_iff₀ hz1] at hlo; linarith
  have hY : 0 < 2 * zbar 1 - zbar 0 := by
    rw [div_lt_iff₀ hz1] at hhi; linarith
  constructor
  · intro h
    obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (TwoByTwo.exercise_15_D_6a hM _ zbar w z).1 h
    have hall := (TwoByTwo.exercise_15_D_6b hM hFI cd8What_pos cd8What_c hz hq hpc hqp hw
      hsum).2 ⟨by rw [hk1]; exact hlo, by rw [hk0]; exact hhi⟩
    have hwe : w = cd8What := TwoByTwo.factor_price_equalization hM hFI hw cd8What_pos
      (fun j => (hqp j (hall j)).symm) cd8What_c
    subst hwe
    rw [Fin.sum_univ_two, ha0, ha1, smul_smul, smul_smul] at hsum
    have s0 := congrFun hsum 0
    have s1 := congrFun hsum 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at s0 s1
    have eX : q 0 * cdModel.a 0 cd8What 1 = (2 * zbar 0 - zbar 1) / 3 := by linarith
    have eY : q 1 * cdModel.a 1 cd8What 0 = (2 * zbar 1 - zbar 0) / 3 := by linarith
    have e0 : z 0 = ((2 * zbar 0 - zbar 1) / 3) • ![2, 1] := by
      rw [hzq 0, ha0, smul_smul, eX]
    have e1 : z 1 = ((2 * zbar 1 - zbar 0) / 3) • ![1, 2] := by
      rw [hzq 1, ha1, smul_smul, eY]
    refine ⟨rfl, ?_⟩
    funext j
    fin_cases j
    · exact e0
    · exact e1
  · rintro ⟨rfl, rfl⟩
    set q : Fin 2 → ℝ := ![(2 * zbar 0 - zbar 1) / 3 / cdModel.a 0 cd8What 1,
      (2 * zbar 1 - zbar 0) / 3 / cdModel.a 1 cd8What 0] with hqdef
    have hq : ∀ j, 0 < q j := fun j => by
      fin_cases j
      · simp only [hqdef, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
      · simp only [hqdef, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        positivity
    have e0 : q 0 • cdModel.a 0 cd8What = ((2 * zbar 0 - zbar 1) / 3) • ![2, 1] := by
      rw [ha0, smul_smul]
      congr 1
      simp only [hqdef, Matrix.cons_val_zero]
      field_simp
    have e1 : q 1 • cdModel.a 1 cd8What = ((2 * zbar 1 - zbar 0) / 3) • ![1, 2] := by
      rw [ha1, smul_smul]
      congr 1
      simp only [hqdef, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    have hzform : cd8ZDiv zbar = fun j => q j • cdModel.a j cd8What := by
      funext j
      fin_cases j
      · exact e0.symm
      · exact e1.symm
    rw [hzform, TwoByTwo.interior_eqm_iff hM cd8What_pos hq]
    refine ⟨fun j => (cd8What_c j).symm, ?_⟩
    rw [Fin.sum_univ_two, e0, e1]
    funext l
    fin_cases l
    · simp; ring
    · simp; ring

/-- **Exercise 15.D.8** (MWG, p. 544), outputs in the diversified region:
`q₁ = 2^{2/3}(2z̄₁ - z̄₂)/3` and `q₂ = 2^{2/3}(2z̄₂ - z̄₁)/3`. -/
theorem exercise_15_D_8_outputs {zbar : Fin 2 → ℝ} (hlo : zbar 1 ≤ 2 * zbar 0)
    (hhi : zbar 0 ≤ 2 * zbar 1) :
    cdModel.f 0 (cd8ZDiv zbar 0) = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((2 * zbar 0 - zbar 1) / 3) ∧
      cdModel.f 1 (cd8ZDiv zbar 1) = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((2 * zbar 1 - zbar 0) / 3) := by
  have hM := cdModel_isModel
  have n0 : (![2, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> norm_num
  have n1 : (![1, 2] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> norm_num
  constructor
  · change cdModel.f 0 (((2 * zbar 0 - zbar 1) / 3) • ![2, 1]) = _
    rw [hM.hom 0 _ n0 _ (by linarith)]
    change _ * cdtF (2 / 3) ![2, 1] = _
    simp only [cdtF, Matrix.cons_val_zero, Matrix.cons_val_one, Real.one_rpow, mul_one]
    norm_num
    ring
  · change cdModel.f 1 (((2 * zbar 1 - zbar 0) / 3) • ![1, 2]) = _
    rw [hM.hom 1 _ n1 _ (by linarith)]
    change _ * cdtF (1 / 3) ![1, 2] = _
    simp only [cdtF, Matrix.cons_val_zero, Matrix.cons_val_one, Real.one_rpow, one_mul]
    norm_num
    ring

/-- **Exercise 15.D.8** (MWG, p. 544), specialization in good 1. For `z̄ ≫ 0` with
`ρ = z̄₁/z̄₂ ≥ 2` the factor market equilibria at `p = (1, 1)` are exactly
`w = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`, `z = (z̄, 0)`. -/
theorem exercise_15_D_8_spec0 {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hρ : 2 ≤ zbar 0 / zbar 1) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔
      w = cd8WSpec0 (zbar 0 / zbar 1) ∧ z = ![zbar, 0] := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hρ0 : 0 < zbar 0 / zbar 1 := div_pos (hz 0) (hz 1)
  have hW := cd8WSpec0_pos hρ0
  have hkW : cdModel.a 0 (cd8WSpec0 (zbar 0 / zbar 1)) 0 /
      cdModel.a 0 (cd8WSpec0 (zbar 0 / zbar 1)) 1 = zbar 0 / zbar 1 := by
    rw [(cdModel_ratio hW).1]
    have hrel := cd8WSpec0_rel hρ0
    have h0 := hW 0
    have h1 := hW 1
    have hz0 := (hz 0).ne'
    have hz1 := (hz 1).ne'
    field_simp at hrel ⊢
    linarith
  constructor
  · intro h
    obtain ⟨hz', hc0, hk⟩ := TwoByTwo.exercise_15_D_6d_spec0_unique hM hFI cd8What_pos cd8What_c
      hz (by rw [cd8What_ratio.1]; exact hρ) h
    have hw := h.1
    refine ⟨TwoByTwo.eq_of_relPrice_eq_of_c_eq hM 0 hw hW ?_ ?_, hz'⟩
    · rw [(cdModel_ratio hw).1] at hk
      rw [(cdModel_ratio hW).1] at hkW
      have h0 := hw 0
      have h1 := hw 1
      have h0' := hW 0
      have h1' := hW 1
      rw [div_eq_div_iff h1.ne' h1'.ne']
      rw [← hkW, div_eq_div_iff h0.ne' h0'.ne'] at hk
      linarith
    · rw [hc0, cd8WSpec0_c0 hρ0]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine TwoByTwo.exercise_15_D_6d_spec0 hM hFI cd8What_pos cd8What_c hz hW
      (cd8WSpec0_c0 hρ0) hkW ?_
    rw [cd8WSpec0_rel hρ0]
    have : cd8What 0 / cd8What 1 = 1 := div_self (cd8What_pos 1).ne'
    rw [this, div_le_one hρ0]
    exact hρ

/-- **Exercise 15.D.8** (MWG, p. 544), specialization in good 2. For `z̄ ≫ 0` with
`ρ = z̄₁/z̄₂ ≤ 1/2` the factor market equilibria at `p = (1, 1)` are exactly
`w = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`, `z = (0, z̄)`. -/
theorem exercise_15_D_8_spec1 {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hρ : zbar 0 / zbar 1 ≤ 1 / 2) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔
      w = cd8WSpec1 (zbar 0 / zbar 1) ∧ z = ![0, zbar] := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hρ0 : 0 < zbar 0 / zbar 1 := div_pos (hz 0) (hz 1)
  have hW := cd8WSpec1_pos hρ0
  have hkW : cdModel.a 1 (cd8WSpec1 (zbar 0 / zbar 1)) 0 /
      cdModel.a 1 (cd8WSpec1 (zbar 0 / zbar 1)) 1 = zbar 0 / zbar 1 := by
    rw [(cdModel_ratio hW).2]
    have hrel := cd8WSpec1_rel hρ0
    have h0 := hW 0
    have h1 := hW 1
    have hz0 := (hz 0).ne'
    have hz1 := (hz 1).ne'
    field_simp at hrel ⊢
    linarith
  constructor
  · intro h
    obtain ⟨hz', hc1, hk⟩ := TwoByTwo.exercise_15_D_6d_spec1_unique hM hFI cd8What_pos cd8What_c
      hz (by rw [cd8What_ratio.2]; exact hρ) h
    have hw := h.1
    refine ⟨TwoByTwo.eq_of_relPrice_eq_of_c_eq hM 1 hw hW ?_ ?_, hz'⟩
    · rw [(cdModel_ratio hw).2] at hk
      rw [(cdModel_ratio hW).2] at hkW
      have h0 := hw 0
      have h1 := hw 1
      have h0' := hW 0
      have h1' := hW 1
      rw [div_eq_div_iff h1.ne' h1'.ne']
      rw [← hkW, div_eq_div_iff (by positivity) (by positivity)] at hk
      linarith
    · rw [hc1, cd8WSpec1_c1 hρ0]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine TwoByTwo.exercise_15_D_6d_spec1 hM hFI cd8What_pos cd8What_c hz hW
      (cd8WSpec1_c1 hρ0) hkW ?_
    rw [cd8WSpec1_rel hρ0]
    have : cd8What 0 / cd8What 1 = 1 := div_self (cd8What_pos 1).ne'
    rw [this, le_div_iff₀ (by positivity)]
    linarith

/-- **Exercise 15.D.8** (MWG, p. 544), summary: for every `z̄ ≫ 0` there is exactly one factor
market equilibrium at `p = (1, 1)`, given by the formula of the region of `ρ = z̄₁/z̄₂`
(`ρ ≥ 2`: specialization in good 1; `ρ ≤ 1/2`: specialization in good 2; otherwise
diversified). -/
theorem exercise_15_D_8 {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) :
    ∃! wz : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ), IsFactorEqm cdModel.f ![1, 1] zbar wz.1 wz.2 := by
  by_cases h2 : 2 ≤ zbar 0 / zbar 1
  · refine ⟨(cd8WSpec0 (zbar 0 / zbar 1), ![zbar, 0]), (exercise_15_D_8_spec0 hz h2).2
      ⟨rfl, rfl⟩, fun wz h => ?_⟩
    obtain ⟨h1, h2⟩ := (exercise_15_D_8_spec0 hz h2).1 h
    exact Prod.ext h1 h2
  by_cases h1 : zbar 0 / zbar 1 ≤ 1 / 2
  · refine ⟨(cd8WSpec1 (zbar 0 / zbar 1), ![0, zbar]), (exercise_15_D_8_spec1 hz h1).2
      ⟨rfl, rfl⟩, fun wz h => ?_⟩
    obtain ⟨e1, e2⟩ := (exercise_15_D_8_spec1 hz h1).1 h
    exact Prod.ext e1 e2
  rw [not_le] at h1 h2
  refine ⟨(cd8What, cd8ZDiv zbar), (exercise_15_D_8_diversified hz h1 h2).2 ⟨rfl, rfl⟩,
    fun wz h => ?_⟩
  obtain ⟨e1, e2⟩ := (exercise_15_D_8_diversified hz h1 h2).1 h
  exact Prod.ext e1 e2

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Pareto set of factor allocations; Exercise 15.D.1 and footnote 16 (MWG pp. 532-536)

In the 2 × 2 production model (`TwoByTwo`) with total factor endowment `z̄`:

* p. 533, Figure 15.D.2(b): a factor allocation (`IsFactorAllocation`) is *efficient*
  (`TwoByTwo.IsEfficientAllocation`, the Pareto set) if no other allocation of `z̄` produces at
  least as much of both goods and more of one. An allocation is *supported*
  (`TwoByTwo.IsSupportedBy`, `TwoByTwo.IsSupportedAllocation`) if `zⱼ = qⱼ aⱼ(w)` for common
  factor prices `w ≫ 0` (the book's tangency of the isoquants). Supported allocations are efficient
  (`TwoByTwo.supported_isEfficient`); conversely, with ray-surjective technologies that are
  differentiable along rays, every efficient allocation with `zⱼ ≫ 0` is supported
  (`TwoByTwo.efficient_isSupported`).
* **Exercise 15.D.1(a)** and the claim of p. 533: along the interior supported allocations of a
  given `z̄` the intensity ranking `r₀ = a₁₁/a₂₁` versus `r₁ = a₁₂/a₂₂` never flips
  (`TwoByTwo.factorRatio_order_preserved`, `TwoByTwo.exercise_15_D_1a`); if one interior
  supported allocation lies on the diagonal of the Edgeworth box, every interior point of the
  diagonal is supported with the same factor prices and every interior supported allocation is
  on the diagonal (`TwoByTwo.diagonal_pareto_set`). For smooth technologies these are
  statements about the Pareto set itself (`TwoByTwo.exercise_15_D_1a_pareto`).
* **Exercise 15.D.1(b)**: false as printed in this generality. In the Leontief model a ray from
  firm 1's origin meets the Pareto set twice, and the Pareto set is not the diagonal
  (`exercise_15_D_1b_counterexample`). Corrected statement: when the technologies are
  differentiable along rays the factor intensities are strictly decreasing in `w₁/w₂`
  (`TwoByTwo.relRatio_strictAnti`), along the interior supported allocations with `r₀ > r₁`
  a higher relative factor price means lower intensities in both firms and strictly more of both
  factors for firm 1 (`TwoByTwo.exercise_15_D_1b_monotone`), and a ray from either origin meets
  the interior supported allocations at most once (`TwoByTwo.exercise_15_D_1b`); instance
  `exercise_15_D_1b_cdModel`.
* **Footnote 16** (p. 536): the Stolper-Samuelson conclusion holds without the global factor
  intensity condition when firm 1 is more intensive in factor 1 at the initial interior
  equilibrium (`TwoByTwo.footnote_16`; instance `footnote_16_leontief`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

/-- **Figure 15.D.2** (MWG, pp. 532-533). A factor allocation of the endowment `z̄` between the two
firms: `zⱼ ∈ ℝ²₊` are the inputs of firm `j` and `z₀ + z₁ = z̄` (a point of the Edgeworth box). -/
def IsFactorAllocation (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ j, z j ∈ nonnegOrthant 2) ∧ z 0 + z 1 = zbar

/-- **Figure 15.D.2(b)** (MWG, p. 533). The Pareto set of factor allocations: allocations of `z̄`
at which it is not possible to produce more of one good without producing less of the other. -/
def TwoByTwo.IsEfficientAllocation (M : TwoByTwo) (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  IsFactorAllocation zbar z ∧ ¬ ∃ z', IsFactorAllocation zbar z' ∧
    (∀ j, M.f j (z j) ≤ M.f j (z' j)) ∧ ∃ j, M.f j (z j) < M.f j (z' j)

/-- **Section 15.D** (MWG, p. 533). The allocation `z` of `z̄` is supported by the factor prices
`w ≫ 0` with outputs `q ≥ 0`: `zⱼ = qⱼ aⱼ(w)` (both firms minimize costs at the same factor
prices, the tangency of the isoquants in Figure 15.D.2(b)). -/
def TwoByTwo.IsSupportedBy (M : TwoByTwo) (zbar w q : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  StrictlyPositive w ∧ (∀ j, 0 ≤ q j) ∧ (∀ j, z j = q j • M.a j w) ∧ z 0 + z 1 = zbar

/-- **Section 15.D** (MWG, p. 533). The allocation `z` of `z̄` is supported by some factor prices
`w ≫ 0`. -/
def TwoByTwo.IsSupportedAllocation (M : TwoByTwo) (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  ∃ w q, M.IsSupportedBy zbar w q z

/-- **Exercise 15.D.1** (MWG, p. 533). An interior supported allocation: factor prices `w ≫ 0` and
outputs `q ≫ 0` with `q₀ a₀(w) + q₁ a₁(w) = z̄` (the allocation is `zⱼ = qⱼ aⱼ(w)`). -/
def TwoByTwo.IsInteriorSupport (M : TwoByTwo) (zbar w q : Fin 2 → ℝ) : Prop :=
  StrictlyPositive w ∧ (∀ j, 0 < q j) ∧ q 0 • M.a 0 w + q 1 • M.a 1 w = zbar

/-- **Exercise 15.D.1** (MWG, p. 533). The factor intensity of firm `j` at factor prices `w`: its
use of factor 1 relative to factor 2, `a_{1j}(w)/a_{2j}(w)`. -/
noncomputable def TwoByTwo.factorRatio (M : TwoByTwo) (j : Fin 2) (w : Fin 2 → ℝ) : ℝ :=
  M.a j w 0 / M.a j w 1

namespace TwoByTwo

variable {M : TwoByTwo}

/-- Producing with the unit input vector: `fⱼ(q aⱼ(w)) = q` for `q ≥ 0`. -/
theorem f_smul_a (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ}
    (hq : 0 ≤ q) : M.f j (q • M.a j w) = q := by
  rw [hM.hom j _ (hM.a_mem j w hw).1 q hq, (hM.a_mem j w hw).2, mul_one]

/-! ### Supported allocations are efficient -/

/-- **Figure 15.D.2(b)** (MWG, p. 533). An allocation supported by common factor prices `w ≫ 0` is
in the Pareto set: if `z'` produced at least as much of both goods and more of one, then
`∑ⱼ fⱼ(z'ⱼ) cⱼ(w) > ∑ⱼ qⱼ cⱼ(w) = w·z̄`, while duality gives `fⱼ(z'ⱼ) cⱼ(w) ≤ w·z'ⱼ`. -/
theorem supported_isEfficient (hM : M.IsModel) {zbar w q : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsSupportedBy zbar w q z) : M.IsEfficientAllocation zbar z := by
  obtain ⟨hw, hq, hz, hsum⟩ := h
  have hzm : ∀ j, z j ∈ nonnegOrthant 2 := fun j l => by
    rw [hz j]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (hq j) ((hM.a_mem j w hw).1 l)
  refine ⟨⟨hzm, hsum⟩, ?_⟩
  rintro ⟨z', ⟨hz'm, hsum'⟩, hge, j, hlt⟩
  have hfz : ∀ k, M.f k (z k) = q k := fun k => by rw [hz k]; exact f_smul_a hM k hw (hq k)
  have hdual : ∀ k, M.f k (z' k) * M.c k w ≤ w ⬝ᵥ z' k := fun k => f_mul_c_le hM k hw (hz'm k)
  have hcost : ∀ k, w ⬝ᵥ z k = q k * M.c k w := fun k => by
    rw [hz k, dotProduct_smul, smul_eq_mul]
    rfl
  have htot : w ⬝ᵥ z' 0 + w ⬝ᵥ z' 1 = w ⬝ᵥ z 0 + w ⬝ᵥ z 1 := by
    rw [← dotProduct_add, ← dotProduct_add, hsum, hsum']
  rw [hcost 0, hcost 1] at htot
  have hc0 := c_pos hM 0 hw
  have hc1 := c_pos hM 1 hw
  have h0 := hge 0
  have h1 := hge 1
  rw [hfz] at h0 h1 hlt
  have hd0 := hdual 0
  have hd1 := hdual 1
  rcases Fin.exists_fin_two.1 (⟨j, hlt⟩ : ∃ k, q k < M.f k (z' k)) with hl | hl
  · nlinarith [mul_le_mul_of_nonneg_right h1 hc1.le, mul_lt_mul_of_pos_right hl hc0]
  · nlinarith [mul_le_mul_of_nonneg_right h0 hc0.le, mul_lt_mul_of_pos_right hl hc1]

/-! ### Exercise 15.D.1(a): the intensity ranking along the supported allocations -/

/-- The second endowment coordinate of an interior supported allocation is positive. -/
theorem interiorSupport_zbar_pos (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) : StrictlyPositive zbar := by
  obtain ⟨hw, hq, hsum⟩ := h
  intro l
  rw [← hsum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_pos (hq 0) (hM.a_pos 0 w l hw)
  have := mul_pos (hq 1) (hM.a_pos 1 w l hw)
  linarith

/-- The full-employment identities of an interior supported allocation, with `rⱼ` the factor
intensities at `w`: `q₀ a₂₁ (r₀ - r₁) = z̄₁ - r₁ z̄₂` and `q₁ a₂₂ (r₀ - r₁) = r₀ z̄₂ - z̄₁`. -/
theorem interiorSupport_identities (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) :
    q 0 * M.a 0 w 1 * (M.factorRatio 0 w - M.factorRatio 1 w) =
        zbar 0 - M.factorRatio 1 w * zbar 1 ∧
      q 1 * M.a 1 w 1 * (M.factorRatio 0 w - M.factorRatio 1 w) =
        M.factorRatio 0 w * zbar 1 - zbar 0 := by
  obtain ⟨hw, -, hsum⟩ := h
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
  have h01 := (hM.a_pos 0 w 1 hw).ne'
  have h11 := (hM.a_pos 1 w 1 hw).ne'
  unfold factorRatio
  rw [← e0, ← e1]
  constructor <;> field_simp <;> ring

/-- **Exercise 15.D.1(a)** (MWG, p. 533). At an interior supported allocation with
`r₁ < r₀`, the endowment ratio `ρ̄ = z̄₁/z̄₂` lies strictly between the intensities:
`r₁ < ρ̄ < r₀`. -/
theorem interiorSupport_between (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (hlt : M.factorRatio 1 w < M.factorRatio 0 w) :
    M.factorRatio 1 w < zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 < M.factorRatio 0 w := by
  obtain ⟨e0, e1⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hp0 := mul_pos (mul_pos (h.2.1 0) (hM.a_pos 0 w 1 h.1)) (sub_pos.2 hlt)
  have hp1 := mul_pos (mul_pos (h.2.1 1) (hM.a_pos 1 w 1 h.1)) (sub_pos.2 hlt)
  rw [lt_div_iff₀ hz1, div_lt_iff₀ hz1]
  constructor <;> linarith

/-- The mirror image: if `r₀ < r₁` then `r₀ < ρ̄ < r₁`. -/
theorem interiorSupport_between' (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (hlt : M.factorRatio 0 w < M.factorRatio 1 w) :
    M.factorRatio 0 w < zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 < M.factorRatio 1 w := by
  obtain ⟨e0, e1⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hp0 := mul_pos (mul_pos (h.2.1 0) (hM.a_pos 0 w 1 h.1)) (sub_pos.2 hlt)
  have hp1 := mul_pos (mul_pos (h.2.1 1) (hM.a_pos 1 w 1 h.1)) (sub_pos.2 hlt)
  rw [lt_div_iff₀ hz1, div_lt_iff₀ hz1]
  constructor <;> nlinarith

/-- With equal intensities, `r₀ = r₁ = ρ̄`: both firms use the factors in the endowment
proportions. -/
theorem interiorSupport_eq (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (heq : M.factorRatio 0 w = M.factorRatio 1 w) :
    M.factorRatio 0 w = zbar 0 / zbar 1 ∧ M.factorRatio 1 w = zbar 0 / zbar 1 := by
  obtain ⟨e0, -⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  rw [heq, sub_self, mul_zero] at e0
  have : M.factorRatio 1 w = zbar 0 / zbar 1 := by
    rw [eq_div_iff hz1.ne']
    linarith
  exact ⟨heq.trans this, this⟩

/-- Revealed cost minimization in terms of `w`: the factor intensities are antitone in the
relative factor price `w₁/w₂` (MWG, p. 532). -/
theorem factorRatio_antitone (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : w 0 / w 1 ≤ w' 0 / w' 1) :
    M.factorRatio j w' ≤ M.factorRatio j w := by
  unfold factorRatio
  rw [a_eq_rel hM j hw, a_eq_rel hM j hw']
  exact intensity_antitone hM j (div_pos (hw 0) (hw 1)) h

/-- **Exercise 15.D.1(a)** (MWG, p. 533). If firm 1 is more intensive in factor 1 at one interior
supported allocation of `z̄`, it is so at every interior supported allocation of `z̄`. (A flip
would put `ρ̄` on opposite sides, which the monotonicity of both intensities in `w₁/w₂` rules
out.) -/
theorem factorRatio_order_preserved (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (hlt : M.factorRatio 1 w < M.factorRatio 0 w) :
    M.factorRatio 1 w' < M.factorRatio 0 w' := by
  by_contra hn
  rw [not_lt] at hn
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM h hlt
  have hρ' : M.factorRatio 0 w' ≤ zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 ≤ M.factorRatio 1 w' := by
    rcases eq_or_lt_of_le hn with he | hl
    · have := interiorSupport_eq hM h' he
      exact ⟨this.1.le, this.2.ge⟩
    · have := interiorSupport_between' hM h' hl
      exact ⟨this.1.le, this.2.le⟩
  rcases le_or_gt (w' 0 / w' 1) (w 0 / w 1) with hle | hgt
  · have := factorRatio_antitone hM 0 h'.1 h.1 hle
    linarith
  · have := factorRatio_antitone hM 1 h.1 h'.1 hgt.le
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533), the mirror image: if firm 2 is more intensive in
factor 1 at one interior supported allocation of `z̄`, it is so at all of them. -/
theorem factorRatio_order_preserved' (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (hlt : M.factorRatio 0 w < M.factorRatio 1 w) :
    M.factorRatio 0 w' < M.factorRatio 1 w' := by
  by_contra hn
  rw [not_lt] at hn
  obtain ⟨hb1, hb2⟩ := interiorSupport_between' hM h hlt
  have hρ' : M.factorRatio 1 w' ≤ zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 ≤ M.factorRatio 0 w' := by
    rcases eq_or_lt_of_le hn with he | hl
    · have := interiorSupport_eq hM h' he.symm
      exact ⟨this.2.le, this.1.ge⟩
    · have := interiorSupport_between hM h' hl
      exact ⟨this.1.le, this.2.le⟩
  rcases le_or_gt (w' 0 / w' 1) (w 0 / w 1) with hle | hgt
  · have := factorRatio_antitone hM 1 h'.1 h.1 hle
    linarith
  · have := factorRatio_antitone hM 0 h.1 h'.1 hgt.le
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533). Equal intensities at one interior supported allocation
of `z̄` force equal intensities at all of them. -/
theorem factorRatio_eq_preserved (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (heq : M.factorRatio 0 w = M.factorRatio 1 w) :
    M.factorRatio 0 w' = M.factorRatio 1 w' := by
  rcases lt_trichotomy (M.factorRatio 0 w') (M.factorRatio 1 w') with hl | he | hg
  · have := factorRatio_order_preserved' hM h' h hl
    linarith
  · exact he
  · have := factorRatio_order_preserved hM h' h hg
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533). For a given endowment `z̄`, either firm 1 is more
intensive in factor 1 at every interior supported allocation, or firm 2 is at every one, or at
every one both firms use the factors in the endowment proportions `ρ̄ = z̄₁/z̄₂` (the diagonal of
the Edgeworth box). -/
theorem exercise_15_D_1a (hM : M.IsModel) (zbar : Fin 2 → ℝ) :
    (∀ w q, M.IsInteriorSupport zbar w q → M.factorRatio 1 w < M.factorRatio 0 w) ∨
      (∀ w q, M.IsInteriorSupport zbar w q → M.factorRatio 0 w < M.factorRatio 1 w) ∨
      (∀ w q, M.IsInteriorSupport zbar w q →
        M.factorRatio 0 w = zbar 0 / zbar 1 ∧ M.factorRatio 1 w = zbar 0 / zbar 1) := by
  by_cases hex : ∃ w q, M.IsInteriorSupport zbar w q
  · obtain ⟨w, q, h⟩ := hex
    rcases lt_trichotomy (M.factorRatio 0 w) (M.factorRatio 1 w) with hl | he | hg
    · exact Or.inr (Or.inl fun w' q' h' => factorRatio_order_preserved' hM h h' hl)
    · exact Or.inr (Or.inr fun w' q' h' =>
        interiorSupport_eq hM h' (factorRatio_eq_preserved hM h h' he))
    · exact Or.inl fun w' q' h' => factorRatio_order_preserved hM h h' hg
  · exact Or.inl fun w q h => absurd ⟨w, q, h⟩ hex

/-- **Section 15.D** (MWG, p. 533), the diagonal claim: "if [the Pareto set] ever cuts the
diagonal then ... the diagonal must be the Pareto set". If at an interior supported allocation
firm 1 uses `t z̄` (`0 < t < 1`), then every point `s z̄` (`0 < s < 1`) of the diagonal is
supported by the same factor prices, and every interior supported allocation of `z̄` lies on the
diagonal. -/
theorem diagonal_pareto_set (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hdiag : q 0 • M.a 0 w = t • zbar) :
    (∀ s : ℝ, 0 < s → s < 1 →
        M.IsInteriorSupport zbar w ![s * q 0 / t, (1 - s) * q 1 / (1 - t)] ∧
          (s * q 0 / t) • M.a 0 w = s • zbar) ∧
      ∀ w' q', M.IsInteriorSupport zbar w' q' →
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧ q' 0 • M.a 0 w' = s • zbar := by
  obtain ⟨hw, hq, hsum⟩ := h
  have d0 : ∀ l, q 0 * M.a 0 w l = t * zbar l := fun l => by simpa using congrFun hdiag l
  have d1 : ∀ l, q 1 * M.a 1 w l = (1 - t) * zbar l := fun l => by
    have := congrFun hsum l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [sub_mul, one_mul, ← d0 l]
    linarith
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  constructor
  · intro s hs0 hs1
    have hs1' : 0 < 1 - s := sub_pos.2 hs1
    have e0 : ∀ l, s * q 0 / t * M.a 0 w l = s * zbar l := fun l => by
      rw [show s * q 0 / t * M.a 0 w l = s / t * (q 0 * M.a 0 w l) by ring, d0 l]
      field_simp
    have e1 : ∀ l, (1 - s) * q 1 / (1 - t) * M.a 1 w l = (1 - s) * zbar l := fun l => by
      rw [show (1 - s) * q 1 / (1 - t) * M.a 1 w l = (1 - s) / (1 - t) * (q 1 * M.a 1 w l)
        by ring, d1 l]
      field_simp
    refine ⟨⟨hw, fun j => ?_, ?_⟩, ?_⟩
    · fin_cases j
      · simpa using div_pos (mul_pos hs0 (hq 0)) ht0
      · simpa using div_pos (mul_pos hs1' (hq 1)) ht1'
    · funext l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [e0 l, e1 l]
      ring
    · funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact e0 l
  · intro w' q' h'
    have hz1 := interiorSupport_zbar_pos hM ⟨hw, hq, hsum⟩ 1
    have hr0 : M.factorRatio 0 w = M.factorRatio 1 w := by
      have hq0 := (hq 0).ne'
      have hq1 := (hq 1).ne'
      have h01 := (hM.a_pos 0 w 1 hw).ne'
      have h11 := (hM.a_pos 1 w 1 hw).ne'
      unfold factorRatio
      rw [div_eq_div_iff h01 h11]
      have k0 : q 0 * (M.a 0 w 0 * zbar 1) = q 0 * (M.a 0 w 1 * zbar 0) := by
        linear_combination zbar 1 * d0 0 - zbar 0 * d0 1
      have k1 : q 1 * (M.a 1 w 0 * zbar 1) = q 1 * (M.a 1 w 1 * zbar 0) := by
        linear_combination zbar 1 * d1 0 - zbar 0 * d1 1
      have k0' := mul_left_cancel₀ hq0 k0
      have k1' := mul_left_cancel₀ hq1 k1
      have hzb := hz1.ne'
      have : M.a 0 w 0 * M.a 1 w 1 * zbar 1 = M.a 1 w 0 * M.a 0 w 1 * zbar 1 := by
        linear_combination M.a 1 w 1 * k0' - M.a 0 w 1 * k1'
      exact mul_right_cancel₀ hzb this
    have he' := factorRatio_eq_preserved hM ⟨hw, hq, hsum⟩ h' hr0
    have hρ := (interiorSupport_eq hM h' he').1
    have hw' := h'.1
    have hq' := h'.2.1
    have hs' := congrFun h'.2.2 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs'
    have ha01 := hM.a_pos 0 w' 1 hw'
    have ha11 := hM.a_pos 1 w' 1 hw'
    refine ⟨q' 0 * M.a 0 w' 1 / zbar 1, div_pos (mul_pos (hq' 0) ha01) hz1, ?_, ?_⟩
    · rw [div_lt_one hz1]
      nlinarith [mul_pos (hq' 1) ha11]
    · unfold factorRatio at hρ
      rw [div_eq_div_iff ha01.ne' hz1.ne'] at hρ
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue]
        field_simp
        linear_combination q' 0 * hρ
      · simp only [Fin.mk_one, Fin.isValue]
        field_simp

/-! ### Exercise 15.D.1(b), corrected: smooth technologies -/

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected hypothesis. If good `j`'s technology is
differentiable along rays, its factor intensity is strictly decreasing in the relative factor
price: two relative prices with the same cost-minimizing ratio `ρ` would give two different
slopes `ω/gⱼ(ω) = Fⱼ(ρ) ω/(ωρ + 1)` of the isoquant at `ρ` (`rayF_deriv_eq`). -/
theorem relRatio_strictAnti (hM : M.IsModel) (j : Fin 2) (hd : M.RayDifferentiable j)
    {ω ω' : ℝ} (hω : 0 < ω) (hlt : ω < ω') :
    M.a j ![ω', 1] 0 / M.a j ![ω', 1] 1 < M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 := by
  have hω' : 0 < ω' := hω.trans hlt
  refine lt_of_le_of_ne (intensity_antitone hM j hω hlt.le) fun heq => ?_
  obtain ⟨ρ, hρ⟩ : ∃ ρ, M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ := ⟨_, rfl⟩
  rw [hρ] at heq
  have hp := relPrice_pos hω
  have hρpos : 0 < ρ := hρ ▸ div_pos (hM.a_pos j _ 0 hp) (hM.a_pos j _ 1 hp)
  have hD := (hd ρ hρpos).hasDerivAt
  have e1 := rayF_deriv_eq hM j hω hρ hD
  have e2 := rayF_deriv_eq hM j hω' heq hD
  have f1 := rayF_mul_g_eq hM j hω hρ
  have f2 := rayF_mul_g_eq hM j hω' heq
  have hg : 0 < M.g j ω := c_pos hM j hp
  have hg' : 0 < M.g j ω' := c_pos hM j (relPrice_pos hω')
  rw [e1, div_eq_div_iff hg.ne' hg'.ne'] at e2
  have key : ω * (ω' * ρ + 1) = ω' * (ω * ρ + 1) := by
    rw [← f1, ← f2]
    linear_combination M.f j ![ρ, 1] * e2
  have : ω = ω' := by linear_combination key
  exact absurd this hlt.ne

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected. With technologies differentiable along rays,
a higher relative factor price `w₁/w₂` makes both firms strictly less intensive in factor 1. -/
theorem exercise_15_D_1b_ratios_fall (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (hlt : w 0 / w 1 < w' 0 / w' 1) (j : Fin 2) : M.factorRatio j w' < M.factorRatio j w := by
  unfold factorRatio
  rw [a_eq_rel hM j hw, a_eq_rel hM j hw']
  exact relRatio_strictAnti hM j (hd j) (div_pos (hw 0) (hw 1)) hlt

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected: "the factor intensities of the two firms and
the supporting relative factor prices change monotonically as we move along the Pareto set from
one origin to the other". For interior supported allocations of `z̄` with firm 1 more intensive
in factor 1, and technologies differentiable along rays: if the supporting relative factor price
is higher at `w'` than at `w`, both intensities are strictly lower at `w'`, and firm 1 uses
strictly more of both factors (the allocation moves from firm 1's origin towards firm 2's). -/
theorem exercise_15_D_1b_monotone (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {zbar w q w' q' : Fin 2 → ℝ} (h : M.IsInteriorSupport zbar w q)
    (h' : M.IsInteriorSupport zbar w' q') (hint : M.factorRatio 1 w < M.factorRatio 0 w)
    (hlt : w 0 / w 1 < w' 0 / w' 1) :
    M.factorRatio 0 w' < M.factorRatio 0 w ∧ M.factorRatio 1 w' < M.factorRatio 1 w ∧
      q 0 * M.a 0 w 0 < q' 0 * M.a 0 w' 0 ∧ q 0 * M.a 0 w 1 < q' 0 * M.a 0 w' 1 := by
  have ha0 := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hlt 0
  have ha1 := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hlt 1
  have hint' := factorRatio_order_preserved hM h h' hint
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM h hint
  obtain ⟨hb1', hb2'⟩ := interiorSupport_between hM h' hint'
  obtain ⟨eS, -⟩ := interiorSupport_identities hM h
  obtain ⟨eS', -⟩ := interiorSupport_identities hM h'
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hbpos : 0 < M.factorRatio 1 w := div_pos (hM.a_pos 1 w 0 h.1) (hM.a_pos 1 w 1 h.1)
  have c0 : q 0 * M.a 0 w 0 = M.factorRatio 0 w * (q 0 * M.a 0 w 1) := by
    have := (hM.a_pos 0 w 1 h.1).ne'
    unfold factorRatio
    field_simp
  have c0' : q' 0 * M.a 0 w' 0 = M.factorRatio 0 w' * (q' 0 * M.a 0 w' 1) := by
    have := (hM.a_pos 0 w' 1 h'.1).ne'
    unfold factorRatio
    field_simp
  rw [lt_div_iff₀ hz1] at hb1 hb1'
  rw [div_lt_iff₀ hz1] at hb2 hb2'
  refine ⟨ha0, ha1, ?_, ?_⟩
  · rw [c0, c0']
    set a := M.factorRatio 0 w
    set b := M.factorRatio 1 w
    set a' := M.factorRatio 0 w'
    set b' := M.factorRatio 1 w'
    set S := q 0 * M.a 0 w 1
    set S' := q' 0 * M.a 0 w' 1
    have key : (a' * S' - a * S) * ((a - b) * (a' - b')) * (a' - b) =
        a' * (b - b') * (a' * zbar 1 - zbar 0) * (a - b) +
          (zbar 0 - b * zbar 1) * b * (a - a') * (a' - b') := by
      linear_combination (a' * (a - b) * (a' - b)) * eS' - (a * (a' - b') * (a' - b)) * eS
    have ha'pos : 0 < a' := by nlinarith
    have hR : 0 < a' * (b - b') * (a' * zbar 1 - zbar 0) * (a - b) +
        (zbar 0 - b * zbar 1) * b * (a - a') * (a' - b') := by
      apply add_pos
      · apply mul_pos (mul_pos (mul_pos ha'pos (by linarith)) (by linarith)) (by linarith)
      · apply mul_pos (mul_pos (mul_pos (by linarith) hbpos) (by linarith)) (by linarith)
    have hP : 0 < (a - b) * (a' - b') * (a' - b) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
    by_contra hc
    rw [not_lt] at hc
    have : (a' * S' - a * S) * ((a - b) * (a' - b')) * (a' - b) ≤ 0 :=
      calc _ = (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hP.le
    linarith
  · set a := M.factorRatio 0 w
    set b := M.factorRatio 1 w
    set a' := M.factorRatio 0 w'
    set b' := M.factorRatio 1 w'
    set S := q 0 * M.a 0 w 1
    set S' := q' 0 * M.a 0 w' 1
    have key : (S' - S) * ((a - b) * (a' - b')) =
        (zbar 0 - b * zbar 1) * (a - a') + (b - b') * (zbar 1 * a - zbar 0) := by
      linear_combination (a - b) * eS' - (a' - b') * eS
    have hR : 0 < (zbar 0 - b * zbar 1) * (a - a') + (b - b') * (zbar 1 * a - zbar 0) :=
      add_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
    have hP : 0 < (a - b) * (a' - b') := mul_pos (by linarith) (by linarith)
    by_contra hc
    rw [not_lt] at hc
    have : (S' - S) * ((a - b) * (a' - b')) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hP.le
    linarith

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected: "any ray from the origin of either of the
firms can intersect the Pareto set at most once". With technologies differentiable along rays,
two interior supported allocations of `z̄` off the diagonal (`r₀ ≠ r₁`) at which firm `j` uses
the factors in the same proportion (the same ray from firm `j`'s origin) are equal. -/
theorem exercise_15_D_1b (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {zbar w q w' q' : Fin 2 → ℝ} (h : M.IsInteriorSupport zbar w q)
    (h' : M.IsInteriorSupport zbar w' q') (hne : M.factorRatio 0 w ≠ M.factorRatio 1 w)
    (j : Fin 2) (hray : M.factorRatio j w = M.factorRatio j w') :
    (fun k => q k • M.a k w) = fun k => q' k • M.a k w' := by
  have hω : w 0 / w 1 = w' 0 / w' 1 := by
    rcases lt_trichotomy (w 0 / w 1) (w' 0 / w' 1) with hl | he | hg
    · have := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hl j
      linarith
    · exact he
    · have := exercise_15_D_1b_ratios_fall hM hd h'.1 h.1 hg j
      linarith
  have ha : ∀ k, M.a k w = M.a k w' := fun k => by
    rw [a_eq_rel hM k h.1, a_eq_rel hM k h'.1, hω]
  have h01 := hM.a_pos 0 w 1 h.1
  have h11 := hM.a_pos 1 w 1 h.1
  have hD : M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 ≠ 0 := by
    intro hD0
    apply hne
    unfold factorRatio
    rw [div_eq_div_iff h01.ne' h11.ne']
    linarith
  have hs : ∑ k, q k • M.a k w = zbar := by rw [Fin.sum_univ_two]; exact h.2.2
  have hs' : ∑ k, q' k • M.a k w = zbar := by
    rw [Fin.sum_univ_two, ha 0, ha 1]
    exact h'.2.2
  have hc := outputs_cramer (a := fun k => M.a k w) hD hs
  have hc' := outputs_cramer (a := fun k => M.a k w) hD hs'
  have hq : q = q' := by
    funext k
    fin_cases k
    · exact hc.1.trans hc'.1.symm
    · exact hc.2.trans hc'.2.symm
  funext k
  rw [hq, ha k]

/-! ### Efficient interior allocations are supported (smooth technologies) -/

/-- Moving along a line from an interior point keeps it interior for small steps. -/
theorem eventually_strictlyPositive_line {z : Fin 2 → ℝ} (hz : StrictlyPositive z)
    (d : Fin 2 → ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), StrictlyPositive (z + t • d) := by
  have : ∀ l, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (z + t • d) l := by
    intro l
    have hc : Continuous fun t : ℝ => (z + t • d) l := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hz l))
  exact Filter.eventually_all.2 this

/-- A function with positive derivative at `0` exceeds its value at `0` just to the right. -/
theorem eventually_lt_of_hasDerivAt_pos {φ : ℝ → ℝ} {D : ℝ} (hφ : HasDerivAt φ D 0)
    (hD : 0 < D) : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ 0 < φ t := by
  have h1 := hφ.tendsto_slope_zero_right.eventually (lt_mem_nhds hD)
  filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, smul_eq_mul] at ht
  have htpos' : 0 < t := htpos
  have := mul_pos htpos' ht
  rwa [← mul_assoc, mul_inv_cancel₀ htpos'.ne', one_mul, sub_pos] at this

/-- The derivative of `fⱼ` along a line through an interior point `z` whose factor ratio is
cost-minimizing at the relative factor price `ω`: `d/dt fⱼ(z + t d) = (ω d₁ + d₂)/gⱼ(ω)` at
`t = 0`. The gradient of `fⱼ` at `z` is a positive multiple of `(ω, 1)` (by homogeneity,
`fⱼ(x) = x₂ Fⱼ(x₁/x₂)`, and `rayF_deriv_eq`). -/
theorem f_hasDerivAt_line (hM : M.IsModel) (j : Fin 2) (hd : M.RayDifferentiable j)
    {z d : Fin 2 → ℝ} (hz : StrictlyPositive z) {ω : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = z 0 / z 1) :
    HasDerivAt (fun t : ℝ => M.f j (z + t • d)) ((ω * d 0 + d 1) / M.g j ω) 0 := by
  have hz0 := hz 0
  have hz1 := hz 1
  have hρ : 0 < z 0 / z 1 := div_pos hz0 hz1
  have hF := (hd _ hρ).hasDerivAt
  have hF' := rayF_deriv_eq hM j hω hk hF
  have hFg := rayF_mul_g_eq hM j hω hk
  have hg : 0 < M.g j ω := c_pos hM j (relPrice_pos hω)
  have h0 : HasDerivAt (fun t : ℝ => z 0 + t * d 0) (d 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add (z 0)
  have h1 : HasDerivAt (fun t : ℝ => z 1 + t * d 1) (d 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 1)).const_add (z 1)
  have hr : HasDerivAt (fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1))
      ((d 0 * (z 1 + 0 * d 1) - (z 0 + 0 * d 0) * d 1) / (z 1 + 0 * d 1) ^ 2) 0 :=
    h0.div h1 (by simpa using hz1.ne')
  have hF0 : HasDerivAt (fun s : ℝ => M.f j ![s, 1])
      (deriv (fun s : ℝ => M.f j ![s, 1]) (z 0 / z 1))
      ((fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1)) 0) := by
    simpa using hF
  have hprod := h1.mul (hF0.comp (0 : ℝ) hr)
  have heq : (fun t : ℝ => M.f j (z + t • d)) =ᶠ[𝓝 0] fun t =>
      (z 1 + t * d 1) * ((fun s : ℝ => M.f j ![s, 1]) ∘
        (fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1))) t := by
    filter_upwards [eventually_strictlyPositive_line hz d] with t ht
    rw [f_eq_ray hM j ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have := hprod.congr_of_eventuallyEq heq
  convert this using 1
  rw [hF']
  have hFρ : M.f j ![z 0 / z 1, 1] = (ω * (z 0 / z 1) + 1) / M.g j ω := by
    rw [eq_div_iff hg.ne']
    exact hFg
  simp only [Function.comp_apply, zero_mul, add_zero]
  rw [hFρ]
  field_simp
  ring

/-- **Figure 15.D.2(b)** (MWG, p. 533), the converse: with ray-surjective technologies that are
differentiable along rays, every efficient allocation with `zⱼ ≫ 0` for both firms is supported
by common factor prices (the isoquants are tangent). Otherwise the gradients of `f₁` and `f₂`
point in different directions, and moving a little of the factors from firm 2 to firm 1 along a
suitable direction raises both outputs. -/
theorem efficient_isSupported (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) :
    M.IsSupportedAllocation zbar z := by
  obtain ⟨⟨-, hsum⟩, hne⟩ := h
  choose ω hω hk using fun j => hs j (z j 0 / z j 1) (div_pos (hint j 0) (hint j 1))
  have hrep : ∀ j, z j = (z j 1 / M.a j ![ω j, 1] 1) • M.a j ![ω j, 1] := by
    intro j
    have ha1 := hM.a_pos j ![ω j, 1] 1 (relPrice_pos (hω j))
    have hk' := hk j
    rw [div_eq_div_iff ha1.ne' (hint j 1).ne'] at hk'
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
  have heq : ω 0 = ω 1 := by
    by_contra hne'
    have hδ : 0 < (ω 0 - ω 1) ^ 2 / 2 := by
      have := sub_ne_zero.2 hne'
      positivity
    set d : Fin 2 → ℝ := ![ω 0 - ω 1, -((ω 0 - ω 1) * (ω 0 + ω 1) / 2)] with hdd
    have hD0 := f_hasDerivAt_line hM 0 (hd 0) (hint 0) (d := d) (hω 0) (hk 0)
    have hD1 := f_hasDerivAt_line hM 1 (hd 1) (hint 1) (d := -d) (hω 1) (hk 1)
    have hv0 : 0 < (ω 0 * d 0 + d 1) / M.g 0 (ω 0) := by
      apply div_pos _ (c_pos hM 0 (relPrice_pos (hω 0)))
      have : ω 0 * d 0 + d 1 = (ω 0 - ω 1) ^ 2 / 2 := by
        simp only [hdd, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [this]
      exact hδ
    have hv1 : 0 < (ω 1 * (-d) 0 + (-d) 1) / M.g 1 (ω 1) := by
      apply div_pos _ (c_pos hM 1 (relPrice_pos (hω 1)))
      have : ω 1 * (-d) 0 + (-d) 1 = (ω 0 - ω 1) ^ 2 / 2 := by
        simp only [hdd, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [this]
      exact hδ
    have e0 := eventually_lt_of_hasDerivAt_pos hD0 hv0
    have e1 := eventually_lt_of_hasDerivAt_pos hD1 hv1
    have ep0 := (eventually_strictlyPositive_line (hint 0) d).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have ep1 := (eventually_strictlyPositive_line (hint 1) (-d)).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    obtain ⟨t, ht0, ht1, hp0, hp1⟩ := (e0.and (e1.and (ep0.and ep1))).exists
    simp only [zero_smul, add_zero] at ht0 ht1
    apply hne
    refine ⟨![z 0 + t • d, z 1 + t • -d], ⟨Fin.forall_fin_two.2 ⟨fun l => (hp0 l).le,
      fun l => (hp1 l).le⟩, ?_⟩, Fin.forall_fin_two.2 ⟨ht0.le, ht1.le⟩, 0, ht0⟩
    rw [← hsum]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_neg]
    abel
  refine ⟨![ω 0, 1], fun j => z j 1 / M.a j ![ω 0, 1] 1, relPrice_pos (hω 0),
    fun j => div_nonneg (hint j 1).le (hM.a_pos j _ 1 (relPrice_pos (hω 0))).le,
    Fin.forall_fin_two.2 ⟨hrep 0, ?_⟩, hsum⟩
  rw [heq]
  exact hrep 1

/-- An allocation supported by `w` with both firms' inputs `≫ 0` is an interior supported
allocation, and its factor proportions are the intensities at `w`. -/
theorem interiorSupport_of_supportedBy (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    {z : Fin 2 → Fin 2 → ℝ} (h : M.IsSupportedBy zbar w q z)
    (hint : ∀ j, StrictlyPositive (z j)) :
    M.IsInteriorSupport zbar w q ∧ ∀ j, z j 0 / z j 1 = M.factorRatio j w := by
  obtain ⟨hw, -, hz, hsum⟩ := h
  have hq : ∀ j, 0 < q j := by
    intro j
    have := hint j 0
    rw [hz j] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (hM.a_pos j w 0 hw).le]
  refine ⟨⟨hw, hq, by rw [← hz 0, ← hz 1]; exact hsum⟩, fun j => ?_⟩
  rw [hz j]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ (hq j).ne']
  rfl

/-- **Exercise 15.D.1(a)** (MWG, p. 533), for the Pareto set itself (smooth technologies): if at
one efficient allocation with both firms' inputs `≫ 0` firm 1 uses factor 1 more intensively,
it does so at every such efficient allocation of `z̄`. -/
theorem exercise_15_D_1a_pareto (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z z' : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j))
    (h' : M.IsEfficientAllocation zbar z') (hint' : ∀ j, StrictlyPositive (z' j))
    (hlt : z 1 0 / z 1 1 < z 0 0 / z 0 1) : z' 1 0 / z' 1 1 < z' 0 0 / z' 0 1 := by
  obtain ⟨w, q, hS⟩ := efficient_isSupported hM hs hd h hint
  obtain ⟨w', q', hS'⟩ := efficient_isSupported hM hs hd h' hint'
  obtain ⟨hI, hr⟩ := interiorSupport_of_supportedBy hM hS hint
  obtain ⟨hI', hr'⟩ := interiorSupport_of_supportedBy hM hS' hint'
  rw [hr, hr] at hlt
  rw [hr', hr']
  exact factorRatio_order_preserved hM hI hI' hlt

/-- **Section 15.D** (MWG, p. 533), the diagonal claim for the Pareto set (smooth technologies):
if one efficient allocation with both firms' inputs `≫ 0` lies on the diagonal, `z₁ = t z̄`, then
every point `(s z̄, (1 - s) z̄)` of the diagonal is efficient, and every efficient allocation with
both firms' inputs `≫ 0` lies on the diagonal: "the diagonal must be the Pareto set". -/
theorem diagonal_pareto_set_efficient (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hdiag : z 0 = t • zbar) :
    (∀ s : ℝ, 0 < s → s < 1 → M.IsEfficientAllocation zbar ![s • zbar, (1 - s) • zbar]) ∧
      ∀ z', M.IsEfficientAllocation zbar z' → (∀ j, StrictlyPositive (z' j)) →
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧ z' 0 = s • zbar := by
  obtain ⟨w, q, hS⟩ := efficient_isSupported hM hs hd h hint
  obtain ⟨hI, -⟩ := interiorSupport_of_supportedBy hM hS hint
  have hdiag' : q 0 • M.a 0 w = t • zbar := by rw [← hS.2.2.1 0]; exact hdiag
  have hD := diagonal_pareto_set hM hI ht0 ht1 hdiag'
  constructor
  · intro s hs0 hs1
    obtain ⟨hS2, h0⟩ := hD.1 s hs0 hs1
    obtain ⟨hw2, hq2, hsum2⟩ := hS2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum2 hq2
    refine supported_isEfficient hM (w := w) (q := ![s * q 0 / t, (1 - s) * q 1 / (1 - t)])
      ⟨hw2, fun j => (hq2 j).le, Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact h0.symm
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h0] at hsum2
      funext l
      have := congrFun hsum2 l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      module
  · intro z' h' hint'
    obtain ⟨w', q', hS'⟩ := efficient_isSupported hM hs hd h' hint'
    obtain ⟨hI', -⟩ := interiorSupport_of_supportedBy hM hS' hint'
    obtain ⟨s, hs0, hs1, hs⟩ := hD.2 w' q' hI'
    exact ⟨s, hs0, hs1, by rw [hS'.2.2.1 0]; exact hs⟩

/-! ### Footnote 16: Stolper-Samuelson without the global factor intensity condition -/

/-- **Footnote 16** (MWG, p. 536). The Stolper-Samuelson conclusion without the factor intensity
condition. Compare interior factor market equilibria (`q ≫ 0`, `q' ≫ 0`) for the same endowment
at output prices `p` and `p'` with `p'₁ > p₁`, `p'₂ = p₂`, where firm 1 is more intensive in
factor 1 at the initial equilibrium. Then `w'₁ > w₁` and `w'₂ < w₂`. By Exercise 15.D.1(a) the
intensity ranking also holds at `w'`, hence at every relative factor price between, so the ratio
of unit costs is increasing on that interval and the relative price of factor 1 rises. -/
theorem footnote_16 (hM : M.IsModel) {p p' zbar w w' q q' : Fin 2 → ℝ}
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p' zbar w' (fun j => q' j • M.a j w'))
    (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1)
    (hint : M.factorRatio 1 w < M.factorRatio 0 w) : w 0 < w' 0 ∧ w' 1 < w 1 := by
  have hw := h.1
  have hw' := h'.1
  obtain ⟨hc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hS : M.IsInteriorSupport zbar w q := ⟨hw, hq, by rw [← hsum, Fin.sum_univ_two]⟩
  have hS' : M.IsInteriorSupport zbar w' q' := ⟨hw', hq', by rw [← hsum', Fin.sum_univ_two]⟩
  obtain ⟨-, hb2⟩ := interiorSupport_between hM hS hint
  have hint' := factorRatio_order_preserved hM hS hS' hint
  obtain ⟨hb1', -⟩ := interiorSupport_between hM hS' hint'
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have hb2r : zbar 0 / zbar 1 < M.a 0 ![ω, 1] 0 / M.a 0 ![ω, 1] 1 := by
    rw [hωd, ← a_eq_rel hM 0 hw]
    exact hb2
  have hb1r : M.a 1 ![ω', 1] 0 / M.a 1 ![ω', 1] 1 < zbar 0 / zbar 1 := by
    rw [hωd', ← a_eq_rel hM 1 hw']
    exact hb1'
  have hp1pos : 0 < p 1 := by rw [hc 1]; exact c_pos hM 1 hw
  -- the relative factor price rises
  have hlt : ω < ω' := by
    by_contra hn
    rw [not_lt] at hn
    have hpos : ∀ t ∈ Set.Icc ω' ω,
        M.a 1 ![t, 1] 0 / M.a 1 ![t, 1] 1 < M.a 0 ![t, 1] 0 / M.a 0 ![t, 1] 1 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' ht.1
      have k0 := intensity_antitone hM 0 ht0 ht.2
      have k1 := intensity_antitone hM 1 hω' ht.1
      linarith
    have hderiv : ∀ t ∈ Set.Icc ω' ω, HasDerivAt (fun t => M.g 0 t / M.g 1 t)
        ((M.a 0 ![t, 1] 0 * M.g 1 t - M.g 0 t * M.a 1 ![t, 1] 0) / M.g 1 t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' ht.1
      exact (unitCost_hasDerivAt hM 0 ht0).div (unitCost_hasDerivAt hM 1 ht0)
        (c_pos hM 1 (relPrice_pos ht0)).ne'
    have hmono : StrictMonoOn (fun t => M.g 0 t / M.g 1 t) (Set.Icc ω' ω) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc ω' ω)
        (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      have htI := Set.Ioo_subset_Icc_self ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' htI.1
      rw [(hderiv t htI).deriv]
      have hpt := relPrice_pos ht0
      have hpp := hpos t htI
      rw [div_lt_div_iff₀ (hM.a_pos 1 _ 1 hpt) (hM.a_pos 0 _ 1 hpt)] at hpp
      apply div_pos _ (pow_pos (c_pos hM 1 hpt) 2)
      rw [g_eq, g_eq]
      nlinarith
    have hle := hmono.monotoneOn (Set.left_mem_Icc.2 hn) (Set.right_mem_Icc.2 hn) hn
    have e := c_ratio_eq_g hM hw
    have e' := c_ratio_eq_g hM hw'
    rw [← hωd] at e
    rw [← hωd'] at e'
    have : M.c 0 w / M.c 1 w < M.c 0 w' / M.c 1 w' := by
      rw [← hc 0, ← hc 1, ← hc' 0, ← hc' 1, hp1]
      exact div_lt_div_of_pos_right hp0 hp1pos
    rw [e, e'] at this
    linarith
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [hc 0, c_eq_g hM 0 hw, hωd]
  have e1 : p 1 = w 1 * M.g 1 ω := by rw [hc 1, c_eq_g hM 1 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [hc' 0, c_eq_g hM 0 hw', hωd']
  have e1' : p 1 = w' 1 * M.g 1 ω' := by rw [← hp1, hc' 1, c_eq_g hM 1 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hg1' : 0 < M.g 1 ω' := c_pos hM 1 (relPrice_pos hω')
  have hw1 := hw 1
  have hw1' := hw' 1
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  constructor
  · have hm := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hlt
    have hw0 : w 0 = p 0 * (ω / M.g 0 ω) := by
      have : w 1 * M.g 0 ω * (ω / M.g 0 ω) = w 1 * ω := by field_simp
      rw [e0, this, hωd]; field_simp
    have hw0' : w' 0 = p' 0 * (ω' / M.g 0 ω') := by
      have : w' 1 * M.g 0 ω' * (ω' / M.g 0 ω') = w' 1 * ω' := by field_simp
      rw [e0', this, hωd']; field_simp
    rw [hw0, hw0']
    have : 0 < ω / M.g 0 ω := div_pos hω hg0
    have : ω / M.g 0 ω < ω' / M.g 0 ω' := hm
    nlinarith
  · have hgm := (g_strictMono hM 1).lt_iff_lt hω hω' |>.2 hlt
    have hw1e : w 1 = p 1 / M.g 1 ω := by rw [e1]; field_simp
    have hw1e' : w' 1 = p 1 / M.g 1 ω' := by rw [e1']; field_simp
    rw [hw1e, hw1e']
    exact div_lt_div_of_pos_left hp1pos hg1 hgm

end TwoByTwo

theorem leontief_f0 (x : Fin 2 → ℝ) : leontiefModel.f 0 x = min (x 0 / 2) (x 1) := rfl

theorem leontief_f1 (x : Fin 2 → ℝ) : leontiefModel.f 1 x = min (x 0) (x 1 / 2) := rfl

/-- In the Leontief model with `z̄ = (3, 3)`, every allocation satisfies the full-employment bounds
`2q₁ + q₂ ≤ 3` and `q₁ + 2q₂ ≤ 3` on the outputs `qⱼ = fⱼ(zⱼ)`. -/
theorem leontief_output_bounds {z : Fin 2 → Fin 2 → ℝ} (hz : IsFactorAllocation ![3, 3] z) :
    2 * leontiefModel.f 0 (z 0) + leontiefModel.f 1 (z 1) ≤ 3 ∧
      leontiefModel.f 0 (z 0) + 2 * leontiefModel.f 1 (z 1) ≤ 3 := by
  obtain ⟨-, hsum⟩ := hz
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at s0 s1
  rw [leontief_f0, leontief_f1]
  have a1 := min_le_left (z 0 0 / 2) (z 0 1)
  have a2 := min_le_right (z 0 0 / 2) (z 0 1)
  have b1 := min_le_left (z 1 0) (z 1 1 / 2)
  have b2 := min_le_right (z 1 0) (z 1 1 / 2)
  constructor <;> linarith

/-- **Exercise 15.D.1(b)** (MWG, p. 533): false as printed for the model as formalized. In the
Leontief model (which satisfies all standing assumptions and the factor intensity condition) with
`z̄ = (3, 3)`, the Pareto set is not the diagonal (the diagonal allocation `((2, 2), (1, 1))`
producing `(1, 1/2)` is dominated), yet the two distinct allocations
`z = ((1, 1/2), (2, 5/2))` (outputs `(1/2, 5/4)`) and `z' = ((2, 1), (1, 2))` (outputs `(1, 1)`)
are both efficient and lie on the same ray from firm 1's origin (`z₁ = z'₁/2`). So a ray from an
origin can meet the Pareto set more than once. The corrected statement assumes differentiable
technologies (`TwoByTwo.exercise_15_D_1b`). -/
theorem exercise_15_D_1b_counterexample :
    leontiefModel.IsEfficientAllocation ![3, 3] ![![1, 1 / 2], ![2, 5 / 2]] ∧
      leontiefModel.IsEfficientAllocation ![3, 3] ![![2, 1], ![1, 2]] ∧
      (![![1, 1 / 2], ![2, 5 / 2]] : Fin 2 → Fin 2 → ℝ) 0 =
        (1 / 2 : ℝ) • (![![2, 1], ![1, 2]] : Fin 2 → Fin 2 → ℝ) 0 ∧
      (![![1, 1 / 2], ![2, 5 / 2]] : Fin 2 → Fin 2 → ℝ) ≠ ![![2, 1], ![1, 2]] ∧
      IsFactorAllocation ![3, 3] ![![2, 2], ![1, 1]] ∧
      (![![2, 2], ![1, 1]] : Fin 2 → Fin 2 → ℝ) 0 = (2 / 3 : ℝ) • ![3, 3] ∧
      ¬ leontiefModel.IsEfficientAllocation ![3, 3] ![![2, 2], ![1, 1]] := by
  have hA : IsFactorAllocation ![3, 3] ![![1, 1 / 2], ![2, 5 / 2]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have hB : IsFactorAllocation ![3, 3] ![![2, 1], ![1, 2]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have hD : IsFactorAllocation ![3, 3] ![![2, 2], ![1, 1]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have fA0 : leontiefModel.f 0 ![1, 1 / 2] = 1 / 2 := by rw [leontief_f0]; norm_num
  have fA1 : leontiefModel.f 1 ![2, 5 / 2] = 5 / 4 := by rw [leontief_f1]; norm_num [min_def]
  have fB0 : leontiefModel.f 0 ![2, 1] = 1 := by rw [leontief_f0]; norm_num
  have fB1 : leontiefModel.f 1 ![1, 2] = 1 := by rw [leontief_f1]; norm_num
  have fD0 : leontiefModel.f 0 ![2, 2] = 1 := by rw [leontief_f0]; norm_num [min_def]
  have fD1 : leontiefModel.f 1 ![1, 1] = 1 / 2 := by rw [leontief_f1]; norm_num [min_def]
  refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩, ?_, ?_, hD, ?_, ?_⟩
  · rintro ⟨z', hz', hge, j, hlt⟩
    have hb := leontief_output_bounds hz'
    have g0 := hge 0
    have g1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fA0, fA1] at g0 g1
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, fA0, fA1] at hlt <;> linarith
  · rintro ⟨z', hz', hge, j, hlt⟩
    have hb := leontief_output_bounds hz'
    have g0 := hge 0
    have g1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fB0, fB1] at g0 g1
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, fB0, fB1] at hlt <;> linarith
  · funext l
    fin_cases l <;> norm_num
  · intro he
    have := congrFun (congrFun he 0) 0
    norm_num at this
  · funext l
    fin_cases l <;> norm_num
  · rintro ⟨-, hne⟩
    refine hne ⟨![![2, 1], ![1, 2]], hB, Fin.forall_fin_two.2 ⟨?_, ?_⟩, 1, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fB0, fB1, fD0, fD1] <;> norm_num

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected statement for the Cobb-Douglas model of
Exercise 15.D.8 (differentiable along rays): a ray from either firm's origin meets the interior
supported (= interior efficient) allocations off the diagonal at most once. -/
theorem exercise_15_D_1b_cdModel {zbar w q w' q' : Fin 2 → ℝ}
    (h : cdModel.IsInteriorSupport zbar w q) (h' : cdModel.IsInteriorSupport zbar w' q')
    (hne : cdModel.factorRatio 0 w ≠ cdModel.factorRatio 1 w) (j : Fin 2)
    (hray : cdModel.factorRatio j w = cdModel.factorRatio j w') :
    (fun k => q k • cdModel.a k w) = fun k => q' k • cdModel.a k w' :=
  TwoByTwo.exercise_15_D_1b cdModel_isModel (fun k => cdtModel_rayDifferentiable _ k) h h' hne j
    hray

/-- **Figure 15.D.2(b)** (MWG, p. 533), instance: in the Cobb-Douglas model of Exercise 15.D.8
every efficient allocation with both firms' inputs `≫ 0` is supported by common factor
prices. -/
theorem efficient_isSupported_cdModel {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : cdModel.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) :
    cdModel.IsSupportedAllocation zbar z :=
  TwoByTwo.efficient_isSupported cdModel_isModel (cdtModel_raySurjective cdModel_alpha)
    (fun k => cdtModel_rayDifferentiable _ k) h hint

/-- **Footnote 16** (MWG, p. 536), non-vacuity: in the Leontief model with `z̄ = (3, 3)`, the
interior equilibria at `p = (3, 3)` (`w = (1, 1)`) and `p' = (4, 3)` (`w' = (5/3, 2/3)`), with
outputs `(1, 1)`, satisfy the hypotheses of `TwoByTwo.footnote_16`, which yields
`w'₁ > w₁` and `w'₂ < w₂`. -/
theorem footnote_16_leontief :
    IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) ∧
      IsFactorEqm leontiefModel.f ![4, 3] ![3, 3] ![5 / 3, 2 / 3]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![5 / 3, 2 / 3]) ∧
      leontiefModel.factorRatio 1 ![1, 1] < leontiefModel.factorRatio 0 ![1, 1] ∧
      (![1, 1] : Fin 2 → ℝ) 0 < (![5 / 3, 2 / 3] : Fin 2 → ℝ) 0 ∧
      (![5 / 3, 2 / 3] : Fin 2 → ℝ) 1 < (![1, 1] : Fin 2 → ℝ) 1 := by
  have hq : ∀ j, 0 < (![1, 1] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> norm_num
  have h1 : IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
      (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) :=
    leontief_instances.2.2.1
  have hw' : StrictlyPositive (![5 / 3, 2 / 3] : Fin 2 → ℝ) := fun l => by
    fin_cases l <;> norm_num
  have h2 : IsFactorEqm leontiefModel.f ![4, 3] ![3, 3] ![5 / 3, 2 / 3]
      (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![5 / 3, 2 / 3]) := by
    refine (TwoByTwo.interior_eqm_iff leontiefModel_isModel hw' hq).2
      ⟨fun j => (leontief_instances.2.1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]
  have h3 : leontiefModel.factorRatio 1 ![1, 1] < leontiefModel.factorRatio 0 ![1, 1] := by
    norm_num [TwoByTwo.factorRatio, leontiefModel]
  exact ⟨h1, h2, h3, TwoByTwo.footnote_16 leontiefModel_isModel h1 h2 hq hq (by norm_num)
    (by norm_num) h3⟩

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 15.D.4(b) for a general 2 × 2 model (MWG p. 543)

The closed economy of Exercise 15.D.4 (`IsClosedEqm`, `ClosedEconomy.lean`) with an arbitrary
2 × 2 technology satisfying the standing assumptions and the factor intensity condition (good 1
relatively intensive in factor 1), consumer 1 owning one unit of factor 1 and caring only for
good 2, consumer 2 owning one unit of factor 2 and caring only for good 1.

* **Exercise 15.D.4(b)** (`TwoByTwo.exercise_15_D_4b_general`): any two equilibria with strictly
  positive factor prices have proportional prices and the same outputs and consumptions: there is
  at most one equilibrium. With `w ≫ 0` both goods are produced, consumer 2's budget and the
  clearing of factor 2 give `w₁ z₁₁ = w₂ z₂₂` (the value of factor 1 used in good 1 equals the
  value of factor 2 used in good 2), and along the supported allocations of `z̄ = (1, 1)`
  `ω z₁₁ - z₂₂` is strictly increasing in `ω = w₁/w₂` (`TwoByTwo.ex15D4b_not_relPrice_lt`).
* Departure: equilibria with a zero factor price are not covered (the standing assumptions say
  nothing about `aⱼ(w)` unless `w ≫ 0`); for the Leontief technologies `exercise_15_D_4b` covers
  them as well.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

namespace TwoByTwo

variable {M : TwoByTwo}

/-- **Exercise 15.D.4(b)** (MWG, p. 543). The structure of an equilibrium with `w ≫ 0`: prices
equal unit costs, the outputs `q ≫ 0` employ `z̄ = (1, 1)` fully, consumer 1 spends `w₁` on good 2
and consumer 2 spends `w₂` on good 1, and `w₁ (q₁ a₁₁) = w₂ (q₂ a₂₂)`. -/
theorem ex15D4b_eqm_facts {p w q : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (hw : StrictlyPositive w) :
    (∀ j, p j = M.c j w) ∧ M.IsInteriorSupport ![1, 1] w q ∧
      w 0 * (q 0 * M.a 0 w 0) = w 1 * (q 1 * M.a 1 w 1) ∧
      x = ![Pi.single 1 (w 0 / p 1), Pi.single 0 (w 1 / p 0)] := by
  obtain ⟨hp, -, -, -, hqp, -, hb, hx, hg⟩ := h
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hx0 := hx 0
  have hx1 := hx 1
  simp only [hown] at hx0 hx1
  rw [onlyGood_demand hp (hw 0).le] at hx0
  rw [onlyGood_demand hp (hw 1).le] at hx1
  have hx0' : x 0 = Pi.single 1 (w 0 / p 1) := hx0
  have hx1' : x 1 = Pi.single 0 (w 1 / p 0) := hx1
  have hq0 : q 0 = w 1 / p 0 := by
    have := hg 0; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hq1 : q 1 = w 0 / p 1 := by
    have := hg 1; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hp0 := hp 0
  have hp1 := hp 1
  have hq0pos : 0 < q 0 := by rw [hq0]; exact div_pos (hw 1) hp0
  have hq1pos : 0 < q 1 := by rw [hq1]; exact div_pos (hw 0) hp1
  have hpc : ∀ j, p j = M.c j w := Fin.forall_fin_two.2 ⟨hqp 0 hq0pos, hqp 1 hq1pos⟩
  have hcl : ∀ l, q 0 * M.a 0 w l + q 1 * M.a 1 w l = 1 := by
    intro l
    have := hb l (hw l)
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at this
    rw [this]
    fin_cases l <;> simp [ex15D4own]
  refine ⟨hpc, ⟨hw, Fin.forall_fin_two.2 ⟨hq0pos, hq1pos⟩, ?_⟩, ?_, ?_⟩
  · funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcl l]
    fin_cases l <;> simp
  · have E1 : p 0 * q 0 = w 1 := by rw [hq0]; field_simp
    have E2 : p 0 = w 0 * M.a 0 w 0 + w 1 * M.a 0 w 1 := by rw [hpc 0, c, dot_two]
    linear_combination -q 0 * E2 + E1 - w 1 * hcl 1
  · funext i
    fin_cases i
    · exact hx0'
    · exact hx1'

/-- **Exercise 15.D.4(b)** (MWG, p. 543), the key step. Under factor intensity, two interior
supported allocations of `z̄ = (1, 1)` both satisfying `w₁ z₁₁ = w₂ z₂₂` cannot have different
relative factor prices: as `ω = w₁/w₂` rises the intensities fall, so `z₁₁ = r₁(1 - r₂)/(r₁ - r₂)`
does not fall and `z₂₂ = (r₁ - 1)/(r₁ - r₂)` does not rise, and `ω z₁₁ - z₂₂` is strictly
increasing. -/
theorem ex15D4b_not_relPrice_lt (hM : M.IsModel) (hFI : M.FactorIntensity)
    {w q w' q' : Fin 2 → ℝ} (hS : M.IsInteriorSupport ![1, 1] w q)
    (hS' : M.IsInteriorSupport ![1, 1] w' q')
    (hb : w 0 * (q 0 * M.a 0 w 0) = w 1 * (q 1 * M.a 1 w 1))
    (hb' : w' 0 * (q' 0 * M.a 0 w' 0) = w' 1 * (q' 1 * M.a 1 w' 1)) :
    ¬ w 0 / w 1 < w' 0 / w' 1 := by
  intro hlt
  have hw := hS.1
  have hw' := hS'.1
  have hint : M.factorRatio 1 w < M.factorRatio 0 w := hFI w hw
  have hint' : M.factorRatio 1 w' < M.factorRatio 0 w' := hFI w' hw'
  have hρ : (![1, 1] : Fin 2 → ℝ) 0 / (![1, 1] : Fin 2 → ℝ) 1 = 1 := by norm_num
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM hS hint
  obtain ⟨hb1', hb2'⟩ := interiorSupport_between hM hS' hint'
  rw [hρ] at hb1 hb2 hb1' hb2'
  have ha0 := factorRatio_antitone hM 0 hw hw' hlt.le
  have ha1 := factorRatio_antitone hM 1 hw hw' hlt.le
  obtain ⟨eS, eT⟩ := interiorSupport_identities hM hS
  obtain ⟨eS', eT'⟩ := interiorSupport_identities hM hS'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at eS eT eS' eT'
  have hbpos : 0 < M.factorRatio 1 w := div_pos (hM.a_pos 1 w 0 hw) (hM.a_pos 1 w 1 hw)
  have c0 : q 0 * M.a 0 w 0 = M.factorRatio 0 w * (q 0 * M.a 0 w 1) := by
    have := (hM.a_pos 0 w 1 hw).ne'
    unfold factorRatio
    field_simp
  have c0' : q' 0 * M.a 0 w' 0 = M.factorRatio 0 w' * (q' 0 * M.a 0 w' 1) := by
    have := (hM.a_pos 0 w' 1 hw').ne'
    unfold factorRatio
    field_simp
  have hZpos : 0 < q 0 * M.a 0 w 0 := mul_pos (hS.2.1 0) (hM.a_pos 0 w 0 hw)
  rw [c0] at hb
  rw [c0'] at hb'
  rw [c0] at hZpos
  set a := M.factorRatio 0 w
  set b := M.factorRatio 1 w
  set a' := M.factorRatio 0 w'
  set b' := M.factorRatio 1 w'
  set S := q 0 * M.a 0 w 1
  set S' := q' 0 * M.a 0 w' 1
  set T := q 1 * M.a 1 w 1
  set T' := q' 1 * M.a 1 w' 1
  have hP : 0 < (a - b) * (a' - b') * (a' - b) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  -- `z₁₁ = a S` does not fall
  have hZ : a * S ≤ a' * S' := by
    have key : (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) =
        a' * (b - b') * (a' - 1) * (a - b) + (1 - b) * b * (a - a') * (a' - b') := by
      linear_combination (a' * (a - b) * (a' - b)) * eS' - (a * (a' - b') * (a' - b)) * eS
    have hR : 0 ≤ a' * (b - b') * (a' - 1) * (a - b) + (1 - b) * b * (a - a') * (a' - b') := by
      have ha'pos : 0 < a' := by linarith
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg (mul_nonneg ha'pos.le (by linarith)) (by linarith))
          (by linarith)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hbpos.le) (by linarith))
          (by linarith)
    by_contra hc
    rw [not_le] at hc
    have : (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hP
    linarith
  -- `z₂₂ = T` does not rise
  have hT : T' ≤ T := by
    have key : (T - T') * ((a - b) * (a' - b') * (a' - b)) =
        (a - a') * (1 - b) * (a' - b') + (a' - 1) * (b - b') * (a - b) := by
      linear_combination ((a' - b') * (a' - b)) * eT - ((a - b) * (a' - b)) * eT'
    have hR : 0 ≤ (a - a') * (1 - b) * (a' - b') + (a' - 1) * (b - b') * (a - b) :=
      add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
    by_contra hc
    rw [not_le] at hc
    have : (T - T') * ((a - b) * (a' - b') * (a' - b)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hP
    linarith
  have hw1 := hw 1
  have hw1' := hw' 1
  have hw0' := hw' 0
  rw [div_lt_div_iff₀ hw1 hw1'] at hlt
  have k1 : w 1 * (w' 0 * (a' * S')) = w 1 * (w' 1 * T') := by rw [hb']
  have k2 : w' 1 * (w 0 * (a * S)) = w' 1 * (w 1 * T) := by rw [hb]
  have k3 : w 1 * w' 1 * T' ≤ w 1 * w' 1 * T := mul_le_mul_of_nonneg_left hT (by positivity)
  have k4 : w 0 * w' 1 * (a * S) < w' 0 * w 1 * (a * S) := mul_lt_mul_of_pos_right hlt hZpos
  have k5 : w' 0 * w 1 * (a * S) ≤ w' 0 * w 1 * (a' * S') :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
  nlinarith

/-- **Exercise 15.D.4(b)** (MWG, p. 543), general technologies. Under the standing assumptions and
the factor intensity condition, with consumer 1 (owner of factor 1) caring only for good 2 and
consumer 2 (owner of factor 2) only for good 1, any two equilibria with strictly positive factor
prices have proportional prices (`w' = t w`, `p' = t p`, `t > 0`), the same outputs and the same
consumptions: there is at most one equilibrium. -/
theorem exercise_15_D_4b_general (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w q p' w' q' : Fin 2 → ℝ} {x x' : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (h' : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p' w' q' x')
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') :
    ∃ t : ℝ, 0 < t ∧ w' = t • w ∧ p' = t • p ∧ q' = q ∧ x' = x := by
  obtain ⟨hpc, hS, hb, hx⟩ := ex15D4b_eqm_facts h hw
  obtain ⟨hpc', hS', hb', hx'⟩ := ex15D4b_eqm_facts h' hw'
  have hω : w 0 / w 1 = w' 0 / w' 1 := by
    rcases lt_trichotomy (w 0 / w 1) (w' 0 / w' 1) with hl | he | hg
    · exact absurd hl (ex15D4b_not_relPrice_lt hM hFI hS hS' hb hb')
    · exact he
    · exact absurd hg (ex15D4b_not_relPrice_lt hM hFI hS' hS hb' hb)
  have ha : ∀ k, M.a k w = M.a k w' := fun k => by
    rw [a_eq_rel hM k hw, a_eq_rel hM k hw', hω]
  have hD : M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 ≠ 0 :=
    (FactorIntensity.det_pos hM hFI hw).ne'
  have hs : ∑ k, q k • M.a k w = ![1, 1] := by rw [Fin.sum_univ_two]; exact hS.2.2
  have hs' : ∑ k, q' k • M.a k w = ![1, 1] := by
    rw [Fin.sum_univ_two, ha 0, ha 1]
    exact hS'.2.2
  have hc := outputs_cramer (a := fun k => M.a k w) hD hs
  have hc' := outputs_cramer (a := fun k => M.a k w) hD hs'
  have hq : q' = q := by
    funext k
    fin_cases k
    · exact hc'.1.trans hc.1.symm
    · exact hc'.2.trans hc.2.symm
  have hw1 := hw 1
  have hw1' := hw' 1
  set t := w' 1 / w 1 with htd
  have ht : 0 < t := div_pos hw1' hw1
  have hwt : w' = t • w := by
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, htd]
      rw [div_eq_div_iff hw1.ne' hw1'.ne'] at hω
      field_simp
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, htd]
      field_simp
  have hpt : p' = t • p := by
    funext j
    rw [hpc' j, hwt, c_smul hM j hw ht, Pi.smul_apply, smul_eq_mul, hpc j]
  refine ⟨t, ht, hwt, hpt, hq, ?_⟩
  rw [hx, hx', hwt, hpt]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ ht.ne', mul_div_mul_left _ _ ht.ne']

end TwoByTwo

/-- **Exercise 15.D.4(b)** (MWG, p. 543), instance: the general theorem applies to the Cobb-Douglas
technologies of Exercise 15.D.8 (`cdModel`, good 1 intensive in factor 1). -/
theorem exercise_15_D_4b_cdModel {p w q p' w' q' : Fin 2 → ℝ} {x x' : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm cdModel (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (h' : IsClosedEqm cdModel (fun i => onlyGood (![1, 0] i)) ex15D4own p' w' q' x')
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') :
    ∃ t : ℝ, 0 < t ∧ w' = t • w ∧ p' = t • p ∧ q' = q ∧ x' = x :=
  TwoByTwo.exercise_15_D_4b_general cdModel_isModel cdModel_factorIntensity h h' hw hw'

end MWG.GeneralEquilibriumExamples

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Pareto curve of an Edgeworth box (MWG Exercises 15.B.7 and 15.B.10(d), pp. 541-542)

Standing hypotheses (`ExchangeEconomy.ParetoCurveHyp`): an Edgeworth box economy with consumption
sets `ℝ²₊`, utilities continuous on `ℝ²₊`, strongly monotone and representing strictly convex
preferences, and a strictly positive total endowment `ω̄`. Write `a = u₁(0)`, `b = u₁(ω̄)`.

* **Exercise 15.B.7** (first part): the Pareto set is connected (`exercise_15_B_7_connected`).
  We prove more: consumer 1's utility is a homeomorphism from the Pareto set onto `[a, b]`
  (`exercise_15_B_7_homeomorph`). Its inverse is the *Pareto curve* `ExchangeEconomy.paretoCurve`,
  continuous on all of `ℝ` (`pc_continuous_paretoCurve`, values clamped to `[a, b]`), with every
  Pareto optimum on it (`pc_eq_paretoCurve`). The Pareto set is compact (`pc_isCompact_paretoSet`).
* **Exercise 15.B.7** (second part): with homothetic preferences as well, the Pareto set lies
  weakly on one side of the diagonal of the box (`exercise_15_B_7_homothetic`; weakly, since the
  two origins are always on the diagonal), and if a Pareto optimum other than the two origins lies
  on the diagonal, the Pareto set is the whole diagonal `{(s ω̄, (1 - s) ω̄) : s ∈ [0, 1]}`
  (`exercise_15_B_7_diagonal`, `ExchangeEconomy.diagonalAllocation`). The key step: homothetic,
  continuous, strongly monotone preferences rank `s y` against `s x` as they rank `y` against `x`
  (`pc_homothetic_le`, `pc_homothetic_lt`), so the supporting prices of one diagonal optimum
  support every diagonal allocation (`pc_diagonal_po`).
* **Exercise 15.B.10(d)**: if `(p', x')` is a Walrasian equilibrium after a transfer `z ≥ 0` to
  consumer 1 (endowments `ω₁ + z`, `ω₂ - z`, with `ω₁ ≥ 0`), then before the transfer there is a
  Walrasian equilibrium (with `p ≫ 0`) at which consumer 1's utility is no higher than at `x'`
  (`exercise_15_B_10d_lower_eqm`); hence a transfer paradox (consumer 1 strictly worse off than at
  some pre-transfer equilibrium) forces multiple equilibria before the transfer
  (`exercise_15_B_10d`). The book's graphical hint is made rigorous by a connectedness argument
  along the Pareto curve with normalized quasi-equilibrium supporting prices
  (`ExchangeEconomy.QuasiSupports`, closed graph `pc_isClosed_quasiSupports`), which are then
  shown to be strictly positive equilibrium prices (`pc_quasiSupports_pos`,
  `pc_walras_of_quasiSupports`). Departure: the hint's "even lower" level of utility is proved in
  the weak form "no higher" (`≤`). The book's "(but, be warned, not more generally)" is a remark.
* Instance: both consumers with `u = √x₁ + √x₂` and endowments `(1, 0)`, `(0, 1)` satisfy all
  hypotheses (`sqrtEconomy_hyp`, `sqrtEconomy_homothetic`); the Pareto set is the diagonal
  (`sqrtEconomy_paretoSet`); after the transfer `z = (0, 1/2)` there is an equilibrium
  (`sqrtEconomy_transfer_eqm`) to which the theorem of Exercise 15.B.10(d) applies
  (`sqrtEconomy_15_B_10d`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-- **Exercise 15.B.7** (MWG, p. 541). The standing hypotheses on an Edgeworth box economy:
consumption sets `ℝ²₊`, continuous, strongly monotone utilities representing strictly convex
preferences, and a strictly positive total endowment. -/
structure ExchangeEconomy.ParetoCurveHyp (E : EdgeworthEconomy) : Prop where
  /-- Consumption sets `ℝ²₊`. -/
  X_eq : ∀ i, E.X i = nonnegOrthant 2
  /-- Utilities continuous on `ℝ²₊`. -/
  cont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant 2)
  /-- Strongly monotone utilities. -/
  mono : ∀ i, UtilityStronglyMonotone (E.u i)
  /-- Strictly convex preferences. -/
  sconv : ∀ i, PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (E.u i))
  /-- `ω̄ ≫ 0`. -/
  ω_pos : ∀ l, 0 < E.totalEndowment l

/-! ### General lemmas -/

/-- Shrinking a bundle a little keeps a continuous utility above `c`. -/
theorem pc_exists_shrink {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    {z : Fin L → ℝ} (hz : z ∈ nonnegOrthant L) {c : ℝ} (hcz : c < u z) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ c < u ((1 - t) • z) := by
  have hg : Continuous fun t : ℝ => (1 - t) • z :=
    (continuous_const.sub continuous_id).smul continuous_const
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • z ∈ nonnegOrthant L := by
    intro t ht l
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith [ht.2]) (hz l)
  have h0 : c < u ((1 - 0 : ℝ) • z) := by simpa using hcz
  exact exists_pos_continuous_lt hc hg hmem h0

/-- Adding a nonzero bundle `z ≥ 0` strictly raises a strongly monotone utility. -/
theorem pc_lt_add {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hm : UtilityStronglyMonotone u)
    {w z : Fin L → ℝ} (hw : w ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) (hz0 : z ≠ 0) :
    u w < u (w + z) :=
  hm.lt hw (fun l => le_add_of_nonneg_right (hz l)) fun he => hz0 (by
    have := congrArg (· - w) he
    simpa using this)

/-- `t • z ∈ ℝ^L₊` for `t ≥ 0`, `z ∈ ℝ^L₊`. -/
theorem pc_smul_mem {L : ℕ} {z : Fin L → ℝ} (hz : z ∈ nonnegOrthant L) {t : ℝ} (ht : 0 ≤ t) :
    t • z ∈ nonnegOrthant L := fun l => by
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg ht (hz l)

variable {E : EdgeworthEconomy}

/-- Box membership in coordinates. -/
theorem pc_inBox_iff (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.InBox x ↔ x 0 ∈ nonnegOrthant 2 ∧ x 1 ∈ nonnegOrthant 2 ∧
      x 0 + x 1 = E.totalEndowment := by
  simp only [ExchangeEconomy.InBox, ExchangeEconomy.IsAllocation, h.X_eq, Fin.forall_fin_two,
    Fin.sum_univ_two, and_assoc]

/-- Box membership, entrywise. -/
theorem pc_inBox_iff' (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.InBox x ↔ (∀ i l, 0 ≤ x i l) ∧ x 0 + x 1 = E.totalEndowment := by
  rw [pc_inBox_iff h, Fin.forall_fin_two, ← and_assoc]
  rfl

/-- In the box, `x₁ ≤ ω̄`. -/
theorem pc_le_total (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) :
    x 0 ≤ E.totalEndowment := by
  obtain ⟨-, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  intro l
  rw [← hs, Pi.add_apply]
  linarith [h1 l]

/-- `ω̄ ∈ ℝ²₊`. -/
theorem pc_total_mem (h : E.ParetoCurveHyp) : E.totalEndowment ∈ nonnegOrthant 2 :=
  fun l => (h.ω_pos l).le

/-- `0 ∈ ℝ²₊`. -/
theorem pc_zero_mem : (0 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun _ => le_rfl

/-- Consumer 1 gains strictly from a transfer of part of consumer 1's bundle to consumer 2,
keeping consumer 1 above `c ≥ u₁(0)`; consumer 2 then gains strictly. -/
theorem pc_transfer0 (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) {c : ℝ}
    (hc : c < E.u 0 (x 0)) (hc0 : E.u 0 0 ≤ c) :
    ∃ x', E.InBox x' ∧ c < E.u 0 (x' 0) ∧ E.u 1 (x 1) < E.u 1 (x' 1) := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hne : x 0 ≠ 0 := by
    intro he
    rw [he] at hc
    linarith
  obtain ⟨t, ht0, ht1, hlt⟩ := pc_exists_shrink (h.cont 0) h0 hc
  have htz0 : t • x 0 ≠ 0 := smul_ne_zero ht0.ne' hne
  refine ⟨![(1 - t) • x 0, x 1 + t • x 0], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩, by simpa using hlt,
    by simpa using pc_lt_add (h.mono 1) h1 (pc_smul_mem h0 ht0.le) htz0⟩
  · simpa using pc_smul_mem h0 (by linarith)
  · intro l
    simp only [Matrix.cons_val_one]
    exact add_nonneg (h1 l) (pc_smul_mem h0 ht0.le l)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hs]
    module

/-- Mirror image of `pc_transfer0`: part of consumer 2's bundle goes to consumer 1. -/
theorem pc_transfer1 (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) {c : ℝ}
    (hc : c < E.u 1 (x 1)) (hc0 : E.u 1 0 ≤ c) :
    ∃ x', E.InBox x' ∧ E.u 0 (x 0) < E.u 0 (x' 0) ∧ c < E.u 1 (x' 1) := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hne : x 1 ≠ 0 := by
    intro he
    rw [he] at hc
    linarith
  obtain ⟨t, ht0, ht1, hlt⟩ := pc_exists_shrink (h.cont 1) h1 hc
  have htz0 : t • x 1 ≠ 0 := smul_ne_zero ht0.ne' hne
  refine ⟨![x 0 + t • x 1, (1 - t) • x 1], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩,
    by simpa using pc_lt_add (h.mono 0) h0 (pc_smul_mem h1 ht0.le) htz0, by simpa using hlt⟩
  · intro l
    simp only [Matrix.cons_val_zero, Pi.add_apply]
    exact add_nonneg (h0 l) (pc_smul_mem h1 ht0.le l)
  · simpa using pc_smul_mem h1 (by linarith)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hs]
    module

/-- Pareto optimality equals weak Pareto optimality (no allocation in the box makes both
consumers strictly better off). -/
theorem pc_isParetoOptimal_iff (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.IsParetoOptimal x ↔ E.InBox x ∧
      ∀ x', E.InBox x' → ¬ (E.u 0 (x 0) < E.u 0 (x' 0) ∧ E.u 1 (x 1) < E.u 1 (x' 1)) := by
  constructor
  · rintro ⟨hb, hno⟩
    refine ⟨hb, fun x' hx' ⟨h0, h1⟩ => hno ⟨x', hx', ?_, 0, h0⟩⟩
    rw [Fin.forall_fin_two]
    exact ⟨h0.le, h1.le⟩
  · rintro ⟨hb, hno⟩
    refine ⟨hb, ?_⟩
    rintro ⟨x', hx', hle, i, hi⟩
    rw [Fin.forall_fin_two] at hle
    obtain ⟨hm0, hm1, -⟩ := (pc_inBox_iff h x).1 hb
    have hge0 : E.u 0 0 ≤ E.u 0 (x 0) := (h.mono 0).le pc_zero_mem hm0
    have hge1 : E.u 1 0 ≤ E.u 1 (x 1) := (h.mono 1).le pc_zero_mem hm1
    have hcases : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hcases with rfl | rfl
    · obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer0 h hx' hi hge0
      exact hno x'' hx'' ⟨h0, lt_of_le_of_lt hle.2 h1⟩
    · obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer1 h hx' hi hge1
      exact hno x'' hx'' ⟨lt_of_le_of_lt hle.1 h0, h1⟩

/-- Every Pareto optimum gives consumer 1 a utility in `[u₁(0), u₁(ω̄)]`. -/
theorem pc_po_bounds (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.IsParetoOptimal x) :
    E.u 0 0 ≤ E.u 0 (x 0) ∧ E.u 0 (x 0) ≤ E.u 0 E.totalEndowment := by
  obtain ⟨h0, -, -⟩ := (pc_inBox_iff h x).1 hx.1
  exact ⟨(h.mono 0).le pc_zero_mem h0, (h.mono 0).le h0 (pc_le_total h hx.1)⟩

/-- `u₁(0) ≤ u₁(ω̄)`. -/
theorem pc_a_le_b (h : E.ParetoCurveHyp) : E.u 0 0 ≤ E.u 0 E.totalEndowment :=
  (h.mono 0).le pc_zero_mem (pc_total_mem h)

/-- The set of box allocations is closed. -/
theorem pc_isClosed_box (h : E.ParetoCurveHyp) : IsClosed {x : Fin 2 → Fin 2 → ℝ | E.InBox x} := by
  simp only [pc_inBox_iff' h, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun l =>
    isClosed_le continuous_const (by fun_prop)).inter (isClosed_eq (by fun_prop) continuous_const)

/-- The set of box allocations is compact. -/
theorem pc_isCompact_box (h : E.ParetoCurveHyp) :
    IsCompact {x : Fin 2 → Fin 2 → ℝ | E.InBox x} := by
  refine (isCompact_Icc (a := (0 : Fin 2 → Fin 2 → ℝ))
    (b := fun _ => E.totalEndowment)).of_isClosed_subset
    (pc_isClosed_box h) fun x hx => ⟨fun i l => ?_, fun i l => ?_⟩
  · exact ((pc_inBox_iff' h x).1 hx).1 i l
  · obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
    have hl := congrFun hs l
    simp only [Pi.add_apply] at hl
    fin_cases i
    · simp only [Fin.zero_eta]
      linarith [h1 l]
    · simp only [Fin.mk_one]
      linarith [h0 l]

/-- `x ↦ u₁(x₁)` is continuous on the box. -/
theorem pc_continuousOn_u (h : E.ParetoCurveHyp) (i : Fin 2) :
    ContinuousOn (fun x : Fin 2 → Fin 2 → ℝ => E.u i (x i)) {x | E.InBox x} :=
  (h.cont i).comp (continuous_apply i).continuousOn fun x hx => by
    rw [← h.X_eq i]
    exact hx.1 i

/-! ### Exercise 15.B.7: the Pareto set is the graph of a homeomorphism onto `[a, b]` -/

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is closed. -/
theorem pc_isClosed_paretoSet (h : E.ParetoCurveHyp) : IsClosed E.paretoSet := by
  set B := {x : Fin 2 → Fin 2 → ℝ | E.InBox x}
  have hS : E.paretoSet = B ∩ ⋂ x' ∈ B,
      ((B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 0 (x 0)) ⁻¹' Set.Ici (E.u 0 (x' 0))) ∪
        (B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 1 (x 1)) ⁻¹' Set.Ici (E.u 1 (x' 1)))) := by
    ext x
    simp only [ExchangeEconomy.paretoSet, Set.mem_ofPred_eq, pc_isParetoOptimal_iff h,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_preimage, Set.mem_Ici, B,
      not_and_or, not_lt]
    constructor
    · rintro ⟨hb, hno⟩
      exact ⟨hb, fun x' hx' => (hno x' hx').imp (fun h' => ⟨hb, h'⟩) fun h' => ⟨hb, h'⟩⟩
    · rintro ⟨hb, hno⟩
      exact ⟨hb, fun x' hx' => (hno x' hx').imp (fun h' => h'.2) fun h' => h'.2⟩
  rw [hS]
  refine (pc_isClosed_box h).inter (isClosed_biInter fun x' _ => ?_)
  exact ((pc_continuousOn_u h 0).preimage_isClosed_of_isClosed (pc_isClosed_box h)
    isClosed_Ici).union
    ((pc_continuousOn_u h 1).preimage_isClosed_of_isClosed (pc_isClosed_box h) isClosed_Ici)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is compact. -/
theorem pc_isCompact_paretoSet (h : E.ParetoCurveHyp) : IsCompact E.paretoSet :=
  (pc_isCompact_box h).of_isClosed_subset (pc_isClosed_paretoSet h) fun _ hx => hx.1

/-- **Exercise 15.B.7** (MWG, p. 541). Two Pareto optima giving consumer 1 the same utility are
equal (strict convexity: otherwise their midpoint is better for both consumers). -/
theorem pc_po_injective (h : E.ParetoCurveHyp) {x y : Fin 2 → Fin 2 → ℝ}
    (hx : E.IsParetoOptimal x) (hy : E.IsParetoOptimal y) (he : E.u 0 (x 0) = E.u 0 (y 0)) :
    x = y := by
  obtain ⟨hx0, hx1, hxs⟩ := (pc_inBox_iff h x).1 hx.1
  obtain ⟨hy0, hy1, hys⟩ := (pc_inBox_iff h y).1 hy.1
  have he1 : E.u 1 (x 1) = E.u 1 (y 1) := by
    rcases lt_trichotomy (E.u 1 (x 1)) (E.u 1 (y 1)) with hlt | heq | hgt
    · exact absurd ⟨y, hy.1, Fin.forall_fin_two.2 ⟨he.le, hlt.le⟩, 1, hlt⟩ hx.2
    · exact heq
    · exact absurd ⟨x, hx.1, Fin.forall_fin_two.2 ⟨he.ge, hgt.le⟩, 1, hgt⟩ hy.2
  have h0 : x 0 = y 0 := by
    by_contra hne
    have hne1 : x 1 ≠ y 1 := by
      intro h1
      apply hne
      have : x 0 + x 1 = y 0 + y 1 := hxs.trans hys.symm
      rw [h1] at this
      exact add_right_cancel this
    set m : Fin 2 → Fin 2 → ℝ := fun k => (1 / 2 : ℝ) • x k + (1 - 1 / 2 : ℝ) • y k with hm
    have hmm : ∀ k, x k ∈ nonnegOrthant 2 → y k ∈ nonnegOrthant 2 → m k ∈ nonnegOrthant 2 :=
      fun k hxk hyk l => by
        simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [hxk l, hyk l]
    have g0 : E.u 0 (x 0) < E.u 0 (m 0) :=
      not_le.1 (h.sconv 0 (x 0) hx0 (x 0) hx0 (y 0) hy0 le_rfl he.le hne (1 / 2) (by norm_num)
        (by norm_num)).2
    have g1 : E.u 1 (x 1) < E.u 1 (m 1) :=
      not_le.1 (h.sconv 1 (x 1) hx1 (x 1) hx1 (y 1) hy1 le_rfl he1.le hne1 (1 / 2) (by norm_num)
        (by norm_num)).2
    refine hx.2 ⟨m, (pc_inBox_iff h m).2 ⟨hmm 0 hx0 hy0, hmm 1 hx1 hy1, ?_⟩,
      Fin.forall_fin_two.2 ⟨g0.le, g1.le⟩, 0, g0⟩
    simp only [hm]
    calc (1 / 2 : ℝ) • x 0 + (1 - 1 / 2 : ℝ) • y 0 + ((1 / 2 : ℝ) • x 1 + (1 - 1 / 2 : ℝ) • y 1)
        = (1 / 2 : ℝ) • (x 0 + x 1) + (1 - 1 / 2 : ℝ) • (y 0 + y 1) := by module
      _ = E.totalEndowment := by rw [hxs, hys]; module
  funext i
  fin_cases i
  · exact h0
  · simp only [Fin.mk_one]
    have : x 0 + x 1 = y 0 + y 1 := hxs.trans hys.symm
    rw [h0] at this
    exact add_left_cancel this

/-- **Exercise 15.B.7** (MWG, p. 541). For every `v ∈ [u₁(0), u₁(ω̄)]` there is a Pareto optimum
giving consumer 1 utility exactly `v`: maximise consumer 2's utility over the compact set of box
allocations giving consumer 1 at least `v`. -/
theorem pc_exists_po (h : E.ParetoCurveHyp) {v : ℝ} (hva : E.u 0 0 ≤ v)
    (hvb : v ≤ E.u 0 E.totalEndowment) : ∃ x, E.IsParetoOptimal x ∧ E.u 0 (x 0) = v := by
  set B := {x : Fin 2 → Fin 2 → ℝ | E.InBox x}
  set C := B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 0 (x 0)) ⁻¹' Set.Ici v with hC
  have hCc : IsCompact C := (pc_isCompact_box h).of_isClosed_subset
    ((pc_continuousOn_u h 0).preimage_isClosed_of_isClosed (pc_isClosed_box h) isClosed_Ici)
    Set.inter_subset_left
  have hCne : C.Nonempty := by
    refine ⟨![E.totalEndowment, 0], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa using pc_total_mem h
    · simpa using pc_zero_mem
    · simp
    · simpa using hvb
  obtain ⟨xs, hxs, hmax⟩ := hCc.exists_isMaxOn hCne ((pc_continuousOn_u h 1).mono
    Set.inter_subset_left)
  rw [isMaxOn_iff] at hmax
  have hxsv : E.u 0 (xs 0) = v := by
    refine le_antisymm (not_lt.1 fun hlt => ?_) hxs.2
    obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer0 h hxs.1 hlt hva
    exact absurd (hmax x'' ⟨hx'', h0.le⟩) (not_le.2 h1)
  refine ⟨xs, (pc_isParetoOptimal_iff h xs).2 ⟨hxs.1, fun x' hx' ⟨h0, h1⟩ => ?_⟩, hxsv⟩
  exact absurd (hmax x' ⟨hx', by rw [← hxsv] at *; exact h0.le⟩) (not_le.2 h1)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve: the Pareto optimum giving consumer 1 the
utility `v` clamped to `[u₁(0), u₁(ω̄)]` (and `0` if there is none, which does not happen under
`ParetoCurveHyp`). -/
noncomputable def ExchangeEconomy.paretoCurve (E : EdgeworthEconomy) (v : ℝ) :
    Fin 2 → Fin 2 → ℝ := by
  classical
  exact if hx : ∃ x, E.IsParetoOptimal x ∧
      E.u 0 (x 0) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) then hx.choose else 0

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve at `v` is Pareto optimal and gives
consumer 1 utility `v` clamped to `[u₁(0), u₁(ω̄)]`. -/
theorem pc_paretoCurve_spec (h : E.ParetoCurveHyp) (v : ℝ) :
    E.IsParetoOptimal (E.paretoCurve v) ∧
      E.u 0 (E.paretoCurve v 0) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) := by
  have hab := pc_a_le_b h
  have hex := pc_exists_po h (v := max (E.u 0 0) (min (E.u 0 E.totalEndowment) v))
    (le_max_left _ _) (max_le hab (min_le_left _ _))
  unfold ExchangeEconomy.paretoCurve
  split_ifs with hc
  · exact hc.choose_spec
  · exact absurd hex hc

/-- **Exercise 15.B.7** (MWG, p. 541). For `v ∈ [u₁(0), u₁(ω̄)]` the Pareto curve gives
consumer 1 utility exactly `v`. -/
theorem pc_paretoCurve_u (h : E.ParetoCurveHyp) {v : ℝ}
    (hv : v ∈ Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment)) : E.u 0 (E.paretoCurve v 0) = v := by
  rw [(pc_paretoCurve_spec h v).2, min_eq_right hv.2, max_eq_right hv.1]

/-- **Exercise 15.B.7** (MWG, p. 541). Every Pareto optimum lies on the Pareto curve. -/
theorem pc_eq_paretoCurve (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ}
    (hx : E.IsParetoOptimal x) : x = E.paretoCurve (E.u 0 (x 0)) :=
  pc_po_injective h hx (pc_paretoCurve_spec h _).1
    (pc_paretoCurve_u h (pc_po_bounds h hx)).symm

/-- **Exercise 15.B.7** (MWG, p. 541). Consumer 1's utility is a homeomorphism from the Pareto set
onto `[u₁(0), u₁(ω̄)]` (a continuous bijection from a compact space onto a Hausdorff space). -/
theorem exercise_15_B_7_homeomorph (h : E.ParetoCurveHyp) :
    ∃ g : E.paretoSet ≃ₜ Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment),
      ∀ x, (g x : ℝ) = E.u 0 (x.1 0) := by
  have : CompactSpace E.paretoSet := isCompact_iff_compactSpace.mp (pc_isCompact_paretoSet h)
  let f : E.paretoSet → Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment) :=
    fun x => ⟨E.u 0 (x.1 0), pc_po_bounds h x.2⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ((h.cont 0).comp_continuous
      ((continuous_apply 0).comp continuous_subtype_val) fun x => ?_) _
    have := ((pc_inBox_iff h x.1).1 x.2.1).1
    exact this
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (pc_po_injective h x.2 y.2 (congrArg Subtype.val hxy)),
      fun w => ?_⟩
    obtain ⟨x, hx, hxv⟩ := pc_exists_po h w.2.1 w.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hfc, fun _ => rfl⟩

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve is continuous (it is the inverse of the
homeomorphism `exercise_15_B_7_homeomorph`, composed with the clamp onto `[u₁(0), u₁(ω̄)]`). -/
theorem pc_continuous_paretoCurve (h : E.ParetoCurveHyp) : Continuous E.paretoCurve := by
  obtain ⟨g, hg⟩ := exercise_15_B_7_homeomorph h
  have hab := pc_a_le_b h
  have key : E.paretoCurve = fun v => (g.symm (Set.projIcc _ _ hab v)).1 := by
    funext v
    set w := g.symm (Set.projIcc _ _ hab v)
    have hw : (g w : ℝ) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) := by
      rw [g.apply_symm_apply, Set.coe_projIcc]
    rw [hg] at hw
    exact pc_po_injective h (pc_paretoCurve_spec h v).1 w.2
      (by rw [(pc_paretoCurve_spec h v).2, hw])
  rw [key]
  exact continuous_subtype_val.comp (g.symm.continuous.comp continuous_projIcc)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is the image of `[u₁(0), u₁(ω̄)]` under the
Pareto curve. -/
theorem pc_paretoSet_eq_image (h : E.ParetoCurveHyp) :
    E.paretoSet = E.paretoCurve '' Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment) := by
  ext x
  constructor
  · intro hx
    exact ⟨_, pc_po_bounds h hx, (pc_eq_paretoCurve h hx).symm⟩
  · rintro ⟨v, -, rfl⟩
    exact (pc_paretoCurve_spec h v).1

/-- **Exercise 15.B.7** (MWG, p. 541), first part. With continuous, strongly monotone and strictly
convex preferences (and `ω̄ ≫ 0`) the Pareto set has no "holes": it is connected. -/
theorem exercise_15_B_7_connected (h : E.ParetoCurveHyp) : IsConnected E.paretoSet := by
  rw [pc_paretoSet_eq_image h]
  exact (isConnected_Icc (pc_a_le_b h)).image _ (pc_continuous_paretoCurve h).continuousOn

/-! ### Exercise 15.B.7, second part: homothetic preferences -/

/-- A homothetic (Definition 3.B.6), continuous and strongly monotone utility preserves weak
rankings under scaling: `u(y) ≤ u(x)` implies `u(s y) ≤ u(s x)` for `s ≥ 0`. (If `u(y) < u(x)`,
`y` is indifferent to a point `t x`, `t ∈ [0, 1]`, of the ray through `x`.) -/
theorem pc_homothetic_le {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hxy : u y ≤ u x)
    {s : ℝ} (hs : 0 ≤ s) : u (s • y) ≤ u (s • x) := by
  rcases hxy.lt_or_eq with hlt | heq
  · have hcf : ContinuousOn (fun t : ℝ => u (t • x)) (Set.Icc 0 1) :=
      hc.comp (continuous_id.smul continuous_const).continuousOn fun t ht => pc_smul_mem hx ht.1
    have h0 : u ((0 : ℝ) • x) ≤ u y := by
      rw [zero_smul]
      exact hm.le (fun _ => le_rfl) fun l => hy l
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc zero_le_one hcf
      ⟨h0, by rw [one_smul]; exact hlt.le⟩
    have htx : t • x ∈ nonnegOrthant L := pc_smul_mem hx ht.1
    have hind := (hh (t • x) htx y hy ⟨hty.ge, hty.le⟩ s hs).1
    refine le_trans hind (hm.le (pc_smul_mem htx hs) fun l => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hx l) ht.2) hs
  · exact (hh x hx y hy ⟨heq.le, heq.ge⟩ s hs).1

/-- Strict form of `pc_homothetic_le`: `u(y) < u(x)` implies `u(s y) < u(s x)` for `s > 0`. -/
theorem pc_homothetic_lt {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hxy : u y < u x)
    {s : ℝ} (hs : 0 < s) : u (s • y) < u (s • x) := by
  by_contra hle
  rw [not_lt] at hle
  have := pc_homothetic_le hc hm hh (pc_smul_mem hy hs.le) (pc_smul_mem hx hs.le) hle
    (inv_nonneg.2 hs.le)
  rw [inv_smul_smul₀ hs.ne', inv_smul_smul₀ hs.ne'] at this
  linarith

/-- With homothetic preferences, if `t c` (`t > 0`) is optimal in the budget set
`{y ≥ 0 : p·y ≤ p·(t c)}`, then `s c` is optimal in `{y ≥ 0 : p·y ≤ p·(s c)}` for every
`s ≥ 0`. -/
theorem pc_scaled_support {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {p c : Fin L → ℝ} (hp : StrictlyPositive p) (hcm : c ∈ nonnegOrthant L) {t : ℝ}
    (ht : 0 < t)
    (hmax : ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (t • c) → u y ≤ u (t • c)) {s : ℝ}
    (hs : 0 ≤ s) : ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (s • c) → u y ≤ u (s • c) := by
  intro y hy hpy
  rcases hs.lt_or_eq with hs | rfl
  · have h1 : u ((t / s) • y) ≤ u (t • c) := by
      refine hmax _ (pc_smul_mem hy (by positivity)) ?_
      rw [dotProduct_smul, smul_eq_mul, dotProduct_smul, smul_eq_mul] at *
      calc t / s * (p ⬝ᵥ y) ≤ t / s * (s * (p ⬝ᵥ c)) :=
            mul_le_mul_of_nonneg_left hpy (by positivity)
        _ = t * (p ⬝ᵥ c) := by field_simp
    have h2 := pc_homothetic_le hc hm hh (pc_smul_mem hcm ht.le) (pc_smul_mem hy (by positivity))
      h1 (s := s / t) (by positivity)
    have e1 : (s / t) • ((t / s) • y) = y := by
      rw [smul_smul, div_mul_div_comm, mul_comm s t, div_self (by positivity), one_smul]
    have e2 : (s / t) • (t • c) = s • c := by rw [smul_smul, div_mul_cancel₀ s ht.ne']
    rwa [e1, e2] at h2
  · have := eq_zero_of_dotProduct_nonpos hp hy (by simpa using hpy)
    rw [this, zero_smul]

/-- **Exercise 15.B.7** (MWG, p. 541). The allocation `(s ω̄, (1 - s) ω̄)` on the diagonal of the
Edgeworth box. -/
noncomputable def ExchangeEconomy.diagonalAllocation (E : EdgeworthEconomy) (s : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![s • E.totalEndowment, (1 - s) • E.totalEndowment]

/-- The diagonal allocations with `s ∈ [0, 1]` are in the box. -/
theorem pc_diagonal_inBox (h : E.ParetoCurveHyp) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    E.InBox (E.diagonalAllocation s) := by
  refine (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩
  · simpa [ExchangeEconomy.diagonalAllocation] using pc_smul_mem (pc_total_mem h) hs.1
  · simpa [ExchangeEconomy.diagonalAllocation] using
      pc_smul_mem (pc_total_mem h) (sub_nonneg.2 hs.2)
  · simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Matrix.cons_val_one]
    module

/-- **Exercise 15.B.7** (MWG, p. 541). With homothetic preferences, if a Pareto optimum `z` has
`z₁ = t ω̄` with `0 < t < 1`, then every diagonal allocation `(s ω̄, (1 - s) ω̄)`, `s ∈ [0, 1]`,
is Pareto optimal: the supporting prices of `z` (second welfare theorem) support every diagonal
allocation, by homotheticity. -/
theorem pc_diagonal_po (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i)))
    {z : Fin 2 → Fin 2 → ℝ} (hz : E.IsParetoOptimal z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hzt : z 0 = t • E.totalEndowment) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    E.IsParetoOptimal (E.diagonalAllocation s) := by
  obtain ⟨p, hp, hT⟩ := second_welfare_theorem two_pos h.X_eq h.cont
    (fun i => (h.sconv i).prefConvex (convex_nonnegOrthant 2)) h.mono h.ω_pos hz
  have hsup : ∀ i, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ z i → E.u i y ≤ E.u i (z i) := by
    intro i y hy hpy
    exact hT.2.2 i y (by rw [h.X_eq i]; exact hy) (by beta_reduce; linarith)
  have hz1 : z 1 = (1 - t) • E.totalEndowment := by
    obtain ⟨-, -, hsum⟩ := (pc_inBox_iff h z).1 hz.1
    have : z 1 = E.totalEndowment - z 0 := by rw [← hsum]; abel
    rw [this, hzt]
    module
  have h0 := pc_scaled_support (h.cont 0) (h.mono 0) (hom 0) hp (pc_total_mem h) ht0
    (by rw [← hzt]; exact hsup 0) hs.1
  have h1 := pc_scaled_support (h.cont 1) (h.mono 1) (hom 1) hp (pc_total_mem h)
    (sub_pos.2 ht1) (by rw [← hz1]; exact hsup 1) (sub_nonneg.2 hs.2)
  refine (pc_isParetoOptimal_iff h _).2 ⟨pc_diagonal_inBox h hs, fun x' hx' ⟨g0, g1⟩ => ?_⟩
  simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Matrix.cons_val_one] at g0 g1
  obtain ⟨m0, m1, hsum⟩ := (pc_inBox_iff h x').1 hx'
  have c0 : p ⬝ᵥ (s • E.totalEndowment) < p ⬝ᵥ x' 0 := by
    by_contra hc
    exact absurd (h0 _ m0 (not_lt.1 hc)) (not_le.2 g0)
  have c1 : p ⬝ᵥ ((1 - s) • E.totalEndowment) < p ⬝ᵥ x' 1 := by
    by_contra hc
    exact absurd (h1 _ m1 (not_lt.1 hc)) (not_le.2 g1)
  have hadd : p ⬝ᵥ (x' 0 + x' 1) =
      p ⬝ᵥ (s • E.totalEndowment) + p ⬝ᵥ ((1 - s) • E.totalEndowment) := by
    rw [hsum, ← dotProduct_add]
    congr 1
    module
  rw [dotProduct_add] at hadd
  linarith

/-- **Exercise 15.B.7** (MWG, p. 541) and the claim of p. 533. With homothetic preferences (as
well as continuous, strongly monotone and strictly convex ones, and `ω̄ ≫ 0`), if some Pareto
optimum `z` other than the two origins lies on the diagonal of the box, then the Pareto set is the
whole diagonal `{(s ω̄, (1 - s) ω̄) : s ∈ [0, 1]}`. -/
theorem exercise_15_B_7_diagonal (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i)))
    {z : Fin 2 → Fin 2 → ℝ} (hz : E.IsParetoOptimal z) (hz0 : z 0 ≠ 0)
    (hzw : z 0 ≠ E.totalEndowment)
    (hdiag : z 0 0 * E.totalEndowment 1 = z 0 1 * E.totalEndowment 0) :
    E.paretoSet = E.diagonalAllocation '' Set.Icc 0 1 := by
  have hw0 := h.ω_pos 0
  have hzm := ((pc_inBox_iff h z).1 hz.1).1
  set t := z 0 0 / E.totalEndowment 0 with ht
  have hzt : z 0 = t • E.totalEndowment := by
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
      linarith
  have ht0 : 0 < t := by
    rcases (show (0 : ℝ) ≤ t from div_nonneg (hzm 0) hw0.le).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (by rw [hzt, ← heq, zero_smul]) hz0
  have ht1 : t < 1 := by
    have hle : t ≤ 1 := by rw [ht, div_le_one hw0]; exact pc_le_total h hz.1 0
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (by rw [hzt, heq, one_smul]) hzw
  ext x
  constructor
  · intro hx
    obtain ⟨hva, hvb⟩ := pc_po_bounds h hx
    have hcf : ContinuousOn (fun s : ℝ => E.u 0 (s • E.totalEndowment)) (Set.Icc 0 1) :=
      (h.cont 0).comp (continuous_id.smul continuous_const).continuousOn
        fun s hs => pc_smul_mem (pc_total_mem h) hs.1
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc zero_le_one hcf
      ⟨by simpa using hva, by simpa using hvb⟩
    refine ⟨s, hs, (pc_po_injective h hx (pc_diagonal_po h hom hz ht0 ht1 hzt hs) ?_).symm⟩
    simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero]
    exact hsv.symm
  · rintro ⟨s, hs, rfl⟩
    exact pc_diagonal_po h hom hz ht0 ht1 hzt hs

/-- **Exercise 15.B.7** (MWG, p. 541), second part. If, in addition, preferences are homothetic,
the Pareto set lies (weakly) on one side of the diagonal of the box: either every Pareto optimum
`x` has `x₁₁ ω̄₂ ≤ x₂₁ ω̄₁` (consumer 1's bundle on or below the diagonal ray) or every one has
`≥`. (Weakly: the two origins are always on the diagonal, and by `exercise_15_B_7_diagonal` the
whole Pareto set may be the diagonal.) -/
theorem exercise_15_B_7_homothetic (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i))) :
    (∀ x ∈ E.paretoSet, x 0 0 * E.totalEndowment 1 - x 0 1 * E.totalEndowment 0 ≤ 0) ∨
      (∀ x ∈ E.paretoSet, 0 ≤ x 0 0 * E.totalEndowment 1 - x 0 1 * E.totalEndowment 0) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le, exists_prop] at hcon
  obtain ⟨⟨x, hx, hDx⟩, ⟨y, hy, hDy⟩⟩ := hcon
  -- a Pareto optimum off the diagonal is not at an origin
  have hint : ∀ q ∈ E.paretoSet,
      q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0 ≠ 0 →
      E.u 0 0 < E.u 0 (q 0) ∧ E.u 0 (q 0) < E.u 0 E.totalEndowment := by
    intro q hq hD
    have hqm := ((pc_inBox_iff h q).1 hq.1).1
    refine ⟨(h.mono 0).lt pc_zero_mem (fun l => hqm l) fun he => hD ?_,
      (h.mono 0).lt hqm (pc_le_total h hq.1) fun he => hD ?_⟩
    · rw [he]
      simp
    · rw [← he]
      ring
  have hxi := hint x hx hDx.ne'
  have hyi := hint y hy hDy.ne
  set S := E.paretoCurve '' Set.uIcc (E.u 0 (y 0)) (E.u 0 (x 0)) with hS
  have hSc : IsPreconnected S :=
    isPreconnected_uIcc.image _ (pc_continuous_paretoCurve h).continuousOn
  have hxS : x ∈ S := ⟨_, Set.right_mem_uIcc, (pc_eq_paretoCurve h hx).symm⟩
  have hyS : y ∈ S := ⟨_, Set.left_mem_uIcc, (pc_eq_paretoCurve h hy).symm⟩
  have hDc : ContinuousOn
      (fun q : Fin 2 → Fin 2 → ℝ => q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0) S :=
    (by fun_prop : Continuous fun q : Fin 2 → Fin 2 → ℝ =>
      q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0).continuousOn
  obtain ⟨q, ⟨v, hv, rfl⟩, hq0⟩ := hSc.intermediate_value hyS hxS hDc ⟨hDy.le, hDx.le⟩
  have hva : E.u 0 0 < v ∧ v < E.u 0 E.totalEndowment := by
    rcases Set.mem_uIcc.1 hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hyi.1], by linarith [hxi.2]⟩
    · exact ⟨by linarith [hxi.1], by linarith [hyi.2]⟩
  have hu := pc_paretoCurve_u h ⟨hva.1.le, hva.2.le⟩
  have hpo := (pc_paretoCurve_spec h v).1
  have hz0 : E.paretoCurve v 0 ≠ 0 := fun he => by
    rw [he] at hu
    linarith [hva.1]
  have hzw : E.paretoCurve v 0 ≠ E.totalEndowment := fun he => by
    rw [he] at hu
    linarith [hva.2]
  have hset := exercise_15_B_7_diagonal h hom hpo hz0 hzw (by linarith)
  have hxd : x ∈ E.diagonalAllocation '' Set.Icc 0 1 := hset ▸ hx
  obtain ⟨s, -, rfl⟩ := hxd
  simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Pi.smul_apply,
    smul_eq_mul] at hDx
  linarith

/-! ### Exercise 15.B.10(d): a transfer paradox needs multiple equilibria -/

/-- The value of `y` at the normalized prices `(q, 1 - q)`. -/
theorem pc_dot_pair (q : ℝ) (y : Fin 2 → ℝ) : ![q, 1 - q] ⬝ᵥ y = q * y 0 + (1 - q) * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Normalizing `p` with `p₁ + p₂ > 0` to the price simplex. -/
theorem pc_normalize {p : Fin 2 → ℝ} (hp : 0 < p 0 + p 1) :
    ![p 0 / (p 0 + p 1), 1 - p 0 / (p 0 + p 1)] = (p 0 + p 1)⁻¹ • p := by
  funext l
  fin_cases l
  · simp [div_eq_inv_mul]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul]
    field_simp
    ring

/-- **Exercise 15.B.10(d)** (MWG, p. 542). The normalized prices `(q, 1 - q)` support the
allocation `x` as a quasi-equilibrium: a bundle that a consumer strictly prefers to his bundle
costs at least as much. -/
def ExchangeEconomy.QuasiSupports (E : EdgeworthEconomy) (q : ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x i) < E.u i y → ![q, 1 - q] ⬝ᵥ x i ≤ ![q, 1 - q] ⬝ᵥ y

/-- Prices `p ≫ 0` with `p·xᵢ ≤ p·y` whenever `y` is strictly preferred give, normalized, a
quasi-equilibrium support. -/
theorem pc_quasiSupports_of_pos {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {x : Fin 2 → Fin 2 → ℝ}
    (hx : ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x i) < E.u i y → p ⬝ᵥ x i ≤ p ⬝ᵥ y) :
    p 0 / (p 0 + p 1) ∈ Set.Icc (0 : ℝ) 1 ∧ E.QuasiSupports (p 0 / (p 0 + p 1)) x := by
  have hs : 0 < p 0 + p 1 := add_pos (hp 0) (hp 1)
  refine ⟨⟨div_nonneg (hp 0).le hs.le, (div_le_one hs).2 (by linarith [hp 1])⟩, ?_⟩
  intro i y hy hlt
  rw [pc_normalize hs, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hx i y hy hlt) (inv_nonneg.2 hs.le)

/-- The bundles on the Pareto curve lie in `ℝ²₊`. -/
theorem pc_paretoCurve_mem (h : E.ParetoCurveHyp) (v : ℝ) (i : Fin 2) :
    E.paretoCurve v i ∈ nonnegOrthant 2 := by
  rw [← h.X_eq i]
  exact (pc_paretoCurve_spec h v).1.1.1 i

/-- Consumer `i`'s utility along the Pareto curve is continuous. -/
theorem pc_continuous_u_paretoCurve (h : E.ParetoCurveHyp) (i : Fin 2) :
    Continuous fun v => E.u i (E.paretoCurve v i) :=
  (h.cont i).comp_continuous ((continuous_apply i).comp (pc_continuous_paretoCurve h))
    fun v => pc_paretoCurve_mem h v i

/-- **Exercise 15.B.10(d)** (MWG, p. 542). Every point of the Pareto curve has a
quasi-equilibrium support (second welfare theorem, normalized). -/
theorem pc_exists_quasiSupports (h : E.ParetoCurveHyp) (v : ℝ) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) := by
  obtain ⟨p, hp, hT⟩ := second_welfare_theorem two_pos h.X_eq h.cont
    (fun i => (h.sconv i).prefConvex (convex_nonnegOrthant 2)) h.mono h.ω_pos
    (pc_paretoCurve_spec h v).1
  refine ⟨_, pc_quasiSupports_of_pos hp fun i y hy hlt => ?_⟩
  by_contra hc
  exact absurd (hT.2.2 i y (by rw [h.X_eq i]; exact hy) (by beta_reduce; linarith))
    (not_le.2 hlt)

/-- **Exercise 15.B.10(d)** (MWG, p. 542). The graph `{(v, q) : (q, 1 - q) supports the Pareto
curve at v}` is closed: a limit of supporting prices supports the limit allocation. -/
theorem pc_isClosed_quasiSupports (h : E.ParetoCurveHyp) :
    IsClosed {vq : ℝ × ℝ | E.QuasiSupports vq.2 (E.paretoCurve vq.1)} := by
  have hpc := pc_continuous_paretoCurve h
  have hS : {vq : ℝ × ℝ | E.QuasiSupports vq.2 (E.paretoCurve vq.1)} =
      ⋂ i, ⋂ y ∈ nonnegOrthant 2, ({vq : ℝ × ℝ | E.u i y ≤ E.u i (E.paretoCurve vq.1 i)} ∪
        {vq : ℝ × ℝ | vq.2 * E.paretoCurve vq.1 i 0 + (1 - vq.2) * E.paretoCurve vq.1 i 1 ≤
          vq.2 * y 0 + (1 - vq.2) * y 1}) := by
    ext vq
    simp only [ExchangeEconomy.QuasiSupports, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union,
      pc_dot_pair]
    refine forall_congr' fun i => forall_congr' fun y => forall_congr' fun _ => ?_
    rw [imp_iff_not_or, not_lt]
  rw [hS]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => IsClosed.union ?_ ?_
  · exact isClosed_le continuous_const ((pc_continuous_u_paretoCurve h i).comp continuous_fst)
  · exact isClosed_le (by fun_prop) (by fun_prop)

/-- Projecting a closed subset of `ℝ × [0, 1]` to the first factor gives a closed set. -/
theorem pc_isClosed_exists_Icc {C : Set (ℝ × ℝ)} (hC : IsClosed C) :
    IsClosed {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, (v, q) ∈ C} := by
  have hT : IsClosed {vq : ℝ × Set.Icc (0 : ℝ) 1 | ((vq.1, (vq.2 : ℝ)) : ℝ × ℝ) ∈ C} :=
    hC.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have key : {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, (v, q) ∈ C} =
      Prod.fst '' {vq : ℝ × Set.Icc (0 : ℝ) 1 | ((vq.1, (vq.2 : ℝ)) : ℝ × ℝ) ∈ C} := by
    ext v
    constructor
    · rintro ⟨q, hq, hc⟩
      exact ⟨(v, ⟨q, hq⟩), hc, rfl⟩
    · rintro ⟨⟨v', q⟩, hc, rfl⟩
      exact ⟨q.1, q.2, hc⟩
  rw [key]
  exact isClosedMap_fst_of_compactSpace _ hT

/-- Quasi-equilibrium supports at a fixed allocation form an interval of `q`'s. -/
theorem pc_quasiSupports_uIcc {x : Fin 2 → Fin 2 → ℝ} {q₁ q₂ q : ℝ}
    (h₁ : E.QuasiSupports q₁ x) (h₂ : E.QuasiSupports q₂ x) (hq : q ∈ Set.uIcc q₁ q₂) :
    E.QuasiSupports q x := by
  intro i y hy hlt
  have a₁ := h₁ i y hy hlt
  have a₂ := h₂ i y hy hlt
  rw [pc_dot_pair, pc_dot_pair] at a₁ a₂ ⊢
  rcases le_total (y 0 - x i 0) (y 1 - x i 1) with hd | hd <;>
    rcases Set.mem_uIcc.1 hq with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hd)]

/-- Adding `e ≥ 0`, `e ≠ 0` to a bundle and removing a small fraction of `f`, `0 ≤ f ≤ x`, leaves
a strongly monotone, continuous utility strictly higher. -/
theorem pc_exists_better_cheaper {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hm : UtilityStronglyMonotone u)
    {x e f : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (he : e ∈ nonnegOrthant L) (he0 : e ≠ 0)
    (hf : f ∈ nonnegOrthant L) (hfx : f ≤ x) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x + e - t • f ∈ nonnegOrthant L ∧ u x < u (x + e - t • f) := by
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + e - t • f ∈ nonnegOrthant L := by
    intro t ht l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hf l, hfx l, he l, ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.2) (hf l)]
  have hg : Continuous fun t : ℝ => x + e - t • f := by fun_prop
  have h0 : u x < u (x + e - (0 : ℝ) • f) := by simpa using pc_lt_add hm hx he he0
  obtain ⟨t, ht0, ht1, hlt⟩ := exists_pos_continuous_lt hc hg hmem h0
  exact ⟨t, ht0, ht1, hmem t ⟨ht0.le, ht1⟩, hlt⟩

/-- **Exercise 15.B.10(d)** (MWG, p. 542). Quasi-equilibrium supporting prices of a box allocation
are strictly positive: if a good were free, the consumer holding some of the other good (`ω̄ ≫ 0`)
would find a strictly better and strictly cheaper bundle. -/
theorem pc_quasiSupports_pos (h : E.ParetoCurveHyp) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hS : E.QuasiSupports q x) : 0 < q ∧ q < 1 := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hxm : ∀ i, x i ∈ nonnegOrthant 2 := Fin.forall_fin_two.2 ⟨h0, h1⟩
  have hpos : ∀ l, ∃ i, 0 < x i l := by
    intro l
    by_contra hc
    simp only [not_exists, not_lt] at hc
    have := congrFun hs l
    simp only [Pi.add_apply] at this
    linarith [h.ω_pos l, hc 0, hc 1]
  have e0m : (![1, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> simp
  have e1m : (![0, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> simp
  have e0ne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun he => by simpa using congrFun he 0
  have e1ne : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun he => by simpa using congrFun he 1
  refine ⟨lt_of_le_of_ne hq.1 fun hq0 => ?_, lt_of_le_of_ne hq.2 fun hq1 => ?_⟩
  · obtain ⟨i, hi⟩ := hpos 1
    have hfm : (![0, x i 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
      fin_cases l <;> simp [hi.le]
    have hfx : (![0, x i 1] : Fin 2 → ℝ) ≤ x i := fun l => by
      fin_cases l <;> simp [hxm i 0]
    obtain ⟨t, ht0, -, hmem, hlt⟩ :=
      pc_exists_better_cheaper (h.cont i) (h.mono i) (hxm i) e0m e0ne hfm hfx
    have := hS i _ hmem hlt
    rw [pc_dot_pair, pc_dot_pair, ← hq0] at this
    simp [Matrix.vecHead, Matrix.vecTail] at this
    nlinarith [mul_pos ht0 hi]
  · obtain ⟨i, hi⟩ := hpos 0
    have hfm : (![x i 0, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
      fin_cases l <;> simp [hi.le]
    have hfx : (![x i 0, 0] : Fin 2 → ℝ) ≤ x i := fun l => by
      fin_cases l <;> simp [hxm i 1]
    obtain ⟨t, ht0, -, hmem, hlt⟩ :=
      pc_exists_better_cheaper (h.cont i) (h.mono i) (hxm i) e1m e1ne hfm hfx
    have := hS i _ hmem hlt
    rw [pc_dot_pair, pc_dot_pair, hq1] at this
    simp [Matrix.vecHead, Matrix.vecTail] at this
    nlinarith [mul_pos ht0 hi]

/-- **Exercise 15.B.10(d)** (MWG, p. 542). A quasi-equilibrium with strictly positive prices at
which every consumer's bundle is worth his endowment is a Walrasian equilibrium: a consumer with a
nonzero bundle could shrink a strictly preferred affordable bundle to a strictly cheaper one, and
a consumer with the zero bundle can afford only `0`. -/
theorem pc_walras_of_quasiSupports (h : E.ParetoCurveHyp) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hS : E.QuasiSupports q x)
    (hb : ∀ i, ![q, 1 - q] ⬝ᵥ x i = ![q, 1 - q] ⬝ᵥ E.ω i) : E.IsWalrasEqm ![q, 1 - q] x := by
  have hp : StrictlyPositive ![q, 1 - q] := fun l => by
    fin_cases l
    · simpa using hq0
    · simpa using hq1
  refine ⟨hx, fun i y hy => ?_⟩
  obtain ⟨hym, hpy⟩ := hy
  rw [h.X_eq i] at hym
  have hxi : x i ∈ nonnegOrthant 2 := by
    rw [← h.X_eq i]
    exact hx.1 i
  by_contra hlt
  rw [not_le] at hlt
  by_cases hx0 : x i = 0
  · rw [← hb i, hx0, dotProduct_zero] at hpy
    have hy0 := eq_zero_of_dotProduct_nonpos hp hym hpy
    rw [hy0, ← hx0] at hlt
    exact lt_irrefl _ hlt
  · have hpos := dotProduct_pos_of_strictlyPositive hp hxi hx0
    obtain ⟨t, ht0, ht1, hlt'⟩ := pc_exists_shrink (h.cont i) hym hlt
    have := hS i _ (pc_smul_mem hym (by linarith)) hlt'
    rw [dotProduct_smul, smul_eq_mul] at this
    rw [← hb i] at hpy
    nlinarith [mul_le_mul_of_nonneg_left hpy (sub_nonneg.2 ht1), mul_pos ht0 hpos]

/-- Moving endowments between consumers without changing the total does not change the Pareto
set. -/
theorem pc_isParetoOptimal_with (ω' : Fin 2 → Fin 2 → ℝ) (hsum : ∑ i, ω' i = ∑ i, E.ω i)
    (x : Fin 2 → Fin 2 → ℝ) :
    ({ E with ω := ω' } : EdgeworthEconomy).IsParetoOptimal x ↔ E.IsParetoOptimal x := by
  have hb : ∀ y, ({ E with ω := ω' } : EdgeworthEconomy).InBox y ↔ E.InBox y := fun y => by
    change ((∀ i, y i ∈ E.X i) ∧ ∑ i, y i = ∑ i, ω' i) ↔
      ((∀ i, y i ∈ E.X i) ∧ ∑ i, y i = ∑ i, E.ω i)
    rw [hsum]
  change (({ E with ω := ω' } : EdgeworthEconomy).InBox x ∧
      ¬ ∃ x', ({ E with ω := ω' } : EdgeworthEconomy).InBox x' ∧
        (∀ i, E.u i (x i) ≤ E.u i (x' i)) ∧ ∃ i, E.u i (x i) < E.u i (x' i)) ↔
    (E.InBox x ∧ ¬ ∃ x', E.InBox x' ∧ (∀ i, E.u i (x i) ≤ E.u i (x' i)) ∧
      ∃ i, E.u i (x i) < E.u i (x' i))
  simp only [hb]

/-- **Exercise 15.B.10(d)** (MWG, p. 542), the hint. Let `(p', x')` be a Walrasian equilibrium of
the economy after a transfer `z ≥ 0` from consumer 2 to consumer 1 (endowments `ω₁ + z`,
`ω₂ - z`). Then the economy before the transfer has a Walrasian equilibrium `(p, x)` with `p ≫ 0`
at which consumer 1's utility is no higher than at `x'`. Proof: along the Pareto curve from
consumer 1's origin (where consumer 1's excess value `p·(x₁ - ω₁)` at supporting prices is
`≤ 0`) to `x'` (where it is `≥ 0`), the closed sets of utility levels with a supporting price
making it `≤ 0`, resp. `≥ 0`, cover a connected interval and so intersect; there a supporting
price makes it `0`, and that quasi-equilibrium is a Walrasian equilibrium. (The hint's "even lower
level of utility" is proved in the weak form `≤`.) -/
theorem exercise_15_B_10d_lower_eqm (h : E.ParetoCurveHyp) (hω0 : E.ω 0 ∈ nonnegOrthant 2)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {p' : Fin 2 → ℝ} {x' : Fin 2 → Fin 2 → ℝ}
    (heq : ({ E with ω := ![E.ω 0 + z, E.ω 1 - z] } : EdgeworthEconomy).IsWalrasEqm p' x') :
    ∃ p x, StrictlyPositive p ∧ E.IsWalrasEqm p x ∧ E.u 0 (x 0) ≤ E.u 0 (x' 0) := by
  set E' : EdgeworthEconomy := { E with ω := ![E.ω 0 + z, E.ω 1 - z] } with hE'
  have hsum : ∑ i, E'.ω i = ∑ i, E.ω i := by
    change ∑ i, (![E.ω 0 + z, E.ω 1 - z] : Fin 2 → Fin 2 → ℝ) i = ∑ i, E.ω i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    abel
  have hlns : ∀ i, UtilityLNS (E.u i) := fun i => (h.mono i).lns two_pos
  have hd' : E'.IsDemandEqm p' x' := (isWalrasEqm_iff_isDemandEqm (E := E') h.X_eq hlns p' x').1 heq
  have hpo : E.IsParetoOptimal x' :=
    (pc_isParetoOptimal_with _ hsum x').1 (first_welfare_theorem (E := E') h.X_eq hlns heq)
  have hx'm : ∀ i, x' i ∈ nonnegOrthant 2 := fun i => by
    rw [← h.X_eq i]
    exact hpo.1.1 i
  -- the equilibrium prices of the economy after the transfer are strictly positive
  have hp' : StrictlyPositive p' := by
    intro l
    by_contra hc
    rw [not_lt] at hc
    have hel : (Pi.single l 1 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun k => by
      by_cases hk : k = l
      · subst hk
        simp
      · simp [hk]
    have hel0 : (Pi.single l 1 : Fin 2 → ℝ) ≠ 0 := fun he => by
      simpa using congrFun he l
    have hy : x' 0 + Pi.single l 1 ∈ E'.budget 0 p' := by
      refine ⟨?_, ?_⟩
      · change x' 0 + Pi.single l 1 ∈ E.X 0
        rw [h.X_eq 0]
        exact fun k => add_nonneg (hx'm 0 k) (hel k)
      · rw [dotProduct_add, dotProduct_single, mul_one]
        linarith [(hd'.2 0).1.2]
    have := (hd'.2 0).2 _ hy
    linarith [pc_lt_add (h.mono 0) (hx'm 0) hel hel0]
  set v' := E.u 0 (x' 0) with hv'
  have hx'c : x' = E.paretoCurve v' := pc_eq_paretoCurve h hpo
  have hav' : E.u 0 0 ≤ v' := (pc_po_bounds h hpo).1
  have hpc := pc_continuous_paretoCurve h
  set g : ℝ → ℝ → ℝ := fun v q => ![q, 1 - q] ⬝ᵥ (E.paretoCurve v 0 - E.ω 0) with hg
  have hgc : Continuous fun vq : ℝ × ℝ => g vq.1 vq.2 := by
    simp only [hg, pc_dot_pair, Pi.sub_apply]
    fun_prop
  set A := {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) ∧ g v q ≤ 0}
    with hA
  set B := {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) ∧ 0 ≤ g v q}
    with hB
  have hAc : IsClosed A := pc_isClosed_exists_Icc
    ((pc_isClosed_quasiSupports h).inter (isClosed_le hgc continuous_const))
  have hBc : IsClosed B := pc_isClosed_exists_Icc
    ((pc_isClosed_quasiSupports h).inter (isClosed_le continuous_const hgc))
  have hcover : Set.Icc (E.u 0 0) v' ⊆ A ∪ B := by
    intro v _
    obtain ⟨q, hq, hS⟩ := pc_exists_quasiSupports h v
    rcases le_total (g v q) 0 with hle | hle
    · exact Or.inl ⟨q, hq, hS, hle⟩
    · exact Or.inr ⟨q, hq, hS, hle⟩
  -- at consumer 1's origin the excess value is `≤ 0`
  have haA : E.u 0 0 ∈ A := by
    have hu := pc_paretoCurve_u h ⟨le_rfl, pc_a_le_b h⟩
    have h0 : E.paretoCurve (E.u 0 0) 0 = 0 := by
      by_contra hne
      exact absurd hu ((h.mono 0).lt pc_zero_mem (fun l => pc_paretoCurve_mem h _ 0 l) hne).ne'
    obtain ⟨q, hq, hS⟩ := pc_exists_quasiSupports h (E.u 0 0)
    refine ⟨q, hq, hS, ?_⟩
    simp only [hg, h0, zero_sub, dotProduct_neg, neg_nonpos]
    refine dotProduct_nonneg_of_nonneg (fun l => ?_) hω0
    fin_cases l
    · simpa using hq.1
    · simpa using hq.2
  -- at `x'` the excess value is `≥ 0`
  have hv'B : v' ∈ B := by
    have hsupp : ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x' i) < E.u i y → p' ⬝ᵥ x' i ≤ p' ⬝ᵥ y := by
      intro i y hy hlt
      by_contra hc
      rw [not_le] at hc
      have hyb : y ∈ E'.budget i p' := by
        refine ⟨?_, ?_⟩
        · change y ∈ E.X i
          rw [h.X_eq i]
          exact hy
        · linarith [(hd'.2 i).1.2]
      linarith [(hd'.2 i).2 y hyb]
    obtain ⟨hq, hS⟩ := pc_quasiSupports_of_pos (E := E) hp' hsupp
    refine ⟨_, hq, hx'c ▸ hS, ?_⟩
    have hs : 0 < p' 0 + p' 1 := add_pos (hp' 0) (hp' 1)
    have hbud := budget_line_of_inBox hd'.1 (fun i => (hd'.2 i).1.2) 0
    have hω'0 : E'.ω 0 = E.ω 0 + z := rfl
    rw [hω'0, dotProduct_add] at hbud
    simp only [hg]
    rw [← hx'c, pc_normalize hs, smul_dotProduct, smul_eq_mul, dotProduct_sub, hbud]
    exact mul_nonneg (inv_nonneg.2 hs.le)
      (by linarith [dotProduct_nonneg_of_nonneg (fun l => (hp' l).le) hz])
  obtain ⟨v, hv, hvA, hvB⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc A B hAc hBc hcover
    ⟨_, Set.left_mem_Icc.2 hav', haA⟩ ⟨v', Set.right_mem_Icc.2 hav', hv'B⟩
  obtain ⟨q₁, hq₁, hS₁, hg₁⟩ := hvA
  obtain ⟨q₂, hq₂, hS₂, hg₂⟩ := hvB
  have hgv : ContinuousOn (fun q => g v q) (Set.uIcc q₁ q₂) := by
    simp only [hg, pc_dot_pair]
    fun_prop
  obtain ⟨q, hq, hgq⟩ :=
    isPreconnected_uIcc.intermediate_value Set.left_mem_uIcc Set.right_mem_uIcc hgv ⟨hg₁, hg₂⟩
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc hq₁ hq₂ hq
  have hSq := pc_quasiSupports_uIcc hS₁ hS₂ hq
  set x := E.paretoCurve v with hx
  have hxb : E.InBox x := (pc_paretoCurve_spec h v).1.1
  obtain ⟨hq0, hq1⟩ := pc_quasiSupports_pos h hqI hxb hSq
  have hb0 : ![q, 1 - q] ⬝ᵥ x 0 = ![q, 1 - q] ⬝ᵥ E.ω 0 := by
    have : ![q, 1 - q] ⬝ᵥ (x 0 - E.ω 0) = 0 := hgq
    rw [dotProduct_sub] at this
    linarith
  have hb : ∀ i, ![q, 1 - q] ⬝ᵥ x i = ![q, 1 - q] ⬝ᵥ E.ω i := by
    rw [Fin.forall_fin_two]
    refine ⟨hb0, ?_⟩
    obtain ⟨-, -, hsx⟩ := (pc_inBox_iff h x).1 hxb
    have htot : E.totalEndowment = E.ω 0 + E.ω 1 := by
      simp [ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
    have := congrArg (fun y => ![q, 1 - q] ⬝ᵥ y) hsx
    simp only [htot, dotProduct_add] at this
    linarith
  refine ⟨![q, 1 - q], x, fun l => ?_, pc_walras_of_quasiSupports h hq0 hq1 hxb hSq hb, ?_⟩
  · fin_cases l
    · simpa using hq0
    · simpa using hq1
  · rw [hx, pc_paretoCurve_u h ⟨hv.1, hv.2.trans (pc_po_bounds h hpo).2⟩]
    exact hv.2

/-- **Exercise 15.B.10(d)** (MWG, p. 542). In an Edgeworth box economy with continuous, strictly
convex and strongly monotone preferences, the transfer paradox can happen only if there is a
multiplicity of equilibria: if after a transfer `z ≥ 0` to consumer 1 there is an equilibrium
`(p', x')` at which consumer 1 is strictly worse off than at some equilibrium `(p, x)` before the
transfer, then the economy before the transfer has two equilibria with different allocations. -/
theorem exercise_15_B_10d (h : E.ParetoCurveHyp) (hω0 : E.ω 0 ∈ nonnegOrthant 2)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {p' : Fin 2 → ℝ} {x' : Fin 2 → Fin 2 → ℝ}
    (heq : ({ E with ω := ![E.ω 0 + z, E.ω 1 - z] } : EdgeworthEconomy).IsWalrasEqm p' x')
    {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ} (hE : E.IsWalrasEqm p x)
    (hlt : E.u 0 (x' 0) < E.u 0 (x 0)) :
    ∃ p₁ x₁ p₂ x₂, E.IsWalrasEqm p₁ x₁ ∧ E.IsWalrasEqm p₂ x₂ ∧ x₁ ≠ x₂ := by
  obtain ⟨p₂, x₂, -, h₂, hle⟩ := exercise_15_B_10d_lower_eqm h hω0 hz heq
  refine ⟨p, x, p₂, x₂, hE, h₂, fun he => ?_⟩
  rw [he] at hlt
  linarith

/-! ### The instance `u = √x₁ + √x₂` -/

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. The utility function
`u(x) = √x₁ + √x₂`. -/
noncomputable def sqrtUtility (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + Real.sqrt (x 1)

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. The Edgeworth box economy
in which both consumers have `u = √x₁ + √x₂`, with endowments `ω₁ = (1, 0)` and `ω₂ = (0, 1)`. -/
noncomputable def sqrtEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ => sqrtUtility) ![![1, 0], ![0, 1]]

/-- The total endowment of `sqrtEconomy` is `(1, 1)`. -/
theorem sqrtEconomy_total : sqrtEconomy.totalEndowment = ![1, 1] := by
  funext l
  fin_cases l <;>
    simp [ExchangeEconomy.totalEndowment, sqrtEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two]

/-- `√x₁ + √x₂` is strongly monotone on `ℝ²₊`. -/
theorem sqrtUtility_stronglyMonotone : UtilityStronglyMonotone sqrtUtility := by
  intro x hx y _ hxy hne
  have key : sqrtUtility x < sqrtUtility y := by
    have h0 := Real.sqrt_le_sqrt (hxy 0)
    have h1 := Real.sqrt_le_sqrt (hxy 1)
    have hor : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hne (funext (Fin.forall_fin_two.2 ⟨hc.1.symm, hc.2.symm⟩))
    unfold sqrtUtility
    rcases hor with hl | hl
    · linarith [Real.sqrt_lt_sqrt (hx 0) (lt_of_le_of_ne (hxy 0) hl)]
    · linarith [Real.sqrt_lt_sqrt (hx 1) (lt_of_le_of_ne (hxy 1) hl)]
  exact ⟨key.le, not_le.2 key⟩

/-- `√x₁ + √x₂` represents strictly convex preferences on `ℝ²₊` (it is strictly concave). -/
theorem sqrtUtility_strictlyConvex :
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref sqrtUtility) := by
  intro x _ y hy z hz hyx hzx hne α h0 h1
  have hyx' : sqrtUtility x ≤ sqrtUtility y := hyx
  have hzx' : sqrtUtility x ≤ sqrtUtility z := hzx
  have hm : ∀ l, (α • y + (1 - α) • z) l = α * y l + (1 - α) * z l := fun l => by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ l, α * Real.sqrt (y l) + (1 - α) * Real.sqrt (z l) ≤
      Real.sqrt (α * y l + (1 - α) * z l) := fun l => by
    simpa [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.2 (hy l) (hz l) h0.le
      (by linarith) (by ring)
  have hsc : ∀ l, y l ≠ z l → α * Real.sqrt (y l) + (1 - α) * Real.sqrt (z l) <
      Real.sqrt (α * y l + (1 - α) * z l) := fun l hl => by
    simpa [smul_eq_mul] using Real.strictConcaveOn_sqrt.2 (hy l) (hz l) hl h0
      (by linarith) (by ring)
  have hor : y 0 ≠ z 0 ∨ y 1 ≠ z 1 := by
    by_contra hc'
    simp only [not_or, not_not] at hc'
    exact hne (funext (Fin.forall_fin_two.2 ⟨hc'.1, hc'.2⟩))
  have hmean : sqrtUtility x ≤ α * sqrtUtility y + (1 - α) * sqrtUtility z := by
    nlinarith [mul_le_mul_of_nonneg_left hyx' h0.le,
      mul_le_mul_of_nonneg_left hzx' (sub_nonneg.2 h1.le)]
  have key : sqrtUtility x < sqrtUtility (α • y + (1 - α) • z) := by
    unfold sqrtUtility at hmean ⊢
    rw [hm 0, hm 1]
    rcases hor with hl | hl
    · linarith [hsc 0 hl, hc 1]
    · linarith [hc 0, hsc 1 hl]
  exact ⟨key.le, not_le.2 key⟩

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. `sqrtEconomy` satisfies the
standing hypotheses. -/
theorem sqrtEconomy_hyp : sqrtEconomy.ParetoCurveHyp where
  X_eq _ := rfl
  cont _ := ((Real.continuous_sqrt.comp (continuous_apply 0)).add
    (Real.continuous_sqrt.comp (continuous_apply 1))).continuousOn
  mono _ := sqrtUtility_stronglyMonotone
  sconv _ := sqrtUtility_strictlyConvex
  ω_pos l := by
    rw [sqrtEconomy_total]
    fin_cases l <;> simp

/-- **Exercise 15.B.7** (MWG, p. 541), instance. `√x₁ + √x₂` is homothetic (Definition 3.B.6):
`√(αx₁) + √(αx₂) = √α (√x₁ + √x₂)`. -/
theorem sqrtEconomy_homothetic :
    ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (sqrtEconomy.u i)) := by
  intro _ x _ y _ hxy α hα
  have e : ∀ v : Fin 2 → ℝ, sqrtUtility (α • v) = Real.sqrt α * sqrtUtility v := fun v => by
    simp only [sqrtUtility, Pi.smul_apply, smul_eq_mul, Real.sqrt_mul hα]
    ring
  have hxy' : sqrtUtility y ≤ sqrtUtility x ∧ sqrtUtility x ≤ sqrtUtility y := hxy
  change sqrtUtility (α • y) ≤ sqrtUtility (α • x) ∧ sqrtUtility (α • x) ≤ sqrtUtility (α • y)
  rw [e, e]
  exact ⟨mul_le_mul_of_nonneg_left hxy'.1 (Real.sqrt_nonneg _),
    mul_le_mul_of_nonneg_left hxy'.2 (Real.sqrt_nonneg _)⟩

/-- With `√x₁ + √x₂`, a bundle with `y₁ + y₂ ≤ 2c` is no better than `(c, c)`. -/
theorem sqrtUtility_le_diag {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2) {c : ℝ} (hc : 0 ≤ c)
    (hyc : y 0 + y 1 ≤ 2 * c) : sqrtUtility y ≤ sqrtUtility ![c, c] := by
  simp only [sqrtUtility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have ha := Real.sq_sqrt (hy 0)
  have hb := Real.sq_sqrt (hy 1)
  have hs := Real.sq_sqrt hc
  have hsq : (Real.sqrt (y 0) + Real.sqrt (y 1)) ^ 2 ≤ (Real.sqrt c + Real.sqrt c) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (y 0) - Real.sqrt (y 1))]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- **Exercise 15.B.7** (MWG, p. 541), instance. In `sqrtEconomy` the equal split
`((1/2, 1/2), (1/2, 1/2))` is Pareto optimal. -/
theorem sqrtEconomy_half_po :
    sqrtEconomy.IsParetoOptimal (sqrtEconomy.diagonalAllocation (1 / 2)) := by
  have hh : (1 / 2 : ℝ) • (![1, 1] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
    funext l
    fin_cases l <;> simp
  have hh' : (1 - 1 / 2 : ℝ) • (![1, 1] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
    funext l
    fin_cases l <;> norm_num
  refine (pc_isParetoOptimal_iff sqrtEconomy_hyp _).2
    ⟨pc_diagonal_inBox sqrtEconomy_hyp ⟨by norm_num, by norm_num⟩, fun x' hx' ⟨g0, g1⟩ => ?_⟩
  obtain ⟨m0, m1, hsum⟩ := (pc_inBox_iff sqrtEconomy_hyp x').1 hx'
  rw [sqrtEconomy_total] at hsum
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at s0 s1
  simp only [ExchangeEconomy.diagonalAllocation, sqrtEconomy_total, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hh, hh'] at g0 g1
  change sqrtUtility ![1 / 2, 1 / 2] < sqrtUtility (x' 0) at g0
  change sqrtUtility ![1 / 2, 1 / 2] < sqrtUtility (x' 1) at g1
  rcases le_total (x' 0 0 + x' 0 1) 1 with hle | hle
  · exact absurd (sqrtUtility_le_diag m0 (by norm_num) (by linarith)) (not_le.2 g0)
  · exact absurd (sqrtUtility_le_diag m1 (by norm_num) (by linarith)) (not_le.2 g1)

/-- **Exercise 15.B.7** (MWG, p. 541), instance. With identical homothetic preferences
`u = √x₁ + √x₂` the Pareto set of `sqrtEconomy` is the diagonal of the box. -/
theorem sqrtEconomy_paretoSet :
    sqrtEconomy.paretoSet = sqrtEconomy.diagonalAllocation '' Set.Icc 0 1 := by
  refine exercise_15_B_7_diagonal sqrtEconomy_hyp sqrtEconomy_homothetic sqrtEconomy_half_po
    ?_ ?_ ?_ <;>
    simp only [ExchangeEconomy.diagonalAllocation, sqrtEconomy_total, Matrix.cons_val_zero]
  · intro he
    simpa using congrFun he 0
  · intro he
    have := congrFun he 0
    norm_num at this
  · simp

/-- **Exercise 15.B.10(d)** (MWG, p. 542), instance. After the transfer `z = (0, 1/2)` to
consumer 1 in `sqrtEconomy` (endowments `(1, 1/2)` and `(0, 1/2)`), the prices `(1, 1)` and the
allocation `((3/4, 3/4), (1/4, 1/4))` form a Walrasian equilibrium. -/
theorem sqrtEconomy_transfer_eqm :
    ({ sqrtEconomy with ω := ![sqrtEconomy.ω 0 + ![0, 1 / 2], sqrtEconomy.ω 1 - ![0, 1 / 2]] } :
      EdgeworthEconomy).IsWalrasEqm ![1, 1] ![![3 / 4, 3 / 4], ![1 / 4, 1 / 4]] := by
  refine ⟨⟨fun i l => ?_, ?_⟩, fun i y hy => ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · funext l
    fin_cases l <;>
      simp [sqrtEconomy, ExchangeEconomy.ofOrthant, ExchangeEconomy.totalEndowment,
        Fin.sum_univ_two] <;> norm_num
  · obtain ⟨hym, hpy⟩ := hy
    change y ∈ nonnegOrthant 2 at hym
    have hb : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 := by simp [dotProduct, Fin.sum_univ_two]
    rw [hb] at hpy
    fin_cases i
    · have hw := hpy.trans_eq (by
        norm_num [sqrtEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] :
          _ = (3 / 2 : ℝ))
      change sqrtUtility y ≤ sqrtUtility ![3 / 4, 3 / 4]
      exact sqrtUtility_le_diag hym (by norm_num) (by linarith)
    · have hw := hpy.trans_eq (by
        norm_num [sqrtEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] :
          _ = (1 / 2 : ℝ))
      change sqrtUtility y ≤ sqrtUtility ![1 / 4, 1 / 4]
      exact sqrtUtility_le_diag hym (by norm_num) (by linarith)

/-- **Exercise 15.B.10(d)** (MWG, p. 542), instance. The theorem `exercise_15_B_10d_lower_eqm`
applies to `sqrtEconomy` with the transfer `z = (0, 1/2)`: before the transfer there is a
Walrasian equilibrium with strictly positive prices at which consumer 1's utility is at most his
utility `√3` at the post-transfer equilibrium. -/
theorem sqrtEconomy_15_B_10d :
    ∃ p x, StrictlyPositive p ∧ sqrtEconomy.IsWalrasEqm p x ∧
      sqrtEconomy.u 0 (x 0) ≤ sqrtUtility ![3 / 4, 3 / 4] :=
  exercise_15_B_10d_lower_eqm sqrtEconomy_hyp
    (fun l => by fin_cases l <;> simp [sqrtEconomy, ExchangeEconomy.ofOrthant])
    (fun l => by fin_cases l <;> norm_num) sqrtEconomy_transfer_eqm

end MWG.GeneralEquilibriumExamples

set_option linter.style.longLine false
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.mk
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.X
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.u
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ω
#print axioms MWG.GeneralEquilibriumExamples.EdgeworthEconomy
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ofOrthant
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.totalEndowment
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsAllocation
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsFeasible
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.InBox
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.budget
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.demand
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.offerCurve
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsWalrasEqm
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsDemandEqm
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsParetoOptimal
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.paretoSet
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.contractCurve
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsEqmWithTransfers
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsSupportable
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.InBox.isFeasible
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.inBox_endowment
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsDemandEqm.isWalrasEqm
#print axioms MWG.GeneralEquilibriumExamples.budget_line_of_inBox
#print axioms MWG.GeneralEquilibriumExamples.offerCurve_ge_endowment
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.budget_smul
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.demand_smul
#print axioms MWG.GeneralEquilibriumExamples.isWalrasEqm_smul
#print axioms MWG.GeneralEquilibriumExamples.isDemandEqm_smul
#print axioms MWG.GeneralEquilibriumExamples.UtilityLNS
#print axioms MWG.GeneralEquilibriumExamples.UtilityStronglyMonotone
#print axioms MWG.GeneralEquilibriumExamples.UtilityStronglyMonotone.lt
#print axioms MWG.GeneralEquilibriumExamples.UtilityStronglyMonotone.lns
#print axioms MWG.GeneralEquilibriumExamples.UtilityLNS.exists_better
#print axioms MWG.GeneralEquilibriumExamples.UtilityLNS.budget_eq
#print axioms MWG.GeneralEquilibriumExamples.isWalrasEqm_iff_isDemandEqm
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.toPrivEconomy
#print axioms MWG.GeneralEquilibriumExamples.isDemandEqm_iff_competitiveEqm
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.toEconomy
#print axioms MWG.GeneralEquilibriumExamples.isParetoOptimal_iff_economy
#print axioms MWG.GeneralEquilibriumExamples.offerCurve_of_isDemandEqm
#print axioms MWG.GeneralEquilibriumExamples.proportional_of_orthogonal
#print axioms MWG.GeneralEquilibriumExamples.isDemandEqm_of_offerCurves
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_1a
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_1b
#print axioms MWG.GeneralEquilibriumExamples.exists_pos_continuous_lt
#print axioms MWG.GeneralEquilibriumExamples.eventually_gt_of_deriv_pos
#print axioms MWG.GeneralEquilibriumExamples.exists_pos_deriv_pos
#print axioms MWG.GeneralEquilibriumExamples.exists_pos_deriv_neg
#print axioms MWG.GeneralEquilibriumExamples.quasiconcave_of_prefConvex
#print axioms MWG.GeneralEquilibriumExamples.dotProduct_pos_of_strictlyPositive
#print axioms MWG.GeneralEquilibriumExamples.dotProduct_nonneg_of_nonneg
#print axioms MWG.GeneralEquilibriumExamples.eq_zero_of_dotProduct_nonpos
#print axioms MWG.GeneralEquilibriumExamples.concave_le_tangent
#print axioms MWG.GeneralEquilibriumExamples.first_welfare_theorem
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_3
#print axioms MWG.GeneralEquilibriumExamples.walrasEqm_mem_contractCurve
#print axioms MWG.GeneralEquilibriumExamples.paretoOptimal_interior_tangency
#print axioms MWG.GeneralEquilibriumExamples.UtilityStronglyMonotone.le
#print axioms MWG.GeneralEquilibriumExamples.sum_add_ite_eq
#print axioms MWG.GeneralEquilibriumExamples.onesVec
#print axioms MWG.GeneralEquilibriumExamples.dotProduct_smul_onesVec
#print axioms MWG.GeneralEquilibriumExamples.UtilityStronglyMonotone.lt_add_ones
#print axioms MWG.GeneralEquilibriumExamples.second_welfare_theorem
#print axioms MWG.GeneralEquilibriumExamples.second_welfare_theorem_edgeworth
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.IsEqmWithTransfers.wealth_eq
#print axioms MWG.GeneralEquilibriumExamples.walrasEqm_of_endowment_transfer
#print axioms MWG.GeneralEquilibriumExamples.walrasEqm_at_allocation
#print axioms MWG.GeneralEquilibriumExamples.footnote_4_unique
#print axioms MWG.GeneralEquilibriumExamples.linearUtility
#print axioms MWG.GeneralEquilibriumExamples.footnote4Economy
#print axioms MWG.GeneralEquilibriumExamples.footnote_4_needs_strict_convexity
#print axioms MWG.GeneralEquilibriumExamples.cdEconomy
#print axioms MWG.GeneralEquilibriumExamples.cdExponent
#print axioms MWG.GeneralEquilibriumExamples.cdEconomy_u
#print axioms MWG.GeneralEquilibriumExamples.cd_no_demand_0
#print axioms MWG.GeneralEquilibriumExamples.cobbDouglas_swap
#print axioms MWG.GeneralEquilibriumExamples.cd_no_demand_1
#print axioms MWG.GeneralEquilibriumExamples.cd_demand_eq
#print axioms MWG.GeneralEquilibriumExamples.cd_demand_empty
#print axioms MWG.GeneralEquilibriumExamples.cdAllocation
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_2
#print axioms MWG.GeneralEquilibriumExamples.cdPriceRatio
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_2_statics
#print axioms MWG.GeneralEquilibriumExamples.example15B1Endowment
#print axioms MWG.GeneralEquilibriumExamples.example_15_B_1_offerCurves
#print axioms MWG.GeneralEquilibriumExamples.example_15_B_1_monotone
#print axioms MWG.GeneralEquilibriumExamples.example_15_B_1
#print axioms MWG.GeneralEquilibriumExamples.cd_endowment_mem_offerCurve
#print axioms MWG.GeneralEquilibriumExamples.ql8_poly
#print axioms MWG.GeneralEquilibriumExamples.ql8_optimal
#print axioms MWG.GeneralEquilibriumExamples.ex15B2a
#print axioms MWG.GeneralEquilibriumExamples.ex15B2r
#print axioms MWG.GeneralEquilibriumExamples.ex15B2a_pow
#print axioms MWG.GeneralEquilibriumExamples.ex15B2r_eq
#print axioms MWG.GeneralEquilibriumExamples.ex15B2a_bounds
#print axioms MWG.GeneralEquilibriumExamples.ex15B2r_bounds
#print axioms MWG.GeneralEquilibriumExamples.ex15B2Economy
#print axioms MWG.GeneralEquilibriumExamples.ex15B2_pos_aux
#print axioms MWG.GeneralEquilibriumExamples.ex15B2OC1
#print axioms MWG.GeneralEquilibriumExamples.ex15B2OC2
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_5_offerCurves
#print axioms MWG.GeneralEquilibriumExamples.ex15B2_factor
#print axioms MWG.GeneralEquilibriumExamples.ex15B2_roots
#print axioms MWG.GeneralEquilibriumExamples.ex15B2a_inv_pow
#print axioms MWG.GeneralEquilibriumExamples.ex15B2_demand0_empty
#print axioms MWG.GeneralEquilibriumExamples.example_15_B_2
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_5_printed
#print axioms MWG.GeneralEquilibriumExamples.example_15_B_2_increasing
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_eq
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_eq_inv_sqrt
#print axioms MWG.GeneralEquilibriumExamples.inv_sq_tangent
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_optimal
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_demand
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_lt_add0
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_swap
#print axioms MWG.GeneralEquilibriumExamples.cesNeg2_lt_add1
#print axioms MWG.GeneralEquilibriumExamples.blairC
#print axioms MWG.GeneralEquilibriumExamples.blairEconomy
#print axioms MWG.GeneralEquilibriumExamples.blairAlloc
#print axioms MWG.GeneralEquilibriumExamples.blair_demand
#print axioms MWG.GeneralEquilibriumExamples.blair_demand_empty
#print axioms MWG.GeneralEquilibriumExamples.blair_factor
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_6
#print axioms MWG.GeneralEquilibriumExamples.endowment_mem_offerCurve
#print axioms MWG.GeneralEquilibriumExamples.GrossSubstitute
#print axioms MWG.GeneralEquilibriumExamples.NormalOfferCurve
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4b
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4b_offerCurves
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4e
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4d
#print axioms MWG.GeneralEquilibriumExamples.ex15B2d
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4f
#print axioms MWG.GeneralEquilibriumExamples.endowment_mem_offerCurve_instance
#print axioms MWG.GeneralEquilibriumExamples.cdOffer
#print axioms MWG.GeneralEquilibriumExamples.cdOffer_grossSubstitute
#print axioms MWG.GeneralEquilibriumExamples.fig10aU1
#print axioms MWG.GeneralEquilibriumExamples.fig10aU2
#print axioms MWG.GeneralEquilibriumExamples.fig10aEconomy
#print axioms MWG.GeneralEquilibriumExamples.fig10a_u0
#print axioms MWG.GeneralEquilibriumExamples.fig10a_u1
#print axioms MWG.GeneralEquilibriumExamples.fig10a_ω0
#print axioms MWG.GeneralEquilibriumExamples.fig10a_ω1
#print axioms MWG.GeneralEquilibriumExamples.fig10a_lns0
#print axioms MWG.GeneralEquilibriumExamples.fig10a_lns1
#print axioms MWG.GeneralEquilibriumExamples.fig10a_lns
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_not_stronglyMonotone
#print axioms MWG.GeneralEquilibriumExamples.fig10a_dot
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_demand1
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_endowment_not_optimal
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_no_demand0
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_no_eqm
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10a_po_not_supportable
#print axioms MWG.GeneralEquilibriumExamples.sqUtility
#print axioms MWG.GeneralEquilibriumExamples.sqUtility_props
#print axioms MWG.GeneralEquilibriumExamples.sqUtility_demand_corner
#print axioms MWG.GeneralEquilibriumExamples.fig10bEconomy
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10b_no_eqm
#print axioms MWG.GeneralEquilibriumExamples.fig14Economy
#print axioms MWG.GeneralEquilibriumExamples.fig14_u2_props
#print axioms MWG.GeneralEquilibriumExamples.fig14_lns
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_14
#print axioms MWG.GeneralEquilibriumExamples.alphanseU
#print axioms MWG.GeneralEquilibriumExamples.betatrixU
#print axioms MWG.GeneralEquilibriumExamples.ex15B9Economy
#print axioms MWG.GeneralEquilibriumExamples.alphanse_demand
#print axioms MWG.GeneralEquilibriumExamples.betatrix_demand
#print axioms MWG.GeneralEquilibriumExamples.ex15B9_lns
#print axioms MWG.GeneralEquilibriumExamples.ex15B9_p0_pos
#print axioms MWG.GeneralEquilibriumExamples.quad_root_nonneg
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_9
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_9_second
#print axioms MWG.GeneralEquilibriumExamples.quasilinear_strictConcave
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_8
#print axioms MWG.GeneralEquilibriumExamples.sqrtQLEconomy
#print axioms MWG.GeneralEquilibriumExamples.sqrtQLEconomy_instance
#print axioms MWG.GeneralEquilibriumExamples.invQL_demand
#print axioms MWG.GeneralEquilibriumExamples.invQL_mem
#print axioms MWG.GeneralEquilibriumExamples.ex15B10aEconomy
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_10a
#print axioms MWG.GeneralEquilibriumExamples.quasilinear_demand_shift
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_10b
#print axioms MWG.GeneralEquilibriumExamples.kinkedPhi
#print axioms MWG.GeneralEquilibriumExamples.kinkedPhi_le
#print axioms MWG.GeneralEquilibriumExamples.kinked_demand
#print axioms MWG.GeneralEquilibriumExamples.kinkedPhi_props
#print axioms MWG.GeneralEquilibriumExamples.kinked_isDemandEqm
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_10b_counterexample
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.mk
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.u
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.Lbar
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.f
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.IsProfitMax
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.budget
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.IsConsumerOpt
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.IsWalrasEqm
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.feasible
#print axioms MWG.GeneralEquilibriumExamples.RCEconomy.IsOptimal
#print axioms MWG.GeneralEquilibriumExamples.budgetLine_eq_isoprofit
#print axioms MWG.GeneralEquilibriumExamples.budgetLine_intercept_slope
#print axioms MWG.GeneralEquilibriumExamples.rc_first_welfare
#print axioms MWG.GeneralEquilibriumExamples.rc_eqm_price_pos
#print axioms MWG.GeneralEquilibriumExamples.pareto_one_consumer_iff
#print axioms MWG.GeneralEquilibriumExamples.rc_second_welfare
#print axioms MWG.GeneralEquilibriumExamples.rc_optimal_frontier
#print axioms MWG.GeneralEquilibriumExamples.footnote_7_unique
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1a
#print axioms MWG.GeneralEquilibriumExamples.fig15C3aEconomy
#print axioms MWG.GeneralEquilibriumExamples.sqrt_le_tangent
#print axioms MWG.GeneralEquilibriumExamples.fig_15_C_3a_optimal
#print axioms MWG.GeneralEquilibriumExamples.fig_15_C_3a_no_eqm
#print axioms MWG.GeneralEquilibriumExamples.fig_15_C_3a_prices
#print axioms MWG.GeneralEquilibriumExamples.rc_budget_eq
#print axioms MWG.GeneralEquilibriumExamples.rc_consumerOpt_iff
#print axioms MWG.GeneralEquilibriumExamples.sqrt_firm_profit
#print axioms MWG.GeneralEquilibriumExamples.ex15C2Economy
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_2
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1b
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1b_sign
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1b_instance
#print axioms MWG.GeneralEquilibriumExamples.ces15C1Economy
#print axioms MWG.GeneralEquilibriumExamples.cesLeisure
#print axioms MWG.GeneralEquilibriumExamples.ces15C1_demands
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1b_not_monotone
#print axioms MWG.GeneralEquilibriumExamples.footnote_8
#print axioms MWG.GeneralEquilibriumExamples.IsOptimalInput
#print axioms MWG.GeneralEquilibriumExamples.IsFactorEqm
#print axioms MWG.GeneralEquilibriumExamples.concave_le_fderiv
#print axioms MWG.GeneralEquilibriumExamples.factorEqm_iff_foc
#print axioms MWG.GeneralEquilibriumExamples.factorEqm_revenue_max
#print axioms MWG.GeneralEquilibriumExamples.factorEqm_supergradient
#print axioms MWG.GeneralEquilibriumExamples.factorEqm_monotone
#print axioms MWG.GeneralEquilibriumExamples.factor_price_endowment_opposite
#print axioms MWG.GeneralEquilibriumExamples.productionPossibilitySet
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_2
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.mk
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.f
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.a
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.mk
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.f_nonneg
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.hom
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.a_mem
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.a_min
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.a_unique
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.a_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsModel.a_cont
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.FactorIntensity
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.dot_two
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relPrice_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.FactorIntensity.det_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c_le
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c_smul
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.a_smul
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.g
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c_eq_g
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.a_eq_rel
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.unitCost_hasDerivAt
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.g_continuousOn
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.g_eq
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.unitCost_ratio_strictMono
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.g_strictMono
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.div_g_strictMono
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.intensity_antitone
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.crs_profitMax_iff
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6a
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interior_eqm_iff
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interior_eqm_allocation
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factor_price_equalization
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.proposition_15_D_1
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_3
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_3_welfare
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.proposition_15_D_1_differential
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.outputs_cramer
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.proposition_15_D_2
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_5
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6b
#print axioms MWG.GeneralEquilibriumExamples.leontiefModel
#print axioms MWG.GeneralEquilibriumExamples.leontiefModel_isModel
#print axioms MWG.GeneralEquilibriumExamples.leontiefModel_factorIntensity
#print axioms MWG.GeneralEquilibriumExamples.leontief_instances
#print axioms MWG.GeneralEquilibriumExamples.ex15D7f
#print axioms MWG.GeneralEquilibriumExamples.ex15D7k
#print axioms MWG.GeneralEquilibriumExamples.ex15D7k_pos
#print axioms MWG.GeneralEquilibriumExamples.ex15D7_optimal_iff
#print axioms MWG.GeneralEquilibriumExamples.ex15D7alloc
#print axioms MWG.GeneralEquilibriumExamples.ex15D7w
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_7
#print axioms MWG.GeneralEquilibriumExamples.two_sqrt_add_sqrt_le
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_7_revenue
#print axioms MWG.GeneralEquilibriumExamples.concaveOn_sqrt_sum
#print axioms MWG.GeneralEquilibriumExamples.sqrtSumDeriv
#print axioms MWG.GeneralEquilibriumExamples.hasFDerivAt_sqrt_sum
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_7_foc
#print axioms MWG.GeneralEquilibriumExamples.endowment_output_identity
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_9
#print axioms MWG.GeneralEquilibriumExamples.homogeneous_demand_scale
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_9_unique_demand
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_9_counterexample
#print axioms MWG.GeneralEquilibriumExamples.IsClosedEqm
#print axioms MWG.GeneralEquilibriumExamples.onlyGood
#print axioms MWG.GeneralEquilibriumExamples.onlyGood_demand
#print axioms MWG.GeneralEquilibriumExamples.ex15D4own
#print axioms MWG.GeneralEquilibriumExamples.leontief_c0
#print axioms MWG.GeneralEquilibriumExamples.leontief_c1
#print axioms MWG.GeneralEquilibriumExamples.leontief_closedEqm_of
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_4c
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_4b
#print axioms MWG.GeneralEquilibriumExamples.IsTaxEqm
#print axioms MWG.GeneralEquilibriumExamples.no_tax_eqm
#print axioms MWG.GeneralEquilibriumExamples.partial_eqm_employment_falls
#print axioms MWG.GeneralEquilibriumExamples.general_eqm_wage_derivative
#print axioms MWG.GeneralEquilibriumExamples.wage_effect_vanishes
#print axioms MWG.GeneralEquilibriumExamples.aggregate_profit_derivative
#print axioms MWG.GeneralEquilibriumExamples.labor_bears_burden
#print axioms MWG.GeneralEquilibriumExamples.quadratic_eqm_path
#print axioms MWG.GeneralEquilibriumExamples.tcp_six_poly_nonneg
#print axioms MWG.GeneralEquilibriumExamples.tcp_six_poly_pos
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_gap
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_tangent
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_tangent_strict
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_strictConcaveOn
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_strictMonoOn
#print axioms MWG.GeneralEquilibriumExamples.tcpPowFive_continuousOn
#print axioms MWG.GeneralEquilibriumExamples.tcpAffineUtility
#print axioms MWG.GeneralEquilibriumExamples.tcpAffineUtility_continuousOn
#print axioms MWG.GeneralEquilibriumExamples.tcpAffineUtility_stronglyMonotone
#print axioms MWG.GeneralEquilibriumExamples.tcpAffineUtility_strictlyConvex
#print axioms MWG.GeneralEquilibriumExamples.tcp_eq_of_strictlyConvex
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.mk
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.u
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.Lbar
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.f
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.IsProfitMax
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.budget
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.IsConsumerOpt
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.IsWalrasEqm
#print axioms MWG.GeneralEquilibriumExamples.ex15C1cEconomy
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_u0
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_u1
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_Lbar0
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_Lbar1
#print axioms MWG.GeneralEquilibriumExamples.tcp_consumerA_opt
#print axioms MWG.GeneralEquilibriumExamples.tcp_consumerB_opt
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_profitMax
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_eqm_of
#print axioms MWG.GeneralEquilibriumExamples.ex15C1cAlloc1
#print axioms MWG.GeneralEquilibriumExamples.ex15C1cAlloc2
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1c
#print axioms MWG.GeneralEquilibriumExamples.ex15C1c_strictlyConvex
#print axioms MWG.GeneralEquilibriumExamples.tcp_eqm_price_pos
#print axioms MWG.GeneralEquilibriumExamples.tcp_crs_profitMax
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1c_crs_no_low_wage
#print axioms MWG.GeneralEquilibriumExamples.tcp_crs_consumerOpt
#print axioms MWG.GeneralEquilibriumExamples.TCEconomy.convex_budget
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1c_crs
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_C_1c_crs_wage
#print axioms MWG.GeneralEquilibriumExamples.ex15B4dUtility
#print axioms MWG.GeneralEquilibriumExamples.ex15B4dDemand
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_props
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_dot
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_opt
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_demand_eq
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_demand_five
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_demand_high
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_4d_exists
#print axioms MWG.GeneralEquilibriumExamples.ex15B4d_inferior
#print axioms MWG.GeneralEquilibriumExamples.fig10b_demand0
#print axioms MWG.GeneralEquilibriumExamples.fig10b_corner_mem
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10b_offerCurve
#print axioms MWG.GeneralEquilibriumExamples.fig_15_B_10b_offerCurve_not_preconnected
#print axioms MWG.GeneralEquilibriumExamples.cdtF
#print axioms MWG.GeneralEquilibriumExamples.cdtRatio
#print axioms MWG.GeneralEquilibriumExamples.cdtA
#print axioms MWG.GeneralEquilibriumExamples.cdtCost
#print axioms MWG.GeneralEquilibriumExamples.cdtRatio_pos
#print axioms MWG.GeneralEquilibriumExamples.cdtA_pos
#print axioms MWG.GeneralEquilibriumExamples.cdtA_ratio
#print axioms MWG.GeneralEquilibriumExamples.cdtF_cdtA
#print axioms MWG.GeneralEquilibriumExamples.cdtF_nonneg
#print axioms MWG.GeneralEquilibriumExamples.cdtF_smul
#print axioms MWG.GeneralEquilibriumExamples.cdtCost_pos
#print axioms MWG.GeneralEquilibriumExamples.cdt_geom
#print axioms MWG.GeneralEquilibriumExamples.cdt_arith
#print axioms MWG.GeneralEquilibriumExamples.cdtCost_mul_le
#print axioms MWG.GeneralEquilibriumExamples.cdtA_balanced
#print axioms MWG.GeneralEquilibriumExamples.cdt_dot_A
#print axioms MWG.GeneralEquilibriumExamples.cdtA_min
#print axioms MWG.GeneralEquilibriumExamples.cdtA_unique
#print axioms MWG.GeneralEquilibriumExamples.cdtA_continuousOn
#print axioms MWG.GeneralEquilibriumExamples.cdtModel
#print axioms MWG.GeneralEquilibriumExamples.cdtModel_isModel
#print axioms MWG.GeneralEquilibriumExamples.cdtModel_c
#print axioms MWG.GeneralEquilibriumExamples.cdtModel_factorIntensity
#print axioms MWG.GeneralEquilibriumExamples.cdModel
#print axioms MWG.GeneralEquilibriumExamples.cdModel_alpha
#print axioms MWG.GeneralEquilibriumExamples.cdModel_isModel
#print axioms MWG.GeneralEquilibriumExamples.cdModel_ratio
#print axioms MWG.GeneralEquilibriumExamples.cdModel_factorIntensity
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.c_ratio_eq_g
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.eq_of_relPrice_eq_of_c_eq
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relPrice_le_of_spec0
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relPrice_ge_of_spec1
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec0
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec1
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relPrice_lt_of_above_cone
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relPrice_gt_of_below_cone
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.RaySurjective
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.smul_relPrice_facts
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec0_of_ray
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec1_of_ray
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec0_exists
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec1_exists
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec0_unique
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6d_spec1_unique
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.unitDollarIsoquant
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.RayDifferentiable
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.f_mul_c_le
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.f_eq_ray
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_mul_a
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_mul_g_le
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_mul_g_eq
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_deriv_eq
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayPrice_lt
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.rayF_ratio_strictMono
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_6c
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_6c_counterexample
#print axioms MWG.GeneralEquilibriumExamples.cdtModel_raySurjective
#print axioms MWG.GeneralEquilibriumExamples.cdtModel_rayDifferentiable
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_6c_cdModel
#print axioms MWG.GeneralEquilibriumExamples.cd8_rpow_pair
#print axioms MWG.GeneralEquilibriumExamples.cd8_c0
#print axioms MWG.GeneralEquilibriumExamples.cd8_c1
#print axioms MWG.GeneralEquilibriumExamples.cd8What
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec0
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec1
#print axioms MWG.GeneralEquilibriumExamples.cd8ZDiv
#print axioms MWG.GeneralEquilibriumExamples.cd8What_pos
#print axioms MWG.GeneralEquilibriumExamples.cd8What_c
#print axioms MWG.GeneralEquilibriumExamples.cd8What_ratio
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec0_pos
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec1_pos
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec0_c0
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec1_c1
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec0_rel
#print axioms MWG.GeneralEquilibriumExamples.cd8WSpec1_rel
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_8_diversified
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_8_outputs
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_8_spec0
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_8_spec1
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_8
#print axioms MWG.GeneralEquilibriumExamples.IsFactorAllocation
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsEfficientAllocation
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsSupportedBy
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsSupportedAllocation
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.IsInteriorSupport
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factorRatio
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.f_smul_a
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.supported_isEfficient
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_zbar_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_identities
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_between
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_between'
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_eq
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factorRatio_antitone
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factorRatio_order_preserved
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factorRatio_order_preserved'
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.factorRatio_eq_preserved
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_1a
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.diagonal_pareto_set
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.relRatio_strictAnti
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_1b_ratios_fall
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_1b_monotone
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_1b
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.eventually_strictlyPositive_line
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.eventually_lt_of_hasDerivAt_pos
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.f_hasDerivAt_line
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.efficient_isSupported
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.interiorSupport_of_supportedBy
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_1a_pareto
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.diagonal_pareto_set_efficient
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.footnote_16
#print axioms MWG.GeneralEquilibriumExamples.leontief_f0
#print axioms MWG.GeneralEquilibriumExamples.leontief_f1
#print axioms MWG.GeneralEquilibriumExamples.leontief_output_bounds
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_1b_counterexample
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_1b_cdModel
#print axioms MWG.GeneralEquilibriumExamples.efficient_isSupported_cdModel
#print axioms MWG.GeneralEquilibriumExamples.footnote_16_leontief
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.ex15D4b_eqm_facts
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.ex15D4b_not_relPrice_lt
#print axioms MWG.GeneralEquilibriumExamples.TwoByTwo.exercise_15_D_4b_general
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_D_4b_cdModel
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.mk
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.X_eq
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.cont
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.mono
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.sconv
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.ParetoCurveHyp.ω_pos
#print axioms MWG.GeneralEquilibriumExamples.pc_exists_shrink
#print axioms MWG.GeneralEquilibriumExamples.pc_lt_add
#print axioms MWG.GeneralEquilibriumExamples.pc_smul_mem
#print axioms MWG.GeneralEquilibriumExamples.pc_inBox_iff
#print axioms MWG.GeneralEquilibriumExamples.pc_inBox_iff'
#print axioms MWG.GeneralEquilibriumExamples.pc_le_total
#print axioms MWG.GeneralEquilibriumExamples.pc_total_mem
#print axioms MWG.GeneralEquilibriumExamples.pc_zero_mem
#print axioms MWG.GeneralEquilibriumExamples.pc_transfer0
#print axioms MWG.GeneralEquilibriumExamples.pc_transfer1
#print axioms MWG.GeneralEquilibriumExamples.pc_isParetoOptimal_iff
#print axioms MWG.GeneralEquilibriumExamples.pc_po_bounds
#print axioms MWG.GeneralEquilibriumExamples.pc_a_le_b
#print axioms MWG.GeneralEquilibriumExamples.pc_isClosed_box
#print axioms MWG.GeneralEquilibriumExamples.pc_isCompact_box
#print axioms MWG.GeneralEquilibriumExamples.pc_continuousOn_u
#print axioms MWG.GeneralEquilibriumExamples.pc_isClosed_paretoSet
#print axioms MWG.GeneralEquilibriumExamples.pc_isCompact_paretoSet
#print axioms MWG.GeneralEquilibriumExamples.pc_po_injective
#print axioms MWG.GeneralEquilibriumExamples.pc_exists_po
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.paretoCurve
#print axioms MWG.GeneralEquilibriumExamples.pc_paretoCurve_spec
#print axioms MWG.GeneralEquilibriumExamples.pc_paretoCurve_u
#print axioms MWG.GeneralEquilibriumExamples.pc_eq_paretoCurve
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_7_homeomorph
#print axioms MWG.GeneralEquilibriumExamples.pc_continuous_paretoCurve
#print axioms MWG.GeneralEquilibriumExamples.pc_paretoSet_eq_image
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_7_connected
#print axioms MWG.GeneralEquilibriumExamples.pc_homothetic_le
#print axioms MWG.GeneralEquilibriumExamples.pc_homothetic_lt
#print axioms MWG.GeneralEquilibriumExamples.pc_scaled_support
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.diagonalAllocation
#print axioms MWG.GeneralEquilibriumExamples.pc_diagonal_inBox
#print axioms MWG.GeneralEquilibriumExamples.pc_diagonal_po
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_7_diagonal
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_7_homothetic
#print axioms MWG.GeneralEquilibriumExamples.pc_dot_pair
#print axioms MWG.GeneralEquilibriumExamples.pc_normalize
#print axioms MWG.GeneralEquilibriumExamples.ExchangeEconomy.QuasiSupports
#print axioms MWG.GeneralEquilibriumExamples.pc_quasiSupports_of_pos
#print axioms MWG.GeneralEquilibriumExamples.pc_paretoCurve_mem
#print axioms MWG.GeneralEquilibriumExamples.pc_continuous_u_paretoCurve
#print axioms MWG.GeneralEquilibriumExamples.pc_exists_quasiSupports
#print axioms MWG.GeneralEquilibriumExamples.pc_isClosed_quasiSupports
#print axioms MWG.GeneralEquilibriumExamples.pc_isClosed_exists_Icc
#print axioms MWG.GeneralEquilibriumExamples.pc_quasiSupports_uIcc
#print axioms MWG.GeneralEquilibriumExamples.pc_exists_better_cheaper
#print axioms MWG.GeneralEquilibriumExamples.pc_quasiSupports_pos
#print axioms MWG.GeneralEquilibriumExamples.pc_walras_of_quasiSupports
#print axioms MWG.GeneralEquilibriumExamples.pc_isParetoOptimal_with
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_10d_lower_eqm
#print axioms MWG.GeneralEquilibriumExamples.exercise_15_B_10d
#print axioms MWG.GeneralEquilibriumExamples.sqrtUtility
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_total
#print axioms MWG.GeneralEquilibriumExamples.sqrtUtility_stronglyMonotone
#print axioms MWG.GeneralEquilibriumExamples.sqrtUtility_strictlyConvex
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_hyp
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_homothetic
#print axioms MWG.GeneralEquilibriumExamples.sqrtUtility_le_diag
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_half_po
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_paretoSet
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_transfer_eqm
#print axioms MWG.GeneralEquilibriumExamples.sqrtEconomy_15_B_10d
