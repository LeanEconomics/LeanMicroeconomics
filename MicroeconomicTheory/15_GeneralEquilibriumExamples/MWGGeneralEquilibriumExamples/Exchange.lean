/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ParetoEquilibrium
import MWGClassicalDemand.UMPBasic
import MWGClassicalDemand.PrefProperties

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
