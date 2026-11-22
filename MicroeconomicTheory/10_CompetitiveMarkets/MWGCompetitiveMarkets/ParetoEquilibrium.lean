/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Profit
import MWGClassicalDemand.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Pareto optimality and competitive equilibria (MWG Section 10.B, pp. 312-316)

An economy has consumers `i : ι`, firms `j : κ` and `L` goods. Consumer `i` has consumption set
`Xᵢ ⊆ ℝ^L` and utility `uᵢ`; firm `j` has production set `Yⱼ ⊆ ℝ^L`; `ω` is the total
endowment.

* **Definition 10.B.1**: allocations and feasibility (`Economy.IsFeasible`).
* **Definition 10.B.2**: Pareto optimality (`Economy.IsParetoOptimal`), the utility possibility
  set `U` (p. 313) and the fact that Pareto optimal allocations are exactly those whose utility
  vector is undominated in `U` (`isParetoOptimal_iff_undominated`).
* **Definition 10.B.3**: competitive (Walrasian) equilibrium of a private ownership economy
  (`PrivEconomy.IsCompetitiveEqm`). Profit maximization is membership in Chapter 5's supply
  correspondence `supply Yⱼ p` and utility maximization is membership in Chapter 3's demand
  `walrasianDemandOn Xᵢ uᵢ p w` with wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ`.
* **Exercise 10.B.2** (p. 316): equilibria are invariant to scaling prices by `α > 0` (we do not
  need `p ≫ 0`).
* **Lemma 10.B.1** (p. 316): with `p ≫ 0`, budgets holding with equality and shares summing to
  one, clearing of all markets but one implies clearing of the last.
* **Exercise 10.B.1** (p. 344): strong and weak Pareto efficiency. (a) strong implies weak;
  (b) with `Xᵢ = ℝ^L_+`, continuous and strongly monotone utilities the notions coincide. We
  prove (b) without the interiority assumption (`exercise_10_B_1b_general`), so interiority is
  not needed (part of the answer to (c)); (c) an example where they differ when strong
  monotonicity fails.
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties

/-- **Section 10.B** (MWG, p. 312). An economy: consumption sets `Xᵢ`, utilities `uᵢ`, the
total endowment `ω` and production sets `Yⱼ`. -/
structure Economy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (Fin L → ℝ)
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Total endowment. -/
  ω : Fin L → ℝ
  /-- Production sets. -/
  Y : κ → Set (Fin L → ℝ)

/-- **Definition 10.B.1** (MWG, p. 312). An economic allocation: consumption vectors `xᵢ` and
production vectors `yⱼ`. -/
structure Allocation (ι κ : Type*) (L : ℕ) where
  /-- Consumption vectors. -/
  x : ι → Fin L → ℝ
  /-- Production vectors. -/
  y : κ → Fin L → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Definition 10.B.1** (MWG, p. 312). `xᵢ ∈ Xᵢ` and `yⱼ ∈ Yⱼ`. -/
def Economy.IsAllocation (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  (∀ i, a.x i ∈ E.X i) ∧ ∀ j, a.y j ∈ E.Y j

/-- **Definition 10.B.1** (MWG, p. 312). A feasible allocation:
`∑ᵢ x_{ℓi} ≤ ω_ℓ + ∑ⱼ y_{ℓj}` for every good `ℓ`. -/
def Economy.IsFeasible (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsAllocation a ∧ ∀ l, ∑ i, a.x i l ≤ E.ω l + ∑ j, a.y j l

/-- **Definition 10.B.2** (MWG, p. 313). A feasible allocation is Pareto optimal if no feasible
allocation makes every consumer weakly and some consumer strictly better off. -/
def Economy.IsParetoOptimal (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ (∀ i, E.u i (a.x i) ≤ E.u i (a'.x i)) ∧
    ∃ i, E.u i (a.x i) < E.u i (a'.x i)

/-- **Definition 10.B.1** (MWG, p. 312), unfolded. -/
theorem definition_10_B_1 (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsFeasible a ↔ (∀ i, a.x i ∈ E.X i) ∧ (∀ j, a.y j ∈ E.Y j) ∧
      ∀ l, ∑ i, a.x i l ≤ E.ω l + ∑ j, a.y j l := by
  unfold Economy.IsFeasible Economy.IsAllocation
  tauto

/-- **Definition 10.B.2** (MWG, p. 313), unfolded. -/
theorem definition_10_B_2 (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsParetoOptimal a ↔ E.IsFeasible a ∧ ∀ a', E.IsFeasible a' →
      (∀ i, E.u i (a.x i) ≤ E.u i (a'.x i)) → ∀ i, E.u i (a'.x i) ≤ E.u i (a.x i) := by
  unfold Economy.IsParetoOptimal
  constructor
  · rintro ⟨h, hno⟩
    exact ⟨h, fun a' ha' hle i => not_lt.1 fun hlt => hno ⟨a', ha', hle, i, hlt⟩⟩
  · rintro ⟨h, hall⟩
    exact ⟨h, fun ⟨a', ha', hle, i, hlt⟩ => absurd (hall a' ha' hle i) (not_le.2 hlt)⟩

/-- **Section 10.B** (MWG, p. 313). The utility possibility set
`U = {v : ∃ feasible allocation with vᵢ ≤ uᵢ(xᵢ) for all i}` (the book writes it for `I = 2`). -/
def Economy.utilityPossibilitySet (E : Economy ι κ L) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i ≤ E.u i (a.x i)}

/-- **Section 10.B** (MWG, p. 313, Figure 10.B.1). A feasible allocation is Pareto optimal if and
only if its utility vector lies on the "northeast boundary" of `U`: no element of `U` weakly
dominates it with a strict improvement for someone. -/
theorem isParetoOptimal_iff_undominated (E : Economy ι κ L) (a : Allocation ι κ L)
    (ha : E.IsFeasible a) :
    E.IsParetoOptimal a ↔ ∀ v ∈ E.utilityPossibilitySet, (∀ i, E.u i (a.x i) ≤ v i) →
      ∀ i, v i = E.u i (a.x i) := by
  constructor
  · rintro ⟨-, hno⟩ v ⟨a', ha', hv⟩ hle i
    by_contra hne
    exact hno ⟨a', ha', fun k => (hle k).trans (hv k),
      ⟨i, lt_of_lt_of_le (lt_of_le_of_ne (hle i) (Ne.symm hne)) (hv i)⟩⟩
  · intro h
    refine ⟨ha, ?_⟩
    rintro ⟨a', ha', hle, i, hi⟩
    have := h (fun k => E.u k (a'.x k)) ⟨a', ha', fun k => le_rfl⟩ hle i
    exact (ne_of_gt hi) this

/-- The utility vector of a feasible allocation lies in `U`. -/
theorem mem_utilityPossibilitySet (E : Economy ι κ L) {a : Allocation ι κ L}
    (ha : E.IsFeasible a) : (fun i => E.u i (a.x i)) ∈ E.utilityPossibilitySet :=
  ⟨a, ha, fun _ => le_rfl⟩

/-- **Section 10.B** (MWG, p. 314). A private ownership economy: consumption sets, utilities,
production sets, individual endowments `ωᵢ` and profit shares `θᵢⱼ`. -/
structure PrivEconomy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (Fin L → ℝ)
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Production sets. -/
  Y : κ → Set (Fin L → ℝ)
  /-- Individual endowments `ωᵢ`. -/
  ωi : ι → Fin L → ℝ
  /-- Profit shares `θᵢⱼ`. -/
  θ : ι → κ → ℝ

/-- The underlying economy, with total endowment `ω = ∑ᵢ ωᵢ` (MWG, p. 314). -/
def PrivEconomy.toEconomy (E : PrivEconomy ι κ L) : Economy ι κ L where
  X := E.X
  u := E.u
  ω := ∑ i, E.ωi i
  Y := E.Y

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` (MWG, p. 314, (10.B.2)). -/
def PrivEconomy.wealth (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (i : ι) : ℝ :=
  p ⬝ᵥ E.ωi i + ∑ j, E.θ i j * (p ⬝ᵥ a.y j)

/-- **Definition 10.B.3** (MWG, p. 314). A competitive (Walrasian) equilibrium: (i) every `yⱼ`
maximizes profit on `Yⱼ` (Chapter 5's `supply`), (ii) every `xᵢ` maximizes `uᵢ` on the budget set
in `Xᵢ` (Chapter 3's `walrasianDemandOn`), (iii) every market clears with equality (10.B.3). -/
def PrivEconomy.IsCompetitiveEqm (E : PrivEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) : Prop :=
  (∀ j, a.y j ∈ supply (E.Y j) p) ∧
  (∀ i, a.x i ∈ walrasianDemandOn (E.X i) (E.u i) p (E.wealth a p i)) ∧
  ∀ l, ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l

/-- **Definition 10.B.3** (MWG, p. 314), unfolded into (10.B.1)-(10.B.3). -/
theorem definition_10_B_3 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ) :
    E.IsCompetitiveEqm a p ↔
      (∀ j, a.y j ∈ E.Y j ∧ ∀ y ∈ E.Y j, p ⬝ᵥ y ≤ p ⬝ᵥ a.y j) ∧
      (∀ i, (a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ E.wealth a p i) ∧
        ∀ x ∈ E.X i, p ⬝ᵥ x ≤ E.wealth a p i → E.u i x ≤ E.u i (a.x i)) ∧
      ∀ l, ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l := by
  unfold PrivEconomy.IsCompetitiveEqm supply walrasianDemandOn budgetSetOn
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx hb => (h2 i).2 x ⟨hx, hb⟩⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx => (h2 i).2 x hx.1 hx.2⟩, h3⟩

/-- A competitive equilibrium allocation is feasible (market clearing (10.B.3) gives
feasibility (Definition 10.B.1)). -/
theorem PrivEconomy.IsCompetitiveEqm.isFeasible {E : PrivEconomy ι κ L}
    {a : Allocation ι κ L} {p : Fin L → ℝ} (h : E.IsCompetitiveEqm a p) :
    E.toEconomy.IsFeasible a := by
  refine ⟨⟨fun i => (h.2.1 i).1.1, fun j => (h.1 j).1⟩, fun l => ?_⟩
  simp only [PrivEconomy.toEconomy, Finset.sum_apply]
  exact (h.2.2 l).le

/-- **Exercise 10.B.2** (MWG, p. 344; p. 316). If `(x*, y*)` and `p*` form a competitive
equilibrium, so do `(x*, y*)` and `αp*` for every `α > 0`. (The book assumes `p* ≫ 0`; this is
not needed.) -/
theorem exercise_10_B_2 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (h : E.IsCompetitiveEqm a p) {α : ℝ} (hα : 0 < α) : E.IsCompetitiveEqm a (α • p) := by
  rw [definition_10_B_3] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  have hw : ∀ i, E.wealth a (α • p) i = α * E.wealth a p i := by
    intro i
    simp only [PrivEconomy.wealth, smul_dotProduct, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun j => ⟨(h1 j).1, fun y hy => ?_⟩, fun i => ⟨⟨(h2 i).1.1, ?_⟩, fun x hx hb => ?_⟩, h3⟩
  · simp only [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left ((h1 j).2 y hy) hα.le
  · rw [hw, smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h2 i).1.2 hα.le
  · rw [hw, smul_dotProduct, smul_eq_mul] at hb
    exact (h2 i).2 x hx (le_of_mul_le_mul_left hb hα)

/-- **Lemma 10.B.1** (MWG, p. 316). Let `p` have `p_k > 0` (the book assumes `p ≫ 0`), let the
shares of each firm sum to one, let every budget constraint hold with equality and let every
market `ℓ ≠ k` clear. Then market `k` clears. -/
theorem lemma_10_B_1 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ) (k : Fin L)
    (hpk : 0 < p k) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    (hbudget : ∀ i, p ⬝ᵥ a.x i = E.wealth a p i)
    (hclear : ∀ l, l ≠ k → ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l) :
    ∑ i, a.x i k = ∑ i, E.ωi i k + ∑ j, a.y j k := by
  set z : Fin L → ℝ := ∑ i, a.x i - ∑ i, E.ωi i - ∑ j, a.y j with hz
  have hzl : ∀ l, z l = ∑ i, a.x i l - ∑ i, E.ωi i l - ∑ j, a.y j l := fun l => by
    simp [hz, Finset.sum_apply]
  have htot : p ⬝ᵥ z = 0 := by
    rw [hz, dotProduct_sub, dotProduct_sub, dotProduct_sum, dotProduct_sum, dotProduct_sum,
      Finset.sum_congr rfl fun i _ => hbudget i]
    unfold PrivEconomy.wealth
    rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun i j => E.θ i j * (p ⬝ᵥ a.y j))]
    simp only [← Finset.sum_mul, hθ, one_mul]
    ring
  have hzero : ∀ l, l ≠ k → z l = 0 := fun l hl => by rw [hzl, hclear l hl]; ring
  have hk : p ⬝ᵥ z = p k * z k := by
    unfold dotProduct
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hzero l hl, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h)]
  rw [hk] at htot
  have := (mul_eq_zero.1 htot).resolve_left hpk.ne'
  rw [hzl] at this
  linarith

/-- **Lemma 10.B.1** (MWG, p. 316) with the book's hypothesis `p ≫ 0`. -/
theorem lemma_10_B_1_strictlyPositive (E : PrivEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (hp : StrictlyPositive p) (k : Fin L) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    (hbudget : ∀ i, p ⬝ᵥ a.x i = E.wealth a p i)
    (hclear : ∀ l, l ≠ k → ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l) :
    ∑ i, a.x i k = ∑ i, E.ωi i k + ∑ j, a.y j k :=
  lemma_10_B_1 E a p k (hp k) hθ hbudget hclear

/-! ## Exercise 10.B.1: strong and weak Pareto efficiency -/

/-- **Exercise 10.B.1** (MWG, p. 344). Weak Pareto efficiency: no feasible allocation makes all
consumers strictly better off. -/
def Economy.IsWeaklyParetoOptimal (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ ∀ i, E.u i (a.x i) < E.u i (a'.x i)

/-- **Exercise 10.B.1(a)** (MWG, p. 344). A strongly Pareto efficient allocation (Definition
10.B.2) is weakly Pareto efficient (there is at least one consumer). -/
theorem exercise_10_B_1a [Nonempty ι] (E : Economy ι κ L) (a : Allocation ι κ L)
    (h : E.IsParetoOptimal a) : E.IsWeaklyParetoOptimal a := by
  refine ⟨h.1, fun ⟨a', ha', hlt⟩ => h.2 ⟨a', ha', fun i => (hlt i).le, ?_⟩⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨i, hlt i⟩

/-- **Exercise 10.B.1(b)** (MWG, p. 344), without interiority. If every `Xᵢ = ℝ^L_+` and every
`uᵢ` is continuous on `ℝ^L_+` and strongly monotone, then a weakly Pareto efficient allocation is
strongly Pareto efficient. -/
theorem exercise_10_B_1b_general (E : Economy ι κ L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (E.u i)))
    (a : Allocation ι κ L) (h : E.IsWeaklyParetoOptimal a) : E.IsParetoOptimal a := by
  classical
  refine ⟨h.1, ?_⟩
  rintro ⟨a', ha', hle, i₀, hi₀⟩
  apply h.2
  have hmem : ∀ i, a'.x i ∈ nonnegOrthant L := fun i => hX i ▸ ha'.1.1 i
  have hmemA : ∀ i, a.x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1.1 i
  -- strict utility comparisons from strong monotonicity
  have hsm : ∀ i, ∀ x y : Fin L → ℝ, x ∈ nonnegOrthant L → y ∈ nonnegOrthant L → x ≤ y →
      y ≠ x → E.u i x < E.u i y := by
    intro i x y hx hy hxy hne
    have := hmono i x hx y hy hxy hne
    exact lt_of_not_ge this.2
  -- `a'.x i₀ ≠ 0`
  have hne0 : a'.x i₀ ≠ 0 := by
    intro h0
    have h00 : (0 : Fin L → ℝ) ∈ nonnegOrthant L := fun _ => le_rfl
    have hle0 : E.u i₀ 0 ≤ E.u i₀ (a.x i₀) := by
      by_cases he : a.x i₀ = 0
      · rw [he]
      · exact (hsm i₀ 0 (a.x i₀) h00 (hmemA i₀) (hmemA i₀) he).le
    rw [h0] at hi₀
    linarith
  by_cases hcard : Fintype.card ι = 1
  · refine ⟨a', ha', fun i => ?_⟩
    have : i = i₀ := Fintype.card_le_one_iff.1 hcard.le i i₀
    rw [this]; exact hi₀
  -- continuity along the ray `t ↦ (1 - t) • a'.x i₀`
  have hray : ContinuousWithinAt (fun t : ℝ => E.u i₀ ((1 - t) • a'.x i₀)) (Set.Icc 0 1) 0 := by
    have hmap : Set.MapsTo (fun t : ℝ => (1 - t) • a'.x i₀) (Set.Icc 0 1) (nonnegOrthant L) := by
      intro t ht l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith [ht.2]) (hmem i₀ l)
    have hc : ContinuousWithinAt (fun t : ℝ => (1 - t) • a'.x i₀) (Set.Icc 0 1) 0 :=
      ((continuous_const.sub continuous_id).smul continuous_const).continuousWithinAt
    have h0mem : (fun t : ℝ => (1 - t) • a'.x i₀) 0 ∈ nonnegOrthant L := hmap ⟨le_rfl, zero_le_one⟩
    exact ContinuousWithinAt.comp (f := fun t : ℝ => (1 - t) • a'.x i₀) (hcont i₀ _ h0mem) hc hmap
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Icc 0 1),
      E.u i₀ (a.x i₀) < E.u i₀ ((1 - t) • a'.x i₀) := by
    have := hray.eventually (lt_mem_nhds (by simpa using hi₀))
    exact this
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioc 0 1),
      E.u i₀ (a.x i₀) < E.u i₀ ((1 - t) • a'.x i₀) :=
    nhdsWithin_mono _ Set.Ioc_subset_Icc_self hev
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioc 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨δ, hδu, hδ⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hn : (1 : ℝ) < Fintype.card ι := by
    have : 1 < Fintype.card ι := by
      have := (Fintype.card_pos_iff.2 ⟨i₀⟩ : 0 < Fintype.card ι)
      omega
    exact_mod_cast this
  set c : ℝ := δ / (Fintype.card ι - 1) with hc
  have hc0 : 0 < c := div_pos hδ.1 (by linarith)
  set coeff : ι → ℝ := fun i => c - (if i = i₀ then c + δ else 0) with hcoeff
  refine ⟨⟨fun i => a'.x i + coeff i • a'.x i₀, a'.y⟩, ⟨⟨fun i => ?_, ha'.1.2⟩, fun l => ?_⟩, ?_⟩
  · rw [hX i]
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcoeff]
    by_cases hi : i = i₀
    · subst hi
      simp only [↓reduceIte]
      have : a'.x i l + (c - (c + δ)) * a'.x i l = (1 - δ) * a'.x i l := by ring
      rw [this]
      exact mul_nonneg (by linarith [hδ.2]) (hmem i l)
    · simp only [hi, ↓reduceIte, sub_zero]
      exact add_nonneg (hmem i l) (mul_nonneg hc0.le (hmem i₀ l))
  · have hsum : ∑ i, coeff i = 0 := by
      simp only [hcoeff, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, nsmul_eq_mul, hc]
      have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    have : ∑ i, (a'.x i + coeff i • a'.x i₀) l = ∑ i, a'.x i l + (∑ i, coeff i) * a'.x i₀ l := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [this, hsum, zero_mul, add_zero]
    exact ha'.2 l
  · intro i
    by_cases hi : i = i₀
    · subst hi
      have : a'.x i + coeff i • a'.x i = (1 - δ) • a'.x i := by
        simp only [hcoeff, ↓reduceIte]
        ext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only
      rw [this]
      exact hδu
    · simp only
      have hco : coeff i = c := by simp [hcoeff, hi]
      rw [hco]
      refine (hle i).trans_lt (hsm i _ _ (hmem i) ?_ ?_ ?_)
      · intro l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (hmem i l) (mul_nonneg hc0.le (hmem i₀ l))
      · intro l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith [mul_nonneg hc0.le (hmem i₀ l)]
      · intro heq
        apply hne0
        have h2 : c • a'.x i₀ = 0 := by
          have := congrArg (fun v => v - a'.x i) heq
          simpa using this
        exact (smul_eq_zero.1 h2).resolve_left hc0.ne'

/-- **Exercise 10.B.1(b)** (MWG, p. 344), as stated: for an interior outcome (every `xᵢ ≫ 0`)
with `Xᵢ = ℝ^L_+` and continuous strongly monotone utilities, strong and weak Pareto efficiency
are equivalent. -/
theorem exercise_10_B_1b [Nonempty ι] (E : Economy ι κ L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (E.u i)))
    (a : Allocation ι κ L) (_hint : ∀ i l, 0 < a.x i l) :
    E.IsParetoOptimal a ↔ E.IsWeaklyParetoOptimal a :=
  ⟨exercise_10_B_1a E a, exercise_10_B_1b_general E hX hcont hmono a⟩

/-- The economy of Exercise 10.B.1(c): one good, two consumers, one firm with `Y = {0}`, total
endowment `1`; consumer `0` is indifferent among all bundles (`u₀ = 0`), consumer `1` has
`u₁(x) = x`. -/
def exercise_10_B_1c_economy : Economy (Fin 2) (Fin 1) 1 where
  X := fun _ => nonnegOrthant 1
  u := fun i x => if i = 0 then 0 else x 0
  ω := fun _ => 1
  Y := fun _ => {0}

/-- **Exercise 10.B.1(c)** (MWG, p. 344). The two notions differ without strong monotonicity:
giving the whole endowment to the indifferent consumer is weakly but not strongly Pareto
efficient. (Interiority alone does not matter: `exercise_10_B_1b_general`.) -/
theorem exercise_10_B_1c :
    exercise_10_B_1c_economy.IsWeaklyParetoOptimal ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ ∧
    ¬ exercise_10_B_1c_economy.IsParetoOptimal ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ := by
  have hfeas : exercise_10_B_1c_economy.IsFeasible ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ := by
    refine ⟨⟨fun i l => ?_, fun j => rfl⟩, fun l => ?_⟩
    · change (0 : ℝ) ≤ if i = 0 then 1 else 0
      split_ifs <;> norm_num
    · simp [exercise_10_B_1c_economy]
  refine ⟨⟨hfeas, ?_⟩, ?_⟩
  · rintro ⟨a', -, h⟩
    have := h 0
    simp [exercise_10_B_1c_economy] at this
  · rintro ⟨-, hno⟩
    apply hno
    refine ⟨⟨fun i _ => if i = 0 then 0 else 1, 0⟩, ⟨⟨fun i l => ?_, fun j => rfl⟩, fun l => ?_⟩,
      fun i => ?_, ⟨1, ?_⟩⟩
    · change (0 : ℝ) ≤ if i = 0 then 0 else 1
      split_ifs <;> norm_num
    · simp [exercise_10_B_1c_economy, Fin.sum_univ_two]
    · fin_cases i <;> simp [exercise_10_B_1c_economy]
    · simp [exercise_10_B_1c_economy]

end MWG.CompetitiveMarkets
