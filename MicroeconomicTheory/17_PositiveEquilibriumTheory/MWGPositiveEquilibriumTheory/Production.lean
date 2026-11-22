/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceBrouwer
import MWGClassicalDemand.AppendixMH

/-!
# Production economies and the production inclusive excess demand (MWG Section 17.B, pp. 582-583;
Exercise 17.B.4, p. 642)

* Supply with closed, strictly convex, bounded above production sets containing `0`: the profit
  maximizing vector `yⱼ(p)` exists and is unique at `p ≫ 0` (`ySup`, `ySup_mem`,
  `supply_subsingleton`), and `p ↦ yⱼ(p)` is continuous on `ℝ^L_{++}` (`continuousOn_ySup`).
* A production economy `ProdEconomy` (consumers on `ℝ^L₊` with utilities, endowments, shares;
  firms) and its **production inclusive excess demand function (17.B.3)** `prodExcessDemand`:
  `z̃(p) = ∑ᵢ xᵢ(p, p·ωᵢ + ∑ⱼ θᵢⱼ πⱼ(p)) - ∑ᵢ ωᵢ - ∑ⱼ yⱼ(p)`.
* `p` is a Walrasian equilibrium price vector iff `z̃(p) = 0` (`prod_eqm_iff`).
* **Exercise 17.B.4** (`exercise_17_B_4`): `z̃` satisfies (i)-(v) of Proposition 17.B.2 when a
  strictly positive aggregate consumption bundle is producible. A concrete instance with a disc
  technology is `discEconomy_isStandard`.
* **Footnote 4** (`footnote_17_4`): with set-valued supply, `p` is an equilibrium price vector
  iff `0 ∈ z̃(p)` for the production inclusive excess demand correspondence.

Correction: Exercise 17.B.4 also needs `0 ∈ Yⱼ` (or some other guarantee of nonnegative
wealth). With a disc technology not containing `0`, owned by a consumer without endowment, all
the printed hypotheses hold but that consumer's wealth is negative at every price vector and no
Walrasian equilibrium exists (`zeroMem_needed`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.Production
open MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {L : ℕ}

/-! ### Supply with strictly convex technologies -/

/-- For `y ∈ Y` with `y ≤ b` and `p·y ≥ 0` at `p ≫ 0`, every coordinate is bounded below:
`pₖ yₖ ≥ -∑ⱼ pⱼ |bⱼ|`. -/
theorem supply_coord_lower {Y : Set (Fin L → ℝ)} {b : Fin L → ℝ} (hb : ∀ y ∈ Y, y ≤ b)
    {p y : Fin L → ℝ} (hp : p ∈ posOrthant L) (hy : y ∈ Y) (h0 : 0 ≤ p ⬝ᵥ y) (k : Fin L) :
    -(∑ j, p j * |b j|) ≤ p k * y k := by
  have hterm : ∀ j ∈ Finset.univ, 0 ≤ p j * (|b j| - y j) := fun j _ =>
    mul_nonneg (hp j).le (by linarith [hb y hy j, le_abs_self (b j)])
  have h1 := Finset.single_le_sum hterm (Finset.mem_univ k)
  have h2 : ∑ j, p j * (|b j| - y j) = ∑ j, p j * |b j| - p ⬝ᵥ y := by
    simp [mul_sub, Finset.sum_sub_distrib, dotProduct]
  rw [h2] at h1
  have h3 : 0 ≤ p k * |b k| := mul_nonneg (hp k).le (abs_nonneg _)
  nlinarith

/-- **Section 17.B** (MWG, p. 582). A closed production set, bounded above and containing `0`, has
a profit maximizing production vector at every `p ≫ 0`. -/
theorem supply_nonempty {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y)
    (hYb : ∃ b : Fin L → ℝ, ∀ y ∈ Y, y ≤ b) (hY0 : (0 : Fin L → ℝ) ∈ Y) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) : (supply Y p).Nonempty := by
  obtain ⟨b, hb⟩ := hYb
  set C := ∑ j, p j * |b j|
  set S := Y ∩ {y | 0 ≤ p ⬝ᵥ y}
  have hdot : Continuous fun y : Fin L → ℝ => p ⬝ᵥ y := by
    simp only [dotProduct]
    fun_prop
  have hSsub : S ⊆ Set.Icc (fun k => -C / p k) b := fun y hy =>
    ⟨fun k => by
      rw [div_le_iff₀ (hp k)]
      have := supply_coord_lower hb hp hy.1 hy.2 k
      linarith [mul_comm (y k) (p k)], hb y hy.1⟩
  have hSc : IsClosed S := hYc.inter (isClosed_le continuous_const hdot)
  have hne : S.Nonempty := ⟨0, hY0, by simp⟩
  obtain ⟨y, hy, hmax⟩ := (isCompact_Icc.of_isClosed_subset hSc hSsub).exists_isMaxOn hne
    hdot.continuousOn
  refine ⟨y, hy.1, fun y' hy' => ?_⟩
  by_cases h : 0 ≤ p ⬝ᵥ y'
  · exact hmax ⟨hy', h⟩
  · have := hy.2
    simp only [Set.mem_ofPred_eq] at this
    linarith

/-- **Proposition 5.C.1(v)**. With a strictly convex production set, supply at `p ≫ 0` has at
most one element. -/
theorem supply_subsingleton {Y : Set (Fin L → ℝ)} (hYs : StrictConvex ℝ Y) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) : (supply Y p).Subsingleton := by
  by_cases h : p = 0
  · intro a _ b _
    funext l
    have := hp l
    rw [h] at this
    exact absurd this (lt_irrefl 0)
  · exact proposition_5_C_1_v_strict hYs h

/-- **Section 17.B** (MWG, p. 582). The profit maximizing production vector `yⱼ(p)` as a
function: the element of `supply Y p` when nonempty, `0` otherwise. -/
noncomputable def ySup (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Fin L → ℝ :=
  open Classical in if h : (supply Y p).Nonempty then h.some else 0

/-- `yⱼ(p)` maximizes profit when supply is nonempty. -/
theorem ySup_mem {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ} (h : (supply Y p).Nonempty) :
    ySup Y p ∈ supply Y p := by
  unfold ySup
  simp only [h, ↓reduceDIte]
  exact h.some_mem

/-- Supply is homogeneous of degree zero (Proposition 5.C.1(iv)). -/
theorem ySup_smul (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 < α) :
    ySup Y (α • p) = ySup Y p := by
  unfold ySup
  rw [proposition_5_C_1_iv Y p hα]

/-- **Section 17.B** (MWG, p. 582). With a closed, strictly convex production set that is bounded
above and contains `0`, the supply function `p ↦ yⱼ(p)` is continuous on `ℝ^L_{++}`: along
`pⁿ → p ≫ 0` supplies eventually lie in a fixed box, and every limit point maximizes profit at
`p`, so equals `yⱼ(p)`. -/
theorem continuousOn_ySup {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y) (hYs : StrictConvex ℝ Y)
    (hYb : ∃ b : Fin L → ℝ, ∀ y ∈ Y, y ≤ b) (hY0 : (0 : Fin L → ℝ) ∈ Y) :
    ContinuousOn (ySup Y) (posOrthant L) := by
  have hYb' := hYb
  obtain ⟨b, hb⟩ := hYb'
  apply appendixMH_continuousOn_of_seq
  intro ps p hps hp hlim
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨c, hc0, hcp⟩ := exists_pos_le_of_strictlyPositive hp
  set C := ∑ j, p j * |b j| + 1 with hCdef
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ j, p j * |b j| := Finset.sum_nonneg fun j _ => mul_nonneg (hp j).le (abs_nonneg _)
    linarith
  have hPn : Tendsto (fun m => ps (ns m)) atTop (𝓝 p) := hlim.comp hns
  have hsumC : ∀ᶠ m in atTop, ∑ j, ps (ns m) j * |b j| < C := by
    have ht : Tendsto (fun m => ∑ j, ps (ns m) j * |b j|) atTop (𝓝 (∑ j, p j * |b j|)) :=
      tendsto_finsetSum _ fun j _ => (((continuous_apply j).tendsto p).comp hPn).mul_const _
    exact ht.eventually (gt_mem_nhds (by linarith))
  have hcev : ∀ᶠ m in atTop, ∀ k, c / 2 < ps (ns m) k := by
    rw [eventually_all]
    intro k
    exact (((continuous_apply k).tendsto p).comp hPn).eventually
      (lt_mem_nhds (by linarith [hcp k]))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsumC.and hcev)
  have hsup : ∀ m, ySup Y (ps m) ∈ supply Y (ps m) := fun m =>
    ySup_mem (supply_nonempty hYc hYb hY0 (hps m))
  have hbox : ∀ m, ySup Y (ps (ns (m + N))) ∈ Set.Icc (fun _ => -(2 * C / c)) b := by
    intro m
    have hy := hsup (ns (m + N))
    have h0 : 0 ≤ ps (ns (m + N)) ⬝ᵥ ySup Y (ps (ns (m + N))) := by
      simpa using hy.2 0 hY0
    obtain ⟨h1, h2⟩ := hN (m + N) (by omega)
    refine ⟨fun k => ?_, hb _ hy.1⟩
    have hl := supply_coord_lower hb (hps _) hy.1 h0 k
    have hk := h2 k
    have heq : -(2 * C / c) = (-(2 * C)) / c := by ring
    change -(2 * C / c) ≤ ySup Y (ps (ns (m + N))) k
    rw [heq, div_le_iff₀ hc0]
    rcases le_or_gt 0 (ySup Y (ps (ns (m + N))) k) with h3 | h3
    · nlinarith
    · nlinarith
  obtain ⟨y', -, ψ, hψ, hy'⟩ := isCompact_Icc.tendsto_subseq hbox
  have hPψ : Tendsto (fun k => ps (ns (ψ k + N))) atTop (𝓝 p) :=
    hlim.comp (hns.comp ((tendsto_add_atTop_nat N).comp hψ.tendsto_atTop))
  have hmem : y' ∈ supply Y p := by
    refine ⟨hYc.mem_of_tendsto hy' (Eventually.of_forall fun k => (hsup _).1), fun y'' hy'' => ?_⟩
    exact le_of_tendsto_of_tendsto (appendixA_tendsto_dotProduct_seq hPψ tendsto_const_nhds)
      (appendixA_tendsto_dotProduct_seq hPψ hy')
      (Eventually.of_forall fun k => (hsup _).2 y'' hy'')
  have heq : y' = ySup Y p :=
    supply_subsingleton hYs hp hmem (ySup_mem (supply_nonempty hYc hYb hY0 hp))
  exact ⟨fun k => ψ k + N, by rw [← heq]; exact hy'⟩

/-- Profits `πⱼ(p) = p·yⱼ(p)` are continuous on `ℝ^L_{++}`. -/
theorem continuousOn_profit {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y) (hYs : StrictConvex ℝ Y)
    (hYb : ∃ b : Fin L → ℝ, ∀ y ∈ Y, y ≤ b) (hY0 : (0 : Fin L → ℝ) ∈ Y) :
    ContinuousOn (fun p => p ⬝ᵥ ySup Y p) (posOrthant L) := by
  have hy := continuousOn_ySup hYc hYs hYb hY0
  simp only [dotProduct]
  exact continuousOn_finsetSum _ fun l _ =>
    (continuous_apply l).continuousOn.mul ((continuous_apply l).comp_continuousOn hy)

/-! ### Production economies and (17.B.3) -/

/-- **Section 17.B** (MWG, p. 582). A private ownership production economy with consumption sets
`ℝ^L₊`: utilities `uᵢ`, endowments `ωᵢ`, production sets `Yⱼ` and shares `θᵢⱼ`. -/
structure ProdEconomy (ι κ : Type*) (L : ℕ) where
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Endowments. -/
  ω : ι → Fin L → ℝ
  /-- Production sets. -/
  Y : κ → Set (Fin L → ℝ)
  /-- Profit shares. -/
  θ : ι → κ → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θᵢⱼ πⱼ(p)`. -/
noncomputable def ProdEconomy.wealth (E : ProdEconomy ι κ L) (i : ι) (p : Fin L → ℝ) : ℝ :=
  p ⬝ᵥ E.ω i + ∑ j, E.θ i j * (p ⬝ᵥ ySup (E.Y j) p)

/-- Total endowment plus aggregate supply, `∑ᵢ ωᵢ + ∑ⱼ yⱼ(p)`. -/
noncomputable def ProdEconomy.supplyTotal (E : ProdEconomy ι κ L) (p : Fin L → ℝ) :
    Fin L → ℝ :=
  ∑ i, E.ω i + ∑ j, ySup (E.Y j) p

/-- **(17.B.3)** (MWG, p. 582). The production inclusive excess demand function
`z̃(p) = ∑ᵢ xᵢ(p, p·ωᵢ + ∑ⱼ θᵢⱼ πⱼ(p)) - ∑ᵢ ωᵢ - ∑ⱼ yⱼ(p)`. -/
noncomputable def prodExcessDemand (E : ProdEconomy ι κ L) (p : Fin L → ℝ) : Fin L → ℝ :=
  wealthExcessDemand E.u E.wealth E.supplyTotal p

/-- The production economy as a private ownership economy of Chapter 16. -/
def ProdEconomy.toPriv (E : ProdEconomy ι κ L) : PrivPrefEconomy ι κ L where
  X := fun _ => nonnegOrthant L
  pref := fun i => utilityPref (E.u i)
  Y := E.Y
  ωi := E.ω
  θ := E.θ

/-- **Section 17.B** (MWG, p. 582). In a production economy with continuous, strictly convex,
strongly monotone consumers, `ωᵢ ∈ ℝ^L₊`, `θᵢⱼ ≥ 0`, and closed, strictly convex production
sets that are bounded above and contain `0`, `p` is a Walrasian equilibrium price vector iff
`z̃(p) = 0` (and `p ≫ 0`). -/
theorem prod_eqm_iff [Nonempty ι] {E : ProdEconomy ι κ L} (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) (hθ0 : ∀ i j, 0 ≤ E.θ i j)
    (hYc : ∀ j, IsClosed (E.Y j)) (hYs : ∀ j, StrictConvex ℝ (E.Y j))
    (hYb : ∀ j, ∃ b : Fin L → ℝ, ∀ y ∈ E.Y j, y ≤ b) (hY0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (p : Fin L → ℝ) :
    (∃ a, E.toPriv.IsWalrasEqm a p) ↔ IsEqmPrice (prodExcessDemand E) p := by
  have hw0 : ∀ i, p ∈ posOrthant L → 0 ≤ E.wealth i p := fun i hp => by
    have h1 : 0 ≤ p ⬝ᵥ E.ω i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
    have h2 : 0 ≤ ∑ j, E.θ i j * (p ⬝ᵥ ySup (E.Y j) p) := Finset.sum_nonneg fun j _ =>
      mul_nonneg (hθ0 i j) (by
        simpa using (ySup_mem (supply_nonempty (hYc j) (hYb j) (hY0 j) hp)).2 0 (hY0 j))
    exact add_nonneg h1 h2
  constructor
  · rintro ⟨a, hy, hx, hc⟩
    have hp : p ∈ posOrthant L := by
      intro l
      by_contra hl
      rw [not_lt] at hl
      let i : ι := Classical.arbitrary ι
      have hmem := hx i
      have hempty := walrasianDemand_eq_empty (hu i).2.2 hl (E.toPriv.wealth a p i)
      exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ hmem
    have hyj : ∀ j, a.y j = ySup (E.Y j) p := fun j =>
      supply_subsingleton (hYs j) hp (hy j) (ySup_mem (supply_nonempty (hYc j) (hYb j) (hY0 j) hp))
    have hwe : ∀ i, E.toPriv.wealth a p i = E.wealth i p := fun i => by
      simp [PrivPrefEconomy.wealth, ProdEconomy.wealth, ProdEconomy.toPriv, hyj]
    have hxi : ∀ i, a.x i = uDemand (E.u i) p (E.wealth i p) := fun i => by
      have hmem : a.x i ∈ walrasianDemand (E.u i) p (E.wealth i p) := by
        rw [← hwe i]
        exact hx i
      rw [walrasianDemand_eq_singleton (hu i).1 (hu i).2.1 hp (hw0 i hp)] at hmem
      exact hmem
    refine ⟨hp, ?_⟩
    simp only [prodExcessDemand, wealthExcessDemand, ProdEconomy.supplyTotal, ← hxi, ← hyj]
    simp only [ProdEconomy.toPriv] at hc
    rw [hc]
    abel
  · rintro ⟨hp, hz⟩
    refine ⟨⟨fun i => uDemand (E.u i) p (E.wealth i p), fun j => ySup (E.Y j) p⟩,
      fun j => ySup_mem (supply_nonempty (hYc j) (hYb j) (hY0 j) hp), fun i => ?_, ?_⟩
    · have hwe : E.toPriv.wealth ⟨fun i => uDemand (E.u i) p (E.wealth i p),
          fun j => ySup (E.Y j) p⟩ p i = E.wealth i p := by
        simp [PrivPrefEconomy.wealth, ProdEconomy.wealth, ProdEconomy.toPriv]
      rw [hwe]
      exact uDemand_mem (proposition_3_D_1 (hu i).1 hp (hw0 i hp))
    · simp only [prodExcessDemand, wealthExcessDemand, ProdEconomy.supplyTotal,
        sub_eq_zero] at hz
      simp only [ProdEconomy.toPriv]
      rw [hz]

/-! ### Exercise 17.B.4 -/

/-- **Exercise 17.B.4** (MWG, p. 642). In a production economy with closed, strictly convex
production sets that are bounded above (and contain `0`, see the correction `zeroMem_needed`),
continuous, strictly convex, strongly monotone consumers with `ωᵢ ∈ ℝ^L₊`, valid shares, and a
producible strictly positive aggregate consumption bundle `x̄ ∈ {∑ᵢ ωᵢ} + Y`, the production
inclusive excess demand function `z̃(p)` of (17.B.3) satisfies properties (i)-(v) of
Proposition 17.B.2. -/
theorem exercise_17_B_4 {E : ProdEconomy ι κ L} (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) (hθ0 : ∀ i j, 0 ≤ E.θ i j)
    (hθ1 : ∀ j, ∑ i, E.θ i j = 1) (hYc : ∀ j, IsClosed (E.Y j))
    (hYs : ∀ j, StrictConvex ℝ (E.Y j)) (hYb : ∀ j, ∃ b : Fin L → ℝ, ∀ y ∈ E.Y j, y ≤ b)
    (hY0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (hprod : ∃ xbar : Fin L → ℝ, (∀ l, 0 < xbar l) ∧ ∃ y : κ → Fin L → ℝ,
      (∀ j, y j ∈ E.Y j) ∧ xbar = ∑ i, E.ω i + ∑ j, y j) :
    IsStandardExcessDemand (prodExcessDemand E) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact isStandardExcessDemand_of_fin_zero _
  have hsupp : ∀ j, ∀ p ∈ posOrthant L, ySup (E.Y j) p ∈ supply (E.Y j) p := fun j p hp =>
    ySup_mem (supply_nonempty (hYc j) (hYb j) (hY0 j) hp)
  have hπ0 : ∀ j, ∀ p ∈ posOrthant L, 0 ≤ p ⬝ᵥ ySup (E.Y j) p := fun j p hp => by
    simpa using (hsupp j p hp).2 0 (hY0 j)
  have hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ E.wealth i p := fun i p hp =>
    add_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l))
      (Finset.sum_nonneg fun j _ => mul_nonneg (hθ0 i j) (hπ0 j p hp))
  have hsum : ∀ p ∈ posOrthant L, ∑ i, E.wealth i p = p ⬝ᵥ E.supplyTotal p := by
    intro p _
    simp only [ProdEconomy.wealth, ProdEconomy.supplyTotal, Finset.sum_add_distrib,
      dotProduct_add, dotProduct_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hθ1 j, one_mul]
  choose b hb using hYb
  obtain ⟨xbar, hxbar, yhat, hyhat, hxeq⟩ := hprod
  refine isStandard_wealthExcessDemand hL hu hw0 (fun i => ?_) ?_ (fun i p hp α hα => ?_)
    (fun p hp α hα => ?_) hsum ⟨∑ i, E.ω i + ∑ j, b j, fun p hp => ?_⟩ ?_
  · have h1 : ContinuousOn (fun p : Fin L → ℝ => p ⬝ᵥ E.ω i) (posOrthant L) := by
      simp only [dotProduct]
      fun_prop
    exact h1.add (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (continuousOn_profit (hYc j) (hYs j) ⟨b j, hb j⟩ (hY0 j)))
  · exact continuousOn_const.add (continuousOn_finsetSum _ fun j _ =>
      continuousOn_ySup (hYc j) (hYs j) ⟨b j, hb j⟩ (hY0 j))
  · simp only [ProdEconomy.wealth, ySup_smul _ _ hα, smul_dotProduct, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [ProdEconomy.supplyTotal, ySup_smul _ _ hα]
  · simp only [ProdEconomy.supplyTotal]
    exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => hb j _ (hsupp j p hp).1)
  · intro ps p hps hlim hp0
    set B : Fin L → ℝ := ∑ i, E.ω i + ∑ j, b j
    set R : ℝ := p ⬝ᵥ B + 1
    have hpB : Tendsto (fun n => ps n ⬝ᵥ B) atTop (𝓝 (p ⬝ᵥ B)) :=
      appendixA_tendsto_dotProduct_seq hlim tendsto_const_nhds
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hpB.eventually (gt_mem_nhds (by linarith : p ⬝ᵥ B < R)))
    have hsumle : ∀ n, ∑ i, E.wealth i (ps n) ≤ ps n ⬝ᵥ B := fun n => by
      rw [hsum _ (hps n)]
      simp only [dotProduct]
      refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hps n l).le
      simp only [ProdEconomy.supplyTotal, B, Pi.add_apply, Finset.sum_apply]
      exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => hb j _ (hsupp j _ (hps n)).1 l)
    have hbox : ∀ n, (fun i => E.wealth i (ps (n + N))) ∈ Set.Icc (0 : ι → ℝ) (fun _ => R) := by
      intro n
      refine ⟨fun i => hw0 i _ (hps _), fun i => ?_⟩
      have h1 := Finset.single_le_sum (fun i _ => hw0 i _ (hps (n + N))) (Finset.mem_univ i)
      have h2 := hsumle (n + N)
      have h3 := hN (n + N) (by omega)
      simp only at h1 ⊢
      linarith
    obtain ⟨w, -, ψ, hψ, hW⟩ := isCompact_Icc.tendsto_subseq hbox
    have hPψ : Tendsto (fun k => ps (ψ k + N)) atTop (𝓝 p) :=
      hlim.comp ((tendsto_add_atTop_nat N).comp hψ.tendsto_atTop)
    have hge : ∀ n, ps n ⬝ᵥ xbar ≤ ∑ i, E.wealth i (ps n) := fun n => by
      rw [hsum _ (hps n), hxeq]
      simp only [ProdEconomy.supplyTotal, dotProduct_add, dotProduct_sum]
      exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => (hsupp j _ (hps n)).2 _ (hyhat j))
    have hlimsum : Tendsto (fun k => ∑ i, E.wealth i (ps (ψ k + N))) atTop (𝓝 (∑ i, w i)) :=
      tendsto_finsetSum _ fun i _ => ((continuous_apply i).tendsto w).comp hW
    have hpos : 0 < ∑ i, w i :=
      lt_of_lt_of_le (dotProduct_pos_of_ne_zero (nonneg_of_tendsto_pos hps hlim) hp0 hxbar)
        (le_of_tendsto_of_tendsto (appendixA_tendsto_dotProduct_seq hPψ tendsto_const_nhds)
          hlimsum (Eventually.of_forall fun k => hge _))
    obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      exact absurd hpos (not_lt.2 (Finset.sum_nonpos fun i _ => h i))
    exact ⟨i, w i, hi, fun k => ψ k + N, fun a b hab => Nat.add_lt_add_right (hψ hab) N,
      ((continuous_apply i).tendsto w).comp hW⟩

/-- **Section 17.C** (MWG, p. 589). Proposition 17.C.1 applies to production economies: under
the hypotheses of Exercise 17.B.4 (with `0 ∈ Yⱼ` and at least one consumer) a Walrasian
equilibrium exists. -/
theorem production_existence [Nonempty ι] {E : ProdEconomy ι κ L}
    (hu : ∀ i, StandardUtility (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L)
    (hθ0 : ∀ i j, 0 ≤ E.θ i j) (hθ1 : ∀ j, ∑ i, E.θ i j = 1) (hYc : ∀ j, IsClosed (E.Y j))
    (hYs : ∀ j, StrictConvex ℝ (E.Y j)) (hYb : ∀ j, ∃ b : Fin L → ℝ, ∀ y ∈ E.Y j, y ≤ b)
    (hY0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (hprod : ∃ xbar : Fin L → ℝ, (∀ l, 0 < xbar l) ∧ ∃ y : κ → Fin L → ℝ,
      (∀ j, y j ∈ E.Y j) ∧ xbar = ∑ i, E.ω i + ∑ j, y j) :
    ∃ p a, E.toPriv.IsWalrasEqm a p := by
  obtain ⟨p, hp⟩ := proposition_17_C_1
    (exercise_17_B_4 hu hω hθ0 hθ1 hYc hYs hYb hY0 hprod)
  exact ⟨p, (prod_eqm_iff hu hω hθ0 hYc hYs hYb hY0 p).2 hp⟩

/-! ### Footnote 4: the excess demand correspondence -/

/-- **Footnote 4** (MWG, p. 583). The production inclusive excess demand correspondence:
`z̃(p) = {∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ}` over profit maximizing `yⱼ` and demanded `xᵢ` (at the
wealths these profits generate). -/
def prodExcessCorr (E : ProdEconomy ι κ L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {z | ∃ a : Allocation ι κ L, (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, a.x i ∈ walrasianDemand (E.u i) p (E.toPriv.wealth a p i)) ∧
    z = ∑ i, a.x i - ∑ i, E.ω i - ∑ j, a.y j}

/-- **Footnote 4** (MWG, p. 583). `p` is a Walrasian equilibrium price vector iff `0 ∈ z̃(p)`. -/
theorem footnote_17_4 (E : ProdEconomy ι κ L) (p : Fin L → ℝ) :
    (∃ a, E.toPriv.IsWalrasEqm a p) ↔ (0 : Fin L → ℝ) ∈ prodExcessCorr E p := by
  constructor
  · rintro ⟨a, hy, hx, hc⟩
    refine ⟨a, hy, hx, ?_⟩
    simp only [ProdEconomy.toPriv] at hc
    rw [hc]
    abel
  · rintro ⟨a, hy, hx, hz⟩
    refine ⟨a, hy, hx, ?_⟩
    simp only [ProdEconomy.toPriv]
    rw [sub_sub, eq_comm, sub_eq_zero] at hz
    exact hz

/-! ### A concrete instance: a disc technology -/

/-- The closed unit disc centred at `c` in `ℝ²`. -/
def discTech (c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {y | (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2 ≤ 1}

/-- The disc is closed. -/
theorem isClosed_discTech (c : Fin 2 → ℝ) : IsClosed (discTech c) :=
  isClosed_le (by fun_prop) continuous_const

/-- The disc is bounded above by `c + (1, 1)`. -/
theorem discTech_bdd (c : Fin 2 → ℝ) : ∀ y ∈ discTech c, y ≤ c + fun _ => 1 := by
  intro y hy l
  simp only [discTech, Set.mem_ofPred_eq] at hy
  simp only [Pi.add_apply]
  fin_cases l
  · simp only [Fin.zero_eta]
    nlinarith [sq_nonneg (y 1 - c 1), sq_nonneg (y 0 - c 0 - 1)]
  · simp only [Fin.mk_one]
    nlinarith [sq_nonneg (y 0 - c 0), sq_nonneg (y 1 - c 1 - 1)]

/-- The disc is strictly convex. -/
theorem strictConvex_discTech (c : Fin 2 → ℝ) : StrictConvex ℝ (discTech c) := by
  have hopen : IsOpen {y : Fin 2 → ℝ | (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsub : {y : Fin 2 → ℝ | (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2 < 1} ⊆ discTech c :=
    fun y hy => by
      simp only [discTech, Set.mem_ofPred_eq] at hy ⊢
      exact le_of_lt hy
  intro x hx y hy hxy a b ha hb hab
  apply interior_maximal hsub hopen
  simp only [discTech, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hd : 0 < (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    by_contra h
    push Not at h
    apply hxy
    funext l
    fin_cases l
    · simp only [Fin.zero_eta]
      nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
    · simp only [Fin.mk_one]
      nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : ∀ u v : ℝ, (a * u + (1 - a) * v) ^ 2 =
      a * u ^ 2 + (1 - a) * v ^ 2 - a * (1 - a) * (u - v) ^ 2 := fun u v => by ring
  have e0 : a * x 0 + (1 - a) * y 0 - c 0 = a * (x 0 - c 0) + (1 - a) * (y 0 - c 0) := by ring
  have e1 : a * x 1 + (1 - a) * y 1 - c 1 = a * (x 1 - c 1) + (1 - a) * (y 1 - c 1) := by ring
  rw [e0, e1, key, key]
  have h1 : (x 0 - c 0 - (y 0 - c 0)) ^ 2 + (x 1 - c 1 - (y 1 - c 1)) ^ 2 =
      (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by ring
  have hab' : 0 < a * (1 - a) := mul_pos ha hb
  nlinarith

/-- A one-consumer, one-firm production economy: `u = √x₁ + √x₂`, `ω = (1, 1)`, and the disc
technology centred at `(-1, 0)` (which contains `0`). -/
noncomputable def discEconomy : ProdEconomy (Fin 1) (Fin 1) 2 where
  u := fun _ => sqrtUtility 2
  ω := fun _ _ => 1
  Y := fun _ => discTech ![-1, 0]
  θ := fun _ _ => 1

/-- **Exercise 17.B.4**, instance: the production inclusive excess demand of `discEconomy`
satisfies (i)-(v). -/
theorem discEconomy_isStandard : IsStandardExcessDemand (prodExcessDemand discEconomy) :=
  exercise_17_B_4 (fun _ => standardUtility_sqrtUtility 2) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) (fun _ => by simp [discEconomy])
    (fun _ => isClosed_discTech _) (fun _ => strictConvex_discTech _)
    (fun _ => ⟨_, discTech_bdd _⟩) (fun _ => by simp [discEconomy, discTech])
    ⟨fun _ => 1, fun _ => one_pos, fun _ => 0, fun _ => by simp [discEconomy, discTech], by
      funext l
      simp [discEconomy]⟩

/-! ### Correction: `0 ∈ Yⱼ` is needed in Exercise 17.B.4 -/

/-- An economy satisfying every printed hypothesis of Exercise 17.B.4 (closed, strictly convex,
bounded above technology; standard consumers; `x̄ = (2, 2) ≫ 0` producible) in which no Walrasian
equilibrium exists: the disc technology centred at `(-1, -1)` (which does not contain `0`) is
owned by consumer 0, who has no endowment. -/
noncomputable def negProfitEconomy : ProdEconomy (Fin 2) (Fin 1) 2 where
  u := fun _ => sqrtUtility 2
  ω := ![0, fun _ => 3]
  Y := fun _ => discTech ![-1, -1]
  θ := ![fun _ => 1, fun _ => 0]

/-- Every production plan in `negProfitEconomy` makes a loss at every `p ≫ 0`. -/
theorem negProfitEconomy_loss {p : Fin 2 → ℝ} (hp : p ∈ posOrthant 2) {y : Fin 2 → ℝ}
    (hy : y ∈ discTech ![-1, -1]) : p ⬝ᵥ y < 0 := by
  simp only [discTech, Set.mem_ofPred_eq] at hy
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_neg_eq_add] at hy
  have h0 := hp 0
  have h1 := hp 1
  have hy0 : y 0 ≤ 0 := by nlinarith [sq_nonneg (y 1 + 1)]
  have hy1 : y 1 ≤ 0 := by nlinarith [sq_nonneg (y 0 + 1)]
  have hne : y 0 < 0 ∨ y 1 < 0 := by
    by_contra h
    push Not at h
    have e0 : y 0 = 0 := le_antisymm hy0 h.1
    have e1 : y 1 = 0 := le_antisymm hy1 h.2
    rw [e0, e1] at hy
    norm_num at hy
  simp only [dotProduct, Fin.sum_univ_two]
  rcases hne with h | h
  · nlinarith
  · nlinarith

/-- **Correction to Exercise 17.B.4** (MWG, p. 642). `negProfitEconomy` satisfies the printed
hypotheses (closed, strictly convex, bounded above technology; standard preferences;
`ωᵢ ∈ ℝ²₊`; valid shares; `x̄ = (2, 2) ≫ 0` producible), yet it has no Walrasian equilibrium at
all: at `p ≫ 0` consumer 0's wealth is a (negative) profit, and at any other `p` the strongly
monotone consumers have no demand. So `z̃(p)` is defined nowhere. -/
theorem zeroMem_needed :
    IsClosed (negProfitEconomy.Y 0) ∧ StrictConvex ℝ (negProfitEconomy.Y 0) ∧
      (∃ b : Fin 2 → ℝ, ∀ y ∈ negProfitEconomy.Y 0, y ≤ b) ∧
      (∀ i, StandardUtility (negProfitEconomy.u i)) ∧
      (∀ i, negProfitEconomy.ω i ∈ nonnegOrthant 2) ∧ (∀ i j, 0 ≤ negProfitEconomy.θ i j) ∧
      (∀ j, ∑ i, negProfitEconomy.θ i j = 1) ∧
      (∃ y : Fin 1 → Fin 2 → ℝ, (∀ j, y j ∈ negProfitEconomy.Y j) ∧
        (∀ l, 0 < (∑ i, negProfitEconomy.ω i + ∑ j, y j) l)) ∧
      (0 : Fin 2 → ℝ) ∉ negProfitEconomy.Y 0 ∧
      ∀ p a, ¬ negProfitEconomy.toPriv.IsWalrasEqm a p := by
  refine ⟨isClosed_discTech _, strictConvex_discTech _, ⟨_, discTech_bdd _⟩,
    fun _ => standardUtility_sqrtUtility 2, fun i l => ?_, fun i j => ?_, fun j => ?_,
    ⟨fun _ => ![-1, -1], fun _ => by simp [negProfitEconomy, discTech], fun l => ?_⟩,
    by simp [negProfitEconomy, discTech], ?_⟩
  · fin_cases i <;> simp [negProfitEconomy]
  · fin_cases i <;> simp [negProfitEconomy]
  · simp [negProfitEconomy, Fin.sum_univ_two]
  · fin_cases l <;> simp [negProfitEconomy, Fin.sum_univ_two]
  · rintro p a ⟨hy, hx, -⟩
    by_cases hp : p ∈ posOrthant 2
    · have hloss := negProfitEconomy_loss hp (hy 0).1
      obtain ⟨⟨hx0, hb⟩, -⟩ := hx 0
      have hw : negProfitEconomy.toPriv.wealth a p 0 = p ⬝ᵥ a.y 0 := by
        simp [PrivPrefEconomy.wealth, negProfitEconomy, ProdEconomy.toPriv]
      rw [hw] at hb
      have : 0 ≤ p ⬝ᵥ a.x 0 := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hx0 l)
      linarith
    · simp only [mem_posOrthant, not_forall, not_lt] at hp
      obtain ⟨l, hl⟩ := hp
      have hempty := walrasianDemand_eq_empty (sqrtUtility_stronglyMonotone 2) hl
        (negProfitEconomy.toPriv.wealth a p 1)
      exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ (hx 1)

end MWG.PositiveEquilibriumTheory
