import MWGWelfareTheorems.Replica
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import MWGWelfareTheorems.FirstOrderWelfare
import MWGWelfareBargaining.Shapley
import MWGProduction.AppendixMM
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The core of an economy: basic definitions (MWG Section 18.B, pp. 652-657)

The setting of Section 18.B (p. 653): consumers `i : ι`, `L` goods, consumption sets `ℝ^L₊`,
endowments `ωᵢ ≥ 0`, continuous, strictly convex, strongly monotone (rational) preferences
`≿ᵢ`, and a publicly available convex constant returns technology `Y ⊆ ℝ^L` (a convex cone,
`IsCRSTechnology`). The standing assumptions are bundled in `CoreEconomy.Standing`, with a
proved instance (`sqrtEconomy_standing`: utilities `∑ₗ √xₗ` and `Y = -ℝ^L₊`).

* Feasibility (p. 653): `∑ᵢ xᵢ = y + ∑ᵢ ωᵢ` for some `y ∈ Y`.
* **Definition 18.B.1**: a coalition `S` (nonempty) blocks `x*` if there are `xᵢ ≥ 0`, `i ∈ S`,
  with `xᵢ ≻ᵢ x*ᵢ` and `∑_{i∈S} xᵢ ∈ Y + {∑_{i∈S} ωᵢ}`.
* **Definition 18.B.2**: the core property and the core.
* Walrasian equilibrium for the constant returns economy: profit maximization on `Y` and
  preference maximization on the budget `{x ≥ 0 : p·x ≤ p·ωᵢ}` (profits are zero under constant
  returns, so the wealth is `p·ωᵢ`). `isWalrasEqm_iff_toPriv` bridges it to Chapter 16's
  Definition 16.B.3 for the private ownership economy with one firm and any valid shares.
* Replica economies (p. 656): types `h : H`, the `N`-replica with consumers `(h, n)`,
  equal-treatment allocations, type allocations and the sets `C_N` (p. 657).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

/-- **Section 18.B** (MWG, p. 653). An economy for the theory of the core: preference relations
`pref i x y` (read `x ≿ᵢ y`) on `ℝ^L₊`, endowments `ωᵢ` and the public technology `Y`. -/
structure CoreEconomy (ι : Type*) (L : ℕ) where
  /-- Preference relations `≿ᵢ`. -/
  pref : ι → (Fin L → ℝ) → (Fin L → ℝ) → Prop
  /-- Endowments `ωᵢ`. -/
  ω : ι → Fin L → ℝ
  /-- The publicly available technology `Y`. -/
  Y : Set (Fin L → ℝ)

variable {ι : Type*} {L : ℕ}

/-- **Section 18.B** (MWG, p. 653). A convex constant returns technology: `Y` is convex, contains
`0` and is closed under multiplication by nonnegative scalars. -/
def IsCRSTechnology (Y : Set (Fin L → ℝ)) : Prop :=
  Convex ℝ Y ∧ (0 : Fin L → ℝ) ∈ Y ∧ ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y

/-- **Section 18.B** (MWG, p. 653). The standing assumptions of Section 18.B: a convex constant
returns technology, `ωᵢ ≥ 0`, and rational, continuous, strictly convex, strongly monotone
preferences on `ℝ^L₊`. -/
def CoreEconomy.Standing (E : CoreEconomy ι L) : Prop :=
  IsCRSTechnology E.Y ∧ ∀ i, (∀ l, 0 ≤ E.ω i l) ∧ RationalOn (nonnegOrthant L) (E.pref i) ∧
    PrefContinuous (nonnegOrthant L) (E.pref i) ∧
    PrefStrictlyConvex (nonnegOrthant L) (E.pref i) ∧
    PrefStronglyMonotone (nonnegOrthant L) (E.pref i)

/-- **Section 18.B** (MWG, p. 653). A feasible allocation: `xᵢ ∈ ℝ^L₊` and
`∑ᵢ xᵢ = y + ∑ᵢ ωᵢ` for some `y ∈ Y`. -/
def CoreEconomy.IsFeasible [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  (∀ i, x i ∈ nonnegOrthant L) ∧ ∃ y ∈ E.Y, ∑ i, x i = y + ∑ i, E.ω i

/-- **Definition 18.B.1** (MWG, p. 653). The coalition `S` (a nonempty set of consumers) improves
upon, or blocks, `x*`: there are consumptions `xᵢ ≥ 0`, `i ∈ S`, with (i) `xᵢ ≻ᵢ x*ᵢ` for every
`i ∈ S` and (ii) `∑_{i∈S} xᵢ ∈ Y + {∑_{i∈S} ωᵢ}`. -/
def CoreEconomy.Blocks (E : CoreEconomy ι L) (S : Finset ι) (x : ι → Fin L → ℝ) : Prop :=
  S.Nonempty ∧ ∃ x' : ι → Fin L → ℝ,
    (∀ i ∈ S, x' i ∈ nonnegOrthant L ∧ Strict (E.pref i) (x' i) (x i)) ∧
    ∃ y ∈ E.Y, ∑ i ∈ S, x' i = y + ∑ i ∈ S, E.ω i

/-- **Definition 18.B.2** (MWG, p. 654). The feasible allocation `x*` has the core property: no
coalition can improve upon it. -/
def CoreEconomy.HasCoreProperty [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Prop :=
  E.IsFeasible x ∧ ∀ S : Finset ι, ¬ E.Blocks S x

/-- **Definition 18.B.2** (MWG, p. 654). The core: the allocations with the core property. -/
def CoreEconomy.core [Fintype ι] (E : CoreEconomy ι L) : Set (ι → Fin L → ℝ) :=
  {x | E.HasCoreProperty x}

/-- **Section 18.B** (MWG, pp. 654-655). `x` is a Walrasian equilibrium allocation with price
vector `p` of the constant returns economy: there is a profit-maximizing `y ∈ Y` with
`∑ᵢ xᵢ = y + ∑ᵢ ωᵢ`, and every `xᵢ` is maximal for `≿ᵢ` in the budget set
`{x ∈ ℝ^L₊ : p·x ≤ p·ωᵢ}` (Definition 16.B.3 with zero profits). -/
def CoreEconomy.IsWalrasEqm [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ)
    (p : Fin L → ℝ) : Prop :=
  (∃ y ∈ E.Y, ∑ i, x i = y + ∑ i, E.ω i ∧ ∀ y' ∈ E.Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y) ∧
    ∀ i, IsMaximalFor (E.pref i) (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ E.ω i)) (x i)

/-- A Walrasian equilibrium allocation: a Walrasian equilibrium for some price vector. -/
def CoreEconomy.IsWalrasAlloc [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∃ p, E.IsWalrasEqm x p

/-- **Definition 18.B.1** (MWG, p. 653), unfolded. -/
theorem definition_18_B_1 (E : CoreEconomy ι L) (S : Finset ι) (x : ι → Fin L → ℝ) :
    E.Blocks S x ↔ S.Nonempty ∧ ∃ x' : ι → Fin L → ℝ,
      (∀ i ∈ S, (∀ l, 0 ≤ x' i l) ∧ Strict (E.pref i) (x' i) (x i)) ∧
      ∃ y ∈ E.Y, ∑ i ∈ S, x' i = y + ∑ i ∈ S, E.ω i := Iff.rfl

/-- **Definition 18.B.2** (MWG, p. 654), unfolded. -/
theorem definition_18_B_2 [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    x ∈ E.core ↔ E.IsFeasible x ∧ ∀ S : Finset ι, ¬ E.Blocks S x := Iff.rfl

/-- Under constant returns, a profit-maximizing production plan makes zero profit. -/
theorem profit_eq_zero_of_max {Y : Set (Fin L → ℝ)} (hY : IsCRSTechnology Y) {p y : Fin L → ℝ}
    (hy : y ∈ Y) (hmax : ∀ y' ∈ Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y) : p ⬝ᵥ y = 0 := by
  have h0 := hmax 0 hY.2.1
  have h2 := hmax ((2 : ℝ) • y) (hY.2.2 y hy 2 (by norm_num))
  rw [dotProduct_zero] at h0
  rw [dotProduct_smul, smul_eq_mul] at h2
  linarith

/-- The private ownership economy of Chapter 16 with one firm owning the technology `Y` and
shares `θ`. -/
def CoreEconomy.toPriv (E : CoreEconomy ι L) (θ : ι → ℝ) : PrivPrefEconomy ι Unit L where
  X := fun _ => nonnegOrthant L
  pref := E.pref
  Y := fun _ => E.Y
  ωi := E.ω
  θ := fun i _ => θ i

/-- The Walrasian equilibrium of Section 18.B is Chapter 16's Definition 16.B.3 for the private
ownership economy with one constant returns firm, whatever the shares `θ`. -/
theorem isWalrasEqm_iff_toPriv [Fintype ι] (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y)
    (θ : ι → ℝ) (x : ι → Fin L → ℝ) (p : Fin L → ℝ) :
    E.IsWalrasEqm x p ↔ ∃ y ∈ E.Y, (E.toPriv θ).IsWalrasEqm ⟨x, fun _ => y⟩ p := by
  constructor
  · rintro ⟨⟨y, hy, hsum, hmax⟩, hx⟩
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨y, hy, fun _ => ⟨hy, hmax⟩, fun i => ?_, ?_⟩
    · simpa [PrivPrefEconomy.wealth, CoreEconomy.toPriv, h0] using hx i
    · simpa [CoreEconomy.toPriv, add_comm] using hsum
  · rintro ⟨y, hy, hsup, hx, hsum⟩
    have hmax : ∀ y' ∈ E.Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y := (hsup ()).2
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨⟨y, hy, by simpa [CoreEconomy.toPriv, add_comm] using hsum, hmax⟩, fun i => ?_⟩
    simpa [PrivPrefEconomy.wealth, CoreEconomy.toPriv, h0] using hx i

/-! ### Replica economies (p. 656) -/

/-- **Section 18.B** (MWG, p. 656). The `N`-replica of the economy of types `E`: `N` consumers
`(h, n)` of every type `h`, each with the preference and endowment of type `h`. -/
def CoreEconomy.replica {H : Type*} (E : CoreEconomy H L) (N : ℕ) :
    CoreEconomy (H × Fin N) L where
  pref := fun i => E.pref i.1
  ω := fun i => E.ω i.1
  Y := E.Y

/-- **Section 18.B** (MWG, p. 657). The equal-treatment allocation of the `N`-replica induced by
the type allocation `(x₁, ..., x_H)`: every consumer of type `h` gets `xₕ`. -/
def typeAlloc {H : Type*} (x : H → Fin L → ℝ) (N : ℕ) : H × Fin N → Fin L → ℝ :=
  fun i => x i.1

/-- **Section 18.B** (MWG, p. 656). The equal-treatment property: all consumers of the same type
get the same consumption bundle. -/
def EqualTreatment {H : Type*} {N : ℕ} (x : H × Fin N → Fin L → ℝ) : Prop :=
  ∀ h m n, x (h, m) = x (h, n)

/-- **Section 18.B** (MWG, p. 657). `C_N`: the feasible type allocations whose induced
equal-treatment allocation has the core property in the `N`-replica. (A type allocation is
feasible if `∑ₕ xₕ = y + ∑ₕ ωₕ` for some `y ∈ Y`, i.e. feasible in the economy of types.) -/
def CoreEconomy.CN {H : Type*} [Fintype H] (E : CoreEconomy H L) (N : ℕ) :
    Set (H → Fin L → ℝ) :=
  {x | E.IsFeasible x ∧ (E.replica N).HasCoreProperty (typeAlloc x N)}

/-- The induced equal-treatment allocation has the equal-treatment property. -/
theorem equalTreatment_typeAlloc {H : Type*} (x : H → Fin L → ℝ) (N : ℕ) :
    EqualTreatment (typeAlloc x N) := fun _ _ _ => rfl

/-! ### A concrete economy satisfying the standing assumptions -/

/-- The utility function `∑ₗ √xₗ`. -/
noncomputable def sqrtU (x : Fin L → ℝ) : ℝ := ∑ l, Real.sqrt (x l)

/-- The pure exchange economy (`Y = -ℝ^L₊`) of consumers with utility `∑ₗ √xₗ` and endowments
`ω`. -/
noncomputable def sqrtEconomy (ω : ι → Fin L → ℝ) : CoreEconomy ι L where
  pref := fun _ => utilityPref sqrtU
  ω := ω
  Y := nonposOrthant L

/-- The free disposal technology `-ℝ^L₊` is a convex constant returns technology. -/
theorem isCRSTechnology_nonposOrthant : IsCRSTechnology (nonposOrthant L) := by
  refine ⟨?_, fun l => le_refl _, fun y hy t ht l => ?_⟩
  · intro a ha b hb s r hs hr _ l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [ha l, hb l]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ht (hy l)

/-- `∑ₗ √xₗ` is continuous. -/
theorem continuous_sqrtU : Continuous (sqrtU (L := L)) :=
  continuous_finsetSum _ fun l _ => (continuous_apply l).sqrt

/-- `∑ₗ √xₗ` is strictly increasing on `ℝ^L₊` for the strong order. -/
theorem sqrtU_lt_of_le_of_ne {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y)
    (hne : y ≠ x) : sqrtU x < sqrtU y := by
  obtain ⟨m, hm⟩ : ∃ m, x m ≠ y m := by
    by_contra h
    push Not at h
    exact hne (funext fun l => (h l).symm)
  have hlt : x m < y m := lt_of_le_of_ne (hxy m) hm
  refine Finset.sum_lt_sum (fun l _ => Real.sqrt_le_sqrt (hxy l)) ⟨m, Finset.mem_univ m, ?_⟩
  exact Real.sqrt_lt_sqrt (hx m) hlt

/-- `∑ₗ √xₗ` is strictly concave on `ℝ^L₊`. -/
theorem sqrtU_strict_concave {y z : Fin L → ℝ} (hy : y ∈ nonnegOrthant L)
    (hz : z ∈ nonnegOrthant L) (hne : y ≠ z) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    α * sqrtU y + (1 - α) * sqrtU z < sqrtU (α • y + (1 - α) • z) := by
  obtain ⟨m, hm⟩ : ∃ m, y m ≠ z m := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hb : (0 : ℝ) < 1 - α := by linarith
  unfold sqrtU
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_lt_sum (fun l _ => ?_) ⟨m, Finset.mem_univ m, ?_⟩
  · have := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.mpr (hy l))
      (Set.mem_Ici.mpr (hz l)) h0.le hb.le (by ring)
    simpa [smul_eq_mul] using this
  · have := Real.strictConcaveOn_sqrt.2 (Set.mem_Ici.mpr (hy m)) (Set.mem_Ici.mpr (hz m)) hm
      h0 hb (by ring)
    simpa [smul_eq_mul] using this

/-- The economy `sqrtEconomy ω` with `ω ≥ 0` satisfies the standing assumptions of Section 18.B. -/
theorem sqrtEconomy_standing {ω : ι → Fin L → ℝ} (hω : ∀ i l, 0 ≤ ω i l) :
    (sqrtEconomy ω).Standing := by
  refine ⟨isCRSTechnology_nonposOrthant, fun i => ⟨hω i, rationalOn_utilityPref _ _,
    prefContinuous_utilityPref continuous_sqrtU.continuousOn, ?_, ?_⟩⟩
  · intro x _ y hy z hz hyx hzx hne α h0 h1
    have hc := sqrtU_strict_concave hy hz hne h0 h1
    have hlt : sqrtU x < sqrtU (α • y + (1 - α) • z) := by
      have hyx' : sqrtU x ≤ sqrtU y := hyx
      have hzx' : sqrtU x ≤ sqrtU z := hzx
      nlinarith
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩
  · intro x hx y _ hxy hne
    have hlt := sqrtU_lt_of_le_of_ne hx hxy hne
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Walrasian allocations are in the core (MWG Section 18.B, pp. 653-655; Exercise 18.B.1)

* **Proposition 18.B.1** (`proposition_18_B_1`): every Walrasian equilibrium allocation has the
  core property, for any convex constant returns technology `Y` (this is **Exercise 18.B.1**;
  only the cone property of `Y` and no assumption on preferences is used). The book's exchange
  case `Y = -ℝ^L₊` is `proposition_18_B_1_exchange`.
* Pareto optimality for the economy of Section 18.B (`CoreEconomy.IsParetoOptimal`), with the
  bridge `isParetoOptimal_iff_toPriv` to Chapter 16's Definition 16.B.2.
* **Footnote 2** (`footnote_18_2`): with continuity and strong monotonicity a Pareto dominated
  feasible allocation is dominated by a feasible allocation that is strictly better for every
  consumer (a small transfer of one good), via the general lemma `exists_strict_all_of_weak`.
* p. 654: core allocations are Pareto optimal (`core_isParetoOptimal`; without footnote 2 only
  weak Pareto optimality holds, `core_not_strictly_dominated`) and individually rational.
* **Figure 18.B.1** (`figure_18_B_1`): with two consumers the core is the set of Pareto optimal
  and individually rational allocations (the contract curve).
* p. 655, the converse of Proposition 18.B.1 is false (`converse_18_B_1_false`): with
  `u = √x₁ + √x₂`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)`, the allocation `x₁ = (1/3, 1/3)`,
  `x₂ = (2/3, 2/3)` is in the core but is not Walrasian for any price vector.
* **Figure 18.B.2** (`figure_18_B_2`): in the 2-replica of that economy the same equal-treatment
  allocation is blocked by the two consumers of the less favoured type 1 together with one
  consumer of type 2 (type 2 gets `(1, 9/20)`, each type 1 gets `(1/2, 11/40)`), so the type
  allocation lies in `C₁` but not in `C₂` (the book's figure has the roles of the types
  interchanged). The book's bracketed identity `-2(x'₂ - ω₂) = x'₁ - ω₁` is
  `figure_18_B_2_identity`; footnote 4 (Bertrand competition) is verbal.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {ι : Type*} {L : ℕ}

/-- **Proposition 18.B.1** (MWG, p. 654), in the generality of Exercise 18.B.1: with a constant
returns technology, every Walrasian equilibrium allocation has the core property. -/
theorem proposition_18_B_1 [Fintype ι] (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y)
    {x : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) : x ∈ E.core := by
  obtain ⟨⟨y, hy, hsum, hmax⟩, hx⟩ := h
  have hp0 := profit_eq_zero_of_max hY hy hmax
  refine ⟨⟨fun i => (hx i).1.1, y, hy, hsum⟩, fun S ⟨hS, x', hx', y', hy', hsum'⟩ => ?_⟩
  have hgt : ∀ i ∈ S, p ⬝ᵥ E.ω i < p ⬝ᵥ x' i := by
    intro i hi
    by_contra hle
    push Not at hle
    exact (hx' i hi).2.2 ((hx i).2 _ ⟨(hx' i hi).1, hle⟩)
  have hlt := Finset.sum_lt_sum_of_nonempty hS hgt
  rw [← dotProduct_sum, ← dotProduct_sum, hsum', dotProduct_add] at hlt
  have := hmax y' hy'
  linarith

/-- **Exercise 18.B.1** (MWG, p. 684). Walrasian allocations are in the core for the model with a
constant returns technology of Section 18.B. -/
theorem exercise_18_B_1 [Fintype ι] (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y)
    {x : ι → Fin L → ℝ} (h : E.IsWalrasAlloc x) : x ∈ E.core :=
  proposition_18_B_1 E hY h.choose_spec

/-- **Proposition 18.B.1** (MWG, pp. 654-655), the exchange case proved in the book:
`Y = -ℝ^L₊`. -/
theorem proposition_18_B_1_exchange [Fintype ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) {x : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    x ∈ E.core :=
  proposition_18_B_1 E (hY ▸ isCRSTechnology_nonposOrthant) h

/-! ### Pareto optimality and individual rationality -/

/-- **Section 18.B** (MWG, p. 654; Definition 16.B.2). `x'` Pareto dominates `x`. -/
def CoreEconomy.ParetoDominates (E : CoreEconomy ι L) (x' x : ι → Fin L → ℝ) : Prop :=
  (∀ i, E.pref i (x' i) (x i)) ∧ ∃ i, Strict (E.pref i) (x' i) (x i)

/-- **Section 18.B** (MWG, p. 654; Definition 16.B.2). A feasible allocation is Pareto optimal if
no feasible allocation Pareto dominates it. -/
def CoreEconomy.IsParetoOptimal [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Prop :=
  E.IsFeasible x ∧ ¬ ∃ x', E.IsFeasible x' ∧ E.ParetoDominates x' x

/-- **Section 18.B** (MWG, p. 654). `x` is individually rational: no consumer can do strictly
better on her own, i.e. `xᵢ ≿ᵢ z` for every `z ≥ 0` in `Y + {ωᵢ}` (no one-consumer coalition
blocks). -/
def CoreEconomy.IsIndividuallyRational (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∀ i, ∀ z ∈ nonnegOrthant L, (∃ y ∈ E.Y, z = y + E.ω i) → E.pref i (x i) z

/-- Pareto optimality of Section 18.B is Chapter 16's Definition 16.B.2 for the private ownership
economy with one constant returns firm (any shares). -/
theorem isParetoOptimal_iff_toPriv [Fintype ι] (E : CoreEconomy ι L) (θ : ι → ℝ)
    (x : ι → Fin L → ℝ) :
    E.IsParetoOptimal x ↔ ∃ y, (E.toPriv θ).toEconomy.IsParetoOptimal ⟨x, fun _ => y⟩ := by
  have hfeas : ∀ (x' : ι → Fin L → ℝ) (y : Fin L → ℝ),
      (E.toPriv θ).toEconomy.IsFeasible ⟨x', fun _ => y⟩ ↔
        (∀ i, x' i ∈ nonnegOrthant L) ∧ y ∈ E.Y ∧ ∑ i, x' i = y + ∑ i, E.ω i := by
    intro x' y
    simp only [PrefEconomy.IsFeasible, PrefEconomy.IsAllocation, PrivPrefEconomy.toEconomy,
      CoreEconomy.toPriv, Finset.univ_unique, Finset.sum_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2 (), by rw [h3, add_comm]⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, fun _ => h2⟩, by rw [h3, add_comm]⟩
  constructor
  · rintro ⟨⟨hx, y, hy, hsum⟩, hpo⟩
    refine ⟨y, (hfeas x y).2 ⟨hx, hy, hsum⟩, ?_⟩
    rintro ⟨a', ha', hdom⟩
    obtain ⟨h1, h2, h3⟩ := (hfeas a'.x (a'.y ())).1 (by
      obtain ⟨⟨hx1, hy1⟩, hs1⟩ := ha'
      refine ⟨⟨hx1, fun _ => hy1 ()⟩, ?_⟩
      simpa [PrivPrefEconomy.toEconomy] using hs1)
    exact hpo ⟨a'.x, ⟨h1, _, h2, h3⟩, hdom⟩
  · rintro ⟨y, hfe, hpo⟩
    obtain ⟨hx, hy, hsum⟩ := (hfeas x y).1 hfe
    refine ⟨⟨hx, y, hy, hsum⟩, ?_⟩
    rintro ⟨x', ⟨hx', y', hy', hsum'⟩, hdom⟩
    exact hpo ⟨⟨x', fun _ => y'⟩, (hfeas x' y').2 ⟨hx', hy', hsum'⟩, hdom⟩

/-- A transfer lemma (footnotes 2 and 5 of MWG, pp. 654 and 656): if within the group `S` every
`x'ᵢ` is weakly preferred to `zᵢ` and `x'ₖ` is strictly preferred to `zₖ`, then, with rational,
continuous and strongly monotone preferences on `ℝ^L₊`, there are `x''ᵢ ≥ 0` with the same total
over `S`, every one strictly preferred to `zᵢ`: consumer `k` gives away a small amount `δ` of a
good she holds, shared equally among the members of `S`. -/
theorem exists_strict_all_of_weak
    {pref : ι → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant L) (pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (pref i)) (S : Finset ι)
    {x' z : ι → Fin L → ℝ} (hx' : ∀ i ∈ S, x' i ∈ nonnegOrthant L)
    (hz : ∀ i ∈ S, z i ∈ nonnegOrthant L) (hweak : ∀ i ∈ S, pref i (x' i) (z i)) {k : ι}
    (hk : k ∈ S) (hstrict : Strict (pref k) (x' k) (z k)) :
    ∃ x'' : ι → Fin L → ℝ, (∀ i ∈ S, x'' i ∈ nonnegOrthant L ∧ Strict (pref i) (x'' i) (z i)) ∧
      ∑ i ∈ S, x'' i = ∑ i ∈ S, x' i := by
  classical
  -- consumer `k` holds some good in positive quantity
  obtain ⟨m, hm0⟩ : ∃ m, 0 < x' k m := by
    by_contra hall
    push Not at hall
    have hx0 : x' k = 0 := funext fun m => le_antisymm (hall m) (hx' k hk m)
    by_cases hzk : z k = x' k
    · rw [hzk] at hstrict
      exact hstrict.2 hstrict.1
    · have hle : x' k ≤ z k := fun l => by rw [hx0]; exact hz k hk l
      exact hstrict.2 (hm k (x' k) (hx' k hk) (z k) (hz k hk) hle hzk).1
  obtain ⟨δ, hδ, hmem, hs⟩ :=
    exists_strict_sub_single (hr k) (hc k) (hx' k hk) (hz k hk) hstrict hm0
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨k, hk⟩
  set base : ι → Fin L → ℝ := fun i => x' i - if i = k then Pi.single m δ else 0 with hbase
  set x'' : ι → Fin L → ℝ := fun i => base i + Pi.single m (δ / S.card) with hx''
  have hbaseX : ∀ i ∈ S, base i ∈ nonnegOrthant L := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simpa [hbase] using hmem
    · simpa [hbase, hik] using hx' i hi
  have hbaseR : ∀ i ∈ S, pref i (base i) (z i) := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simpa [hbase] using hs.1
    · simpa [hbase, hik] using hweak i hi
  have hδc : 0 < δ / S.card := div_pos hδ hcard
  refine ⟨x'', fun i hi => ?_, ?_⟩
  · have hle : base i ≤ x'' i := fun l => by
      simp only [hx'', Pi.add_apply, le_add_iff_nonneg_right]
      by_cases hl : l = m
      · subst hl; simp [hδc.le]
      · simp [hl]
    have hne : x'' i ≠ base i := by
      intro h
      have := congrFun h m
      simp only [hx'', Pi.add_apply, Pi.single_eq_same, add_eq_left] at this
      exact hδc.ne' this
    have hX : x'' i ∈ nonnegOrthant L := fun l => le_trans (hbaseX i hi l) (hle l)
    have hst := hm i (base i) (hbaseX i hi) (x'' i) hX hle hne
    refine ⟨hX, ?_⟩
    exact strict_of_strict_of_pref (hr i).2 hX (hbaseX i hi) (hz i hi) hst (hbaseR i hi)
  · simp only [hx'', hbase, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' S k, hk, ↓reduceIte, Finset.sum_const]
    have hns : S.card • (Pi.single m (δ / S.card) : Fin L → ℝ) = Pi.single m δ := by
      funext l
      rw [Pi.smul_apply, nsmul_eq_mul]
      by_cases hl : l = m
      · subst hl
        rw [Pi.single_eq_same, Pi.single_eq_same]
        field_simp
      · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, mul_zero]
    rw [hns]
    abel

/-- **Footnote 2** (MWG, p. 654). With continuity and strong monotonicity of preferences, if a
feasible allocation `x'` Pareto dominates `x`, then some feasible allocation is strictly better
than `x` for every consumer. -/
theorem footnote_18_2 [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {x x' : ι → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (hfe : E.IsFeasible x') (hdom : E.ParetoDominates x' x) :
    ∃ x'', E.IsFeasible x'' ∧ ∀ i, Strict (E.pref i) (x'' i) (x i) := by
  classical
  obtain ⟨k, hk⟩ := hdom.2
  obtain ⟨x'', hx'', hsum⟩ := exists_strict_all_of_weak hr hc hm Finset.univ
    (fun i _ => hfe.1 i) (fun i _ => hx i) (fun i _ => hdom.1 i) (Finset.mem_univ k) hk
  obtain ⟨y, hy, hs⟩ := hfe.2
  exact ⟨x'', ⟨fun i => (hx'' i (Finset.mem_univ i)).1, y, hy, by rw [hsum, hs]⟩,
    fun i => (hx'' i (Finset.mem_univ i)).2⟩

/-- **Section 18.B** (MWG, p. 654). A core allocation is weakly Pareto optimal: the coalition of
the whole cannot make everyone strictly better off. -/
theorem core_not_strictly_dominated [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    {x : ι → Fin L → ℝ} (hx : x ∈ E.core) :
    ¬ ∃ x', E.IsFeasible x' ∧ ∀ i, Strict (E.pref i) (x' i) (x i) := by
  rintro ⟨x', ⟨hx', y, hy, hsum⟩, hs⟩
  exact hx.2 Finset.univ ⟨Finset.univ_nonempty, x', fun i _ => ⟨hx' i, hs i⟩, y, hy, hsum⟩

/-- **Section 18.B** (MWG, p. 654). All allocations in the core are Pareto optimal (with
footnote 2: continuous, strongly monotone preferences). -/
theorem core_isParetoOptimal [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : x ∈ E.core) : E.IsParetoOptimal x := by
  refine ⟨hx.1, ?_⟩
  rintro ⟨x', hfe, hdom⟩
  have : Nonempty ι := ⟨hdom.2.choose⟩
  obtain ⟨x'', hfe'', hs⟩ := footnote_18_2 E hr hc hm hx.1.1 hfe hdom
  exact core_not_strictly_dominated E hx ⟨x'', hfe'', hs⟩

/-- **Section 18.B** (MWG, p. 654). A core allocation is individually rational (no one-consumer
coalition blocks it; completeness of preferences is used). -/
theorem core_isIndividuallyRational [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : x ∈ E.core) : E.IsIndividuallyRational x := by
  classical
  intro i z hz ⟨y, hy, hzy⟩
  rcases (hr i).1 (x i) (hx.1.1 i) z hz with h | h
  · exact h
  · by_contra hn
    refine hx.2 {i} ⟨Finset.singleton_nonempty i, fun _ => z, ?_, y, hy, ?_⟩
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨hz, h, hn⟩
    · simp [hzy]

/-- In a pure exchange economy with rational, strongly monotone preferences and `ωᵢ ≥ 0`,
individual rationality is `xᵢ ≿ᵢ ωᵢ` for every `i`. -/
theorem isIndividuallyRational_iff_exchange (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {x : ι → Fin L → ℝ} (hx : ∀ i, x i ∈ nonnegOrthant L) :
    E.IsIndividuallyRational x ↔ ∀ i, E.pref i (x i) (E.ω i) := by
  constructor
  · intro h i
    exact h i (E.ω i) (hω i) ⟨0, hY ▸ fun _ => le_rfl, (zero_add _).symm⟩
  · intro h i z hz ⟨y, hy, hzy⟩
    rw [hY] at hy
    have hle : z ≤ E.ω i := fun l => by rw [hzy]; simp only [Pi.add_apply]; linarith [hy l]
    by_cases hzω : E.ω i = z
    · rw [← hzω]; exact h i
    · exact (hr i).2 _ (hx i) _ (hω i) _ hz (h i) (hm i z hz (E.ω i) (hω i) hle hzω).1

/-- **Figure 18.B.1** (MWG, p. 654). With two consumers (continuous, strongly monotone
preferences) the core consists exactly of the Pareto optimal and individually rational
allocations: the only coalitions are `{1}`, `{2}` and `{1, 2}`. -/
theorem figure_18_B_1 [Fintype ι] (hcard : Fintype.card ι = 2) (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (x : ι → Fin L → ℝ) :
    x ∈ E.core ↔ E.IsParetoOptimal x ∧ E.IsIndividuallyRational x := by
  classical
  refine ⟨fun h => ⟨core_isParetoOptimal E hr hc hm h, core_isIndividuallyRational E hr h⟩, ?_⟩
  rintro ⟨hpo, hir⟩
  refine ⟨hpo.1, fun S ⟨hS, x', hx', y, hy, hsum⟩ => ?_⟩
  have hle : S.card ≤ 2 := hcard ▸ Finset.card_le_univ S
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  rcases (show S.card = 1 ∨ S.card = 2 by omega) with h1 | h2
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have hi := hx' i (Finset.mem_singleton_self i)
    exact hi.2.2 (hir i (x' i) hi.1 ⟨y, hy, by simpa using hsum⟩)
  · have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [h2, hcard])
    subst hSu
    obtain ⟨k, -⟩ := hS
    exact hpo.2 ⟨x', ⟨fun i => (hx' i (Finset.mem_univ i)).1, y, hy, hsum⟩,
      fun i => (hx' i (Finset.mem_univ i)).2.1, k, (hx' k (Finset.mem_univ k)).2⟩

/-! ### The converse of Proposition 18.B.1 is false (p. 655) -/

/-- `√x₁ + √x₂` for two goods. -/
theorem sqrtU_two (x : Fin 2 → ℝ) : sqrtU x = Real.sqrt (x 0) + Real.sqrt (x 1) := by
  simp [sqrtU, Fin.sum_univ_two]

/-- `√a + √b` at the bundle `(a, b)`. -/
theorem sqrtU_vec (a b : ℝ) : sqrtU ![a, b] = Real.sqrt a + Real.sqrt b := by
  rw [sqrtU_two]
  rfl

/-- The tangent-line bound for `√`: `2c√a ≤ a + c²` for `a ≥ 0`. -/
theorem two_mul_sqrt_le (a c : ℝ) (ha : 0 ≤ a) : 2 * c * Real.sqrt a ≤ a + c ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - c), Real.sq_sqrt ha]

/-- In a pure exchange economy with utilities `√x₁ + √x₂`, an allocation on the diagonals,
`xᵢ = (tᵢ, tᵢ)` with `tᵢ > 0` and `∑ᵢ tᵢ` equal to the total endowment of each good, is Pareto
optimal (the tangent-line bound gives `x'ᵢ₁ + x'ᵢ₂ ≥ 2tᵢ` for any `x'ᵢ ≿ xᵢ`). -/
theorem sqrtEconomy_diag_isParetoOptimal [Fintype ι] {ω : ι → Fin 2 → ℝ} {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (h0 : ∑ i, ω i 0 = ∑ i, t i) (h1 : ∑ i, ω i 1 = ∑ i, t i) :
    (sqrtEconomy ω).IsParetoOptimal (fun i => ![t i, t i]) := by
  have hfe : (sqrtEconomy ω).IsFeasible (fun i => ![t i, t i]) := by
    refine ⟨fun i l => ?_, 0, fun _ => le_rfl, ?_⟩
    · fin_cases l <;> simp [(ht i).le]
    · funext l
      fin_cases l <;> simp [Finset.sum_apply, sqrtEconomy, h0, h1]
  refine ⟨hfe, ?_⟩
  rintro ⟨x', ⟨hx', y, hy, hsum⟩, hweak, k, hk⟩
  -- each consumer needs at least `2tᵢ` units in total, consumer `k` more
  have hbound : ∀ i, 2 * t i ≤ x' i 0 + x' i 1 := by
    intro i
    have hw : 2 * Real.sqrt (t i) ≤ sqrtU (x' i) := by
      have := hweak i
      change sqrtU ![t i, t i] ≤ sqrtU (x' i) at this
      rw [sqrtU_vec] at this
      linarith
    rw [sqrtU_two] at hw
    have a0 := two_mul_sqrt_le (x' i 0) (Real.sqrt (t i)) (hx' i 0)
    have a1 := two_mul_sqrt_le (x' i 1) (Real.sqrt (t i)) (hx' i 1)
    have hs := Real.sq_sqrt (ht i).le
    have hsp := Real.sqrt_pos.mpr (ht i)
    nlinarith
  have hstrict : 2 * t k < x' k 0 + x' k 1 := by
    have hw : 2 * Real.sqrt (t k) < sqrtU (x' k) := by
      have := hk.2
      change ¬ sqrtU (x' k) ≤ sqrtU ![t k, t k] at this
      rw [sqrtU_vec] at this
      linarith
    rw [sqrtU_two] at hw
    have a0 := two_mul_sqrt_le (x' k 0) (Real.sqrt (t k)) (hx' k 0)
    have a1 := two_mul_sqrt_le (x' k 1) (Real.sqrt (t k)) (hx' k 1)
    have hs := Real.sq_sqrt (ht k).le
    have hsp := Real.sqrt_pos.mpr (ht k)
    nlinarith
  have hlt : ∑ i, 2 * t i < ∑ i, (x' i 0 + x' i 1) :=
    Finset.sum_lt_sum (fun i _ => hbound i) ⟨k, Finset.mem_univ k, hstrict⟩
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply] at e0 e1
  have hy0 := hy 0
  have hy1 := hy 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hlt
  simp only [sqrtEconomy] at e0 e1
  linarith

/-- The endowments `ω₁ = (1, 0)`, `ω₂ = (0, 1)` of the example of p. 655. -/
def exampleEndow : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- The diagonal shares `t = (1/3, 2/3)`. -/
noncomputable def exampleShare : Fin 2 → ℝ := ![1 / 3, 2 / 3]

/-- The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)`. -/
noncomputable def exampleAlloc : Fin 2 → Fin 2 → ℝ := fun i => ![exampleShare i, exampleShare i]

/-- `2√(1/3) < 6/5`. -/
theorem two_sqrt_third_lt : 2 * Real.sqrt (1 / 3) < 6 / 5 := by
  have : Real.sqrt (1 / 3) < 3 / 5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- `2√(2/3) < 41/25`. -/
theorem two_sqrt_two_thirds_lt : 2 * Real.sqrt (2 / 3) < 41 / 25 := by
  have : Real.sqrt (2 / 3) < 41 / 50 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Individual rationality in the example of p. 655: `uₕ(ωₕ) = 1 ≤ uₕ(xₕ)`. -/
theorem exampleAlloc_ir (a : Fin 2) : sqrtU (exampleEndow a) ≤ sqrtU (exampleAlloc a) := by
  fin_cases a
  · change sqrtU ![1, 0] ≤ sqrtU ![1 / 3, 1 / 3]
    rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one, Real.sqrt_zero]
    have : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 3) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  · change sqrtU ![0, 1] ≤ sqrtU ![2 / 3, 2 / 3]
    rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one, Real.sqrt_zero]
    have : (1 : ℝ) / 2 ≤ Real.sqrt (2 / 3) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith

/-- **Section 18.B** (MWG, p. 655). The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` of the
economy with `u = √x₁ + √x₂`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)` is in the core. -/
theorem exampleAlloc_mem_core : exampleAlloc ∈ (sqrtEconomy exampleEndow).core := by
  have hst := sqrtEconomy_standing (ω := exampleEndow) (L := 2)
    (fun i l => by fin_cases i <;> fin_cases l <;> norm_num [exampleEndow])
  have hr := fun i => (hst.2 i).2.1
  have hc := fun i => (hst.2 i).2.2.1
  have hm := fun i => (hst.2 i).2.2.2.2
  have hx : ∀ i, exampleAlloc i ∈ nonnegOrthant 2 := fun i l => by
    fin_cases i <;> fin_cases l <;> norm_num [exampleAlloc, exampleShare]
  refine (figure_18_B_1 (by simp) _ hr hc hm _).2 ⟨?_, ?_⟩
  · exact sqrtEconomy_diag_isParetoOptimal (t := exampleShare)
      (fun i => by fin_cases i <;> norm_num [exampleShare])
      (by simp [exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
      (by simp [exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
  · refine (isIndividuallyRational_iff_exchange _ rfl hr hm (fun i l => (hst.2 i).1 l) hx).2 ?_
    intro i
    exact exampleAlloc_ir i

/-- **Section 18.B** (MWG, p. 655). The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` is not a
Walrasian equilibrium allocation for any price vector `p`: affordability of both bundles forces
`p₂ = 2p₁`; if `p₁ ≤ 0` the bundle `(1, 1)` is affordable for consumer 1, and if `p₁ > 0` the
bundle `(1/2, 1/4)` is, both better than `(1/3, 1/3)`. -/
theorem exampleAlloc_not_walras : ¬ (sqrtEconomy exampleEndow).IsWalrasAlloc exampleAlloc := by
  rintro ⟨p, -, hx⟩
  have b0 := (hx 0).1.2
  have b1 := (hx 1).1.2
  change p ⬝ᵥ ![1 / 3, 1 / 3] ≤ p ⬝ᵥ ![1, 0] at b0
  change p ⬝ᵥ ![2 / 3, 2 / 3] ≤ p ⬝ᵥ ![0, 1] at b1
  simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at b0 b1
  have hu : sqrtU (exampleAlloc 0) < 6 / 5 := by
    change sqrtU ![1 / 3, 1 / 3] < 6 / 5
    rw [sqrtU_vec]
    linarith [two_sqrt_third_lt]
  rcases le_or_gt (p 0) 0 with hp | hp
  · have hb : (![1, 1] : Fin 2 → ℝ) ∈
        budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy exampleEndow).ω 0) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      change p ⬝ᵥ ![1, 1] ≤ p ⬝ᵥ ![1, 0]
      simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have := (hx 0).2 _ hb
    change sqrtU ![1, 1] ≤ sqrtU (exampleAlloc 0) at this
    rw [sqrtU_vec, Real.sqrt_one] at this
    linarith
  · have hb : (![1 / 2, 1 / 4] : Fin 2 → ℝ) ∈
        budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy exampleEndow).ω 0) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      change p ⬝ᵥ ![1 / 2, 1 / 4] ≤ p ⬝ᵥ ![1, 0]
      simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have := (hx 0).2 _ hb
    change sqrtU ![1 / 2, 1 / 4] ≤ sqrtU (exampleAlloc 0) at this
    rw [sqrtU_vec] at this
    have h1 : (7 : ℝ) / 10 < Real.sqrt (1 / 2) := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h2 : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 4) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith

/-- **Section 18.B** (MWG, p. 655). The converse of Proposition 18.B.1 is false: a core allocation
need not be Walrasian. -/
theorem converse_18_B_1_false :
    exampleAlloc ∈ (sqrtEconomy exampleEndow).core ∧
      ¬ (sqrtEconomy exampleEndow).IsWalrasAlloc exampleAlloc :=
  ⟨exampleAlloc_mem_core, exampleAlloc_not_walras⟩

/-! ### Figure 18.B.2: blocking in the 2-replica -/

/-- The blocking coalition of the 2-replica: both consumers of type 1 and one of type 2. -/
def fig18B2Coalition : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0)}

/-- The blocking consumptions: `(1/2, 11/40)` for type 1 and `(1, 9/20)` for type 2. -/
noncomputable def fig18B2Bundle : Fin 2 × Fin 2 → Fin 2 → ℝ :=
  fun i => ![![1 / 2, 11 / 40], ![1, 9 / 20]] i.1

/-- **Figure 18.B.2** (MWG, p. 655). In the 2-replica of the economy of p. 655 (two consumers of
each type), the equal-treatment allocation induced by `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` is
blocked by the two consumers of type 1 together with one consumer of type 2: the former get
`(1/2, 11/40)` each, the latter `(1, 9/20)`. So the type allocation is in `C₁` but not in
`C₂`. (The book's figure has the roles of the types interchanged.) -/
theorem figure_18_B_2 :
    ((sqrtEconomy exampleEndow).replica 2).Blocks fig18B2Coalition (typeAlloc exampleAlloc 2) ∧
      exampleAlloc ∈ (sqrtEconomy exampleEndow).CN 1 ∧
      exampleAlloc ∉ (sqrtEconomy exampleEndow).CN 2 := by
  have hblock : ((sqrtEconomy exampleEndow).replica 2).Blocks fig18B2Coalition
      (typeAlloc exampleAlloc 2) := by
    refine ⟨⟨(0, 0), by simp [fig18B2Coalition]⟩, fig18B2Bundle, fun i hi => ?_, 0,
      fun _ => le_rfl, ?_⟩
    · have h1 : (7 : ℝ) / 10 < Real.sqrt (1 / 2) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h2 : (13 : ℝ) / 25 < Real.sqrt (11 / 40) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h3 : (67 : ℝ) / 100 < Real.sqrt (9 / 20) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h4 := two_sqrt_third_lt
      have h5 := two_sqrt_two_thirds_lt
      simp only [fig18B2Coalition, Finset.mem_insert, Finset.mem_singleton] at hi
      have k1 : sqrtU ![1 / 3, 1 / 3] < sqrtU ![1 / 2, 11 / 40] := by
        rw [sqrtU_vec, sqrtU_vec]; linarith
      have k2 : sqrtU ![2 / 3, 2 / 3] < sqrtU ![1, 9 / 20] := by
        rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]; linarith
      rcases hi with rfl | rfl | rfl
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![1 / 3, 1 / 3] ≤ sqrtU ![1 / 2, 11 / 40] ∧
          ¬ sqrtU ![1 / 2, 11 / 40] ≤ sqrtU ![1 / 3, 1 / 3]
        exact ⟨k1.le, not_le.mpr k1⟩
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![1 / 3, 1 / 3] ≤ sqrtU ![1 / 2, 11 / 40] ∧
          ¬ sqrtU ![1 / 2, 11 / 40] ≤ sqrtU ![1 / 3, 1 / 3]
        exact ⟨k1.le, not_le.mpr k1⟩
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![2 / 3, 2 / 3] ≤ sqrtU ![1, 9 / 20] ∧
          ¬ sqrtU ![1, 9 / 20] ≤ sqrtU ![2 / 3, 2 / 3]
        exact ⟨k2.le, not_le.mpr k2⟩
    · funext l
      fin_cases l <;>
        simp [fig18B2Coalition, fig18B2Bundle, CoreEconomy.replica, sqrtEconomy,
          exampleEndow] <;> norm_num
  refine ⟨hblock, ⟨exampleAlloc_mem_core.1, ?_⟩, fun h => h.2.2 _ hblock⟩
  -- `C₁`: the replica with one consumer of each type is a two-consumer economy
  have hst := sqrtEconomy_standing (ω := fun i : Fin 2 × Fin 1 => exampleEndow i.1) (L := 2)
    (fun i l => by fin_cases l <;> fin_cases i <;> norm_num [exampleEndow])
  have hr := fun i => (hst.2 i).2.1
  have hc := fun i => (hst.2 i).2.2.1
  have hm := fun i => (hst.2 i).2.2.2.2
  have hx : ∀ i, typeAlloc exampleAlloc 1 i ∈ nonnegOrthant 2 := fun i l => by
    obtain ⟨a, b⟩ := i
    fin_cases a <;> fin_cases l <;> norm_num [typeAlloc, exampleAlloc, exampleShare]
  refine (figure_18_B_1 (by simp) _ hr hc hm _).2 ⟨?_, ?_⟩
  · exact sqrtEconomy_diag_isParetoOptimal (ι := Fin 2 × Fin 1)
      (ω := fun i => exampleEndow i.1) (t := fun i => exampleShare i.1)
      (fun i => by obtain ⟨a, b⟩ := i; fin_cases a <;> norm_num [exampleShare])
      (by simp [Fintype.sum_prod_type, exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
      (by simp [Fintype.sum_prod_type, exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
  · refine (isIndividuallyRational_iff_exchange _ rfl hr hm (fun i l => (hst.2 i).1 l) hx).2 ?_
    intro i
    exact exampleAlloc_ir i.1

/-- **Figure 18.B.2** (MWG, p. 655), the bracketed identity: for a coalition of one consumer of
type 1 (consuming `x'₁`) and two of type 2 (each consuming `x'₂`) in a pure exchange economy, the
coalition's consumptions exactly exhaust its endowments iff `-2(x'₂ - ω₂) = x'₁ - ω₁`. -/
theorem figure_18_B_2_identity (x₁ x₂ ω₁ ω₂ : Fin L → ℝ) :
    x₁ + (2 : ℝ) • x₂ = ω₁ + (2 : ℝ) • ω₂ ↔ -(2 : ℝ) • (x₂ - ω₂) = x₁ - ω₁ := by
  constructor
  · intro h
    linear_combination (norm := module) (-1 : ℝ) • h
  · intro h
    linear_combination (norm := module) (-1 : ℝ) • h

/-- **Figure 18.B.2** (MWG, p. 655): the blocking consumptions of `figure_18_B_2` satisfy the
identity, with the roles of the types interchanged: `-2(x'₁ - ω₁) = x'₂ - ω₂`. -/
theorem figure_18_B_2_identity_instance :
    -(2 : ℝ) • (fig18B2Bundle (0, 0) - exampleEndow 0) = fig18B2Bundle (1, 0) - exampleEndow 1 := by
  funext l
  fin_cases l <;> simp [fig18B2Bundle, exampleEndow] <;> norm_num

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equal treatment in replica economies (MWG Section 18.B, pp. 655-657, 685)

* **Proposition 18.B.2** (`proposition_18_B_2`): under the standing assumptions every core
  allocation of the `N`-replica has the equal-treatment property. The proof is the book's: the
  worst-treated member of each type (`exists_worst`), the type averages, strict convexity
  (18.B.1) (`avg_pref`, `avg_strict`), **footnote 5** (`footnote_18_5`, continuity and strong
  monotonicity turn "weakly better for all, strictly for one" into blocking) and the constant
  returns fact `(1/N) y ∈ Y`.
* p. 657: the equal-treatment allocation of a feasible type allocation is feasible in every
  replica (`replica_isFeasible_typeAlloc`); `C_{N+1} ⊆ C_N` (`CN_succ_subset`); a type
  allocation is Walrasian in the economy of types iff it is Walrasian in the `N`-replica, `N ≥ 1`
  (`isWalrasEqm_typeAlloc_iff`), so the set of Walrasian type allocations does not depend on `N`
  (`walrasTypeAllocs_eq`) and lies in every `C_N` (`walras_mem_CN`); the core allocations of the
  `N`-replica are the equal-treatment allocations of `C_N` (`core_replica_eq_typeAlloc`).
* **Exercise 18.B.3** (`exercise_18_B_3`): directly, consumers with the same (rational, strictly
  convex) preferences and endowments get the same bundle in a Walrasian equilibrium; continuity is
  not needed. Hence Walrasian allocations of replicas have equal treatment.
* **Exercise 18.B.2**: (i) `exercise_18_B_2a`: a three-consumer exchange economy (`u = 2√x + m`,
  consumers 1 and 2 identical with endowment `(0, 2)`, consumer 3 with `(3, 2)`; preferences
  continuous, strictly convex and strongly monotone, `ex18B2Economy_standing`) whose core
  contains the allocation `(1, 1), (1, 1/2), (1, 9/2)`, which does not have equal treatment. No
  coalition blocks it by the transferable-utility bound `2√a ≤ a/c + c` (`ex18B2_tu_bound`).
  (ii) `exercise_18_B_2b`: no example with two consumers exists: if the two consumers have the
  same preferences and endowments, every core allocation gives them the same bundle.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {L : ℕ}

/-! ### Convexity facts -/

/-- With strictly convex preferences on `ℝ^L₊` the upper contour set `{y ≥ 0 : y ≿ x}` is
convex. -/
theorem convex_upper_of_strictlyConvex {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) : Convex ℝ {y | y ∈ nonnegOrthant L ∧ r y x} := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_nonnegOrthant L hy.1 hz.1 ha hb hab, ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · by_cases hyz : y = z
      · subst hyz
        rw [← add_smul, hab, one_smul]
        exact hy.2
      · have hb1 : b = 1 - a := by linarith
        subst hb1
        exact (hsc x hx y hy.1 z hz.1 hy.2 hz.2 hyz a ha' (by linarith)).1
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hy.2
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hz.2

/-- A worst element: for a rational preference, finitely many bundles have a worst one. -/
theorem exists_worst {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (s : Finset κ) (hs : s.Nonempty)
    (f : κ → Fin L → ℝ) (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L) :
    ∃ k ∈ s, ∀ j ∈ s, r (f j) (f k) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨a, Finset.mem_singleton_self a, fun j hj => ?_⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    have ha := hf j (Finset.mem_singleton_self j)
    exact (hr.1 _ ha _ ha).elim id id
  | cons a s ha hs ih =>
    have hf' : ∀ k ∈ s, f k ∈ nonnegOrthant L := fun k hk => hf k (Finset.mem_cons_of_mem hk)
    obtain ⟨k, hk, hkw⟩ := ih hf'
    have hfa := hf a (Finset.mem_cons_self a s)
    have hfk := hf' k hk
    rcases hr.1 (f k) hfk (f a) hfa with h | h
    · refine ⟨a, Finset.mem_cons_self a s, fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact (hr.1 _ hfa _ hfa).elim id id
      · exact hr.2 _ (hf' j hj) _ hfk _ hfa (hkw j hj) h
    · refine ⟨k, Finset.mem_cons_of_mem hk, fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact h
      · exact hkw j hj

/-- The average of finitely many bundles each weakly preferred to `w` is weakly preferred to `w`
(strictly convex, hence convex, preferences). -/
theorem avg_pref {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {w : Fin L → ℝ}
    (hw : w ∈ nonnegOrthant L) (s : Finset κ) (hs : s.Nonempty) (f : κ → Fin L → ℝ)
    (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L ∧ r (f k) w) :
    (s.card : ℝ)⁻¹ • ∑ k ∈ s, f k ∈ nonnegOrthant L ∧
      r ((s.card : ℝ)⁻¹ • ∑ k ∈ s, f k) w := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have := (convex_upper_of_strictlyConvex hsc hw).sum_mem (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (z := f) (fun _ _ => inv_nonneg.mpr hc.le) (by
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']) hf
  rwa [← Finset.smul_sum] at this

/-- **Section 18.B** (MWG, p. 656, (18.B.1)). If finitely many bundles are weakly preferred to `w`
and two of them differ, their average is strictly preferred to `w` (strict convexity). -/
theorem avg_strict {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {w : Fin L → ℝ}
    (hw : w ∈ nonnegOrthant L) (s : Finset κ) (f : κ → Fin L → ℝ)
    (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L ∧ r (f k) w) {a b : κ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : f a ≠ f b) : Strict r ((s.card : ℝ)⁻¹ • ∑ k ∈ s, f k) w := by
  classical
  set c := (s.card : ℝ)⁻¹ • ∑ k ∈ s, f k with hcdef
  -- a member different from the average
  obtain ⟨k₀, hk₀, hne⟩ : ∃ k₀ ∈ s, f k₀ ≠ c := by
    by_contra hall
    push Not at hall
    exact hab ((hall a ha).trans (hall b hb).symm)
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  set s' := s.erase k₀ with hs'
  have hs'ne : s'.Nonempty := by
    by_cases hk : k₀ = a
    · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab' (hk.symm.trans h.symm), hb⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨fun h => hk h.symm, ha⟩⟩
  have hm : (0 : ℝ) < s'.card := by exact_mod_cast hs'ne.card_pos
  have hcard : (s.card : ℝ) = s'.card + 1 := by
    have := Finset.card_erase_add_one hk₀
    rw [hs']
    exact_mod_cast this.symm
  set d := (s'.card : ℝ)⁻¹ • ∑ k ∈ s', f k with hd
  obtain ⟨hdX, hdR⟩ := avg_pref hsc hw s' hs'ne f fun k hk => hf k (Finset.mem_of_mem_erase hk)
  have hcd : c = (s.card : ℝ)⁻¹ • f k₀ + (1 - (s.card : ℝ)⁻¹) • d := by
    rw [hcdef, hd, ← Finset.add_sum_erase s f hk₀, smul_add, smul_smul, ← hs']
    congr 2
    rw [hcard]
    field_simp
    ring
  have hfd : f k₀ ≠ d := by
    intro h
    apply hne
    rw [hcd, ← h, ← add_smul, add_sub_cancel, one_smul]
  have hn2 : (1 : ℝ) < s.card := by rw [hcard]; linarith
  rw [hcd]
  exact hsc w hw (f k₀) (hf k₀ hk₀).1 d hdX (hf k₀ hk₀).2 hdR hfd _ (by positivity)
    (inv_lt_one_of_one_lt₀ hn2)

/-! ### Proposition 18.B.2 -/

/-- **Footnote 5** (MWG, p. 656). With continuous and strongly monotone preferences, if the
coalition `S` can achieve consumptions that make all its members at least as well off as under
`x` and one of them strictly better off, then `S` blocks `x`. -/
theorem footnote_18_5 {ι : Type*} (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {S : Finset ι}
    {x x' : ι → Fin L → ℝ} (hx : ∀ i ∈ S, x i ∈ nonnegOrthant L)
    (hx' : ∀ i ∈ S, x' i ∈ nonnegOrthant L) (hweak : ∀ i ∈ S, E.pref i (x' i) (x i)) {k : ι}
    (hk : k ∈ S) (hstrict : Strict (E.pref k) (x' k) (x k))
    (hfeas : ∃ y ∈ E.Y, ∑ i ∈ S, x' i = y + ∑ i ∈ S, E.ω i) : E.Blocks S x := by
  classical
  obtain ⟨x'', hx'', hsum⟩ := exists_strict_all_of_weak hr hc hm S hx' hx hweak hk hstrict
  obtain ⟨y, hy, hs⟩ := hfeas
  exact ⟨⟨k, hk⟩, x'', hx'', y, hy, by rw [hsum, hs]⟩

/-- **Proposition 18.B.2** (MWG, p. 656). Under the standing assumptions of Section 18.B, every
allocation in the core of the `N`-replica economy has the equal-treatment property. -/
theorem proposition_18_B_2 {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    {N : ℕ} {x : H × Fin N → Fin L → ℝ} (hx : x ∈ (E.replica N).core) : EqualTreatment x := by
  classical
  intro h₀ m n
  by_contra hne
  obtain ⟨⟨hxX, y, hy, hsum⟩, hcore⟩ := hx
  have hr := fun h => (hst.2 h).2.1
  have hc := fun h => (hst.2 h).2.2.1
  have hsc := fun h => (hst.2 h).2.2.2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fin.pos m)
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty := ⟨m, Finset.mem_univ m⟩
  have hcardN : ((Finset.univ : Finset (Fin N)).card : ℝ) = N := by simp
  -- the worst-treated member of every type
  have hworst : ∀ h, ∃ k : Fin N, ∀ j, E.pref h (x (h, j)) (x (h, k)) := by
    intro h
    obtain ⟨k, -, hk⟩ :=
      exists_worst (hr h) Finset.univ huniv (fun j => x (h, j)) fun j _ => hxX (h, j)
    exact ⟨k, fun j => hk j (Finset.mem_univ j)⟩
  choose w hw using hworst
  -- the averages
  set xhat : H → Fin L → ℝ := fun h => (N : ℝ)⁻¹ • ∑ j, x (h, j) with hxhat
  have hweak : ∀ h, xhat h ∈ nonnegOrthant L ∧ E.pref h (xhat h) (x (h, w h)) := by
    intro h
    have := avg_pref (hsc h) (hxX (h, w h)) Finset.univ huniv (fun j => x (h, j))
      fun j _ => ⟨hxX (h, j), hw h j⟩
    rwa [hcardN] at this
  have hstrict : Strict (E.pref h₀) (xhat h₀) (x (h₀, w h₀)) := by
    have := avg_strict (hsc h₀) (hxX (h₀, w h₀)) Finset.univ (fun j => x (h₀, j))
      (fun j _ => ⟨hxX (h₀, j), hw h₀ j⟩) (Finset.mem_univ m)
      (Finset.mem_univ n) hne
    rwa [hcardN] at this
  -- the coalition of the worst-treated members
  set e : H ↪ H × Fin N := ⟨fun h => (h, w h), fun a b hab => (Prod.ext_iff.mp hab).1⟩ with he
  set S : Finset (H × Fin N) := Finset.univ.map e with hS
  apply hcore S
  have hmem : ∀ h, (h, w h) ∈ S := fun h => Finset.mem_map_of_mem e (Finset.mem_univ h)
  have hS' : ∀ i ∈ S, i = (i.1, w i.1) := by
    intro i hi
    obtain ⟨h, -, rfl⟩ := Finset.mem_map.mp hi
    rfl
  refine footnote_18_5 (E.replica N) (fun i => hr i.1) (fun i => hc i.1) (fun i => hm i.1)
    (x' := fun i => xhat i.1) (fun i _ => hxX i) (fun i _ => (hweak i.1).1) ?_ (hmem h₀)
    hstrict ?_
  · intro i hi
    rw [hS' i hi]
    exact (hweak i.1).2
  · refine ⟨(N : ℝ)⁻¹ • y, hst.1.2.2 y hy _ (inv_nonneg.mpr hN.le), ?_⟩
    simp only [hS, Finset.sum_map, he]
    change ∑ h, xhat h = (N : ℝ)⁻¹ • y + ∑ h, E.ω h
    have htot : ∑ h, ∑ j, x (h, j) = y + ∑ h, (N : ℝ) • E.ω h := by
      rw [← Fintype.sum_prod_type', hsum]
      congr 1
      rw [Fintype.sum_prod_type]
      simp only [CoreEconomy.replica, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_smul_eq_nsmul]
    simp only [hxhat]
    rw [← Finset.smul_sum, htot, smul_add, ← Finset.smul_sum, smul_smul,
      inv_mul_cancel₀ hN.ne', one_smul]

/-! ### Type allocations (p. 657) -/

/-- **Section 18.B** (MWG, p. 657). If the type allocation `x` is feasible (`∑ₕ xₕ = y + ∑ₕ ωₕ`),
the induced equal-treatment allocation is feasible in every replica:
`∑ₕ N xₕ = N y + N ∑ₕ ωₕ` with `N y ∈ Y` by constant returns. -/
theorem replica_isFeasible_typeAlloc {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {x : H → Fin L → ℝ} (hx : E.IsFeasible x) (N : ℕ) :
    (E.replica N).IsFeasible (typeAlloc x N) := by
  obtain ⟨hxX, y, hy, hsum⟩ := hx
  refine ⟨fun i => hxX i.1, (N : ℝ) • y, hY.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  simp only [typeAlloc, CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, ← Finset.smul_sum, hsum, smul_add, Nat.cast_smul_eq_nsmul]

/-- **Section 18.B** (MWG, p. 657). By Proposition 18.B.2 the core allocations of the `N`-replica
(`N ≥ 1`) are the equal-treatment allocations of the type allocations in `C_N`. -/
theorem core_replica_eq_typeAlloc {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    {N : ℕ} (hN : 1 ≤ N) {x : H × Fin N → Fin L → ℝ} (hx : x ∈ (E.replica N).core) :
    ∃ xbar ∈ E.CN N, x = typeAlloc xbar N := by
  have het := proposition_18_B_2 E hst hx
  set xbar : H → Fin L → ℝ := fun h => x (h, ⟨0, hN⟩) with hxbar
  have hxe : x = typeAlloc xbar N := funext fun i => het i.1 i.2 ⟨0, hN⟩
  refine ⟨xbar, ⟨⟨fun h => hx.1.1 (h, ⟨0, hN⟩), ?_⟩, hxe ▸ hx⟩, hxe⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, y, hy, hsum⟩ := hx.1
  have hsumT : ∑ i : H × Fin N, x i = (N : ℝ) • ∑ h, xbar h := by
    rw [hxe]
    simp only [typeAlloc, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  have hsumω : ∑ i : H × Fin N, (E.replica N).ω i = (N : ℝ) • ∑ h, E.ω h := by
    simp only [CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  refine ⟨(N : ℝ)⁻¹ • y, hst.1.2.2 y hy _ (inv_nonneg.mpr hN'.le), ?_⟩
  rw [hsumT, hsumω] at hsum
  have := congrArg (fun v => (N : ℝ)⁻¹ • v) hsum
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hN'.ne', one_smul] at this
  exact this

/-- **Section 18.B** (MWG, p. 657). `C_{N+1} ⊆ C_N`: a type allocation blocked in the `N`-replica
is blocked in the `(N+1)`-replica by a coalition of the same composition. -/
theorem CN_succ_subset {H : Type*} [Fintype H] (E : CoreEconomy H L) (hY : IsCRSTechnology E.Y)
    (N : ℕ) : E.CN (N + 1) ⊆ E.CN N := by
  classical
  rintro x ⟨hx, -, hcore⟩
  refine ⟨hx, replica_isFeasible_typeAlloc E hY hx N, ?_⟩
  rintro S ⟨hS, x', hx', y, hy, hsum⟩
  set e : H × Fin N ↪ H × Fin (N + 1) :=
    ⟨fun i => (i.1, i.2.castSucc), fun a b hab => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hab
      exact Prod.ext h1 (Fin.castSucc_injective N h2)⟩ with he
  set x'' : H × Fin (N + 1) → Fin L → ℝ :=
    fun i => if hi : (i.2 : ℕ) < N then x' (i.1, ⟨i.2, hi⟩) else 0 with hx''
  have hx''e : ∀ j, x'' (e j) = x' j := by
    intro j
    change (if hi : ((j.2.castSucc : Fin (N + 1)) : ℕ) < N then
      x' (j.1, ⟨(j.2.castSucc : ℕ), hi⟩) else 0) = x' j
    simp
  apply hcore (S.map e)
  refine ⟨hS.map, x'', fun i hi => ?_, y, hy, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    rw [hx''e]
    exact hx' j hj
  · rw [Finset.sum_map, Finset.sum_map]
    simp only [hx''e]
    exact hsum

/-- **Section 18.B** (MWG, p. 657; Exercise 18.B.3). For `N ≥ 1`, the type allocation `x` with
prices `p` is a Walrasian equilibrium of the economy of types iff the induced equal-treatment
allocation is a Walrasian equilibrium of the `N`-replica with the same prices. -/
theorem isWalrasEqm_typeAlloc_iff {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {N : ℕ} (hN : 1 ≤ N) (x : H → Fin L → ℝ) (p : Fin L → ℝ) :
    E.IsWalrasEqm x p ↔ (E.replica N).IsWalrasEqm (typeAlloc x N) p := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsumT : ∑ i : H × Fin N, typeAlloc x N i = (N : ℝ) • ∑ h, x h := by
    simp only [typeAlloc, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  have hsumω : ∑ i : H × Fin N, (E.replica N).ω i = (N : ℝ) • ∑ h, E.ω h := by
    simp only [CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  constructor
  · rintro ⟨⟨y, hy, hsum, hmax⟩, hx⟩
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨⟨(N : ℝ) • y, hY.2.2 y hy _ hN'.le, ?_, fun y' hy' => ?_⟩, fun i => hx i.1⟩
    · rw [hsumT, hsumω, hsum, smul_add]
    · rw [dotProduct_smul, smul_eq_mul, h0, mul_zero]
      exact (hmax y' hy').trans h0.le
  · rintro ⟨⟨y, hy, hsum, hmax⟩, hx⟩
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨⟨(N : ℝ)⁻¹ • y, hY.2.2 y hy _ (inv_nonneg.mpr hN'.le), ?_, fun y' hy' => ?_⟩,
      fun h => hx (h, ⟨0, hN⟩)⟩
    · rw [hsumT, hsumω] at hsum
      have := congrArg (fun v => (N : ℝ)⁻¹ • v) hsum
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hN'.ne', one_smul] at this
      exact this
    · rw [dotProduct_smul, smul_eq_mul, h0, mul_zero]
      exact (hmax y' hy').trans h0.le

/-- **Section 18.B** (MWG, p. 657; Exercise 18.B.3). The set of Walrasian type allocations does
not depend on `N ≥ 1`: it is the set of Walrasian allocations of the economy of types. -/
theorem walrasTypeAllocs_eq {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {N : ℕ} (hN : 1 ≤ N) :
    {x | (E.replica N).IsWalrasAlloc (typeAlloc x N)} = {x | E.IsWalrasAlloc x} := by
  ext x
  exact ⟨fun ⟨p, hp⟩ => ⟨p, (isWalrasEqm_typeAlloc_iff E hY hN x p).2 hp⟩,
    fun ⟨p, hp⟩ => ⟨p, (isWalrasEqm_typeAlloc_iff E hY hN x p).1 hp⟩⟩

/-- **Section 18.B** (MWG, p. 657). Walrasian type allocations belong to `C_N` for every `N`
(Proposition 18.B.1 in each replica). -/
theorem walras_mem_CN {H : Type*} [Fintype H] (E : CoreEconomy H L) (hY : IsCRSTechnology E.Y)
    {x : H → Fin L → ℝ} (hx : E.IsWalrasAlloc x) (N : ℕ) : x ∈ E.CN N := by
  obtain ⟨p, hp⟩ := hx
  have hfe : E.IsFeasible x := (proposition_18_B_1 E hY hp).1
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨hfe, replica_isFeasible_typeAlloc E hY hfe 0, fun S hS => ?_⟩
    obtain ⟨i, -⟩ := hS.1
    exact i.2.elim0
  · exact ⟨hfe, proposition_18_B_1 (E.replica N) hY
      ((isWalrasEqm_typeAlloc_iff E hY hN x p).1 hp)⟩

/-! ### Exercise 18.B.3 -/

/-- **Exercise 18.B.3** (MWG, p. 685). Directly (without core arguments): in a Walrasian
equilibrium, two consumers with the same rational, strictly convex preferences on `ℝ^L₊` and the
same endowments get the same bundle (if they differed, the midpoint would be affordable and
strictly preferred). Continuity is not needed. -/
theorem exercise_18_B_3 {ι : Type*} [Fintype ι] (E : CoreEconomy ι L) {x : ι → Fin L → ℝ}
    {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) {i j : ι}
    (hr : RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) (hpref : E.pref i = E.pref j)
    (hω : E.ω i = E.ω j) : x i = x j := by
  by_contra hne
  have hi := h.2 i
  have hj := h.2 j
  rw [← hpref, ← hω] at hj
  have hmid : (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • x j ∈
      budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ E.ω i) := by
    refine ⟨convex_nonnegOrthant L hi.1.1 hj.1.1 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [hi.1.2, hj.1.2]
  have hrefl : E.pref i (x i) (x i) := (hr.1 _ hi.1.1 _ hi.1.1).elim id id
  have hs := hsc (x i) hi.1.1 (x i) hi.1.1 (x j) hj.1.1 hrefl (hj.2 (x i) hi.1) hne (1 / 2)
    (by norm_num) (by norm_num)
  exact hs.2 (hi.2 _ hmid)

/-- **Exercise 18.B.3** (MWG, p. 685). Walrasian allocations of a replica economy (rational,
strictly convex preferences) have the equal-treatment property. -/
theorem replica_walras_equalTreatment {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hr : ∀ h, RationalOn (nonnegOrthant L) (E.pref h))
    (hsc : ∀ h, PrefStrictlyConvex (nonnegOrthant L) (E.pref h)) {N : ℕ}
    {x : H × Fin N → Fin L → ℝ} (hx : (E.replica N).IsWalrasAlloc x) : EqualTreatment x := by
  obtain ⟨p, hp⟩ := hx
  intro h m n
  exact exercise_18_B_3 (E.replica N) hp (hr h) (hsc h) rfl rfl

/-! ### Exercise 18.B.2 -/

/-- The quasilinear utility `u(x, m) = 2√x + m` of Exercise 18.B.2. -/
noncomputable def ex18B2U (x : Fin 2 → ℝ) : ℝ := 2 * Real.sqrt (x 0) + x 1

/-- `u(a, b) = 2√a + b`. -/
theorem ex18B2U_vec (a b : ℝ) : ex18B2U ![a, b] = 2 * Real.sqrt a + b := rfl

/-- The economy of Exercise 18.B.2: three consumers with `u = 2√x + m` on `ℝ²₊`, endowments
`(0, 2)`, `(0, 2)`, `(3, 2)`, pure exchange. -/
noncomputable def ex18B2Economy : CoreEconomy (Fin 3) 2 where
  pref := fun _ => utilityPref ex18B2U
  ω := ![![0, 2], ![0, 2], ![3, 2]]
  Y := nonposOrthant 2

/-- The allocation `(1, 1)`, `(1, 1/2)`, `(1, 9/2)`. -/
noncomputable def ex18B2Alloc : Fin 3 → Fin 2 → ℝ := ![![1, 1], ![1, 1 / 2], ![1, 9 / 2]]

/-- `u = 2√x + m` is strictly increasing on `ℝ²₊` for the strong order. -/
theorem ex18B2U_lt_of_le_of_ne {x y : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hxy : x ≤ y)
    (hne : y ≠ x) : ex18B2U x < ex18B2U y := by
  unfold ex18B2U
  have h0 := Real.sqrt_le_sqrt (hxy 0)
  rcases (hxy 0).lt_or_eq with h | h
  · have := Real.sqrt_lt_sqrt (hx 0) h
    linarith [hxy 1]
  · have h1 : x 1 < y 1 := by
      refine lt_of_le_of_ne (hxy 1) fun h1 => hne (funext fun l => ?_)
      fin_cases l
      · exact h.symm
      · exact h1.symm
    rw [h]
    linarith

/-- The economy of Exercise 18.B.2 satisfies the standing assumptions of Section 18.B:
preferences are rational, continuous, strictly convex and strongly monotone. -/
theorem ex18B2Economy_standing : ex18B2Economy.Standing := by
  refine ⟨isCRSTechnology_nonposOrthant, fun i => ⟨fun l => ?_, rationalOn_utilityPref _ _,
    prefContinuous_utilityPref (by unfold ex18B2U; fun_prop), ?_, ?_⟩⟩
  · fin_cases i <;> fin_cases l <;> norm_num [ex18B2Economy]
  · intro x _ y hy z hz hyx hzx hne α h0 h1
    change ex18B2U x ≤ ex18B2U y at hyx
    change ex18B2U x ≤ ex18B2U z at hzx
    have hb : (0 : ℝ) < 1 - α := by linarith
    have hlt : ex18B2U x < ex18B2U (α • y + (1 - α) • z) := by
      unfold ex18B2U at hyx hzx ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h00 : y 0 = z 0
      · have h11 : y 1 ≠ z 1 := fun h11 => hne (funext fun l => by
          fin_cases l
          · exact h00
          · exact h11)
        rw [← h00, ← add_mul, add_sub_cancel, one_mul]
        rw [← h00] at hzx
        rcases lt_or_gt_of_ne h11 with h | h
        · nlinarith [mul_pos hb (sub_pos.mpr h)]
        · nlinarith [mul_pos h0 (sub_pos.mpr h)]
      · have hc := Real.strictConcaveOn_sqrt.2 (Set.mem_Ici.mpr (hy 0)) (Set.mem_Ici.mpr (hz 0))
          h00 h0 hb (by ring)
        simp only [smul_eq_mul] at hc
        nlinarith
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩
  · intro x hx y _ hxy hne
    have hlt := ex18B2U_lt_of_le_of_ne hx hxy hne
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩

/-- **Exercise 18.B.2** (MWG, p. 685), the transferable-utility bound: if the coalition `S` blocks
`x` in the economy of Exercise 18.B.2, then for every `c > 0`,
`∑_{i∈S} uᵢ(xᵢ) < ∑_{i∈S} (ωᵢ₁/c + c + ωᵢ₂)` (from `2√a ≤ a/c + c` and free disposal). -/
theorem ex18B2_tu_bound {S : Finset (Fin 3)} {x : Fin 3 → Fin 2 → ℝ}
    (hb : ex18B2Economy.Blocks S x) {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ S, ex18B2U (x i) <
      ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) := by
  obtain ⟨hS, x', hx', y, hy, hsum⟩ := hb
  have hlt : ∑ i ∈ S, ex18B2U (x i) < ∑ i ∈ S, ex18B2U (x' i) :=
    Finset.sum_lt_sum_of_nonempty hS fun i hi => lt_of_not_ge (hx' i hi).2.2
  have hle : ∀ i ∈ S, ex18B2U (x' i) ≤ x' i 0 / c + c + x' i 1 := by
    intro i hi
    have h := two_mul_sqrt_le (x' i 0) c ((hx' i hi).1 0)
    unfold ex18B2U
    have : 2 * Real.sqrt (x' i 0) ≤ x' i 0 / c + c := by
      rw [div_add' _ _ _ hc.ne', le_div_iff₀ hc]
      nlinarith
    linarith
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply] at e0 e1
  have hy0 : y 0 ≤ 0 := hy 0
  have hy1 : y 1 ≤ 0 := hy 1
  have h2 : ∑ i ∈ S, (x' i 0 / c + c + x' i 1) ≤
      ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    rw [e0, e1]
    have : (y 0 + ∑ i ∈ S, ex18B2Economy.ω i 0) / c ≤ (∑ i ∈ S, ex18B2Economy.ω i 0) / c :=
      div_le_div_of_nonneg_right (by linarith) hc.le
    linarith
  linarith [Finset.sum_le_sum hle]

/-- The utilities of the allocation of Exercise 18.B.2: `3`, `5/2`, `13/2`. -/
theorem ex18B2_util (i : Fin 3) : ex18B2U (ex18B2Alloc i) = ![3, 5 / 2, 13 / 2] i := by
  fin_cases i
  · change ex18B2U ![1, 1] = 3
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num
  · change ex18B2U ![1, 1 / 2] = 5 / 2
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num
  · change ex18B2U ![1, 9 / 2] = 13 / 2
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num

/-- **Exercise 18.B.2(i)** (MWG, p. 685). In the three-consumer exchange economy
`ex18B2Economy` (continuous, strictly convex, strongly monotone preferences), the allocation
`(1, 1)`, `(1, 1/2)`, `(1, 9/2)` is in the core, but consumers 1 and 2, who have the same
preferences and endowments, get different bundles: the core need not have the equal-treatment
property outside replica economies. -/
theorem exercise_18_B_2a :
    ex18B2Economy.Standing ∧ ex18B2Alloc ∈ ex18B2Economy.core ∧
      ex18B2Economy.pref 0 = ex18B2Economy.pref 1 ∧ ex18B2Economy.ω 0 = ex18B2Economy.ω 1 ∧
      ex18B2Alloc 0 ≠ ex18B2Alloc 1 := by
  classical
  refine ⟨ex18B2Economy_standing, ⟨⟨fun i l => ?_, 0, fun _ => le_rfl, ?_⟩, fun S hb => ?_⟩,
    rfl, rfl, fun h => ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num [ex18B2Alloc]
  · funext l
    fin_cases l <;> simp [ex18B2Alloc, ex18B2Economy, Fin.sum_univ_three] <;> norm_num
  · -- for every coalition, a tangent point `c` for which the bound fails
    have key : ∃ c : ℝ, 0 < c ∧ ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) ≤
        ∑ i ∈ S, ex18B2U (ex18B2Alloc i) := by
      simp only [ex18B2_util]
      simp only [← Finset.sum_ite_mem_eq S, Fin.sum_univ_three]
      by_cases h2 : (2 : Fin 3) ∈ S
      · by_cases h0 : (0 : Fin 3) ∈ S
        · by_cases h1 : (1 : Fin 3) ∈ S
          · exact ⟨1, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
          · exact ⟨5 / 4, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
        · by_cases h1 : (1 : Fin 3) ∈ S
          · exact ⟨5 / 4, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
          · exact ⟨2, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
      · refine ⟨1 / 2, by norm_num, ?_⟩
        by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
          simp [h0, h1, h2, ex18B2Economy] <;> norm_num
    obtain ⟨c, hc, hle⟩ := key
    exact absurd (ex18B2_tu_bound hb hc) (not_lt.mpr hle)
  · have := congrFun h 1
    norm_num [ex18B2Alloc] at this

/-- **Exercise 18.B.2(ii)** (MWG, p. 685). No such example exists with only two consumers: in a
two-consumer economy with a constant returns technology, if the consumers have the same rational,
strictly convex preferences and the same endowments, every core allocation gives them the same
bundle (otherwise the less well-off consumer alone could produce the average bundle
`(xᵢ + xⱼ)/2 = y/2 + ω`). -/
theorem exercise_18_B_2b {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 2)
    (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y) {i j : ι} (hij : i ≠ j)
    (hr : RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) (hpref : E.pref i = E.pref j)
    (hω : E.ω i = E.ω j) {x : ι → Fin L → ℝ} (hx : x ∈ E.core) : x i = x j := by
  classical
  by_contra hne
  obtain ⟨⟨hxX, y, hy, hsum⟩, hcore⟩ := hx
  have huniv : (Finset.univ : Finset ι) = {i, j} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hij, hcard]
  rw [huniv, Finset.sum_pair hij, Finset.sum_pair hij, ← hω] at hsum
  set a : Fin L → ℝ := (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • x j with ha
  have haX : a ∈ nonnegOrthant L :=
    convex_nonnegOrthant L (hxX i) (hxX j) (by norm_num) (by norm_num) (by norm_num)
  have hay : a = (1 / 2 : ℝ) • y + E.ω i := by
    rw [ha, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← smul_add, hsum, smul_add, ← two_smul ℝ,
      smul_smul]
    norm_num
  have hrefl : ∀ k, E.pref i (x k) (x k) := fun k => (hr.1 _ (hxX k) _ (hxX k)).elim id id
  -- the consumer who is (weakly) worse off blocks on her own
  have hblock : ∀ k, E.ω k = E.ω i → E.pref k = E.pref i → Strict (E.pref i) a (x k) →
      E.Blocks {k} x := by
    intro k hωk hpk hs
    refine ⟨Finset.singleton_nonempty k, fun _ => a, fun l hl => ?_,
      (1 / 2 : ℝ) • y, hY.2.2 y hy _ (by norm_num), ?_⟩
    · rw [Finset.mem_singleton] at hl
      subst hl
      rw [hpk]
      exact ⟨haX, hs⟩
    · rw [Finset.sum_singleton, Finset.sum_singleton, hωk, hay]
  rcases hr.1 (x i) (hxX i) (x j) (hxX j) with h | h
  · have hs := hsc (x j) (hxX j) (x i) (hxX i) (x j) (hxX j) h (hrefl j) hne (1 / 2)
      (by norm_num) (by norm_num)
    exact hcore {j} (hblock j hω.symm hpref.symm hs)
  · have hs := hsc (x i) (hxX i) (x i) (hxX i) (x j) (hxX j) (hrefl i) h hne (1 / 2)
      (by norm_num) (by norm_num)
    exact hcore {i} (hblock i rfl rfl hs)

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Debreu-Scarf core convergence theorem (MWG Section 18.B, pp. 657-659)

**Proposition 18.B.3** (p. 657) states: if the feasible type allocation `x*` is in `C_N` for every
`N = 1, 2, ...`, then `x*` is a Walrasian equilibrium allocation, under the standing assumptions of
Section 18.B, which only ask `ωₕ ≥ 0`.

* As printed the proposition is false (`proposition_18_B_3_false`): with one type, two goods,
  `ω = (1, 0)`, `u = √x₁ + √x₂` and `Y = -ℝ²₊` (standing assumptions hold), the no-trade
  allocation `x* = ω` lies in every `C_N` (`oneZero_mem_core`: nobody can do better than `(1, 0)`
  with only good 1 available) but is not Walrasian at any price vector (`not_maximal_one_zero`:
  the marginal utility of good 2 at `x₂ = 0` is infinite, so a small trade always pays when good 2
  is not free, and when it is free `(1, 1)` is affordable).
* The corrected statement `proposition_18_B_3` adds `ωₕ ≫ 0` for every type (the assumption of
  Debreu and Scarf; the book's special-case proof assumes it in a stronger form) and is proved in
  the full generality of Section 18.B (any convex constant returns `Y`, continuous, strictly
  convex, strongly monotone preferences, any number of goods and types). The proof: the convex
  hull `Γ` of the improving net trades `{z : z + ωₕ ≻ₕ x*ₕ}` does not meet `Y - ℝ^L₊₊`, because
  a point of the intersection, after grouping by type (`exists_type_combination`) and rounding the
  weights down (`exists_rounding`), gives a blocking coalition of a large replica
  (`disjoint_improving_trades`); separating the two convex sets gives prices `p ≥ 0`, `p ≠ 0`,
  with `p·y ≤ 0` on `Y` and `p·z ≥ 0` on `Γ`, hence a quasi-equilibrium, and `p·ωₕ > 0` turns it
  into an equilibrium (cheaper point argument).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {L : ℕ}

/-! ### The counterexample to Proposition 18.B.3 as printed -/

/-- At any prices `p`, the bundle `(1, 0)` is not maximal for `√x₁ + √x₂` in the budget set
`{x ≥ 0 : p·x ≤ p·(1, 0)}`. -/
theorem not_maximal_one_zero (p : Fin 2 → ℝ) :
    ¬ IsMaximalFor (utilityPref sqrtU) (budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ ![1, 0]))
      ![1, 0] := by
  intro h
  have hu : sqrtU ![1, 0] = 1 := by rw [sqrtU_vec, Real.sqrt_one, Real.sqrt_zero, add_zero]
  have hw : p ⬝ᵥ ![1, 0] = p 0 := by rw [dot_two]; simp
  -- any affordable bundle with utility above `1` contradicts maximality
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → p 0 * a + p 1 * b ≤ p 0 →
      1 < Real.sqrt a + Real.sqrt b → False := by
    intro a b ha hb hab hgt
    have hmem : (![a, b] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ ![1, 0]) := by
      refine ⟨fun l => by fin_cases l <;> simpa, ?_⟩
      rw [hw, dot_two]
      simpa using hab
    have := h.2 _ hmem
    change sqrtU ![a, b] ≤ sqrtU ![1, 0] at this
    rw [hu, sqrtU_vec] at this
    linarith
  rcases le_or_gt (p 1) 0 with hp1 | hp1
  · refine key 1 1 zero_le_one zero_le_one (by linarith) ?_
    rw [Real.sqrt_one]
    norm_num
  rcases le_or_gt (p 0) 0 with hp0 | hp0
  · refine key 2 0 (by norm_num) le_rfl (by linarith) ?_
    rw [Real.sqrt_zero, add_zero]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · -- a small trade: give up `t` of good 1 for `t·p₁/p₂` of good 2
    set r := p 0 / p 1 with hr
    have hr0 : 0 < r := div_pos hp0 hp1
    set t := min (1 / 2) (r / 2) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (by linarith)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    have ht2 : t ≤ r / 2 := min_le_right _ _
    refine key (1 - t) (t * r) (by linarith) (by positivity) ?_ ?_
    · have : p 1 * (t * r) = t * p 0 := by
        rw [hr]
        field_simp
      nlinarith
    · have h1 : 1 - t ≤ Real.sqrt (1 - t) := by
        rw [Real.le_sqrt (by linarith) (by linarith)]
        nlinarith
      have h2 : t < Real.sqrt (t * r) := by
        rw [Real.lt_sqrt ht0.le]
        nlinarith
      linarith

/-- If every consumer has utility `√x₁ + √x₂` and endowment `(1, 0)` and `Y = -ℝ²₊`, the no-trade
allocation is in the core: a blocking coalition would need more than one unit of good 1 per
member, as good 2 is not available. -/
theorem oneZero_mem_core {ι : Type*} [Fintype ι] (E : CoreEconomy ι 2)
    (hpref : ∀ i, E.pref i = utilityPref sqrtU) (hω : ∀ i, E.ω i = ![1, 0])
    (hY : E.Y = nonposOrthant 2) : (fun _ => ![1, 0]) ∈ E.core := by
  refine ⟨⟨fun _ l => by fin_cases l <;> norm_num, 0, hY ▸ fun _ => le_rfl, ?_⟩, ?_⟩
  · simp [hω]
  rintro S ⟨hS, x', hx', y, hy, hsum⟩
  rw [hY] at hy
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply, hω] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_const_zero,
    add_zero] at e0 e1
  -- nobody in `S` gets good 2
  have h1 : ∀ i ∈ S, x' i 1 = 0 := by
    have hle : ∑ i ∈ S, x' i 1 ≤ 0 := by rw [e1]; exact hy 1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i hi => (hx' i hi).1 1).mp
      (le_antisymm hle (Finset.sum_nonneg fun i hi => (hx' i hi).1 1))
    exact this
  have hgt : ∀ i ∈ S, (1 : ℝ) < x' i 0 := by
    intro i hi
    have hs := (hx' i hi).2.2
    rw [hpref] at hs
    change ¬ sqrtU (x' i) ≤ sqrtU ![1, 0] at hs
    rw [sqrtU_two, sqrtU_vec, h1 i hi, Real.sqrt_one, Real.sqrt_zero, add_zero,
      add_zero] at hs
    by_contra hle
    push Not at hle
    exact hs (Real.sqrt_le_one.mpr hle)
  have := Finset.sum_lt_sum_of_nonempty hS hgt
  rw [e0] at this
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  linarith [hy 0]

/-- The economy of types of the counterexample: one type, `u = √x₁ + √x₂`, `ω = (1, 0)`,
`Y = -ℝ²₊`. -/
noncomputable def dsEconomy : CoreEconomy (Fin 1) 2 := sqrtEconomy fun _ => ![1, 0]

/-- **Proposition 18.B.3** (MWG, p. 657) is false as printed (with `ωₕ ≥ 0` only): the economy
`dsEconomy` satisfies the standing assumptions of Section 18.B, the type allocation `x* = ω`
(no trade) belongs to `C_N` for every `N`, but it is not a Walrasian equilibrium allocation. -/
theorem proposition_18_B_3_false :
    dsEconomy.Standing ∧ (∀ N, (fun _ => ![1, 0]) ∈ dsEconomy.CN N) ∧
      ¬ dsEconomy.IsWalrasAlloc (fun _ => ![1, 0]) := by
  refine ⟨sqrtEconomy_standing fun _ l => by fin_cases l <;> norm_num, fun N => ⟨?_, ?_⟩, ?_⟩
  · exact (oneZero_mem_core dsEconomy (fun _ => rfl) (fun _ => rfl) rfl).1
  · exact oneZero_mem_core (dsEconomy.replica N) (fun _ => rfl) (fun _ => rfl) rfl
  · rintro ⟨p, -, hx⟩
    exact not_maximal_one_zero p (hx 0)

/-! ### Lemmas for the proof of the corrected Proposition 18.B.3 -/

/-- With strictly convex preferences, the strictly preferred set `{u ≥ 0 : u ≻ x}` is convex. -/
theorem convex_strictUpper {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) : Convex ℝ {u | u ∈ nonnegOrthant L ∧ Strict r u x} := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_nonnegOrthant L hy.1 hz.1 ha hb hab, ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · by_cases hyz : y = z
      · subst hyz
        rw [← add_smul, hab, one_smul]
        exact hy.2
      · have hb1 : b = 1 - a := by linarith
        subst hb1
        exact hsc x hx y hy.1 z hz.1 hy.2.1 hz.2.1 hyz a ha' (by linarith)
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hy.2
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hz.2

/-- Grouping a convex combination by type: a point of the convex hull of `⋃ₕ Pₕ` (each `Pₕ`
convex, finitely many types) is `∑ₕ aₕ zₕ` with `a ≥ 0`, `∑ₕ aₕ = 1` and `zₕ ∈ Pₕ` whenever
`aₕ > 0`. -/
theorem exists_type_combination {H : Type*} [Fintype H] {P : H → Set (Fin L → ℝ)}
    (hP : ∀ h, Convex ℝ (P h)) {g : Fin L → ℝ} (hg : g ∈ convexHull ℝ (⋃ h, P h)) :
    ∃ a : H → ℝ, ∃ z : H → Fin L → ℝ, (∀ h, 0 ≤ a h) ∧ ∑ h, a h = 1 ∧
      (∀ h, 0 < a h → z h ∈ P h) ∧ ∑ h, a h • z h = g := by
  classical
  obtain ⟨K, hK, zk, w, hzB, -, hw, hw1, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hg
  have hmem : ∀ k, ∃ h, zk k ∈ P h := fun k => Set.mem_iUnion.mp (hzB ⟨k, rfl⟩)
  choose typ htyp using hmem
  set a : H → ℝ := fun h => ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k with ha
  set z : H → Fin L → ℝ :=
    fun h => (a h)⁻¹ • ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k • zk k with hz
  have ha0 : ∀ h, 0 ≤ a h := fun h => Finset.sum_nonneg fun k _ => (hw k).le
  -- `aₕ zₕ` is the sum of the terms of type `h`
  have haz : ∀ h, a h • z h = ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k • zk k := by
    intro h
    rcases (ha0 h).lt_or_eq with hpos | hzero
    · rw [hz, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · have hempty : Finset.univ.filter (fun k => typ k = h) = ∅ := by
        by_contra hne
        obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have : 0 < a h := Finset.sum_pos (fun k _ => hw k) ⟨k, hk⟩
        linarith
      rw [hempty, Finset.sum_empty, ← hzero, zero_smul]
  refine ⟨a, z, ha0, ?_, fun h hpos => ?_, ?_⟩
  · rw [← hw1]
    exact Finset.sum_fiberwise Finset.univ typ w
  · -- `zₕ` is a convex combination of points of `Pₕ`
    have := (hP h).sum_mem (t := Finset.univ.filter (fun k => typ k = h))
      (w := fun k => (a h)⁻¹ * w k) (z := zk)
      (fun k _ => mul_nonneg (inv_nonneg.mpr (ha0 h)) (hw k).le)
      (by rw [← Finset.mul_sum, inv_mul_cancel₀ hpos.ne'])
      (fun k hk => by
        have := htyp k
        rwa [(Finset.mem_filter.mp hk).2] at this)
    simpa [hz, Finset.smul_sum, smul_smul] using this
  · simp only [haz]
    rw [Finset.sum_fiberwise Finset.univ typ (fun k => w k • zk k)]
    exact hcomb

/-- Rounding: given weights `a ≥ 0` with `∑ aₕ = 1`, vectors `zₕ` and `n ≪ 0`, there are `N ≥ 1`
and integers `kₕ = ⌊N aₕ⌋ ≤ N`, at least one of them positive, `kₕ > 0` only if `aₕ > 0`, such that
`N (∑ₕ aₕ zₕ - n) - ∑ₕ kₕ zₕ ≫ 0`. -/
theorem exists_rounding {H : Type*} [Fintype H] (a : H → ℝ) (z : H → Fin L → ℝ)
    (ha0 : ∀ h, 0 ≤ a h) (ha1 : ∑ h, a h = 1) {n : Fin L → ℝ} (hn : ∀ l, n l < 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ k : H → ℕ, (∀ h, k h ≤ N) ∧ (∀ h, 0 < k h → 0 < a h) ∧
      (∃ h₀, 0 < k h₀) ∧ ∀ l, 0 < ((N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (k h : ℝ) • z h) l := by
  classical
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, 0 < a h₀ := by
    by_contra hall
    push Not at hall
    have : ∑ h, a h ≤ 0 := Finset.sum_nonpos fun h _ => hall h
    linarith
  -- a scale making `-N n` dominate the rounding errors, with `N a_{h₀} ≥ 1`
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ l, ∑ h, |z h l| < (N₁ : ℝ) * -n l := by
    have hex : ∀ l, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∑ h, |z h l| < (m : ℝ) * -n l := by
      intro l
      obtain ⟨N, hN⟩ := exists_nat_gt ((∑ h, |z h l|) / -n l)
      refine ⟨N, fun m hm => ?_⟩
      have hm' : (∑ h, |z h l|) / -n l < m := lt_of_lt_of_le hN (by exact_mod_cast hm)
      rwa [div_lt_iff₀ (by linarith [hn l])] at hm'
    choose Nl hNl using hex
    exact ⟨Finset.univ.sup Nl, fun l => hNl l _ (Finset.le_sup (Finset.mem_univ l))⟩
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / a h₀)
  set N := max (max N₁ N₂) 1 with hN
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNN₁ : (N₁ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₂ : (N₂ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
  have hale : ∀ h, a h ≤ 1 := fun h => by
    rw [← ha1]
    exact Finset.single_le_sum (fun h _ => ha0 h) (Finset.mem_univ h)
  refine ⟨N, hN1, fun h => ⌊(N : ℝ) * a h⌋₊, fun h => ?_, fun h hk => ?_, ⟨h₀, ?_⟩, fun l => ?_⟩
  · apply Nat.floor_le_of_le
    calc (N : ℝ) * a h ≤ N * 1 := mul_le_mul_of_nonneg_left (hale h) (Nat.cast_nonneg N)
      _ = N := mul_one _
  · rcases (ha0 h).lt_or_eq with hpos | hzero
    · exact hpos
    · have : a h = 0 := hzero.symm
      simp [this] at hk
  · apply Nat.floor_pos.mpr
    rw [div_lt_iff₀ hh₀] at hN₂
    nlinarith
  · have hterm : ∀ h, -|z h l| ≤ ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l := by
      intro h
      have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (ha0 h))
      have h2 := Nat.lt_floor_add_one ((N : ℝ) * a h)
      have h3 : 0 ≤ (N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊ := by linarith
      have h4 : (N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊ ≤ 1 := by linarith
      have h5 := neg_abs_le (z h l)
      have h6 := le_abs_self (z h l)
      nlinarith [abs_nonneg (z h l)]
    have hsum : -∑ h, |z h l| ≤ ∑ h, ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun h _ => hterm h
    have heq : ((N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (⌊(N : ℝ) * a h⌋₊ : ℝ) • z h) l =
        ∑ h, ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l - N * n l := by
      simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_sub,
        Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc]
      ring
    rw [heq]
    have := hN₁ l
    have : (N₁ : ℝ) * -n l ≤ N * -n l := mul_le_mul_of_nonneg_right hNN₁ (by linarith [hn l])
    linarith

/-- In the `N`-replica, the coalition with the first `kₕ ≤ N` members of every type `h`: summing
a function of the type over it gives `∑ₕ kₕ fₕ`. -/
theorem sum_replica_filter {H : Type*} [Fintype H] {N : ℕ} (k : H → ℕ) (hk : ∀ h, k h ≤ N)
    (f : H → Fin L → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : H × Fin N => (i.2 : ℕ) < k i.1), f i.1 =
      ∑ h, (k h : ℝ) • f h := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, Fin.card_filter_val_lt, min_eq_right (hk h),
    Nat.cast_smul_eq_nsmul]

/-! ### Proposition 18.B.3, corrected -/

open scoped Pointwise in
/-- Step (a) of the proof of Proposition 18.B.3: if `x*` is in `C_N` for all `N ≥ 1`, the convex
hull of the improving net trades `⋃ₕ {z : z + ωₕ ≥ 0, z + ωₕ ≻ₕ x*ₕ}` does not meet `Y - ℝ^L₊₊`
(otherwise rounding a convex combination gives a blocking coalition of a large replica). -/
theorem disjoint_improving_trades {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hst : E.Standing) {x : H → Fin L → ℝ} (hx : ∀ N, 1 ≤ N → x ∈ E.CN N) :
    Disjoint (E.Y + {n | ∀ l, n l < 0})
      (convexHull ℝ (⋃ h, (fun z => z + E.ω h) ⁻¹'
        {u | u ∈ nonnegOrthant L ∧ Strict (E.pref h) u (x h)})) := by
  classical
  have hxX : ∀ h, x h ∈ nonnegOrthant L := (hx 1 le_rfl).1.1
  have hr := fun h => (hst.2 h).2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  rw [Set.disjoint_left]
  rintro g ⟨y, hy, n, hn, rfl⟩ hg
  obtain ⟨a, z, ha0, ha1, hzP, hcomb⟩ := exists_type_combination
    (fun h => ((convex_strictUpper (hst.2 h).2.2.2.1 (hxX h)).translate_preimage_left
      (E.ω h))) hg
  obtain ⟨N, hN1, k, hkN, hka, ⟨h₀, hh₀⟩, hd⟩ := exists_rounding a z ha0 ha1 hn
  set d : Fin L → ℝ := (N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (k h : ℝ) • z h with hddef
  have hy' : ∑ h, a h • z h - n = y := by rw [hcomb]; simp
  set S := Finset.univ.filter (fun i : H × Fin N => (i.2 : ℕ) < k i.1) with hS
  set i₀ : H × Fin N := (h₀, ⟨0, hN1⟩) with hi₀
  have hi₀S : i₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh₀⟩
  set x' : H × Fin N → Fin L → ℝ := fun i => z i.1 + E.ω i.1 + if i = i₀ then d else 0
    with hx'
  apply (hx N hN1).2.2 S
  refine ⟨⟨i₀, hi₀S⟩, x', fun i hi => ?_, (N : ℝ) • y, hst.1.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  · have hki : 0 < k i.1 := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_filter.mp hi).2
    have hP := hzP i.1 (hka i.1 hki)
    by_cases hii : i = i₀
    · by_cases hd0 : d = 0
      · have : x' i = z i.1 + E.ω i.1 := by simp only [hx', hii, ↓reduceIte, hd0, add_zero]
        rw [this]
        exact hP
      · have hle : z i.1 + E.ω i.1 ≤ x' i := fun l => by
          simp only [hx', hii, ↓reduceIte, Pi.add_apply]
          linarith [hd l]
        have hne : x' i ≠ z i.1 + E.ω i.1 := by
          intro h
          apply hd0
          simpa only [hx', hii, ↓reduceIte, add_eq_left] using h
        have hX : x' i ∈ nonnegOrthant L := fun l => le_trans (hP.1 l) (hle l)
        refine ⟨hX, ?_⟩
        exact strict_of_strict_of_pref (hr i.1).2 hX hP.1 (hxX i.1)
          (hm i.1 _ hP.1 _ hX hle hne) hP.2.1
    · have : x' i = z i.1 + E.ω i.1 := by simp only [hx', hii, ↓reduceIte, add_zero]
      rw [this]
      exact hP
  · change ∑ i ∈ S, x' i = (N : ℝ) • y + ∑ i ∈ S, E.ω i.1
    simp only [hx', Finset.sum_add_distrib, Finset.sum_ite_eq', hi₀S, ↓reduceIte]
    rw [hS, sum_replica_filter k hkN z, hddef, hy']
    abel

/-- **Proposition 18.B.3** (MWG, p. 657), corrected: under the standing assumptions of Section 18.B
(any convex constant returns technology `Y`; continuous, strictly convex, strongly monotone
preferences on `ℝ^L₊`) and **strictly positive endowments** `ωₕ ≫ 0`, a type allocation `x*` that
belongs to `C_N` for every `N ≥ 1` is a Walrasian equilibrium allocation. (Without `ωₕ ≫ 0` the
statement fails: `proposition_18_B_3_false`.) -/
theorem proposition_18_B_3 {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    (hω : ∀ h l, 0 < E.ω h l) {x : H → Fin L → ℝ} (hx : ∀ N, 1 ≤ N → x ∈ E.CN N) :
    E.IsWalrasAlloc x := by
  classical
  obtain ⟨hxX, yf, hyf, hsumf⟩ := (hx 1 le_rfl).1
  have hY := hst.1
  have hr := fun h => (hst.2 h).2.1
  have hc := fun h => (hst.2 h).2.2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  rcases Nat.eq_zero_or_pos L with hL | hL
  · -- no goods: every price vector works
    subst hL
    refine ⟨0, ⟨yf, hyf, hsumf, fun y' _ => by simp⟩, fun h => ⟨⟨hxX h, by simp⟩,
      fun x' _ => ?_⟩⟩
    rw [Subsingleton.elim x' (x h)]
    exact ((hr h).1 _ (hxX h) _ (hxX h)).elim id id
  set Nn : Set (Fin L → ℝ) := {n | ∀ l, n l < 0} with hNn
  have hNopen : IsOpen Nn := by
    have : Nn = ⋂ l, {n : Fin L → ℝ | n l < 0} := by ext n; simp [hNn]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt (continuous_apply l) continuous_const
  have hNconv : Convex ℝ Nn := by
    intro a ha b hb s t hs ht hst' l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := ha l
    have := hb l
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [mul_neg_of_pos_of_neg hs' (ha l), mul_nonpos_of_nonneg_of_nonpos ht (hb l).le]
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using hb l
  have hdisj := disjoint_improving_trades E hst hx
  obtain ⟨f, u, hfO, hfΓ⟩ := geometric_hahn_banach_open (hY.1.add hNconv)
    (hNopen.add_left) (convex_convexHull ℝ _) hdisj
  obtain ⟨q, hq⟩ := duality_exists_dot_of_clm f
  have hO : ∀ y ∈ E.Y, ∀ n : Fin L → ℝ, (∀ l, n l < 0) → q ⬝ᵥ y + q ⬝ᵥ n < u := by
    intro y hy n hn
    have := hfO (y + n) (Set.add_mem_add hy hn)
    rwa [hq, dotProduct_add] at this
  have hP : ∀ h, ∀ z : Fin L → ℝ, z + E.ω h ∈ nonnegOrthant L →
      Strict (E.pref h) (z + E.ω h) (x h) → u ≤ q ⬝ᵥ z := by
    intro h z h1 h2
    have := hfΓ z (subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨h, h1, h2⟩))
    rwa [hq] at this
  have hone : q ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ l, q l := by simp [dotProduct]
  have h0Y : (0 : Fin L → ℝ) ∈ E.Y := hY.2.1
  -- `q ≥ 0`
  have hq0 : ∀ l, 0 ≤ q l := by
    intro l
    by_contra hneg
    push Not at hneg
    set t := max 0 ((u + ∑ k, q k) / -q l) + 1 with ht
    have ht1 : 1 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / -q l)]
    have ht2 : (u + ∑ k, q k) / -q l ≤ t - 1 := by
      linarith [le_max_right 0 ((u + ∑ k, q k) / -q l)]
    have hmem : ∀ k, ((-(Pi.single l t) - fun _ => (1 : ℝ)) : Fin L → ℝ) k < 0 := by
      intro k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]
    have := hO 0 h0Y _ hmem
    rw [dotProduct_zero, zero_add, dotProduct_sub, dotProduct_neg, hone] at this
    have hdot1 : q ⬝ᵥ (Pi.single l t : Fin L → ℝ) = q l * t := by simp
    rw [hdot1] at this
    have hql : 0 < -q l := by linarith
    rw [div_le_iff₀ hql] at ht2
    nlinarith
  have hS0 : 0 ≤ ∑ l, q l := Finset.sum_nonneg fun l _ => hq0 l
  -- `u ≥ 0`
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    set ε := -u / (∑ k, q k + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have := hO 0 h0Y (fun _ => -ε) (fun _ => by linarith)
    rw [dotProduct_zero, zero_add] at this
    have hdot : q ⬝ᵥ (fun _ => -ε) = -ε * ∑ k, q k := by
      simp [dotProduct, Finset.sum_mul, mul_comm]
    rw [hdot] at this
    have : -ε * ∑ k, q k ≥ u := by
      rw [hε, ge_iff_le, neg_div, neg_mul, neg_mul, neg_neg, div_mul_eq_mul_div,
        le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  -- `q·y ≤ 0` on `Y`
  have hqY : ∀ y ∈ E.Y, q ⬝ᵥ y ≤ 0 := by
    intro y hy
    by_contra hpos
    push Not at hpos
    set t := max 0 ((u + ∑ k, q k) / (q ⬝ᵥ y)) + 1 with ht
    have ht0 : 0 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / (q ⬝ᵥ y))]
    have ht2 : (u + ∑ k, q k) / (q ⬝ᵥ y) ≤ t - 1 := by
      linarith [le_max_right 0 ((u + ∑ k, q k) / (q ⬝ᵥ y))]
    have := hO (t • y) (hY.2.2 y hy t ht0) (fun _ => -1) (fun _ => by norm_num)
    have hdot : q ⬝ᵥ (fun _ => (-1 : ℝ)) = -∑ k, q k := by simp [dotProduct]
    rw [dotProduct_smul, smul_eq_mul, hdot] at this
    rw [div_le_iff₀ hpos] at ht2
    nlinarith
  -- `q·x*ₕ ≥ q·ωₕ`: bundles slightly above `x*ₕ` are improving
  have hL0 : (⟨0, hL⟩ : Fin L) = ⟨0, hL⟩ := rfl
  have hup : ∀ h, ∀ ε : ℝ, 0 < ε → x h + (fun _ => ε) ∈ nonnegOrthant L ∧
      Strict (E.pref h) (x h + fun _ => ε) (x h) := by
    intro h ε hε
    have hX : x h + (fun _ => ε) ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hxX h l]
    refine ⟨hX, hm h (x h) (hxX h) _ hX (fun l => ?_) fun heq => ?_⟩
    · simp only [Pi.add_apply]; linarith
    · have := congrFun heq ⟨0, hL⟩
      simp only [Pi.add_apply, add_eq_left] at this
      linarith
  have hxω : ∀ h, q ⬝ᵥ E.ω h ≤ q ⬝ᵥ x h := by
    intro h
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / (∑ k, q k + 1) with hε
    have hε0 : 0 < ε := div_pos hε' (by linarith)
    obtain ⟨hX, hs⟩ := hup h ε hε0
    have := hP h (x h + (fun _ => ε) - E.ω h) (by simpa using hX) (by simpa using hs)
    rw [dotProduct_sub, dotProduct_add] at this
    have hdot : q ⬝ᵥ (fun _ => ε) = ε * ∑ k, q k := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hdot] at this
    have hεS : ε * ∑ k, q k ≤ ε' := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- budgets balance and the production plan maximizes profit
  have hsumq : ∑ h, (q ⬝ᵥ x h - q ⬝ᵥ E.ω h) = q ⬝ᵥ yf := by
    rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsumf, dotProduct_add]
    ring
  have hbal : ∀ h, q ⬝ᵥ x h - q ⬝ᵥ E.ω h = 0 := by
    have hle : ∑ h, (q ⬝ᵥ x h - q ⬝ᵥ E.ω h) ≤ 0 := by rw [hsumq]; exact hqY yf hyf
    have := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => sub_nonneg.mpr (hxω h)).mp
      (le_antisymm hle (Finset.sum_nonneg fun h _ => sub_nonneg.mpr (hxω h)))
    exact fun h => this h (Finset.mem_univ h)
  have hyf0 : q ⬝ᵥ yf = 0 := by
    rw [← hsumq]
    exact Finset.sum_eq_zero fun h _ => hbal h
  refine ⟨q, ⟨yf, hyf, hsumf, fun y' hy' => by rw [hyf0]; exact hqY y' hy'⟩, fun h => ?_⟩
  -- `q ≠ 0`, hence `q·ωₕ > 0`
  have hqne : q ≠ 0 := by
    intro hq0'
    obtain ⟨hX, hs⟩ := hup h 1 one_pos
    have h1 := hP h (x h + (fun _ => 1) - E.ω h) (by simpa using hX) (by simpa using hs)
    have h2 := hO 0 h0Y (fun _ => -1) (fun _ => by norm_num)
    rw [hq0'] at h1 h2
    simp only [zero_dotProduct, add_zero] at h1 h2
    linarith
  have hqω : 0 < q ⬝ᵥ E.ω h := dotProduct_pos_of_nonneg_ne_zero hq0 hqne (hω h)
  refine isMaximalFor_of_strict_gt (hr h) (hxX h) (by linarith [hbal h]) fun x' hx' hs => ?_
  have h1 := hP h (x' - E.ω h) (by simpa using hx') (by simpa using hs)
  rw [dotProduct_sub] at h1
  rcases (show q ⬝ᵥ E.ω h ≤ q ⬝ᵥ x' by linarith).lt_or_eq with h3 | h3
  · exact h3
  exfalso
  -- the cheaper point: reduce a good with positive price held in positive quantity
  obtain ⟨m, hmpos⟩ : ∃ m, 0 < q m * x' m := by
    by_contra hall
    push Not at hall
    have : q ⬝ᵥ x' ≤ 0 := Finset.sum_nonpos fun m _ => hall m
    linarith
  have hxm : 0 < x' m := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (hq0 m) hle]
  have hqm : 0 < q m := by
    by_contra hle
    push Not at hle
    have : q m = 0 := le_antisymm hle (hq0 m)
    rw [this, zero_mul] at hmpos
    exact lt_irrefl 0 hmpos
  obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single (hr h) (hc h) hx' (hxX h) hs hxm
  have h4 := hP h (x' - Pi.single m δ - E.ω h) (by simpa using hmem) (by simpa using hs')
  rw [dotProduct_sub, dotProduct_sub, ← h3] at h4
  simp only [dotProduct_single, sub_sub_cancel_left] at h4
  nlinarith

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The book's proof of Proposition 18.B.3 (MWG Section 18.B, pp. 657-659, 685)

* The special-case proof (pp. 657-658): from a type allocation that is not Walrasian, take a
  favoured type `h₁` (`exists_favoured_type`, `grad_dot_pos_of_proportional`) and form the
  coalition of `N - 1` members of type `h₁` and `N` of every other type, each member of type `h`
  getting `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))`. The displayed identity
  (`special_coalition_identity`) makes it feasible (`special_coalition_blocks`), the `x'ₕ` are
  nonnegative for large `N` when `xₕ ≫ 0` (`special_nonneg_eventually`), and, by
  **Exercise 18.B.4** (`exercise_18_B_4`, first-order Taylor: `∇u(x)·v > 0` gives
  `u(x + αv) > u(x)` for `0 < α < ᾱ`), every member gains for large `N`. Together:
  `proposition_18_B_3_special_case`.
* p. 659, pure exchange: `Vᵢ = {xᵢ ≥ 0 : xᵢ ≻ᵢ x*ᵢ} ∪ {ωᵢ}` (`coreVset`), `V = ∑ᵢ Vᵢ` (`coreV`),
  `∑ᵢ ωᵢ ∈ V` (`sum_endow_mem_coreV`), and the core property implies that `∑ᵢ ωᵢ` is not interior
  to `V` (`core_not_mem_interior_coreV`; this needs at least one good). If `p ≠ 0` supports `V` at
  `∑ᵢ ωᵢ`, then `p` is a Walrasian price vector for `x*` (`supporting_price_isWalrasEqm`) with
  continuity, strong monotonicity and **`ωᵢ ≫ 0`** (an added hypothesis: the final step
  `p·x'ᵢ > p·ωᵢ` needs `p·ωᵢ > 0`; without it the claim fails,
  `supporting_price_needs_positive_endowment`). `V` need not be convex
  (`coreVset_not_convex`).
* Footnote 6 (Anderson's proof) and the Aumann-Vind continuum remark are verbal.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open Filter Topology

variable {L : ℕ}

/-! ### The special-case proof (pp. 657-658) -/

/-- **Section 18.B** (MWG, p. 657). If the net trades of the types are worth `0` in total at `p`
but not all zero, some type `h` has `p·(xₕ - ωₕ) > 0` (a favoured type). -/
theorem exists_favoured_type {H : Type*} [Fintype H] {p : Fin L → ℝ} {x ω : H → Fin L → ℝ}
    (hsum : ∑ h, p ⬝ᵥ (x h - ω h) = 0) (hne : ∃ h, p ⬝ᵥ (x h - ω h) ≠ 0) :
    ∃ h, 0 < p ⬝ᵥ (x h - ω h) := by
  by_contra hall
  push Not at hall
  obtain ⟨h, hh⟩ := hne
  have := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hall k).mp hsum h (Finset.mem_univ h)
  exact hh this

/-- **Section 18.B** (MWG, p. 658). If `∇uₕ(xₕ) = μₕ p` with `μₕ > 0` and `p·(x₁ - ω₁) > 0`, then
`∇uₕ(xₕ)·(x₁ - ω₁) > 0`. -/
theorem grad_dot_pos_of_proportional {g p v : Fin L → ℝ} {μ : ℝ} (hμ : 0 < μ) (hg : g = μ • p)
    (hv : 0 < p ⬝ᵥ v) : 0 < g ⬝ᵥ v := by
  rw [hg, smul_dotProduct, smul_eq_mul]
  exact mul_pos hμ hv

/-- **Section 18.B** (MWG, p. 658), the displayed identity. Let `x` be a feasible type allocation,
`∑ₕ xₕ = y + ∑ₕ ωₕ`, and consider the coalition with `N - 1` members of type `h₁` and `N` of every
other type, `cₕ` members of type `h`, `D = ∑ₕ cₕ = (N - 1) + N(H - 1)`; every member of type `h`
gets `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / D`. Then `∑ₕ cₕ x'ₕ = N y + ∑ₕ cₕ ωₕ` (the book has
`y = 0`). -/
theorem special_coalition_identity {H : Type*} [Fintype H] [DecidableEq H] (h₁ : H) (N : ℕ)
    {x ω : H → Fin L → ℝ} {y : Fin L → ℝ} (hsum : ∑ h, x h = y + ∑ h, ω h)
    (hD : (N : ℝ) * Fintype.card H - 1 ≠ 0) :
    ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) •
        (x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - ω h₁)) =
      (N : ℝ) • y + ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • ω h := by
  have hc : ∑ h : H, ((N : ℝ) - if h = h₁ then 1 else 0) = (N : ℝ) * Fintype.card H - 1 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Finset.card_univ, nsmul_eq_mul]
    ring
  have hsplit : ∀ f : H → Fin L → ℝ,
      ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • f h = (N : ℝ) • ∑ h, f h - f h₁ := by
    intro f
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hc, smul_smul, mul_inv_cancel₀ hD, one_smul, hsplit x, hsplit ω, hsum,
    smul_add]
  abel

/-- **Section 18.B** (MWG, p. 658). The coalition of all consumers of the `N`-replica except one of
type `h₁` blocks the equal-treatment allocation of `x` if every member of type `h` strictly
prefers `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))` and `x'ₕ ≥ 0` (constant returns:
`N y ∈ Y`). -/
theorem special_coalition_blocks {H : Type*} [Fintype H] [DecidableEq H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) (h₁ : H) {N : ℕ} (hN : 1 ≤ N)
    (hD : (N : ℝ) * Fintype.card H - 1 ≠ 0) {x : H → Fin L → ℝ} (hx : E.IsFeasible x)
    (hX : ∀ h, x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁) ∈ nonnegOrthant L)
    (hS : ∀ h, Strict (E.pref h) (x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁))
      (x h)) :
    (E.replica N).Blocks (Finset.univ.erase (h₁, ⟨0, hN⟩)) (typeAlloc x N) := by
  obtain ⟨-, y, hy, hsum⟩ := hx
  set x' : H → Fin L → ℝ := fun h => x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁)
    with hx'
  -- summing a function of the type over the coalition
  have hcoal : ∀ f : H → Fin L → ℝ, ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), f i.1 =
      ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • f h := by
    intro f
    have h1 := Finset.add_sum_erase Finset.univ (fun i : H × Fin N => f i.1)
      (Finset.mem_univ (h₁, ⟨0, hN⟩))
    have h2 : ∑ i : H × Fin N, f i.1 = (N : ℝ) • ∑ h, f h := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
        Finset.smul_sum]
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← h2, ← h1]
    abel
  refine ⟨?_, fun i => x' i.1, fun i _ => ⟨hX i.1,
    hS i.1⟩, (N : ℝ) • y, hY.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  · obtain ⟨i, hi⟩ : (Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin]
      have hH : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr ⟨h₁⟩
      have h1 : 1 ≤ Fintype.card H * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp hH) (Nat.one_le_iff_ne_zero.mp hN))
      by_contra h0
      have : Fintype.card H * N = 1 := by omega
      apply hD
      have : ((Fintype.card H * N : ℕ) : ℝ) = 1 := by exact_mod_cast this
      push_cast at this
      linarith
    exact ⟨i, hi⟩
  · change ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), x' i.1 =
      (N : ℝ) • y + ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), E.ω i.1
    rw [hcoal, hcoal]
    exact special_coalition_identity h₁ N hsum hD

/-- **Section 18.B** (MWG, p. 658). If every `xₕ ≫ 0`, the consumptions
`x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))` are nonnegative for all `N` large enough. -/
theorem special_nonneg_eventually {H : Type*} [Fintype H] (h₁ : H) {x ω : H → Fin L → ℝ}
    (hx : ∀ h l, 0 < x h l) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ h,
      x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - ω h₁) ∈ nonnegOrthant L := by
  classical
  set v := x h₁ - ω h₁ with hv
  have hex : ∀ q : H × Fin L, ∃ M : ℕ, |v q.2| / x q.1 q.2 + 1 < M := fun q => exists_nat_gt _
  choose M hM using hex
  refine ⟨Finset.univ.sup M + 1, fun N hN h l => ?_⟩
  have hH : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨h₁⟩
  have hMN : (M (h, l) : ℝ) + 1 ≤ N := by
    have : M (h, l) ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ (h, l))
    exact_mod_cast (show M (h, l) + 1 ≤ N by omega)
  have hD : (N : ℝ) - 1 ≤ (N : ℝ) * Fintype.card H - 1 := by
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hlt := hM (h, l)
  have hxl := hx h l
  have hDpos : |v l| / x h l + 1 < (N : ℝ) * Fintype.card H - 1 := by
    simp only at hlt
    linarith
  have hD0 : 0 < (N : ℝ) * Fintype.card H - 1 := by
    have := div_nonneg (abs_nonneg (v l)) hxl.le
    linarith
  have habs : |v l| < ((N : ℝ) * Fintype.card H - 1) * x h l := by
    rw [div_add_one hxl.ne', div_lt_iff₀ hxl] at hDpos
    nlinarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : -(((N : ℝ) * Fintype.card H - 1) * x h l) < v l := by
    linarith [neg_abs_le (v l)]
  have h2 : -x h l < ((N : ℝ) * Fintype.card H - 1)⁻¹ * v l := by
    rw [inv_mul_eq_div, lt_div_iff₀ hD0]
    linarith
  change 0 ≤ x h l + ((N : ℝ) * Fintype.card H - 1)⁻¹ * v l
  linarith

/-- **Exercise 18.B.4** (MWG, p. 685), Taylor's formula to first order: if `u` is differentiable at
`x` with derivative `u'` and `u'(v) = ∇u(x)·v > 0`, there is `ᾱ > 0` with `u(x + αv) > u(x)` for all
`0 < α < ᾱ`. -/
theorem exercise_18_B_4 {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ} {x v : Fin L → ℝ}
    (hu : HasFDerivAt u u' x) (hv : 0 < u' v) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ a : ℝ, 0 < a → a < abar → u x < u (x + a • v) := by
  have hl : HasDerivAt (fun a : ℝ => x + a • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hu0 : HasFDerivAt u u' (x + (0 : ℝ) • v) := by simpa using hu
  have hg : HasDerivAt (fun a : ℝ => u (x + a • v)) (u' v) 0 := hu0.comp_hasDerivAt 0 hl
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < slope (fun a : ℝ => u (x + a • v)) 0 a :=
    ((hs.mono_left (nhdsWithin_mono 0 fun a (ha : 0 < a) => ha.ne')).eventually
      (lt_mem_nhds hv))
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨b, hb, fun a ha hab => ?_⟩
  have := hsub ⟨ha, hab⟩
  change 0 < slope (fun a : ℝ => u (x + a • v)) 0 a at this
  simp only [slope_def_field, zero_smul, add_zero, sub_zero] at this
  have := (div_pos_iff_of_pos_right ha).mp this
  linarith

/-- **Exercise 18.B.4** (MWG, p. 685), with the gradient: `∇u(x)·v > 0` gives `u(x + αv) > u(x)`
for `0 < α < ᾱ`. -/
theorem exercise_18_B_4_grad {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {x v g : Fin L → ℝ} (hu : HasFDerivAt u u' x) (hg : ∀ w, u' w = g ⬝ᵥ w) (hv : 0 < g ⬝ᵥ v) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ a : ℝ, 0 < a → a < abar → u x < u (x + a • v) :=
  exercise_18_B_4 hu (by rw [hg]; exact hv)

/-- **Proposition 18.B.3** (MWG, pp. 657-658), the book's special-case argument completed with
Exercise 18.B.4: let preferences be represented by utilities `uₕ` differentiable at `xₕ` with
`∇uₕ(xₕ)·(x_{h₁} - ω_{h₁}) > 0` for every type (the favoured type `h₁` of p. 657), `xₕ ≫ 0`, and
`x` a feasible type allocation (constant returns technology). Then for some `N ≥ 1` the coalition
of `N - 1` members of type `h₁` and `N` of every other type blocks, so `x ∉ C_N`. -/
theorem proposition_18_B_3_special_case {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) (u : H → (Fin L → ℝ) → ℝ) (hu : ∀ h, E.pref h = utilityPref (u h))
    (u' : H → (Fin L → ℝ) →L[ℝ] ℝ) {x : H → Fin L → ℝ} (hx : E.IsFeasible x)
    (hpos : ∀ h l, 0 < x h l) (h₁ : H) (hd : ∀ h, HasFDerivAt (u h) (u' h) (x h))
    (hgain : ∀ h, 0 < u' h (x h₁ - E.ω h₁)) : ∃ N, 1 ≤ N ∧ x ∉ E.CN N := by
  classical
  have hTay := fun h => exercise_18_B_4 (hd h) (hgain h)
  choose abar habar hgt using hTay
  have hne : (Finset.univ : Finset H).Nonempty := ⟨h₁, Finset.mem_univ h₁⟩
  set A := Finset.univ.inf' hne abar with hA
  have hA0 : 0 < A := (Finset.lt_inf'_iff hne).mpr fun h _ => habar h
  have hAle : ∀ h, A ≤ abar h := fun h => Finset.inf'_le _ (Finset.mem_univ h)
  obtain ⟨N₀, hN₀⟩ := special_nonneg_eventually (ω := E.ω) h₁ hpos
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / A)
  set N := max (max N₀ 2) (M + 2) with hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNM : M + 2 ≤ N := le_max_right _ _
  have hH : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨h₁⟩
  have hDge : (N : ℝ) - 1 ≤ (N : ℝ) * Fintype.card H - 1 := by
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hNM' : (M : ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hD0 : 0 < (N : ℝ) * Fintype.card H - 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hDA : ((N : ℝ) * Fintype.card H - 1)⁻¹ < A := by
    rw [inv_lt_comm₀ hD0 hA0]
    have : 1 / A = A⁻¹ := one_div A
    linarith
  refine ⟨N, le_trans one_le_two hN2, fun hxC => hxC.2.2 _
    (special_coalition_blocks E hY h₁ (le_trans one_le_two hN2) hD0.ne' hx
    (hN₀ N (le_trans (le_max_left _ _) (le_max_left _ _))) fun h => ?_)⟩
  have := hgt h _ (inv_pos.mpr hD0) (lt_of_lt_of_le hDA (hAle h))
  rw [hu h]
  exact ⟨this.le, not_le.mpr this⟩

/-! ### Core allocations and supporting prices (p. 659) -/

/-- **Section 18.B** (MWG, p. 659). `Vᵢ = {xᵢ ∈ ℝ^L₊ : xᵢ ≻ᵢ x*ᵢ} ∪ {ωᵢ}`. -/
def coreVset {ι : Type*} (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) (i : ι) :
    Set (Fin L → ℝ) :=
  {z | z ∈ nonnegOrthant L ∧ Strict (E.pref i) z (x i)} ∪ {E.ω i}

/-- **Section 18.B** (MWG, p. 659). `V = ∑ᵢ Vᵢ`. -/
def coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  {z | ∃ v : ι → Fin L → ℝ, (∀ i, v i ∈ coreVset E x i) ∧ ∑ i, v i = z}

/-- **Section 18.B** (MWG, p. 659). `∑ᵢ ωᵢ ∈ V`. -/
theorem sum_endow_mem_coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L)
    (x : ι → Fin L → ℝ) : ∑ i, E.ω i ∈ coreV E x :=
  ⟨E.ω, fun _ => Or.inr rfl, rfl⟩

/-- **Section 18.B** (MWG, p. 659). In a pure exchange economy (with at least one good), if `x*`
has the core property then `∑ᵢ ωᵢ` is not in the interior of `V`: otherwise some `z ≪ ∑ᵢ ωᵢ` is in
`V`, and the consumers with `x'ᵢ ≠ ωᵢ` form a blocking coalition. -/
theorem core_not_mem_interior_coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hL : 0 < L) {x : ι → Fin L → ℝ} (hx : x ∈ E.core) :
    ∑ i, E.ω i ∉ interior (coreV E x) := by
  classical
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set z : Fin L → ℝ := ∑ i, E.ω i - fun _ => ε / 2 with hz
  have hzb : z ∈ Metric.ball (∑ i, E.ω i) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro l
    simp only [hz, Pi.sub_apply, Real.dist_eq, sub_sub_cancel_left, abs_neg]
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨v, hv, hvz⟩ := hball hzb
  set S := Finset.univ.filter (fun i => v i ≠ E.ω i) with hS
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => v i ≠ E.ω i) v
  have hrest : ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), v i =
      ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i :=
    Finset.sum_congr rfl fun i hi => not_not.mp (Finset.mem_filter.mp hi).2
  have hsplitω := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => v i ≠ E.ω i) E.ω
  apply hx.2 S
  refine ⟨?_, v, fun i hi => ?_, -(fun _ => ε / 2), ?_, ?_⟩
  · by_contra hSe
    rw [Finset.not_nonempty_iff_eq_empty] at hSe
    rw [← hS, hSe, Finset.sum_empty, zero_add, hrest] at hsplit
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i = ∑ i, E.ω i := by
      rw [← hsplitω, ← hS, hSe, Finset.sum_empty, zero_add]
    rw [h1, hvz] at hsplit
    have := congrFun hsplit ⟨0, hL⟩
    simp only [hz, Pi.sub_apply] at this
    linarith
  · rcases hv i with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp hi).2
  · rw [hY]
    intro l
    simp only [Pi.neg_apply]
    linarith
  · rw [← hS] at hsplit hsplitω
    rw [hrest, hvz] at hsplit
    have : ∑ i ∈ S, v i = z - ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i := by
      rw [← hsplit]; abel
    rw [this, hz, ← hsplitω]
    abel

/-- **Section 18.B** (MWG, p. 659), corrected. In a pure exchange economy with rational,
continuous, strongly monotone preferences and **strictly positive endowments**, if `x*` has the
core property and `p ≠ 0` supports `V` at `∑ᵢ ωᵢ` (`p·z ≥ p·∑ᵢ ωᵢ` on `V`), then `p` is a Walrasian
price vector for `x*`. The book's argument gives `p ≥ 0`, `p·x*ᵢ = p·ωᵢ` and `x'ᵢ ≻ᵢ x*ᵢ ⟹
p·x'ᵢ ≥ p·ωᵢ`; the final strengthening to `>` uses `p·ωᵢ > 0`, which needs an assumption such as
`ωᵢ ≫ 0` (`supporting_price_needs_positive_endowment`). -/
theorem supporting_price_isWalrasEqm {ι : Type*} [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (hω : ∀ i l, 0 < E.ω i l)
    {x : ι → Fin L → ℝ} (hx : x ∈ E.core) {p : Fin L → ℝ} (hp : p ≠ 0)
    (hsupp : ∀ z ∈ coreV E x, p ⬝ᵥ ∑ i, E.ω i ≤ p ⬝ᵥ z) : E.IsWalrasEqm x p := by
  classical
  obtain ⟨⟨hxX, y, hy, hsum⟩, -⟩ := hx
  rw [hY] at hy
  -- a strictly preferred bundle costs at least `p·ωᵢ`
  have hpref : ∀ i, ∀ x' ∈ nonnegOrthant L, Strict (E.pref i) x' (x i) →
      p ⬝ᵥ E.ω i ≤ p ⬝ᵥ x' := by
    intro i x' hx' hs
    have hmem : ∑ k, Function.update E.ω i x' k ∈ coreV E x := by
      refine ⟨Function.update E.ω i x', fun k => ?_, rfl⟩
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact Or.inl ⟨hx', hs⟩
      · rw [Function.update_of_ne hk]
        exact Or.inr rfl
    have h1 := hsupp _ hmem
    rw [dotProduct_sum, dotProduct_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ Function.update E.ω i x' k)
        (Finset.mem_univ i), Function.update_self] at h1
    have h2 : ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ Function.update E.ω i x' k =
        ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ E.ω k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    linarith
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hL : 0 < L := by
    by_contra hL0
    push Not at hL0
    apply hp
    funext l
    exact absurd l.2 (by omega)
  have hup : ∀ i, ∀ w : Fin L → ℝ, (∀ l, 0 ≤ w l) → w ≠ 0 →
      x i + w ∈ nonnegOrthant L ∧ Strict (E.pref i) (x i + w) (x i) := by
    intro i w hw hw0
    have hX : x i + w ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hxX i l, hw l]
    refine ⟨hX, hm i (x i) (hxX i) _ hX (fun l => ?_) fun heq => hw0 ?_⟩
    · simp only [Pi.add_apply]; linarith [hw l]
    · simpa using heq
  have hone : p ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ l, p l := by simp [dotProduct]
  -- `p ≥ 0`
  have hp0 : ∀ l, 0 ≤ p l := by
    intro l
    by_contra hneg
    push Not at hneg
    set c := p ⬝ᵥ x i₀ + ∑ k, p k - p ⬝ᵥ E.ω i₀ with hcdef
    set t := max 0 (c / -p l) + 1 with ht
    have ht0 : 0 ≤ t := by linarith [le_max_left 0 (c / -p l)]
    have ht2 : c / -p l ≤ t - 1 := by linarith [le_max_right 0 (c / -p l)]
    have hw : ∀ k, 0 ≤ ((fun _ => (1 : ℝ)) + Pi.single l t : Fin L → ℝ) k := by
      intro k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]
    have hw0 : ((fun _ => (1 : ℝ)) + Pi.single l t : Fin L → ℝ) ≠ 0 := by
      intro h
      have := congrFun h l
      simp at this
      linarith
    obtain ⟨hX, hs⟩ := hup i₀ _ hw hw0
    have := hpref i₀ _ hX hs
    rw [dotProduct_add, dotProduct_add, hone] at this
    have hdot : p ⬝ᵥ (Pi.single l t : Fin L → ℝ) = p l * t := by simp
    rw [hdot] at this
    rw [div_le_iff₀ (by linarith)] at ht2
    nlinarith
  -- `p·x*ᵢ ≥ p·ωᵢ` (bundles slightly above `x*ᵢ`)
  have hS0 : 0 ≤ ∑ l, p l := Finset.sum_nonneg fun l _ => hp0 l
  have hxω : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ x i := by
    intro i
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / (∑ k, p k + 1) with hε
    have hε0 : 0 < ε := div_pos hε' (by linarith)
    have hw0 : (fun _ => ε : Fin L → ℝ) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, hL⟩
      simp only [Pi.zero_apply] at this
      linarith
    obtain ⟨hX, hs⟩ := hup i _ (fun _ => hε0.le) hw0
    have := hpref i _ hX hs
    rw [dotProduct_add] at this
    have hdot : p ⬝ᵥ (fun _ => ε) = ε * ∑ k, p k := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hdot] at this
    have hεS : ε * ∑ k, p k ≤ ε' := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- budgets balance, `p·y = 0`
  have hpy : p ⬝ᵥ y ≤ 0 :=
    Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp0 l) (hy l)
  have hsump : ∑ i, (p ⬝ᵥ x i - p ⬝ᵥ E.ω i) = p ⬝ᵥ y := by
    rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsum, dotProduct_add]
    ring
  have hbal : ∀ i, p ⬝ᵥ x i - p ⬝ᵥ E.ω i = 0 := by
    have hle : ∑ i, (p ⬝ᵥ x i - p ⬝ᵥ E.ω i) ≤ 0 := by rw [hsump]; exact hpy
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hxω i)).mp
      (le_antisymm hle (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hxω i)))
    exact fun i => this i (Finset.mem_univ i)
  have hy0 : p ⬝ᵥ y = 0 := by rw [← hsump]; exact Finset.sum_eq_zero fun i _ => hbal i
  refine ⟨⟨y, hY ▸ hy, hsum, fun y' hy' => ?_⟩, fun i => ?_⟩
  · rw [hY] at hy'
    rw [hy0]
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp0 l) (hy' l)
  -- the cheaper point argument, with `p·ωᵢ > 0`
  have hpω : 0 < p ⬝ᵥ E.ω i := dotProduct_pos_of_nonneg_ne_zero hp0 hp (hω i)
  refine isMaximalFor_of_strict_gt (hr i) (hxX i) (by linarith [hbal i]) fun x' hx' hs => ?_
  rcases (hpref i x' hx' hs).lt_or_eq with h3 | h3
  · exact h3
  exfalso
  obtain ⟨m, hmpos⟩ : ∃ m, 0 < p m * x' m := by
    by_contra hall
    push Not at hall
    have : p ⬝ᵥ x' ≤ 0 := Finset.sum_nonpos fun m _ => hall m
    linarith
  have hxm : 0 < x' m := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (hp0 m) hle]
  have hpm : 0 < p m := by
    by_contra hle
    push Not at hle
    have : p m = 0 := le_antisymm hle (hp0 m)
    rw [this, zero_mul] at hmpos
    exact lt_irrefl 0 hmpos
  obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single (hr i) (hc i) hx' (hxX i) hs hxm
  have h4 := hpref i _ hmem hs'
  rw [dotProduct_sub, ← h3, dotProduct_single] at h4
  nlinarith

/-- **Section 18.B** (MWG, p. 659): the claim that a nonzero supporting price is Walrasian fails
without a positivity assumption on endowments. One consumer with `u = √x₁ + √x₂` and `ω = (1, 0)`:
`x* = ω` is in the core and `p = (0, 1) ≠ 0` supports `V` at `ω`, but `p` is not a Walrasian price
vector for `x*` (`(2, 0)` is affordable and better). -/
theorem supporting_price_needs_positive_endowment :
    (fun _ => ![1, 0]) ∈ dsEconomy.core ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      (∀ z ∈ coreV dsEconomy (fun _ => ![1, 0]),
        ![0, 1] ⬝ᵥ ∑ i, dsEconomy.ω i ≤ ![0, 1] ⬝ᵥ z) ∧
      ¬ dsEconomy.IsWalrasEqm (fun _ => ![1, 0]) ![0, 1] := by
  refine ⟨oneZero_mem_core dsEconomy (fun _ => rfl) (fun _ => rfl) rfl, fun h => ?_, ?_,
    fun h => not_maximal_one_zero _ (h.2 0)⟩
  · have := congrFun h 1
    simp at this
  · rintro z ⟨v, hv, rfl⟩
    rw [Fin.sum_univ_one, Fin.sum_univ_one, dot_two, dot_two]
    change (0 : ℝ) * 1 + 1 * 0 ≤ 0 * v 0 0 + 1 * v 0 1
    rcases hv 0 with h | h
    · linarith [h.1 1]
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      change (0 : ℝ) * 1 + 1 * 0 ≤ 0 * 1 + 1 * 0
      norm_num

/-- **Section 18.B** (MWG, p. 659). The sets `Vᵢ` need not be convex: in the example of p. 655
(`x*₁ = (1/3, 1/3)`, `ω₁ = (1, 0)`), `ω₁` and `(1, 1/4)` belong to `V₁` but `(1, 1/100)` does
not. -/
theorem coreVset_not_convex :
    ¬ Convex ℝ (coreVset (sqrtEconomy exampleEndow) exampleAlloc 0) := by
  intro hconv
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ coreVset (sqrtEconomy exampleEndow) exampleAlloc 0 :=
    Or.inr rfl
  have h2 : (![1, 1 / 4] : Fin 2 → ℝ) ∈ coreVset (sqrtEconomy exampleEndow) exampleAlloc 0 := by
    refine Or.inl ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    have hlt : sqrtU ![1 / 3, 1 / 3] < sqrtU ![1, 1 / 4] := by
      rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]
      have : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 4) := Real.le_sqrt_of_sq_le (by norm_num)
      linarith [two_sqrt_third_lt]
    exact ⟨hlt.le, not_le.mpr hlt⟩
  have h3 := hconv h1 h2 (a := 24 / 25) (b := 1 / 25) (by norm_num) (by norm_num) (by norm_num)
  have heq : (24 / 25 : ℝ) • (![1, 0] : Fin 2 → ℝ) + (1 / 25 : ℝ) • ![1, 1 / 4] =
      ![1, 1 / 100] := by
    funext l
    fin_cases l <;> simp <;> norm_num
  rw [heq] at h3
  rcases h3 with h | h
  · have hlt : sqrtU ![1, 1 / 100] < sqrtU ![1 / 3, 1 / 3] := by
      rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]
      have ha : Real.sqrt (1 / 100) < 11 / 100 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      have hb : (111 : ℝ) / 200 < Real.sqrt (1 / 3) := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    exact h.2.2 hlt.le
  · have := congrFun (Set.mem_singleton_iff.mp h) 1
    simp [sqrtEconomy, exampleEndow] at this

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The market for shoes (MWG Section 18.B, Exercise 18.B.5, p. 685)

`2I + 1` consumers `i : Fin (2I + 1)`; consumers `i < I` own one right shoe each, the other
`I + 1` own one left shoe each. Shoes are indivisible (quantities in `ℕ`) and every consumer has
utility `min {R, L}`. Allocations are feasible with free disposal (`∑ Rᵢ ≤ I`, `∑ Lᵢ ≤ I + 1`), as
with `Y = -ℝ²₊` in Section 18.B.

* (a) `shoe_paretoOptimal_iff`: an allocation is Pareto optimal iff it forms `I` pairs in total,
  `∑ᵢ min {Rᵢ, Lᵢ} = I`. A matched allocation (`Rᵢ = Lᵢ` for all `i`) that uses all right shoes is
  Pareto optimal (`exercise_18_B_5a`). Departures: a matched allocation that throws pairs away
  is not Pareto optimal (`shoe_matched_not_paretoOptimal`), and the converse holds only up to the
  disposal of unusable left shoes: a Pareto optimum has `Rᵢ ≤ Lᵢ` and `∑ Rᵢ = I`, and discarding
  the extra left shoes gives a matched Pareto optimum with the same utilities
  (`exercise_18_B_5a_converse`), but need not itself be matched (`shoe_paretoOptimal_not_matched`).
* (b) With blocking by weak dominance, the core consists exactly of the feasible allocations in
  which every owner of a right shoe gets one pair and the owners of left shoes get nothing
  (`exercise_18_B_5b`).
* (c) Walrasian equilibria (`shoeWalras`; prices `p ≥ 0`, a good may be disposed of only at price
  `0`, as profit maximization on `-ℝ²₊` requires): `p_R > 0` in every equilibrium
  (`shoeWalras_pR_pos`); with `p_L = 0` the owners of right shoes get one pair each and the others
  nothing; with `p_L > 0` nobody can afford a pair and every utility is `0`
  (`exercise_18_B_5c`); both kinds exist (`shoeWalras_pairs`, `shoeWalras_endowment`).
* (d) `exercise_18_B_5d`: the core is exactly the set of Walrasian allocations with `p_L = 0`: the
  single extra left shoe drives the price of left shoes to zero and gives the owners of right
  shoes all the surplus, even with few consumers. Because of indivisibility (no local
  nonsatiation) there are also Walrasian equilibria with `p_L > 0` (no trade) which are neither
  Pareto optimal nor in the core.
-/

namespace MWG.CoreFoundations

variable {I : ℕ}

/-- **Exercise 18.B.5** (MWG, p. 685). The utility `min {Rᵢ, Lᵢ}` of consumer `i` at the
allocation `a` (`a i = (Rᵢ, Lᵢ)`). -/
def shoeU (a : Fin (2 * I + 1) → ℕ × ℕ) (i : Fin (2 * I + 1)) : ℕ := min (a i).1 (a i).2

/-- **Exercise 18.B.5** (MWG, p. 685). Feasibility with free disposal: at most `I` right shoes and
`I + 1` left shoes are consumed. -/
def shoeFeasible (I : ℕ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  ∑ i, (a i).1 ≤ I ∧ ∑ i, (a i).2 ≤ I + 1

/-- **Exercise 18.B.5(a)** (MWG, p. 685). Pareto optimality. -/
def shoeParetoOptimal (I : ℕ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  shoeFeasible I a ∧ ¬ ∃ a', shoeFeasible I a' ∧ (∀ i, shoeU a i ≤ shoeU a' i) ∧
    ∃ i, shoeU a i < shoeU a' i

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A matched allocation: every consumer gets as many right
as left shoes. -/
def shoeMatched (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop := ∀ i, (a i).1 = (a i).2

/-- **Exercise 18.B.5(b)** (MWG, p. 685). Blocking with weak dominance: with its own shoes (the
right shoes of its members `i < I` and the left shoes of the others) the coalition `S` can make
every member at least as well off and some member strictly better off. -/
def shoeBlocks (I : ℕ) (S : Finset (Fin (2 * I + 1))) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  ∃ a' : Fin (2 * I + 1) → ℕ × ℕ,
    ∑ i ∈ S, (a' i).1 ≤ (S.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card ∧
    ∑ i ∈ S, (a' i).2 ≤ (S.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I).card ∧
    (∀ i ∈ S, shoeU a i ≤ shoeU a' i) ∧ ∃ i ∈ S, shoeU a i < shoeU a' i

/-- **Exercise 18.B.5(b)** (MWG, p. 685). The core (with weak-dominance blocking). -/
def shoeCore (I : ℕ) : Set (Fin (2 * I + 1) → ℕ × ℕ) :=
  {a | shoeFeasible I a ∧ ∀ S, ¬ shoeBlocks I S a}

/-- The wealth of consumer `i` at prices `(p_R, p_L)`: the value of her shoe. -/
noncomputable def shoeWealth (I : ℕ) (pR pL : ℝ) (i : Fin (2 * I + 1)) : ℝ :=
  if (i : ℕ) < I then pR else pL

/-- **Exercise 18.B.5(c)** (MWG, p. 685). A Walrasian equilibrium with prices `(p_R, p_L)`:
`p ≥ 0`, feasibility, a good with positive price is not disposed of (profit maximization on the
free disposal technology), and every consumer's bundle is affordable and maximizes `min {R, L}`
over the affordable bundles of `ℕ²`. -/
def shoeWalras (I : ℕ) (pR pL : ℝ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  0 ≤ pR ∧ 0 ≤ pL ∧ shoeFeasible I a ∧ (0 < pR → ∑ i, (a i).1 = I) ∧
    (0 < pL → ∑ i, (a i).2 = I + 1) ∧
    ∀ i, pR * (a i).1 + pL * (a i).2 ≤ shoeWealth I pR pL i ∧
      ∀ r l : ℕ, pR * r + pL * l ≤ shoeWealth I pR pL i → min r l ≤ shoeU a i

/-- `I` consumers own right shoes. -/
theorem shoe_card_right (I : ℕ) :
    (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card = I := by
  rw [Fin.card_filter_val_lt]
  omega

/-- `I + 1` consumers own left shoes. -/
theorem shoe_card_left (I : ℕ) :
    (Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I).card = I + 1 := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i : Fin (2 * I + 1) => (i : ℕ) < I)
  rw [shoe_card_right, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- Utilities sum to at most the number of right shoes used. -/
theorem shoe_sum_u_le {a : Fin (2 * I + 1) → ℕ × ℕ} (S : Finset (Fin (2 * I + 1))) :
    ∑ i ∈ S, shoeU a i ≤ ∑ i ∈ S, (a i).1 :=
  Finset.sum_le_sum fun _ _ => min_le_left _ _

/-- If `fᵢ ≥ 1` on `s` and `∑_s f ≤ #s`, then `f = 1` on `s`. -/
theorem shoe_eq_one_of_sum_le {s : Finset (Fin (2 * I + 1))} {f : Fin (2 * I + 1) → ℕ}
    (h1 : ∀ i ∈ s, 1 ≤ f i) (hs : ∑ i ∈ s, f i ≤ s.card) : ∀ i ∈ s, f i = 1 := by
  have hc : s.card = ∑ i ∈ s, 1 := by simp
  have heq : ∑ i ∈ s, 1 = ∑ i ∈ s, f i := le_antisymm (Finset.sum_le_sum h1) (hc ▸ hs)
  intro i hi
  exact ((Finset.sum_eq_sum_iff_of_le h1).mp heq i hi).symm

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A feasible allocation is Pareto optimal iff it forms `I`
pairs: `∑ᵢ min {Rᵢ, Lᵢ} = I`. -/
theorem shoe_paretoOptimal_iff (a : Fin (2 * I + 1) → ℕ × ℕ) :
    shoeParetoOptimal I a ↔ shoeFeasible I a ∧ ∑ i, shoeU a i = I := by
  classical
  constructor
  · rintro ⟨hfe, hpo⟩
    refine ⟨hfe, le_antisymm ((shoe_sum_u_le _).trans hfe.1) ?_⟩
    by_contra hlt
    push Not at hlt
    -- give the unused pairs to consumer `0`
    set k := I - ∑ i, shoeU a i with hk
    set a' : Fin (2 * I + 1) → ℕ × ℕ := fun i =>
      (shoeU a i + if i = 0 then k else 0, shoeU a i + if i = 0 then k else 0) with ha'
    have hu' : ∀ i, shoeU a' i = shoeU a i + if i = 0 then k else 0 := fun i => by
      simp [shoeU, ha']
    have hsum : ∑ i, (shoeU a i + if i = 0 then k else 0) = I := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (2 * I + 1))]
      simp only [Finset.mem_univ, ↓reduceIte]
      omega
    apply hpo
    refine ⟨a', ⟨?_, ?_⟩, fun i => ?_, 0, ?_⟩
    · simp only [ha']; omega
    · simp only [ha']; omega
    · rw [hu']; omega
    · rw [hu']; simp only [↓reduceIte]; omega
  · rintro ⟨hfe, hsum⟩
    refine ⟨hfe, ?_⟩
    rintro ⟨a', hfe', hle, i, hi⟩
    have := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
    have := (shoe_sum_u_le (a := a') Finset.univ).trans hfe'.1
    omega

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A matched allocation that uses all `I` right shoes is
Pareto optimal. -/
theorem exercise_18_B_5a (a : Fin (2 * I + 1) → ℕ × ℕ) (hfe : shoeFeasible I a)
    (hm : shoeMatched a) (hall : ∑ i, (a i).1 = I) : shoeParetoOptimal I a := by
  refine (shoe_paretoOptimal_iff a).2 ⟨hfe, ?_⟩
  exact (Finset.sum_congr rfl fun i _ => by simp [shoeU, hm i]).trans hall

/-- **Exercise 18.B.5(a)** (MWG, p. 685): a matched allocation that discards pairs (here,
nobody gets any shoe) is not Pareto optimal when `I ≥ 1`. -/
theorem shoe_matched_not_paretoOptimal (hI : 1 ≤ I) :
    shoeMatched (fun _ : Fin (2 * I + 1) => ((0 : ℕ), (0 : ℕ))) ∧
      shoeFeasible I (fun _ => (0, 0)) ∧ ¬ shoeParetoOptimal I (fun _ => (0, 0)) := by
  refine ⟨fun _ => rfl, ⟨by simp, by simp⟩, fun h => ?_⟩
  have := ((shoe_paretoOptimal_iff _).1 h).2
  simp [shoeU] at this
  omega

/-- **Exercise 18.B.5(a)** (MWG, p. 685), the converse up to disposal: a Pareto optimum uses all
right shoes, gives no one more right than left shoes, and discarding the unusable left shoes
(`Lᵢ ↦ Rᵢ`) gives a matched Pareto optimum with the same utilities. -/
theorem exercise_18_B_5a_converse {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeParetoOptimal I a) :
    (∀ i, (a i).1 ≤ (a i).2) ∧ ∑ i, (a i).1 = I ∧
      shoeMatched (fun i => ((a i).1, (a i).1)) ∧
      shoeParetoOptimal I (fun i => ((a i).1, (a i).1)) ∧
      ∀ i, shoeU (fun i => ((a i).1, (a i).1)) i = shoeU a i := by
  obtain ⟨hfe, hsum⟩ := (shoe_paretoOptimal_iff a).1 h
  have hR : ∑ i, (a i).1 = I := by
    have := shoe_sum_u_le (a := a) Finset.univ
    have := hfe.1
    omega
  have heq : ∀ i, shoeU a i = (a i).1 := by
    have : ∑ i, shoeU a i = ∑ i, (a i).1 := by rw [hsum, hR]
    intro i
    exact (Finset.sum_eq_sum_iff_of_le fun j _ => min_le_left _ _).mp this i (Finset.mem_univ i)
  have hle : ∀ i, (a i).1 ≤ (a i).2 := fun i => by
    have := heq i
    simp only [shoeU] at this
    omega
  have hu : ∀ i, shoeU (fun i => ((a i).1, (a i).1)) i = shoeU a i := fun i => by
    simp only [shoeU, min_self]
    exact (min_eq_left (hle i)).symm
  refine ⟨hle, hR, fun _ => rfl, (shoe_paretoOptimal_iff _).2 ⟨⟨?_, ?_⟩, ?_⟩, hu⟩
  · simpa using hfe.1
  · simp only
    omega
  · simp only [hu]
    exact hsum

/-- With `I = 1`: consumer 1 holds one right and two left shoes, the others nothing. -/
def shoeExample : Fin (2 * 1 + 1) → ℕ × ℕ := ![(1, 2), (0, 0), (0, 0)]

/-- **Exercise 18.B.5(a)** (MWG, p. 685): a Pareto optimum need not be matched. With `I = 1`,
consumer 1 holding one right and two left shoes is Pareto optimal. -/
theorem shoe_paretoOptimal_not_matched :
    shoeParetoOptimal 1 shoeExample ∧ ¬ shoeMatched shoeExample := by
  refine ⟨(shoe_paretoOptimal_iff _).2 ⟨⟨by decide, by decide⟩, by decide⟩, fun h => ?_⟩
  have := h 0
  simp [shoeExample] at this

/-- **Exercise 18.B.5(b)** (MWG, p. 685). With blocking by weak dominance, the core consists of
the feasible allocations in which every owner of a right shoe gets exactly one pair (utility `1`)
and every owner of a left shoe gets utility `0`. -/
theorem exercise_18_B_5b (a : Fin (2 * I + 1) → ℕ × ℕ) :
    a ∈ shoeCore I ↔
      shoeFeasible I a ∧ ∀ i : Fin (2 * I + 1), shoeU a i = if (i : ℕ) < I then 1 else 0 := by
  classical
  set R := Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I with hRdef
  set Lf := Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I with hLdef
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (2 * I + 1) => (i : ℕ) < I) (shoeU a)
  constructor
  · rintro ⟨hfe, hcore⟩
    -- the core is Pareto optimal (the grand coalition blocks by weak dominance)
    have hpo : shoeParetoOptimal I a := by
      refine ⟨hfe, fun ⟨a', hfe', hle, i, hi⟩ => hcore Finset.univ ⟨a', ?_, ?_, fun j _ => hle j,
        i, Finset.mem_univ i, hi⟩⟩
      · rw [shoe_card_right]; exact hfe'.1
      · rw [shoe_card_left]; exact hfe'.2
    have hsum := ((shoe_paretoOptimal_iff a).1 hpo).2
    -- every owner of a right shoe has a pair
    have hright : ∀ i ∈ R, 1 ≤ shoeU a i := by
      intro i hi
      by_contra h0
      have hi0 : shoeU a i = 0 := by omega
      have hiR : (i : ℕ) < I := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj, hj0⟩ : ∃ j ∈ Lf, shoeU a j = 0 := by
        by_contra hall
        push Not at hall
        have h1 : ∑ j ∈ Lf, 1 ≤ ∑ j ∈ Lf, shoeU a j :=
          Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (hall j hj)
        rw [Finset.sum_const, smul_eq_mul, mul_one, hLdef, shoe_card_left] at h1
        omega
      have hjL : ¬ (j : ℕ) < I := (Finset.mem_filter.mp hj).2
      have hij : i ≠ j := fun h => hjL (h ▸ hiR)
      refine hcore {i, j} ⟨fun k => if k = i then (1, 1) else (0, 0), ?_, ?_, fun k hk => ?_,
        i, Finset.mem_insert_self i {j}, ?_⟩
      · rw [Finset.sum_pair hij, Finset.filter_insert, Finset.filter_singleton]
        simp [hiR, hjL, hij.symm]
      · rw [Finset.sum_pair hij, Finset.filter_insert, Finset.filter_singleton]
        simp [hiR, hjL, hij.symm]
      · rcases Finset.mem_insert.mp hk with rfl | hk
        · rw [hi0]; exact Nat.zero_le _
        · rw [Finset.mem_singleton] at hk
          subst hk
          rw [hj0]; exact Nat.zero_le _
      · rw [hi0]; simp [shoeU]
    have hRsum : ∑ i ∈ R, shoeU a i ≤ R.card := by
      rw [hRdef, shoe_card_right]
      omega
    have hone := shoe_eq_one_of_sum_le hright hRsum
    have hRI : ∑ i ∈ R, shoeU a i = I := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, hRdef,
        shoe_card_right]
    have hL0 : ∑ i ∈ Lf, shoeU a i = 0 := by
      simp only [← hRdef, ← hLdef] at hsplit
      omega
    refine ⟨hfe, fun i => ?_⟩
    by_cases hi : (i : ℕ) < I
    · simp only [hi, ↓reduceIte]
      exact hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    · simp only [hi, ↓reduceIte]
      exact (Finset.sum_eq_zero_iff.mp hL0) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · rintro ⟨hfe, hu⟩
    refine ⟨hfe, fun S ⟨a', hR', _, hle, i, hiS, hi⟩ => ?_⟩
    have hlt := Finset.sum_lt_sum hle ⟨i, hiS, hi⟩
    have hSu : ∑ j ∈ S, shoeU a j = (S.filter fun j : Fin (2 * I + 1) => (j : ℕ) < I).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun j _ => hu j
    have := (shoe_sum_u_le (a := a') S).trans hR'
    omega

/-- **Exercise 18.B.5(c)** (MWG, p. 685). In every Walrasian equilibrium `p_R > 0`: if right
shoes were free, each of the `I + 1` owners of left shoes could afford a pair, and only `I` right
shoes exist. -/
theorem shoeWalras_pR_pos {pR pL : ℝ} {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeWalras I pR pL a) :
    0 < pR := by
  classical
  obtain ⟨hpR, hpL, hfe, -, -, hopt⟩ := h
  rcases hpR.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hone : ∀ j ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I,
      1 ≤ (a j).1 := by
    intro j hj
    have hjL := (Finset.mem_filter.mp hj).2
    have := (hopt j).2 1 1 (by simp [shoeWealth, hjL, ← heq])
    simp only [shoeU] at this
    omega
  have h1 := Finset.sum_le_sum hone
  rw [Finset.sum_const, smul_eq_mul, mul_one, shoe_card_left] at h1
  have h2 := Finset.sum_le_sum_of_subset (f := fun i => (a i).1)
    (Finset.filter_subset (fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I) Finset.univ)
  have := hfe.1
  omega

/-- **Exercise 18.B.5(c)** (MWG, p. 685). The Walrasian equilibria: either `p_L = 0` and every
owner of a right shoe gets one pair while the owners of left shoes get nothing, or `p_L > 0` and
nobody can afford a pair (every utility is `0`). In both cases `p_R > 0`. -/
theorem exercise_18_B_5c {pR pL : ℝ} {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeWalras I pR pL a) :
    0 < pR ∧ ((pL = 0 ∧ ∀ i : Fin (2 * I + 1), shoeU a i = if (i : ℕ) < I then 1 else 0) ∨
      (0 < pL ∧ ∀ i : Fin (2 * I + 1), shoeU a i = 0)) := by
  classical
  have hpR := shoeWalras_pR_pos h
  obtain ⟨-, hpL, hfe, -, -, hopt⟩ := h
  refine ⟨hpR, ?_⟩
  rcases hpL.lt_or_eq with hlt | heq
  · -- a pair costs `p_R + p_L`, more than anyone's wealth
    refine Or.inr ⟨hlt, fun i => ?_⟩
    by_contra hne
    have h1 : 1 ≤ (a i).1 := by simp only [shoeU] at hne; omega
    have h2 : 1 ≤ (a i).2 := by simp only [shoeU] at hne; omega
    have hb := (hopt i).1
    have h1' : (1 : ℝ) ≤ (a i).1 := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ (a i).2 := by exact_mod_cast h2
    unfold shoeWealth at hb
    split_ifs at hb <;> nlinarith
  · refine Or.inl ⟨heq.symm, ?_⟩
    have hleft : ∀ i : Fin (2 * I + 1), ¬ (i : ℕ) < I → shoeU a i = 0 := by
      intro i hi
      have hb := (hopt i).1
      simp only [shoeWealth, hi, ↓reduceIte, ← heq, zero_mul, add_zero] at hb
      have : (a i).1 = 0 := by
        by_contra h0
        have : (1 : ℝ) ≤ (a i).1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        nlinarith
      simp [shoeU, this]
    have hright : ∀ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I,
        1 ≤ shoeU a i := by
      intro i hi
      have hiR := (Finset.mem_filter.mp hi).2
      exact (hopt i).2 1 1 (by simp [shoeWealth, hiR, ← heq])
    have hRsum : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I, shoeU a i ≤
        (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card := by
      rw [shoe_card_right]
      exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
        ((shoe_sum_u_le _).trans hfe.1)
    have hone := shoe_eq_one_of_sum_le hright hRsum
    intro i
    by_cases hi : (i : ℕ) < I
    · simp only [hi, ↓reduceIte]
      exact hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    · simp only [hi, ↓reduceIte]
      exact hleft i hi

/-- The allocation in which every owner of a right shoe gets one pair. -/
def shoePairs (I : ℕ) : Fin (2 * I + 1) → ℕ × ℕ := fun i => if (i : ℕ) < I then (1, 1) else (0, 0)

/-- The endowment allocation (no trade). -/
def shoeEndow (I : ℕ) : Fin (2 * I + 1) → ℕ × ℕ := fun i => if (i : ℕ) < I then (1, 0) else (0, 1)

/-- `∑ᵢ [i < I] = I` on `Fin (2I + 1)`. -/
theorem shoe_sum_ite_right (I : ℕ) :
    ∑ i : Fin (2 * I + 1), (if (i : ℕ) < I then 1 else 0) = I := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
    shoe_card_right]

/-- `∑ᵢ [i ≥ I] = I + 1` on `Fin (2I + 1)`. -/
theorem shoe_sum_ite_left (I : ℕ) :
    ∑ i : Fin (2 * I + 1), (if (i : ℕ) < I then 0 else 1) = I + 1 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    shoe_card_left]

/-- **Exercise 18.B.5(c)** (MWG, p. 685). For every `p_R > 0`, the prices `(p_R, 0)` with one pair
for every owner of a right shoe form a Walrasian equilibrium. -/
theorem shoeWalras_pairs {pR : ℝ} (hpR : 0 < pR) : shoeWalras I pR 0 (shoePairs I) := by
  have hR : ∑ i, (shoePairs I i).1 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoePairs
    split_ifs <;> rfl
  have hL : ∑ i, (shoePairs I i).2 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoePairs
    split_ifs <;> rfl
  refine ⟨hpR.le, le_rfl, ⟨hR.le, by omega⟩, fun _ => hR, fun h => absurd h (lt_irrefl 0),
    fun i => ⟨?_, fun r l hb => ?_⟩⟩
  · unfold shoePairs shoeWealth
    split_ifs <;> simp
  · unfold shoeWealth at hb
    unfold shoeU shoePairs
    split_ifs at hb ⊢ with hi
    · simp only [zero_mul, add_zero] at hb
      have : (r : ℝ) ≤ 1 := by nlinarith
      have : r ≤ 1 := by exact_mod_cast this
      simp only
      omega
    · simp only [zero_mul, add_zero] at hb
      have : (r : ℝ) ≤ 0 := by nlinarith
      have : r = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg r)
      simp [this]

/-- **Exercise 18.B.5(c)** (MWG, p. 685). For all `p_R, p_L > 0` no consumer can afford a pair, and
the endowment allocation (no trade) is a Walrasian equilibrium. -/
theorem shoeWalras_endowment {pR pL : ℝ} (hpR : 0 < pR) (hpL : 0 < pL) :
    shoeWalras I pR pL (shoeEndow I) := by
  have hR : ∑ i, (shoeEndow I i).1 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoeEndow
    split_ifs <;> rfl
  have hL : ∑ i, (shoeEndow I i).2 = I + 1 := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_left I)
    unfold shoeEndow
    split_ifs <;> rfl
  refine ⟨hpR.le, hpL.le, ⟨hR.le, hL.le⟩, fun _ => hR, fun _ => hL, fun i => ⟨?_, fun r l hb => ?_⟩⟩
  · unfold shoeEndow shoeWealth
    split_ifs <;> simp
  · by_contra hne
    have h1 : 1 ≤ r := by omega
    have h2 : 1 ≤ l := by omega
    have h1' : (1 : ℝ) ≤ r := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ l := by exact_mod_cast h2
    unfold shoeWealth at hb
    split_ifs at hb <;> nlinarith

/-- **Exercise 18.B.5(d)** (MWG, p. 685). The core (weak-dominance blocking) is exactly the set of
Walrasian equilibrium allocations with `p_L = 0` (`p_R > 0`): the owners of right shoes, the
short side of the market, get all the surplus. With `I ≥ 1` there are also Walrasian equilibria
with `p_L > 0` (no trade) that are neither Pareto optimal nor in the core (indivisibility: local
nonsatiation fails). -/
theorem exercise_18_B_5d :
    shoeCore I = {a | ∃ pR : ℝ, 0 < pR ∧ shoeWalras I pR 0 a} ∧
      (1 ≤ I → shoeWalras I 1 1 (shoeEndow I) ∧ shoeEndow I ∉ shoeCore I ∧
        ¬ shoeParetoOptimal I (shoeEndow I)) := by
  classical
  refine ⟨Set.ext fun a => ⟨fun ha => ?_, fun ⟨pR, hpR, h⟩ => ?_⟩, fun hI => ?_⟩
  · -- a core allocation: every owner of a right shoe has exactly one right shoe
    obtain ⟨hfe, hu⟩ := (exercise_18_B_5b a).1 ha
    have hR1 : ∀ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I,
        1 ≤ (a i).1 := by
      intro i hi
      have := hu i
      simp only [(Finset.mem_filter.mp hi).2, ↓reduceIte, shoeU] at this
      omega
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * I + 1) => (i : ℕ) < I) (fun i => (a i).1)
    have hge := Finset.sum_le_sum hR1
    rw [Finset.sum_const, smul_eq_mul, mul_one, shoe_card_right] at hge
    have hRle : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I, (a i).1 ≤
        (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card := by
      rw [shoe_card_right]; have := hfe.1; omega
    have hone := shoe_eq_one_of_sum_le hR1 hRle
    have hL0 : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I, (a i).1 = 0 := by
      have := hfe.1; omega
    refine ⟨1, one_pos, le_of_lt one_pos, le_rfl, hfe, fun _ => by have := hfe.1; omega,
      fun h => absurd h (lt_irrefl 0), fun i => ⟨?_, fun r l hb => ?_⟩⟩
    · unfold shoeWealth
      by_cases hi : (i : ℕ) < I
      · simp only [hi, ↓reduceIte, zero_mul, add_zero, one_mul]
        exact_mod_cast (hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)).le
      · simp only [hi, ↓reduceIte, zero_mul, add_zero, one_mul]
        have := (Finset.sum_eq_zero_iff.mp hL0) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        simp [this]
    · rw [hu i]
      unfold shoeWealth at hb
      simp only [zero_mul, add_zero, one_mul] at hb
      split_ifs at hb ⊢
      · have : r ≤ 1 := by exact_mod_cast hb
        omega
      · have : r = 0 := by exact_mod_cast le_antisymm hb (Nat.cast_nonneg r)
        simp [this]
  · obtain ⟨-, hc⟩ := exercise_18_B_5c h
    rcases hc with ⟨-, hu⟩ | ⟨hlt, -⟩
    · exact (exercise_18_B_5b a).2 ⟨h.2.2.1, hu⟩
    · exact absurd hlt (lt_irrefl 0)
  · have hw := shoeWalras_endowment (I := I) one_pos one_pos
    have h0 : shoeU (shoeEndow I) ⟨0, by omega⟩ = 0 := by
      simp [shoeU, shoeEndow, show (0 : ℕ) < I by omega]
    refine ⟨hw, fun hc => ?_, fun hpo => ?_⟩
    · have := ((exercise_18_B_5b _).1 hc).2 ⟨0, by omega⟩
      rw [h0] at this
      simp [show (0 : ℕ) < I by omega] at this
    · have hsum := ((shoe_paretoOptimal_iff _).1 hpo).2
      have : ∀ i, shoeU (shoeEndow I) i = 0 := fun i => by
        unfold shoeU shoeEndow; split_ifs <;> simp
      simp only [this, Finset.sum_const_zero] at hsum
      omega

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Noncooperative foundations of Walrasian equilibria (MWG Section 18.C, pp. 660-665)

* The abstract trading model (p. 660, `TradingModel`, requirements `TradingModel.IsValid`),
  **Definition 18.C.1** (`TradingModel.IsTradingEqm`, `definition_18_C_1`), the notation of
  **footnote 7** (`footnote_18_7`), the effective budget set `Bᵢ(a)` (p. 661,
  `TradingModel.effBudget`; equilibrium bundles are maximal there,
  `TradingModel.isTradingEqm_maximal_effBudget`) and **footnote 8** (`footnote_18_8`: if the
  price does not react to `a'ᵢ`, achievable net trades lie in the hyperplane `p̄·z = 0` and, for
  `p̄ ≥ 0`, `Bᵢ(a)` is inside the Walrasian budget `B(p̄, p̄·ωᵢ)`).
* p. 661, insensitivity to own actions (`price_insensitivity`): if `p(a) = φ((1/r) ∑ᵢ aᵢ)` with
  `φ` continuous and the actions in a bounded set of `ℝ^m`, a unilateral deviation moves the price
  by less than any `ε > 0` once `r` is large, uniformly. (Actions are taken in `ℝ^m`.)
* **Example 18.C.1** (pp. 661-663, footnotes 10, 12): the Cournot model as a trading model
  (`cournotModel`), the Walrasian benchmark (`example_18_C_1_walras`), the Cournot equilibria
  bounded away from the Walrasian outcome (`example_18_C_1`), why they are not Walrasian
  (`example_18_C_1_not_walrasian`) and a concrete selection satisfying all hypotheses
  (`example_18_C_1_instance`). "Very elastic" is made precise as: `p` nonincreasing and
  `s p(s)` nondecreasing on `[0, b']` (both as drawn in Figure 18.C.3).
* **Example 18.C.2** (p. 663, footnote 13): the complements model (`complementsModel`), the
  null-production equilibrium (`example_18_C_2`; it needs only `ψ(·,0) ≡ 0 ≡ ψ(0,·)`), and for
  `ψ = √(x₁x₂)` the price discontinuity at the origin (`footnote_18_13_prices`,
  `footnote_18_13_discontinuous`), the failure of differentiability
  (`footnote_18_13_not_differentiable`), homotheticity, nonlinearity and concavity
  (`footnote_18_13_psi`, `footnote_18_13_psi_concave`). As printed, `p(q₁, q₂) ≫ 0` cannot hold
  on the axes when `ψ(·, 0) ≡ 0` (`partialOne_axis_eq_zero`).
* **Example 18.C.3** (pp. 663-665, footnote 14): trading posts with the price (18.C.1)
  (`tpPrice`) and the share form of the trading rule (`tpGood`, `tpMoney`), which is the book's
  `a''/p - a'` with `p·g = 0` and clearing when both sides are active (`example_18_C_3_rule`);
  continuity of (18.C.1) where goods are offered (`example_18_C_3_continuous`) and the
  impossibility of a continuous price at the inactive post
  (`example_18_C_3_no_continuous_price`); footnote 14 (`footnote_18_14`); an inactive post
  preserves equilibrium (`example_18_C_3_inactive_post`, for nondecreasing utilities); a
  consumer without money cannot buy goods (`example_18_C_3_no_money`).
* **Exercise 18.C.1** (`L = 2`): with the others active on both sides (`A', A'' > 0`) every
  bid, one- or two-sided, yields the net trades `((bA' - sA'')/(b + A''), (sA'' - bA')/(s + A'))`
  (`tp_outcome`, one-sided cases `exercise_18_C_1_one_sided`), all on the curve
  `m = φ(g) = -gA''/(A' - g)` (`tp_outcome_on_frontier`); the achievable `g` form
  `[-ω₁, ω₂A'/(ω₂ + A'')]` (`tp_reachable`); the effective budget set is the region under `φ`
  (`exercise_18_C_1_eq`), convex (`exercise_18_C_1_convex`), with upper boundary the graph of
  the strictly concave `φ` (`tpFrontier_strictConcaveOn`, `exercise_18_C_1_boundary`: no
  straight segments).

Verbal or graphical: Figures 18.C.1-18.C.4, footnote 9 (references), footnote 11 (money is a
Giffen good in the example), the quasilinear partial-equilibrium remark on p. 662, the
individual-spanning discussion (p. 661) and the cash-in-advance remark (p. 665).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.WelfareTheorems

/-! ### The abstract trading model (p. 660) -/

/-- **Section 18.C** (MWG, p. 660). The abstract model of price-mediated competition: agents
`i : ι`, a set `P ⊆ ℝ^L` of price vectors, action sets `Aᵢ` of market actions (elements of
`Act`), endowments `ωᵢ`, a trading rule `g(aᵢ; p) ∈ ℝ^L`, a market clearing process `a ↦ p(a)`
and utilities `uᵢ`, evaluated at `g(aᵢ; p(a)) + ωᵢ`. -/
structure TradingModel (ι Act : Type*) (L : ℕ) where
  /-- The set `P` of possible price vectors. -/
  P : Set (Fin L → ℝ)
  /-- The action sets `Aᵢ ⊆ A`. -/
  A : ι → Set Act
  /-- The endowments `ωᵢ`. -/
  ω : ι → Fin L → ℝ
  /-- The trading rule `g(aᵢ; p)`. -/
  g : Act → (Fin L → ℝ) → Fin L → ℝ
  /-- The market clearing price `p(a)`. -/
  price : (ι → Act) → Fin L → ℝ
  /-- The utility functions `uᵢ`. -/
  u : ι → (Fin L → ℝ) → ℝ

variable {ι Act : Type*} {L : ℕ}

/-- **Section 18.C** (MWG, p. 660). The requirements of the abstract model: the trading rule
satisfies `p·g(a; p) = 0` for every action and every `p ∈ P`, and the clearing price of every
profile of feasible actions lies in `P`. -/
def TradingModel.IsValid (M : TradingModel ι Act L) : Prop :=
  (∀ a, ∀ p ∈ M.P, p ⬝ᵥ M.g a p = 0) ∧ ∀ a : ι → Act, (∀ i, a i ∈ M.A i) → M.price a ∈ M.P

/-- The utility agent `i` obtains at the action profile `a`: `uᵢ(g(aᵢ; p(a)) + ωᵢ)`. -/
def TradingModel.payoff (M : TradingModel ι Act L) (a : ι → Act) (i : ι) : ℝ :=
  M.u i (M.g (a i) (M.price a) + M.ω i)

/-- **Definition 18.C.1** (MWG, p. 660). `a*` is a trading equilibrium: `a*ᵢ ∈ Aᵢ` for every
`i`, and no agent gains by a unilateral deviation,
`uᵢ(g(a*ᵢ; p(a*)) + ωᵢ) ≥ uᵢ(g(aᵢ; p(aᵢ, a*₋ᵢ)) + ωᵢ)` for all `aᵢ ∈ Aᵢ` (the profile
`(aᵢ, a*₋ᵢ)` of footnote 7 is `Function.update a* i aᵢ`). -/
def TradingModel.IsTradingEqm [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) :
    Prop :=
  (∀ i, a i ∈ M.A i) ∧
    ∀ i, ∀ b ∈ M.A i, M.u i (M.g b (M.price (Function.update a i b)) + M.ω i) ≤
      M.u i (M.g (a i) (M.price a) + M.ω i)

/-- **Footnote 7** (MWG, p. 660). The notation `(aᵢ, a*₋ᵢ)`: the profile that agrees with `a*`
except in coordinate `i`; replacing `a*ᵢ` by itself gives back `a*`. -/
theorem footnote_18_7 [DecidableEq ι] (a : ι → Act) (i : ι) (b : Act) :
    Function.update a i b i = b ∧ (∀ j, j ≠ i → Function.update a i b j = a j) ∧
      Function.update a i (a i) = a :=
  ⟨Function.update_self i b a, fun _ hj => Function.update_of_ne hj b a,
    Function.update_eq_self i a⟩

/-- **Definition 18.C.1** (MWG, p. 660), in terms of payoffs. -/
theorem definition_18_C_1 [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) :
    M.IsTradingEqm a ↔ (∀ i, a i ∈ M.A i) ∧
      ∀ i, ∀ b ∈ M.A i, M.payoff (Function.update a i b) i ≤ M.payoff a i := by
  unfold TradingModel.IsTradingEqm TradingModel.payoff
  simp only [Function.update_self]

/-- **Section 18.C** (MWG, p. 661). The effective budget set of agent `i` at `a`:
`Bᵢ(a) = {xᵢ ∈ ℝ^L₊ : xᵢ - ωᵢ ≤ g(a'ᵢ; p(a'ᵢ, a₋ᵢ))` for some `a'ᵢ ∈ Aᵢ}`. (The Walrasian
budget `B(p, p·ωᵢ)` of the text is `budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ ωᵢ)`.) -/
def TradingModel.effBudget [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) (i : ι) :
    Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧
    ∃ b ∈ M.A i, x - M.ω i ≤ M.g b (M.price (Function.update a i b))}

/-- **Section 18.C** (MWG, p. 661). At a trading equilibrium every agent's equilibrium bundle,
when nonnegative, lies in her effective budget set, and it is maximal there for a utility that
is nondecreasing: no point of `Bᵢ(a*)` is better. -/
theorem TradingModel.isTradingEqm_maximal_effBudget [DecidableEq ι] (M : TradingModel ι Act L)
    {a : ι → Act} (h : M.IsTradingEqm a) (i : ι)
    (hmono : ∀ x y : Fin L → ℝ, x ≤ y → M.u i x ≤ M.u i y)
    (hx : M.g (a i) (M.price a) + M.ω i ∈ nonnegOrthant L) :
    M.g (a i) (M.price a) + M.ω i ∈ M.effBudget a i ∧
      ∀ x ∈ M.effBudget a i, M.u i x ≤ M.u i (M.g (a i) (M.price a) + M.ω i) := by
  refine ⟨⟨hx, a i, h.1 i, ?_⟩, ?_⟩
  · rw [Function.update_eq_self, add_sub_cancel_right]
  · rintro x ⟨-, b, hb, hle⟩
    refine (hmono _ _ fun l => ?_).trans (h.2 i b hb)
    have := hle l
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    linarith

/-- **Footnote 8** (MWG, p. 661). Since `p(a'ᵢ, a₋ᵢ)·g(a'ᵢ; p(a'ᵢ, a₋ᵢ)) = 0`, if the price
`p(a'ᵢ, a₋ᵢ) = p̄` does not depend on `a'ᵢ ∈ Aᵢ`, then every achievable net trade lies in the
hyperplane `{z : p̄·z = 0}` perpendicular to `p̄`, and, when `p̄ ≥ 0`, the effective budget set
is contained in the Walrasian budget set `B(p̄, p̄·ωᵢ)`. -/
theorem footnote_18_8 [DecidableEq ι] (M : TradingModel ι Act L) (hv : M.IsValid)
    {a : ι → Act} (ha : ∀ j, a j ∈ M.A j) (i : ι) {pbar : Fin L → ℝ}
    (hconst : ∀ b ∈ M.A i, M.price (Function.update a i b) = pbar) :
    (∀ b ∈ M.A i, pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) = 0) ∧
      (0 ≤ pbar → M.effBudget a i ⊆ budgetSetOn (nonnegOrthant L) pbar (pbar ⬝ᵥ M.ω i)) := by
  have hzero : ∀ b ∈ M.A i, pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) = 0 := by
    intro b hb
    have hall : ∀ j, Function.update a i b j ∈ M.A j := by
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hb
      · rw [Function.update_of_ne hj]
        exact ha j
    have := hv.1 b _ (hv.2 _ hall)
    rwa [hconst b hb] at this ⊢
  refine ⟨hzero, fun hp x ⟨hx, b, hb, hle⟩ => ⟨hx, ?_⟩⟩
  have h1 : pbar ⬝ᵥ (x - M.ω i) ≤ pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) := by
    simp only [dotProduct]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (hp l)
  rw [hzero b hb, dotProduct_sub] at h1
  linarith

/-- **Section 18.C** (MWG, p. 661), insensitivity of prices to own actions made precise. If the
price depends only on the average action, `p(a) = φ((1/r) ∑ᵢ aᵢ)`, with `φ` continuous and the
actions in a bounded set `K ⊆ ℝ^m`, then the effect of one agent's action on the price becomes
negligible as the economy grows: for every `ε > 0` there is `R` such that in every economy with
`r ≥ R` agents, any unilateral change of action moves the price by less than `ε`. (Uniformly in
the profile, the agent and the deviation; the proof uses uniform continuity of `φ` on the
compact closure of the convex hull of `K`.) -/
theorem price_insensitivity {m : ℕ} {F : Type*} [PseudoMetricSpace F]
    (φ : (Fin m → ℝ) → F) (hφ : Continuous φ) {K : Set (Fin m → ℝ)}
    (hK : Bornology.IsBounded K) :
    ∀ ε > 0, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ a : Fin r → Fin m → ℝ, (∀ i, a i ∈ K) →
      ∀ i, ∀ b ∈ K, dist (φ ((r : ℝ)⁻¹ • ∑ j, Function.update a i b j))
        (φ ((r : ℝ)⁻¹ • ∑ j, a j)) < ε := by
  intro ε hε
  set C := closure (convexHull ℝ K) with hC
  have hCc : IsCompact C :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_convexHull.mpr hK).closure
  obtain ⟨δ, hδ, hunif⟩ :=
    Metric.uniformContinuousOn_iff.mp (hCc.uniformContinuousOn_of_continuous hφ.continuousOn)
      ε hε
  obtain ⟨M, hM⟩ := hK.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |M| / δ)
  refine ⟨n + 1, fun r hr a ha i b hb => ?_⟩
  have hr0 : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.le_add_left 1 n).trans hr
    linarith
  -- the averages lie in the convex hull of `K`
  have hmean : ∀ c : Fin r → Fin m → ℝ, (∀ j, c j ∈ K) →
      (r : ℝ)⁻¹ • ∑ j, c j ∈ C := by
    intro c hc
    apply subset_closure
    rw [Finset.smul_sum]
    refine (convex_convexHull ℝ K).sum_mem (fun _ _ => inv_nonneg.mpr hr0.le) ?_
      fun j _ => subset_convexHull ℝ K (hc j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hr0.ne'
  have hupd : ∀ j, Function.update a i b j ∈ K := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hb
    · rw [Function.update_of_ne hj]
      exact ha j
  refine hunif _ (hmean _ hupd) _ (hmean _ ha) ?_
  -- the two averages differ by `(b - aᵢ)/r`
  have hsum : ∑ j, Function.update a i b j = ∑ j, a j + (b - a i) := by
    have : Function.update a i b = a + Pi.single i (b - a i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [this]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    simp
  rw [dist_eq_norm, hsum, smul_add, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr0]
  have hb' : ‖b‖ ≤ M := mem_closedBall_zero_iff.mp (hM hb)
  have ha' : ‖a i‖ ≤ M := mem_closedBall_zero_iff.mp (hM (ha i))
  have hdiff : ‖b - a i‖ ≤ 2 * |M| := by
    have := norm_sub_le b (a i)
    have := le_abs_self M
    linarith
  have hrn : (n : ℝ) + 1 ≤ r := by exact_mod_cast hr
  have hlt : 2 * |M| < δ * r := by
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  calc (r : ℝ)⁻¹ * ‖b - a i‖ ≤ (r : ℝ)⁻¹ * (2 * |M|) :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hr0.le)
    _ < (r : ℝ)⁻¹ * (δ * r) := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hr0)
    _ = δ := by field_simp

/-! ### Example 18.C.1: general equilibrium, single-good Cournot competition (pp. 661-663) -/

/-- **Example 18.C.1** and **footnote 10** (MWG, pp. 661-662). The Cournot model as a trading
model: the players are the `J` firms; good `0` is the consumption good and good `1` is money
(price `1`); firm `j` is "endowed" with one unit of the good, chooses `qⱼ ∈ [0, 1] = Aⱼ`, and
the trading rule is `g(qⱼ; p, 1) = (-qⱼ, p qⱼ)`. With `r` consumers the market selects the price
`p(∑ⱼ qⱼ / r)` (the price selection `sel`), and the owners care only about money. -/
noncomputable def cournotModel (J r : ℕ) (sel : ℝ → ℝ) : TradingModel (Fin J) ℝ 2 where
  P := {p | p 1 = 1}
  A := fun _ => Set.Icc 0 1
  ω := fun _ => ![1, 0]
  g := fun q p => ![-q, p 0 * q]
  price := fun a => ![sel ((∑ j, a j) / r), 1]
  u := fun _ x => x 1

/-- The Cournot model satisfies the requirements of the abstract model:
`(p, 1)·(-q, pq) = 0`. -/
theorem cournotModel_isValid (J r : ℕ) (sel : ℝ → ℝ) : (cournotModel J r sel).IsValid := by
  refine ⟨fun q p hp => ?_, fun a _ => ?_⟩
  · change p 1 = 1 at hp
    simp [cournotModel, dotProduct, Fin.sum_univ_two, hp]
  · rfl

/-- The profit of firm `j` in the Cournot model: `p(∑ₖ qₖ / r) qⱼ`. -/
theorem cournotModel_payoff (J r : ℕ) (sel : ℝ → ℝ) (a : Fin J → ℝ) (j : Fin J) :
    (cournotModel J r sel).payoff a j = sel ((∑ k, a k) / r) * a j := by
  simp [TradingModel.payoff, cournotModel]

/-- The total production after firm `j` changes its output from `c` to `q`, when all firms
produce `c`: `q + (J - 1)c`. -/
theorem cournot_sum_update (J : ℕ) (j : Fin J) (c q : ℝ) :
    ∑ k, Function.update (fun _ : Fin J => c) j q k = q - c + J * c := by
  have : Function.update (fun _ : Fin J => c) j q = (fun _ => c) + Pi.single j (q - c) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  rw [this]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- **Example 18.C.1** (MWG, p. 662), the Walrasian benchmark. A price-taking firm facing a
positive price `p*` maximizes profit `p* q` over `q ∈ [0, 1]` exactly at capacity `q = 1`; when
every firm produces at capacity the production per consumer is `J/r`, so the Walrasian price is
the selected price `p* = p(J/r)`. -/
theorem example_18_C_1_walras {pstar : ℝ} (hp : 0 < pstar) (J r : ℕ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, pstar * q ≤ pstar * 1) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, pstar * 1 ≤ pstar * q → q = 1) ∧
      (∑ _j : Fin J, (1 : ℝ)) / r = J / r := by
  refine ⟨fun q hq => mul_le_mul_of_nonneg_left hq.2 hp.le, fun q hq h => ?_, by simp⟩
  have := le_of_mul_le_mul_left h hp
  linarith [hq.2]

/-- **Example 18.C.1** and **footnote 12** (MWG, pp. 662-663). Cournot equilibria bounded away
from the Walrasian outcome. Let the price selection satisfy `p(s) ≥ 1/λ` on `[0, b']`,
`p(s) ≤ 1/γ` for `s > b'`, and be "very elastic" on `[0, b']`: `p` is nonincreasing and the
revenue `s p(s)` nondecreasing there (Figure 18.C.3). If `r > Jλ/(γ b')` and `r b'/J < 1`,
then every firm producing `r b'/J` is a trading (Cournot) equilibrium: the profit
`p(b') r b'/J ≥ r b'/(Jλ)` exceeds `1/γ`, an upper bound for the profit of a firm that produces
more (the price drops to at most `1/γ` and `q ≤ 1`), and contracting does not pay because
revenue is nondecreasing and the price nonincreasing on `[0, b']`. -/
theorem example_18_C_1 {J r : ℕ} (hJ : 0 < J) {sel : ℝ → ℝ} {lam gam b : ℝ}
    (hlam : 0 < lam) (hgam : 0 < gam) (hb : 0 < b)
    (hhigh : ∀ s ∈ Set.Icc 0 b, 1 / lam ≤ sel s) (hlow : ∀ s, b < s → sel s ≤ 1 / gam)
    (hanti : AntitoneOn sel (Set.Icc 0 b))
    (hel : MonotoneOn (fun s => s * sel s) (Set.Icc 0 b))
    (hr : J * lam / (gam * b) < r) (hcap : r * b / J < 1) :
    (cournotModel J r sel).IsTradingEqm (fun _ => r * b / J) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) hr
  set c := r * b / J with hc
  have hc0 : 0 ≤ c := by positivity
  have hJc : J * c = r * b := by rw [hc]; field_simp
  refine ⟨fun _ => ⟨hc0, hcap.le⟩, fun j q hq => ?_⟩
  have hdev := cournotModel_payoff J r sel (Function.update (fun _ => c) j q) j
  have heq := cournotModel_payoff J r sel (fun _ => c) j
  simp only [TradingModel.payoff] at hdev heq
  rw [Function.update_self] at hdev
  beta_reduce
  rw [hdev, heq, cournot_sum_update]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hJc]
  have hbr : r * b / r = b := by field_simp
  rw [hbr]
  set s := (q - c + r * b) / r with hs
  have hsr : r * s = q - c + r * b := by rw [hs]; field_simp
  -- the equilibrium profit exceeds `1/γ`
  have hpb : 1 / lam ≤ sel b := hhigh b ⟨hb.le, le_rfl⟩
  have hprofit : 1 / gam < sel b * c := by
    have h1 : 1 / gam < c / lam := by
      rw [hc, div_lt_div_iff₀ hgam hlam, div_mul_eq_mul_div, lt_div_iff₀ hJ']
      rw [div_lt_iff₀ (by positivity)] at hr
      linarith
    have h2 : c / lam ≤ sel b * c := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hpb hc0
    linarith
  rcases lt_or_ge c q with hqc | hqc
  · -- expanding production: the price drops to at most `1/γ`
    have hsb : b < s := by
      rw [hs, lt_div_iff₀ hr0]
      linarith
    have hps := hlow s hsb
    have : sel s * q ≤ 1 / gam := by
      have h1 : sel s * q ≤ 1 / gam * q := mul_le_mul_of_nonneg_right hps hq.1
      have h2 : 1 / gam * q ≤ 1 / gam := by
        have := hq.2
        have : 0 < 1 / gam := by positivity
        nlinarith
      linarith
    linarith
  · -- contracting production: revenue is nondecreasing and the price nonincreasing
    have hs0 : 0 ≤ s := by
      rw [hs]
      apply div_nonneg _ hr0.le
      have : c ≤ r * b := by
        rw [← hJc]
        nlinarith
      linarith [hq.1]
    have hsb : s ≤ b := by
      rw [hs, div_le_iff₀ hr0]
      linarith
    have hmem : s ∈ Set.Icc 0 b := ⟨hs0, hsb⟩
    have hbmem : b ∈ Set.Icc 0 b := ⟨hb.le, le_rfl⟩
    have hrev : s * sel s ≤ b * sel b := hel hmem hbmem hsb
    have hprice : sel b ≤ sel s := hanti hmem hbmem hsb
    have hK : 0 ≤ r * b - c := by
      have : c ≤ r * b := by
        rw [← hJc]
        nlinarith
      linarith
    have hq' : q = r * s - (r * b - c) := by linarith
    rw [hq']
    have : r * (s * sel s) ≤ r * (b * sel b) := mul_le_mul_of_nonneg_left hrev hr0.le
    have : (r * b - c) * sel b ≤ (r * b - c) * sel s := mul_le_mul_of_nonneg_left hprice hK
    nlinarith

/-- **Example 18.C.1** (MWG, p. 663). The Cournot equilibrium of `example_18_C_1` is not
Walrasian: production per consumer is `b' < J/r` (so not every firm produces at capacity), and
at the prevailing price `p(b') > 0` a price-taking firm would rather produce the capacity
output `1` than `r b'/J`. -/
theorem example_18_C_1_not_walrasian {J r : ℕ} (hJ : 0 < J) {sel : ℝ → ℝ} {lam b : ℝ}
    (hlam : 0 < lam) (hb : 0 < b) (hhigh : ∀ s ∈ Set.Icc 0 b, 1 / lam ≤ sel s)
    (hr : 0 < r) (hcap : r * b / J < 1) :
    b < J / r ∧ sel b * (r * b / J) < sel b * 1 := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpos : 0 < sel b := lt_of_lt_of_le (by positivity) (hhigh b ⟨hb.le, le_rfl⟩)
  refine ⟨?_, mul_lt_mul_of_pos_left hcap hpos⟩
  rw [div_lt_one hJ'] at hcap
  rw [lt_div_iff₀ hr']
  linarith

/-- A concrete price selection for Example 18.C.1 (a step version of Figure 18.C.3):
`p(s) = 1` for `s ≤ 1/2` and `p(s) = 1/2` for `s > 1/2`. -/
noncomputable def cournotStepSel (s : ℝ) : ℝ := if s ≤ 1 / 2 then 1 else 1 / 2

/-- **Example 18.C.1** (MWG, pp. 662-663), a concrete instance: with `J = 2` firms, `r = 3`
consumers and the selection `cournotStepSel` (`λ = 1`, `γ = 2`, `b' = 1/2`), every firm
producing `3/4 < 1` is a Cournot equilibrium; production per consumer `1/2` is below the
Walrasian `J/r = 2/3`. -/
theorem example_18_C_1_instance :
    (cournotModel 2 3 cournotStepSel).IsTradingEqm (fun _ => 3 / 4) ∧ (1 / 2 : ℝ) < 2 / 3 := by
  have h := example_18_C_1 (J := 2) (r := 3) (sel := cournotStepSel) (lam := 1) (gam := 2)
    (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s hs => by
      have : s ≤ 1 / 2 := hs.2
      simp only [cournotStepSel, this, ↓reduceIte]
      norm_num)
    (fun s hs => by
      have : ¬ s ≤ 1 / 2 := not_le.mpr hs
      simp only [cournotStepSel, this, ↓reduceIte]
      norm_num)
    (fun x hx y hy _ => by
      have h1 : x ≤ 1 / 2 := hx.2
      have h2 : y ≤ 1 / 2 := hy.2
      simp only [cournotStepSel, h1, h2, ↓reduceIte, le_refl])
    (fun x hx y hy hxy => by
      have h1 : x ≤ 1 / 2 := hx.2
      have h2 : y ≤ 1 / 2 := hy.2
      simp only [cournotStepSel, h1, h2, ↓reduceIte, mul_one]
      exact hxy)
    (by norm_num) (by norm_num)
  refine ⟨?_, by norm_num⟩
  have he : (fun _ : Fin 2 => ((3 : ℕ) : ℝ) * (1 / 2) / ((2 : ℕ) : ℝ)) = fun _ => 3 / 4 := by
    funext _
    norm_num
  rwa [he] at h

/-! ### Example 18.C.2: Cournot competition among complements (p. 663) -/

/-- The partial derivative `∂ψ/∂x₁ (x₁, x₂)`. -/
noncomputable def partialOne (ψ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun s => ψ s y) x

/-- The partial derivative `∂ψ/∂x₂ (x₁, x₂)`. -/
noncomputable def partialTwo (ψ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun s => ψ x s) y

/-- **Example 18.C.2** (MWG, p. 663). The market clearing prices at total productions
`(q₁, q₂)` with `r` consumers of quasilinear utility `ψ(x₁, x₂) + money`:
`p(q₁, q₂) = ∇ψ(q₁/r, q₂/r)`, with money (the third good) as numeraire. -/
noncomputable def complementsPrice (ψ : ℝ → ℝ → ℝ) (r : ℕ) (q₁ q₂ : ℝ) : Fin 3 → ℝ :=
  ![partialOne ψ (q₁ / r) (q₂ / r), partialTwo ψ (q₁ / r) (q₂ / r), 1]

/-- **Example 18.C.2** (MWG, p. 663) as a trading model: `J₁` firms producing good 1 and `J₂`
firms producing good 2, each with capacity one and zero cost (as in Example 18.C.1). An action
is a pair `(q₁, q₂)`: a firm of the first kind chooses `(q, 0)`, `q ∈ [0, 1]`, one of the second
kind `(0, q)`; the trading rule is `g((q₁, q₂); p) = (-q₁, -q₂, p₁q₁ + p₂q₂)` and owners care
only about money. -/
noncomputable def complementsModel (J₁ J₂ r : ℕ) (ψ : ℝ → ℝ → ℝ) :
    TradingModel (Fin J₁ ⊕ Fin J₂) (ℝ × ℝ) 3 where
  P := {p | p 2 = 1}
  A := Sum.elim (fun _ => Set.Icc 0 1 ×ˢ {0}) (fun _ => {0} ×ˢ Set.Icc 0 1)
  ω := Sum.elim (fun _ => ![1, 0, 0]) (fun _ => ![0, 1, 0])
  g := fun q p => ![-q.1, -q.2, p 0 * q.1 + p 1 * q.2]
  price := fun a => complementsPrice ψ r (∑ k, (a k).1) (∑ k, (a k).2)
  u := fun _ x => x 2

/-- The complements model satisfies the requirements of the abstract model. -/
theorem complementsModel_isValid (J₁ J₂ r : ℕ) (ψ : ℝ → ℝ → ℝ) :
    (complementsModel J₁ J₂ r ψ).IsValid := by
  refine ⟨fun q p hp => ?_, fun a _ => rfl⟩
  change p 2 = 1 at hp
  simp [complementsModel, dotProduct, Fin.sum_univ_three, hp]
  ring

/-- **Example 18.C.2** (MWG, p. 663). If `ψ(·, 0) ≡ 0`, then `∂ψ/∂x₁ (s, 0) = 0` for every `s`:
when nothing of good 2 is produced, any supply of good 1 is absorbed only at price `0`. (In
particular the book's `p(q₁, q₂) ≫ 0` fails on the axes.) -/
theorem partialOne_axis_eq_zero {ψ : ℝ → ℝ → ℝ} (h : ∀ x, ψ x 0 = 0) (s : ℝ) :
    partialOne ψ s 0 = 0 := by
  have : (fun t => ψ t 0) = fun _ => 0 := funext h
  simp [partialOne, this]

/-- The symmetric statement for good 2. -/
theorem partialTwo_axis_eq_zero {ψ : ℝ → ℝ → ℝ} (h : ∀ y, ψ 0 y = 0) (s : ℝ) :
    partialTwo ψ 0 s = 0 := by
  have : (fun t => ψ 0 t) = fun _ => 0 := funext h
  simp [partialTwo, this]

/-- Changing one coordinate of the zero profile: the sum of the first components is that of the
new action. -/
theorem complements_sum_update_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (b : ℝ × ℝ) :
    (∑ k, (Function.update (fun _ : κ => ((0 : ℝ), (0 : ℝ))) i b k).1 = b.1) ∧
      ∑ k, (Function.update (fun _ : κ => ((0 : ℝ), (0 : ℝ))) i b k).2 = b.2 := by
  constructor
  · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Function.update_of_ne hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Function.update_of_ne hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp

/-- **Example 18.C.2** (MWG, p. 663). If the two goods are complements in the extreme sense
`ψ(0, x₂) = ψ(x₁, 0) = 0`, the null production is a trading equilibrium: a firm that produces
`q > 0` of good 1 while nothing of good 2 is produced faces the price `∂ψ/∂x₁(q/r, 0) = 0`
and earns nothing (and symmetrically for good 2). No concavity or monotonicity of `ψ` is
needed for this claim. -/
theorem example_18_C_2 (J₁ J₂ r : ℕ) {ψ : ℝ → ℝ → ℝ} (h₁ : ∀ x, ψ x 0 = 0)
    (h₂ : ∀ y, ψ 0 y = 0) :
    (complementsModel J₁ J₂ r ψ).IsTradingEqm (fun _ => (0, 0)) := by
  classical
  refine ⟨fun i => ?_, fun i b hb => ?_⟩
  · cases i with
    | inl i => exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
    | inr i => exact ⟨rfl, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨hs1, hs2⟩ := complements_sum_update_zero i b
  cases i with
  | inl i =>
    obtain ⟨q, z⟩ := b
    obtain ⟨-, hz⟩ := hb
    change z = 0 at hz
    subst hz
    simp only [complementsModel, complementsPrice] at hs1 hs2 ⊢
    rw [hs1, hs2]
    simp [partialOne_axis_eq_zero h₁]
  | inr i =>
    obtain ⟨q, z⟩ := b
    obtain ⟨hq, -⟩ := hb
    change q = 0 at hq
    subst hq
    simp only [complementsModel, complementsPrice] at hs1 hs2 ⊢
    rw [hs1, hs2]
    simp [partialTwo_axis_eq_zero h₂]

/-- **Footnote 13** (MWG, p. 663). The homothetic, nonlinear complementary utility
`ψ(x₁, x₂) = √(x₁ x₂)`. -/
noncomputable def fn13GeomMean (x y : ℝ) : ℝ := Real.sqrt (x * y)

/-- `√(x₁x₂)` vanishes on the axes, is homogeneous of degree one (hence homothetic) and is not
linear. -/
theorem footnote_18_13_psi :
    (∀ x, fn13GeomMean x 0 = 0) ∧ (∀ y, fn13GeomMean 0 y = 0) ∧
      (∀ c x y : ℝ, 0 ≤ c → fn13GeomMean (c * x) (c * y) = c * fn13GeomMean x y) ∧
      fn13GeomMean 1 0 + fn13GeomMean 0 1 ≠ fn13GeomMean 1 1 := by
  refine ⟨fun x => by simp [fn13GeomMean], fun y => by simp [fn13GeomMean],
    fun c x y hc => ?_, ?_⟩
  · unfold fn13GeomMean
    rw [show c * x * (c * y) = (c * c) * (x * y) by ring, Real.sqrt_mul (mul_self_nonneg c),
      Real.sqrt_mul_self hc]
  · simp [fn13GeomMean]

/-- `√(x₁x₂)` is concave on `ℝ²₊`: `a√(x₁x₂) + b√(y₁y₂) ≤ √((ax₁ + by₁)(ax₂ + by₂))` for
`a, b ≥ 0` (in particular for `a + b = 1`). -/
theorem footnote_18_13_psi_concave {x₁ x₂ y₁ y₂ a b : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * fn13GeomMean x₁ x₂ + b * fn13GeomMean y₁ y₂ ≤
      fn13GeomMean (a * x₁ + b * y₁) (a * x₂ + b * y₂) := by
  unfold fn13GeomMean
  set s := Real.sqrt (x₁ * x₂)
  set t := Real.sqrt (y₁ * y₂)
  have hs : s ^ 2 = x₁ * x₂ := Real.sq_sqrt (mul_nonneg hx₁ hx₂)
  have ht : t ^ 2 = y₁ * y₂ := Real.sq_sqrt (mul_nonneg hy₁ hy₂)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  apply Real.le_sqrt_of_sq_le
  -- the cross term: `2st ≤ x₁y₂ + y₁x₂`
  have hst : (s * t) ^ 2 = (x₁ * y₂) * (y₁ * x₂) := by
    rw [mul_pow, hs, ht]
    ring
  have hcross : 2 * (s * t) ≤ x₁ * y₂ + y₁ * x₂ := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), mul_nonneg hs0 ht0, mul_nonneg hx₁ hy₂,
      mul_nonneg hy₁ hx₂]
  have hab2 : 0 ≤ a * b := mul_nonneg ha hb
  have e1 : (a * s + b * t) ^ 2 =
      a ^ 2 * (x₁ * x₂) + 2 * (a * b) * (s * t) + b ^ 2 * (y₁ * y₂) := by
    rw [← hs, ← ht]
    ring
  have e2 : (a * x₁ + b * y₁) * (a * x₂ + b * y₂) =
      a ^ 2 * (x₁ * x₂) + (a * b) * (x₁ * y₂ + y₁ * x₂) + b ^ 2 * (y₁ * y₂) := by ring
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hcross hab2]

/-- **Footnote 13** (MWG, p. 663). With `ψ = √(x₁x₂)`, the price of good 1 is `0` at every
`(ε, 0)`, while at `(ε, ε)`, `ε > 0`, both prices equal `1/2`: the clearing prices are bounded
away from `0` along the diagonal but vanish on the axis. -/
theorem footnote_18_13_prices (r : ℕ) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    complementsPrice fn13GeomMean r ε 0 0 = 0 ∧ complementsPrice fn13GeomMean r ε ε 0 = 1 / 2 ∧
      complementsPrice fn13GeomMean r ε ε 1 = 1 / 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set e := ε / r with he
  have he0 : 0 < e := div_pos hε hr'
  have hsq : Real.sqrt (e * e) = e := Real.sqrt_mul_self he0.le
  have hd1 : HasDerivAt (fun s => fn13GeomMean s e) (1 / 2) e := by
    have := ((hasDerivAt_id e).mul_const e).sqrt (by simp [he0.ne'])
    simp only [id, one_mul, hsq] at this
    convert this using 1
    · rfl
    · field_simp
  have hd2 : HasDerivAt (fun s => fn13GeomMean e s) (1 / 2) e := by
    have := ((hasDerivAt_id e).const_mul e).sqrt (by simp [he0.ne'])
    simp only [id, mul_one, hsq] at this
    convert this using 1
    · rfl
    · field_simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [complementsPrice, zero_div, Matrix.cons_val_zero]
    exact partialOne_axis_eq_zero footnote_18_13_psi.1 _
  · simp only [complementsPrice, Matrix.cons_val_zero, partialOne]
    exact hd1.deriv
  · simp only [complementsPrice, Matrix.cons_val_one, Matrix.cons_val_zero, partialTwo]
    exact hd2.deriv

/-- **Footnote 13** (MWG, p. 663). With `ψ = √(x₁x₂)` the clearing price of good 1 is
discontinuous at the origin: it is `0` at `(0, 0)` but `1/2` at every `(ε, ε)`, `ε > 0`. -/
theorem footnote_18_13_discontinuous (r : ℕ) (hr : 0 < r) :
    ¬ ContinuousAt (fun q : ℝ × ℝ => complementsPrice fn13GeomMean r q.1 q.2 0) (0, 0) := by
  intro hc
  have h0 : complementsPrice fn13GeomMean r 0 0 0 = 0 := by
    simp only [complementsPrice, zero_div, Matrix.cons_val_zero]
    exact partialOne_axis_eq_zero footnote_18_13_psi.1 _
  have hdiag : Filter.Tendsto (fun t : ℝ => ((t, t) : ℝ × ℝ)) (nhds 0) (nhds (0, 0)) :=
    (continuous_id.prodMk continuous_id).tendsto' 0 (0, 0) rfl
  have hlim := (hc.tendsto.comp hdiag).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [h0] at hlim
  have hev : (fun t : ℝ => complementsPrice fn13GeomMean r t t 0) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun _ => 1 / 2 :=
    eventually_nhdsWithin_of_forall fun t ht => (footnote_18_13_prices r hr ht).2.1
  have h2 : Filter.Tendsto (fun t : ℝ => complementsPrice fn13GeomMean r t t 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) :=
    tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique hlim h2
  norm_num at this

/-- **Footnote 13** (MWG, p. 663). `ψ = √(x₁x₂)` is not differentiable at the origin (along the
diagonal it is `|t|`), as the footnote says complementarity forces. -/
theorem footnote_18_13_not_differentiable :
    ¬ DifferentiableAt ℝ (fun v : ℝ × ℝ => fn13GeomMean v.1 v.2) (0, 0) := by
  intro hd
  have hdiag : DifferentiableAt ℝ (fun t : ℝ => ((t, t) : ℝ × ℝ)) 0 :=
    differentiableAt_id.prodMk differentiableAt_id
  have := hd.comp (f := fun t : ℝ => ((t, t) : ℝ × ℝ)) (0 : ℝ) hdiag
  have habs : ((fun v : ℝ × ℝ => fn13GeomMean v.1 v.2) ∘ fun t : ℝ => ((t, t) : ℝ × ℝ)) =
      (abs : ℝ → ℝ) := by
    funext t
    simp [fn13GeomMean, Real.sqrt_mul_self_eq_abs]
  rw [habs] at this
  exact not_differentiableAt_abs_zero this

/-! ### Example 18.C.3: trading posts (pp. 663-665) -/

/-- **Example 18.C.3**, (18.C.1) (MWG, p. 664). The price at one trading post, given the bids
`cₖ = (a'ₖ, a''ₖ)` (good offered, money offered) of all consumers: `p = ∑ₖ a''ₖ / ∑ₖ a'ₖ`.
(Lean's convention `x / 0 = 0` gives `p = 0` at a post with no goods offered.) -/
noncomputable def tpPrice {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) : ℝ :=
  (∑ k, (c k).2) / (∑ k, (c k).1)

/-- **Example 18.C.3** (MWG, p. 664). Consumer `i`'s net trade in the good at a trading post:
she receives the share `a''ᵢ / ∑ₖ a''ₖ` of the goods offered and gives up her offer `a'ᵢ`,
`a''ᵢ ∑ₖ a'ₖ / ∑ₖ a''ₖ - a'ᵢ`. This is the book's `a''ᵢ / p - a'ᵢ` whenever both sides of the
post are active (`example_18_C_3_rule`); the share form fixes the convention at inactive posts:
a side of the market facing no offers on the other side receives nothing. -/
noncomputable def tpGood {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) (i : κ) : ℝ :=
  (c i).2 * (∑ k, (c k).1) / (∑ k, (c k).2) - (c i).1

/-- **Example 18.C.3** (MWG, p. 664). Consumer `i`'s net receipt of money at a trading post:
the share `a'ᵢ / ∑ₖ a'ₖ` of the money offered minus her money bid `a''ᵢ` (the book's
`p a'ᵢ - a''ᵢ`, obtained from her budget constraint). -/
noncomputable def tpMoney {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) (i : κ) : ℝ :=
  (c i).1 * (∑ k, (c k).2) / (∑ k, (c k).1) - (c i).2

/-- **Example 18.C.3** (MWG, p. 664). When both sides of the post are active the trading rule
is the book's `gₗ = a''ᵢ/pₗ - a'ᵢ` with money receipt `pₗ a'ᵢ - a''ᵢ`, so the net trade is
orthogonal to the prices (`p·g = 0`), and the post clears: net trades in the good and in money
sum to zero. -/
theorem example_18_C_3_rule {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ)
    (h₁ : 0 < ∑ k, (c k).1) (h₂ : 0 < ∑ k, (c k).2) (i : κ) :
    tpGood c i = (c i).2 / tpPrice c - (c i).1 ∧ tpMoney c i = tpPrice c * (c i).1 - (c i).2 ∧
      tpPrice c * tpGood c i + tpMoney c i = 0 ∧ ∑ k, tpGood c k = 0 ∧ ∑ k, tpMoney c k = 0 := by
  have h₁' := h₁.ne'
  have h₂' := h₂.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [tpGood, tpPrice]
    field_simp
  · simp only [tpMoney, tpPrice]
    field_simp
  · simp only [tpGood, tpMoney, tpPrice]
    field_simp
    ring
  · simp only [tpGood]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    ring
  · simp only [tpMoney]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    ring

/-- The aggregate offer on one side of a post is continuous in the bids. -/
theorem tp_continuous_sum_fst {κ : Type*} [Fintype κ] :
    Continuous fun c : κ → ℝ × ℝ => ∑ k, (c k).1 :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).fst

/-- The aggregate money bid at a post is continuous in the bids. -/
theorem tp_continuous_sum_snd {κ : Type*} [Fintype κ] :
    Continuous fun c : κ → ℝ × ℝ => ∑ k, (c k).2 :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).snd

/-- **Example 18.C.3** (MWG, p. 664). The price (18.C.1) is well defined and continuous at every
bid profile with goods offered at the post (`∑ᵢ a'ᵢ ≠ 0`). -/
theorem example_18_C_3_continuous {κ : Type*} [Fintype κ] :
    ContinuousOn (tpPrice (κ := κ)) {c | ∑ k, (c k).1 ≠ 0} :=
  tp_continuous_sum_snd.continuousOn.div tp_continuous_sum_fst.continuousOn fun _ hc => hc

/-- The bid profile in which only consumer `i` bids `(t, m t)` at the post. -/
def tpLoneBid {κ : Type*} [DecidableEq κ] (i : κ) (m t : ℝ) : κ → ℝ × ℝ :=
  fun k => if k = i then (t, m * t) else 0

/-- The lone bid is continuous in `t`. -/
theorem tp_continuous_loneBid {κ : Type*} [DecidableEq κ] (i : κ) (m : ℝ) :
    Continuous (tpLoneBid i m) := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = i
  · simp only [tpLoneBid, hk, ↓reduceIte]
    exact continuous_id.prodMk (continuous_const.mul continuous_id)
  · simp only [tpLoneBid, hk, ↓reduceIte]
    exact continuous_const

/-- With a lone bid `(t, m t)`, `t > 0`, the price is `m`. -/
theorem tpPrice_loneBid {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (m : ℝ) {t : ℝ}
    (ht : 0 < t) : tpPrice (tpLoneBid i m t) = m ∧ 0 < ∑ k, (tpLoneBid i m t k).1 := by
  have h1 : ∑ k, (tpLoneBid i m t k).1 = t := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [tpLoneBid]
  have h2 : ∑ k, (tpLoneBid i m t k).2 = m * t := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [tpLoneBid]
  refine ⟨?_, by rw [h1]; exact ht⟩
  rw [tpPrice, h1, h2]
  field_simp

/-- **Example 18.C.3** (MWG, p. 665). "The impossibility of assigning prices continuously when
`aₗᵢ = 0` for all `i`": no function that agrees with the price (18.C.1) wherever both sides
of the post are active is continuous at the inactive profile `0` (lone bids `(t, t)` give
price `1`, lone bids `(t, 2t)` price `2`, and both tend to `0`). -/
theorem example_18_C_3_no_continuous_price {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : (κ → ℝ × ℝ) → ℝ)
    (hf : ∀ c, 0 < ∑ k, (c k).1 → 0 < ∑ k, (c k).2 → f c = tpPrice c) :
    ¬ ContinuousAt f 0 := by
  classical
  intro hc
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hval : ∀ m : ℝ, 0 < m → f 0 = m := by
    intro m hm
    have h0 : tpLoneBid i m 0 = 0 := by
      funext k
      by_cases hk : k = i <;> simp [tpLoneBid, hk]
    have ht : Filter.Tendsto (tpLoneBid i m) (nhds 0) (nhds 0) := by
      have := (tp_continuous_loneBid i m).tendsto 0
      rwa [h0] at this
    have hcomp := (hc.tendsto.comp ht).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have hev : (f ∘ tpLoneBid i m) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => m := by
      refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
      obtain ⟨hp, h1⟩ := tpPrice_loneBid i m ht
      have h2 : 0 < ∑ k, (tpLoneBid i m t k).2 := by
        rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp only [tpLoneBid, ↓reduceIte]
        positivity
      change f (tpLoneBid i m t) = m
      rw [hf _ h1 h2, hp]
    exact tendsto_nhds_unique hcomp (tendsto_const_nhds.congr' hev.symm)
  have := (hval 1 one_pos).symm.trans (hval 2 two_pos)
  norm_num at this

/-- **Footnote 14** (MWG, p. 664). With a single trading post (`L = 2`) the relative price of
money in terms of the good, `∑ᵢ a'ᵢ / ∑ᵢ a''ᵢ`, is well defined and continuous wherever money is
offered (`∑ᵢ a''ᵢ ≠ 0`), and it is `0` when money but no good is offered; the essential
difficulty is at `∑ᵢ a'ᵢ = ∑ᵢ a''ᵢ = 0`, where it cannot be extended continuously. -/
theorem footnote_18_14 {κ : Type*} [Fintype κ] [Nonempty κ] :
    ContinuousOn (fun c : κ → ℝ × ℝ => (∑ k, (c k).1) / (∑ k, (c k).2))
        {c | ∑ k, (c k).2 ≠ 0} ∧
      (∀ c : κ → ℝ × ℝ, ∑ k, (c k).1 = 0 → (∑ k, (c k).1) / (∑ k, (c k).2) = 0) ∧
      ∀ f : (κ → ℝ × ℝ) → ℝ,
        (∀ c, 0 < ∑ k, (c k).1 → 0 < ∑ k, (c k).2 →
          f c = (∑ k, (c k).1) / (∑ k, (c k).2)) → ¬ ContinuousAt f 0 := by
  refine ⟨tp_continuous_sum_fst.continuousOn.div tp_continuous_sum_snd.continuousOn fun _ hc => hc,
    fun c hc => by rw [hc, zero_div], fun f hf hcont => ?_⟩
  -- swap the two sides of the post
  set sw : (κ → ℝ × ℝ) → κ → ℝ × ℝ := fun c k => (c k).swap with hsw
  have hswc : Continuous sw := continuous_pi fun k => continuous_swap.comp (continuous_apply k)
  have hsw0 : sw 0 = 0 := by
    funext k
    simp [hsw]
  refine example_18_C_3_no_continuous_price (f ∘ sw) (fun c h1 h2 => ?_) ?_
  · simp only [Function.comp, hsw]
    rw [hf _ h2 h1]
    rfl
  · have : ContinuousAt f (sw 0) := by rwa [hsw0]
    exact this.comp hswc.continuousAt

/-- An economy with trading posts (Example 18.C.3, MWG, p. 664): `n = L - 1` goods traded for
money at `n` posts; consumer `i` has endowments `ωₗᵢ` of the goods and `ω_Lᵢ` of money, and a
utility over the bundle of goods and money. -/
structure TradingPostEconomy (κ : Type*) (n : ℕ) where
  /-- Endowments of the goods `ωₗᵢ`, `l ≤ L - 1`. -/
  ωg : κ → Fin n → ℝ
  /-- Endowments of money `ω_Lᵢ`. -/
  ωm : κ → ℝ
  /-- Utilities over goods and money. -/
  u : κ → (Fin n → ℝ) → ℝ → ℝ

variable {κ : Type*} {n : ℕ}

/-- **Example 18.C.3** (MWG, p. 664). The feasible bids of consumer `i`: at every post
`aₗᵢ = (a'ₗᵢ, a''ₗᵢ) ∈ ℝ²₊` with `a'ₗᵢ ≤ ωₗᵢ`, and `∑ₗ a''ₗᵢ ≤ ω_Lᵢ`. -/
def TradingPostEconomy.FeasibleBid (E : TradingPostEconomy κ n) (i : κ)
    (b : Fin n → ℝ × ℝ) : Prop :=
  (∀ l, 0 ≤ (b l).1 ∧ (b l).1 ≤ E.ωg i l ∧ 0 ≤ (b l).2) ∧ ∑ l, (b l).2 ≤ E.ωm i

/-- The goods consumer `i` ends up with: `ωₗᵢ` plus her net trade at post `l`. -/
noncomputable def TradingPostEconomy.goodsOut [Fintype κ] (E : TradingPostEconomy κ n)
    (a : κ → Fin n → ℝ × ℝ) (i : κ) : Fin n → ℝ :=
  fun l => E.ωg i l + tpGood (fun k => a k l) i

/-- The money consumer `i` ends up with: `ω_Lᵢ` plus her net money receipts at all posts. -/
noncomputable def TradingPostEconomy.moneyOut [Fintype κ] (E : TradingPostEconomy κ n)
    (a : κ → Fin n → ℝ × ℝ) (i : κ) : ℝ :=
  E.ωm i + ∑ l, tpMoney (fun k => a k l) i

/-- **Definition 18.C.1** for the trading-post game in which only the posts in `O` exist (bids
at the other posts are zero): every consumer bids feasibly and no feasible unilateral change of
bids raises her utility. -/
def TradingPostEconomy.IsEqm [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    (O : Set (Fin n)) (a : κ → Fin n → ℝ × ℝ) : Prop :=
  (∀ i, E.FeasibleBid i (a i) ∧ ∀ l ∉ O, a i l = 0) ∧
    ∀ i b, E.FeasibleBid i b → (∀ l ∉ O, b l = 0) →
      E.u i (E.goodsOut (Function.update a i b) i) (E.moneyOut (Function.update a i b) i) ≤
        E.u i (E.goodsOut a i) (E.moneyOut a i)

/-- A lone bidder at a post gets nothing back: if all other bids at the post are `0` and
consumer `i`'s bid is nonnegative, her net trades in the good and in money are `≤ 0`. -/
theorem tp_lone_bidder [Fintype κ] {c : κ → ℝ × ℝ} {i : κ} (hc : ∀ k, k ≠ i → c k = 0)
    (h₁ : 0 ≤ (c i).1) (h₂ : 0 ≤ (c i).2) : tpGood c i ≤ 0 ∧ tpMoney c i ≤ 0 := by
  have s1 : ∑ k, (c k).1 = (c i).1 := Finset.sum_eq_single i
    (fun k _ hk => by simp [hc k hk]) (fun h => absurd (Finset.mem_univ i) h)
  have s2 : ∑ k, (c k).2 = (c i).2 := Finset.sum_eq_single i
    (fun k _ hk => by simp [hc k hk]) (fun h => absurd (Finset.mem_univ i) h)
  simp only [tpGood, tpMoney, s1, s2]
  constructor
  · rcases h₂.eq_or_lt with h | h
    · rw [← h]
      simp [h₁]
    · rw [mul_div_cancel_left₀ _ h.ne', sub_self]
  · rcases h₁.eq_or_lt with h | h
    · rw [← h]
      simp [h₂]
    · rw [mul_div_cancel_left₀ _ h.ne', sub_self]

/-- At a post where nobody bids, every net trade is zero. -/
theorem tp_all_zero [Fintype κ] {c : κ → ℝ × ℝ} (hc : ∀ k, c k = 0) (i : κ) :
    tpGood c i = 0 ∧ tpMoney c i = 0 := by
  simp [tpGood, tpMoney, hc]

/-- **Example 18.C.3** (MWG, p. 665). An inactive trading post does not destroy an equilibrium:
any trading equilibrium of the model in which post `l` is closed remains an equilibrium when the
post is open but inactive (`aₗᵢ = (0, 0)` for all `i`), provided utilities are nondecreasing in
goods and money. A consumer who bids alone at post `l` receives nothing in return
(`tp_lone_bidder`), so dropping her bid there is a feasible deviation in the closed model that is
at least as good. -/
theorem example_18_C_3_inactive_post [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    (hmono : ∀ i (x x' : Fin n → ℝ) (m m' : ℝ), x ≤ x' → m ≤ m' → E.u i x m ≤ E.u i x' m')
    {O : Set (Fin n)} {a : κ → Fin n → ℝ × ℝ} (h : E.IsEqm O a) {l : Fin n} (hl : l ∉ O) :
    E.IsEqm (insert l O) a := by
  refine ⟨fun i => ⟨(h.1 i).1, fun l' hl' => (h.1 i).2 l' fun h' => hl'
    (Set.mem_insert_of_mem _ h')⟩, fun i b hb hbO => ?_⟩
  set b' := Function.update b l 0 with hb'
  have hfeas : E.FeasibleBid i b' := by
    refine ⟨fun l' => ?_, ?_⟩
    · by_cases hl' : l' = l
      · subst hl'
        have := (h.1 i).1.1 l'
        rw [hb', Function.update_self]
        exact ⟨le_rfl, this.1.trans this.2.1, le_rfl⟩
      · simp only [hb', Function.update_of_ne hl']
        exact hb.1 l'
    · refine le_trans (Finset.sum_le_sum fun l' _ => ?_) hb.2
      by_cases hl' : l' = l
      · subst hl'
        simp [hb', (hb.1 l').2.2]
      · simp [hb', Function.update_of_ne hl']
  have hO : ∀ l' ∉ O, b' l' = 0 := by
    intro l' hl'
    by_cases hll : l' = l
    · subst hll
      simp [hb']
    · simp only [hb', Function.update_of_ne hll]
      exact hbO l' fun h' => (Set.mem_insert_iff.mp h').elim hll hl'
  refine le_trans (hmono i _ _ _ _ ?_ ?_) (h.2 i b' hfeas hO)
  · -- post by post, the goods obtained are no larger with the bid at post `l`
    intro l'
    simp only [TradingPostEconomy.goodsOut]
    by_cases hll : l' = l
    · subst hll
      have hother : ∀ k, k ≠ i → Function.update a i b k l' = 0 := fun k hk => by
        rw [Function.update_of_ne hk]
        exact (h.1 k).2 l' hl
      have h1 := (tp_lone_bidder (c := fun k => Function.update a i b k l') hother
        (by simpa using (hb.1 l').1) (by simpa using (hb.1 l').2.2)).1
      have h2 := (tp_all_zero (c := fun k => Function.update a i b' k l') (fun k => by
        by_cases hk : k = i
        · subst hk
          simp [hb']
        · rw [Function.update_of_ne hk]
          exact (h.1 k).2 l' hl) i).1
      linarith
    · have : (fun k => Function.update a i b k l') = fun k => Function.update a i b' k l' := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [hb', Function.update_of_ne hll]
        · simp [Function.update_of_ne hk]
      rw [this]
  · simp only [TradingPostEconomy.moneyOut, add_le_add_iff_left]
    refine Finset.sum_le_sum fun l' _ => ?_
    by_cases hll : l' = l
    · subst hll
      have hother : ∀ k, k ≠ i → Function.update a i b k l' = 0 := fun k hk => by
        rw [Function.update_of_ne hk]
        exact (h.1 k).2 l' hl
      have h1 := (tp_lone_bidder (c := fun k => Function.update a i b k l') hother
        (by simpa using (hb.1 l').1) (by simpa using (hb.1 l').2.2)).2
      have h2 := (tp_all_zero (c := fun k => Function.update a i b' k l') (fun k => by
        by_cases hk : k = i
        · subst hk
          simp [hb']
        · rw [Function.update_of_ne hk]
          exact (h.1 k).2 l' hl) i).2
      linarith
    · have : (fun k => Function.update a i b k l') = fun k => Function.update a i b' k l' := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [hb', Function.update_of_ne hll]
        · simp [Function.update_of_ne hk]
      rw [this]

/-- **Example 18.C.3** (MWG, p. 665). A consumer without money (`ω_Lᵢ = 0`) cannot buy goods:
whatever the others bid, every feasible bid leaves her with no more of any good than her
endowment. -/
theorem example_18_C_3_no_money [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    {i : κ} (h0 : E.ωm i = 0) {b : Fin n → ℝ × ℝ} (hb : E.FeasibleBid i b)
    (a : κ → Fin n → ℝ × ℝ) (l : Fin n) :
    E.goodsOut (Function.update a i b) i l ≤ E.ωg i l := by
  have hzero : ∀ l', (b l').2 = 0 := by
    have hsum := hb.2
    rw [h0] at hsum
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l' _ => (hb.1 l').2.2)).mp
      (le_antisymm hsum (Finset.sum_nonneg fun l' _ => (hb.1 l').2.2))
    exact fun l' => this l' (Finset.mem_univ l')
  simp only [TradingPostEconomy.goodsOut, tpGood, Function.update_self, hzero l, zero_mul,
    zero_div, zero_sub, add_neg_le_iff_le_add, le_add_iff_nonneg_right]
  exact (hb.1 l).1

/-! ### Exercise 18.C.1: effective budget sets at a trading post (L = 2) -/

/-- **Exercise 18.C.1** (MWG, p. 685), `L = 2`. The effective budget set of consumer `i` at a
single trading post, given the bids `c` of the others: the bundles `x ∈ ℝ²₊` (good, money) with
`x ≤ ωᵢ + (gᵢ, mᵢ)` for some feasible bid `(s, b)` of `i` (`0 ≤ s ≤ ω₁ᵢ` of the good offered,
`0 ≤ b ≤ ω₂ᵢ` of money offered; two-sided bids allowed). -/
noncomputable def tpBudget [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    (ω : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ ∃ s b : ℝ, 0 ≤ s ∧ s ≤ ω 0 ∧ 0 ≤ b ∧ b ≤ ω 1 ∧
    x 0 ≤ ω 0 + tpGood (Function.update c i (s, b)) i ∧
    x 1 ≤ ω 1 + tpMoney (Function.update c i (s, b)) i}

/-- The others' aggregate offers at the post: `A' = ∑_{k ≠ i} a'ₖ`, `A'' = ∑_{k ≠ i} a''ₖ`,
and the aggregates after `i` bids `(s, b)`: `s + A'` and `b + A''`. -/
theorem tp_update_sums [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) (s b : ℝ) :
    ∑ k, (Function.update c i (s, b) k).1 = s + ∑ k ∈ Finset.univ.erase i, (c k).1 ∧
      ∑ k, (Function.update c i (s, b) k).2 = b + ∑ k ∈ Finset.univ.erase i, (c k).2 := by
  constructor
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- **Exercise 18.C.1** (MWG, p. 685). With the others' aggregates `A', A'' > 0`, the bid
`(s, b) ≥ 0` yields the net trades `g = (bA' - sA'')/(b + A'')` in the good and
`m = (sA'' - bA')/(s + A')` in money. -/
theorem tp_outcome [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpGood (Function.update c i (s, b)) i =
        (b * ∑ k ∈ Finset.univ.erase i, (c k).1 - s * ∑ k ∈ Finset.univ.erase i, (c k).2) /
          (b + ∑ k ∈ Finset.univ.erase i, (c k).2) ∧
      tpMoney (Function.update c i (s, b)) i =
        (s * ∑ k ∈ Finset.univ.erase i, (c k).2 - b * ∑ k ∈ Finset.univ.erase i, (c k).1) /
          (s + ∑ k ∈ Finset.univ.erase i, (c k).1) := by
  obtain ⟨h1, h2⟩ := tp_update_sums c i s b
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2
  have hb' : b + A₂ ≠ 0 := by positivity
  have hs' : s + A₁ ≠ 0 := by positivity
  simp only [tpGood, tpMoney, h1, h2, Function.update_self]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **Exercise 18.C.1** (MWG, p. 664, p. 685). The displayed outcomes of one-sided bids: selling
`s` gives `x = (ω₁ - s, ω₂ + sA''/(s + A'))` and buying with `b` gives
`x = (ω₁ + bA'/(b + A''), ω₂ - b)`. -/
theorem exercise_18_C_1_one_sided [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    (tpGood (Function.update c i (s, 0)) i = -s ∧
      tpMoney (Function.update c i (s, 0)) i =
        s * (∑ k ∈ Finset.univ.erase i, (c k).2) / (s + ∑ k ∈ Finset.univ.erase i, (c k).1)) ∧
    (tpGood (Function.update c i (0, b)) i =
        b * (∑ k ∈ Finset.univ.erase i, (c k).1) / (b + ∑ k ∈ Finset.univ.erase i, (c k).2) ∧
      tpMoney (Function.update c i (0, b)) i = -b) := by
  obtain ⟨g1, m1⟩ := tp_outcome c i hs le_rfl hA₁ hA₂
  obtain ⟨g2, m2⟩ := tp_outcome c i le_rfl hb hA₁ hA₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [g1]
    field_simp
    ring
  · rw [m1]
    ring
  · rw [g2]
    ring
  · rw [m2]
    field_simp
    ring

/-- The frontier of the effective budget set in net-trade coordinates: a net trade `d` in the
good comes with the money trade `φ(d) = -dA''/(A' - d)` (defined for `d < A'`). -/
noncomputable def tpFrontier (A₁ A₂ d : ℝ) : ℝ := -(d * A₂) / (A₁ - d)

/-- Every feasible bid, one- or two-sided, lands on the frontier: `m = φ(g)`. -/
theorem tp_outcome_on_frontier [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpMoney (Function.update c i (s, b)) i =
      tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1) (∑ k ∈ Finset.univ.erase i, (c k).2)
        (tpGood (Function.update c i (s, b)) i) := by
  obtain ⟨g, m⟩ := tp_outcome c i hs hb hA₁ hA₂
  rw [g, m]
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2
  have hb' : 0 < b + A₂ := by positivity
  have hs' : 0 < s + A₁ := by positivity
  have hden : A₁ - (b * A₁ - s * A₂) / (b + A₂) = A₂ * (s + A₁) / (b + A₂) := by
    field_simp
    ring
  unfold tpFrontier
  rw [hden]
  field_simp
  ring

/-- `φ(d) = A'' - A'A''/(A' - d)`. -/
theorem tpFrontier_eq {A₁ A₂ d : ℝ} (hd : d < A₁) :
    tpFrontier A₁ A₂ d = A₂ - A₁ * A₂ / (A₁ - d) := by
  have : A₁ - d ≠ 0 := by linarith
  unfold tpFrontier
  field_simp
  ring

/-- **Exercise 18.C.1** (MWG, p. 685). The frontier `φ` is strictly concave on `d < A'`: the
upper boundary of the effective budget set contains no straight segments. -/
theorem tpFrontier_strictConcaveOn {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    StrictConcaveOn ℝ (Set.Iio A₁) (tpFrontier A₁ A₂) := by
  refine ⟨convex_Iio A₁, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Iio] at hx hy
  have hz : a * x + b * y < A₁ := by
    have : a * x + b * y < a * A₁ + b * A₁ := by
      rcases lt_or_gt_of_ne hxy with h | h
      · nlinarith
      · nlinarith
    linarith [show a * A₁ + b * A₁ = A₁ by rw [← add_mul, hab, one_mul]]
  simp only [smul_eq_mul]
  rw [tpFrontier_eq hx, tpFrontier_eq hy, tpFrontier_eq hz]
  set u := A₁ - x with hu
  set v := A₁ - y with hv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hw : A₁ - (a * x + b * y) = a * u + b * v := by
    rw [hu, hv]
    linear_combination (-A₁) * hab
  rw [hw]
  have huv : u ≠ v := fun h => hxy (by linarith)
  have hw0 : 0 < a * u + b * v := by positivity
  -- the strict convexity of `t ↦ 1/t`
  have key : 1 / (a * u + b * v) < a / u + b / v := by
    rw [div_add_div _ _ hu0.ne' hv0.ne', div_lt_div_iff₀ hw0 (mul_pos hu0 hv0)]
    have hsq : 0 < (u - v) ^ 2 := by
      have : u - v ≠ 0 := sub_ne_zero.mpr huv
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) hsq]
  have hK : 0 < A₁ * A₂ := mul_pos hA₁ hA₂
  have e1 : a * (A₂ - A₁ * A₂ / u) + b * (A₂ - A₁ * A₂ / v) =
      A₂ - A₁ * A₂ * (a / u + b / v) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    field_simp
    ring
  have e2 : A₂ - A₁ * A₂ / (a * u + b * v) = A₂ - A₁ * A₂ * (1 / (a * u + b * v)) := by
    rw [mul_one_div]
  rw [e1, e2]
  nlinarith [mul_lt_mul_of_pos_left key hK]

/-- The frontier is nonincreasing on `d < A'`. -/
theorem tpFrontier_antitoneOn {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    AntitoneOn (tpFrontier A₁ A₂) (Set.Iio A₁) := by
  intro x hx y hy hxy
  simp only [Set.mem_Iio] at hx hy
  rw [tpFrontier_eq hx, tpFrontier_eq hy]
  have : A₁ * A₂ / (A₁ - x) ≤ A₁ * A₂ / (A₁ - y) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  linarith

/-- The largest net purchase of the good: spending all money, `b = ω₂`, buys
`ω₂A'/(ω₂ + A'')`. -/
noncomputable def tpMaxBuy (A₁ A₂ w : ℝ) : ℝ := w * A₁ / (w + A₂)

/-- The achievable net trades in the good are exactly `[-ω₁, ω₂A'/(ω₂ + A'')]`: every feasible
bid lands there, and every point of the interval is reached by a one-sided bid. -/
theorem tp_reachable [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {ω : Fin 2 → ℝ}
    (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) (d : ℝ) :
    (∃ s b : ℝ, 0 ≤ s ∧ s ≤ ω 0 ∧ 0 ≤ b ∧ b ≤ ω 1 ∧
      tpGood (Function.update c i (s, b)) i = d) ↔
    d ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
      (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)) := by
  have hout : ∀ s b : ℝ, 0 ≤ s → 0 ≤ b → tpGood (Function.update c i (s, b)) i =
      (b * ∑ k ∈ Finset.univ.erase i, (c k).1 - s * ∑ k ∈ Finset.univ.erase i, (c k).2) /
        (b + ∑ k ∈ Finset.univ.erase i, (c k).2) :=
    fun s b hs hb => (tp_outcome c i hs hb hA₁ hA₂).1
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hw : 0 ≤ ω 1 := hω 1
  constructor
  · rintro ⟨s, b, hs, hsω, hb, hbω, rfl⟩
    rw [hout s b hs hb]
    have hb' : 0 < b + A₂ := by positivity
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hb']
      nlinarith
    · unfold tpMaxBuy
      rw [div_le_div_iff₀ hb' (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hbω) (mul_pos hA₁ hA₂).le,
        mul_nonneg hs (mul_nonneg hA₂.le (add_nonneg hw hA₂.le))]
  · rintro ⟨hd0, hd1⟩
    rcases le_or_gt d 0 with hd | hd
    · refine ⟨-d, 0, by linarith, by linarith, le_rfl, hw, ?_⟩
      rw [hout _ _ (by linarith) le_rfl]
      field_simp
      ring
    · have hlt : d < A₁ := by
        have : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
          unfold tpMaxBuy
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      have hden : 0 < A₁ - d := by linarith
      refine ⟨0, d * A₂ / (A₁ - d), le_rfl, hω 0, by positivity, ?_, ?_⟩
      · rw [div_le_iff₀ hden]
        unfold tpMaxBuy at hd1
        rw [le_div_iff₀ (by positivity)] at hd1
        linarith
      · rw [hout _ _ le_rfl (by positivity)]
        field_simp
        ring

/-- **Exercise 18.C.1** (MWG, p. 685). The effective budget set of a trading-post consumer
(with the others active on both sides, `A', A'' > 0`) is
`{x ≥ 0 : x₁ - ω₁ ≤ ω₂A'/(ω₂ + A''), x₂ - ω₂ ≤ φ(x₁ - ω₁)}`: the region below the graph of the
strictly concave, nonincreasing frontier `φ`. -/
theorem exercise_18_C_1_eq [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpBudget c i ω = {x | x ∈ nonnegOrthant 2 ∧
      x 0 - ω 0 ≤ tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1) ∧
      x 1 - ω 1 ≤ tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (x 0 - ω 0)} := by
  have hfr := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) =>
    tp_outcome_on_frontier c i hs hb hA₁ hA₂
  have hreach := tp_reachable c i hω hA₁ hA₂
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  ext x
  constructor
  · rintro ⟨hx, s, b, hs, hsω, hb, hbω, h0, h1⟩
    have hd := (hreach _).mp ⟨s, b, hs, hsω, hb, hbω, rfl⟩
    rw [hfr s b hs hb] at h1
    refine ⟨hx, by linarith [hd.2], ?_⟩
    have hx0 : x 0 - ω 0 < A₁ := by linarith [hd.2]
    have := tpFrontier_antitoneOn hA₁ hA₂ (Set.mem_Iio.mpr hx0)
      (Set.mem_Iio.mpr (hd.2.trans_lt hmax)) (by linarith)
    linarith
  · rintro ⟨hx, h0, h1⟩
    obtain ⟨s, b, hs, hsω, hb, hbω, hg⟩ :=
      (hreach (x 0 - ω 0)).mpr ⟨by linarith [hx 0], h0⟩
    refine ⟨hx, s, b, hs, hsω, hb, hbω, by linarith, ?_⟩
    rw [tp_outcome_on_frontier c i hs hb hA₁ hA₂, hg]
    linarith

/-- **Exercise 18.C.1** (MWG, pp. 664, 685), convexity. With the other consumers active on
both sides of the post (`∑_{k≠i} a'ₖ > 0`, `∑_{k≠i} a''ₖ > 0`), the effective budget set of
consumer `i` (two-sided bids included) is convex. -/
theorem exercise_18_C_1_convex [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    Convex ℝ (tpBudget c i ω) := by
  rw [exercise_18_C_1_eq c i hω hA₁ hA₂]
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  have hconc := (tpFrontier_strictConcaveOn hA₁ hA₂).concaveOn
  rintro x ⟨hx, hx0, hx1⟩ y ⟨hy, hy0, hy1⟩ a b ha hb hab
  refine ⟨fun l => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : a * x 0 + b * y 0 - ω 0 = a * (x 0 - ω 0) + b * (y 0 - ω 0) := by
      linear_combination (ω 0) * hab
    rw [this]
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e0 : a * x 0 + b * y 0 - ω 0 = a * (x 0 - ω 0) + b * (y 0 - ω 0) := by
      linear_combination (ω 0) * hab
    have e1 : a * x 1 + b * y 1 - ω 1 = a * (x 1 - ω 1) + b * (y 1 - ω 1) := by
      linear_combination (ω 1) * hab
    rw [e0, e1]
    have hc := hconc.2 (Set.mem_Iio.mpr (hx0.trans_lt hmax)) (Set.mem_Iio.mpr (hy0.trans_lt hmax))
      ha hb hab
    simp only [smul_eq_mul] at hc
    nlinarith

/-- **Exercise 18.C.1** (MWG, pp. 664, 685), the upper boundary. For every achievable net trade
`d ∈ [-ω₁, ω₂A'/(ω₂ + A'')]` the point `(ω₁ + d, ω₂ + φ(d))` lies in the effective budget set
and nothing above it does; and the boundary contains no straight segment: for two distinct
boundary points, every point strictly between them lies in the budget set strictly below the
boundary. -/
theorem exercise_18_C_1_boundary [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    (∀ d ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)),
      ![ω 0 + d, ω 1 + tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) d] ∈ tpBudget c i ω) ∧
    (∀ x ∈ tpBudget c i ω, x 1 ≤ ω 1 + tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (x 0 - ω 0)) ∧
    ∀ d₁ ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)),
      ∀ d₂ ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)), d₁ ≠ d₂ → ∀ t : ℝ, 0 < t → t < 1 →
      t * tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
          (∑ k ∈ Finset.univ.erase i, (c k).2) d₁ +
        (1 - t) * tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
          (∑ k ∈ Finset.univ.erase i, (c k).2) d₂ <
      tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (t * d₁ + (1 - t) * d₂) := by
  have hfr := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) =>
    tp_outcome_on_frontier c i hs hb hA₁ hA₂
  have hmo := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) => (tp_outcome c i hs hb hA₁ hA₂).2
  have heq := exercise_18_C_1_eq c i hω hA₁ hA₂
  have hreach := tp_reachable c i hω hA₁ hA₂
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  refine ⟨fun d hd => ?_, fun x hx => ?_, fun d₁ hd₁ d₂ hd₂ hne t ht0 ht1 => ?_⟩
  · obtain ⟨s, b, hs, hsω, hb, hbω, hg⟩ := (hreach d).mpr hd
    have hm := hfr s b hs hb
    rw [hg] at hm
    -- the bid `(s, b)` attains the point, which is therefore nonnegative
    have hnn : ![ω 0 + d, ω 1 + tpFrontier A₁ A₂ d] ∈ nonnegOrthant 2 := by
      intro l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linarith [hd.1]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← hm, hmo s b hs hb]
        have hs' : 0 < s + A₁ := by positivity
        rw [← sub_nonneg]
        have : ω 1 + (s * A₂ - b * A₁) / (s + A₁) - 0 =
            ((ω 1 - b) * (s + A₁) + b * s + s * A₂) / (s + A₁) := by
          field_simp
          ring
        rw [this]
        apply div_nonneg _ hs'.le
        nlinarith
    refine ⟨hnn, s, b, hs, hsω, hb, hbω, ?_, ?_⟩
    · simp [hg]
    · simp [hm]
  · rw [heq] at hx
    linarith [hx.2.2]
  · have hs := tpFrontier_strictConcaveOn hA₁ hA₂
    have := hs.2 (Set.mem_Iio.mpr (hd₁.2.trans_lt hmax)) (Set.mem_Iio.mpr (hd₂.2.trans_lt hmax))
      hne ht0 (by linarith : (0 : ℝ) < 1 - t) (by ring)
    simpa only [smul_eq_mul] using this

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The limits to redistribution (MWG Section 18.D, pp. 665-670)

The exchange economy of Section 18.D is a `CoreEconomy` (preferences `≿ᵢ` on `ℝ^L₊`,
endowments `ωᵢ`; feasibility with the technology `Y`, `Y = -ℝ^L₊` in the exchange case).

* **Definition 18.D.1** (`CoreEconomy.IsSelfSelectiveWith`, `CoreEconomy.IsSelfSelective`,
  `definition_18_D_1`).
* p. 666, corrected (`selfSelective_iff_netTrades`): a feasible allocation is self-selective iff
  it is self-selective with `B = {z*₁, ..., z*_I}` (the net trades) iff no consumer envies another
  consumer's net trade (`CoreEconomy.NoEnvyNetTrades`). The printed `B = {x*₁, ..., x*_I}` is a
  misprint: `selfSelective_consumptions_misprint`.
* p. 667 (`walras_isParetoOptimal_selfSelective`): with rational monotone preferences a
  Walrasian allocation with prices `p` is Pareto optimal (Proposition 16.C.1 through the
  Chapter 16 bridges) and self-selective with `B = {z : p·z = 0}` (budgets bind by
  monotonicity), and also with `B = {z : p·z ≤ 0}`.
* **Figures 18.D.2 and 18.D.3** (`figure_18_D_2`): with `u = √x₁ + √x₂`, `ω₁ = (9/2, 17)`,
  `ω₂ = (41/2, 8)`, the allocation `x*₁ = (9, 9)`, `x*₂ = (16, 16)` is Pareto optimal,
  self-selective and not Walrasian.
* **Exercise 18.D.1** (`exercise_18_D_1`, key step `pref_add_of_pref_endow`): in an Edgeworth
  box with rational strictly convex preferences, every feasible allocation weakly preferred by
  both consumers to their endowments is self-selective with `B = {z*₁, -z*₁}` (continuity and
  monotonicity are not needed).
* **Proposition 18.D.1** (p. 669), the parts that can be made rigorous: the equal-treatment step
  (`proposition_18_D_1_supported_eq`, `proposition_18_D_1_equal_treatment`), the single net
  trade step (`proposition_18_D_1_single_net_trade`), and a corrected main claim for a smooth
  continuum of types `t ∈ [0, 1]` (`proposition_18_D_1_smooth`, `proposition_18_D_1_walrasian`)
  under the regularity the book's proof assumes informally (net trades `z t` continuous on
  `[0, 1]` and differentiable inside, interior bundles, differentiable utilities with gradients
  proportional to the supporting price `p`, no envy among all types, and `0` a convex
  combination of net trades present), with a concrete instance
  (`proposition_18_D_1_instance`). A continuum form with a population measure, in which the
  continuity of `z(t)` is derived, is in `Closer18D` (`proposition_18_D_1_continuum`).

Verbal or graphical: Figure 18.D.1, footnotes 15-19, Figures 18.D.4-18.D.6 (Figure 18.D.4 is a
continuum example with kinked preferences; its finite counterpart is `figure_18_D_2`), and the
discussion of pp. 665-669.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {ι : Type*} {L : ℕ}

/-! ### Definition 18.D.1 -/

/-- **Definition 18.D.1** (MWG, p. 666). The allocation `x*` is self-selective with the
generalized budget set (tax system) `B ⊆ ℝ^L`: for every consumer `i`, the net trade
`z*ᵢ = x*ᵢ - ωᵢ` solves `max uᵢ(zᵢ + ωᵢ)` subject to `zᵢ ∈ B`, `zᵢ + ωᵢ ≥ 0`. -/
def CoreEconomy.IsSelfSelectiveWith (E : CoreEconomy ι L) (x : ι → Fin L → ℝ)
    (B : Set (Fin L → ℝ)) : Prop :=
  ∀ i, x i - E.ω i ∈ B ∧ ∀ z ∈ B, z + E.ω i ∈ nonnegOrthant L → E.pref i (x i) (z + E.ω i)

/-- **Definition 18.D.1** (MWG, p. 666). A feasible allocation is self-selective (anonymous,
envy-free in net trades) if it is self-selective with some generalized budget set `B`. -/
def CoreEconomy.IsSelfSelective [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Prop :=
  E.IsFeasible x ∧ ∃ B, E.IsSelfSelectiveWith x B

/-- No consumer envies the net trade of another (whenever that net trade is feasible for her):
`x*ᵢ ≿ᵢ ωᵢ + z*ₖ` for all `i, k` with `ωᵢ + z*ₖ ≥ 0`. -/
def CoreEconomy.NoEnvyNetTrades (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∀ i k, x k - E.ω k + E.ω i ∈ nonnegOrthant L → E.pref i (x i) (x k - E.ω k + E.ω i)

/-- **Definition 18.D.1** (MWG, p. 666), restated: `z*ᵢ + ωᵢ = x*ᵢ` is maximal for `≿ᵢ` among the
bundles `z + ωᵢ ≥ 0` with `z ∈ B`. -/
theorem definition_18_D_1 (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) (B : Set (Fin L → ℝ))
    (hx : ∀ i, x i ∈ nonnegOrthant L) :
    E.IsSelfSelectiveWith x B ↔
      ∀ i, IsMaximalFor (E.pref i) {y | y ∈ nonnegOrthant L ∧ y - E.ω i ∈ B} (x i) := by
  constructor
  · intro h i
    refine ⟨⟨hx i, (h i).1⟩, fun y ⟨hy, hyB⟩ => ?_⟩
    have := (h i).2 _ hyB (by rwa [sub_add_cancel])
    rwa [sub_add_cancel] at this
  · intro h i
    refine ⟨(h i).1.2, fun z hz hzω => (h i).2 _ ⟨hzω, by rwa [add_sub_cancel_right]⟩⟩

/-- **Section 18.D** (MWG, p. 666), corrected. For a feasible allocation, being self-selective
is equivalent to being self-selective with `B = {z*₁, ..., z*_I}`, the set of the equilibrium
net trades, and to no consumer envying the net trade of another. (The book prints
`B = {x*₁, ..., x*_I}`; see `selfSelective_consumptions_misprint`.) -/
theorem selfSelective_iff_netTrades [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ)
    (hfe : E.IsFeasible x) :
    (E.IsSelfSelective x ↔ E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k)) ∧
      (E.IsSelfSelective x ↔ E.NoEnvyNetTrades x) := by
  have h1 : E.IsSelfSelective x → E.NoEnvyNetTrades x := by
    rintro ⟨-, B, hB⟩ i k hik
    exact (hB i).2 _ (hB k).1 hik
  have h2 : E.NoEnvyNetTrades x → E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k) := by
    intro h i
    refine ⟨⟨i, rfl⟩, ?_⟩
    rintro z ⟨k, rfl⟩ hz
    exact h i k hz
  have h3 : E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k) → E.IsSelfSelective x :=
    fun h => ⟨hfe, _, h⟩
  exact ⟨⟨fun h => h2 (h1 h), h3⟩, ⟨h1, fun h => h3 (h2 h)⟩⟩

/-- The economy of the misprint counterexample: two consumers with utility `√x₁ + √x₂` and
endowments `(1, 1)`. -/
noncomputable def misprintEconomy : CoreEconomy (Fin 2) 2 := sqrtEconomy fun _ => ![1, 1]

/-- **Section 18.D** (MWG, p. 666), the misprint. "It is enough to take `B = {x*₁, ..., x*_I}`"
is false as printed: the no-trade allocation `x* = ω = ((1, 1), (1, 1))` of `misprintEconomy`
is self-selective (with `B = {0}`), but not with `B = {x*₁, x*₂} = {(1, 1)}`, which does not
contain the net trades `z*ᵢ = 0`. The set to take is the set of net trades
(`selfSelective_iff_netTrades`). -/
theorem selfSelective_consumptions_misprint :
    misprintEconomy.IsSelfSelective (fun _ => ![1, 1]) ∧
      ¬ misprintEconomy.IsSelfSelectiveWith (fun _ => ![1, 1])
        (Set.range fun _ : Fin 2 => (![1, 1] : Fin 2 → ℝ)) := by
  refine ⟨⟨⟨fun _ l => by fin_cases l <;> norm_num, 0, fun _ => le_rfl, by
    simp [misprintEconomy, sqrtEconomy]⟩, {0}, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · simp [misprintEconomy, sqrtEconomy]
  · rintro z rfl -
    simp [misprintEconomy, sqrtEconomy, utilityPref]
  · intro h
    obtain ⟨k, hk⟩ := (h 0).1
    have := congrFun hk 0
    simp [misprintEconomy, sqrtEconomy] at this

/-! ### Walrasian allocations (p. 667) -/

/-- **Section 18.D** (MWG, p. 667). A Walrasian allocation with price vector `p` of an economy
with rational, monotone preferences (Definition 3.B.2) and a constant returns technology (e.g.
the exchange case `Y = -ℝ^L₊`) is Pareto optimal (first welfare theorem, Proposition 16.C.1 via
the bridges of `CoreWalras`) and self-selective with `B = {z : p·z = 0}`, and also with
`B = {z : p·z ≤ 0}`: monotonicity makes every budget bind, `p·z*ᵢ = 0`. -/
theorem walras_isParetoOptimal_selfSelective [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    (hL : 0 < L) (hY : IsCRSTechnology E.Y)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefMonotone (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    E.IsParetoOptimal x ∧ E.IsSelfSelectiveWith x {z | p ⬝ᵥ z = 0} ∧
      E.IsSelfSelectiveWith x {z | p ⬝ᵥ z ≤ 0} ∧ E.IsSelfSelective x := by
  have hlns : ∀ i, LocallyNonsatiated (nonnegOrthant L) (E.pref i) :=
    fun i => exercise_3_B_1b_orthant hL (hm i)
  -- Pareto optimality through Chapter 16
  set θ : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ) with hθ
  obtain ⟨y, hy, hpriv⟩ := (isWalrasEqm_iff_toPriv E hY θ x p).mp h
  have hθ1 : ∀ j, ∑ i, (E.toPriv θ).θ i j = 1 := by
    intro j
    simp only [CoreEconomy.toPriv, hθ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    field_simp
  have hpo := proposition_16_C_1_walras (E := E.toPriv θ) (fun i => hr i) (fun i => hlns i) hθ1
    hpriv
  have hPO : E.IsParetoOptimal x := (isParetoOptimal_iff_toPriv E θ x).mpr ⟨y, hpo⟩
  -- budgets bind
  have hbind : ∀ i, p ⬝ᵥ (x i - E.ω i) = 0 := by
    intro i
    have hxi := (h.2 i).1
    have hrefl : E.pref i (x i) (x i) := ((hr i).1 _ hxi.1 _ hxi.1).elim id id
    have hge := exercise_16_C_2 (hlns i) (hr i).2 (h.2 i) hxi.1 hrefl
    rw [dotProduct_sub]
    linarith [hxi.2]
  have hle : E.IsSelfSelectiveWith x {z | p ⬝ᵥ z ≤ 0} := by
    intro i
    refine ⟨le_of_eq (hbind i), fun z hz hzω => (h.2 i).2 _ ⟨hzω, ?_⟩⟩
    have : p ⬝ᵥ z ≤ 0 := hz
    rw [dotProduct_add]
    linarith
  refine ⟨hPO, fun i => ⟨hbind i, fun z hz hzω => (hle i).2 z (le_of_eq hz) hzω⟩, hle,
    hPO.1, _, hle⟩

/-! ### Figures 18.D.2 and 18.D.3: a Pareto optimal, self-selective, non-Walrasian allocation -/

/-- The endowments of the Edgeworth box of `figure_18_D_2`: `ω₁ = (9/2, 17)`, `ω₂ = (41/2, 8)`. -/
noncomputable def fig18D2Endow : Fin 2 → Fin 2 → ℝ := ![![9 / 2, 17], ![41 / 2, 8]]

/-- The allocation `x*₁ = (9, 9)`, `x*₂ = (16, 16)` of `figure_18_D_2`. -/
noncomputable def fig18D2Alloc : Fin 2 → Fin 2 → ℝ := fun i => ![![9, 16] i, ![9, 16] i]

/-- `√(n²) = n` for the small perfect squares used below. -/
theorem fig18D2_sqrt_sq {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha

/-- **Figures 18.D.2 and 18.D.3** (MWG, p. 667). In the Edgeworth box with identical utilities
`√x₁ + √x₂` and endowments `ω₁ = (9/2, 17)`, `ω₂ = (41/2, 8)`, the allocation
`x*₁ = (9, 9)`, `x*₂ = (16, 16)` is Pareto optimal and self-selective (consumer 1 prefers her net
trade `z*₁` to `z*₂`: `ω₁ + z*₂ = (0, 25)` gives utility `5 < 6`; consumer 2 prefers `z*₂` to
`z*₁`: `ω₂ + z*₁ = (25, 0)` gives `5 < 8`), but it is not a Walrasian allocation for any price
vector (the budgets force `p₁ = 16p₂/9`, at which consumer 1 can afford `(81/16, 16)`, worth
`25/4 > 6`, or, if `p₂ ≤ 0`, `(10, 10)`). -/
theorem figure_18_D_2 :
    (sqrtEconomy fig18D2Endow).IsParetoOptimal fig18D2Alloc ∧
      (sqrtEconomy fig18D2Endow).IsSelfSelective fig18D2Alloc ∧
      ¬ (sqrtEconomy fig18D2Endow).IsWalrasAlloc fig18D2Alloc := by
  have hPO : (sqrtEconomy fig18D2Endow).IsParetoOptimal fig18D2Alloc :=
    sqrtEconomy_diag_isParetoOptimal (t := ![9, 16])
      (fun i => by fin_cases i <;> norm_num)
      (by simp [fig18D2Endow, Fin.sum_univ_two]; norm_num)
      (by simp [fig18D2Endow, Fin.sum_univ_two]; norm_num)
  have h3 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  have h4 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  have h5 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  refine ⟨hPO, ?_, ?_⟩
  · refine ((selfSelective_iff_netTrades _ _ hPO.1).2).2 fun i k _ => ?_
    fin_cases i <;> fin_cases k
    · simp [sqrtEconomy, utilityPref]
    · change sqrtU (fig18D2Alloc 1 - fig18D2Endow 1 + fig18D2Endow 0) ≤ sqrtU (fig18D2Alloc 0)
      have e : fig18D2Alloc 1 - fig18D2Endow 1 + fig18D2Endow 0 = ![0, 25] := by
        funext l
        fin_cases l <;> simp [fig18D2Alloc, fig18D2Endow] <;> norm_num
      rw [e, sqrtU_two, sqrtU_two]
      simp [fig18D2Alloc, h3, h5]
      norm_num
    · change sqrtU (fig18D2Alloc 0 - fig18D2Endow 0 + fig18D2Endow 1) ≤ sqrtU (fig18D2Alloc 1)
      have e : fig18D2Alloc 0 - fig18D2Endow 0 + fig18D2Endow 1 = ![25, 0] := by
        funext l
        fin_cases l <;> simp [fig18D2Alloc, fig18D2Endow] <;> norm_num
      rw [e, sqrtU_two, sqrtU_two]
      simp [fig18D2Alloc, h4, h5]
      norm_num
    · simp [sqrtEconomy, utilityPref]
  · rintro ⟨p, -, hx⟩
    have b0 := (hx 0).1.2
    have b1 := (hx 1).1.2
    change p ⬝ᵥ ![9, 9] ≤ p ⬝ᵥ ![9 / 2, 17] at b0
    change p ⬝ᵥ ![16, 16] ≤ p ⬝ᵥ ![41 / 2, 8] at b1
    simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at b0 b1
    have hu : sqrtU (fig18D2Alloc 0) = 6 := by
      change sqrtU ![9, 9] = 6
      rw [sqrtU_vec, h3]
      norm_num
    rcases le_or_gt (p 1) 0 with hp | hp
    · have hb : (![10, 10] : Fin 2 → ℝ) ∈
          budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy fig18D2Endow).ω 0) := by
        refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
        change p ⬝ᵥ ![10, 10] ≤ p ⬝ᵥ ![9 / 2, 17]
        simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      have := (hx 0).2 _ hb
      change sqrtU ![10, 10] ≤ sqrtU (fig18D2Alloc 0) at this
      rw [hu, sqrtU_vec] at this
      have : (3 : ℝ) < Real.sqrt 10 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    · have hb : (![81 / 16, 16] : Fin 2 → ℝ) ∈
          budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy fig18D2Endow).ω 0) := by
        refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
        change p ⬝ᵥ ![81 / 16, 16] ≤ p ⬝ᵥ ![9 / 2, 17]
        simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      have := (hx 0).2 _ hb
      change sqrtU ![81 / 16, 16] ≤ sqrtU (fig18D2Alloc 0) at this
      rw [hu, sqrtU_vec, h4] at this
      have h94 : Real.sqrt (81 / 16) = 9 / 4 := by
        rw [show (81 / 16 : ℝ) = (9 / 4) ^ 2 by norm_num]
        exact fig18D2_sqrt_sq (by norm_num)
      rw [h94] at this
      norm_num at this

/-! ### Exercise 18.D.1 -/

/-- The key step of Exercise 18.D.1: with rational, strictly convex preferences on `ℝ^L₊`, if
`ω + z ≿ ω` then `ω + z ≿ ω - z` (when `ω - z ≥ 0`). Otherwise `ω - z ≻ ω + z`, the two bundles
differ, and strict convexity gives `ω = ½(ω - z) + ½(ω + z) ≻ ω + z`, a contradiction. -/
theorem pref_add_of_pref_endow {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {ω z : Fin L → ℝ} (hp : ω + z ∈ nonnegOrthant L)
    (hm : ω - z ∈ nonnegOrthant L) (hir : r (ω + z) ω) : r (ω + z) (ω - z) := by
  by_contra hne
  have hrev : r (ω - z) (ω + z) := ((hr.1 _ hp _ hm).resolve_left hne)
  have hrefl : r (ω + z) (ω + z) := (hr.1 _ hp _ hp).elim id id
  have hdiff : ω - z ≠ ω + z := by
    intro h
    rw [h] at hne
    exact hne hrefl
  have := hsc _ hp _ hm _ hp hrev hrefl hdiff (1 / 2) (by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (ω - z) + (1 - 1 / 2 : ℝ) • (ω + z) = ω := by
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hmid] at this
  exact this.2 hir

/-- **Exercise 18.D.1** (MWG, p. 685). In an Edgeworth box (two consumers, exact feasibility
`x₁ + x₂ = ω₁ + ω₂`) with rational, strictly convex preferences, every feasible allocation that
leaves both consumers at least as well off as at their endowments is self-selective, with the
generalized budget set `B = {z*₁, -z*₁} = {z*₁, z*₂}`. (Continuity and monotonicity, assumed in
the exercise, are not needed, nor is `ωᵢ ≥ 0`.) -/
theorem exercise_18_D_1 (E : CoreEconomy (Fin 2) L) (h0Y : (0 : Fin L → ℝ) ∈ E.Y)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) {x : Fin 2 → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (hsum : x 0 + x 1 = E.ω 0 + E.ω 1)
    (hir : ∀ i, E.pref i (x i) (E.ω i)) :
    E.IsSelfSelectiveWith x {x 0 - E.ω 0, -(x 0 - E.ω 0)} ∧ E.IsSelfSelective x := by
  have hz1 : x 1 - E.ω 1 = -(x 0 - E.ω 0) := by
    funext l
    have := congrFun hsum l
    simp only [Pi.add_apply] at this
    simp only [Pi.sub_apply, Pi.neg_apply]
    linarith
  have hrefl : ∀ i, E.pref i (x i) (x i) := fun i => ((hr i).1 _ (hx i) _ (hx i)).elim id id
  have hB : E.IsSelfSelectiveWith x {x 0 - E.ω 0, -(x 0 - E.ω 0)} := by
    intro i
    fin_cases i
    · refine ⟨Set.mem_insert _ _, fun z hz hzω => ?_⟩
      rcases hz with rfl | hz
      · simpa using hrefl 0
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        have hp : E.ω 0 + (x 0 - E.ω 0) ∈ nonnegOrthant L := by simpa using hx 0
        have hm : E.ω 0 - (x 0 - E.ω 0) ∈ nonnegOrthant L := by
          rwa [sub_eq_neg_add]
        have := pref_add_of_pref_endow (hr 0) (hsc 0) hp hm (by simpa using hir 0)
        simpa [sub_eq_neg_add] using this
    · refine ⟨by simp [hz1], fun z hz hzω => ?_⟩
      rcases hz with rfl | hz
      · have hm : E.ω 1 - (x 1 - E.ω 1) ∈ nonnegOrthant L := by
          rw [hz1, sub_neg_eq_add, add_comm]
          exact hzω
        have hp : E.ω 1 + (x 1 - E.ω 1) ∈ nonnegOrthant L := by simpa using hx 1
        have := pref_add_of_pref_endow (hr 1) (hsc 1) hp hm (by simpa using hir 1)
        simp only [add_sub_cancel] at this
        rw [hz1, sub_neg_eq_add, add_comm] at this
        exact this
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [← hz1]
        simpa using hrefl 1
  refine ⟨hB, ⟨hx, 0, h0Y, ?_⟩, _, hB⟩
  rw [zero_add, Fin.sum_univ_two, Fin.sum_univ_two, hsum]

/-! ### Proposition 18.D.1: the rigorous steps -/

/-- **Proposition 18.D.1**, proof, equal-treatment step (MWG, p. 669). With rational, strictly
convex preferences on `ℝ^L₊`, two bundles on the same indifference curve that are both
supported by the same price vector `p` (each maximal in its own budget `{y ≥ 0 : p·y ≤ p·x}`)
are equal: otherwise their midpoint is strictly preferred and affordable for one of them. -/
theorem proposition_18_D_1_supported_eq {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {p x x' : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hx' : x' ∈ nonnegOrthant L)
    (hmax : IsMaximalFor r (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x)) x)
    (hmax' : IsMaximalFor r (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x')) x')
    (hxx' : r x x') (hx'x : r x' x) : x = x' := by
  by_contra hne
  have hrefl : r x x := (hr.1 _ hx _ hx).elim id id
  have hs := hsc _ hx _ hx _ hx' hrefl hx'x hne (1 / 2) (by norm_num) (by norm_num)
  set m := (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • x' with hm
  have hmX : m ∈ nonnegOrthant L := fun l => by
    simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx l, hx' l]
  have hpm : p ⬝ᵥ m = (p ⬝ᵥ x + p ⬝ᵥ x') / 2 := by
    rw [hm, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rcases le_total (p ⬝ᵥ x) (p ⬝ᵥ x') with h | h
  · have := hmax'.2 m ⟨hmX, by rw [hpm]; linarith⟩
    exact hs.2 (hr.2 _ hx _ hx' _ hmX hxx' this)
  · exact hs.2 (hmax.2 m ⟨hmX, by rw [hpm]; linarith⟩)

/-- **Proposition 18.D.1**, proof, equal treatment (MWG, p. 669). If consumers `i` and `k` have
the same preferences and endowments, the allocation has no envy in net trades, and a common
price vector `p` supports every consumer's bundle (a price equilibrium with transfers), then
`x*ᵢ = x*ₖ`. -/
theorem proposition_18_D_1_equal_treatment (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (henvy : E.NoEnvyNetTrades x) {p : Fin L → ℝ}
    (hsupp : ∀ i, IsMaximalFor (E.pref i) (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x i)) (x i))
    {i k : ι} (hpref : E.pref i = E.pref k) (hω : E.ω i = E.ω k) : x i = x k := by
  have h1 : E.pref i (x i) (x k) := by
    have := henvy i k (by rw [hω, sub_add_cancel]; exact hx k)
    rwa [hω, sub_add_cancel] at this
  have h2 : E.pref k (x k) (x i) := by
    have := henvy k i (by rw [← hω, sub_add_cancel]; exact hx i)
    rwa [← hω, sub_add_cancel] at this
  rw [← hpref] at h2
  have hsk := hsupp k
  rw [← hpref] at hsk
  exact proposition_18_D_1_supported_eq (hr i) (hsc i) (hx i) (hx k) (hsupp i) hsk h1 h2

/-- **Proposition 18.D.1**, proof (MWG, p. 669). If all consumers have the same net trade and
the net trades add up to zero (`∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`), the common net trade is `0`. -/
theorem proposition_18_D_1_single_net_trade [Fintype ι] [Nonempty ι] {x ω : ι → Fin L → ℝ}
    (hsum : ∑ i, x i = ∑ i, ω i) (hz : ∀ i k, x i - ω i = x k - ω k) (i : ι) :
    x i - ω i = 0 := by
  have h : ∑ k, (x k - ω k) = (Fintype.card ι : ℝ) • (x i - ω i) := by
    rw [Finset.sum_congr rfl fun k _ => hz k i, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  rw [Finset.sum_sub_distrib, hsum, sub_self] at h
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- **Proposition 18.D.1** (MWG, p. 669), a rigorous version of the main step for a smooth
continuum of types. Types are `t ∈ [0, 1]`, with utilities `u t`, endowments `ω t` and net trades
`z t`. Assume (the regularity the book's proof takes for granted) that `t ↦ z t` is continuous
on `[0, 1]` and differentiable on `(0, 1)`; that the allocation is interior and has no envy in
net trades (no type prefers another type's net trade); that every `u t` is differentiable at the
type's bundle with gradient proportional to `p` (`D t v = μ t (p·v)`, `μ t ≠ 0`); and that the
net trades add up to zero in the sense that `0` is a convex combination of net trades present in
the economy. Then `p·z t = 0` for every type: the first-order condition of no envy makes the
derivative of `t ↦ p·z t` vanish, so `p·z t` is constant, and aggregate feasibility makes the
constant zero. -/
theorem proposition_18_D_1_smooth {u : ℝ → (Fin L → ℝ) → ℝ} {ω z z' : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) →L[ℝ] ℝ} {μ : ℝ → ℝ}
    (hzc : ContinuousOn z (Set.Icc 0 1)) (hzd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) (D t) (ω t + z t))
    (hgrad : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ v, D t v = μ t * (p ⬝ᵥ v))
    (hμ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, μ t ≠ 0) {n : ℕ} {τ w : Fin n → ℝ}
    (hτ : ∀ k, τ k ∈ Set.Icc (0 : ℝ) 1) (hw1 : ∑ k, w k = 1)
    (hagg : ∑ k, w k • z (τ k) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = 0 := by
  -- the first-order condition of no envy
  have hfoc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, p ⬝ᵥ z' t = 0 := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self ht
    have hzt : ContinuousAt z t := (hzd t ht).continuousAt
    have hpos : ∀ l, ∀ᶠ s in nhds t, 0 < ω t l + z s l := by
      intro l
      have hcont : ContinuousAt (fun s => ω t l + z s l) t :=
        continuousAt_const.add ((continuous_apply l).continuousAt.comp hzt)
      exact continuousAt_const.eventually_lt hcont (hint t htI l)
    have hloc : IsLocalMax (fun s => u t (ω t + z s)) t := by
      filter_upwards [Filter.eventually_all.mpr hpos, isOpen_Ioo.mem_nhds ht] with s hs hsI
      exact henvy t htI s (Set.Ioo_subset_Icc_self hsI) fun l => (hs l).le
    have hder : HasDerivAt (fun s => u t (ω t + z s)) (D t (z' t)) t :=
      (hD t ht).comp_hasDerivAt (f := fun s => ω t + z s) t ((hzd t ht).const_add (ω t))
    have := hloc.hasDerivAt_eq_zero hder
    rw [hgrad t ht] at this
    exact (mul_eq_zero.mp this).resolve_left (hμ t ht)
  -- `t ↦ p·z t` has derivative `p·z' t` on `(0, 1)`
  have hderf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => p ⬝ᵥ z s) (p ⬝ᵥ z' t) t := by
    intro t ht
    have hl : ∀ l ∈ Finset.univ, HasDerivAt (fun s => p l * z s l) (p l * z' t l) t :=
      fun l _ => (hasDerivAt_pi.mp (hzd t ht) l).const_mul (p l)
    exact HasDerivAt.fun_sum hl
  have hcontf : ContinuousOn (fun s => p ⬝ᵥ z s) (Set.Icc 0 1) := by
    have : ∀ l ∈ Finset.univ, ContinuousOn (fun s => p l * z s l) (Set.Icc 0 1) :=
      fun l _ => continuousOn_const.mul ((continuous_apply l).comp_continuousOn hzc)
    exact continuousOn_finsetSum _ this
  -- hence `p·z t = p·z 0` on `[0, 1]`
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = p ⬝ᵥ z 0 := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => p ⬝ᵥ z s)
        (fun s => p ⬝ᵥ z' s) h0 (hcontf.mono (Set.Icc_subset_Icc_right ht.2))
        fun s hs => hderf s ⟨hs.1, hs.2.trans_le ht.2⟩
      have hc0 : p ⬝ᵥ z' c = 0 := hfoc c ⟨hc.1, hc.2.trans_le ht.2⟩
      rw [hc0, eq_comm, div_eq_zero_iff] at hslope
      rcases hslope with h | h
      · linarith
      · linarith
  -- aggregate feasibility makes the constant zero
  have h0 : p ⬝ᵥ z 0 = 0 := by
    have := congrArg (fun v => p ⬝ᵥ v) hagg
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at this
    rw [Finset.sum_congr rfl fun k _ => by rw [hconst (τ k) (hτ k)], ← Finset.sum_mul,
      hw1, one_mul] at this
    exact this
  intro t ht
  rw [hconst t ht, h0]

/-- **Proposition 18.D.1** (MWG, p. 669), conclusion. Under the hypotheses of
`proposition_18_D_1_smooth`, if moreover `p` supports every type's bundle as a price equilibrium
with transfers (`x t = ω t + z t` is best among `y ≥ 0` with `p·y ≤ p·x t`, as `p` does for a
Pareto optimal allocation), then every type's bundle is her Walrasian demand at `p`: the
allocation is a Walrasian equilibrium allocation. -/
theorem proposition_18_D_1_walrasian {u : ℝ → (Fin L → ℝ) → ℝ} {ω z z' : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) →L[ℝ] ℝ} {μ : ℝ → ℝ}
    (hzc : ContinuousOn z (Set.Icc 0 1)) (hzd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) (D t) (ω t + z t))
    (hgrad : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ v, D t v = μ t * (p ⬝ᵥ v))
    (hμ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, μ t ≠ 0) {n : ℕ} {τ w : Fin n → ℝ}
    (hτ : ∀ k, τ k ∈ Set.Icc (0 : ℝ) 1) (hw1 : ∑ k, w k = 1)
    (hagg : ∑ k, w k • z (τ k) = 0)
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t ∧
      ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ ω t → u t y ≤ u t (ω t + z t) := by
  have h := proposition_18_D_1_smooth hzc hzd hint henvy hD hgrad hμ hτ hw1 hagg
  intro t ht
  have he : p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t := by rw [dotProduct_add, h t ht, add_zero]
  exact ⟨he, fun y hy hpy => hsupp t ht y hy (he ▸ hpy)⟩

/-- The linear utility `x₁ + x₂` of the instance of Proposition 18.D.1, as a continuous linear
map. -/
noncomputable def prop18D1D : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

/-- **Proposition 18.D.1**, a concrete instance of the hypotheses (MWG, Figure 18.D.6): types
`t ∈ [0, 1]` with utility `x₁ + x₂`, endowments `ω t = (2t, 2 - 2t)` and net trades
`z t = (1 - 2t, 2t - 1)` (every type consumes `(1, 1)`), `p = (1, 1)`, and aggregate net trade
`½ z 0 + ½ z 1 = 0`; all hypotheses of `proposition_18_D_1_walrasian` hold. -/
theorem proposition_18_D_1_instance :
    let u : ℝ → (Fin 2 → ℝ) → ℝ := fun _ => prop18D1D
    let ω : ℝ → Fin 2 → ℝ := fun t => ![2 * t, 2 - 2 * t]
    let z : ℝ → Fin 2 → ℝ := fun t => ![1 - 2 * t, 2 * t - 1]
    let p : Fin 2 → ℝ := ![1, 1]
    ContinuousOn z (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z ![-2, 2] t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant 2 →
        u t (ω t + z s) ≤ u t (ω t + z t)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) prop18D1D (ω t + z t)) ∧
      (∀ v, prop18D1D v = 1 * (p ⬝ᵥ v)) ∧
      (∑ k : Fin 2, ![1 / 2, 1 / 2] k • z (![0, 1] k) = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
        u t y ≤ u t (ω t + z t)) := by
  intro u ω z p
  have hD : ∀ v, prop18D1D v = v 0 + v 1 := fun v => by simp [prop18D1D]
  have hz : Continuous z := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_const.sub (continuous_const.mul continuous_id)
    · exact (continuous_const.mul continuous_id).sub continuous_const
  refine ⟨hz.continuousOn, fun t _ => ?_, fun t _ l => ?_, fun t _ s _ _ => ?_,
    fun t _ => prop18D1D.hasFDerivAt, fun v => ?_, ?_, fun t _ y _ hy => ?_⟩
  · refine hasDerivAt_pi.mpr fun l => ?_
    fin_cases l
    · have := ((hasDerivAt_id t).const_mul 2).const_sub 1
      simpa [z] using this
    · have := ((hasDerivAt_id t).const_mul 2).sub_const 1
      simpa [z] using this
  · fin_cases l <;> simp [ω, z]
  · simp only [u, hD]
    simp [ω, z]
    linarith
  · rw [hD, dot_two]
    simp [p]
  · funext l
    fin_cases l <;> simp [z]
  · simp only [u, hD]
    rw [dot_two, dot_two] at hy
    simpa [p] using hy

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equilibrium and the marginal productivity principle (MWG Section 18.E, pp. 670-673)

The quasilinear exchange economy of Section 18.E: `H` types, bundles `x = (y, m)` with
`y ∈ ℝ^K₊` (the `K = L - 1` non-numeraire goods) and money `m ∈ ℝ`, utilities
`u_h(y, m) = ψ_h(y) + m`, endowments `ω_h`. For a population `μ ∈ ℝ^H₊`,
`v(μ) = sup {∑ μ_h u_h(x_h) : ∑ μ_h x_h ≤ ∑ μ_h ω_h, y_h ≥ 0}` (18.E.1)/(18.E.2) (`QLEconomy.v`,
defined with `sSup`).

Proved here (examples and Exercise 18.E.3 are in `MarginalProductExamples`):
* homogeneity of `v` (p. 670) for every `r ≥ 0`, unconditionally, and `v(I/I) = v(I)/I`;
* finiteness: an affine majorant bounds `v` (`QLEconomy.v_le_of_majorant`), and concave,
  nondecreasing `ψ_h` differentiable at some point of `ℝ^K₊` admit one
  (`QLEconomy.exists_majorant`);
* **Exercise 18.E.1**: `v` is superadditive, concave and homogeneous of degree one on `ℝ^H₊`;
* **Footnote 20**: averaging within a type keeps feasibility and does not lower the objective, so
  the supremum over unequal allocations of a finite economy equals (18.E.1);
* **Definition 18.E.1** (with footnote 22 built in) and the Walrasian equilibrium of the
  continuum population;
* Euler's formula (`ql_euler`, Section M.B) by differentiating `t ↦ v(tμ)` at `t = 1`;
* **Proposition 18.E.1** (`proposition_18_E_1`), with **(18.E.4)** (`supporting_prices`) and
  **(18.E.5)** = **Exercise 18.E.2** (`exercise_18_E_2`);
* the finite-economy claims of p. 672: `Δ_h v ≥ ∂v/∂μ_h`, `∑ I_h Δ_h v ≥ v(I)`, impossibility of
  paying every consumer her marginal contribution (equal and unequal treatment), and the
  characterisation of Walrasian allocations of a finite economy by `u_h(x*_h) = ∂v(I)/∂μ_h`.

Departures. The multipliers (18.E.4) are obtained from first-order conditions for transfers of a
good between two types and for a surplus (not from Section M.K), and (18.E.5) from
`v(ν) ≤ ∑ ν_h [u_h(x*_h) + p·(ω_h - x*_h)]` on `ℝ^H₊` with equality at `μ` (not from the
envelope theorem of Section M.L). Hypotheses used are weaker than the book's: `ψ_h` concave and
nondecreasing (not strictly), differentiable only at `y*_h`; `v` differentiable only at `μ`;
`x* ≫ 0` only through `y* ≫ 0`; `ω_h ≥ 0` only for the non-numeraire goods. `v` is defined
with `sSup`; the book's "Max" is attained wherever an optimal allocation exists (e.g. at a
Walrasian allocation).
-/

namespace MWG.CoreFoundations

open Filter Topology

/-- **Section 18.E** (MWG, p. 670). A quasilinear exchange economy with types `h : H`: bundles
are pairs `(y, m)` with `y : Fin K → ℝ` the non-numeraire goods and `m ∈ ℝ` the numeraire (good
`L`); `u_h(y, m) = ψ_h(y) + m`; `ω h` is the endowment of type `h`. -/
structure QLEconomy (H : Type*) (K : ℕ) where
  /-- The functions `ψ_h` of the non-numeraire goods. -/
  ψ : H → (Fin K → ℝ) → ℝ
  /-- Endowments `ω_h = (ω_h^y, ω_h^m)`. -/
  ω : H → (Fin K → ℝ) × ℝ

variable {H : Type*} {K : ℕ}

/-- **Section 18.E** (MWG, p. 670). The quasilinear utility `u_h(y, m) = ψ_h(y) + m`. -/
def QLEconomy.u (E : QLEconomy H K) (h : H) (x : (Fin K → ℝ) × ℝ) : ℝ := E.ψ h x.1 + x.2

/-- **Section 18.E** (MWG, pp. 671-672). The value `p·x = q·y + m` of the bundle `x = (y, m)` at
the price vector `p = (q, 1)` (the numeraire has price `1`). -/
def qlPrice (q : Fin K → ℝ) (x : (Fin K → ℝ) × ℝ) : ℝ := q ⬝ᵥ x.1 + x.2

/-- **(18.E.2)** constraints and **footnote 22** (MWG, pp. 671). An equal-treatment allocation
`x` (one bundle per type) is feasible for the population `μ`: (ii) `y_h ≥ 0` for all `h`, and
(i) `∑_h μ_h x_h ≤ ∑_h μ_h ω_h`. -/
def QLEconomy.IsFeasible [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  (∀ h, 0 ≤ (x h).1) ∧ ∑ h, μ h • x h ≤ ∑ h, μ h • E.ω h

/-- **(18.E.2)** (MWG, p. 671). The objective `∑_h μ_h u_h(x_h)`. -/
def QLEconomy.welfare [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : ℝ :=
  ∑ h, μ h * E.u h (x h)

/-- **(18.E.2)** (MWG, p. 671). The set of values of the objective over feasible allocations. -/
def QLEconomy.valueSet [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) : Set ℝ :=
  {s | ∃ x, E.IsFeasible μ x ∧ E.welfare μ x = s}

/-- **(18.E.1)/(18.E.2)** (MWG, pp. 670-671). The maximal social utility
`v(μ) = sup {∑ μ_h u_h(x_h) : x feasible for μ}` (a `sSup`; it is a maximum whenever an
allocation attains it, `QLEconomy.IsOptimal`). -/
noncomputable def QLEconomy.v [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) : ℝ :=
  sSup (E.valueSet μ)

/-- **(18.E.2)** (MWG, p. 671). `x` solves problem (18.E.2) for `μ`. -/
def QLEconomy.IsOptimal [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ x', E.IsFeasible μ x' → E.welfare μ x' ≤ E.welfare μ x

/-- **Definition 18.E.1** (MWG, p. 671). A feasible allocation `x*` for the population `μ` is a
marginal product (no-surplus) allocation: `u_h(x*_h) = ∂v(μ)/∂μ_h` for all `h` (18.E.3). The
partial derivatives are those of the Fréchet derivative; the book assumes `v` differentiable
(footnote 21), and every result below using this definition takes `DifferentiableAt ℝ E.v μ`. -/
def QLEconomy.IsMarginalProduct [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ h, E.u h (x h) = fderiv ℝ E.v μ (Pi.single h 1)

/-- **Section 18.E** (MWG, pp. 671-672). A Walrasian equilibrium of the continuum population
`μ` with non-numeraire prices `q` (numeraire price `1`): the allocation is feasible as in
footnote 22, and each `x*_h` maximizes `u_h` on the budget set
`{x : y ≥ 0, q·y + m ≤ q·ω_h^y + ω_h^m}`. -/
def QLEconomy.IsWalrasEqm [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) (q : Fin K → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ h, qlPrice q (x h) ≤ qlPrice q (E.ω h) ∧
    ∀ x' : (Fin K → ℝ) × ℝ, 0 ≤ x'.1 → qlPrice q x' ≤ qlPrice q (E.ω h) →
      E.u h x' ≤ E.u h (x h)

/-! ### The price functional -/

/-- The price functional is linear in aggregates: `p·∑ μ_h x_h = ∑ μ_h p·x_h`. -/
theorem qlPrice_sum [Fintype H] (q : Fin K → ℝ) (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ) :
    qlPrice q (∑ h, μ h • x h) = ∑ h, μ h * qlPrice q (x h) := by
  simp only [qlPrice, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib]

/-- The price functional of a difference. -/
theorem qlPrice_sub (q : Fin K → ℝ) (x x' : (Fin K → ℝ) × ℝ) :
    qlPrice q (x - x') = qlPrice q x - qlPrice q x' := by
  simp only [qlPrice, Prod.fst_sub, Prod.snd_sub, dotProduct_sub]
  ring

/-- With `q ≥ 0` the price functional is monotone. -/
theorem qlPrice_mono {q : Fin K → ℝ} (hq : 0 ≤ q) {x x' : (Fin K → ℝ) × ℝ} (h : x ≤ x') :
    qlPrice q x ≤ qlPrice q x' := by
  unfold qlPrice
  have h1 : q ⬝ᵥ x.1 ≤ q ⬝ᵥ x'.1 := dotProduct_le_dotProduct_of_nonneg_left h.1 hq
  linarith [h.2]

/-! ### Upper bounds and finiteness of `v` -/

/-- The endowment allocation is feasible when `ω_h^y ≥ 0`, so the value set is nonempty. -/
theorem QLEconomy.valueSet_nonempty [Fintype H] (E : QLEconomy H K)
    (hω : ∀ h, 0 ≤ (E.ω h).1) (μ : H → ℝ) : (E.valueSet μ).Nonempty :=
  ⟨_, E.ω, ⟨hω, le_rfl⟩, rfl⟩

/-- If every `u_h` is majorised on `{y ≥ 0}` by `c_h + p·x` with `p = (q, 1)`, `q ≥ 0`, then the
objective of every feasible allocation for `μ ≥ 0` is at most `∑ μ_h c_h + p·∑ μ_h ω_h`. -/
theorem QLEconomy.welfare_le_of_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) {x : H → (Fin K → ℝ) × ℝ}
    (hx : E.IsFeasible μ x) :
    E.welfare μ x ≤ ∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h) := by
  have h1 : E.welfare μ x ≤ ∑ h, μ h * (c h + qlPrice q (x h)) :=
    Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hmaj h (x h) (hx.1 h)) (hμ h)
  have h2 : ∑ h, μ h * (c h + qlPrice q (x h)) =
      ∑ h, μ h * c h + qlPrice q (∑ h, μ h • x h) := by
    rw [qlPrice_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have h3 := qlPrice_mono hq hx.2
  linarith

/-- Under an affine majorant, `v(μ) ≤ ∑ μ_h c_h + p·∑ μ_h ω_h` for `μ ≥ 0`. -/
theorem QLEconomy.v_le_of_majorant [Fintype H] (E : QLEconomy H K)
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q)
    (c : H → ℝ) (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) :
    E.v μ ≤ ∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h) := by
  refine csSup_le (E.valueSet_nonempty hω μ) ?_
  rintro s ⟨x, hx, rfl⟩
  exact E.welfare_le_of_majorant hμ hq c hmaj hx

/-- Under an affine majorant the value set is bounded above for every `μ ≥ 0`. -/
theorem QLEconomy.bddAbove_of_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) : BddAbove (E.valueSet μ) := by
  refine ⟨∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h), ?_⟩
  rintro s ⟨x, hx, rfl⟩
  exact E.welfare_le_of_majorant hμ hq c hmaj hx

/-- A continuous linear functional on `ι → ℝ` is `z ↦ ∑ᵢ zᵢ D(eᵢ)`. -/
theorem ql_clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) : D z = ∑ i, z i * D (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (z i) = z i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

/-- The line `t ↦ z + t • d` has derivative `D d` under `f` when `f` has derivative `D` at
`z`. -/
theorem ql_hasDerivAt_line {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : E' → ℝ} {D : E' →L[ℝ] ℝ} {z : E'} (hf : HasFDerivAt f D z) (d : E') :
    HasDerivAt (fun t : ℝ => f (z + t • d)) (D d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have h2 : HasFDerivAt f D (z + (0 : ℝ) • d) := by simpa using hf
  exact h2.comp_hasDerivAt 0 h1

/-- The derivative of a function nondecreasing on `ℝ^K₊`, at a point `z ≥ 0`, is nonnegative
in every coordinate direction. -/
theorem ql_fderiv_single_nonneg {f : (Fin K → ℝ) → ℝ} {D : (Fin K → ℝ) →L[ℝ] ℝ}
    {z : Fin K → ℝ} (hmono : MonotoneOn f (Set.Ici 0)) (hz : 0 ≤ z) (hf : HasFDerivAt f D z)
    (l : Fin K) : 0 ≤ D (Pi.single l 1) := by
  have hslope := (ql_hasDerivAt_line hf (Pi.single l 1)).tendsto_slope_zero_right
  refine ge_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hle : z ≤ z + t • (Pi.single l 1 : Fin K → ℝ) := by
    intro k
    have : 0 ≤ t * (Pi.single l (1 : ℝ) : Fin K → ℝ) k := by
      rcases eq_or_ne k l with rfl | hk
      · simp [ht.le]
      · simp [hk]
    simpa using this
  have hmon := hmono (Set.mem_Ici.2 hz) (Set.mem_Ici.2 (hz.trans hle)) hle
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 ht.le) (by linarith)

/-- **Section 18.E** (MWG, p. 670): finiteness of the supremum. If each `ψ_h` is concave and
nondecreasing on `ℝ^K₊` and differentiable at some `z_h ≥ 0`, then all `u_h` share an affine
majorant `c_h + q·y + m` with `q ≥ 0` (tangent planes, with `q` the sum of the gradients). -/
theorem QLEconomy.exists_majorant [Finite H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hdiff : ∀ h, ∃ z, 0 ≤ z ∧ DifferentiableAt ℝ (E.ψ h) z) :
    ∃ q : Fin K → ℝ, 0 ≤ q ∧ ∃ c : H → ℝ, ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x := by
  have : Fintype H := Fintype.ofFinite H
  choose z hz hdz using hdiff
  set D := fun h => fderiv ℝ (E.ψ h) (z h)
  have hD : ∀ h, HasFDerivAt (E.ψ h) (D h) (z h) := fun h => (hdz h).hasFDerivAt
  have hg : ∀ h l, 0 ≤ D h (Pi.single l 1) := fun h l =>
    ql_fderiv_single_nonneg (hmono h) (hz h) (hD h) l
  refine ⟨fun l => ∑ h, D h (Pi.single l 1), fun l => Finset.sum_nonneg fun h _ => hg h l,
    fun h => E.ψ h (z h) - D h (z h), fun h x hx => ?_⟩
  have ht := MWG.WelfareTheorems.concaveOn_le_tangent (hconc h) (Set.mem_Ici.2 (hz h))
    (Set.mem_Ici.2 hx) (hD h)
  rw [map_sub] at ht
  have hle : D h x.1 ≤ (fun l => ∑ k, D k (Pi.single l 1)) ⬝ᵥ x.1 := by
    rw [ql_clm_apply_eq_sum, dotProduct]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [mul_comm (x.1 l)]
    refine mul_le_mul_of_nonneg_right ?_ (hx l)
    exact Finset.single_le_sum (f := fun k => D k (Pi.single l 1)) (fun k _ => hg k l)
      (Finset.mem_univ h)
  simp only [QLEconomy.u, qlPrice]
  linarith

/-! ### Homogeneity (p. 670) -/

open Pointwise in
/-- Scaling the population by `r > 0` scales the value set. -/
theorem QLEconomy.valueSet_smul [Fintype H] (E : QLEconomy H K) {r : ℝ} (hr : 0 < r)
    (μ : H → ℝ) : E.valueSet (r • μ) = r • E.valueSet μ := by
  ext s
  constructor
  · rintro ⟨x, ⟨hx0, hx⟩, rfl⟩
    refine ⟨E.welfare μ x, ⟨x, ⟨hx0, ?_⟩, rfl⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum] at hx
      exact (smul_le_smul_iff_of_pos_left hr).1 hx
    · simp only [QLEconomy.welfare, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · rintro ⟨t, ⟨x, ⟨hx0, hx⟩, rfl⟩, rfl⟩
    refine ⟨x, ⟨hx0, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum]
      exact (smul_le_smul_iff_of_pos_left hr).2 hx
    · simp only [QLEconomy.welfare, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `v(0) = 0`. -/
theorem QLEconomy.v_zero [Fintype H] (E : QLEconomy H K) : E.v 0 = 0 := by
  have : E.valueSet 0 = {0} := by
    ext s
    constructor
    · rintro ⟨x, -, rfl⟩
      simp [QLEconomy.welfare]
    · rintro rfl
      exact ⟨0, ⟨fun _ => le_rfl, by simp⟩, by simp [QLEconomy.welfare]⟩
  rw [QLEconomy.v, this, csSup_singleton]

open Pointwise in
/-- **Section 18.E** (MWG, p. 670). `v` is homogeneous of degree one:
`v(r μ) = r v(μ)` for every `r ≥ 0` (no assumption needed: the value set scales). -/
theorem QLEconomy.v_smul [Fintype H] (E : QLEconomy H K) {r : ℝ} (hr : 0 ≤ r) (μ : H → ℝ) :
    E.v (r • μ) = r * E.v μ := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [zero_smul, zero_mul, E.v_zero]
  · rw [QLEconomy.v, E.valueSet_smul hr, Real.sSup_smul_of_nonneg hr.le, smul_eq_mul,
      QLEconomy.v]

/-- **Section 18.E** (MWG, p. 670). `v(I₁/I, …, I_H/I) = v(I₁, …, I_H)/I` for `I > 0`. -/
theorem QLEconomy.v_div [Fintype H] (E : QLEconomy H K) (I : H → ℝ) {N : ℝ} (hN : 0 < N) :
    E.v (fun h => I h / N) = E.v I / N := by
  have : (fun h => I h / N) = N⁻¹ • I := by
    ext h; simp [div_eq_inv_mul]
  rw [this, E.v_smul (inv_nonneg.2 hN.le), inv_mul_eq_div]

/-! ### Exercise 18.E.1: concavity -/

/-- The set `{x : y ≥ 0}` of bundles is convex. -/
theorem ql_convex_bundles : Convex ℝ {x : (Fin K → ℝ) × ℝ | 0 ≤ x.1} := by
  intro x hx y hy a b ha hb _
  change 0 ≤ (a • x + b • y).1
  simp only [Prod.fst_add, Prod.smul_fst]
  exact add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)

/-- `u_h(y, m) = ψ_h(y) + m` is concave on `{y ≥ 0}` when `ψ_h` is concave on `ℝ^K₊`. -/
theorem QLEconomy.u_concaveOn (E : QLEconomy H K) {h : H}
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) :
    ConcaveOn ℝ {x : (Fin K → ℝ) × ℝ | 0 ≤ x.1} (E.u h) := by
  refine ⟨ql_convex_bundles, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hconc.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) ha hb hab
  simp only [QLEconomy.u, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h1 ⊢
  linarith

/-- **Exercise 18.E.1** (MWG, p. 671), superadditivity: for `μ, ν ≥ 0`,
`v(μ) + v(ν) ≤ v(μ + ν)` (given bounded value sets and `ω_h^y ≥ 0`). Each type's bundle in the
merged population is the population-weighted average, which is feasible, and concavity of `u_h`
does the rest. -/
theorem QLEconomy.v_superadditive [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hω : ∀ h, 0 ≤ (E.ω h).1)
    (hbdd : ∀ μ : H → ℝ, 0 ≤ μ → BddAbove (E.valueSet μ)) {μ ν : H → ℝ} (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) : E.v μ + E.v ν ≤ E.v (μ + ν) := by
  have hμh : ∀ h, 0 ≤ μ h := fun h => hμ h
  have hνh : ∀ h, 0 ≤ ν h := fun h => hν h
  -- the key inequality for a pair of allocations
  have key : ∀ x x', E.IsFeasible μ x → E.IsFeasible ν x' →
      E.welfare μ x + E.welfare ν x' ≤ E.v (μ + ν) := by
    intro x x' hx hx'
    classical
    let s : H → ℝ := fun h => μ h + ν h
    let z : H → (Fin K → ℝ) × ℝ := fun h =>
      if s h = 0 then 0 else ((s h)⁻¹ * μ h) • x h + ((s h)⁻¹ * ν h) • x' h
    have hz : ∀ h, s h • z h = μ h • x h + ν h • x' h ∧
        μ h * E.u h (x h) + ν h * E.u h (x' h) ≤ s h * E.u h (z h) ∧ 0 ≤ (z h).1 := by
      intro h
      by_cases hs : s h = 0
      · have h0 : μ h = 0 := by linarith [hμh h, hνh h, show μ h + ν h = 0 from hs]
        have h0' : ν h = 0 := by linarith [hμh h, hνh h, show μ h + ν h = 0 from hs]
        simp only [z, hs, ↓reduceIte, h0, h0', zero_smul, add_zero, zero_mul, le_refl,
          true_and]
        exact le_rfl
      · have hspos : 0 < s h := lt_of_le_of_ne (add_nonneg (hμh h) (hνh h)) (Ne.symm hs)
        have hw1 : 0 ≤ (s h)⁻¹ * μ h := mul_nonneg (inv_nonneg.2 hspos.le) (hμh h)
        have hw2 : 0 ≤ (s h)⁻¹ * ν h := mul_nonneg (inv_nonneg.2 hspos.le) (hνh h)
        have hw : (s h)⁻¹ * μ h + (s h)⁻¹ * ν h = 1 := by
          rw [← mul_add]; exact inv_mul_cancel₀ hs
        simp only [z, hs, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs,
            one_mul, one_mul]
        · have hc := (E.u_concaveOn (hconc h)).2 (hx.1 h) (hx'.1 h) hw1 hw2 hw
          simp only [smul_eq_mul] at hc
          have := mul_le_mul_of_nonneg_left hc hspos.le
          calc μ h * E.u h (x h) + ν h * E.u h (x' h)
              = s h * ((s h)⁻¹ * μ h * E.u h (x h) + (s h)⁻¹ * ν h * E.u h (x' h)) := by
                field_simp
            _ ≤ _ := this
        · exact ql_convex_bundles (hx.1 h) (hx'.1 h) hw1 hw2 hw
    have hfeas : E.IsFeasible (μ + ν) z := by
      refine ⟨fun h => (hz h).2.2, ?_⟩
      have e1 : ∑ h, (μ + ν) h • z h = ∑ h, μ h • x h + ∑ h, ν h • x' h := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => (hz h).1
      have e2 : ∑ h, (μ + ν) h • E.ω h = ∑ h, μ h • E.ω h + ∑ h, ν h • E.ω h := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => by rw [Pi.add_apply, add_smul]
      rw [e1, e2]
      exact ⟨add_le_add hx.2.1 hx'.2.1, add_le_add hx.2.2 hx'.2.2⟩
    have hle : E.welfare μ x + E.welfare ν x' ≤ E.welfare (μ + ν) z := by
      unfold QLEconomy.welfare
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun h _ => (hz h).2.1
    exact hle.trans (le_csSup (hbdd _ (add_nonneg hμh hν)) ⟨z, hfeas, rfl⟩)
  -- pass to suprema
  have step : ∀ x', E.IsFeasible ν x' → E.v μ ≤ E.v (μ + ν) - E.welfare ν x' := by
    intro x' hx'
    refine csSup_le (E.valueSet_nonempty hω μ) ?_
    rintro s ⟨x, hx, rfl⟩
    linarith [key x x' hx hx']
  have : E.v ν ≤ E.v (μ + ν) - E.v μ := by
    refine csSup_le (E.valueSet_nonempty hω ν) ?_
    rintro s ⟨x', hx', rfl⟩
    linarith [step x' hx']
  linarith

/-- **Exercise 18.E.1** (MWG, p. 671). `v : ℝ^H₊ → ℝ` is concave and homogeneous of degree
one, for `ψ_h` concave, nondecreasing and differentiable at some point of `ℝ^K₊`, and
`ω_h^y ≥ 0`. -/
theorem exercise_18_E_1 [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hdiff : ∀ h, ∃ z, 0 ≤ z ∧ DifferentiableAt ℝ (E.ψ h) z) (hω : ∀ h, 0 ≤ (E.ω h).1) :
    ConcaveOn ℝ (Set.Ici 0) E.v ∧ ∀ r : ℝ, 0 ≤ r → ∀ μ, E.v (r • μ) = r * E.v μ := by
  obtain ⟨q, hq, c, hmaj⟩ := E.exists_majorant hconc hmono hdiff
  have hbdd : ∀ μ : H → ℝ, 0 ≤ μ → BddAbove (E.valueSet μ) := fun μ hμ =>
    E.bddAbove_of_majorant hμ hq c hmaj
  refine ⟨⟨convex_Ici 0, fun μ hμ ν hν a b ha hb _ => ?_⟩, fun r hr μ => E.v_smul hr μ⟩
  have hμ' : 0 ≤ μ := hμ
  have hν' : 0 ≤ ν := hν
  rw [smul_eq_mul, smul_eq_mul, ← E.v_smul ha, ← E.v_smul hb]
  exact E.v_superadditive hconc hω hbdd (smul_nonneg ha hμ') (smul_nonneg hb hν')

/-! ### Footnote 20: equal treatment is without loss -/

/-- **Footnote 20** (MWG, p. 670). A finite economy with consumers `i : ι` of types `τ i`: an
allocation `x` (not necessarily treating equals equally) is feasible if `y_i ≥ 0` and
`∑ᵢ xᵢ ≤ ∑ᵢ ω_{τ i}`. -/
def QLEconomy.IsFeasibleFinite {ι : Type*} [Fintype ι] (E : QLEconomy H K) (τ : ι → H)
    (x : ι → (Fin K → ℝ) × ℝ) : Prop :=
  (∀ i, 0 ≤ (x i).1) ∧ ∑ i, x i ≤ ∑ i, E.ω (τ i)

/-- **Footnote 20** (MWG, p. 670). The profile `I_h = #{i : τ i = h}` of a finite economy. -/
def qlTypeCount {ι : Type*} [Fintype ι] [DecidableEq H] (τ : ι → H) (h : H) : ℝ :=
  ((Finset.univ.filter fun i => τ i = h).card : ℝ)

/-- Summing over consumers is summing over types with multiplicities `I_h`. -/
theorem ql_sum_fiber {ι M : Type*} [Fintype ι] [Fintype H] [DecidableEq H] [AddCommGroup M]
    [Module ℝ M] (τ : ι → H) (f : H → M) :
    ∑ i, f (τ i) = ∑ h, qlTypeCount τ h • f h := by
  rw [← Finset.sum_fiberwise Finset.univ τ (fun i => f (τ i))]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    qlTypeCount, Nat.cast_smul_eq_nsmul]

/-- **Footnote 20** (MWG, p. 670). Because utilities are concave, the maximum is reached treating
consumers of the same type equally: replacing the bundles of the consumers of each type by their
average keeps feasibility (for the profile `I`) and does not lower the sum of utilities, so every
feasible allocation of the finite economy gives at most `v(I)`. -/
theorem footnote_18_20 {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (τ : ι → H)
    (hbdd : BddAbove (E.valueSet (qlTypeCount τ))) {x : ι → (Fin K → ℝ) × ℝ}
    (hx : E.IsFeasibleFinite τ x) : ∑ i, E.u (τ i) (x i) ≤ E.v (qlTypeCount τ) := by
  set I := qlTypeCount τ with hI
  let F : H → Finset ι := fun h => Finset.univ.filter fun i => τ i = h
  let xb : H → (Fin K → ℝ) × ℝ := fun h => (I h)⁻¹ • ∑ i ∈ F h, x i
  have hcard : ∀ h, I h = ((F h).card : ℝ) := fun h => rfl
  have hsmul : ∀ h, I h • xb h = ∑ i ∈ F h, x i := by
    intro h
    by_cases h0 : I h = 0
    · have hF : F h = ∅ := by
        rw [hcard] at h0
        exact Finset.card_eq_zero.1 (by exact_mod_cast h0)
      simp [h0, hF]
    · simp only [xb, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hjensen : ∀ h, ∑ i ∈ F h, E.u h (x i) ≤ I h * E.u h (xb h) := by
    intro h
    by_cases h0 : I h = 0
    · have hF : F h = ∅ := by
        rw [hcard] at h0
        exact Finset.card_eq_zero.1 (by exact_mod_cast h0)
      simp [h0, hF]
    · have hpos : 0 < I h := lt_of_le_of_ne (by rw [hcard]; positivity) (Ne.symm h0)
      have hJ := (E.u_concaveOn (hconc h)).le_map_sum (t := F h) (w := fun _ => (I h)⁻¹)
        (p := x) (fun _ _ => inv_nonneg.2 hpos.le)
        (by rw [Finset.sum_const, nsmul_eq_mul, ← hcard, mul_inv_cancel₀ h0])
        (fun i _ => hx.1 i)
      simp only [smul_eq_mul, ← Finset.smul_sum, ← Finset.mul_sum] at hJ
      have := mul_le_mul_of_nonneg_left hJ hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ h0, one_mul] at this
  have hfeas : E.IsFeasible I xb := by
    refine ⟨fun h => ?_, ?_⟩
    · change 0 ≤ ((I h)⁻¹ • ∑ i ∈ F h, x i).1
      rw [Prod.smul_fst, Prod.fst_sum]
      exact smul_nonneg (inv_nonneg.2 (by rw [hcard]; positivity))
        (Finset.sum_nonneg fun i _ => hx.1 i)
    · have e1 : ∑ h, I h • xb h = ∑ i, x i := by
        simp only [hsmul]
        exact Finset.sum_fiberwise Finset.univ τ x
      rw [e1, hI, ← ql_sum_fiber τ E.ω]
      exact hx.2
  have hsum : ∑ i, E.u (τ i) (x i) = ∑ h, ∑ i ∈ F h, E.u h (x i) := by
    rw [← Finset.sum_fiberwise Finset.univ τ (fun i => E.u (τ i) (x i))]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hle : ∑ i, E.u (τ i) (x i) ≤ E.welfare I xb := by
    rw [hsum]
    exact Finset.sum_le_sum fun h _ => hjensen h
  exact hle.trans (le_csSup hbdd ⟨xb, hfeas, rfl⟩)

/-- **Footnote 20** (MWG, p. 670). The supremum of the sum of utilities over all feasible
allocations of the finite economy (unequal treatment allowed) equals `v(I)` of (18.E.1). -/
theorem footnote_18_20_sSup {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H]
    (E : QLEconomy H K) (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h))
    (hω : ∀ h, 0 ≤ (E.ω h).1) (τ : ι → H) (hbdd : BddAbove (E.valueSet (qlTypeCount τ))) :
    sSup {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} =
      E.v (qlTypeCount τ) := by
  have hsub : E.valueSet (qlTypeCount τ) ⊆
      {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} := by
    rintro s ⟨x, hx, rfl⟩
    refine ⟨fun i => x (τ i), ⟨fun i => hx.1 (τ i), ?_⟩, ?_⟩
    · rw [ql_sum_fiber τ x, ql_sum_fiber τ E.ω]
      exact hx.2
    · rw [ql_sum_fiber τ (fun h => E.u h (x h))]
      rfl
  have hne := E.valueSet_nonempty hω (qlTypeCount τ)
  have hbdd' : BddAbove {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} := by
    refine ⟨E.v (qlTypeCount τ), ?_⟩
    rintro s ⟨x, hx, rfl⟩
    exact footnote_18_20 E hconc τ hbdd hx
  refine le_antisymm (csSup_le (hne.mono hsub) ?_) (csSup_le_csSup hbdd' hne hsub)
  rintro s ⟨x, hx, rfl⟩
  exact footnote_18_20 E hconc τ hbdd hx

/-! ### Euler's formula and the comparison lemma -/

/-- **Section M.B** (MWG, p. 671, Euler's formula). If `v` is homogeneous of degree one
(`v(tμ) = t v(μ)` for `t > 0`) and differentiable at `μ`, then `v(μ) = ∑_h μ_h ∂v(μ)/∂μ_h`:
differentiate `t ↦ v(tμ)` at `t = 1`. -/
theorem ql_euler [Fintype H] [DecidableEq H] {v : (H → ℝ) → ℝ} {D : (H → ℝ) →L[ℝ] ℝ}
    {μ : H → ℝ} (hv : HasFDerivAt v D μ) (hhom : ∀ t : ℝ, 0 < t → v (t • μ) = t * v μ) :
    v μ = ∑ h, μ h * D (Pi.single h 1) := by
  have h1 : HasDerivAt (fun t : ℝ => v (t • μ)) (D μ) 1 := by
    have hl : HasDerivAt (fun t : ℝ => t • μ) μ 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const μ
    have hv' : HasFDerivAt v D ((1 : ℝ) • μ) := by simpa using hv
    exact hv'.comp_hasDerivAt (1 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => v (t • μ)) (v μ) 1 := by
    have : HasDerivAt (fun t : ℝ => t * v μ) (v μ) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (v μ)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with t ht using hhom t ht
  rw [h2.unique h1, ql_clm_apply_eq_sum]

/-- The comparison lemma behind (18.E.5): if `v ≤ g` on `ℝ^H₊` for the linear
`g(ν) = ∑ ν_k a_k`, with equality at `μ`, and `v` is differentiable at `μ` with `μ_h > 0`, then
`∂v(μ)/∂μ_h = a_h` (`g - v` has a local minimum along the `h`-th coordinate line). -/
theorem ql_partial_eq_of_le_linear [Fintype H] [DecidableEq H] {v : (H → ℝ) → ℝ}
    {D : (H → ℝ) →L[ℝ] ℝ} {μ : H → ℝ} (hv : HasFDerivAt v D μ) (hμ : 0 ≤ μ) (a : H → ℝ)
    (hle : ∀ ν : H → ℝ, 0 ≤ ν → v ν ≤ ∑ k, ν k * a k) (heq : v μ = ∑ k, μ k * a k) {h : H}
    (hμh : 0 < μ h) : D (Pi.single h 1) = a h := by
  set e : H → ℝ := Pi.single h 1 with he
  have hlin : ∀ t : ℝ, ∑ k, (μ + t • e) k * a k = ∑ k, μ k * a k + t * a h := by
    intro t
    simp [he, add_mul, Finset.sum_add_distrib, Pi.single_apply]
  have hφ : HasDerivAt (fun t : ℝ => (∑ k, μ k * a k + t * a h) - v (μ + t • e))
      (a h - D e) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ∑ k, μ k * a k + t * a h) (a h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a h)).const_add (∑ k, μ k * a k)
    exact h1.sub (ql_hasDerivAt_line hv e)
  have hmin : IsLocalMin (fun t : ℝ => (∑ k, μ k * a k + t * a h) - v (μ + t • e)) 0 := by
    filter_upwards [lt_mem_nhds (show -μ h < 0 by linarith)] with t ht
    have hnn : 0 ≤ μ + t • e := by
      intro k
      by_cases hk : k = h
      · subst hk
        simp [he]
        linarith
      · simpa [he, hk] using hμ k
    have := hle _ hnn
    rw [hlin] at this
    simp only [zero_mul, add_zero, zero_smul]
    linarith
  linarith [hmin.hasDerivAt_eq_zero hφ]

/-! ### First-order conditions for (18.E.2) -/

/-- Along a line `t ↦ y + t d` from a strictly positive `y`, nonnegativity holds near `t = 0`. -/
theorem ql_eventually_nonneg_line {ι : Type*} [Finite ι] {y : ι → Fin K → ℝ}
    (hy : ∀ h l, 0 < y h l) (d : ι → Fin K → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ h, 0 ≤ y h + t • d h := by
  rw [Filter.eventually_all]
  intro h
  have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < y h l + t * d h l := by
    rw [Filter.eventually_all]
    intro l
    have hc : Continuous fun t : ℝ => y h l + t * d h l := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hy h l))
  filter_upwards [this] with t ht l
  simpa using (ht l).le

/-- Aggregate of a perturbation of the non-numeraire goods. -/
theorem ql_sum_perturb [Fintype H] (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ)
    (d : H → Fin K → ℝ) (t : ℝ) :
    ∑ h, μ h • (x h + (t • d h, (0 : ℝ))) = ∑ h, μ h • x h + (t • ∑ h, μ h • d h, 0) := by
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, Finset.smul_sum, smul_smul, mul_comm]
  · simp [Prod.snd_sum]

/-- **(18.E.2)** first-order conditions (MWG, p. 671). If `x` solves (18.E.2) for `μ`, each
`ψ_h` is differentiable at `y_h` with derivative `Dψ_h`, and the perturbed allocations
`x_h + (t d_h, 0)` are feasible for `t` near `0`, then `∑_h μ_h Dψ_h(d_h) = 0`. -/
theorem QLEconomy.foc_of_optimal [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) (d : H → Fin K → ℝ)
    (hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun h => x h + (t • d h, 0))) :
    ∑ h, μ h * Dψ h (d h) = 0 := by
  let φ : ℝ → ℝ := fun t => ∑ h, μ h * (E.ψ h ((x h).1 + t • d h) + (x h).2)
  have hφeq : ∀ t, E.welfare μ (fun h => x h + (t • d h, 0)) = φ t := by
    intro t
    simp [φ, QLEconomy.welfare, QLEconomy.u]
  have hφ0 : φ 0 = E.welfare μ x := by
    simp [φ, QLEconomy.welfare, QLEconomy.u]
  have hder : HasDerivAt φ (∑ h, μ h * Dψ h (d h)) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun h _ =>
      ((ql_hasDerivAt_line (hDψ h) (d h)).add_const ((x h).2)).const_mul (μ h)
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hfeas] with t ht
    rw [← hφeq, hφ0]
    exact hopt.2 _ ht
  exact hmax.hasDerivAt_eq_zero hder

/-- **(18.E.2)** (MWG, p. 671). `x` solves (18.E.2) iff it is feasible and attains `v(μ)`
(given a bounded value set). -/
theorem QLEconomy.isOptimal_iff [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hbdd : BddAbove (E.valueSet μ)) :
    E.IsOptimal μ x ↔ E.IsFeasible μ x ∧ E.v μ = E.welfare μ x := by
  constructor
  · intro hopt
    refine ⟨hopt.1, ?_⟩
    refine le_antisymm (csSup_le ⟨_, x, hopt.1, rfl⟩ ?_) (le_csSup hbdd ⟨x, hopt.1, rfl⟩)
    rintro s ⟨x', hx', rfl⟩
    exact hopt.2 x' hx'
  · rintro ⟨hx, hv⟩
    exact ⟨hx, fun x' hx' => hv ▸ le_csSup hbdd ⟨x', hx', rfl⟩⟩

/-! ### Walrasian equilibrium of the continuum economy -/

/-- With `ψ_h` nondecreasing on `ℝ^K₊`, Walrasian prices are nonnegative (`q_l < 0` would let a
consumer buy one more unit of good `l` and keep the money). -/
theorem QLEconomy.walras_price_nonneg [Fintype H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) {μ : H → ℝ} {q : Fin K → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H) : 0 ≤ q := by
  intro l
  by_contra hneg
  have hql : q l < 0 := lt_of_not_ge hneg
  set x' : (Fin K → ℝ) × ℝ := ((x h).1 + Pi.single l 1, (x h).2 - q l)
  have hy : (x h).1 ≤ x'.1 := by
    intro k
    have : 0 ≤ (Pi.single l (1 : ℝ) : Fin K → ℝ) k := by
      rcases eq_or_ne k l with rfl | hk
      · simp
      · simp [hk]
    simpa [x'] using this
  have hx'0 : 0 ≤ x'.1 := (hW.1.1 h).trans hy
  have hp : qlPrice q x' = qlPrice q (x h) := by
    simp only [qlPrice, x', dotProduct_add, dotProduct_single, mul_one]
    ring
  have hle := (hW.2 h).2 x' hx'0 (hp ▸ (hW.2 h).1)
  have hm := hmono h (Set.mem_Ici.2 (hW.1.1 h)) (Set.mem_Ici.2 hx'0) hy
  simp only [QLEconomy.u, x'] at hle hm
  linarith

/-- In a Walrasian equilibrium every budget binds: `p·x*_h = p·ω_h` (money is desirable). -/
theorem QLEconomy.walras_budget_eq [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H) :
    qlPrice q (x h) = qlPrice q (E.ω h) := by
  refine le_antisymm (hW.2 h).1 (not_lt.1 fun hlt => ?_)
  set x' : (Fin K → ℝ) × ℝ := ((x h).1, (x h).2 + (qlPrice q (E.ω h) - qlPrice q (x h)))
  have hp : qlPrice q x' = qlPrice q (E.ω h) := by
    simp only [qlPrice, x'] at hlt ⊢
    ring
  have hle := (hW.2 h).2 x' (hW.1.1 h) hp.le
  simp only [QLEconomy.u, x'] at hle
  linarith

/-- By quasilinearity, `x*_h` maximizes `u_h(x) - p·x` over `{y ≥ 0}`:
`u_h(x) ≤ u_h(x*_h) - p·x*_h + p·x`. -/
theorem QLEconomy.walras_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H)
    (x' : (Fin K → ℝ) × ℝ) (hx' : 0 ≤ x'.1) :
    E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x' := by
  set x'' : (Fin K → ℝ) × ℝ := (x'.1, x'.2 + (qlPrice q (x h) - qlPrice q x'))
  have hp : qlPrice q x'' = qlPrice q (x h) := by
    simp only [qlPrice, x'']
    ring
  have hle := (hW.2 h).2 x'' hx' (hp ▸ (hW.2 h).1)
  simp only [QLEconomy.u, x''] at hle ⊢
  linarith

/-- The linear upper bound `v(ν) ≤ ∑ ν_k (c_k + p·ω_k)` on `ℝ^H₊` from an affine majorant. -/
theorem QLEconomy.v_le_linear [Fintype H] (E : QLEconomy H K) (hω : ∀ h, 0 ≤ (E.ω h).1)
    {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) (ν : H → ℝ) (hν : 0 ≤ ν) :
    E.v ν ≤ ∑ k, ν k * (c k + qlPrice q (E.ω k)) := by
  have := E.v_le_of_majorant hω hν hq c hmaj
  rw [qlPrice_sum, ← Finset.sum_add_distrib] at this
  simpa only [mul_add] using this

/-- **(18.E.5)** at a Walrasian equilibrium, and the "Walrasian ⇒ marginal product" half of
**Proposition 18.E.1** (MWG, pp. 671-672). Let `ψ_h` be nondecreasing on `ℝ^K₊`, `ω_h^y ≥ 0`,
`μ ≫ 0`, `(q, x*)` a Walrasian equilibrium and `v` differentiable at `μ`. Then
`∂v(μ)/∂μ_h = u_h(x*_h)`.

Proof (in place of the envelope theorem): each type's `x*_h` maximizes `u_h(x) - p·x`, so
`v(ν) ≤ ∑ ν_h [u_h(x*_h) + p·(ω_h - x*_h)]` for every `ν ≥ 0`; budgets bind, so the right side
equals `∑ μ_h u_h(x*_h) ≤ v(μ)` at `ν = μ`; a differentiable function lying below a linear one,
with contact at the interior point `μ`, has the linear function's partial derivatives. -/
theorem QLEconomy.partial_v_of_walras [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ}
    (hμ : ∀ h, 0 < μ h) {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D μ) (h : H) :
    D (Pi.single h 1) = E.u h (x h) := by
  have hq := E.walras_price_nonneg hmono hW h
  have hμ0 : 0 ≤ μ := fun k => (hμ k).le
  set c : H → ℝ := fun k => E.u k (x k) - qlPrice q (x k)
  have hmaj : ∀ k x', 0 ≤ x'.1 → E.u k x' ≤ c k + qlPrice q x' := fun k x' hx' =>
    E.walras_majorant hW k x' hx'
  have ha : ∀ k, c k + qlPrice q (E.ω k) = E.u k (x k) := fun k => by
    simp only [c, E.walras_budget_eq hW k]; ring
  have hle := E.v_le_linear hω hq c hmaj
  have heq : E.v μ = ∑ k, μ k * (c k + qlPrice q (E.ω k)) := by
    refine le_antisymm (hle μ hμ0) ?_
    have hbdd := E.bddAbove_of_majorant hμ0 hq c hmaj
    simp only [ha]
    exact le_csSup hbdd ⟨x, hW.1, rfl⟩
  rw [ql_partial_eq_of_le_linear hv hμ0 _ hle heq (hμ h), ha]

/-- **Proposition 18.E.1** (MWG, p. 671), "if" direction: a Walrasian equilibrium allocation of
the continuum population `μ ≫ 0` is a marginal product allocation (`ψ_h` nondecreasing,
`ω_h^y ≥ 0`, `v` differentiable at `μ`; neither concavity, differentiability of `ψ_h` nor
interiority of `x*` is needed in this direction). -/
theorem proposition_18_E_1_of_walras [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ}
    (hμ : ∀ h, 0 < μ h) {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x)
    (hv : DifferentiableAt ℝ E.v μ) : E.IsMarginalProduct μ x :=
  ⟨hW.1, fun h => (E.partial_v_of_walras hmono hω hμ hW hv.hasFDerivAt h).symm⟩

/-- **(18.E.4)** (MWG, p. 671), the supporting prices of a solution of (18.E.2). Let `ψ_h` be
concave and nondecreasing on `ℝ^K₊`, `μ ≫ 0`, and let `x` solve (18.E.2) with `y_h ≫ 0` and `ψ_h`
differentiable at `y_h` (derivative `Dψ_h`). Then there is `q ≥ 0` with
`q_l = ∂ψ_h(y_h)/∂y_l` for all `h, l` (18.E.4); `x_h` maximizes `u_h(x) - p·x` over `{y ≥ 0}`
(concavity: the tangent plane majorises `ψ_h`); and `∑ μ_h p·(ω_h - x_h) = 0` (no surplus has
positive value). The multipliers are obtained from first-order conditions for transfers of a
good between two types and for disposal of a surplus, not from Section M.K. -/
theorem QLEconomy.supporting_prices [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ} (hint : ∀ h l, 0 < (x h).1 l)
    (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) :
    ∃ q : Fin K → ℝ, (∀ h l, Dψ h (Pi.single l 1) = q l) ∧ 0 ≤ q ∧
      (∀ h x', 0 ≤ x'.1 → E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x') ∧
      ∑ h, μ h * qlPrice q (E.ω h - x h) = 0 := by
  classical
  rcases isEmpty_or_nonempty H with hH | hH
  · exact ⟨0, fun h => isEmptyElim h, le_rfl, fun h => isEmptyElim h, by simp⟩
  obtain ⟨h0⟩ := hH
  set q : Fin K → ℝ := fun l => Dψ h0 (Pi.single l 1) with hqdef
  set e : Fin K → Fin K → ℝ := fun l => Pi.single l 1
  -- (18.E.4): transfers between `h` and `h0`
  have hgrad : ∀ h l, Dψ h (Pi.single l 1) = q l := by
    intro h l
    let d : H → Fin K → ℝ := fun j =>
      (if j = h then (μ h)⁻¹ • e l else 0) - (if j = h0 then (μ h0)⁻¹ • e l else 0)
    have hsumd : ∑ j, μ j • d j = 0 := by
      simp only [d, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, smul_smul, mul_inv_cancel₀ (hμ _).ne', one_smul, sub_self]
    have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun j => x j + (t • d j, 0)) := by
      filter_upwards [ql_eventually_nonneg_line hint d] with t ht
      refine ⟨fun j => by simpa using ht j, ?_⟩
      rw [ql_sum_perturb, hsumd, smul_zero, Prod.mk_zero_zero, add_zero]
      exact hopt.1.2
    have hfoc := E.foc_of_optimal hopt hDψ d hfeas
    have hterm : ∀ j, μ j * Dψ j (d j) = (if j = h then Dψ h (e l) else 0) -
        (if j = h0 then Dψ h0 (e l) else 0) := by
      intro j
      by_cases hjh : j = h <;> by_cases hj0 : j = h0
      · subst hjh; subst hj0; simp [d]
      · subst hjh; simp [d, hj0, map_smul, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (hμ j).ne']
      · subst hj0; simp [d, hjh, map_smul, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (hμ j).ne']
      · simp [d, hjh, hj0]
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hfoc
    simp only [hqdef]
    exact sub_eq_zero.1 hfoc
  have hq : 0 ≤ q := fun l => ql_fderiv_single_nonneg (hmono h0) (hopt.1.1 h0) (hDψ h0) l
  have hDq : ∀ h z, Dψ h z = q ⬝ᵥ z := by
    intro h z
    rw [ql_clm_apply_eq_sum, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [hgrad, mul_comm]
  have hmaj : ∀ h x', 0 ≤ x'.1 → E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x' := by
    intro h x' hx'
    have ht := MWG.WelfareTheorems.concaveOn_le_tangent (hconc h)
      (Set.mem_Ici.2 (hopt.1.1 h)) (Set.mem_Ici.2 hx') (hDψ h)
    rw [hDq, dotProduct_sub] at ht
    simp only [QLEconomy.u, qlPrice]
    linarith
  -- the surplus `s = ∑ μ ω - ∑ μ x ≥ 0` has zero value
  set S : (Fin K → ℝ) × ℝ := ∑ j, μ j • E.ω j - ∑ j, μ j • x j with hS
  have hgood : ∀ l, q l * S.1 l = 0 := by
    intro l
    have hS1 : 0 ≤ S.1 l := by
      simp only [hS, Prod.fst_sub, Pi.sub_apply, sub_nonneg]
      exact hopt.1.2.1 l
    rcases hS1.eq_or_lt with h0l | hpos
    · rw [← h0l, mul_zero]
    let d : H → Fin K → ℝ := fun j => if j = h0 then (μ h0)⁻¹ • e l else 0
    have hsumd : ∑ j, μ j • d j = e l := by
      simp only [d, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        smul_smul, mul_inv_cancel₀ (hμ h0).ne', one_smul]
    have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun j => x j + (t • d j, 0)) := by
      filter_upwards [ql_eventually_nonneg_line hint d, Iio_mem_nhds hpos] with t ht ht'
      refine ⟨fun j => by simpa using ht j, ?_⟩
      rw [ql_sum_perturb, hsumd]
      refine ⟨fun k => ?_, ?_⟩
      · have hk := hopt.1.2.1 k
        rcases eq_or_ne k l with rfl | hkl
        · have : t < (∑ j, μ j • E.ω j).1 k - (∑ j, μ j • x j).1 k := by
            simpa [hS] using ht'
          simp [e]
          linarith
        · simpa [e, hkl] using hk
      · simpa using hopt.1.2.2
    have hfoc := E.foc_of_optimal hopt hDψ d hfeas
    have hterm : ∀ j, μ j * Dψ j (d j) = if j = h0 then q l else 0 := by
      intro j
      by_cases hj0 : j = h0
      · subst hj0
        simp [d, hqdef, e, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hμ j).ne']
      · simp [d, hj0]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hfoc
    rw [hfoc, zero_mul]
  have hmoney : S.2 = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) (sub_nonneg.2 hopt.1.2.2)
    let x' : H → (Fin K → ℝ) × ℝ := fun j => x j + (0, if j = h0 then S.2 / μ h0 else 0)
    have hfeas : E.IsFeasible μ x' := by
      refine ⟨fun j => by simpa [x'] using hopt.1.1 j, ?_⟩
      have hagg : ∑ j, μ j • x' j = ∑ j, μ j • x j + (0, S.2) := by
        simp only [x', smul_add, Finset.sum_add_distrib]
        congr 1
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum]
        · simp [Prod.snd_sum, mul_div_cancel₀ _ (hμ h0).ne']
      rw [hagg]
      refine ⟨by simpa using hopt.1.2.1, ?_⟩
      simp [hS]
    have hw : E.welfare μ x' = E.welfare μ x + S.2 := by
      simp only [QLEconomy.welfare, QLEconomy.u, x', Prod.fst_add, Prod.snd_add, add_zero]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_div_cancel₀ _ (hμ h0).ne']
      ring
    linarith [hopt.2 x' hfeas]
  refine ⟨q, hgrad, hq, hmaj, ?_⟩
  have : ∑ h, μ h * qlPrice q (E.ω h - x h) = qlPrice q S := by
    rw [← qlPrice_sum, hS]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [this, qlPrice, hmoney, add_zero, dotProduct]
  exact Finset.sum_eq_zero fun l _ => hgood l

/-- **Exercise 18.E.2** (MWG, p. 685): expression **(18.E.5)** (p. 672). If `x*` solves (18.E.2)
for `μ ≫ 0`, with `y*_h ≫ 0`, `ψ_h` concave and nondecreasing on `ℝ^K₊` and differentiable at
`y*_h`, `ω_h^y ≥ 0`, and `v` is differentiable at `μ`, then with the prices `p = (q, 1)` of
(18.E.4), `∂v(μ)/∂μ_h = u_h(x*_h) + p·(ω_h - x*_h)`. Derived from `v(ν) ≤ ∑ ν_h [u_h(x*_h) +
p·(ω_h - x*_h)]` on `ℝ^H₊` with equality at `μ` (`ql_partial_eq_of_le_linear`) instead of the
envelope theorem of Section M.L. -/
theorem exercise_18_E_2 [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) {D : (H → ℝ) →L[ℝ] ℝ}
    (hv : HasFDerivAt E.v D μ) :
    ∃ q : Fin K → ℝ, (∀ h l, Dψ h (Pi.single l 1) = q l) ∧
      ∀ h, D (Pi.single h 1) = E.u h (x h) + qlPrice q (E.ω h - x h) := by
  obtain ⟨q, hgrad, hq, hmaj, hzero⟩ := E.supporting_prices hconc hmono hμ hint hopt hDψ
  refine ⟨q, hgrad, fun h => ?_⟩
  have hμ0 : 0 ≤ μ := fun k => (hμ k).le
  set c : H → ℝ := fun k => E.u k (x k) - qlPrice q (x k)
  have ha : ∀ k, c k + qlPrice q (E.ω k) = E.u k (x k) + qlPrice q (E.ω k - x k) := fun k => by
    simp only [c, qlPrice_sub]; ring
  have hle := E.v_le_linear hω hq c hmaj
  have heq : E.v μ = ∑ k, μ k * (c k + qlPrice q (E.ω k)) := by
    have hbdd := E.bddAbove_of_majorant hμ0 hq c hmaj
    rw [((E.isOptimal_iff hbdd).1 hopt).2]
    simp only [ha, mul_add, Finset.sum_add_distrib, hzero, add_zero]
    rfl
  rw [ql_partial_eq_of_le_linear hv hμ0 _ hle heq (hμ h), ha]

/-- A solution `x*` of (18.E.2) satisfying (18.E.3) is a Walrasian equilibrium allocation: by
(18.E.5) every `p·(ω_h - x*_h) = 0`, so budgets are met, and the majorant of
`QLEconomy.supporting_prices` makes `x*_h` each type's demand. -/
theorem QLEconomy.walras_of_optimal_of_partial [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) {D : (H → ℝ) →L[ℝ] ℝ}
    (hv : HasFDerivAt E.v D μ) (hmp : ∀ h, E.u h (x h) = D (Pi.single h 1)) :
    ∃ q, E.IsWalrasEqm μ q x := by
  obtain ⟨q, hgrad, hq, hmaj, hzero⟩ := E.supporting_prices hconc hmono hμ hint hopt hDψ
  -- (18.E.5) for these prices
  have h185 : ∀ h, D (Pi.single h 1) = E.u h (x h) + qlPrice q (E.ω h - x h) := by
    intro h
    obtain ⟨q', hgrad', h5⟩ := exercise_18_E_2 E hconc hmono hω hμ hint hopt hDψ hv
    have hqq : q' = q := by
      ext l; rw [← hgrad' h l, hgrad h l]
    simpa [hqq] using h5 h
  have hbal : ∀ h, qlPrice q (x h) = qlPrice q (E.ω h) := by
    intro h
    have := h185 h
    rw [← hmp h, qlPrice_sub] at this
    linarith
  refine ⟨q, hopt.1, fun h => ⟨(hbal h).le, fun x' hx' hb => ?_⟩⟩
  have := hmaj h x' hx'
  linarith [hbal h]

/-- **Proposition 18.E.1** (MWG, p. 671). For a continuum population `μ ≫ 0`, a feasible
allocation `x*` with `y*_h ≫ 0` is a marginal product allocation iff it is a Walrasian
equilibrium allocation. Hypotheses: `ψ_h` concave and nondecreasing on `ℝ^K₊` and differentiable
at `y*_h`, `ω_h^y ≥ 0`, `v` differentiable at `μ` (footnote 21). The book's `x* ≫ 0` is used
only through `y* ≫ 0`; strict concavity and strict monotonicity of `ψ_h` are not needed.
"Only if": Euler's formula gives `v(μ) = ∑ μ_h ∂v/∂μ_h = ∑ μ_h u_h(x*_h)`, so `x*` solves
(18.E.2); then (18.E.4)-(18.E.5). "If": `proposition_18_E_1_of_walras`. -/
theorem proposition_18_E_1 [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hfeas : E.IsFeasible μ x) (hint : ∀ h l, 0 < (x h).1 l)
    (hdψ : ∀ h, DifferentiableAt ℝ (E.ψ h) (x h).1) (hv : DifferentiableAt ℝ E.v μ) :
    E.IsMarginalProduct μ x ↔ ∃ q, E.IsWalrasEqm μ q x := by
  constructor
  · intro hmp
    have hD := hv.hasFDerivAt
    have hDψ : ∀ h, HasFDerivAt (E.ψ h) (fderiv ℝ (E.ψ h) (x h).1) (x h).1 :=
      fun h => (hdψ h).hasFDerivAt
    -- Euler: `v(μ) = ∑ μ_h u_h(x*_h)`, so `x*` solves (18.E.2)
    obtain ⟨q, hq, c, hmaj⟩ := E.exists_majorant hconc hmono
      fun h => ⟨(x h).1, hfeas.1 h, hdψ h⟩
    have hbdd := E.bddAbove_of_majorant (fun k => (hμ k).le) hq c hmaj
    have heul := ql_euler hD fun t ht => E.v_smul ht.le μ
    have hopt : E.IsOptimal μ x := by
      refine (E.isOptimal_iff hbdd).2 ⟨hfeas, ?_⟩
      rw [heul, QLEconomy.welfare]
      exact Finset.sum_congr rfl fun h _ => by rw [hmp.2 h]
    exact E.walras_of_optimal_of_partial hconc hmono hω hμ hint hopt hDψ hD hmp.2
  · rintro ⟨q, hW⟩
    exact proposition_18_E_1_of_walras E hmono hω hμ hW hv

/-- Near a strictly positive population, populations are nonnegative. -/
theorem ql_eventually_nonneg_of_pos [Finite H] {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) :
    ∀ᶠ ν in 𝓝 μ, 0 ≤ ν := by
  have : ∀ᶠ ν in 𝓝 μ, ∀ h, 0 < ν h := Filter.eventually_all.2 fun h =>
    ((continuous_apply h).tendsto μ).eventually (lt_mem_nhds (hμ h))
  filter_upwards [this] with ν hν h using (hν h).le

/-! ### Finite economies (p. 672) -/

/-- **Section 18.E** (MWG, p. 672). The marginal contribution of a type-`h` consumer in the
finite economy `I`: `Δ_h v(I) = v(I) - v(I - e_h)`. -/
noncomputable def QLEconomy.deltaV [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (I : H → ℝ) (h : H) : ℝ :=
  E.v I - E.v (I - Pi.single h 1)

/-- **Section 18.E** (MWG, p. 672). By concavity of `v`, `Δ_h v(I) ≥ ∂v(I)/∂μ_h` (for `I ≥ e_h`
and `v` differentiable at `I`). -/
theorem claim_18_E_deltaV_ge_partial [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ConcaveOn ℝ (Set.Ici 0) E.v) {I : H → ℝ} {h : H} (hI : 0 ≤ I - Pi.single h 1)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D I) : D (Pi.single h 1) ≤ E.deltaV I h := by
  have hI0 : 0 ≤ I := by
    have : I = (I - Pi.single h 1) + Pi.single h 1 := by abel
    rw [this]
    exact add_nonneg hI (Pi.single_nonneg.2 zero_le_one)
  have ht := MWG.WelfareTheorems.concaveOn_le_tangent hconc (Set.mem_Ici.2 hI0)
    (Set.mem_Ici.2 hI) hv
  rw [sub_sub_cancel_left, map_neg] at ht
  unfold QLEconomy.deltaV
  linarith

/-- **Section 18.E** (MWG, p. 672). With Euler's formula, `∑_h I_h Δ_h v(I) ≥ v(I)` (for a
profile with `I_h ≥ 1`, `v` concave on `ℝ^H₊` and differentiable at `I`). -/
theorem claim_18_E_sum_deltaV_ge [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ConcaveOn ℝ (Set.Ici 0) E.v) {I : H → ℝ} (hI : ∀ h, 0 ≤ I - Pi.single h 1)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D I) :
    E.v I ≤ ∑ h, I h * E.deltaV I h := by
  rw [ql_euler hv fun t ht => E.v_smul ht.le I]
  refine Finset.sum_le_sum fun h _ => ?_
  have hIh : 0 ≤ I h := by
    have := hI h h
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply] at this
    linarith
  exact mul_le_mul_of_nonneg_left (claim_18_E_deltaV_ge_partial E hconc (hI h) hv) hIh

/-- **Section 18.E** (MWG, p. 672). "It is impossible to give each consumer the full extent of
her marginal contribution while maintaining feasibility": if `∑ I_h Δ_h v(I) > v(I)`, no
feasible equal-treatment allocation gives every type `h` the utility `Δ_h v(I)`. -/
theorem claim_18_E_no_full_marginal [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    {I : H → ℝ} (hI : 0 ≤ I) (hbdd : BddAbove (E.valueSet I))
    (hgt : E.v I < ∑ h, I h * E.deltaV I h) :
    ¬ ∃ x, E.IsFeasible I x ∧ ∀ h, E.deltaV I h ≤ E.u h (x h) := by
  rintro ⟨x, hx, hge⟩
  have h1 : ∑ h, I h * E.deltaV I h ≤ E.welfare I x :=
    Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hge h) (hI h)
  have h2 : E.welfare I x ≤ E.v I := le_csSup hbdd ⟨x, hx, rfl⟩
  linarith

/-- **Section 18.E** (MWG, p. 672), the same for the finite economy with unequal treatment
allowed (via footnote 20): if `∑ I_h Δ_h v(I) > v(I)`, no feasible allocation of the finite
economy gives every consumer `i` the utility `Δ_{τ i} v(I)`. -/
theorem claim_18_E_no_full_marginal_finite {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H]
    (E : QLEconomy H K) (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (τ : ι → H)
    (hbdd : BddAbove (E.valueSet (qlTypeCount τ)))
    (hgt : E.v (qlTypeCount τ) < ∑ h, qlTypeCount τ h * E.deltaV (qlTypeCount τ) h) :
    ¬ ∃ x, E.IsFeasibleFinite τ x ∧
      ∀ i, E.deltaV (qlTypeCount τ) (τ i) ≤ E.u (τ i) (x i) := by
  rintro ⟨x, hx, hge⟩
  have h1 : ∑ h, qlTypeCount τ h * E.deltaV (qlTypeCount τ) h ≤ ∑ i, E.u (τ i) (x i) := by
    have := ql_sum_fiber τ (fun h => E.deltaV (qlTypeCount τ) h)
    simp only [smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_le_sum fun i _ => hge i
  linarith [footnote_18_20 E hconc τ hbdd hx]

/-- **Section 18.E** (MWG, p. 672). In a finite economy `I ≫ 0`, an allocation `x*` solving
(18.E.2) for `μ = I` (with `y*_h ≫ 0`) is a Walrasian equilibrium allocation iff
`u_h(x*_h) = ∂v(I)/∂μ_h` for all `h` (from (18.E.5)). -/
theorem claim_18_E_finite_walras_iff [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {I : H → ℝ} (hI : ∀ h, 0 < I h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal I x)
    (hdψ : ∀ h, DifferentiableAt ℝ (E.ψ h) (x h).1) (hv : DifferentiableAt ℝ E.v I) :
    (∃ q, E.IsWalrasEqm I q x) ↔ ∀ h, E.u h (x h) = fderiv ℝ E.v I (Pi.single h 1) := by
  constructor
  · rintro ⟨q, hW⟩
    exact (proposition_18_E_1_of_walras E hmono hω hI hW hv).2
  · intro hmp
    exact E.walras_of_optimal_of_partial hconc hmono hω hI hint hopt
      (fun h => (hdψ h).hasFDerivAt) hv.hasFDerivAt hmp

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Marginal productivity: examples and Exercise 18.E.3 (MWG Section 18.E, pp. 670-673, 685)

Concrete instances for the hypotheses of `MWGCoreFoundations.MarginalProduct`.

* The square-root economy `sqrtQLEconomy`: two types, one non-numeraire good,
  `ψ_h(y) = 2√y`, type 0 endowed with one unit of the good, type 1 with nothing. Here
  `v(μ) = 2√((μ₀ + μ₁) μ₀)` on `ℝ²₊` (`sqrtQL_v`), `v` is differentiable at `μ = (1, 1)`, the
  Walrasian equilibrium has price `√2` and utilities `3√2/2`, `√2/2`, which are the partial
  derivatives of `v` (a marginal product allocation, Proposition 18.E.1). As a finite economy
  with one consumer of each type: `Δ₀v = 2√2 > 3√2/2`, `Δ₁v = 2√2 - 2 > √2/2`, and
  `∑ Δ_h v > v(1, 1)`, so no feasible allocation gives everyone her marginal contribution and the
  Walrasian allocation is not a marginal product allocation in the finite sense (p. 672).
* **Exercise 18.E.3**: the Leontief economy `leontiefQLEconomy` (`ψ_h(y) = min(y₁, y₂)`, type 0
  owns one unit of good 1, type 1 one unit of good 2, `μ = (1, 1)`). `v(μ) = min(μ₀, μ₁)`, which
  is not differentiable at `(1, 1)`. The marginal contribution of a trader is taken as the loss
  from removing a marginal trader, the left partial derivative of `v`, equal to `1` (and equal to
  the finite `Δ_h v(1, 1)`); the right partial derivative is `0`. At every Walrasian equilibrium
  with both prices positive each type's utility is strictly below `1` (`exercise_18_E_3`); an
  equilibrium with prices `(1/2, 1/2)` exists. With prices `(1, 0)` (also an equilibrium)
  type 0 gets exactly `1`, so positivity of both prices is needed for "every trader".
* p. 673: the efficiency identity of the Shapley value of the TU game of a finite economy,
  `∑ᵢ Shᵢ = v(I)` (`claim_18_E_shapley_sum`), from Chapter 22's `shapley_pareto`.
-/

namespace MWG.CoreFoundations

open Filter Topology

variable {K : ℕ}

/-! ### The square-root economy -/

/-- **Section 18.E** example (MWG, pp. 670-672). Two types, one non-numeraire good,
`ψ_h(y) = 2√y`; type 0 owns one unit of the good, type 1 owns nothing (both own no money). -/
noncomputable def sqrtQLEconomy : QLEconomy (Fin 2) 1 where
  ψ := fun _ y => 2 * Real.sqrt (y 0)
  ω := ![((fun _ => 1 : Fin 1 → ℝ), (0 : ℝ)), (0, 0)]

/-- The square-root economy satisfies the concavity hypothesis. -/
theorem sqrtQL_concave : ∀ h, ConcaveOn ℝ (Set.Ici 0) (sqrtQLEconomy.ψ h) := by
  intro h
  refine ⟨convex_Ici 0, fun y hy y' hy' a b ha hb hab => ?_⟩
  have := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 ((Set.mem_Ici.1 hy) 0))
    (Set.mem_Ici.2 ((Set.mem_Ici.1 hy') 0)) ha hb hab
  simp only [sqrtQLEconomy, smul_eq_mul, Pi.add_apply, Pi.smul_apply] at this ⊢
  linarith

/-- The square-root economy satisfies the monotonicity hypothesis. -/
theorem sqrtQL_mono : ∀ h, MonotoneOn (sqrtQLEconomy.ψ h) (Set.Ici 0) := by
  intro h y _ y' _ hle
  simp only [sqrtQLEconomy]
  gcongr
  exact hle 0

/-- `ψ_h` is differentiable at every `y` with `y > 0`. -/
theorem sqrtQL_differentiableAt (h : Fin 2) {y : Fin 1 → ℝ} (hy : 0 < y 0) :
    DifferentiableAt ℝ (sqrtQLEconomy.ψ h) y :=
  ((differentiableAt_apply 0 y).sqrt hy.ne').const_mul 2

/-- Endowments of non-numeraire goods are nonnegative. -/
theorem sqrtQL_omega_nonneg : ∀ h, 0 ≤ (sqrtQLEconomy.ω h).1 := by
  intro h l
  fin_cases h <;> simp [sqrtQLEconomy]

/-- Every feasible allocation gives at most `2√((μ₀ + μ₁) μ₀)` (Cauchy-Schwarz). -/
theorem sqrtQL_welfare_le {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) {x : Fin 2 → (Fin 1 → ℝ) × ℝ}
    (hx : sqrtQLEconomy.IsFeasible μ x) :
    sqrtQLEconomy.welfare μ x ≤ 2 * √((μ 0 + μ 1) * μ 0) := by
  have hy : μ 0 * (x 0).1 0 + μ 1 * (x 1).1 0 ≤ μ 0 := by
    simpa [Fin.sum_univ_two, sqrtQLEconomy] using hx.2.1 0
  have hm : μ 0 * (x 0).2 + μ 1 * (x 1).2 ≤ 0 := by
    simpa [Fin.sum_univ_two, sqrtQLEconomy] using hx.2.2
  have ha : 0 ≤ (x 0).1 0 := hx.1 0 0
  have hb : 0 ≤ (x 1).1 0 := hx.1 1 0
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set s := √((x 0).1 0)
  set t := √((x 1).1 0)
  have hs : s ^ 2 = (x 0).1 0 := Real.sq_sqrt ha
  have ht : t ^ 2 = (x 1).1 0 := Real.sq_sqrt hb
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have key : μ 0 * s + μ 1 * t ≤ √((μ 0 + μ 1) * μ 0) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [← hs, ← ht] at hy
    have e : (μ 0 + μ 1) * (μ 0 * s ^ 2 + μ 1 * t ^ 2) - (μ 0 * s + μ 1 * t) ^ 2 =
        μ 0 * μ 1 * (s - t) ^ 2 := by ring
    linarith [mul_nonneg (mul_nonneg h0 h1) (sq_nonneg (s - t)),
      mul_le_mul_of_nonneg_left hy (add_nonneg h0 h1)]
  simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy]
  nlinarith

/-- **Section 18.E** example (MWG, p. 671). `v(μ) = 2√((μ₀ + μ₁) μ₀)` on `ℝ²₊`, attained by
giving each type `μ₀/(μ₀ + μ₁)` units of the good. -/
theorem sqrtQL_v {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) :
    sqrtQLEconomy.v μ = 2 * √((μ 0 + μ 1) * μ 0) := by
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set c := μ 0 / (μ 0 + μ 1)
  have hc : 0 ≤ c := div_nonneg h0 (add_nonneg h0 h1)
  have hSc : (μ 0 + μ 1) * c ≤ μ 0 := by
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · rw [← hS, zero_mul]; exact h0
    · rw [mul_div_cancel₀ _ hS.ne']
  let x : Fin 2 → (Fin 1 → ℝ) × ℝ := fun _ => (fun _ => c, 0)
  have hfeas : sqrtQLEconomy.IsFeasible μ x := by
    refine ⟨fun _ _ => hc, fun l => ?_, ?_⟩
    · simp [x, Fin.sum_univ_two, sqrtQLEconomy]
      linarith
    · simp [x, Fin.sum_univ_two, sqrtQLEconomy]
  have hval : sqrtQLEconomy.welfare μ x = 2 * √((μ 0 + μ 1) * μ 0) := by
    simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy, x, add_zero]
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · have e0 : μ 0 = 0 := by linarith
      have e1 : μ 1 = 0 := by linarith
      simp [e0, e1]
    · have : (μ 0 + μ 1) * √c = √((μ 0 + μ 1) * μ 0) := by
        have e1 : (μ 0 + μ 1) * μ 0 = (μ 0 + μ 1) ^ 2 * c := by
          simp only [c]
          field_simp
        rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS.le]
      linear_combination 2 * this
  refine IsGreatest.csSup_eq ⟨⟨x, hfeas, hval⟩, ?_⟩
  rintro s ⟨x', hx', rfl⟩
  exact sqrtQL_welfare_le hμ hx'

/-- The population `μ = (1, 1)`, i.e. the finite economy with one consumer of each type. -/
def qlOnes : Fin 2 → ℝ := fun _ => 1

/-- **Footnote 21** instance (MWG, p. 671). In the square-root economy `v` is differentiable at
`μ = (1, 1)`. -/
theorem sqrtQL_v_differentiableAt : DifferentiableAt ℝ sqrtQLEconomy.v qlOnes := by
  have hF : DifferentiableAt ℝ (fun μ : Fin 2 → ℝ => 2 * √((μ 0 + μ 1) * μ 0)) qlOnes :=
    ((((differentiableAt_apply 0 qlOnes).add (differentiableAt_apply 1 qlOnes)).mul
      (differentiableAt_apply 0 qlOnes)).sqrt (by norm_num [qlOnes])).const_mul 2
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [ql_eventually_nonneg_of_pos (μ := qlOnes) (fun _ => one_pos)] with ν hν
  exact sqrtQL_v hν

/-- The Walrasian allocation of the square-root economy at `μ = (1, 1)`: each type consumes `1/2`
of the good; type 0 receives `√2/2` units of money, type 1 pays `√2/2`. -/
noncomputable def sqrtQLStar : Fin 2 → (Fin 1 → ℝ) × ℝ :=
  ![((fun _ => 1 / 2 : Fin 1 → ℝ), √2 / 2), (fun _ => 1 / 2, -(√2 / 2))]

/-- `√(1/2) = √2/2`. -/
theorem ql_sqrt_half : √(1 / 2 : ℝ) = √2 / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The tangent line of `2√y` at `y = 1/2`: `2√y ≤ √2 y + √2/2`. -/
theorem ql_sqrt_tangent {y : ℝ} (hy : 0 ≤ y) : 2 * √y ≤ √2 * y + √2 / 2 := by
  have hs := Real.sq_sqrt hy
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have e : √2 * (√y - √2 / 2) ^ 2 = √2 * √y ^ 2 - (√2 * √2) * √y + (√2 * √2) * √2 / 4 := by
    ring
  rw [h2, hs] at e
  linarith [mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg (√y - √2 / 2))]

/-- **Section 18.E** example (MWG, pp. 671-672). `(√2, x*)` is a Walrasian equilibrium of the
square-root economy with `μ = (1, 1)`. -/
theorem sqrtQL_walras : sqrtQLEconomy.IsWalrasEqm qlOnes (fun _ => √2) sqrtQLStar := by
  have hu : ∀ h, sqrtQLEconomy.u h (sqrtQLStar h) =
      qlPrice (fun _ => √2) (sqrtQLEconomy.ω h) + √2 / 2 := by
    intro h
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h2' : (0 : ℝ) < √2 := by positivity
    fin_cases h <;>
      simp [QLEconomy.u, qlPrice, sqrtQLEconomy, sqrtQLStar, dotProduct] <;> field_simp <;>
      nlinarith
  refine ⟨⟨fun h l => ?_, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' hx' hb => ?_⟩⟩
  · fin_cases h <;> simp [sqrtQLStar]
  · simp [Fin.sum_univ_two, sqrtQLStar, sqrtQLEconomy, qlOnes]
    norm_num
  · simp [Fin.sum_univ_two, sqrtQLStar, sqrtQLEconomy, qlOnes]
  · fin_cases h <;> simp [qlPrice, sqrtQLStar, sqrtQLEconomy, dotProduct] <;> ring_nf <;> simp
  · rw [hu]
    have ht := ql_sqrt_tangent (hx' 0)
    simp only [qlPrice, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton] at hb
    simp only [QLEconomy.u, sqrtQLEconomy, qlPrice, dotProduct, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton] at hb ⊢
    linarith

/-- **(18.E.5)** instance (MWG, p. 672). The partial derivatives of `v` at `(1, 1)` are the
Walrasian utilities: `∂v/∂μ₀ = 3√2/2` and `∂v/∂μ₁ = √2/2`. -/
theorem sqrtQL_partial :
    fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single 0 1) = 3 * √2 / 2 ∧
      fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single 1 1) = √2 / 2 := by
  have hD := sqrtQL_v_differentiableAt.hasFDerivAt
  have e := fun h => sqrtQLEconomy.partial_v_of_walras sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras hD h
  rw [e 0, e 1]
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2' : (0 : ℝ) < √2 := by positivity
  constructor <;>
    simp [QLEconomy.u, sqrtQLEconomy, sqrtQLStar] <;> field_simp <;> nlinarith

/-- **Definition 18.E.1** instance (MWG, p. 671). The Walrasian allocation of the square-root
economy is a marginal product allocation. -/
theorem definition_18_E_1_instance : sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar :=
  proposition_18_E_1_of_walras sqrtQLEconomy sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras sqrtQL_v_differentiableAt

/-- **Proposition 18.E.1** instance (MWG, p. 671). All hypotheses of `proposition_18_E_1` hold
for the square-root economy at `μ = (1, 1)` and `x* = sqrtQLStar` (with `y* = 1/2 > 0`), and
both sides of the equivalence are true. -/
theorem proposition_18_E_1_instance :
    (sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar ↔
      ∃ q, sqrtQLEconomy.IsWalrasEqm qlOnes q sqrtQLStar) ∧
      sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar := by
  have hint : ∀ h l, 0 < (sqrtQLStar h).1 l := by
    intro h l; fin_cases h <;> simp [sqrtQLStar]
  refine ⟨proposition_18_E_1 sqrtQLEconomy sqrtQL_concave sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras.1 hint (fun h => sqrtQL_differentiableAt h (hint h 0))
    sqrtQL_v_differentiableAt, definition_18_E_1_instance⟩

/-- **(18.E.2)** instance (MWG, p. 671). The Walrasian allocation of the square-root economy
solves (18.E.2) for `μ = (1, 1)` (its welfare `2√2` equals the bound of `sqrtQL_welfare_le`); so
the hypotheses of `exercise_18_E_2` and `claim_18_E_finite_walras_iff` are satisfiable. -/
theorem sqrtQL_optimal : sqrtQLEconomy.IsOptimal qlOnes sqrtQLStar := by
  have hw : sqrtQLEconomy.welfare qlOnes sqrtQLStar = 2 * √2 := by
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h2' : (0 : ℝ) < √2 := by positivity
    simp [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy, sqrtQLStar, qlOnes]
    field_simp
    nlinarith
  refine ⟨sqrtQL_walras.1, fun x' hx' => ?_⟩
  have hb := sqrtQL_welfare_le (μ := qlOnes) (fun _ => zero_le_one) hx'
  rw [show (qlOnes 0 + qlOnes 1) * qlOnes 0 = (2 : ℝ) by norm_num [qlOnes]] at hb
  rw [hw]
  exact hb

/-- **Exercise 18.E.1** instance (MWG, p. 671). In the square-root economy `v` is concave on
`ℝ²₊`. -/
theorem sqrtQL_v_concave : ConcaveOn ℝ (Set.Ici 0) sqrtQLEconomy.v :=
  (exercise_18_E_1 sqrtQLEconomy sqrtQL_concave sqrtQL_mono
    (fun h => ⟨fun _ => 1, fun _ => zero_le_one,
      sqrtQL_differentiableAt h (by norm_num)⟩) sqrtQL_omega_nonneg).1

/-- **Section 18.E** example (MWG, p. 672). The finite marginal contributions with one consumer
of each type: `Δ₀v(1, 1) = 2√2` and `Δ₁v(1, 1) = 2√2 - 2`. -/
theorem sqrtQL_deltaV :
    sqrtQLEconomy.deltaV qlOnes 0 = 2 * √2 ∧ sqrtQLEconomy.deltaV qlOnes 1 = 2 * √2 - 2 := by
  have hv11 : sqrtQLEconomy.v qlOnes = 2 * √2 := by
    rw [sqrtQL_v (μ := qlOnes) (fun _ => zero_le_one)]
    norm_num [qlOnes]
  have hnn : ∀ h, 0 ≤ qlOnes - Pi.single h 1 := by
    intro h k
    fin_cases h <;> fin_cases k <;> simp [qlOnes]
  unfold QLEconomy.deltaV
  rw [hv11, sqrtQL_v (hnn 0), sqrtQL_v (hnn 1)]
  constructor <;> norm_num [qlOnes]

/-- **Section 18.E** (MWG, p. 672), "typically `Δ_h v > ∂v/∂μ_h`" and
"`∑_h I_h Δ_h v > v(I)`", strictly, in the square-root economy with `I = (1, 1)`. -/
theorem example_18_E_finite_strict :
    (∀ h, fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single h 1) < sqrtQLEconomy.deltaV qlOnes h) ∧
      sqrtQLEconomy.v qlOnes < ∑ h, qlOnes h * sqrtQLEconomy.deltaV qlOnes h := by
  obtain ⟨p0, p1⟩ := sqrtQL_partial
  obtain ⟨d0, d1⟩ := sqrtQL_deltaV
  have hs : (4 / 3 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs0 : 0 < √2 := by positivity
  have hv11 : sqrtQLEconomy.v qlOnes = 2 * √2 := by
    rw [sqrtQL_v (μ := qlOnes) (fun _ => zero_le_one)]
    norm_num [qlOnes]
  refine ⟨fun h => ?_, ?_⟩
  · fin_cases h
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [p0, d0]; linarith
    · simp only [Fin.mk_one, Fin.isValue]
      rw [p1, d1]; linarith
  · rw [hv11, Fin.sum_univ_two, d0, d1]
    simp only [qlOnes]
    linarith

/-- **Section 18.E** (MWG, p. 672) instance: with one consumer of each type in the square-root
economy, no feasible allocation gives every consumer her full marginal contribution
`Δ_h v(1, 1)`. -/
theorem example_18_E_no_full_marginal :
    ¬ ∃ x, sqrtQLEconomy.IsFeasible qlOnes x ∧
      ∀ h, sqrtQLEconomy.deltaV qlOnes h ≤ sqrtQLEconomy.u h (x h) := by
  refine claim_18_E_no_full_marginal sqrtQLEconomy (fun _ => zero_le_one) ?_
    example_18_E_finite_strict.2
  refine ⟨2 * √((qlOnes 0 + qlOnes 1) * qlOnes 0), ?_⟩
  rintro s ⟨x, hx, rfl⟩
  exact sqrtQL_welfare_le (fun _ => zero_le_one) hx

/-- **Section 18.E** (MWG, p. 672) instance: "in a finite economy the Walrasian allocation is
typically not a marginal product allocation": in the square-root economy with `I = (1, 1)` each
consumer's Walrasian utility is strictly below her marginal contribution `Δ_h v(1, 1)`. -/
theorem example_18_E_walras_below_delta (h : Fin 2) :
    sqrtQLEconomy.u h (sqrtQLStar h) < sqrtQLEconomy.deltaV qlOnes h := by
  have hmp := definition_18_E_1_instance.2 h
  rw [hmp]
  exact example_18_E_finite_strict.1 h

/-- **Section 18.E** (MWG, p. 672) instance of `claim_18_E_deltaV_ge_partial` and
`claim_18_E_sum_deltaV_ge`: their hypotheses hold in the square-root economy at `I = (1, 1)`. -/
theorem example_18_E_finite_claims :
    (∀ h, fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single h 1) ≤ sqrtQLEconomy.deltaV qlOnes h) ∧
      sqrtQLEconomy.v qlOnes ≤ ∑ h, qlOnes h * sqrtQLEconomy.deltaV qlOnes h := by
  have hnn : ∀ h, 0 ≤ qlOnes - Pi.single h 1 := by
    intro h k
    fin_cases h <;> fin_cases k <;> simp [qlOnes]
  have hD := sqrtQL_v_differentiableAt.hasFDerivAt
  exact ⟨fun h => claim_18_E_deltaV_ge_partial sqrtQLEconomy sqrtQL_v_concave (hnn h) hD,
    claim_18_E_sum_deltaV_ge sqrtQLEconomy sqrtQL_v_concave hnn hD⟩

/-! ### Exercise 18.E.3: Leontief preferences -/

/-- **Exercise 18.E.3** (MWG, p. 685). Two types, two non-numeraire goods, L-shaped preferences
`ψ_h(y) = min(y₁, y₂)`; type 0 owns one unit of good 1, type 1 one unit of good 2 (no money). -/
noncomputable def leontiefQLEconomy : QLEconomy (Fin 2) 2 where
  ψ := fun _ y => min (y 0) (y 1)
  ω := ![((![1, 0] : Fin 2 → ℝ), (0 : ℝ)), (![0, 1], 0)]

/-- The Leontief `ψ_h` is concave on `ℝ²₊`. -/
theorem leontief_concave : ∀ h, ConcaveOn ℝ (Set.Ici 0) (leontiefQLEconomy.ψ h) := by
  intro h
  refine ⟨convex_Ici 0, fun y _ y' _ a b ha hb _ => ?_⟩
  simp only [leontiefQLEconomy, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  refine le_min ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left (y 0) (y 1)) ha,
      mul_le_mul_of_nonneg_left (min_le_left (y' 0) (y' 1)) hb]
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_right (y 0) (y 1)) ha,
      mul_le_mul_of_nonneg_left (min_le_right (y' 0) (y' 1)) hb]

/-- The Leontief `ψ_h` is nondecreasing. -/
theorem leontief_mono : ∀ h, MonotoneOn (leontiefQLEconomy.ψ h) (Set.Ici 0) := by
  intro h y _ y' _ hle
  exact min_le_min (hle 0) (hle 1)

/-- Every feasible allocation of the Leontief economy gives at most `min(μ₀, μ₁)`. -/
theorem leontief_welfare_le {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) {x : Fin 2 → (Fin 2 → ℝ) × ℝ}
    (hx : leontiefQLEconomy.IsFeasible μ x) :
    leontiefQLEconomy.welfare μ x ≤ min (μ 0) (μ 1) := by
  have hy0 := hx.2.1 0
  have hy1 := hx.2.1 1
  have hm := hx.2.2
  simp [Fin.sum_univ_two, leontiefQLEconomy] at hy0 hy1 hm
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, leontiefQLEconomy]
  refine le_min ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left ((x 0).1 0) ((x 0).1 1)) h0,
      mul_le_mul_of_nonneg_left (min_le_left ((x 1).1 0) ((x 1).1 1)) h1]
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_right ((x 0).1 0) ((x 0).1 1)) h0,
      mul_le_mul_of_nonneg_left (min_le_right ((x 1).1 0) ((x 1).1 1)) h1]

/-- **Exercise 18.E.3** (MWG, p. 685). In the Leontief economy `v(μ) = min(μ₀, μ₁)` on `ℝ²₊`. -/
theorem leontief_v {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) : leontiefQLEconomy.v μ = min (μ 0) (μ 1) := by
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set c := min (μ 0) (μ 1) / (μ 0 + μ 1)
  have hc : 0 ≤ c := div_nonneg (le_min h0 h1) (add_nonneg h0 h1)
  have hSc : (μ 0 + μ 1) * c = min (μ 0) (μ 1) := by
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · have e0 : μ 0 = 0 := by linarith
      have e1 : μ 1 = 0 := by linarith
      simp [e0, e1]
    · exact mul_div_cancel₀ _ hS.ne'
  let x : Fin 2 → (Fin 2 → ℝ) × ℝ := fun _ => (fun _ => c, 0)
  have hfeas : leontiefQLEconomy.IsFeasible μ x := by
    refine ⟨fun _ _ => hc, fun l => ?_, ?_⟩
    · fin_cases l <;> simp [x, Fin.sum_univ_two, leontiefQLEconomy] <;>
        nlinarith [min_le_left (μ 0) (μ 1), min_le_right (μ 0) (μ 1)]
    · simp [x, Fin.sum_univ_two, leontiefQLEconomy]
  have hval : leontiefQLEconomy.welfare μ x = min (μ 0) (μ 1) := by
    simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, leontiefQLEconomy, x,
      min_self, add_zero]
    linarith
  refine IsGreatest.csSup_eq ⟨⟨x, hfeas, hval⟩, ?_⟩
  rintro s ⟨x', hx', rfl⟩
  exact leontief_welfare_le hμ hx'

/-- Along the `h`-th coordinate line through `(1, 1)`, `v = min(1 + t, 1)` (for `t ≥ -1`). -/
theorem leontief_line (h : Fin 2) {t : ℝ} (ht : -1 ≤ t) :
    leontiefQLEconomy.v (qlOnes + t • Pi.single h 1) = min (1 + t) 1 := by
  have hnn : 0 ≤ qlOnes + t • Pi.single h 1 := by
    intro k
    fin_cases h <;> fin_cases k <;> simp [qlOnes] <;> linarith
  rw [leontief_v hnn]
  fin_cases h <;> simp [qlOnes, min_comm]

/-- **Exercise 18.E.3** (MWG, p. 685). The marginal contribution of a trader of either type at
`μ = (1, 1)`, read as the loss from removing a marginal trader (the left partial derivative of
`v`), is `1`. -/
theorem exercise_18_E_3_left_deriv (h : Fin 2) :
    HasDerivWithinAt (fun t : ℝ => leontiefQLEconomy.v (qlOnes + t • Pi.single h 1)) 1
      (Set.Iic 0) 0 := by
  have hlin : HasDerivWithinAt (fun t : ℝ => 1 + t) 1 (Set.Iic 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).hasDerivWithinAt (s := Set.Iic 0)
  refine hlin.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with t ht ht'
    rw [leontief_line h ht'.le, min_eq_left (by linarith [Set.mem_Iic.1 ht])]
  · rw [leontief_line h (by norm_num)]
    norm_num

/-- **Exercise 18.E.3** (MWG, p. 685). The right partial derivative of `v` at `(1, 1)` (the gain
from adding a marginal trader) is `0`. -/
theorem exercise_18_E_3_right_deriv (h : Fin 2) :
    HasDerivWithinAt (fun t : ℝ => leontiefQLEconomy.v (qlOnes + t • Pi.single h 1)) 0
      (Set.Ici 0) 0 := by
  have hc : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ici 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℝ)).hasDerivWithinAt
  refine hc.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [leontief_line h (by linarith [Set.mem_Ici.1 ht]),
      min_eq_right (by linarith [Set.mem_Ici.1 ht])]
  · rw [leontief_line h (by norm_num)]
    norm_num

/-- **Exercise 18.E.3** (MWG, p. 685). With L-shaped preferences `v` is not differentiable at
`(1, 1)` (left and right partial derivatives `1 ≠ 0`). -/
theorem exercise_18_E_3_not_differentiable :
    ¬ DifferentiableAt ℝ leontiefQLEconomy.v qlOnes := by
  intro hd
  have hφ := ql_hasDerivAt_line hd.hasFDerivAt (Pi.single (0 : Fin 2) (1 : ℝ))
  have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Iic 0 0 (Set.mem_Iic.2 le_rfl))
    hφ.hasDerivWithinAt (exercise_18_E_3_left_deriv 0)
  have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.2 le_rfl))
    hφ.hasDerivWithinAt (exercise_18_E_3_right_deriv 0)
  rw [e1] at e2
  exact one_ne_zero e2

/-- **Exercise 18.E.3** (MWG, p. 685). The finite marginal contribution `Δ_h v(1, 1)` is also
`1`. -/
theorem exercise_18_E_3_delta (h : Fin 2) : leontiefQLEconomy.deltaV qlOnes h = 1 := by
  have h1 := leontief_line h (t := -1) le_rfl
  rw [neg_one_smul, ← sub_eq_add_neg] at h1
  unfold QLEconomy.deltaV
  rw [h1, leontief_v (μ := qlOnes) (fun _ => zero_le_one)]
  norm_num [qlOnes]

/-- **Exercise 18.E.3** (MWG, p. 685). At every Walrasian equilibrium of the Leontief economy
with `μ = (1, 1)` and both prices positive, every trader gets strictly less than her marginal
contribution `1` (`exercise_18_E_3_left_deriv`, `exercise_18_E_3_delta`). Each type gets at
least the value of her endowment `q_h` (buying nothing), and the two utilities sum to at most
`v(1, 1) = 1`. -/
theorem exercise_18_E_3 {q : Fin 2 → ℝ} {x : Fin 2 → (Fin 2 → ℝ) × ℝ}
    (hW : leontiefQLEconomy.IsWalrasEqm qlOnes q x) (hq0 : 0 < q 0) (hq1 : 0 < q 1)
    (h : Fin 2) : leontiefQLEconomy.u h (x h) < 1 := by
  have hlow : ∀ k, qlPrice q (leontiefQLEconomy.ω k) ≤ leontiefQLEconomy.u k (x k) := by
    intro k
    have := (hW.2 k).2 (0, qlPrice q (leontiefQLEconomy.ω k)) le_rfl (by simp [qlPrice])
    simpa [QLEconomy.u, leontiefQLEconomy] using this
  have hsum := leontief_welfare_le (fun _ => zero_le_one) hW.1
  simp only [QLEconomy.welfare, Fin.sum_univ_two, one_mul, min_self] at hsum
  have p0 : qlPrice q (leontiefQLEconomy.ω 0) = q 0 := by
    simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  have p1 : qlPrice q (leontiefQLEconomy.ω 1) = q 1 := by
    simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  have l0 := hlow 0
  have l1 := hlow 1
  rw [p0] at l0
  rw [p1] at l1
  fin_cases h
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; linarith

/-- **Exercise 18.E.3** (MWG, p. 685). The Walrasian equilibrium with prices `(1/2, 1/2)`: each
type consumes `(1/2, 1/2)` and gets utility `1/2 < 1`. -/
theorem exercise_18_E_3_eqm :
    leontiefQLEconomy.IsWalrasEqm qlOnes (fun _ => 1 / 2) (fun _ => (fun _ => 1 / 2, 0)) := by
  refine ⟨⟨fun _ _ => by norm_num, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' _ hb => ?_⟩⟩
  · fin_cases l <;> simp [Fin.sum_univ_two, leontiefQLEconomy, qlOnes]
  · simp [Fin.sum_univ_two, leontiefQLEconomy]
  · fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  · have hω : qlPrice (fun _ => (1 : ℝ) / 2) (leontiefQLEconomy.ω h) = 1 / 2 := by
      fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
    rw [hω] at hb
    simp only [qlPrice, dotProduct, Fin.sum_univ_two] at hb
    simp only [QLEconomy.u, leontiefQLEconomy, min_self, add_zero]
    have := min_le_left (x'.1 0) (x'.1 1)
    have := min_le_right (x'.1 0) (x'.1 1)
    linarith

/-- **Exercise 18.E.3** (MWG, p. 685), boundary prices. `(1, 0)` with `x*₀ = ((1, 1), 0)`,
`x*₁ = 0` is also a Walrasian equilibrium, and there type 0 gets exactly her marginal
contribution `1`: positivity of both prices is needed for "every trader gets less". -/
theorem exercise_18_E_3_boundary :
    leontiefQLEconomy.IsWalrasEqm qlOnes ![1, 0] ![((fun _ => 1 : Fin 2 → ℝ), (0 : ℝ)), 0] ∧
      leontiefQLEconomy.u 0 (![((fun _ => 1 : Fin 2 → ℝ), (0 : ℝ)), 0] 0) = 1 := by
  refine ⟨⟨⟨fun h l => ?_, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' hx' hb => ?_⟩⟩, ?_⟩
  · fin_cases h <;> simp
  · fin_cases l <;> simp [Fin.sum_univ_two, leontiefQLEconomy, qlOnes]
  · simp [Fin.sum_univ_two, leontiefQLEconomy]
  · fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  · have := min_le_left (x'.1 0) (x'.1 1)
    fin_cases h <;>
      simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two, QLEconomy.u] at hb ⊢ <;>
      linarith
  · simp [QLEconomy.u, leontiefQLEconomy]

/-- **Exercise 18.E.3** hypotheses (MWG, p. 685): the Leontief economy satisfies the concavity,
monotonicity and endowment hypotheses of Proposition 18.E.1; what fails is the differentiability
of `v` (`exercise_18_E_3_not_differentiable`), and indeed the Walrasian utilities `1/2` differ
from both one-sided partial derivatives `1` and `0`. -/
theorem exercise_18_E_3_hypotheses :
    (∀ h, ConcaveOn ℝ (Set.Ici 0) (leontiefQLEconomy.ψ h)) ∧
      (∀ h, MonotoneOn (leontiefQLEconomy.ψ h) (Set.Ici 0)) ∧
      (∀ h, 0 ≤ (leontiefQLEconomy.ω h).1) ∧ ¬ DifferentiableAt ℝ leontiefQLEconomy.v qlOnes := by
  refine ⟨leontief_concave, leontief_mono, fun h l => ?_, exercise_18_E_3_not_differentiable⟩
  fin_cases h <;> fin_cases l <;> simp [leontiefQLEconomy]

/-! ### The Shapley value (p. 673) -/

/-- **Section 18.E** (MWG, p. 673). The TU game of a finite economy with consumers
`i : Fin n` of types `τ i`: the worth of a coalition `S` is `v` of its type profile. -/
noncomputable def qlShapleyGame {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (E : QLEconomy H K) (τ : Fin n → H) :
    MWG.WelfareBargaining.Game n :=
  fun S => E.v (fun h => ((S.filter fun i => τ i = h).card : ℝ))

/-- **Section 18.E** (MWG, p. 673). The Shapley value of the economy's TU game distributes
exactly `v(I)`: `∑ᵢ Shᵢ = v(I)` (grouping consumers by type, `∑_h I_h Sh_h = v(I)` when equal
types get equal values). From Chapter 22's `shapley_pareto` and `v(0) = 0`. -/
theorem claim_18_E_shapley_sum {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (E : QLEconomy H K) (τ : Fin n → H) :
    ∑ i, MWG.WelfareBargaining.shapley (qlShapleyGame E τ) i = E.v (qlTypeCount τ) := by
  rw [MWG.WelfareBargaining.shapley_pareto]
  · rfl
  · simp only [qlShapleyGame, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact E.v_zero

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cooperative games: characteristic form and the core (MWG Appendix A, pp. 673-679)

Players are `Fin n` (`I = {1, ..., I}`), coalitions are nonempty `S : Finset (Fin n)`, and an
outcome is `u : Fin n → ℝ`.

**Representation of `ℝ^S`.** A subset `U^S ⊆ ℝ^S` is represented by the cylinder
`{u ∈ ℝ^I : u^S ∈ U^S}`, a set of outcomes whose membership depends only on the coordinates in
`S`. Definition 18.AA.1 is stated on such sets (`IsUtilityPossibilitySet`); the bridge
`isUtilityPossibilitySet_iff` proves that this is exactly the preimage, under the projection
`u ↦ u^S` (`projS`, with values in `S → ℝ`), of a nonempty, closed, comprehensive subset of
`S → ℝ`. With this representation the pair `(u^S, u^T)` of Definition 18.AA.3 is the outcome
that agrees with `u` on `S` and with `u'` elsewhere.

* Definitions 18.AA.1-18.AA.2: utility possibility sets, games in characteristic form
  (`NTUGame`, `IsCharacteristicForm`).
* **Example 18.AA.1** (`econGame`): comprehensive, nonempty, convex (`example_18_AA_1_convex`)
  and superadditive (`example_18_AA_1_superadditive`). **Correction**: `V(S)` need not be closed
  when `Y` is not closed (`example_18_AA_1_not_closed`: `L = 2`, one consumer,
  `Y = {y : y₁ < 0, y₂ < -y₁} ∪ {0}`, `ω = (1, 0)`, `u(x) = x₂`, `V = (-∞, 1)`); it is closed when
  `Y` is closed and contained in `-ℝ^L₊` (`example_18_AA_1_closed`; closed cones with no free
  production in `Closer18AA`).
* **Example 18.AA.2** (`votingGame`): a game in characteristic form, superadditive; with the
  values of Figure 18.AA.4, `V(I)` is not convex (`example_18_AA_2_not_convex`).
* Definition 18.AA.3 (superadditivity); TU games (Definition 18.AA.4, `tuSet` on Chapter 22's
  `Game`): utility possibility sets, superadditive iff `v` is (`tuSet_superadditive_iff`);
  **Example 18.AA.3** (`tuMajority`, the worths are the maximal total utilities).
* Definitions 18.AA.5-18.AA.6 (`ntuBlocks`, `ntuCore`), the TU specialisations
  (`tu_blocks_iff`, `ntuCore_tuSet`), **Exercise 18.AA.2**, **Example 18.AA.4** (both majority
  games have empty cores), **Example 18.AA.5** (the core of an economy and of its game),
  **Example 18.AA.6** and **Exercise 18.AA.3** (production games), **footnote 28**.

The Bondareva-Shapley theorem (Exercise 18.AA.1) is in `MWGCoreFoundations.Balanced`.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {n : ℕ}

/-! ### Outcomes, utility possibility sets, games in characteristic form -/

/-- **Appendix A** (MWG, p. 674). The projection `u^S = (uᵢ)_{i∈S} ∈ ℝ^S` of an outcome. -/
def projS (S : Finset (Fin n)) (u : Fin n → ℝ) : S → ℝ := fun i => u i

/-- **Definition 18.AA.1** (MWG, p. 674). A utility possibility set for the coalition `S`
(represented as a set of outcomes depending only on the coordinates in `S`): nonempty, closed
and comprehensive (`u ∈ U` and `u'^S ≤ u^S` imply `u' ∈ U`). -/
def IsUtilityPossibilitySet (S : Finset (Fin n)) (U : Set (Fin n → ℝ)) : Prop :=
  U.Nonempty ∧ IsClosed U ∧ ∀ u ∈ U, ∀ u' : Fin n → ℝ, (∀ i ∈ S, u' i ≤ u i) → u' ∈ U

/-- **Appendix A** (MWG, p. 674). The extension of `w ∈ ℝ^S` by zero outside `S`. -/
noncomputable def extS (S : Finset (Fin n)) (w : S → ℝ) : Fin n → ℝ := fun i => by
  classical
  exact if h : i ∈ S then w ⟨i, h⟩ else 0

/-- **Appendix A** (MWG, p. 674). `(ext_S w)^S = w`. -/
theorem projS_extS (S : Finset (Fin n)) (w : S → ℝ) : projS S (extS S w) = w := by
  funext i
  simp [projS, extS, i.2]

/-- **Appendix A** (MWG, p. 674). The projection `u ↦ u^S` is continuous. -/
theorem continuous_projS (S : Finset (Fin n)) : Continuous (projS S) :=
  continuous_pi fun i => continuous_apply (i : Fin n)

/-- **Appendix A** (MWG, p. 674). The extension by zero is continuous. -/
theorem continuous_extS (S : Finset (Fin n)) : Continuous (extS S) := by
  classical
  refine continuous_pi fun i => ?_
  by_cases h : i ∈ S
  · have : (fun w : S → ℝ => extS S w i) = fun w => w ⟨i, h⟩ := by
      funext w; simp [extS, h]
    rw [this]; exact continuous_apply _
  · have : (fun w : S → ℝ => extS S w i) = fun _ => 0 := by
      funext w; simp [extS, h]
    rw [this]; exact continuous_const

/-- **Definition 18.AA.1** (MWG, p. 674), bridge to `ℝ^S`: a set of outcomes is a utility
possibility set for `S` in our representation iff it is the preimage under `u ↦ u^S` of a
nonempty, closed, comprehensive subset of `ℝ^S = (S → ℝ)`. -/
theorem isUtilityPossibilitySet_iff (S : Finset (Fin n)) (U : Set (Fin n → ℝ)) :
    IsUtilityPossibilitySet S U ↔ ∃ W : Set (S → ℝ), W.Nonempty ∧ IsClosed W ∧
      (∀ w ∈ W, ∀ w' : S → ℝ, w' ≤ w → w' ∈ W) ∧ U = projS S ⁻¹' W := by
  constructor
  · rintro ⟨⟨u, hu⟩, hcl, hcomp⟩
    have hW : projS S '' U = extS S ⁻¹' U := by
      ext w
      constructor
      · rintro ⟨u', hu', rfl⟩
        refine hcomp u' hu' _ fun i hi => ?_
        simp [extS, projS, hi]
      · intro hw
        exact ⟨extS S w, hw, projS_extS S w⟩
    refine ⟨projS S '' U, ⟨projS S u, u, hu, rfl⟩, ?_, ?_, ?_⟩
    · rw [hW]; exact hcl.preimage (continuous_extS S)
    · rintro w ⟨u', hu', rfl⟩ w' hw'
      refine ⟨extS S w', hcomp u' hu' _ fun i hi => ?_, projS_extS S w'⟩
      have := hw' ⟨i, hi⟩
      simpa [extS, projS, hi] using this
    · ext u'
      constructor
      · intro h; exact ⟨u', h, rfl⟩
      · rintro ⟨u'', hu'', he⟩
        refine hcomp u'' hu'' u' fun i hi => ?_
        have := congrFun he ⟨i, hi⟩
        simp only [projS] at this
        rw [this]
  · rintro ⟨W, ⟨w, hw⟩, hcl, hcomp, rfl⟩
    refine ⟨⟨extS S w, by simp [projS_extS, hw]⟩, hcl.preimage (continuous_projS S), ?_⟩
    intro u hu u' hle
    exact hcomp _ hu _ fun i => hle i i.2

/-- **Definition 18.AA.2** (MWG, p. 675). A game in characteristic form `(I, V)`: a rule `V`
assigning to every coalition a set of payoffs (represented as in Definition 18.AA.1). -/
abbrev NTUGame (n : ℕ) := Finset (Fin n) → Set (Fin n → ℝ)

/-- **Definition 18.AA.2** (MWG, p. 675). `V(S)` is a utility possibility set for `S` for every
coalition `S`. -/
def IsCharacteristicForm (V : NTUGame n) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → IsUtilityPossibilitySet S (V S)

/-- **Definition 18.AA.3** (MWG, p. 676). Superadditivity: for disjoint coalitions `S, T`,
`u^S ∈ V(S)` and `u'^T ∈ V(T)` imply `(u^S, u'^T) ∈ V(S ∪ T)`. -/
def IsSuperadditive (V : NTUGame n) : Prop :=
  ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty → Disjoint S T → ∀ u u' : Fin n → ℝ,
    u ∈ V S → u' ∈ V T → (fun i => if i ∈ S then u i else u' i) ∈ V (S ∪ T)

/-! ### Example 18.AA.1: economies -/

variable {L : ℕ}

/-- **Example 18.AA.1** (MWG, p. 675). The game of an economy with utilities `uᵢ`, endowments
`ωᵢ` and the public technology `Y`: `V(S) = {(uᵢ(xᵢ))_{i∈S} : ∑_S xᵢ = ∑_S ωᵢ + y, y ∈ Y} - ℝ^S₊`
with `xᵢ ∈ ℝ^L₊`. -/
def econGame (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ) (Y : Set (Fin L → ℝ)) :
    NTUGame n := fun S =>
  {w | ∃ x : Fin n → Fin L → ℝ, (∀ i ∈ S, x i ∈ nonnegOrthant L) ∧
    (∃ y ∈ Y, ∑ i ∈ S, x i = ∑ i ∈ S, ω i + y) ∧ ∀ i ∈ S, w i ≤ u i (x i)}

/-- **Example 18.AA.1** (MWG, p. 675). `V(S)` is comprehensive. -/
theorem econGame_comprehensive (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ)
    (Y : Set (Fin L → ℝ)) (S : Finset (Fin n)) {w w' : Fin n → ℝ}
    (hw : w ∈ econGame u ω Y S) (hle : ∀ i ∈ S, w' i ≤ w i) : w' ∈ econGame u ω Y S := by
  obtain ⟨x, hx, hy, hu⟩ := hw
  exact ⟨x, hx, hy, fun i hi => (hle i hi).trans (hu i hi)⟩

/-- **Example 18.AA.1** (MWG, p. 675). `V(S)` is nonempty when `0 ∈ Y` and `ωᵢ ≥ 0`. -/
theorem econGame_nonempty (u : Fin n → (Fin L → ℝ) → ℝ) {ω : Fin n → Fin L → ℝ}
    {Y : Set (Fin L → ℝ)} (h0 : (0 : Fin L → ℝ) ∈ Y) (hω : ∀ i, ω i ∈ nonnegOrthant L)
    (S : Finset (Fin n)) : (econGame u ω Y S).Nonempty :=
  ⟨fun i => u i (ω i), ω, fun i _ => hω i, ⟨0, h0, by simp⟩, fun _ _ => le_rfl⟩

/-- **Example 18.AA.1** (MWG, p. 675; Exercise 16.E.2). With concave utilities on `ℝ^L₊` and a
convex technology, every `V(S)` is convex. -/
theorem example_18_AA_1_convex {u : Fin n → (Fin L → ℝ) → ℝ} (ω : Fin n → Fin L → ℝ)
    {Y : Set (Fin L → ℝ)} (hY : Convex ℝ Y) (hu : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (u i))
    (S : Finset (Fin n)) : Convex ℝ (econGame u ω Y S) := by
  rintro w₁ ⟨x₁, hx₁, ⟨y₁, hy₁, hs₁⟩, hu₁⟩ w₂ ⟨x₂, hx₂, ⟨y₂, hy₂, hs₂⟩, hu₂⟩ a b ha hb hab
  have hxS : ∀ i ∈ S, a • x₁ i + b • x₂ i ∈ nonnegOrthant L := fun i hi =>
    (hu i).1 (hx₁ i hi) (hx₂ i hi) ha hb hab
  refine ⟨a • x₁ + b • x₂, fun i hi => hxS i hi, ⟨a • y₁ + b • y₂, hY hy₁ hy₂ ha hb hab, ?_⟩,
    fun i hi => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, hs₁, hs₂]
    calc a • (∑ i ∈ S, ω i + y₁) + b • (∑ i ∈ S, ω i + y₂)
        = (a + b) • ∑ i ∈ S, ω i + (a • y₁ + b • y₂) := by module
      _ = ∑ i ∈ S, ω i + (a • y₁ + b • y₂) := by rw [hab, one_smul]
  · have hc := (hu i).2 (hx₁ i hi) (hx₂ i hi) ha hb hab
    simp only [smul_eq_mul] at hc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hu₁ i hi, hu₂ i hi]

/-- **Example 18.AA.1** (MWG, pp. 675-676). With a convex constant returns technology the game
of an economy is superadditive (the claim of p. 676). -/
theorem example_18_AA_1_superadditive (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ)
    {Y : Set (Fin L → ℝ)} (hY : IsCRSTechnology Y) : IsSuperadditive (econGame u ω Y) := by
  classical
  intro S T _ _ hST w w' ⟨x, hx, ⟨y, hy, hs⟩, hu⟩ ⟨x', hx', ⟨y', hy', hs'⟩, hu'⟩
  have hyy : y + y' ∈ Y := by
    have h := hY.1 hy hy' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have h2 := hY.2.2 _ h 2 (by norm_num)
    have e : (2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') = y + y' := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    rwa [e] at h2
  have hT : ∀ i ∈ T, i ∉ S := fun i hi hiS => Finset.disjoint_left.1 hST hiS hi
  refine ⟨fun i => if i ∈ S then x i else x' i, fun i hi => ?_, ⟨y + y', hyy, ?_⟩,
    fun i hi => ?_⟩
  · rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using hx i h
    · simpa [hT i h] using hx' i h
  · have e1 : ∑ i ∈ S, (if i ∈ S then x i else x' i) = ∑ i ∈ S, x i :=
      Finset.sum_congr rfl fun i hi => by simp [hi]
    have e2 : ∑ i ∈ T, (if i ∈ S then x i else x' i) = ∑ i ∈ T, x' i :=
      Finset.sum_congr rfl fun i hi => by simp [hT i hi]
    rw [Finset.sum_union hST, Finset.sum_union hST, e1, e2, hs, hs']
    abel
  · rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using hu i h
    · simpa [hT i h] using hu' i h

/-- **Example 18.AA.1** (MWG, p. 675), correction. The technology `{y : y₁ < 0, y₂ < -y₁} ∪ {0}` of
the correction to Example 18.AA.1. -/
def openConeTech : Set (Fin 2 → ℝ) := {y | y 0 < 0 ∧ y 1 < -y 0} ∪ {0}

/-- **Example 18.AA.1** (MWG, p. 675), correction. The technology `openConeTech` is a convex
constant returns technology (a convex cone). -/
theorem openConeTech_isCRS : IsCRSTechnology openConeTech := by
  refine ⟨?_, Or.inr rfl, ?_⟩
  · rintro a ha b hb s t hs ht hst
    simp only [openConeTech, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with ⟨ha0, ha1⟩ | rfl <;> rcases hb with ⟨hb0, hb1⟩ | rfl
    · left
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_lt_of_le hs with h | hs'
      · subst h
        have ht1 : t = 1 := by linarith
        subst ht1; constructor <;> linarith
      · have h1 := mul_pos hs' (neg_pos.2 ha0)
        have h2 := mul_pos hs' (by linarith : (0 : ℝ) < -(a 1 + a 0))
        have h3 := mul_nonneg ht (neg_pos.2 hb0).le
        have h4 := mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(b 1 + b 0))
        constructor <;> nlinarith
    · rcases eq_or_lt_of_le hs with h | hs'
      · subst h; right; simp
      · left
        simp only [smul_zero, add_zero, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_pos hs' (neg_pos.2 ha0)
        have h2 := mul_pos hs' (by linarith : (0 : ℝ) < -(a 1 + a 0))
        constructor <;> nlinarith
    · rcases eq_or_lt_of_le ht with h | ht'
      · subst h; right; simp
      · left
        simp only [smul_zero, zero_add, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_pos ht' (neg_pos.2 hb0)
        have h2 := mul_pos ht' (by linarith : (0 : ℝ) < -(b 1 + b 0))
        constructor <;> nlinarith
    · right; simp
  · intro y hy t ht
    simp only [openConeTech, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hy ⊢
    rcases hy with ⟨h0, h1⟩ | rfl
    · rcases eq_or_lt_of_le ht with h | ht'
      · subst h; right; simp
      · left
        simp only [Pi.smul_apply, smul_eq_mul]
        have h2 := mul_pos ht' (by linarith : (0 : ℝ) < -(y 1 + y 0))
        constructor <;> nlinarith
    · right; simp

/-- **Example 18.AA.1** (MWG, p. 675), correction: `V(S)` need not be closed. With `L = 2`, one
consumer with `ω = (1, 0)` and the continuous, increasing, concave utility `u(x) = x₂`, and the
convex constant returns technology `openConeTech`, `V(I) = {w : w₁ < 1}`, which is not closed. -/
theorem example_18_AA_1_not_closed :
    econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech Finset.univ =
      {w | w 0 < 1} ∧
    ¬ IsClosed (econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech
      Finset.univ) := by
  have hV : econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech Finset.univ =
      {w | w 0 < 1} := by
    ext w
    simp only [econGame, Finset.mem_univ, true_implies, Fin.sum_univ_one, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, ⟨y, hy, hs⟩, hu⟩
      have h0 := congrFun hs 0
      have h1 := congrFun hs 1
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hx0 := hx 0 0
      have hw := hu 0
      rcases hy with ⟨hy0, hy1⟩ | hy
      · linarith
      · rw [Set.mem_singleton_iff] at hy; subst hy
        simp only [Pi.zero_apply] at h1; linarith
    · intro hw
      refine ⟨fun _ => ![0, max (w 0) 0], fun _ l => ?_, ⟨![-1, max (w 0) 0], Or.inl ⟨?_, ?_⟩,
        ?_⟩, fun _ => ?_⟩
      · fin_cases l <;> simp
      · simp
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [max_lt_iff]; constructor <;> norm_num [hw]
      · funext l; fin_cases l <;> simp
      · rename_i j; fin_cases j; simp
  refine ⟨hV, fun hcl => ?_⟩
  rw [hV] at hcl
  have hc : IsClosed (Set.Iio (1 : ℝ)) := by
    have : Set.Iio (1 : ℝ) = (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' {w | w 0 < 1} := by
      ext t; simp
    rw [this]; exact hcl.preimage (continuous_pi fun _ => continuous_id)
  have := hc.closure_eq
  rw [closure_Iio] at this
  have h1 : (1 : ℝ) ∈ Set.Iic (1 : ℝ) := Set.mem_Iic.2 le_rfl
  rw [this] at h1
  exact lt_irrefl _ (Set.mem_Iio.1 h1)

open Filter Topology in
/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness: if the technology `Y` is closed and
contained in `-ℝ^L₊` (e.g. pure exchange, `Y = -ℝ^L₊`) and the utilities are continuous on
`ℝ^L₊`, then every `V(S)` is closed (the feasible consumptions lie in a compact box). -/
theorem example_18_AA_1_closed {u : Fin n → (Fin L → ℝ) → ℝ} {ω : Fin n → Fin L → ℝ}
    {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y) (hYneg : Y ⊆ nonposOrthant L)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) := by
  classical
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨ws, hws, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose x hx hy hux using hws
  choose y hyY hsum using hy
  set M : Fin n → Fin L → ℝ := fun _ => ∑ j ∈ S, ω j with hM
  set xt : ℕ → Fin n → Fin L → ℝ := fun k i => if i ∈ S then x k i else 0 with hxt
  have hxtS : ∀ k, ∀ i ∈ S, xt k i = x k i := fun k i hi => by simp [hxt, hi]
  have hbox : ∀ k, xt k ∈ Set.Icc (0 : Fin n → Fin L → ℝ) M := by
    intro k
    refine ⟨fun i l => ?_, fun i l => ?_⟩
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]; exact hx k i hi l
      · simp [hxt, hi]
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]
        have h1 : x k i l ≤ ∑ j ∈ S, x k j l :=
          Finset.single_le_sum (f := fun j => x k j l) (fun j hj => hx k j hj l) hi
        have h2 := congrFun (hsum k) l
        simp only [Finset.sum_apply, Pi.add_apply] at h2
        have h3 := hYneg (hyY k) l
        simp only [hM, Finset.sum_apply]
        linarith
      · simp only [hxt, hi, ↓reduceIte, hM, Pi.zero_apply, Finset.sum_apply]
        have h2 := congrFun (hsum k) l
        have h3 := hYneg (hyY k) l
        have h4 : 0 ≤ ∑ j ∈ S, x k j l := Finset.sum_nonneg fun j hj => hx k j hj l
        simp only [Finset.sum_apply, Pi.add_apply] at h2
        linarith
  obtain ⟨xb, hxb, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hbox
  have hcoord : ∀ i, Tendsto (fun k => xt (φ k) i) atTop (𝓝 (xb i)) :=
    fun i => tendsto_pi_nhds.1 hconv i
  have hxbnn : ∀ i, xb i ∈ nonnegOrthant L := fun i l => hxb.1 i l
  refine ⟨xb, fun i _ => hxbnn i, ⟨∑ i ∈ S, xb i - ∑ i ∈ S, ω i, ?_, by abel⟩, fun i hi => ?_⟩
  · refine hYc.mem_of_tendsto (f := fun k => y (φ k)) (b := atTop) ?_
      (Eventually.of_forall fun k => hyY _)
    have hy' : (fun k => y (φ k)) = fun k => ∑ i ∈ S, xt (φ k) i - ∑ i ∈ S, ω i := by
      funext k
      rw [Finset.sum_congr rfl fun i hi => hxtS (φ k) i hi, hsum (φ k)]
      abel
    rw [hy']
    exact (tendsto_finsetSum S fun i _ => hcoord i).sub tendsto_const_nhds
  · have hwl : Tendsto (fun k => ws (φ k) i) atTop (𝓝 (w i)) :=
      (tendsto_pi_nhds.1 hlim i).comp hφ.tendsto_atTop
    have hul : Tendsto (fun k => u i (xt (φ k) i)) atTop (𝓝 (u i (xb i))) :=
      ((hu i) (xb i) (hxbnn i)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hcoord i, Eventually.of_forall fun k l =>
          (hbox (φ k)).1 i l⟩)
    refine le_of_tendsto_of_tendsto hwl hul (Eventually.of_forall fun k => ?_)
    simp only [hxtS (φ k) i hi]
    exact hux (φ k) i hi

/-! ### Example 18.AA.2: majority voting -/

/-- **Example 18.AA.2** (MWG, p. 675). Majority voting among three players over the alternatives
`A` with payoffs `uᵢ(a)`: a coalition of at least two players can select any alternative,
`V(S) = {(uᵢ(a))_{i∈S} : a ∈ A} - ℝ^S₊`, and a single player can only withdraw, `V({i}) = -ℝ₊`. -/
def votingGame {A : Type*} (u : A → Fin 3 → ℝ) : NTUGame 3 := fun S =>
  if 2 ≤ S.card then {w | ∃ a, ∀ i ∈ S, w i ≤ u a i} else {w | ∀ i ∈ S, w i ≤ 0}

/-- **Example 18.AA.2** (MWG, p. 675). With finitely many alternatives (and at least one), the
majority voting game is a game in characteristic form. -/
theorem votingGame_isCharacteristicForm {A : Type*} [Finite A] [Nonempty A]
    (u : A → Fin 3 → ℝ) : IsCharacteristicForm (votingGame u) := by
  intro S _
  unfold votingGame
  split_ifs with h
  · refine ⟨⟨u (Classical.arbitrary A), Classical.arbitrary A, fun _ _ => le_rfl⟩, ?_, ?_⟩
    · have : {w : Fin 3 → ℝ | ∃ a, ∀ i ∈ S, w i ≤ u a i} =
          ⋃ a, ⋂ i ∈ S, {w | w i ≤ u a i} := by
        ext w; simp
      rw [this]
      exact isClosed_iUnion_of_finite fun a => isClosed_biInter fun i _ =>
        isClosed_le (continuous_apply i) continuous_const
    · rintro w ⟨a, ha⟩ w' hw'
      exact ⟨a, fun i hi => (hw' i hi).trans (ha i hi)⟩
  · refine ⟨⟨0, fun _ _ => le_rfl⟩, ?_, ?_⟩
    · have : {w : Fin 3 → ℝ | ∀ i ∈ S, w i ≤ 0} = ⋂ i ∈ S, {w | w i ≤ 0} := by
        ext w; simp
      rw [this]
      exact isClosed_biInter fun i _ => isClosed_le (continuous_apply i) continuous_const
    · intro w hw w' hw' i hi
      exact (hw' i hi).trans (hw i hi)

/-- **Definition 18.AA.3** (MWG, p. 676). The majority voting game of Example 18.AA.2 is
superadditive (nonnegative payoffs `uᵢ(a) ≥ 0`, at least one alternative). -/
theorem votingGame_superadditive {A : Type*} [Nonempty A] {u : A → Fin 3 → ℝ}
    (hu : ∀ a i, 0 ≤ u a i) : IsSuperadditive (votingGame u) := by
  classical
  intro S T hS hT hST w w' hw hw'
  have hcard : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  have hle : (S ∪ T).card ≤ 3 := by simpa using Finset.card_le_univ (S ∪ T)
  have hS1 := hS.card_pos
  have hT1 := hT.card_pos
  have hU : 2 ≤ (S ∪ T).card := by omega
  have hTS : ∀ i ∈ T, i ∉ S := fun i hi hiS => Finset.disjoint_left.1 hST hiS hi
  simp only [votingGame, hU, ↓reduceIte] at hw hw' ⊢
  by_cases h2S : 2 ≤ S.card
  · have h1T : ¬ 2 ≤ T.card := by omega
    simp only [h2S, h1T, ↓reduceIte] at hw hw'
    obtain ⟨a, ha⟩ := hw
    refine ⟨a, fun i hi => ?_⟩
    rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using ha i h
    · simpa [hTS i h] using (hw' i h).trans (hu a i)
  · simp only [h2S, ↓reduceIte] at hw
    by_cases h2T : 2 ≤ T.card
    · simp only [h2T, ↓reduceIte] at hw'
      obtain ⟨a, ha⟩ := hw'
      refine ⟨a, fun i hi => ?_⟩
      rcases Finset.mem_union.1 hi with h | h
      · simpa [h] using (hw i h).trans (hu a i)
      · simpa [hTS i h] using ha i h
    · simp only [h2T, ↓reduceIte] at hw'
      refine ⟨Classical.arbitrary A, fun i hi => ?_⟩
      rcases Finset.mem_union.1 hi with h | h
      · simpa [h] using (hw i h).trans (hu _ i)
      · simpa [hTS i h] using (hw' i h).trans (hu _ i)

/-- **Figure 18.AA.4** (MWG, pp. 675-676). The payoffs of the three alternatives:
`u(a₁) = (2, 1, 0)`, `u(a₂) = (1, 0, 2)`, `u(a₃) = (0, 2, 1)`. -/
def votingPayoffs : Fin 3 → Fin 3 → ℝ := ![![2, 1, 0], ![1, 0, 2], ![0, 2, 1]]

/-- **Example 18.AA.2** (MWG, p. 676). With the values of Figure 18.AA.4, `V(I)` is not convex:
the midpoint of `u(a₁)` and `u(a₃)` is not dominated by any `u(a)`. -/
theorem example_18_AA_2_not_convex : ¬ Convex ℝ (votingGame votingPayoffs Finset.univ) := by
  intro hc
  have h1 : votingPayoffs 0 ∈ votingGame votingPayoffs Finset.univ := by
    simp only [votingGame, Finset.card_univ, Fintype.card_fin]
    exact ⟨0, fun _ _ => le_rfl⟩
  have h3 : votingPayoffs 2 ∈ votingGame votingPayoffs Finset.univ := by
    simp only [votingGame, Finset.card_univ, Fintype.card_fin]
    exact ⟨2, fun _ _ => le_rfl⟩
  have hm := hc h1 h3 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [votingGame, Finset.card_univ, Fintype.card_fin] at hm
  obtain ⟨a, ha⟩ := hm
  have e0 := ha 0 (Finset.mem_univ _)
  have e1 := ha 1 (Finset.mem_univ _)
  have e2 := ha 2 (Finset.mem_univ _)
  fin_cases a <;> simp [votingPayoffs] at e0 e1 e2 <;> linarith

/-! ### Transferable utility games -/

/-- **Definition 18.AA.4** (MWG, p. 676). The utility possibility set of a TU game with
characteristic function `v` (Chapter 22's `Game`): `V(S) = {u^S : ∑_{i∈S} uᵢ ≤ v(S)}`. -/
def tuSet (v : WelfareBargaining.Game n) : NTUGame n := fun S => {w | ∑ i ∈ S, w i ≤ v S}

/-- **Definition 18.AA.4** (MWG, p. 676). The sets of a TU game are utility possibility sets: the
TU game is a game in characteristic form. -/
theorem tuSet_isCharacteristicForm (v : WelfareBargaining.Game n) :
    IsCharacteristicForm (tuSet v) := by
  intro S hS
  refine ⟨⟨fun _ => v S / S.card, ?_⟩, ?_, ?_⟩
  · have : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
    simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ this]
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  · intro w hw w' hle
    exact (Finset.sum_le_sum hle).trans hw

/-- **Definitions 18.AA.3-18.AA.4** (MWG, p. 676). A TU game is superadditive in the sense of
Definition 18.AA.3 iff `v(S) + v(T) ≤ v(S ∪ T)` for disjoint coalitions `S, T`. -/
theorem tuSet_superadditive_iff (v : WelfareBargaining.Game n) :
    IsSuperadditive (tuSet v) ↔ ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty →
      Disjoint S T → v S + v T ≤ v (S ∪ T) := by
  classical
  have hTS : ∀ {S T : Finset (Fin n)}, Disjoint S T → ∀ i ∈ T, i ∉ S :=
    fun hST i hi hiS => Finset.disjoint_left.1 hST hiS hi
  have hsplit : ∀ {S T : Finset (Fin n)}, Disjoint S T → ∀ u u' : Fin n → ℝ,
      ∑ i ∈ S ∪ T, (if i ∈ S then u i else u' i) = ∑ i ∈ S, u i + ∑ i ∈ T, u' i := by
    intro S T hST u u'
    rw [Finset.sum_union hST]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by simp [hi]
    · exact Finset.sum_congr rfl fun i hi => by simp [hTS hST i hi]
  constructor
  · intro h S T hS hT hST
    have hcS : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
    have hcT : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
    have hu : (fun _ => v S / S.card) ∈ tuSet v S := by
      simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hcS]
    have hu' : (fun _ => v T / T.card) ∈ tuSet v T := by
      simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hcT]
    have := h S T hS hT hST _ _ hu hu'
    simp only [tuSet, Set.mem_ofPred_eq] at this
    rw [hsplit hST] at this
    simp only [Finset.sum_const, nsmul_eq_mul] at this
    rwa [mul_div_cancel₀ _ hcS, mul_div_cancel₀ _ hcT] at this
  · intro h S T hS hT hST u u' hu hu'
    simp only [tuSet, Set.mem_ofPred_eq] at hu hu' ⊢
    rw [hsplit hST]
    linarith [h S T hS hT hST]

/-- **Example 18.AA.3** (MWG, p. 677). TU majority voting: `v(I) = 3`, `v(S) = 3` for pairs and
`v({i}) = 0`. -/
def tuMajority : WelfareBargaining.Game 3 := fun S => if 2 ≤ S.card then 3 else 0

/-- **Example 18.AA.3** (MWG, pp. 676-677). With the values of Figure 18.AA.4 and freely
transferable utility, the worth of every coalition with at least two members is the maximal
total utility `max_a ∑_{i∈S} uᵢ(a)` it can obtain, and `v({i}) = 0`. -/
theorem example_18_AA_3 :
    (∀ S : Finset (Fin 3), 2 ≤ S.card →
      IsGreatest (Set.range fun a => ∑ i ∈ S, votingPayoffs a i) (tuMajority S)) ∧
    ∀ i : Fin 3, tuMajority {i} = 0 := by
  refine ⟨fun S hS => ?_, fun i => by simp [tuMajority]⟩
  have hcases : S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = Finset.univ := by
    revert S; decide
  have hv : tuMajority S = 3 := by simp [tuMajority, hS]
  rw [hv]
  rcases hcases with rfl | rfl | rfl | rfl
  · refine ⟨⟨0, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨1, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨2, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨0, by simp [votingPayoffs, Fin.sum_univ_three]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs, Fin.sum_univ_three] <;> norm_num

/-! ### Blocking and the core -/

/-- **Definition 18.AA.5** (MWG, p. 678). The outcome `u` is blocked (improved upon) by the
coalition `S` if some `u' ∈ V(S)` has `uᵢ < u'ᵢ` for all `i ∈ S`. -/
def ntuBlocks (V : NTUGame n) (S : Finset (Fin n)) (u : Fin n → ℝ) : Prop :=
  S.Nonempty ∧ ∃ u' ∈ V S, ∀ i ∈ S, u i < u' i

/-- **Definition 18.AA.6** (MWG, p. 678). The core: the outcomes feasible for the grand
coalition (`u ∈ V(I)`) that no coalition blocks. -/
def ntuCore (V : NTUGame n) : Set (Fin n → ℝ) :=
  {u | u ∈ V Finset.univ ∧ ∀ S, ¬ ntuBlocks V S u}

/-- **Appendix A** (MWG, p. 678). The core of a TU game:
`∑_{i∈S} uᵢ ≥ v(S)` for every coalition `S` and `∑_{i∈I} uᵢ ≤ v(I)`. -/
def tuCore (v : WelfareBargaining.Game n) : Set (Fin n → ℝ) :=
  {u | (∀ S : Finset (Fin n), S.Nonempty → v S ≤ ∑ i ∈ S, u i) ∧ ∑ i, u i ≤ v Finset.univ}

/-- **Definition 18.AA.5** (MWG, p. 678), TU case: `u` is blocked by `S` iff
`∑_{i∈S} uᵢ < v(S)`. -/
theorem tu_blocks_iff (v : WelfareBargaining.Game n) (S : Finset (Fin n)) (u : Fin n → ℝ) :
    ntuBlocks (tuSet v) S u ↔ S.Nonempty ∧ ∑ i ∈ S, u i < v S := by
  constructor
  · rintro ⟨hS, u', hu', hlt⟩
    exact ⟨hS, (Finset.sum_lt_sum_of_nonempty hS hlt).trans_le hu'⟩
  · rintro ⟨hS, hlt⟩
    have hc : (0 : ℝ) < S.card := Nat.cast_pos.2 hS.card_pos
    set δ := (v S - ∑ i ∈ S, u i) / S.card with hδ
    have hδpos : 0 < δ := div_pos (by linarith) hc
    refine ⟨hS, fun i => u i + δ, ?_, fun i _ => by linarith⟩
    simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, hδ]
    rw [mul_div_cancel₀ _ hc.ne']
    linarith

/-- **Definition 18.AA.6** (MWG, p. 678), TU case: the core of the TU game is the set of
`u` with `∑_{i∈S} uᵢ ≥ v(S)` for all `S` and `∑_{i∈I} uᵢ ≤ v(I)`. -/
theorem ntuCore_tuSet (v : WelfareBargaining.Game n) : ntuCore (tuSet v) = tuCore v := by
  ext u
  simp only [ntuCore, tuCore, Set.mem_ofPred_eq, tu_blocks_iff, tuSet, not_and, not_lt]
  exact ⟨fun h => ⟨fun S hS => h.2 S hS, h.1⟩, fun h => ⟨h.2, fun S hS => h.1 S hS⟩⟩

/-- **Exercise 18.AA.2** (MWG, p. 678). A TU game with a nonempty core satisfies
`v(S) + v(T) ≤ v(I)` for every partition of `I` into two coalitions `S, T`. -/
theorem exercise_18_AA_2 {v : WelfareBargaining.Game n} (hcore : (tuCore v).Nonempty)
    {S T : Finset (Fin n)} (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T)
    (hU : S ∪ T = Finset.univ) : v S + v T ≤ v Finset.univ := by
  obtain ⟨u, hu, htot⟩ := hcore
  have h := Finset.sum_union hST (f := u)
  rw [hU] at h
  linarith [hu S hS, hu T hT]

/-- **Example 18.AA.4** (MWG, p. 678). The TU majority voting game has an empty core: if
`u₁ + u₂ + u₃ ≤ 3` then some pair gets less than `3`. -/
theorem example_18_AA_4_tu : tuCore tuMajority = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hS, htot⟩
  have h01 := hS {0, 1} (by simp)
  have h02 := hS {0, 2} (by simp)
  have h12 := hS {1, 2} (by simp)
  simp [tuMajority, Fin.sum_univ_three] at h01 h02 h12 htot
  linarith

/-- **Example 18.AA.4** (MWG, p. 678). The majority voting game of Figure 18.AA.4 has an empty
core: `(2, 1, 0)`, `(1, 0, 2)`, `(0, 2, 1)` (and everything below them) are blocked by `{2, 3}`
using `a₃`, `{1, 2}` using `a₁` and `{1, 3}` using `a₂` (the Condorcet paradox). -/
theorem example_18_AA_4_ntu : ntuCore (votingGame votingPayoffs) = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hu, hnb⟩
  simp only [votingGame, Finset.card_univ, Fintype.card_fin] at hu
  obtain ⟨a, ha⟩ := hu
  have e0 := ha 0 (Finset.mem_univ _)
  have e1 := ha 1 (Finset.mem_univ _)
  have e2 := ha 2 (Finset.mem_univ _)
  fin_cases a
  · apply hnb {1, 2}
    refine ⟨by simp, votingPayoffs 2, ?_, ?_⟩
    · have hc : 2 ≤ ({1, 2} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨2, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith
  · apply hnb {0, 1}
    refine ⟨by simp, votingPayoffs 0, ?_, ?_⟩
    · have hc : 2 ≤ ({0, 1} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨0, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith
  · apply hnb {0, 2}
    refine ⟨by simp, votingPayoffs 1, ?_, ?_⟩
    · have hc : 2 ≤ ({0, 2} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨1, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith

/-! ### Example 18.AA.5: economies again -/

/-- **Example 18.AA.5** (MWG, pp. 678-679). For an economy of Section 18.B whose preferences are
represented by utilities `Uᵢ`, a feasible allocation `x` has the core property iff its utility
vector `(Uᵢ(xᵢ))ᵢ` is in the core of the game of Example 18.AA.1: the two notions of the core
coincide. -/
theorem example_18_AA_5 (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) (x : Fin n → Fin L → ℝ) :
    x ∈ E.core ↔ E.IsFeasible x ∧ (fun i => U i (x i)) ∈ ntuCore (econGame U E.ω E.Y) := by
  constructor
  · rintro ⟨hfeas, hnb⟩
    obtain ⟨hx0, y, hy, hsum⟩ := hfeas
    refine ⟨⟨hx0, y, hy, hsum⟩, ⟨x, fun i _ => hx0 i, ⟨y, hy, by rw [hsum, add_comm]⟩,
      fun _ _ => le_rfl⟩, ?_⟩
    rintro S ⟨hS, w, ⟨x', hx', ⟨y', hy', hs'⟩, hu'⟩, hlt⟩
    refine hnb S ⟨hS, x', fun i hi => ⟨hx' i hi, ?_⟩, y', hy', by rw [hs', add_comm]⟩
    rw [hpref i]
    have h := (hlt i hi).trans_le (hu' i hi)
    exact ⟨h.le, not_le.2 h⟩
  · rintro ⟨hfeas, _, hnb⟩
    refine ⟨hfeas, fun S ⟨hS, x', hx', y', hy', hs'⟩ => hnb S ⟨hS, fun i => U i (x' i),
      ⟨x', fun i hi => (hx' i hi).1, ⟨y', hy', by rw [hs', add_comm]⟩, fun _ _ => le_rfl⟩,
      fun i hi => ?_⟩⟩
    have h := (hx' i hi).2
    rw [hpref i] at h
    exact not_le.1 h.2

/-- **Example 18.AA.5** (MWG, p. 678). Conversely, every core outcome of the game of the economy
is dominated by the utility vector of an allocation with the core property. -/
theorem example_18_AA_5_game_core (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) {w : Fin n → ℝ}
    (hw : w ∈ ntuCore (econGame U E.ω E.Y)) : ∃ x ∈ E.core, ∀ i, w i ≤ U i (x i) := by
  obtain ⟨⟨x, hx0, ⟨y, hy, hsum⟩, hux⟩, hnb⟩ := hw
  refine ⟨x, ?_, fun i => hux i (Finset.mem_univ i)⟩
  refine ⟨⟨fun i => hx0 i (Finset.mem_univ i), y, hy, by rw [hsum, add_comm]⟩, ?_⟩
  rintro S ⟨hS, x', hx', y', hy', hs'⟩
  refine hnb S ⟨hS, fun i => U i (x' i), ⟨x', fun i hi => (hx' i hi).1,
    ⟨y', hy', by rw [hs', add_comm]⟩, fun _ _ => le_rfl⟩, fun i hi => ?_⟩
  have h := (hx' i hi).2
  rw [hpref i] at h
  exact (hux i (Finset.mem_univ i)).trans_lt (not_le.1 h.2)

/-- **Example 18.AA.5** (MWG, p. 679). If a Walrasian equilibrium exists then the core of the
game of the economy is nonempty (Proposition 18.B.1, for a convex constant returns
technology). -/
theorem example_18_AA_5_walras (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) (hY : IsCRSTechnology E.Y)
    {x : Fin n → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    (ntuCore (econGame U E.ω E.Y)).Nonempty :=
  ⟨_, ((example_18_AA_5 E U hpref x).1 (proposition_18_B_1 E hY h)).2⟩

/-! ### Example 18.AA.6: single-input production games -/

/-- **Example 18.AA.6** (MWG, p. 679). The TU game of a one-input technology `f`:
`v(S) = f(∑_{i∈S} ωᵢ)`. -/
def prodGame (f : ℝ → ℝ) (ω : Fin n → ℝ) : WelfareBargaining.Game n :=
  fun S => f (∑ i ∈ S, ω i)

/-- **Example 18.AA.6** (MWG, p. 679). The proportional distribution of output:
`u_h = ω_h / (∑_{i∈I} ωᵢ) · f(∑_{i∈I} ωᵢ)`. -/
noncomputable def propAlloc (f : ℝ → ℝ) (ω : Fin n → ℝ) : Fin n → ℝ :=
  fun h => ω h / (∑ i, ω i) * f (∑ i, ω i)

/-- **Example 18.AA.6** (MWG, p. 679). `∑_{h∈S} u_h = (∑_{h∈S} ω_h)/(∑_{i∈I} ωᵢ) · f(∑_{i∈I} ωᵢ)`.
-/
theorem propAlloc_sum (f : ℝ → ℝ) (ω : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ h ∈ S, propAlloc f ω h = (∑ h ∈ S, ω h) / (∑ i, ω i) * f (∑ i, ω i) := by
  simp only [propAlloc, ← Finset.sum_mul, ← Finset.sum_div]

/-- **Example 18.AA.6** (MWG, p. 679). If `f(0) = 0` and the average product `f(z)/z` is
nondecreasing on `z > 0`, the proportional allocation is in the core (`ωᵢ ≥ 0`). -/
theorem example_18_AA_6 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hf0 : f 0 = 0) (hω : ∀ i, 0 ≤ ω i)
    (hmono : MonotoneOn (fun z => f z / z) (Set.Ioi 0)) :
    propAlloc f ω ∈ tuCore (prodGame f ω) := by
  have hZ : 0 ≤ ∑ i, ω i := Finset.sum_nonneg fun i _ => hω i
  refine ⟨fun S _ => ?_, ?_⟩
  · rw [propAlloc_sum]
    simp only [prodGame]
    have hzS : 0 ≤ ∑ i ∈ S, ω i := Finset.sum_nonneg fun i _ => hω i
    have hle : ∑ i ∈ S, ω i ≤ ∑ i, ω i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hω i
    rcases eq_or_lt_of_le hzS with h | h
    · rw [← h, hf0]; simp
    · have hZpos : 0 < ∑ i, ω i := h.trans_le hle
      have hm := hmono h hZpos hle
      simp only at hm
      rw [div_le_div_iff₀ h hZpos] at hm
      rw [div_mul_eq_mul_div, le_div_iff₀ hZpos]
      linarith
  · rw [propAlloc_sum]
    simp only [prodGame]
    rcases eq_or_lt_of_le hZ with h | h
    · rw [← h, hf0]; simp
    · rw [div_self h.ne', one_mul]

/-- **Example 18.AA.6** (MWG, p. 679), bracketed claim: if `f` is convex on `ℝ₊` with
`f(0) = 0` then the average product `f(z)/z` is nondecreasing on `z > 0`. -/
theorem example_18_AA_6_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0) :
    MonotoneOn (fun z => f z / z) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hm := hf.slope_mono (x := 0) h0 (by simpa using ha') (by simpa using hb') hab
  simpa [slope_def_field, hf0] using hm

/-- **Exercise 18.AA.3** (MWG, p. 685). If the average product is constant (`f(z)/z = c` for
`z > 0`, `f(0) = 0`) then the proportional allocation is the only allocation in the core. -/
theorem exercise_18_AA_3 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hf0 : f 0 = 0) (hω : ∀ i, 0 ≤ ω i)
    {c : ℝ} (hc : ∀ z, 0 < z → f z / z = c) : tuCore (prodGame f ω) = {propAlloc f ω} := by
  have hlin : ∀ z, 0 ≤ z → f z = c * z := by
    intro z hz
    rcases eq_or_lt_of_le hz with h | h
    · rw [← h, hf0, mul_zero]
    · have := hc z h; field_simp at this; linarith
  have hZ : 0 ≤ ∑ i, ω i := Finset.sum_nonneg fun i _ => hω i
  have hprop : ∀ h, propAlloc f ω h = c * ω h := by
    intro h
    simp only [propAlloc]
    rcases eq_or_lt_of_le hZ with hz | hz
    · have h0 : ω h = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hω i).1 hz.symm h
        (Finset.mem_univ h)
      rw [h0]; simp
    · rw [hlin _ hZ]; field_simp
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hS, htot⟩
    have hi : ∀ h, c * ω h ≤ u h := by
      intro h
      have := hS {h} (Finset.singleton_nonempty h)
      simpa [prodGame, hlin _ (hω h)] using this
    have htot' : ∑ h, (u h - c * ω h) ≤ 0 := by
      simp only [prodGame, hlin _ hZ] at htot
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => sub_nonneg.2 (hi h)).1
      (le_antisymm htot' (Finset.sum_nonneg fun h _ => sub_nonneg.2 (hi h)))
    funext h
    rw [hprop h]
    linarith [hzero h (Finset.mem_univ h)]
  · rintro rfl
    refine example_18_AA_6 hf0 hω fun a ha b hb _ => ?_
    simp only
    rw [hc a ha, hc b hb]

/-- **Footnote 28** (MWG, p. 679). With strictly decreasing returns (`f(z)/z` strictly decreasing
on `z > 0`) and positive endowments, `v(S) + v(T) > v(I)` for every partition of `I` into two
coalitions `S, T`. -/
theorem footnote_18_28 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hω : ∀ i, 0 < ω i)
    (hanti : StrictAntiOn (fun z => f z / z) (Set.Ioi 0)) {S T : Finset (Fin n)}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T) (hU : S ∪ T = Finset.univ) :
    prodGame f ω Finset.univ < prodGame f ω S + prodGame f ω T := by
  simp only [prodGame]
  have hzS : 0 < ∑ i ∈ S, ω i := Finset.sum_pos (fun i _ => hω i) hS
  have hzT : 0 < ∑ i ∈ T, ω i := Finset.sum_pos (fun i _ => hω i) hT
  have hZ : ∑ i, ω i = ∑ i ∈ S, ω i + ∑ i ∈ T, ω i := by
    rw [← Finset.sum_union hST, hU]
  have hZpos : 0 < ∑ i, ω i := by rw [hZ]; linarith
  have h1 := hanti (show (0 : ℝ) < ∑ i ∈ S, ω i from hzS) (show (0 : ℝ) < ∑ i, ω i from hZpos)
    (by rw [hZ]; linarith)
  have h2 := hanti (show (0 : ℝ) < ∑ i ∈ T, ω i from hzT) (show (0 : ℝ) < ∑ i, ω i from hZpos)
    (by rw [hZ]; linarith)
  simp only at h1 h2
  rw [div_lt_div_iff₀ hZpos hzS] at h1
  rw [div_lt_div_iff₀ hZpos hzT] at h2
  have key : f (∑ i, ω i) * (∑ i, ω i) <
      (f (∑ i ∈ S, ω i) + f (∑ i ∈ T, ω i)) * (∑ i, ω i) := by
    have e : f (∑ i, ω i) * (∑ i, ω i) =
        f (∑ i, ω i) * (∑ i ∈ S, ω i) + f (∑ i, ω i) * (∑ i ∈ T, ω i) := by rw [hZ]; ring
    rw [e]; nlinarith
  exact lt_of_mul_lt_mul_right key hZpos.le

/-- **Footnote 28** (MWG, p. 679). Hence, with at least two players, the core is empty
(Exercise 18.AA.2). -/
theorem footnote_18_28_core_empty {f : ℝ → ℝ} {ω : Fin n → ℝ} (hn : 2 ≤ n)
    (hω : ∀ i, 0 < ω i) (hanti : StrictAntiOn (fun z => f z / z) (Set.Ioi 0)) :
    tuCore (prodGame f ω) = ∅ := by
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  have hab : b ≠ a := by simp [a, b, Fin.ext_iff]
  have hT : (Finset.univ.erase a).Nonempty := ⟨b, Finset.mem_erase.2 ⟨hab, Finset.mem_univ b⟩⟩
  have hST : Disjoint {a} (Finset.univ.erase a) := by simp
  have hU : {a} ∪ Finset.univ.erase a = Finset.univ := by
    rw [Finset.singleton_union, Finset.insert_erase (Finset.mem_univ a)]
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  have h1 := exercise_18_AA_2 ⟨u, hu⟩ (Finset.singleton_nonempty a) hT hST hU
  have h2 := footnote_18_28 hω hanti (Finset.singleton_nonempty a) hT hST hU
  linarith

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Balanced games and the Bondareva-Shapley theorem (MWG Exercise 18.AA.1, p. 685)

* Generalized partitions `S₁, ..., S_N` with weights `δₙ ∈ [0, 1]` and
  `∑_{n : i ∈ Sₙ} δₙ = 1` for every player (indexed by `Fin N`, as in the book):
  `IsGeneralizedPartition`, with the examples asked for (`exercise_18_AA_1_singletons`: an
  ordinary partition with unit weights; `exercise_18_AA_1_pairs`: the three pairs of a
  three-player game with weights `1/2`).
* Balanced TU games (`IsBalanced`), and the theorem: the core is nonempty iff the game is balanced
  (`exercise_18_AA_1`). The hard direction is proved with Chapter 5's Farkas lemma
  (`MWG.Production.farkas`, the theorem of the alternative behind the duality theorem of
  Section M.M): a homogenised system in `ℝ^{I+1}` whose alternative is a balanced family violating
  balancedness.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-- **Exercise 18.AA.1** (MWG, p. 685). `S₁, ..., S_N` (coalitions) form a generalized partition
with weights `δₙ ∈ [0, 1]`: `∑_{n : i ∈ Sₙ} δₙ = 1` for every player `i`. -/
def IsGeneralizedPartition {N : ℕ} (S : Fin N → Finset (Fin n)) (δ : Fin N → ℝ) : Prop :=
  (∀ k, (S k).Nonempty) ∧ (∀ k, 0 ≤ δ k ∧ δ k ≤ 1) ∧
    ∀ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ S k), δ k = 1

/-- **Exercise 18.AA.1** (MWG, p. 685). The TU game `v` is balanced: `∑ₙ δₙ v(Sₙ) ≤ v(I)` for every
generalized partition. -/
def IsBalanced (v : WelfareBargaining.Game n) : Prop :=
  ∀ (N : ℕ) (S : Fin N → Finset (Fin n)) (δ : Fin N → ℝ), IsGeneralizedPartition S δ →
    ∑ k, δ k * v (S k) ≤ v Finset.univ

/-- **Exercise 18.AA.1** (MWG, p. 685), example: an ordinary partition (here into singletons)
with unit weights is a generalized partition. -/
theorem exercise_18_AA_1_singletons :
    IsGeneralizedPartition (n := n) (N := n) (fun k => {k}) (fun _ => 1) := by
  refine ⟨fun k => Finset.singleton_nonempty k, fun _ => ⟨zero_le_one, le_rfl⟩, fun i => ?_⟩
  have : Finset.univ.filter (fun k : Fin n => i ∈ ({k} : Finset (Fin n))) = {i} := by
    ext k; simp [eq_comm]
  rw [this]; simp

/-- **Exercise 18.AA.1** (MWG, p. 685), example: with three players, the three pairs
`{1, 2}, {1, 3}, {2, 3}` with weights `1/2` form a generalized partition. -/
theorem exercise_18_AA_1_pairs :
    IsGeneralizedPartition (n := 3) (N := 3) ![{0, 1}, {0, 2}, {1, 2}] (fun _ => 1 / 2) := by
  refine ⟨fun k => ?_, fun _ => ⟨by norm_num, by norm_num⟩, fun i => ?_⟩
  · fin_cases k <;> simp
  · rw [Finset.sum_filter]
    fin_cases i <;> simp [Fin.sum_univ_three] <;> norm_num

/-- **Exercise 18.AA.1** (MWG, p. 685), easy direction: a TU game with a nonempty core is
balanced. -/
theorem isBalanced_of_core {v : WelfareBargaining.Game n} (h : (tuCore v).Nonempty) :
    IsBalanced v := by
  obtain ⟨u, hS, htot⟩ := h
  intro N S δ ⟨hne, hδ, hsum⟩
  have hswap : ∀ k, δ k * ∑ i ∈ S k, u i = ∑ i, if i ∈ S k then δ k * u i else 0 := by
    intro k
    rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_univ_mem]
  calc ∑ k, δ k * v (S k) ≤ ∑ k, δ k * ∑ i ∈ S k, u i :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hS _ (hne k)) (hδ k).1
    _ = ∑ i, u i * ∑ k ∈ Finset.univ.filter (fun k => i ∈ S k), δ k := by
        simp only [hswap]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
    _ = ∑ i, u i := by simp [hsum]
    _ ≤ v Finset.univ := htot

/-- **Exercise 18.AA.1** (MWG, p. 685). The generators of the cone used in the proof of the
Bondareva-Shapley theorem, in `ℝ^{I+1}`: `(1, ..., 1, -v(I))` and, for every coalition `S`,
`(-𝟙_S, v(S))`. -/
noncomputable def bsGen (v : WelfareBargaining.Game n) :
    Option {S : Finset (Fin n) // S.Nonempty} → Fin (n + 1) → ℝ := fun o => by
  classical
  exact match o with
  | none => Fin.snoc (α := fun _ => ℝ) (fun _ => 1) (-(v Finset.univ))
  | some S => Fin.snoc (α := fun _ => ℝ) (fun i => -(if i ∈ S.1 then 1 else 0)) (v S.1)

/-- **Exercise 18.AA.1** (MWG, p. 685). Dot products with vectors of `ℝ^{I+1}` written as `(p, x)`.
-/
theorem dotProduct_snoc (y : Fin (n + 1) → ℝ) (p : Fin n → ℝ) (x : ℝ) :
    y ⬝ᵥ (Fin.snoc (α := fun _ => ℝ) p x) =
      ∑ i : Fin n, y i.castSucc * p i + y (Fin.last n) * x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- **Exercise 18.AA.1** (MWG, p. 685). The first `I` coordinates of `(p, x)`. -/
theorem snoc_apply_castSucc (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    (Fin.snoc (α := fun _ => ℝ) p x : Fin (n + 1) → ℝ) i.castSucc = p i := by simp

/-- **Exercise 18.AA.1** (MWG, p. 685). The last coordinate of `(p, x)`. -/
theorem snoc_apply_last (p : Fin n → ℝ) (x : ℝ) :
    (Fin.snoc (α := fun _ => ℝ) p x : Fin (n + 1) → ℝ) (Fin.last n) = x := by simp

/-- **Exercise 18.AA.1** (MWG, p. 685), hard direction (Bondareva-Shapley): a balanced TU game
has a nonempty core. Proof by Farkas' lemma (LP duality, Section M.M). -/
theorem core_nonempty_of_isBalanced {v : WelfareBargaining.Game n} (hb : IsBalanced v) :
    (tuCore v).Nonempty := by
  classical
  set b : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) (fun _ => 0) 1 with hbdef
  have hnot : ¬ ∃ lam : Option {S : Finset (Fin n) // S.Nonempty} → ℝ, 0 ≤ lam ∧
      b = ∑ o, lam o • bsGen v o := by
    rintro ⟨lam, hlam, hbeq⟩
    set μ := lam none with hμ
    -- coordinate equations
    have hcoord : ∀ i : Fin n,
        ∑ S : {S : Finset (Fin n) // S.Nonempty}, (if i ∈ S.1 then lam (some S) else 0) = μ := by
      intro i
      have h := congrFun hbeq i.castSucc
      simp only [hbdef, snoc_apply_castSucc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_option, bsGen] at h
      have e : ∀ S : {S : Finset (Fin n) // S.Nonempty},
          lam (some S) * -(if i ∈ S.1 then (1 : ℝ) else 0) =
            -(if i ∈ S.1 then lam (some S) else 0) := fun S => by split_ifs <;> ring
      simp only [e, Finset.sum_neg_distrib, mul_one] at h
      linarith
    have hlast : ∑ S : {S : Finset (Fin n) // S.Nonempty}, lam (some S) * v S.1 =
        1 + μ * v Finset.univ := by
      have h := congrFun hbeq (Fin.last n)
      simp only [hbdef, snoc_apply_last, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_option, bsGen] at h
      linarith
    have hlam0 : ∀ o, 0 ≤ lam o := fun o => hlam o
    rcases eq_or_lt_of_le (hlam0 none) with hμ0 | hμpos
    · -- μ = 0: all weights vanish
      have hμz : μ = 0 := by rw [hμ]; exact hμ0.symm
      have hz : ∀ S : {S : Finset (Fin n) // S.Nonempty}, lam (some S) = 0 := by
        intro S
        obtain ⟨i, hi⟩ := S.2
        have h := hcoord i
        rw [hμz] at h
        have := (Finset.sum_eq_zero_iff_of_nonneg fun S' _ => by
          split_ifs
          · exact hlam0 _
          · exact le_rfl).1 h S (Finset.mem_univ S)
        simpa [hi] using this
      simp only [hz, zero_mul, Finset.sum_const_zero] at hlast
      rw [hμz] at hlast
      linarith
    · -- μ > 0: a balanced family violating balancedness
      have hμ' : 0 < μ := hμpos
      set e := Fintype.equivFin {S : Finset (Fin n) // S.Nonempty}
      set N := Fintype.card {S : Finset (Fin n) // S.Nonempty}
      set Sk : Fin N → Finset (Fin n) := fun k => (e.symm k).1
      set δ : Fin N → ℝ := fun k => lam (some (e.symm k)) / μ
      have hsumδ : ∀ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ Sk k), δ k = 1 := by
        intro i
        rw [Finset.sum_filter]
        have := Equiv.sum_comp e.symm
          (fun S : {S : Finset (Fin n) // S.Nonempty} => if i ∈ S.1 then lam (some S) / μ else 0)
        simp only [Sk, δ]
        rw [this]
        have e2 : ∀ S : {S : Finset (Fin n) // S.Nonempty},
            (if i ∈ S.1 then lam (some S) / μ else 0) = (if i ∈ S.1 then lam (some S) else 0) / μ :=
          fun S => by split_ifs <;> simp
        simp only [e2, ← Finset.sum_div, hcoord i]
        exact div_self hμ'.ne'
      have hδnn : ∀ k, 0 ≤ δ k := fun k => div_nonneg (hlam0 _) hμ'.le
      have hpart : IsGeneralizedPartition Sk δ := by
        refine ⟨fun k => (e.symm k).2, fun k => ⟨hδnn k, ?_⟩, hsumδ⟩
        obtain ⟨i, hi⟩ := (e.symm k).2
        rw [← hsumδ i]
        exact Finset.single_le_sum (fun k' _ => hδnn k')
          (Finset.mem_filter.2 ⟨Finset.mem_univ k, hi⟩)
      have hval := hb N Sk δ hpart
      have hrew : ∑ k, δ k * v (Sk k) = (1 + μ * v Finset.univ) / μ := by
        rw [← hlast, Finset.sum_div]
        have := Equiv.sum_comp e.symm
          (fun S : {S : Finset (Fin n) // S.Nonempty} => lam (some S) * v S.1 / μ)
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [δ, Sk]; ring
      rw [hrew, div_le_iff₀ hμ'] at hval
      linarith
  have hy := (not_not.1 (mt (MWG.Production.farkas (bsGen v) b).2 hnot))
  obtain ⟨y, hya, hyb⟩ := hy
  set t := y (Fin.last n) with ht
  have htpos : 0 < t := by
    rw [hbdef, dotProduct_snoc] at hyb
    simpa using hyb
  refine ⟨fun i => y i.castSucc / t, fun S hS => ?_, ?_⟩
  · have h := hya (some ⟨S, hS⟩)
    simp only [bsGen, dotProduct_snoc] at h
    have e : ∀ i : Fin n, y i.castSucc * -(if i ∈ S then (1 : ℝ) else 0) =
        -(if i ∈ S then y i.castSucc else 0) := fun i => by split_ifs <;> ring
    simp only [e, Finset.sum_neg_distrib, ← Finset.sum_filter, Finset.filter_univ_mem] at h
    rw [← Finset.sum_div, le_div_iff₀ htpos]
    linarith
  · have h := hya none
    simp only [bsGen, dotProduct_snoc, mul_one] at h
    rw [← Finset.sum_div, div_le_iff₀ htpos]
    linarith

/-- **Exercise 18.AA.1** (MWG, p. 685), the Bondareva-Shapley theorem: a TU game has a nonempty
core if and only if it is balanced. -/
theorem exercise_18_AA_1 (v : WelfareBargaining.Game n) :
    (tuCore v).Nonempty ↔ IsBalanced v :=
  ⟨isBalanced_of_core, core_nonempty_of_isBalanced⟩

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Shapley value (MWG Appendix A, pp. 679-682; Exercises 18.AA.4-18.AA.6)

TU games are Chapter 22's `Game n = Finset (Fin n) → ℝ` (with `v(∅) = 0`), and the Shapley value
(18.AA.3), the average marginal contribution over orderings, is Chapter 22's `shapley`. Here:

* (18.AA.1) for every two-player subgame (`egalitarian_pair`), and the two-player game
  (`formula_18_AA_1`);
* subgames `(S, v)` and the preservation-of-differences system (18.AA.2)
  (`IsEgalitarianSolution`): it has at most one solution (`egalitarian_unique`, strong induction
  on `|S|`, as in the book), with the displayed recursion for `Sh₁(I, v)`
  (`egalitarian_recursion`); a solution is `Shᵢ(S, v) = ∑_{T ⊆ S, i ∈ T} d_T(v)/|T|` with
  Chapter 22's Harsanyi dividends (`shapleyFamily`, `shapleyFamily_isEgalitarian`), so
  **Definition 18.AA.7** is well posed (`definition_18_AA_7`);
* (18.AA.3): the value of Definition 18.AA.7 is Chapter 22's `shapley` (`formula_18_AA_3`), also
  for every subgame (`shapley_subgame`); footnote 31 and the claim `∑ᵢ m(S(π, i), i) = v(I)`;
* (18.AA.4) (footnote 32): the subset formula equals the solution of (18.AA.2) on every subgame
  (`subsetFormula_eq_shapleyFamily`, via the identity
  `∑_{U ⊆ T ⊆ S} (|S|-|T|)!(|T|-1)!/|S|! = 1/|U|`), hence (18.AA.4) = (18.AA.3)
  (`formula_18_AA_4`); **Exercise 18.AA.4** (`exercise_18_AA_4`);
* properties (a)-(d) with footnote 33 (`shapley_symmetry_footnote_33`) and the characterization
  (`shapley_characterization`); **Exercises 18.AA.5-18.AA.6**.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-! ### Preservation of differences: (18.AA.1)-(18.AA.2), Definition 18.AA.7 -/

/-- **Appendix A** (MWG, p. 680). The subgame `(S, v)`: the restriction of `v` to the subsets of
`S` (represented as the game `T ↦ v(T ∩ S)` on all players, in which players outside `S` are
dummies). -/
def subgame (v : WelfareBargaining.Game n) (S : Finset (Fin n)) : WelfareBargaining.Game n :=
  fun T => v (T ∩ S)

/-- **Appendix A** (MWG, p. 681), (18.AA.2). A family `{Shᵢ(S, v)}_{S ⊆ I, i ∈ S}` is an
egalitarian solution: differences are preserved,
`Shᵢ(S, v) - Shᵢ(S \ {h}, v) = Sh_h(S, v) - Sh_h(S \ {i}, v)` for `i, h ∈ S`, and
`∑_{i∈S} Shᵢ(S, v) = v(S)` for every coalition `S`. -/
def IsEgalitarianSolution (v : WelfareBargaining.Game n)
    (φ : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S : Finset (Fin n), ∀ i ∈ S, ∀ h ∈ S,
      φ S i - φ (S.erase h) i = φ S h - φ (S.erase i) h) ∧
    ∀ S : Finset (Fin n), S.Nonempty → ∑ i ∈ S, φ S i = v S

/-- **Appendix A** (MWG, p. 681). (18.AA.2) only involves the values `Shᵢ(S, v)` with `i ∈ S`. -/
theorem isEgalitarianSolution_congr {v : WelfareBargaining.Game n}
    {φ ψ : Finset (Fin n) → Fin n → ℝ} (h : ∀ S, ∀ i ∈ S, φ S i = ψ S i)
    (hφ : IsEgalitarianSolution v φ) : IsEgalitarianSolution v ψ := by
  classical
  refine ⟨fun S i hi j hj => ?_, fun S hS => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · ring
    · have h1 := hφ.1 S i hi j hj
      rw [h S i hi, h S j hj, h (S.erase j) i (Finset.mem_erase.2 ⟨hij, hi⟩),
        h (S.erase i) j (Finset.mem_erase.2 ⟨hij.symm, hj⟩)] at h1
      exact h1
  · rw [← hφ.2 S hS]
    exact Finset.sum_congr rfl fun i hi => (h S i hi).symm

/-- **Appendix A** (MWG, p. 681). (18.AA.2) determines the numbers `Shᵢ(S, v)`, `i ∈ S`,
uniquely (induction on the size of `S`). -/
theorem egalitarian_unique {v : WelfareBargaining.Game n} {φ ψ : Finset (Fin n) → Fin n → ℝ}
    (hφ : IsEgalitarianSolution v φ) (hψ : IsEgalitarianSolution v ψ) :
    ∀ S : Finset (Fin n), ∀ i ∈ S, φ S i = ψ S i := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro i hi
    have hconst : ∀ j ∈ S, φ S j - ψ S j = φ S i - ψ S i := by
      intro j hj
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · have h1 := hφ.1 S i hi j hj
        have h2 := hψ.1 S i hi j hj
        have e1 := ih (S.erase j) (Finset.erase_ssubset hj) i (Finset.mem_erase.2 ⟨hij, hi⟩)
        have e2 := ih (S.erase i) (Finset.erase_ssubset hi) j
          (Finset.mem_erase.2 ⟨hij.symm, hj⟩)
        linarith
    have hsum : ∑ j ∈ S, (φ S j - ψ S j) = 0 := by
      rw [Finset.sum_sub_distrib, hφ.2 S ⟨i, hi⟩, hψ.2 S ⟨i, hi⟩, sub_self]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
    have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hi)
    have := (mul_eq_zero.1 hsum).resolve_left hc
    linarith

/-- **Appendix A** (MWG, p. 681). The recursion used in the uniqueness argument:
`Sh_j(S, v) = (1/|S|) [v(S) - ∑_{i ≠ j} Shᵢ(S \ {j}, v) + ∑_{i ≠ j} Sh_j(S \ {i}, v)]`
(the book's display for `j = 1`, `S = I`). -/
theorem egalitarian_recursion {v : WelfareBargaining.Game n}
    {φ : Finset (Fin n) → Fin n → ℝ} (hφ : IsEgalitarianSolution v φ)
    {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    φ S j = (1 / S.card) * (v S - ∑ i ∈ S.erase j, φ (S.erase j) i +
      ∑ i ∈ S.erase j, φ (S.erase i) j) := by
  classical
  have hi : ∀ i ∈ S.erase j, φ S i = φ S j + φ (S.erase j) i - φ (S.erase i) j := by
    intro i hi'
    have := hφ.1 S i (Finset.mem_of_mem_erase hi') j hj
    linarith
  have hsum := hφ.2 S ⟨j, hj⟩
  rw [← Finset.add_sum_erase S _ hj, Finset.sum_congr rfl hi, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul] at hsum
  have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
  have hcast : ((S.card - 1 : ℕ) : ℝ) = S.card - 1 := by
    rw [Nat.cast_sub (by exact_mod_cast hc)]; simp
  rw [hcast] at hsum
  field_simp
  linarith

/-- **Appendix A** (MWG, p. 680), (18.AA.1) for every two-player subgame `{a, b}`:
`Sh_a({a, b}, v) = v({a}) + (v({a, b}) - v({a}) - v({b}))/2`. -/
theorem egalitarian_pair {v : WelfareBargaining.Game n} {φ : Finset (Fin n) → Fin n → ℝ}
    (hφ : IsEgalitarianSolution v φ) {a b : Fin n} (hab : a ≠ b) :
    φ {a, b} a = v {a} + (v {a, b} - v {a} - v {b}) / 2 := by
  classical
  have h1 := hφ.1 {a, b} a (by simp) b (by simp)
  have ea : ({a, b} : Finset (Fin n)).erase b = {a} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩ <;> simp_all
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩
  have eb : ({a, b} : Finset (Fin n)).erase a = {b} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩ <;> simp_all
    · rintro rfl; exact ⟨fun h => hab h.symm, Or.inr rfl⟩
  rw [ea, eb] at h1
  have hsa := hφ.2 {a} (Finset.singleton_nonempty a)
  have hsb := hφ.2 {b} (Finset.singleton_nonempty b)
  have hsab := hφ.2 {a, b} (by simp)
  rw [Finset.sum_singleton] at hsa hsb
  rw [Finset.sum_pair hab] at hsab
  linarith

/-- **Appendix A** (MWG, p. 681). The family `Shᵢ(S, v) = ∑_{T ⊆ S, i ∈ T} d_T(v)/|T|` built from
Chapter 22's Harsanyi dividends `d_T(v)`. -/
noncomputable def shapleyFamily (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : ℝ := by
  classical
  exact ∑ T ∈ S.powerset, if i ∈ T then WelfareBargaining.dividend v T / T.card else 0

/-- **Appendix A** (MWG, p. 681). The subsets of `S` not containing `h` are the subsets of
`S \\ {h}`. -/
theorem powerset_filter_not_mem (S : Finset (Fin n)) (h : Fin n) :
    S.powerset.filter (fun T => h ∉ T) = (S.erase h).powerset := by
  classical
  ext T; simp [Finset.subset_erase]

/-- **Appendix A** (MWG, p. 681). The dividend family satisfies (18.AA.2) (for `v(∅) = 0`). -/
theorem shapleyFamily_isEgalitarian (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    IsEgalitarianSolution v (shapleyFamily v) := by
  classical
  refine ⟨fun S i _ h _ => ?_, fun S _ => ?_⟩
  · have key : ∀ i h : Fin n, shapleyFamily v S i - shapleyFamily v (S.erase h) i =
        ∑ T ∈ S.powerset, if h ∈ T ∧ i ∈ T then WelfareBargaining.dividend v T / T.card
          else 0 := by
      intro i h
      simp only [shapleyFamily]
      rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun T => h ∈ T),
        powerset_filter_not_mem, add_sub_cancel_right, Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hh : h ∈ T <;> simp [hh]
    rw [key i h, key h i]
    exact Finset.sum_congr rfl fun T _ => by simp only [and_comm]
  · simp only [shapleyFamily]
    rw [Finset.sum_comm, ← WelfareBargaining.sum_dividend v S]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : S ∩ T = T := Finset.inter_eq_right.2 (Finset.mem_powerset.1 hT)
    rw [Finset.sum_ite_mem, hTS, Finset.sum_const, nsmul_eq_mul]
    rcases Finset.eq_empty_or_nonempty T with rfl | hne
    · simp [WelfareBargaining.dividend, hv]
    · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hne.card_pos.ne')

/-- **Definition 18.AA.7** (MWG, p. 681). The Shapley value `Sh(I, v)`: the outcome of the
solution of (18.AA.2) on the grand coalition. -/
noncomputable def shapleyMWG (v : WelfareBargaining.Game n) (i : Fin n) : ℝ :=
  shapleyFamily v Finset.univ i

/-- **Definition 18.AA.7** (MWG, p. 681). The Shapley value is well defined: there is exactly
one outcome `Sh(I, v)` consistent with (18.AA.2), namely `shapleyMWG v`. -/
theorem definition_18_AA_7 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    ∃! x : Fin n → ℝ, ∃ φ, IsEgalitarianSolution v φ ∧ ∀ i, φ Finset.univ i = x i := by
  refine ⟨shapleyMWG v, ⟨shapleyFamily v, shapleyFamily_isEgalitarian v hv, fun _ => rfl⟩, ?_⟩
  rintro x ⟨φ, hφ, hx⟩
  funext i
  rw [← hx i]
  exact egalitarian_unique hφ (shapleyFamily_isEgalitarian v hv) _ i (Finset.mem_univ i)

/-- **Appendix A** (MWG, p. 680), (18.AA.1). For two players the Shapley value is the
egalitarian solution `Shᵢ(I, v) = v({i}) + (v(I) - v({1}) - v({2}))/2`. -/
theorem formula_18_AA_1 (v : WelfareBargaining.Game 2) (hv : v ∅ = 0) :
    shapleyMWG v 0 = v {0} + (v Finset.univ - v {0} - v {1}) / 2 ∧
      shapleyMWG v 1 = v {1} + (v Finset.univ - v {0} - v {1}) / 2 := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hu' : (Finset.univ : Finset (Fin 2)) = {1, 0} := by decide
  have h := shapleyFamily_isEgalitarian v hv
  constructor
  · simp only [shapleyMWG]
    rw [hu, egalitarian_pair h (by decide)]
  · simp only [shapleyMWG]
    rw [hu', egalitarian_pair h (by decide), Finset.pair_comm]
    ring

/-! ### (18.AA.3): the Shapley value is the average marginal contribution -/

/-- **Appendix A** (MWG, p. 681), (18.AA.3). The Shapley value of Definition 18.AA.7 is the
average over all orderings of the marginal contributions (Chapter 22's `shapley`). -/
theorem formula_18_AA_3 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    shapleyMWG v = WelfareBargaining.shapley v := by
  classical
  rw [WelfareBargaining.value_eq_dividendValue WelfareBargaining.shapley_pareto
    WelfareBargaining.shapley_symmetric WelfareBargaining.shapley_dummy
    (fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w) v hv]
  funext i
  simp only [shapleyMWG, shapleyFamily, WelfareBargaining.dividendValue]
  rw [Finset.sum_filter_of_ne]
  intro T _ hT
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst hne
  simp at hT

/-- **Appendix A** (MWG, p. 681), footnote 31: with the convention `v(∅) = 0`, the marginal
contribution `m(S, i) = v(S ∪ {i}) - v(S)` to the empty coalition is `v({i})`. -/
theorem footnote_18_31 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (i : Fin n) :
    v (insert i ∅) - v ∅ = v {i} := by
  simp [hv]

/-- **Appendix A** (MWG, p. 681). Along every ordering `π`, the marginal contributions of the
players to their predecessors `S(π, i) = {h : π(h) < π(i)}` exhaust `v(I)`:
`∑ᵢ m(S(π, i), i) = v(I)` (Chapter 22's `sum_margContrib`). -/
theorem sum_marginal_contributions (v : WelfareBargaining.Game n) (hv : v ∅ = 0)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i, (v (insert i (WelfareBargaining.preds σ i)) - v (WelfareBargaining.preds σ i)) =
      v Finset.univ :=
  WelfareBargaining.sum_margContrib v hv σ

/-- **Appendix A** (MWG, p. 681). The dividends of a subgame: `d_T((S, v)) = d_T(v)` if `T ⊆ S`, and
`0` otherwise. -/
theorem dividend_subgame (v : WelfareBargaining.Game n) (S T : Finset (Fin n)) :
    WelfareBargaining.dividend (subgame v S) T =
      if T ⊆ S then WelfareBargaining.dividend v T else 0 := by
  classical
  split_ifs with hTS
  · simp only [WelfareBargaining.dividend, subgame]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [Finset.inter_eq_left.2 ((Finset.mem_powerset.1 hR).trans hTS)]
  · obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hTS
    simp only [WelfareBargaining.dividend, subgame]
    rw [← Finset.insert_erase hjT, Finset.sum_powerset_insert (Finset.notMem_erase j T)]
    have hcard : (insert j (T.erase j)).card = (T.erase j).card + 1 :=
      Finset.card_insert_of_notMem (Finset.notMem_erase j T)
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun R hR => ?_
    have hRsub := Finset.mem_powerset.1 hR
    have hjR : j ∉ R := fun h => Finset.notMem_erase j T (hRsub h)
    have hRc : R.card ≤ (T.erase j).card := Finset.card_le_card hRsub
    rw [Finset.card_insert_of_notMem hjR, Finset.insert_inter_of_notMem hjS]
    have e : (T.erase j).card + 1 - R.card = ((T.erase j).card - R.card) + 1 := by omega
    have e' : (T.erase j).card + 1 - (R.card + 1) = (T.erase j).card - R.card := by omega
    rw [e, e', pow_succ]
    ring

/-- **Appendix A** (MWG, p. 681), (18.AA.3) for subgames: the Shapley value of the subgame
`(S, v)` (the average marginal contribution in the restricted game) is `Shᵢ(S, v)` of (18.AA.2),
for `i ∈ S`. -/
theorem shapley_subgame (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (S : Finset (Fin n))
    (i : Fin n) : WelfareBargaining.shapley (subgame v S) i = shapleyFamily v S i := by
  classical
  have hv' : subgame v S ∅ = 0 := by simp [subgame, hv]
  rw [← formula_18_AA_3 _ hv']
  simp only [shapleyMWG, shapleyFamily, dividend_subgame]
  rw [← Finset.sum_subset (Finset.powerset_mono.2 (Finset.subset_univ S)) (fun T _ hT => ?_)]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    simp [hT]
  · rw [Finset.mem_powerset] at hT
    simp [hT]

/-! ### (18.AA.4): the subset formula -/

/-- **Appendix A** (MWG, p. 682), (18.AA.4) for the subgame `(S, v)`:
`∑_{T ⊆ S, i ∈ T} (|S| - |T|)!(|T| - 1)!/|S|! · (v(T) - v(T \ {i}))` (footnote 32: `#T` is the
number of players in `T`). -/
noncomputable def subsetFormula (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : ℝ := by
  classical
  exact ∑ T ∈ S.powerset, if i ∈ T then
    ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) *
      (v T - v (T.erase i)) else 0

/-- **Appendix A** (MWG, p. 682). The hockey-stick identity
`∑_{j ≤ m} C(k + j, k) = C(k + m + 1, k + 1)`, used for (18.AA.4). -/
theorem hockey_stick (k m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (k + j).choose k = (k + m + 1).choose (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.choose_succ_succ (k + m + 1) k
    rw [Finset.sum_range_succ, ih, show k + (m + 1) + 1 = (k + m + 1) + 1 by ring,
      show k + (m + 1) = k + m + 1 by ring, h]
    ring

/-- **Appendix A** (MWG, p. 682). `(k + 1) ∑_{j ≤ m} C(m, j)(m - j)!(k + j)! = (k + m + 1)!`, the
counting identity behind (18.AA.4). -/
theorem shapley_weight_sum_nat (k m : ℕ) :
    (k + 1) * ∑ j ∈ Finset.range (m + 1),
      m.choose j * (m - j).factorial * (k + j).factorial = (k + m + 1).factorial := by
  have hterm : ∀ j ∈ Finset.range (m + 1), m.choose j * (m - j).factorial * (k + j).factorial =
      m.factorial * k.factorial * (k + j).choose k := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 := Nat.choose_mul_factorial_mul_factorial hjm
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k j)
    rw [show k + j - k = j by omega] at h2
    rw [← h2, ← h1]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hockey_stick]
  have h3 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ k + m + 1 by omega)
  rw [show k + m + 1 - (k + 1) = m by omega, Nat.factorial_succ] at h3
  rw [← h3]
  ring

/-- **Appendix A** (MWG, p. 682). The weights of (18.AA.4) of the coalitions between `U` and `S` add
up to `1/|U|`. -/
theorem shapley_weight_sum {U S : Finset (Fin n)} (hU : U.Nonempty) (hUS : U ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => U ⊆ T),
      ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) =
      1 / U.card := by
  classical
  set c : ℕ → ℝ := fun t =>
    ((S.card - t).factorial * (t - 1).factorial / S.card.factorial : ℝ) with hc
  have hbij : ∑ W ∈ (S \ U).powerset, c (U.card + W.card) =
      ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), c T.card := by
    refine Finset.sum_nbij' (fun W => W ∪ U) (fun T => T \ U) ?_ ?_ ?_ ?_ ?_
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset (hW.trans Finset.sdiff_subset) hUS, Finset.subset_union_right⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hT.1 le_rfl
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      exact Finset.union_sdiff_cancel_right
        (Finset.disjoint_of_subset_left hW disjoint_sdiff_self_left)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      exact Finset.sdiff_union_of_subset hT.2
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left hW disjoint_sdiff_self_left), add_comm]
  rw [← hbij, Finset.sum_powerset_apply_card (fun w => c (U.card + w))]
  obtain ⟨k, hk⟩ : ∃ k, U.card = k + 1 := ⟨U.card - 1, by have := hU.card_pos; omega⟩
  have hsd : (S \ U).card = S.card - U.card := Finset.card_sdiff_of_subset hUS
  have hSU : U.card ≤ S.card := Finset.card_le_card hUS
  set m := (S \ U).card with hm
  have hS : S.card = k + m + 1 := by omega
  have hnat := shapley_weight_sum_nat k m
  have hreal : ((k + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (m + 1),
      ((m.choose j * (m - j).factorial * (k + j).factorial : ℕ) : ℝ) =
      ((k + m + 1).factorial : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_mul, hnat]
  have hterm : ∀ j ∈ Finset.range (m + 1), (m.choose j) • c (U.card + j) =
      ((m.choose j * (m - j).factorial * (k + j).factorial : ℕ) : ℝ) /
        ((k + m + 1).factorial : ℝ) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    simp only [hc, nsmul_eq_mul]
    rw [hk, hS, show k + m + 1 - (k + 1 + j) = m - j by omega,
      show k + 1 + j - 1 = k + j by omega]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, hk]
  have hfac : ((k + m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  rw [div_eq_div_iff hfac hk1]
  rw [← hreal]
  push_cast
  ring

/-- **Appendix A** (MWG, p. 682). `v(T) - v(T \ {i}) = ∑_{U ⊆ T, i ∈ U} d_U(v)`. -/
theorem sub_erase_eq_sum_dividend (v : WelfareBargaining.Game n) (T : Finset (Fin n))
    (i : Fin n) :
    v T - v (T.erase i) =
      ∑ U ∈ T.powerset, if i ∈ U then WelfareBargaining.dividend v U else 0 := by
  classical
  rw [← WelfareBargaining.sum_dividend v T, ← WelfareBargaining.sum_dividend v (T.erase i),
    ← Finset.sum_filter_add_sum_filter_not T.powerset (fun U => i ∈ U),
    powerset_filter_not_mem, add_sub_cancel_right, Finset.sum_filter]

/-- **Appendix A** (MWG, p. 682), (18.AA.4) on every subgame: the subset formula equals the
solution of (18.AA.2). -/
theorem subsetFormula_eq_shapleyFamily (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : subsetFormula v S i = shapleyFamily v S i := by
  classical
  set c : Finset (Fin n) → ℝ := fun T =>
    ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) with hc
  have h1 : subsetFormula v S i = ∑ T ∈ S.powerset, ∑ U ∈ T.powerset,
      (if i ∈ U then c T * WelfareBargaining.dividend v U else 0) := by
    simp only [subsetFormula]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hi : i ∈ T
    · simp only [hi, ↓reduceIte]
      rw [sub_erase_eq_sum_dividend v T i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun U _ => ?_
      split_ifs <;> simp [hc]
    · simp only [hi, ↓reduceIte]
      refine (Finset.sum_eq_zero fun U hU => ?_).symm
      have : i ∉ U := fun h => hi (Finset.mem_powerset.1 hU h)
      simp [this]
  rw [h1, Finset.sum_comm' (t' := S.powerset) (s' := fun U => S.powerset.filter (fun T => U ⊆ T))
    (fun T U => by
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩)]
  simp only [shapleyFamily]
  refine Finset.sum_congr rfl fun U hU => ?_
  by_cases hi : i ∈ U
  · simp only [hi, ↓reduceIte]
    rw [← Finset.sum_mul, hc]
    rw [shapley_weight_sum ⟨i, hi⟩ (Finset.mem_powerset.1 hU)]
    ring
  · simp [hi]

/-- **Appendix A** (MWG, p. 682), (18.AA.4) = (18.AA.3): the subset formula on the grand
coalition is the Shapley value. -/
theorem formula_18_AA_4 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (i : Fin n) :
    subsetFormula v Finset.univ i = WelfareBargaining.shapley v i := by
  rw [subsetFormula_eq_shapleyFamily, ← formula_18_AA_3 v hv]
  rfl

/-- **Exercise 18.AA.4** (MWG, p. 685). If the Shapley value of every subgame is defined by
(18.AA.4), or equivalently by (18.AA.3) (the average marginal contribution in the subgame), then
the preservation-of-differences system (18.AA.2) is satisfied. -/
theorem exercise_18_AA_4 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    IsEgalitarianSolution v (subsetFormula v) ∧
      IsEgalitarianSolution v (fun S i => WelfareBargaining.shapley (subgame v S) i) := by
  have h := shapleyFamily_isEgalitarian v hv
  refine ⟨isEgalitarianSolution_congr (fun S i _ => ?_) h,
    isEgalitarianSolution_congr (fun S i _ => ?_) h⟩
  · exact (subsetFormula_eq_shapleyFamily v S i).symm
  · exact (shapley_subgame v hv S i).symm

/-! ### Properties (a)-(d) and the characterization (pp. 682-683; Exercises 18.AA.5-18.AA.6) -/

/-- **Appendix A** (MWG, p. 682), property (a), efficiency: `∑ᵢ Shᵢ(I, v) = v(I)`. -/
theorem shapley_efficiency (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    ∑ i, WelfareBargaining.shapley v i = v Finset.univ :=
  WelfareBargaining.shapley_pareto v hv

/-- **Appendix A** (MWG, p. 682), footnote 33: the games `v` and `v'` are identical except that
the roles of players `i` and `h` are permuted. -/
def RolesPermuted (v v' : WelfareBargaining.Game n) (i h : Fin n) : Prop :=
  ∀ S : Finset (Fin n), (i ∈ S → h ∈ S → v S = v' S) ∧ (i ∉ S → h ∉ S → v S = v' S) ∧
    (i ∈ S → h ∉ S → v S = v' (insert h (S.erase i))) ∧
    (h ∈ S → i ∉ S → v S = v' (insert i (S.erase h)))

/-- **Appendix A** (MWG, p. 682), footnote 33. The transposition of `i` and `h` fixes a coalition
containing both or neither. -/
theorem map_swap_of_iff {i h : Fin n} {S : Finset (Fin n)} (hS : i ∈ S ↔ h ∈ S) :
    S.map (Equiv.swap i h).toEmbedding = S := by
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne x i with rfl | hxi
  · rw [Equiv.swap_apply_left]; exact hS.symm
  rcases eq_or_ne x h with rfl | hxh
  · rw [Equiv.swap_apply_right]; exact hS
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxh]

/-- **Appendix A** (MWG, p. 682), footnote 33. The transposition of `i ∈ S` and `h ∉ S` maps `S` to
`(S \\ {i}) ∪ {h}`. -/
theorem map_swap_of_mem_notMem {i h : Fin n} {S : Finset (Fin n)} (hi : i ∈ S) (hh : h ∉ S) :
    S.map (Equiv.swap i h).toEmbedding = insert h (S.erase i) := by
  have hih : i ≠ h := fun e => hh (e ▸ hi)
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert, Finset.mem_erase]
  rcases eq_or_ne x i with rfl | hxi
  · rw [Equiv.swap_apply_left]; simp [hh, hih]
  rcases eq_or_ne x h with rfl | hxh
  · rw [Equiv.swap_apply_right]; simp [hi]
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxh]; simp [hxi, hxh]

/-- **Appendix A** (MWG, p. 682), footnote 33: the roles of `i` and `h` are permuted iff
`v(S) = v'(τ(S))` for the transposition `τ` of `i` and `h` (Chapter 22's formulation). -/
theorem rolesPermuted_iff (v v' : WelfareBargaining.Game n) (i h : Fin n) :
    RolesPermuted v v' i h ↔ ∀ S, v S = v' (S.map (Equiv.swap i h).toEmbedding) := by
  constructor
  · intro hp S
    by_cases hi : i ∈ S <;> by_cases hh : h ∈ S
    · rw [map_swap_of_iff (iff_of_true hi hh)]; exact (hp S).1 hi hh
    · rw [map_swap_of_mem_notMem hi hh]; exact (hp S).2.2.1 hi hh
    · rw [Equiv.swap_comm, map_swap_of_mem_notMem hh hi]; exact (hp S).2.2.2 hh hi
    · rw [map_swap_of_iff (iff_of_false hi hh)]; exact (hp S).2.1 hi hh
  · intro hm S
    refine ⟨fun hi hh => ?_, fun hi hh => ?_, fun hi hh => ?_, fun hh hi => ?_⟩
    · rw [hm, map_swap_of_iff (iff_of_true hi hh)]
    · rw [hm, map_swap_of_iff (iff_of_false hi hh)]
    · rw [hm, map_swap_of_mem_notMem hi hh]
    · rw [hm, Equiv.swap_comm, map_swap_of_mem_notMem hh hi]

/-- **Appendix A** (MWG, p. 682), property (b), symmetry in the sense of footnote 33: if `v'` is
`v` with the roles of `i` and `h` permuted then `Shᵢ(I, v) = Sh_h(I, v')`. -/
theorem shapley_symmetry_footnote_33 {v v' : WelfareBargaining.Game n} (hv : v ∅ = 0)
    {i h : Fin n} (hp : RolesPermuted v v' i h) :
    WelfareBargaining.shapley v i = WelfareBargaining.shapley v' h := by
  have hv' : v' ∅ = 0 := by rw [← ((hp ∅).2.1 (by simp) (by simp)), hv]
  have hm : v = fun S => v' (S.map (Equiv.swap i h).toEmbedding) :=
    funext ((rolesPermuted_iff v v' i h).1 hp)
  rw [hm, WelfareBargaining.shapley_symmetric v' (Equiv.swap i h) hv' i,
    Equiv.swap_apply_left]

/-- **Appendix A** (MWG, p. 682), property (c), linearity:
`Sh(I, αv + βw) = α Sh(I, v) + β Sh(I, w)`. -/
theorem shapley_linearity (a b : ℝ) (v w : WelfareBargaining.Game n) :
    WelfareBargaining.shapley (a • v + b • w) =
      a • WelfareBargaining.shapley v + b • WelfareBargaining.shapley w := by
  rw [WelfareBargaining.exercise_22_F_3a, WelfareBargaining.shapley_smul,
    WelfareBargaining.shapley_smul]

/-- **Appendix A** (MWG, p. 682), property (d), the dummy axiom: if
`v(S ∪ {i}) - v(S) = 0` for all `S` then `Shᵢ(I, v) = 0`. -/
theorem shapley_dummy_axiom {v : WelfareBargaining.Game n} (hv : v ∅ = 0) {i : Fin n}
    (hd : ∀ S, v (insert i S) - v S = 0) : WelfareBargaining.shapley v i = 0 :=
  WelfareBargaining.shapley_dummy v i hv fun S => sub_eq_zero.1 (hd S)

/-- **Appendix A** (MWG, p. 682). Symmetry of a solution `f` in the sense of property (b) and
footnote 33. -/
def MWGSymmetric (f : WelfareBargaining.Game n → Fin n → ℝ) : Prop :=
  ∀ (v v' : WelfareBargaining.Game n) (i h : Fin n), v ∅ = 0 → RolesPermuted v v' i h →
    f v i = f v' h

/-- **Appendix A** (MWG, p. 682). The Shapley value is symmetric in the sense of footnote 33. -/
theorem shapley_mwgSymmetric : MWGSymmetric (WelfareBargaining.shapley (n := n)) :=
  fun _ _ _ _ hv hp => shapley_symmetry_footnote_33 hv hp

/-- **Exercise 18.AA.5** (MWG, p. 686). A unanimity game: there is a coalition `S` with
`v(T) = v(S)` if `S ⊆ T` and `v(T) = 0` otherwise. -/
def IsUnanimityGame (v : WelfareBargaining.Game n) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ ∀ T, v T = if S ⊆ T then v S else 0

/-- **Exercise 18.AA.5** (MWG, p. 686). Chapter 22's `unanimity S c` is a unanimity game. -/
theorem isUnanimityGame_unanimity {S : Finset (Fin n)} (hS : S.Nonempty) (c : ℝ) :
    IsUnanimityGame (WelfareBargaining.unanimity S c) S := by
  classical
  refine ⟨hS, fun T => ?_⟩
  simp [WelfareBargaining.unanimity]

/-- **Exercise 18.AA.5** (MWG, p. 686). Efficiency, symmetry (footnote 33) and the dummy axiom
force a solution to distribute `v(S)` equally among the members of `S` in a unanimity game. -/
theorem exercise_18_AA_5 {f : WelfareBargaining.Game n → Fin n → ℝ}
    (hP : WelfareBargaining.CoopPareto f) (hS : MWGSymmetric f)
    (hD : WelfareBargaining.CoopDummy f) {v : WelfareBargaining.Game n} {S : Finset (Fin n)}
    (hu : IsUnanimityGame v S) (i : Fin n) :
    f v i = if i ∈ S then v S / S.card else 0 := by
  classical
  obtain ⟨hSne, hv⟩ := hu
  have h0 : v ∅ = 0 := by
    rw [hv ∅]; simp [Finset.subset_empty, hSne.ne_empty]
  have hdummy : ∀ j ∉ S, f v j = 0 := by
    intro j hj
    refine hD v j h0 fun T => ?_
    rw [hv (insert j T), hv T]
    have : S ⊆ insert j T ↔ S ⊆ T :=
      ⟨fun h x hx => (Finset.mem_insert.1 (h hx)).resolve_left fun e => hj (e ▸ hx),
        fun h => h.trans (Finset.subset_insert _ _)⟩
    simp only [this]
  have hequal : ∀ j ∈ S, ∀ k ∈ S, f v j = f v k := by
    intro j hj k hk
    refine hS v v j k h0 ((rolesPermuted_iff v v j k).2 fun T => ?_)
    rw [hv T, hv (T.map _)]
    have hS' : S.map (Equiv.swap j k).toEmbedding = S := map_swap_of_iff (iff_of_true hj hk)
    have : S ⊆ T.map (Equiv.swap j k).toEmbedding ↔ S ⊆ T := by
      conv_lhs => rw [← hS']
      exact Finset.map_subset_map
    simp only [this]
  have hsum := hP v h0
  obtain ⟨t, ht⟩ := hSne
  have hsplit : ∑ j, f v j = S.card * f v t := by
    rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hdummy j hj,
      Finset.sum_congr rfl fun j hj => hequal j hj t ht]
    simp
  have hvS : v Finset.univ = v S := by rw [hv]; simp
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨t, ht⟩)
  split_ifs with hi
  · rw [hequal i hi t ht]
    rw [hsplit, hvS] at hsum
    rw [eq_div_iff hcard.ne']
    linarith
  · exact hdummy i hi

/-- **Exercise 18.AA.6** (MWG, p. 686). Every TU game (`v(∅) = 0`) is a linear combination of
unanimity games, with the Harsanyi dividends as coefficients (Chapter 22's
`eq_sum_unanimity`). -/
theorem exercise_18_AA_6_decomposition (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    v = fun S => ∑ T ∈ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) S :=
  WelfareBargaining.eq_sum_unanimity v hv

/-- **Exercise 18.AA.6** (MWG, p. 686). The coefficients of the decomposition are unique: if
`v = ∑_{T ≠ ∅} c_T u_T` then `c_T = d_T(v)` for every coalition `T`. -/
theorem exercise_18_AA_6_unique (v : WelfareBargaining.Game n) (c : Finset (Fin n) → ℝ)
    (hc : ∀ S, v S = ∑ T ∈ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      WelfareBargaining.unanimity T (c T) S) :
    ∀ T : Finset (Fin n), T.Nonempty → c T = WelfareBargaining.dividend v T := by
  classical
  set c' : Finset (Fin n) → ℝ := fun T => if T.Nonempty then c T else 0 with hc'
  have hv : ∀ S, v S = ∑ T ∈ S.powerset, c' T := by
    intro S
    rw [hc S]
    simp only [WelfareBargaining.unanimity, hc']
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext T; simp [and_comm]
    · intro _ _; rfl
  set e : Finset (Fin n) → ℝ := fun T => c' T - WelfareBargaining.dividend v T with he
  have hsum : ∀ S : Finset (Fin n), ∑ T ∈ S.powerset, e T = 0 := by
    intro S
    simp only [he, Finset.sum_sub_distrib, ← hv S, WelfareBargaining.sum_dividend, sub_self]
  have hzero : ∀ S : Finset (Fin n), e S = 0 := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      have h := hsum S
      rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S)] at h
      rw [Finset.sum_eq_zero fun T hT => ih T ?_] at h
      · simpa using h
      · obtain ⟨hne, hsub⟩ := Finset.mem_erase.1 hT
        exact Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hsub, hne⟩
  intro T hT
  have := hzero T
  simp only [he, hc', hT, ↓reduceIte] at this
  linarith

/-- **Exercise 18.AA.6** (MWG, p. 686), and the characterization claim of p. 682: a solution
satisfying efficiency, symmetry (footnote 33), the dummy axiom and linearity is the Shapley value
(via Exercise 18.AA.5 and the decomposition into unanimity games). -/
theorem exercise_18_AA_6 {f : WelfareBargaining.Game n → Fin n → ℝ}
    (hP : WelfareBargaining.CoopPareto f) (hS : MWGSymmetric f)
    (hD : WelfareBargaining.CoopDummy f) (hL : WelfareBargaining.CoopLinear f)
    (v : WelfareBargaining.Game n) (hv : v ∅ = 0) : f v = WelfareBargaining.shapley v := by
  classical
  have hzero : f 0 = 0 := by
    have := hL 0 0 rfl rfl
    simp only [add_zero] at this
    have h2 : f 0 + f 0 = f 0 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have key : ∀ A ⊆ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      f (fun S => ∑ T ∈ A, WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) S) =
        ∑ T ∈ A, f (WelfareBargaining.unanimity T (WelfareBargaining.dividend v T)) := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; simp only [Finset.sum_empty]; exact hzero
    | insert T A hTA ih =>
      intro hsub
      have hT : T.Nonempty := (Finset.mem_filter.1 (hsub (Finset.mem_insert_self T A))).2
      have hA : A ⊆ _ := (Finset.subset_insert T A).trans hsub
      have hsplit : (fun S => ∑ T' ∈ insert T A,
          WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S) =
          WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) +
            fun S => ∑ T' ∈ A,
              WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S := by
        funext S; simp [Finset.sum_insert hTA]
      have h0 : (fun S => ∑ T' ∈ A,
          WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S) ∅ = 0 :=
        Finset.sum_eq_zero fun T' hT' =>
          WelfareBargaining.unanimity_empty (Finset.mem_filter.1 (hA hT')).2 _
      rw [hsplit, hL _ _ (WelfareBargaining.unanimity_empty hT _) h0, ih hA,
        Finset.sum_insert hTA]
  rw [WelfareBargaining.value_eq_dividendValue WelfareBargaining.shapley_pareto
    WelfareBargaining.shapley_symmetric WelfareBargaining.shapley_dummy
    (fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w) v hv]
  conv_lhs => rw [WelfareBargaining.eq_sum_unanimity v hv]
  rw [key _ subset_rfl]
  funext i
  simp only [Finset.sum_apply, WelfareBargaining.dividendValue]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hu := isUnanimityGame_unanimity (Finset.mem_filter.1 hT).2 (WelfareBargaining.dividend v T)
  rw [exercise_18_AA_5 hP hS hD hu i]
  classical
  simp [WelfareBargaining.unanimity]

/-- **Appendix A** (MWG, p. 682). The four properties (a)-(d) characterize the Shapley value: the
Shapley value has them, and any solution with them is the Shapley value. -/
theorem shapley_characterization :
    (WelfareBargaining.CoopPareto (WelfareBargaining.shapley (n := n)) ∧
      MWGSymmetric (WelfareBargaining.shapley (n := n)) ∧
      WelfareBargaining.CoopLinear (WelfareBargaining.shapley (n := n)) ∧
      WelfareBargaining.CoopDummy (WelfareBargaining.shapley (n := n))) ∧
    ∀ f : WelfareBargaining.Game n → Fin n → ℝ, WelfareBargaining.CoopPareto f →
      MWGSymmetric f → WelfareBargaining.CoopDummy f → WelfareBargaining.CoopLinear f →
      ∀ v, v ∅ = 0 → f v = WelfareBargaining.shapley v :=
  ⟨⟨WelfareBargaining.shapley_pareto, shapley_mwgSymmetric,
    fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w, WelfareBargaining.shapley_dummy⟩,
    fun _ hP hS hD hL v hv => exercise_18_AA_6 hP hS hD hL v hv⟩

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The glove market, convex games and production games (MWG Appendix A, pp. 681-684;
Exercises 18.AA.7-18.AA.8)

* **Example 18.AA.7** (glove market): the six orderings give player 3 the marginal contributions
  `1, 1, 1, 1, 0, 0` (`example_18_AA_7_orderings`), `Sh = (1/6, 1/6, 2/3)`
  (`example_18_AA_7`), the displayed instance of (18.AA.2) (`example_18_AA_7_check`), and the
  continuation of p. 683: the core is `{(0, 0, 1)}` (`example_18_AA_7_core`), with the book's
  blocking construction (`example_18_AA_7_block`); the Shapley value is not in the core
  (`example_18_AA_7_shapley_not_core`), as it trivially is not when the core is empty
  (`shapley_not_core_majority`).
* **Definition 18.AA.8** (`IsConvexGame`) and **Proposition 18.AA.1** (`proposition_18_AA_1`):
  the Shapley value of a convex game is in the core. Departure in the route only: we prove that
  every marginal-contribution vector is in the core (`marginal_vector_mem_core`), and the Shapley
  value is their average (18.AA.3), instead of the book's comparison `Shᵢ(S, v) ≤ Shᵢ(T, v)`.
* **Example 18.AA.8 / Exercise 18.AA.7** (`exercise_18_AA_7`): production games with
  complementary inputs are convex. Departure: the hypothesis `∂²f/∂z_h∂z_k ≥ 0` is stated as the
  increasing-differences property `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'`, `a ≥ 0`
  (`IncreasingDifferences`, which it implies for `C²` functions on the orthant: proved in
  `Closer18AA`, `example_18_AA_8_increasingDifferences`). The text's "Exercise 18.AA.8" on
  p. 683 is Exercise 18.AA.7 (correction).
  For `N = 1` convexity of `f` suffices (`example_18_AA_8_one_input`, with the second-derivative
  form `example_18_AA_8_one_input_deriv`); for `N > 1` the condition is neither sufficient
  (`z₁z₂`) nor necessary (`(z₁ - z₂)²`) for convexity of `f` (`example_18_AA_8_not_sufficient`,
  `example_18_AA_8_not_necessary`).
* **Exercise 18.AA.8** (`exercise_18_AA_8`): `f(z) = max(z₁, z₂)` is convex, but the game with
  `ω₁ = (1, 0)`, `ω₂ = (0, 1)` has an empty core and is not convex.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-! ### Example 18.AA.7: the glove market -/

/-- **Example 18.AA.7** (MWG, p. 681). The glove market of Example 18.AA.7 with integer worths:
players `1, 2` (here `0, 1`) own a right glove, player `3` (here `2`) a left glove; a coalition is
worth `1` iff it holds a pair. -/
def gloveInt (S : Finset (Fin 3)) : ℤ := if 2 ∈ S ∧ (0 ∈ S ∨ 1 ∈ S) then 1 else 0

/-- **Example 18.AA.7** (MWG, p. 681). The glove market game. -/
def gloveGame : WelfareBargaining.Game 3 := fun S => (gloveInt S : ℝ)

/-- **Example 18.AA.7** (MWG, p. 681). The worths: `v({1,2,3}) = v({1,3}) = v({2,3}) = 1`,
`v({1,2}) = 0` and `v({i}) = 0`. -/
theorem example_18_AA_7_values :
    gloveGame Finset.univ = 1 ∧ gloveGame {0, 2} = 1 ∧ gloveGame {1, 2} = 1 ∧
      gloveGame {0, 1} = 0 ∧ ∀ i, gloveGame {i} = 0 := by
  refine ⟨by simp [gloveGame, gloveInt], by simp [gloveGame, gloveInt],
    by simp [gloveGame, gloveInt], by simp [gloveGame, gloveInt], fun i => ?_⟩
  fin_cases i <;> simp [gloveGame, gloveInt]

/-- **Example 18.AA.7** (MWG, p. 682). Player 3's marginal contribution in the ordering `π` (integer
version). -/
def gloveMarg (σ : Equiv.Perm (Fin 3)) : ℤ :=
  gloveInt (insert 2 (WelfareBargaining.preds σ 2)) - gloveInt (WelfareBargaining.preds σ 2)

/-- **Example 18.AA.7** (MWG, p. 682). Over the six orderings, player 3's marginal contributions
are `1, 1, 1, 1, 0, 0`: four orderings give `1`, two give `0`, and they add up to `4`. -/
theorem example_18_AA_7_orderings :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => gloveMarg σ = 1).card = 4 ∧
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => gloveMarg σ = 0).card = 2 ∧
      ∑ σ : Equiv.Perm (Fin 3), gloveMarg σ = 4 := by
  decide

/-- **Example 18.AA.7** (MWG, p. 681). `v(∅) = 0` (footnote 31). -/
theorem gloveGame_empty : gloveGame ∅ = 0 := by simp [gloveGame, gloveInt]

/-- **Example 18.AA.7** (MWG, p. 682). Players 1 and 2 play symmetric roles. -/
theorem gloveGame_swap : ∀ S : Finset (Fin 3),
    gloveGame S = gloveGame (S.map (Equiv.swap (0 : Fin 3) 1).toEmbedding) := by
  have h : ∀ S : Finset (Fin 3),
      gloveInt S = gloveInt (S.map (Equiv.swap (0 : Fin 3) 1).toEmbedding) := by decide
  intro S
  simp only [gloveGame]
  rw [h S]

/-- **Example 18.AA.7** (MWG, p. 682). The Shapley value of the glove market is
`(1/6, 1/6, 2/3)`. -/
theorem example_18_AA_7 :
    WelfareBargaining.shapley gloveGame = ![1 / 6, 1 / 6, 2 / 3] := by
  have h2 : WelfareBargaining.shapley gloveGame 2 = 2 / 3 := by
    have hm : ∀ σ : Equiv.Perm (Fin 3),
        WelfareBargaining.margContrib gloveGame σ 2 = ((gloveMarg σ : ℤ) : ℝ) := by
      intro σ
      simp [WelfareBargaining.margContrib, gloveMarg, gloveGame]
    simp only [WelfareBargaining.shapley, hm]
    rw [← Int.cast_sum, example_18_AA_7_orderings.2.2]
    simp [Nat.factorial]
    norm_num
  have h01 : WelfareBargaining.shapley gloveGame 0 = WelfareBargaining.shapley gloveGame 1 :=
    shapley_symmetry_footnote_33 gloveGame_empty
      ((rolesPermuted_iff gloveGame gloveGame 0 1).2 gloveGame_swap)
  have hsum := shapley_efficiency gloveGame gloveGame_empty
  rw [Fin.sum_univ_three, h2, ← h01, example_18_AA_7_values.1] at hsum
  funext i
  fin_cases i
  · simp; linarith
  · simp; linarith
  · simpa using h2

/-- **Example 18.AA.7** (MWG, p. 682). The numbers satisfy (18.AA.2), e.g.
`Sh₃(I, v) - Sh₃(I \ {1}, v) = 2/3 - 1/2 = 1/6 - 0 = Sh₁(I, v) - Sh₁(I \ {3}, v)`. -/
theorem example_18_AA_7_check :
    shapleyFamily gloveGame Finset.univ 2 = 2 / 3 ∧
      shapleyFamily gloveGame (Finset.univ.erase 0) 2 = 1 / 2 ∧
      shapleyFamily gloveGame Finset.univ 0 = 1 / 6 ∧
      shapleyFamily gloveGame (Finset.univ.erase 2) 0 = 0 ∧
      shapleyFamily gloveGame Finset.univ 2 - shapleyFamily gloveGame (Finset.univ.erase 0) 2 =
        shapleyFamily gloveGame Finset.univ 0 -
          shapleyFamily gloveGame (Finset.univ.erase 2) 0 := by
  have hφ := shapleyFamily_isEgalitarian gloveGame gloveGame_empty
  have hI : ∀ i, shapleyFamily gloveGame Finset.univ i = WelfareBargaining.shapley gloveGame i :=
    fun i => congrFun (formula_18_AA_3 gloveGame gloveGame_empty) i
  have e0 : (Finset.univ.erase (0 : Fin 3)) = {2, 1} := by decide
  have e2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  have a : shapleyFamily gloveGame Finset.univ 2 = 2 / 3 := by
    rw [hI, example_18_AA_7]; simp
  have b : shapleyFamily gloveGame (Finset.univ.erase 0) 2 = 1 / 2 := by
    rw [e0, egalitarian_pair hφ (by decide)]
    simp [gloveGame, gloveInt]
  have c : shapleyFamily gloveGame Finset.univ 0 = 1 / 6 := by
    rw [hI, example_18_AA_7]; simp
  have d : shapleyFamily gloveGame (Finset.univ.erase 2) 0 = 0 := by
    rw [e2, egalitarian_pair hφ (by decide)]
    simp [gloveGame, gloveInt]
  refine ⟨a, b, c, d, ?_⟩
  rw [a, b, c, d]; norm_num

/-- **Example 18.AA.7 continued** (MWG, p. 683). The total payoff of a coalition at `(0, 0, 1)`. -/
theorem sum_glove_core (S : Finset (Fin 3)) :
    ∑ i ∈ S, (![0, 0, 1] : Fin 3 → ℝ) i = if 2 ∈ S then 1 else 0 := by
  have h : ∀ S : Finset (Fin 3), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = Finset.univ := by decide
  rcases h S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Fin.sum_univ_three]

/-- **Example 18.AA.7 continued** (MWG, p. 683). The core of the glove market consists of the
single outcome `(0, 0, 1)`. -/
theorem example_18_AA_7_core : tuCore gloveGame = {![0, 0, 1]} := by
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hS, htot⟩
    have h0 := hS {0} (by simp)
    have h1 := hS {1} (by simp)
    have h2 := hS {2} (by simp)
    have h02 := hS {0, 2} (by simp)
    have h12 := hS {1, 2} (by simp)
    simp [gloveGame, gloveInt, Fin.sum_univ_three] at h0 h1 h2 h02 h12 htot
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun S _ => ?_, ?_⟩
    · rw [sum_glove_core]
      simp only [gloveGame, gloveInt]
      split_ifs <;> simp_all
    · rw [sum_glove_core]; simp [gloveGame, gloveInt]

/-- **Example 18.AA.7 continued** (MWG, p. 683). If `u₁ + u₂ + u₃ = 1` and `u₁ > 0`, the
coalition `{2, 3}` blocks `u` by means of `(0, u₂ + u₁/2, u₃ + u₁/2)`. -/
theorem example_18_AA_7_block {u : Fin 3 → ℝ} (hsum : u 0 + u 1 + u 2 = 1) (hu : 0 < u 0) :
    ntuBlocks (tuSet gloveGame) {1, 2} u ∧
      ![0, u 1 + u 0 / 2, u 2 + u 0 / 2] ∈ tuSet gloveGame {1, 2} := by
  have hmem : ![0, u 1 + u 0 / 2, u 2 + u 0 / 2] ∈ tuSet gloveGame {1, 2} := by
    simp only [tuSet, Set.mem_ofPred_eq]
    simp [gloveGame, gloveInt]
    linarith
  refine ⟨⟨by simp, _, hmem, fun i hi => ?_⟩, hmem⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp <;> linarith

/-- **Example 18.AA.7 continued** (MWG, p. 683). The Shapley value, although skewed towards
player 3, is not in the core: it leaves `1/6` to each owner of a right glove. -/
theorem example_18_AA_7_shapley_not_core :
    WelfareBargaining.shapley gloveGame ∉ tuCore gloveGame := by
  rw [example_18_AA_7_core, example_18_AA_7, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

/-- **Appendix A** (MWG, pp. 682-683). The Shapley value is defined for every game, so it need not
be in the core when the core is empty: e.g. the TU majority voting game of Example 18.AA.3. -/
theorem shapley_not_core_majority :
    WelfareBargaining.shapley tuMajority ∉ tuCore tuMajority := by
  rw [example_18_AA_4_tu]
  exact Set.notMem_empty _

/-! ### Convex games: Definition 18.AA.8 and Proposition 18.AA.1 -/

/-- **Definition 18.AA.8** (MWG, p. 683). A convex game: marginal contributions increase with
the coalition, `v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T)` for `S ⊆ T` and `i ∉ T`. -/
def IsConvexGame (v : WelfareBargaining.Game n) : Prop :=
  ∀ S T : Finset (Fin n), S ⊆ T → ∀ i, i ∉ T → v (insert i S) - v S ≤ v (insert i T) - v T

/-- **Proposition 18.AA.1** (MWG, p. 683), key step: in a convex game every vector of marginal
contributions along an ordering gives every coalition at least its worth. -/
theorem marginal_vector_mem_core {v : WelfareBargaining.Game n} (hc : IsConvexGame v)
    (hv : v ∅ = 0) (σ : Equiv.Perm (Fin n)) :
    ∀ S : Finset (Fin n), v S ≤ ∑ i ∈ S, WelfareBargaining.margContrib v σ i := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [hv]
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun k => σ k) hne
    have hsub : S.erase j ⊆ WelfareBargaining.preds σ j := by
      intro k hk
      obtain ⟨hkj, hkS⟩ := Finset.mem_erase.1 hk
      simp only [WelfareBargaining.preds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (hmax k hkS) fun e => hkj (σ.injective e)
    have hjp : j ∉ WelfareBargaining.preds σ j := by simp [WelfareBargaining.preds]
    have hconv := hc _ _ hsub j hjp
    rw [Finset.insert_erase hj] at hconv
    have hih := ih _ (Finset.erase_ssubset hj)
    rw [← Finset.add_sum_erase S _ hj]
    simp only [WelfareBargaining.margContrib] at hconv hih ⊢
    linarith

/-- **Proposition 18.AA.1** (MWG, p. 683). If the game is convex then its Shapley value is in the
core (in particular, the core is nonempty). -/
theorem proposition_18_AA_1 {v : WelfareBargaining.Game n} (hc : IsConvexGame v)
    (hv : v ∅ = 0) : WelfareBargaining.shapley v ∈ tuCore v := by
  refine ⟨fun S _ => ?_, (shapley_efficiency v hv).le⟩
  simp only [WelfareBargaining.shapley]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos n)
  have hle : ∑ _σ : Equiv.Perm (Fin n), v S ≤
      ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ S, WelfareBargaining.margContrib v σ i :=
    Finset.sum_le_sum fun σ _ => marginal_vector_mem_core hc hv σ S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hle
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hfac]
  linarith

/-! ### Example 18.AA.8 and Exercises 18.AA.7-18.AA.8: production games -/

/-- **Example 18.AA.8** (MWG, p. 683). Increasing marginal productivities, stated as increasing
differences on `ℝ^N₊`: `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'` and `a ≥ 0` (for
`C²` functions this is the condition `∂²f/∂z_h∂z_k ≥ 0` for all `h, k`). -/
def IncreasingDifferences {N : ℕ} (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ z z' a : Fin N → ℝ, 0 ≤ z → z ≤ z' → 0 ≤ a → f (z + a) - f z ≤ f (z' + a) - f z'

/-- **Example 18.AA.8** (MWG, p. 683). The TU game of an `N`-input technology `f` with input
endowments `ωᵢ ∈ ℝ^N₊`: `v(S) = f(∑_{i∈S} ωᵢ)`. -/
def inputGame {N : ℕ} (f : (Fin N → ℝ) → ℝ) (ω : Fin n → Fin N → ℝ) :
    WelfareBargaining.Game n := fun S => f (∑ i ∈ S, ω i)

/-- **Exercise 18.AA.7** (MWG, p. 686; called "Exercise 18.AA.8" on p. 683). The production game
of Example 18.AA.8 is convex. -/
theorem exercise_18_AA_7 {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : IncreasingDifferences f)
    {ω : Fin n → Fin N → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (inputGame f ω) := by
  classical
  intro S T hST i hiT
  have hiS : i ∉ S := fun h => hiT (hST h)
  simp only [inputGame]
  rw [Finset.sum_insert hiS, Finset.sum_insert hiT, add_comm (ω i), add_comm (ω i)]
  exact hf _ _ _ (Finset.sum_nonneg fun j _ => hω j)
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun j _ _ => hω j) (hω i)

/-- **Example 18.AA.8** (MWG, p. 683). A convex function on `ℝ₊` has increasing differences. -/
theorem convexOn_increasing_differences {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {z z' a : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z') (ha : 0 ≤ a) :
    f (z + a) - f z ≤ f (z' + a) - f z' := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  have h1 := hf.slope_mono (x := z) (Set.mem_Ici.2 hz)
    (show z + a ∈ Set.Ici 0 \ {z} by simp; constructor <;> linarith)
    (show z' + a ∈ Set.Ici 0 \ {z} by simp; constructor <;> linarith) (by linarith)
  have h2 := hf.slope_mono (x := z' + a) (show z' + a ∈ Set.Ici 0 by simp; linarith)
    (show z ∈ Set.Ici 0 \ {z' + a} by simp; constructor <;> linarith)
    (show z' ∈ Set.Ici 0 \ {z' + a} by simp; constructor <;> linarith) hzz
  rw [slope_comm f (z' + a) z, slope_comm f (z' + a) z'] at h2
  have h3 := h1.trans h2
  simp only [slope_def_field] at h3
  rw [show z + a - z = a by ring, show z' + a - z' = a by ring] at h3
  exact (div_le_div_iff_of_pos_right ha').1 h3

/-- **Example 18.AA.8** (MWG, p. 683). With one input (`N = 1`), convexity of `f` suffices for the
convexity of the game `v(S) = f(∑_{i∈S} ωᵢ)`. -/
theorem example_18_AA_8_one_input {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {ω : Fin n → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (prodGame f ω) := by
  classical
  intro S T hST i hiT
  have hiS : i ∉ S := fun h => hiT (hST h)
  simp only [prodGame]
  rw [Finset.sum_insert hiS, Finset.sum_insert hiT, add_comm (ω i), add_comm (ω i)]
  exact convexOn_increasing_differences hf (Finset.sum_nonneg fun j _ => hω j)
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun j _ _ => hω j) (hω i)

/-- **Example 18.AA.8** (MWG, p. 683). For `N = 1` the condition `f'' ≥ 0` (on `ℝ₊`) says that `f`
is convex, hence the game is convex. -/
theorem example_18_AA_8_one_input_deriv {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f (Set.Ici 0)) (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ici 0))
    (hpos : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ (deriv^[2] f) x) {ω : Fin n → ℝ}
    (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (prodGame f ω) :=
  example_18_AA_8_one_input (convexOn_of_deriv2_nonneg' (convex_Ici 0) hf' hf'' hpos) hω

/-- **Example 18.AA.8** (MWG, p. 683). For `N > 1` the complementarity condition is not
sufficient for convexity of `f`: `f(z) = z₁z₂` (cross partial `1`, own partials `0`) has
increasing differences but is not convex on `ℝ²₊`. -/
theorem example_18_AA_8_not_sufficient :
    IncreasingDifferences (fun z : Fin 2 → ℝ => z 0 * z 1) ∧
      ¬ ConvexOn ℝ (MWG.ConsumerChoice.nonnegOrthant 2) (fun z : Fin 2 → ℝ => z 0 * z 1) := by
  refine ⟨fun z z' a hz hzz ha => ?_, fun hc => ?_⟩
  · simp only [Pi.add_apply]
    have h0 := hzz 0
    have h1 := hzz 1
    have a0 := ha 0
    have a1 := ha 1
    nlinarith [mul_le_mul_of_nonneg_left h1 a0, mul_le_mul_of_nonneg_left h0 a1]
  · have hx : (![1, 0] : Fin 2 → ℝ) ∈ MWG.ConsumerChoice.nonnegOrthant 2 := by
      intro l; fin_cases l <;> simp
    have hy : (![0, 1] : Fin 2 → ℝ) ∈ MWG.ConsumerChoice.nonnegOrthant 2 := by
      intro l; fin_cases l <;> simp
    have := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp at this
    norm_num at this

/-- **Example 18.AA.8** (MWG, p. 683). For `N > 1` the complementarity condition is not necessary
for convexity of `f`: `f(z) = (z₁ - z₂)²` is convex (cross partial `-2`) but does not have
increasing differences. -/
theorem example_18_AA_8_not_necessary :
    ConvexOn ℝ Set.univ (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 2) ∧
      ¬ IncreasingDifferences (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 2) := by
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun h => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg ((x 0 - x 1) - (y 0 - y 1)), mul_nonneg ha hb]
  · have := h 0 ![0, 1] ![1, 0] le_rfl (fun l => by fin_cases l <;> simp)
      (fun l => by fin_cases l <;> simp)
    simp at this
    norm_num at this

/-- **Exercise 18.AA.8** (MWG, p. 686). The technology `f(z) = max(z₁, z₂)` of Exercise 18.AA.8. -/
def maxTech (z : Fin 2 → ℝ) : ℝ := max (z 0) (z 1)

/-- **Exercise 18.AA.8** (MWG, p. 686). The two-player game of Exercise 18.AA.8: `ω₁ = (1, 0)`,
`ω₂ = (0, 1)`, `f = maxTech`. -/
def maxGame : WelfareBargaining.Game 2 := inputGame maxTech ![![1, 0], ![0, 1]]

/-- **Exercise 18.AA.8** (MWG, p. 686). The two-input technology `f(z) = max(z₁, z₂)` is convex
(and nondecreasing, with `f(0) = 0`), but its production game with `ω₁ = (1, 0)`, `ω₂ = (0, 1)`
has an empty core; hence (Proposition 18.AA.1) the game is not convex. -/
theorem exercise_18_AA_8 :
    ConvexOn ℝ Set.univ maxTech ∧ Monotone maxTech ∧ maxTech 0 = 0 ∧
      tuCore maxGame = ∅ ∧ ¬ IsConvexGame maxGame := by
  have hcore : tuCore maxGame = ∅ := by
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hS, htot⟩
    have h0 := hS {0} (by simp)
    have h1 := hS {1} (by simp)
    simp [maxGame, inputGame, maxTech, Fin.sum_univ_two] at h0 h1 htot
    linarith
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun x y hxy => ?_, by simp [maxTech],
    hcore, fun hconv => ?_⟩
  · simp only [maxTech, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine max_le ?_ ?_
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (x 0) (x 1)) ha,
        mul_le_mul_of_nonneg_left (le_max_left (y 0) (y 1)) hb]
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_right (x 0) (x 1)) ha,
        mul_le_mul_of_nonneg_left (le_max_right (y 0) (y 1)) hb]
  · exact max_le_max (hxy 0) (hxy 1)
  · have h0 : maxGame ∅ = 0 := by simp [maxGame, inputGame, maxTech]
    have := proposition_18_AA_1 hconv h0
    rw [hcore] at this
    exact this

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 18.AA.9-18.AA.10 (MWG, p. 686)

* **Exercise 18.AA.9**: the four-player game (`game9`) with its table of worths
  (`exercise_18_AA_9_table`); (a) it is the game of the technology `min{z₁, z₂}` with
  `ω₁ = ω₂ = (1, 0)`, `ω₃ = ω₄ = (0, 1)` (`exercise_18_AA_9a`); (b) its core is exactly
  `{(α, α, 1 - α, 1 - α) : α ∈ [0, 1]}` (`exercise_18_AA_9b`; the book asks only for `⊇`);
  (c) raising `v({1,3,4})` to `2` leaves the single core point `(0, 0, 1, 1)`, which gives player 1
  no more than any former core point (`exercise_18_AA_9c`, `exercise_18_AA_9c_compare`);
  (d) the Shapley value is `(1/2, 1/2, 1/2, 1/2)`, by symmetry and efficiency
  (`exercise_18_AA_9d`); (e) after the change it is `(7/12, 1/4, 7/12, 7/12)` (linearity and
  unanimity games; `exercise_18_AA_9e`), and player 1's Shapley value rises while her core payoff
  falls to `0` (`exercise_18_AA_9e_compare`; the discussion is verbal).
* **Exercise 18.AA.10** (`C(X) = X^γ`, `0 < γ < 1`): (a) the Shapley cost allocation
  `ψ₁ = (C(x₁ + x₂) + C(x₁) - C(x₂))/2`, `ψ₂` symmetric, exhausting `C` (`exercise_18_AA_10a`);
  (b) its marginal costs `∂ψ₁/∂x₁ = (C'(x₁ + x₂) + C'(x₁))/2` (`exercise_18_AA_10b`);
  (c) **correction**: with `0 < γ < 1` total profit `α₁x₁ + α₂x₂ - C(x₁ + x₂)` is unbounded above,
  so no efficient (profit-maximizing) choice exists (`exercise_18_AA_10c_unbounded`,
  `exercise_18_AA_10c_no_max`), and the divisions' first-order conditions differ from the joint
  one because each division is charged more than the true marginal cost
  (`exercise_18_AA_10c_foc`); (d) **corrected statement**: no differentiable rule with
  `ψ₁ + ψ₂ = C` charges each division the full marginal cost `C'(x₁ + x₂)` on the open quadrant
  (`exercise_18_AA_10d`).
-/

namespace MWG.CoreFoundations

/-! ### Exercise 18.AA.9 -/

/-- **Exercise 18.AA.9** (MWG, p. 686). The worths of Exercise 18.AA.9 as integers:
`min{#(S ∩ {1, 2}), #(S ∩ {3, 4})}`. -/
def v9Int (S : Finset (Fin 4)) : ℤ :=
  min ((S.filter fun i => i.val < 2).card : ℤ) ((S.filter fun i => ¬ i.val < 2).card : ℤ)

/-- **Exercise 18.AA.9** (MWG, p. 686). The four-player game. -/
def game9 : WelfareBargaining.Game 4 := fun S => (v9Int S : ℝ)

/-- **Exercise 18.AA.9(c)** (MWG, p. 686). The game with `v({1, 3, 4})` raised to `2`. -/
noncomputable def game9mod : WelfareBargaining.Game 4 := by
  classical
  exact fun S => if S = {0, 2, 3} then 2 else game9 S

/-- **Exercise 18.AA.9** (MWG, p. 686). The worths: `v({i}) = 0`, `v({1,2}) = v({3,4}) = 0`,
`v({1,3}) = v({1,4}) = v({2,3}) = v({2,4}) = 1`, `v(S) = 1` for the three-player coalitions,
`v(I) = 2`. -/
theorem exercise_18_AA_9_table :
    (∀ i, game9 {i} = 0) ∧ game9 {0, 1} = 0 ∧ game9 {2, 3} = 0 ∧ game9 {0, 2} = 1 ∧
      game9 {0, 3} = 1 ∧ game9 {1, 2} = 1 ∧ game9 {1, 3} = 1 ∧
      (∀ S : Finset (Fin 4), S.card = 3 → game9 S = 1) ∧ game9 Finset.univ = 2 := by
  have h1 : ∀ i, v9Int {i} = 0 := by decide
  have h3 : ∀ S : Finset (Fin 4), S.card = 3 → v9Int S = 1 := by decide
  refine ⟨fun i => by simp [game9, h1 i], ?_, ?_, ?_, ?_, ?_, ?_,
    fun S hS => by simp [game9, h3 S hS], ?_⟩ <;>
    simp only [game9] <;> norm_cast

/-- **Exercise 18.AA.9** (MWG, p. 686). `v(∅) = 0`. -/
theorem game9_empty : game9 ∅ = 0 := by simp [game9, v9Int]

/-- **Exercise 18.AA.9(a)** (MWG, p. 686). The input endowments of Exercise 18.AA.9(a):
`ω₁ = ω₂ = (1, 0)`, `ω₃ = ω₄ = (0, 1)`. -/
def omega9 : Fin 4 → Fin 2 → ℝ := ![![1, 0], ![1, 0], ![0, 1], ![0, 1]]

/-- **Exercise 18.AA.9(a)** (MWG, p. 686). The game is generated by the technology `min{z₁, z₂}`
with `ω₁ = ω₂ = (1, 0)` and `ω₃ = ω₄ = (0, 1)`. -/
theorem exercise_18_AA_9a : game9 = inputGame (fun z => min (z 0) (z 1)) omega9 := by
  funext S
  simp only [inputGame, game9, v9Int, Finset.sum_apply]
  have e0 : ∀ i, omega9 i 0 = if i.val < 2 then 1 else 0 := by
    intro i; fin_cases i <;> simp [omega9]
  have e1 : ∀ i, omega9 i 1 = if ¬ i.val < 2 then 1 else 0 := by
    intro i; fin_cases i <;> simp [omega9]
  simp only [e0, e1, Finset.sum_boole]
  push_cast
  rfl

/-- **Exercise 18.AA.9(b)** (MWG, p. 686). The sum of `(α, α, 1 - α, 1 - α)` over a coalition. -/
theorem sum_alpha_alloc (α : ℝ) (S : Finset (Fin 4)) :
    ∑ i ∈ S, (![α, α, 1 - α, 1 - α] : Fin 4 → ℝ) i =
      α * (S.filter fun i => i.val < 2).card + (1 - α) * (S.filter fun i => ¬ i.val < 2).card := by
  have e : ∀ i, (![α, α, 1 - α, 1 - α] : Fin 4 → ℝ) i = if i.val < 2 then α else 1 - α := by
    intro i; fin_cases i <;> simp
  simp only [e]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **Exercise 18.AA.9(b)** (MWG, p. 686). `(α, α, 1 - α, 1 - α)` is in the core for `α ∈ [0, 1]`.
-/
theorem alpha_alloc_mem_core {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (![α, α, 1 - α, 1 - α] : Fin 4 → ℝ) ∈ tuCore game9 := by
  refine ⟨fun S _ => ?_, ?_⟩
  · rw [sum_alpha_alloc]
    simp only [game9, v9Int]
    push_cast
    set a : ℝ := ((S.filter fun i => i.val < 2).card : ℝ)
    set b : ℝ := ((S.filter fun i => ¬ i.val < 2).card : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left a b) h0,
      mul_le_mul_of_nonneg_left (min_le_right a b) (sub_nonneg.2 h1)]
  · rw [exercise_18_AA_9_table.2.2.2.2.2.2.2.2]
    simp [Fin.sum_univ_four]
    ring_nf; norm_num

/-- **Exercise 18.AA.9(b)** (MWG, p. 686). The core of the game is exactly the set of outcomes
`(α, α, 1 - α, 1 - α)` with `α ∈ [0, 1]` (the book asks to show that it contains them). -/
theorem exercise_18_AA_9b :
    tuCore game9 = {u | ∃ α ∈ Set.Icc (0 : ℝ) 1, u = ![α, α, 1 - α, 1 - α]} := by
  obtain ⟨hs, h01, -, h02, h03, h12, h13, -, hI⟩ := exercise_18_AA_9_table
  ext u
  constructor
  · rintro ⟨hS, htot⟩
    have a0 := hS {0} (by simp)
    have a2 := hS {2} (by simp)
    have b02 := hS {0, 2} (by simp)
    have b03 := hS {0, 3} (by simp)
    have b12 := hS {1, 2} (by simp)
    have b13 := hS {1, 3} (by simp)
    rw [hs] at a0 a2
    rw [h02] at b02
    rw [h03] at b03
    rw [h12] at b12
    rw [h13] at b13
    rw [hI, Fin.sum_univ_four] at htot
    simp at a0 a2 b02 b03 b12 b13
    refine ⟨u 0, ⟨by linarith, by linarith⟩, ?_⟩
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro ⟨α, ⟨h0, h1⟩, rfl⟩
    exact alpha_alloc_mem_core h0 h1

/-- **Exercise 18.AA.9(c)** (MWG, p. 686). After raising `v({1, 3, 4})` to `2`, the core consists
of the single point `(0, 0, 1, 1)`. -/
theorem exercise_18_AA_9c : tuCore game9mod = {![0, 0, 1, 1]} := by
  classical
  obtain ⟨hs, -, -, -, -, h12, h13, -, hI⟩ := exercise_18_AA_9_table
  have hne : ∀ S : Finset (Fin 4), S ≠ {0, 2, 3} → game9mod S = game9 S := by
    intro S hS; simp [game9mod, hS]
  have hm : game9mod {0, 2, 3} = 2 := by simp [game9mod]
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hS, htot⟩
    have a0 := hS {0} (by simp)
    have a1 := hS {1} (by simp)
    have b023 := hS {0, 2, 3} (by simp)
    have b12 := hS {1, 2} (by simp)
    have b13 := hS {1, 3} (by simp)
    rw [hne _ (by decide), hs] at a0 a1
    rw [hm] at b023
    rw [hne _ (by decide), h12] at b12
    rw [hne _ (by decide), h13] at b13
    rw [hne _ (by decide), hI, Fin.sum_univ_four] at htot
    simp at a0 a1 b023 b12 b13
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    have hcore := alpha_alloc_mem_core (α := 0) le_rfl zero_le_one
    have e : (![0, 0, 1 - 0, 1 - 0] : Fin 4 → ℝ) = ![0, 0, 1, 1] := by
      funext i; fin_cases i <;> simp
    rw [e] at hcore
    refine ⟨fun S hS => ?_, ?_⟩
    · by_cases h : S = {0, 2, 3}
      · subst h; rw [hm]; simp; norm_num
      · rw [hne S h]; exact hcore.1 S hS
    · rw [hne _ (by decide)]; exact hcore.2

/-- **Exercise 18.AA.9(c)** (MWG, p. 686), comparison: at the new core point player 1 gets `0`,
no more than at any point of the former core, where she could get anything in `[0, 1]`. -/
theorem exercise_18_AA_9c_compare :
    (∀ u ∈ tuCore game9mod, ∀ u' ∈ tuCore game9, u 0 ≤ u' 0) ∧
      (∀ u ∈ tuCore game9mod, u 0 = 0) ∧ ∃ u' ∈ tuCore game9, u' 0 = 1 := by
  refine ⟨fun u hu u' hu' => ?_, fun u hu => ?_, ?_⟩
  · rw [exercise_18_AA_9c, Set.mem_singleton_iff] at hu
    rw [exercise_18_AA_9b] at hu'
    obtain ⟨α, ⟨h0, _⟩, rfl⟩ := hu'
    subst hu; simpa using h0
  · rw [exercise_18_AA_9c, Set.mem_singleton_iff] at hu
    subst hu; simp
  · exact ⟨_, alpha_alloc_mem_core (α := 1) zero_le_one le_rfl, by simp⟩

/-- **Exercise 18.AA.9(d)** (MWG, p. 686). A permutation leaving the integer worths invariant leaves
the game invariant. -/
theorem game9_perm_invariant (σ : Equiv.Perm (Fin 4))
    (h : ∀ S : Finset (Fin 4), v9Int (S.map σ.toEmbedding) = v9Int S) :
    (fun S => game9 (S.map σ.toEmbedding)) = game9 := by
  funext S; simp only [game9]; rw [h S]

/-- **Exercise 18.AA.9(d)** (MWG, p. 686). The Shapley value is `(1/2, 1/2, 1/2, 1/2)`: the game
is invariant under exchanging players 1 and 2, and under exchanging the pairs `{1, 2}` and
`{3, 4}`, so all players get the same, and efficiency gives `2/4` each. -/
theorem exercise_18_AA_9d : WelfareBargaining.shapley game9 = fun _ => 1 / 2 := by
  have i01 := game9_perm_invariant (Equiv.swap 0 1) (by decide)
  have i23 := game9_perm_invariant (Equiv.swap 2 3) (by decide)
  have i02 := game9_perm_invariant (Equiv.swap 0 2 * Equiv.swap 1 3) (by decide)
  have s01 := WelfareBargaining.shapley_symmetric game9 (Equiv.swap 0 1) game9_empty 0
  have s23 := WelfareBargaining.shapley_symmetric game9 (Equiv.swap 2 3) game9_empty 2
  have s02 := WelfareBargaining.shapley_symmetric game9 (Equiv.swap 0 2 * Equiv.swap 1 3)
    game9_empty 0
  rw [i01] at s01
  rw [i23] at s23
  rw [i02] at s02
  simp only [Equiv.swap_apply_left, Equiv.Perm.mul_apply] at s01 s23 s02
  have e : (Equiv.swap (0 : Fin 4) 2) ((Equiv.swap (1 : Fin 4) 3) 0) = 2 := by decide
  rw [e] at s02
  have hsum := shapley_efficiency game9 game9_empty
  rw [Fin.sum_univ_four, exercise_18_AA_9_table.2.2.2.2.2.2.2.2] at hsum
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Exercise 18.AA.9(e)** (MWG, p. 686). After the change of part (c) the Shapley value is
`(7/12, 1/4, 7/12, 7/12)`: the change adds the unanimity game of `{1, 3, 4}` and subtracts that
of `I`, whose values are `1/3` on `{1, 3, 4}` and `1/4` for everyone. -/
theorem exercise_18_AA_9e :
    WelfareBargaining.shapley game9mod = ![7 / 12, 1 / 4, 7 / 12, 7 / 12] := by
  classical
  have hdec : game9mod = game9 + WelfareBargaining.unanimity {0, 2, 3} 1 +
      WelfareBargaining.unanimity Finset.univ (-1) := by
    have hsub : ∀ S : Finset (Fin 4), ({0, 2, 3} ⊆ S ↔ S = {0, 2, 3} ∨ S = Finset.univ) := by
      decide
    have hv : game9 {0, 2, 3} = 1 := exercise_18_AA_9_table.2.2.2.2.2.2.2.1 _ (by decide)
    have hne : ({0, 2, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide
    funext S
    simp only [game9mod, Pi.add_apply, WelfareBargaining.unanimity, Finset.univ_subset_iff]
    by_cases h1 : S = {0, 2, 3}
    · subst h1; simp [hv, hne]; norm_num
    · by_cases h2 : S = Finset.univ
      · subst h2; simp [hne.symm]
      · simp [h1, h2, (hsub S).not.2 (by tauto)]
  have hP := WelfareBargaining.shapley_pareto (n := 4)
  have hS := WelfareBargaining.shapley_symmetric (n := 4)
  have hD := WelfareBargaining.shapley_dummy (n := 4)
  have u1 := WelfareBargaining.exercise_22_F_4a hP hS hD {0, 2, 3} (by simp) 1
  have u2 := WelfareBargaining.exercise_22_F_4a hP hS hD Finset.univ Finset.univ_nonempty (-1)
  rw [hdec, WelfareBargaining.exercise_22_F_3a, WelfareBargaining.exercise_22_F_3a,
    exercise_18_AA_9d]
  funext i
  simp only [Pi.add_apply, u1, u2]
  have hc : ({0, 2, 3} : Finset (Fin 4)).card = 3 := by decide
  fin_cases i <;> simp [hc] <;> norm_num

/-- **Exercise 18.AA.9(e)** (MWG, p. 686), comparison: raising `v({1, 3, 4})` raises player 1's
Shapley value (by `1/12`) and lowers player 2's (by `1/4`), while player 1's core payoff falls to
`0` (from anything in `[0, 1]`). -/
theorem exercise_18_AA_9e_compare :
    WelfareBargaining.shapley game9mod 0 - WelfareBargaining.shapley game9 0 = 1 / 12 ∧
      WelfareBargaining.shapley game9mod 1 - WelfareBargaining.shapley game9 1 = -(1 / 4) ∧
      ∀ u ∈ tuCore game9mod, u 0 = 0 := by
  rw [exercise_18_AA_9e, exercise_18_AA_9d]
  refine ⟨by norm_num, by norm_num, exercise_18_AA_9c_compare.2.1⟩

/-! ### Exercise 18.AA.10: cost allocation -/

/-- **Exercise 18.AA.10** (MWG, p. 686). The cost game of two divisions using `x₁, x₂ ≥ 0` units
of space, with `C(X) = X^γ`: `c(S) = C(∑_{i∈S} xᵢ)`. -/
noncomputable def costGame (γ x₁ x₂ : ℝ) : WelfareBargaining.Game 2 :=
  fun S => (∑ i ∈ S, (![x₁, x₂] : Fin 2 → ℝ) i) ^ γ

/-- **Exercise 18.AA.10(a)** (MWG, p. 686). Division 1's Shapley cost share
`ψ₁ = (C(x₁ + x₂) + C(x₁) - C(x₂))/2`. -/
noncomputable def psi1 (γ x₁ x₂ : ℝ) : ℝ := ((x₁ + x₂) ^ γ + x₁ ^ γ - x₂ ^ γ) / 2

/-- **Exercise 18.AA.10(a)** (MWG, p. 686). Division 2's Shapley cost share
`ψ₂ = (C(x₁ + x₂) + C(x₂) - C(x₁))/2`. -/
noncomputable def psi2 (γ x₁ x₂ : ℝ) : ℝ := ((x₁ + x₂) ^ γ + x₂ ^ γ - x₁ ^ γ) / 2

/-- **Exercise 18.AA.10(a)** (MWG, p. 686). The Shapley value of the cost game (the two-player
egalitarian solution (18.AA.1)) is `(ψ₁, ψ₂)`, and it allocates the total cost exactly. -/
theorem exercise_18_AA_10a {γ : ℝ} (hγ : 0 < γ) (x₁ x₂ : ℝ) :
    WelfareBargaining.shapley (costGame γ x₁ x₂) = ![psi1 γ x₁ x₂, psi2 γ x₁ x₂] ∧
      psi1 γ x₁ x₂ + psi2 γ x₁ x₂ = (x₁ + x₂) ^ γ := by
  have h0 : costGame γ x₁ x₂ ∅ = 0 := by
    simp [costGame, Real.zero_rpow hγ.ne']
  have hf := formula_18_AA_1 (costGame γ x₁ x₂) h0
  rw [formula_18_AA_3 _ h0] at hf
  refine ⟨?_, by simp only [psi1, psi2]; ring⟩
  have a : WelfareBargaining.shapley (costGame γ x₁ x₂) 0 = psi1 γ x₁ x₂ := by
    rw [hf.1]; simp [costGame, psi1, Fin.sum_univ_two]; ring
  have b : WelfareBargaining.shapley (costGame γ x₁ x₂) 1 = psi2 γ x₁ x₂ := by
    rw [hf.2]; simp [costGame, psi2, Fin.sum_univ_two]; ring
  funext i
  fin_cases i
  · simpa using a
  · simpa using b

/-- **Exercise 18.AA.10(b)** (MWG, p. 686). The marginal cost charged to division 1 is
`∂ψ₁/∂x₁ = (C'(x₁ + x₂) + C'(x₁))/2` (and symmetrically for division 2), with
`C'(X) = γX^{γ-1}`, at `x₁, x₂ > 0`. -/
theorem exercise_18_AA_10b (γ : ℝ) {x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h₂ : 0 < x₂) :
    HasDerivAt (fun t => psi1 γ t x₂)
        ((γ * (x₁ + x₂) ^ (γ - 1) + γ * x₁ ^ (γ - 1)) / 2) x₁ ∧
      HasDerivAt (fun t => psi2 γ x₁ t)
        ((γ * (x₁ + x₂) ^ (γ - 1) + γ * x₂ ^ (γ - 1)) / 2) x₂ := by
  constructor
  · have hA := ((hasDerivAt_id x₁).add_const x₂).rpow_const (p := γ)
      (Or.inl (by simp; linarith))
    have hB := (hasDerivAt_id x₁).rpow_const (p := γ) (Or.inl h₁.ne')
    have := ((hA.add hB).sub_const (x₂ ^ γ)).div_const 2
    convert this using 1
    · funext t; simp only [psi1, Pi.add_apply, id]
    · simp
  · have hA := ((hasDerivAt_id x₂).const_add x₁).rpow_const (p := γ)
      (Or.inl (by simp; linarith))
    have hB := (hasDerivAt_id x₂).rpow_const (p := γ) (Or.inl h₂.ne')
    have := ((hA.add hB).sub_const (x₁ ^ γ)).div_const 2
    convert this using 1
    · funext t; simp only [psi2, Pi.add_apply, id]
    · simp

open Filter in
/-- **Exercise 18.AA.10(c)** (MWG, p. 686), correction: with `0 < γ < 1` the total profit
`α₁x₁ + α₂x₂ - C(x₁ + x₂)` is unbounded above on `ℝ²₊`. -/
theorem exercise_18_AA_10c_unbounded {γ : ℝ} (hγ1 : γ < 1) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁)
    (M : ℝ) : ∃ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ 0 ≤ x₂ ∧ M < α₁ * x₁ + α₂ * x₂ - (x₁ + x₂) ^ γ := by
  have hlim : Tendsto (fun t : ℝ => t ^ (-(1 - γ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hev := (hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < α₁ / 2))).and
    ((eventually_gt_atTop (2 * (|M| + 1) / α₁)).and (eventually_gt_atTop 0))
  obtain ⟨t, ht1, ht2, ht0⟩ := hev.exists
  refine ⟨t, 0, ht0.le, le_rfl, ?_⟩
  have hpow : t ^ γ = t * t ^ (-(1 - γ)) := by
    have h := Real.rpow_add ht0 1 (-(1 - γ))
    rw [Real.rpow_one, show (1 : ℝ) + -(1 - γ) = γ by ring] at h
    exact h
  have h3 : t * t ^ (-(1 - γ)) < t * (α₁ / 2) := mul_lt_mul_of_pos_left ht1 ht0
  have h4 : 2 * (|M| + 1) < α₁ * t := by
    rw [div_lt_iff₀ hα₁] at ht2; linarith
  simp only [mul_zero, add_zero]
  rw [hpow]
  nlinarith [le_abs_self M]

/-- **Exercise 18.AA.10(c)** (MWG, p. 686), correction: hence no efficient (profit-maximizing)
choice of overhead exists. -/
theorem exercise_18_AA_10c_no_max {γ : ℝ} (hγ1 : γ < 1) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) :
    ¬ ∃ y₁ y₂ : ℝ, 0 ≤ y₁ ∧ 0 ≤ y₂ ∧ ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → 0 ≤ x₂ →
      α₁ * x₁ + α₂ * x₂ - (x₁ + x₂) ^ γ ≤ α₁ * y₁ + α₂ * y₂ - (y₁ + y₂) ^ γ := by
  rintro ⟨y₁, y₂, -, -, hmax⟩
  obtain ⟨x₁, x₂, h₁, h₂, hlt⟩ :=
    exercise_18_AA_10c_unbounded hγ1 hα₁ (α₁ * y₁ + α₂ * y₂ - (y₁ + y₂) ^ γ) (α₂ := α₂)
  exact absurd (hmax x₁ x₂ h₁ h₂) (not_le.2 hlt)

/-- **Exercise 18.AA.10(c)** (MWG, p. 686). At any `x₁, x₂ > 0` the marginal cost charged to
division 1 under the Shapley rule exceeds the true marginal cost `C'(x₁ + x₂)`, so the division's
first-order condition `α₁ = ∂ψ₁/∂x₁` and the joint condition `α₁ = C'(x₁ + x₂)` cannot both
hold. -/
theorem exercise_18_AA_10c_foc {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {x₁ x₂ : ℝ}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (α₁ : ℝ) :
    γ * (x₁ + x₂) ^ (γ - 1) < (γ * (x₁ + x₂) ^ (γ - 1) + γ * x₁ ^ (γ - 1)) / 2 ∧
      ¬ (α₁ = (γ * (x₁ + x₂) ^ (γ - 1) + γ * x₁ ^ (γ - 1)) / 2 ∧
        α₁ = γ * (x₁ + x₂) ^ (γ - 1)) := by
  have h : (x₁ + x₂) ^ (γ - 1) < x₁ ^ (γ - 1) :=
    Real.rpow_lt_rpow_of_neg h₁ (by linarith) (by linarith)
  have h' := mul_lt_mul_of_pos_left h hγ0
  refine ⟨by linarith, fun ⟨e1, e2⟩ => by linarith⟩

/-- **Exercise 18.AA.10(d)** (MWG, p. 686). On `(0, ∞)`, a function whose derivative vanishes
everywhere is constant. -/
theorem const_of_hasDerivAt_zero_Ioi {f : ℝ → ℝ} (hf : ∀ t, 0 < t → HasDerivAt f 0 t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : f a = f b := by
  have key : ∀ a b : ℝ, 0 < a → a < b → f a = f b := by
    intro a b ha hab
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab
      (fun x hx => (hf x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hf x (ha.trans hx.1))
    have hba : b - a ≠ 0 := by linarith
    rw [eq_div_iff hba, zero_mul] at hc
    linarith
  rcases lt_trichotomy a b with h | rfl | h
  · exact key a b ha h
  · rfl
  · exact (key b a hb h).symm

/-- **Exercise 18.AA.10(d)** (MWG, p. 686), corrected statement: there is no distribution rule
`ψ₁ + ψ₂ = C(x₁ + x₂)` under which each division's own marginal charge `∂ψᵢ/∂xᵢ` equals the full
marginal cost `C'(x₁ + x₂)` on the open quadrant (which is what efficient decentralized choice for
all `α₁, α₂` would require): `ψ₂` would not depend on `x₁` nor `ψ₁` on `x₂`, making `C(x₁ + x₂)`
additively separable, against the strict concavity of `C`. -/
theorem exercise_18_AA_10d {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬ ∃ ψ₁ ψ₂ : ℝ → ℝ → ℝ,
      (∀ x₁ x₂, 0 < x₁ → 0 < x₂ → ψ₁ x₁ x₂ + ψ₂ x₁ x₂ = (x₁ + x₂) ^ γ) ∧
      (∀ x₁ x₂, 0 < x₁ → 0 < x₂ →
        HasDerivAt (fun t => ψ₁ t x₂) (γ * (x₁ + x₂) ^ (γ - 1)) x₁) ∧
      (∀ x₁ x₂, 0 < x₁ → 0 < x₂ →
        HasDerivAt (fun t => ψ₂ x₁ t) (γ * (x₁ + x₂) ^ (γ - 1)) x₂) := by
  rintro ⟨ψ₁, ψ₂, hsum, hd₁, hd₂⟩
  -- ψ₂ does not depend on x₁
  have hC : ∀ x₂ t, 0 < x₂ → 0 < t →
      HasDerivAt (fun s => (s + x₂) ^ γ) (γ * (t + x₂) ^ (γ - 1)) t := by
    intro x₂ t h₂ ht
    have := ((hasDerivAt_id t).add_const x₂).rpow_const (p := γ) (Or.inl (by simp; linarith))
    convert this using 1 <;> simp
  have hC' : ∀ x₁ t, 0 < x₁ → 0 < t →
      HasDerivAt (fun s => (x₁ + s) ^ γ) (γ * (x₁ + t) ^ (γ - 1)) t := by
    intro x₁ t h₁ ht
    have := ((hasDerivAt_id t).const_add x₁).rpow_const (p := γ) (Or.inl (by simp; linarith))
    convert this using 1 <;> simp
  have hψ₂ : ∀ x₂, 0 < x₂ → ∀ a b, 0 < a → 0 < b → ψ₂ a x₂ = ψ₂ b x₂ := by
    intro x₂ h₂ a b ha hb
    refine const_of_hasDerivAt_zero_Ioi (f := fun t => ψ₂ t x₂) (fun t ht => ?_) ha hb
    have hd := (hC x₂ t h₂ ht).sub (hd₁ t x₂ ht h₂)
    rw [sub_self] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    have := hsum s x₂ hs h₂
    simp only [Pi.sub_apply]
    linarith
  have hψ₁ : ∀ x₁, 0 < x₁ → ∀ a b, 0 < a → 0 < b → ψ₁ x₁ a = ψ₁ x₁ b := by
    intro x₁ h₁ a b ha hb
    refine const_of_hasDerivAt_zero_Ioi (f := fun t => ψ₁ x₁ t) (fun t ht => ?_) ha hb
    have hd := (hC' x₁ t h₁ ht).sub (hd₂ x₁ t h₁ ht)
    rw [sub_self] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    have := hsum x₁ s h₁ hs
    simp only [Pi.sub_apply]
    linarith
  -- separability: C(x₁ + x₂) = ψ₁(x₁, 1) + ψ₂(1, x₂)
  have hsep : ∀ x₁ x₂, 0 < x₁ → 0 < x₂ → (x₁ + x₂) ^ γ = ψ₁ x₁ 1 + ψ₂ 1 x₂ := by
    intro x₁ x₂ h₁ h₂
    rw [← hsum x₁ x₂ h₁ h₂, hψ₁ x₁ h₁ x₂ 1 h₂ one_pos, hψ₂ x₂ h₂ x₁ 1 h₁ one_pos]
  have e1 := hsep 1 1 one_pos one_pos
  have e2 := hsep 2 2 two_pos two_pos
  have e3 := hsep 1 2 one_pos two_pos
  have e4 := hsep 2 1 two_pos one_pos
  have hsc := (Real.strictConcaveOn_rpow hγ0 hγ1).2 (x := 2) (y := 4)
    (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2 (by norm_num)) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hsc
  norm_num at e1 e2 e3 e4 hsc
  linarith

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Closing Appendix A items: cross partials (Example 18.AA.8, Exercise 18.AA.7) and closedness
of `V(S)` (Example 18.AA.1) (MWG pp. 675, 683, 686)

Example 18.AA.8 assumes `∂²f(z)/∂z_h∂z_k ≥ 0` for all `z` and all `h, k` and Exercise 18.AA.7
asks to show that the production game `v(S) = f(∑_{i∈S} ωᵢ)` is convex. `ShapleyExamples` proves
the game convex under increasing differences (`exercise_18_AA_7`) and derives increasing
differences from the second-derivative condition only for `N = 1`. Here the step is proved for
every `N`:

* `c18_partial_mono`: if `f` is `C²` on an open set `U ⊇ ℝ^N₊` and every second partial
  `∂(∂f/∂z_k)/∂z_h` is nonnegative on `ℝ^N₊`, then every first partial `∂f/∂z_k` is nondecreasing
  along nonnegative directions in `ℝ^N₊` (mean value theorem along the segment `x + s a`);
* `c18_fderiv_mono`: hence `Df(y) d ≤ Df(y + a) d` for `y, a, d ≥ 0`;
* `example_18_AA_8_increasingDifferences`: hence `f` has increasing differences on `ℝ^N₊`
  (mean value theorem along `z + t (z' - z)`);
* `exercise_18_AA_7_crossPartials`: the production game is convex, under the book's hypothesis;
* `c18_product_crossPartials`: an instance, `f(z) = z₁z₂` on `ℝ²`
  (`exercise_18_AA_7_product`).

Example 18.AA.1 (p. 675) asserts that `V(S)` is a utility possibility set; closedness fails for
non-closed `Y` (`example_18_AA_1_not_closed` in `CoopGames`) and was proved there only for closed
`Y ⊆ -ℝ^L₊`. Here:

* `c18_cone_bounded`: in a closed cone `Y` with `Y ∩ ℝ^L₊ = {0}`, `{y ∈ Y : y ≥ -c}` is bounded
  (the negative-part sum `∑ min(y_l, 0)` has a negative maximum on `Y ∩ S^{L-1}`);
* `example_18_AA_1_closed_cone`, `example_18_AA_1_closed_crs`: `V(S)` is closed for every closed
  (convex) constant returns technology with no free production and continuous utilities;
  instance `example_18_AA_1_closed_halfPlane` (`Y = {y₁ + y₂ ≤ 0}`, not inside `-ℝ²₊`);
* `example_18_AA_1_free_production`: the hypothesis `Y ∩ ℝ^L₊ = {0}` cannot be dropped (`Y = ℝ₊`,
  `u(x) = 1 - 1/(1 + x)`, `V = {w < 1}`).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice

/-- **Example 18.AA.8** (MWG, p. 683). The partial derivative `∂f/∂z_k (y) = Df(y) e_k`. -/
noncomputable def c18Partial {N : ℕ} (f : (Fin N → ℝ) → ℝ) (k : Fin N) (y : Fin N → ℝ) : ℝ :=
  fderiv ℝ f y (Pi.single k 1)

/-- A vector is the sum of its coordinates times the unit vectors. -/
theorem c18_eq_sum_single {N : ℕ} (a : Fin N → ℝ) : a = ∑ h, a h • Pi.single h (1 : ℝ) := by
  ext l
  simp [Finset.sum_apply, Pi.single_apply]

/-- A linear functional in coordinates: `L a = ∑_h a_h L(e_h)`. -/
theorem c18_clm_apply_eq_sum {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) (a : Fin N → ℝ) :
    L a = ∑ h, a h * L (Pi.single h 1) := by
  conv_lhs => rw [c18_eq_sum_single a]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- A `C²` function on an open set has differentiable partial derivatives there. -/
theorem c18_partial_differentiableAt {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (k : Fin N) {y : Fin N → ℝ} (hy : y ∈ U) :
    DifferentiableAt ℝ (c18Partial f k) y := by
  have h2 : ContDiffAt ℝ 2 f y := hf.contDiffAt (hU.mem_nhds hy)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := h2.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)

/-- The derivative of `s ↦ F(x + s a)`. -/
theorem c18_hasDerivAt_line {N : ℕ} {F : (Fin N → ℝ) → ℝ} {x a : Fin N → ℝ} {s : ℝ}
    (hF : DifferentiableAt ℝ F (x + s • a)) :
    HasDerivAt (fun s : ℝ => F (x + s • a)) (fderiv ℝ F (x + s • a) a) s := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  exact hF.hasFDerivAt.comp_hasDerivAt s hγ

/-- Points `x + s a` with `x, a ≥ 0`, `s ≥ 0` are in the orthant. -/
theorem c18_line_mem {N : ℕ} {x a : Fin N → ℝ} (hx : x ∈ nonnegOrthant N)
    (ha : a ∈ nonnegOrthant N) {s : ℝ} (hs : 0 ≤ s) : x + s • a ∈ nonnegOrthant N := fun l => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (hx l) (mul_nonneg hs (ha l))

/-- **Example 18.AA.8** (MWG, p. 683), first step. If `f` is `C²` on an open `U ⊇ ℝ^N₊` and all
second partials `∂(∂f/∂z_k)/∂z_h` are nonnegative on `ℝ^N₊`, then each partial `∂f/∂z_k` is
nondecreasing along nonnegative directions: `∂f/∂z_k (x) ≤ ∂f/∂z_k (x + a)` for `x, a ≥ 0`. -/
theorem c18_partial_mono {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    (k : Fin N) {x a : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (ha : a ∈ nonnegOrthant N) :
    c18Partial f k x ≤ c18Partial f k (x + a) := by
  have hdiff : ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ (c18Partial f k) (x + s • a) := fun s hs =>
    c18_partial_differentiableAt hU hf k (hsub (c18_line_mem hx ha hs))
  have hmono : MonotoneOn (fun s : ℝ => c18Partial f k (x + s • a)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => fderiv ℝ (c18Partial f k) (x + s • a) a)
      (fun s hs => (c18_hasDerivAt_line (hdiff s hs)).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (c18_hasDerivAt_line (hdiff s (le_of_lt hs))).hasDerivWithinAt
    · rw [interior_Ici] at hs
      rw [c18_clm_apply_eq_sum]
      refine Finset.sum_nonneg fun h _ => ?_
      exact mul_nonneg (ha h) (hcross _ (c18_line_mem hx ha (le_of_lt hs)) h k)
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simpa using h

/-- **Example 18.AA.8** (MWG, p. 683), second step. Under the hypotheses of `c18_partial_mono`,
`Df(y) d ≤ Df(y + a) d` for `y, a, d ≥ 0`. -/
theorem c18_fderiv_mono {N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    {y a d : Fin N → ℝ} (hy : y ∈ nonnegOrthant N) (ha : a ∈ nonnegOrthant N)
    (hd : d ∈ nonnegOrthant N) : fderiv ℝ f y d ≤ fderiv ℝ f (y + a) d := by
  rw [c18_clm_apply_eq_sum (fderiv ℝ f y), c18_clm_apply_eq_sum (fderiv ℝ f (y + a))]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (c18_partial_mono hU hsub hf hcross k hy ha) (hd k)

/-- **Example 18.AA.8** (MWG, p. 683), the book's hypothesis. If `f` is `C²` on an open set
containing `ℝ^N₊` and `∂²f(z)/∂z_h∂z_k ≥ 0` for all `z ∈ ℝ^N₊` and all `h, k`, then `f` has
increasing differences on `ℝ^N₊`: `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'`,
`a ≥ 0`. -/
theorem example_18_AA_8_increasingDifferences {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1)) :
    IncreasingDifferences f := by
  intro z z' a hz hzz ha
  set d := z' - z with hd
  have hd0 : d ∈ nonnegOrthant N := fun l => by
    simp only [hd, Pi.sub_apply]; linarith [hzz l]
  have hfd : ∀ y ∈ nonnegOrthant N, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hsub hy))
  have hmem : ∀ s : ℝ, 0 ≤ s → z + s • d ∈ nonnegOrthant N := fun s hs => c18_line_mem hz hd0 hs
  have hmem' : ∀ s : ℝ, 0 ≤ s → (z + a) + s • d ∈ nonnegOrthant N := fun s hs =>
    c18_line_mem (fun l => add_nonneg (hz l) (ha l)) hd0 hs
  have hder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun s : ℝ => f ((z + a) + s • d) - f (z + s • d))
      (fderiv ℝ f ((z + a) + s • d) d - fderiv ℝ f (z + s • d) d) s := fun s hs =>
    (c18_hasDerivAt_line (hfd _ (hmem' s hs))).sub (c18_hasDerivAt_line (hfd _ (hmem s hs)))
  have hmono : MonotoneOn (fun s : ℝ => f ((z + a) + s • d) - f (z + s • d)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => fderiv ℝ f ((z + a) + s • d) d - fderiv ℝ f (z + s • d) d)
      (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (hder s (le_of_lt hs)).hasDerivWithinAt
    · rw [interior_Ici] at hs
      have e : (z + a) + s • d = (z + s • d) + a := by abel
      rw [e, sub_nonneg]
      exact c18_fderiv_mono hU hsub hf hcross (hmem s (le_of_lt hs)) ha hd0
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  have e1 : z + (1 : ℝ) • d = z' := by rw [one_smul, hd]; abel
  have e2 : (z + a) + (1 : ℝ) • d = z' + a := by rw [one_smul, hd]; abel
  simp only [zero_smul, add_zero] at h
  rw [e1, e2] at h
  exact h

/-- **Exercise 18.AA.7** (MWG, p. 686), with the hypothesis of Example 18.AA.8 as printed: if `f`
is `C²` on an open set containing `ℝ^N₊` with `∂²f/∂z_h∂z_k ≥ 0` on `ℝ^N₊` for all `h, k`, and
`ωᵢ ∈ ℝ^N₊`, then the production game `v(S) = f(∑_{i∈S} ωᵢ)` is convex. -/
theorem exercise_18_AA_7_crossPartials {n N : ℕ} {f : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hsub : nonnegOrthant N ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hcross : ∀ z ∈ nonnegOrthant N, ∀ h k : Fin N,
      0 ≤ fderiv ℝ (c18Partial f k) z (Pi.single h 1))
    {ω : Fin n → Fin N → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (inputGame f ω) :=
  exercise_18_AA_7 (example_18_AA_8_increasingDifferences hU hsub hf hcross) hω

/-- **Example 18.AA.8** (MWG, p. 683), an instance of the hypotheses: `f(z) = z₁z₂` on `ℝ²` is
`C²` (on the open set `ℝ²`) and every second partial `∂(∂f/∂z_k)/∂z_h` is `0` or `1`, so
nonnegative. -/
theorem c18_product_crossPartials :
    IsOpen (Set.univ : Set (Fin 2 → ℝ)) ∧ nonnegOrthant 2 ⊆ Set.univ ∧
      ContDiffOn ℝ 2 (fun z : Fin 2 → ℝ => z 0 * z 1) Set.univ ∧
      ∀ z ∈ nonnegOrthant 2, ∀ h k : Fin 2,
        0 ≤ fderiv ℝ (c18Partial (fun z : Fin 2 → ℝ => z 0 * z 1) k) z (Pi.single h 1) := by
  refine ⟨isOpen_univ, Set.subset_univ _, ?_, fun z _ h k => ?_⟩
  · exact ((contDiff_apply ℝ ℝ (0 : Fin 2)).mul (contDiff_apply ℝ ℝ (1 : Fin 2))).contDiffOn
  · have hf : ∀ y : Fin 2 → ℝ, fderiv ℝ (fun z : Fin 2 → ℝ => z 0 * z 1) y =
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
          y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 := fun y =>
      ((hasFDerivAt_apply (0 : Fin 2) y).mul (hasFDerivAt_apply (1 : Fin 2) y)).fderiv
    set L : (Fin 2 → ℝ) →L[ℝ] ℝ := Pi.single (M := fun _ : Fin 2 => ℝ) k 1 1 •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      Pi.single (M := fun _ : Fin 2 => ℝ) k 1 0 •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 with hL
    have hP : c18Partial (fun z : Fin 2 → ℝ => z 0 * z 1) k = L := by
      funext y
      simp only [c18Partial, hf, hL, FunLike.coe_add, FunLike.coe_smul,
        Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [hP, L.fderiv]
    simp only [hL, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hs : ∀ (j l : Fin 2), 0 ≤ Pi.single (M := fun _ : Fin 2 => ℝ) j 1 l := fun j l => by
      simp only [Pi.single_apply]; split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg (hs _ _) (hs _ _)) (mul_nonneg (hs _ _) (hs _ _))

/-- **Exercise 18.AA.7** (MWG, p. 686), instance: the production game of `f(z) = z₁z₂` with any
endowments `ωᵢ ∈ ℝ²₊` is convex, by `exercise_18_AA_7_crossPartials`. -/
theorem exercise_18_AA_7_product {n : ℕ} {ω : Fin n → Fin 2 → ℝ} (hω : ∀ i, 0 ≤ ω i) :
    IsConvexGame (inputGame (fun z : Fin 2 → ℝ => z 0 * z 1) ω) :=
  exercise_18_AA_7_crossPartials c18_product_crossPartials.1 c18_product_crossPartials.2.1
    c18_product_crossPartials.2.2.1 c18_product_crossPartials.2.2.2 hω

/-! ### Example 18.AA.1: closedness of `V(S)` for a closed cone with no free production -/

/-- The sum of the negative parts `∑_l min(y_l, 0)` of a vector. -/
noncomputable def c18NegSum {L : ℕ} (y : Fin L → ℝ) : ℝ := ∑ l, min (y l) 0

theorem c18NegSum_continuous {L : ℕ} : Continuous (c18NegSum (L := L)) :=
  continuous_finsetSum _ fun l _ => (continuous_apply l).min continuous_const

theorem c18NegSum_smul {L : ℕ} {t : ℝ} (ht : 0 ≤ t) (y : Fin L → ℝ) :
    c18NegSum (t • y) = t * c18NegSum y := by
  simp only [c18NegSum, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_zero t, ← mul_min_of_nonneg _ _ ht, mul_zero]

/-- **Example 18.AA.1** (MWG, p. 675), boundedness lemma. If `Y` is a closed cone with
`Y ∩ ℝ^L₊ = {0}` (no free production), then for every `c` the vectors `y ∈ Y` with `y ≥ -c` are
bounded. -/
theorem c18_cone_bounded {L : ℕ} {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y)
    (hcone : ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0) (c : Fin L → ℝ) :
    ∃ B : ℝ, ∀ y ∈ Y, (∀ l, -c l ≤ y l) → ‖y‖ ≤ B := by
  set K := Y ∩ Metric.sphere (0 : Fin L → ℝ) 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left hYc
  have hnorm : ∀ y ∈ Y, y ≠ 0 → ‖y‖⁻¹ • y ∈ K := fun y hy hne =>
    ⟨hcone y hy _ (inv_nonneg.2 (norm_nonneg y)), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]⟩
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, fun y hy _ => ?_⟩
    by_contra hlt
    have hne : y ≠ 0 := fun h => hlt (by simp [h])
    have := hnorm y hy hne
    rw [hKe] at this
    exact this
  obtain ⟨y₀, hy₀K, hmax⟩ := hKc.exists_isMaxOn hKne c18NegSum_continuous.continuousOn
  have hy₀ne : y₀ ≠ 0 := fun h => by
    have := hy₀K.2
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  have hm : c18NegSum y₀ < 0 := by
    have hnot : ¬ y₀ ∈ nonnegOrthant L := fun h => hy₀ne (hpos y₀ hy₀K.1 h)
    simp only [nonnegOrthant, Set.mem_ofPred_eq, not_forall, not_le] at hnot
    obtain ⟨l, hl⟩ := hnot
    have h1 : ∑ l', min (y₀ l') 0 ≤ min (y₀ l) 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
      have : ∑ l' ∈ Finset.univ.erase l, min (y₀ l') 0 ≤ 0 :=
        Finset.sum_nonpos fun l' _ => min_le_right _ _
      linarith
    simp only [c18NegSum]
    linarith [min_eq_left hl.le, h1]
  set C : ℝ := -∑ l, min (-c l) 0 with hC
  refine ⟨C / (-c18NegSum y₀), fun y hy hyc => ?_⟩
  rcases eq_or_ne y 0 with rfl | hne
  · rw [norm_zero]
    refine div_nonneg ?_ (by linarith)
    rw [hC, neg_nonneg]
    exact Finset.sum_nonpos fun l _ => min_le_right _ _
  have h1 : c18NegSum (‖y‖⁻¹ • y) ≤ c18NegSum y₀ := hmax (hnorm y hy hne)
  rw [c18NegSum_smul (inv_nonneg.2 (norm_nonneg y))] at h1
  have h2 : -C ≤ c18NegSum y := by
    rw [hC, neg_neg]
    exact Finset.sum_le_sum fun l _ => min_le_min_right 0 (hyc l)
  have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hne
  have h3 : c18NegSum y ≤ ‖y‖ * c18NegSum y₀ := by
    have := mul_le_mul_of_nonneg_left h1 hnpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at this
  rw [le_div_iff₀ (by linarith)]
  nlinarith

open Filter Topology in
/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness for a general technology: if `Y` is a
closed cone with no free production (`Y ∩ ℝ^L₊ = {0}`) and the utilities are continuous on
`ℝ^L₊`, then every `V(S)` is closed. This extends `example_18_AA_1_closed` (closed
`Y ⊆ -ℝ^L₊`); without closedness the claim fails (`example_18_AA_1_not_closed`), and without
`Y ∩ ℝ^L₊ = {0}` too (`example_18_AA_1_free_production`). Convexity of `Y` and `ωᵢ ≥ 0` are not
needed. -/
theorem example_18_AA_1_closed_cone {n L : ℕ} {u : Fin n → (Fin L → ℝ) → ℝ}
    {ω : Fin n → Fin L → ℝ} {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y)
    (hcone : ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) := by
  classical
  obtain ⟨B, hB⟩ := c18_cone_bounded hYc hcone hpos (∑ j ∈ S, ω j)
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨ws, hws, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose x hx hy hux using hws
  choose y hyY hsum using hy
  have hyc : ∀ k, ∀ l, -(∑ j ∈ S, ω j) l ≤ y k l := fun k l => by
    have h2 := congrFun (hsum k) l
    have h4 : 0 ≤ ∑ j ∈ S, x k j l := Finset.sum_nonneg fun j hj => hx k j hj l
    simp only [Finset.sum_apply, Pi.add_apply] at h2 ⊢
    linarith
  have hyB : ∀ k l, y k l ≤ B := fun k l =>
    (le_abs_self _).trans ((norm_le_pi_norm (y k) l).trans (hB _ (hyY k) (hyc k)))
  set M : Fin n → Fin L → ℝ := fun _ l => (∑ j ∈ S, ω j) l + B with hM
  set xt : ℕ → Fin n → Fin L → ℝ := fun k i => if i ∈ S then x k i else 0 with hxt
  have hxtS : ∀ k, ∀ i ∈ S, xt k i = x k i := fun k i hi => by simp [hxt, hi]
  have hbox : ∀ k, xt k ∈ Set.Icc (0 : Fin n → Fin L → ℝ) M := by
    intro k
    refine ⟨fun i l => ?_, fun i l => ?_⟩
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]; exact hx k i hi l
      · simp [hxt, hi]
    · have h2 := congrFun (hsum k) l
      simp only [Finset.sum_apply, Pi.add_apply] at h2
      have h3 := hyB k l
      have h5 := hyc k l
      simp only [Finset.sum_apply] at h5
      by_cases hi : i ∈ S
      · rw [hxtS k i hi]
        have h1 : x k i l ≤ ∑ j ∈ S, x k j l :=
          Finset.single_le_sum (f := fun j => x k j l) (fun j hj => hx k j hj l) hi
        simp only [hM, Finset.sum_apply]
        linarith
      · simp only [hxt, hi, ↓reduceIte, hM, Pi.zero_apply, Finset.sum_apply]
        linarith
  obtain ⟨xb, hxb, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hbox
  have hcoord : ∀ i, Tendsto (fun k => xt (φ k) i) atTop (𝓝 (xb i)) :=
    fun i => tendsto_pi_nhds.1 hconv i
  have hxbnn : ∀ i, xb i ∈ nonnegOrthant L := fun i l => hxb.1 i l
  refine ⟨xb, fun i _ => hxbnn i, ⟨∑ i ∈ S, xb i - ∑ i ∈ S, ω i, ?_, by abel⟩, fun i hi => ?_⟩
  · refine hYc.mem_of_tendsto (f := fun k => y (φ k)) (b := atTop) ?_
      (Eventually.of_forall fun k => hyY _)
    have hy' : (fun k => y (φ k)) = fun k => ∑ i ∈ S, xt (φ k) i - ∑ i ∈ S, ω i := by
      funext k
      rw [Finset.sum_congr rfl fun i hi => hxtS (φ k) i hi, hsum (φ k)]
      abel
    rw [hy']
    exact (tendsto_finsetSum S fun i _ => hcoord i).sub tendsto_const_nhds
  · have hwl : Tendsto (fun k => ws (φ k) i) atTop (𝓝 (w i)) :=
      (tendsto_pi_nhds.1 hlim i).comp hφ.tendsto_atTop
    have hul : Tendsto (fun k => u i (xt (φ k) i)) atTop (𝓝 (u i (xb i))) :=
      ((hu i) (xb i) (hxbnn i)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hcoord i, Eventually.of_forall fun k l =>
          (hbox (φ k)).1 i l⟩)
    refine le_of_tendsto_of_tendsto hwl hul (Eventually.of_forall fun k => ?_)
    simp only [hxtS (φ k) i hi]
    exact hux (φ k) i hi

/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness under the book's hypotheses on `Y`: a
closed convex constant returns technology with no free production. -/
theorem example_18_AA_1_closed_crs {n L : ℕ} {u : Fin n → (Fin L → ℝ) → ℝ}
    {ω : Fin n → Fin L → ℝ} {Y : Set (Fin L → ℝ)} (hY : IsCRSTechnology Y) (hYc : IsClosed Y)
    (hpos : ∀ y ∈ Y, y ∈ nonnegOrthant L → y = 0)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) :=
  example_18_AA_1_closed_cone hYc hY.2.2 hpos hu S

/-- **Example 18.AA.1**, an instance beyond `Y ⊆ -ℝ^L₊`: the half-plane `{y : y₁ + y₂ ≤ 0}`
(which contains `(1, -1)`). -/
def c18HalfPlane : Set (Fin 2 → ℝ) := {y | y 0 + y 1 ≤ 0}

/-- **Example 18.AA.1**, instance: the half-plane technology is a closed convex constant returns
technology with no free production, not contained in `-ℝ²₊`. -/
theorem c18HalfPlane_hyp : IsCRSTechnology c18HalfPlane ∧ IsClosed c18HalfPlane ∧
    (∀ y ∈ c18HalfPlane, y ∈ nonnegOrthant 2 → y = 0) ∧
      ¬ c18HalfPlane ⊆ MWG.WelfareTheorems.nonposOrthant 2 := by
  refine ⟨⟨?_, ?_, fun y hy t ht => ?_⟩, ?_, fun y hy hy0 => ?_, fun h => ?_⟩
  · intro a ha b hb s t hs ht _
    simp only [c18HalfPlane, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ -(a 0 + a 1)),
      mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(b 0 + b 1))]
  · simp [c18HalfPlane]
  · simp only [c18HalfPlane, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(y 0 + y 1))]
  · exact isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const
  · simp only [c18HalfPlane, Set.mem_ofPred_eq] at hy
    have h0 := hy0 0
    have h1 := hy0 1
    funext l
    fin_cases l <;> simp <;> linarith
  · have := h (show (![1, -1] : Fin 2 → ℝ) ∈ c18HalfPlane by simp [c18HalfPlane]) 0
    norm_num at this

/-- **Example 18.AA.1**, instance of `example_18_AA_1_closed_crs`: with the half-plane technology,
`V(S)` is closed for any continuous utilities, e.g. `u(x) = x₁ + x₂`. -/
theorem example_18_AA_1_closed_halfPlane {n : ℕ} (ω : Fin n → Fin 2 → ℝ) (S : Finset (Fin n)) :
    IsClosed (econGame (fun _ x => x 0 + x 1) ω c18HalfPlane S) :=
  example_18_AA_1_closed_crs c18HalfPlane_hyp.1 c18HalfPlane_hyp.2.1 c18HalfPlane_hyp.2.2.1
    (fun _ => ((continuous_apply 0).add (continuous_apply 1)).continuousOn) S

/-- **Example 18.AA.1** (MWG, p. 675), the hypothesis `Y ∩ ℝ^L₊ = {0}` cannot be dropped: with
`L = 1`, the closed convex cone `Y = ℝ₊` (free production), one consumer with `ω = 0` and the
continuous, strictly increasing, concave utility `u(x) = 1 - 1/(1 + x)`, `V(I) = {w : w < 1}`,
which is not closed. -/
theorem example_18_AA_1_free_production :
    IsCRSTechnology (nonnegOrthant 1) ∧ IsClosed (nonnegOrthant 1) ∧
      ConcaveOn ℝ (nonnegOrthant 1) (fun x : Fin 1 → ℝ => 1 - 1 / (1 + x 0)) ∧
      StrictMonoOn (fun t : ℝ => 1 - 1 / (1 + t)) (Set.Ici 0) ∧
      ContinuousOn (fun x : Fin 1 → ℝ => 1 - 1 / (1 + x 0)) (nonnegOrthant 1) ∧
      econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0) (nonnegOrthant 1)
        Finset.univ = {w | w 0 < 1} ∧
      ¬ IsClosed (econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0)
        (nonnegOrthant 1) Finset.univ) := by
  have hV : econGame (n := 1) (fun _ x => 1 - 1 / (1 + x 0)) (fun _ => 0) (nonnegOrthant 1)
      Finset.univ = {w | w 0 < 1} := by
    ext w
    simp only [econGame, Finset.mem_univ, true_implies, Fin.sum_univ_one, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, -, hu⟩
      have h0 := hx 0 0
      have hw := hu 0
      have : 0 < 1 / (1 + x 0 0) := by positivity
      linarith
    · intro hw
      set t : ℝ := max (1 / (1 - w 0) - 1) 0 with ht
      have h1w : 0 < 1 - w 0 := by linarith
      refine ⟨fun _ => fun _ => t, fun _ _ => le_max_right _ _, ⟨fun _ => t, fun _ =>
        le_max_right _ _, by simp⟩, fun j => ?_⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only
      have hge : 1 / (1 - w 0) ≤ 1 + t := by
        rw [ht]; linarith [le_max_left (1 / (1 - w 0) - 1) 0]
      have hpos : 0 < 1 + t := by linarith [le_max_right (1 / (1 - w 0) - 1) 0]
      have : 1 / (1 + t) ≤ 1 - w 0 := by
        rw [div_le_iff₀ hpos]
        rw [div_le_iff₀ h1w] at hge
        linarith
      linarith
  refine ⟨⟨convex_nonnegOrthant 1, fun _ => le_rfl, fun y hy t ht l => ?_⟩,
    ?_, ?_, ?_, ?_, hV, fun hcl => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht (hy l)
  · have e : nonnegOrthant 1 = ⋂ l : Fin 1, {y : Fin 1 → ℝ | 0 ≤ y l} := by
      ext y; simp [nonnegOrthant]
    rw [e]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  · refine ⟨convex_nonnegOrthant 1, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hx0 := hx 0
    have hy0 := hy 0
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h1 : 0 < 1 + x 0 := by linarith
    have h2 : 0 < 1 + y 0 := by linarith
    have h3 : 0 < 1 + (a * x 0 + (1 - a) * y 0) := by nlinarith
    have key : 1 / (1 + (a * x 0 + (1 - a) * y 0)) ≤ a / (1 + x 0) + (1 - a) / (1 + y 0) := by
      rw [div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀ h3 (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]
    have e : a * (1 - 1 / (1 + x 0)) + (1 - a) * (1 - 1 / (1 + y 0)) =
        1 - (a / (1 + x 0) + (1 - a) / (1 + y 0)) := by ring
    rw [e]
    linarith
  · intro s hs t htt hst
    simp only [Set.mem_Ici] at hs htt
    have h1 : 0 < 1 + s := by linarith
    have : 1 / (1 + t) < 1 / (1 + s) := one_div_lt_one_div_of_lt h1 (by linarith)
    linarith
  · refine ContinuousOn.sub continuousOn_const (ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuous_apply 0).continuousOn) fun x hx => ?_)
    have := hx 0
    linarith
  · rw [hV] at hcl
    have hc : IsClosed (Set.Iio (1 : ℝ)) := by
      have : Set.Iio (1 : ℝ) = (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' {w | w 0 < 1} := by
        ext t; simp
      rw [this]; exact hcl.preimage (continuous_pi fun _ => continuous_id)
    have := hc.closure_eq
    rw [closure_Iio] at this
    have h1 : (1 : ℝ) ∈ Set.Iic (1 : ℝ) := Set.mem_Iic.2 le_rfl
    rw [this] at h1
    exact lt_irrefl _ (Set.mem_Iio.1 h1)

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The hypergeometric-average formula for the Shapley value (MWG Section 18.E, p. 673)

MWG (p. 673) describe the Shapley value of an economy with type profile `(I₁, ..., I_H)` as an
average of marginal utilities `Δ_h v(I')` over profiles `I' ≤ I`, with weight `1/I` (the sample
size) times the probability of the profile `I'` when sampling `|I'|` consumers from the
population. Here players are `i : Fin n` with types `τ i`, and the game depends only on the type
profile of a coalition, `v(S) = w(I(S))` (`c18TypeGame`).

* `c18_card_profile_fiber`: the number of subsets `R ⊆ A` with type profile `m` is
  `∏_k C(I_k(A), m_k)` (a bijection with families of subsets of the type classes);
  `c18_sum_powerset_profile`: hence `∑_{R ⊆ A} G(I(R)) = ∑_m ∏_k C(I_k(A), m_k) G(m)`.
* `c18_shapley_types`, `c18_shapley_hypergeometric`: the exact formula. For a player `i` of type
  `h`, with `J = I - e_h` the profile of the other players,
  `Sh_i = ∑_{m ≤ J} (1/I) · [∏_k C(J_k, m_k) / C(I - 1, |m|)] · (w(m + e_h) - w(m))`:
  the sample size `|m|` of the OTHER players is uniform on `{0, ..., I - 1}` and, given the size,
  the profile is hypergeometric from the population `J` (not `I`), and the marginal utility is
  that of adding a type-`h` consumer to the sample.
* `c18_hypergeometric_weights_sum`: the weights sum to `1`.
* `c18_book_formula_counterexample` (correction): read literally (weights `1/I` times the
  hypergeometric probability of `I'` in samples from the population `I`, marginal utility
  `Δ_h v(I') = v(I') - v(I' - e_h)` for `I'_h ≥ 1`), the formula is not the Shapley value: with
  one consumer of each of two types and the additive `v(I') = I'₁ + I'₂` the Shapley value of type
  `1` is `1` and the literal formula gives `3/4`. The printed formula is the large-economy
  approximation of the exact one.

The value equivalence theorem itself (p. 673, "too advanced to be given here") is not formalised.
-/

namespace MWG.CoreFoundations

variable {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}

/-- **Section 18.E** (MWG, p. 673). The type profile `I(R)` of a set of consumers `R`:
`I_k(R) = #{i ∈ R : τ i = k}`. -/
def c18Profile (τ : Fin n → H) (R : Finset (Fin n)) : H → ℕ :=
  fun k => (R.filter fun i => τ i = k).card

/-- **Section 18.E** (MWG, p. 673). The TU game of an economy with types: the worth of a
coalition depends only on its type profile, `v(S) = w(I(S))`. -/
def c18TypeGame (w : (H → ℕ) → ℝ) (τ : Fin n → H) : WelfareBargaining.Game n :=
  fun S => w (c18Profile τ S)

/-- The profiles `m ≤ I(A)`, as a finite set. -/
def c18Box (c : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun k => Finset.range (c k + 1)

/-- **Section 18.E** (MWG, p. 673). The number of subsets `R ⊆ A` with type profile `m` is
`∏_k C(I_k(A), m_k)`. -/
theorem c18_card_profile_fiber (τ : Fin n → H) (A : Finset (Fin n)) (m : H → ℕ) :
    (A.powerset.filter fun R => c18Profile τ R = m).card =
      ∏ k, (c18Profile τ A k).choose (m k) := by
  have hpi : (Fintype.piFinset fun k =>
      (A.filter fun i => τ i = k).powersetCard (m k)).card =
      ∏ k, (c18Profile τ A k).choose (m k) := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun k _ => Finset.card_powersetCard _ _
  rw [← hpi]
  have key : ∀ F : H → Finset (Fin n), (∀ k, F k ⊆ A.filter fun i => τ i = k) →
      ∀ k, (Finset.univ.biUnion F).filter (fun i => τ i = k) = F k := by
    intro F hF k
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, hj⟩, hx⟩
      have := (Finset.mem_filter.1 (hF j hj)).2
      rw [this] at hx
      subst hx
      exact hj
    · intro hx
      exact ⟨⟨k, hx⟩, (Finset.mem_filter.1 (hF k hx)).2⟩
  refine Finset.card_bij' (fun R _ => fun k => R.filter fun i => τ i = k)
    (fun F _ => Finset.univ.biUnion F) (fun R hR => ?_) (fun F hF => ?_) (fun R _ => ?_)
    (fun F hF => ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset] at hR
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset_filter _ hR.1, congrFun hR.2 k⟩
  · rw [Fintype.mem_piFinset] at hF
    have hF' : ∀ k, F k ⊆ A.filter fun i => τ i = k := fun k =>
      (Finset.mem_powersetCard.1 (hF k)).1
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.biUnion_subset.2 fun k _ => (hF' k).trans (Finset.filter_subset _ _), ?_⟩
    funext k
    simp only [c18Profile]
    rw [key F hF' k]
    exact (Finset.mem_powersetCard.1 (hF k)).2
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨τ x, hx, rfl⟩⟩
  · rw [Fintype.mem_piFinset] at hF
    funext k
    exact key F (fun k => (Finset.mem_powersetCard.1 (hF k)).1) k

omit [Fintype H] in
/-- The profile of a subset is bounded by the profile of the set. -/
theorem c18_profile_mono (τ : Fin n → H) {R A : Finset (Fin n)} (h : R ⊆ A) (k : H) :
    c18Profile τ R k ≤ c18Profile τ A k :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Section 18.E** (MWG, p. 673). Summing a function of the type profile over the subsets of
`A`: `∑_{R ⊆ A} G(I(R)) = ∑_{m ≤ I(A)} ∏_k C(I_k(A), m_k) G(m)`. -/
theorem c18_sum_powerset_profile (τ : Fin n → H) (A : Finset (Fin n)) (G : (H → ℕ) → ℝ) :
    ∑ R ∈ A.powerset, G (c18Profile τ R) =
      ∑ m ∈ c18Box (c18Profile τ A), (∏ k, ((c18Profile τ A k).choose (m k) : ℝ)) * G m := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := A.powerset) (t := c18Box (c18Profile τ A))
    (g := c18Profile τ)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_congr rfl fun R hR => by rw [(Finset.mem_filter.1 hR).2], Finset.sum_const,
      c18_card_profile_fiber, nsmul_eq_mul]
    push_cast
    rfl
  · intro R hR
    rw [c18Box, Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact c18_profile_mono τ (Finset.mem_powerset.1 hR) k

omit [Fintype H] in
/-- Adding a consumer `i ∉ R` adds `e_{τ i}` to the profile. -/
theorem c18_profile_insert (τ : Fin n → H) {R : Finset (Fin n)} {i : Fin n} (hi : i ∉ R) :
    c18Profile τ (insert i R) = c18Profile τ R + Pi.single (τ i) 1 := by
  funext k
  simp only [c18Profile, Finset.filter_insert, Pi.add_apply, Pi.single_apply]
  by_cases h : τ i = k
  · simp only [h, ↓reduceIte]
    exact Finset.card_insert_of_notMem fun hm => hi (Finset.mem_filter.1 hm).1
  · simp only [h, Ne.symm h, ↓reduceIte, add_zero]

/-- The size of a set is the sum of its profile. -/
theorem c18_card_eq_sum_profile (τ : Fin n → H) (R : Finset (Fin n)) :
    R.card = ∑ k, c18Profile τ R k :=
  Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _

omit [Fintype H] in
/-- The profile of the other players: `I(I \ {i}) = I - e_{τ i}`. -/
theorem c18_profile_erase (τ : Fin n → H) (i : Fin n) :
    c18Profile τ (Finset.univ.erase i) = c18Profile τ Finset.univ - Pi.single (τ i) 1 := by
  have h := c18_profile_insert τ (Finset.notMem_erase i Finset.univ)
  rw [Finset.insert_erase (Finset.mem_univ i)] at h
  rw [h]
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, add_tsub_cancel_right]

/-- The Shapley value does not depend on `v(∅)`. -/
theorem c18_shapley_sub_const (v : WelfareBargaining.Game n) (c : ℝ) (i : Fin n) :
    WelfareBargaining.shapley (fun S => v S - c) i = WelfareBargaining.shapley v i := by
  simp only [WelfareBargaining.shapley, WelfareBargaining.margContrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype H] in
/-- **Section 18.E** (MWG, p. 673), the Shapley value of an economy with types as a sum over the
sets `R` of other players: `Sh_i = ∑_{R ⊆ I \ {i}} (I - 1 - |R|)! |R|! / I! · (w(I(R) + e_{τ i}) -
w(I(R)))` (from (18.AA.4)). -/
theorem c18_shapley_types (w : (H → ℕ) → ℝ) (τ : Fin n → H) (i : Fin n) :
    WelfareBargaining.shapley (c18TypeGame w τ) i =
      ∑ R ∈ (Finset.univ.erase i).powerset,
        ((n - 1 - R.card).factorial * R.card.factorial / n.factorial : ℝ) *
          (w (c18Profile τ R + Pi.single (τ i) 1) - w (c18Profile τ R)) := by
  classical
  have h0 : c18Profile τ (∅ : Finset (Fin n)) = 0 := by
    funext k; simp [c18Profile]
  have hshift : WelfareBargaining.shapley (c18TypeGame w τ) i =
      WelfareBargaining.shapley (c18TypeGame (fun m => w m - w 0) τ) i :=
    (c18_shapley_sub_const (c18TypeGame w τ) (w 0) i).symm
  rw [hshift, ← formula_18_AA_4 _ (by simp [c18TypeGame, h0])]
  unfold subsetFormula
  rw [Finset.card_univ, Fintype.card_fin]
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i),
    Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)]
  rw [Finset.sum_eq_zero fun T hT => by
    have hT' : i ∉ T := fun h => Finset.notMem_erase i Finset.univ (Finset.mem_powerset.1 hT h)
    simp only [hT', ↓reduceIte], zero_add]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hiR : i ∉ R := fun h => Finset.notMem_erase i Finset.univ (Finset.mem_powerset.1 hR h)
  have e : n - (R.card + 1) = n - 1 - R.card := by omega
  simp only [Finset.mem_insert_self, ↓reduceIte]
  rw [Finset.card_insert_of_notMem hiR, Finset.erase_insert hiR, Nat.add_sub_cancel, e,
    c18TypeGame, c18TypeGame, c18_profile_insert τ hiR]
  ring

/-- **Section 18.E** (MWG, p. 673), the hypergeometric-average formula, corrected. For a player
`i` of type `h = τ i`, with `J = I - e_h` the profile of the other players
(`c18_profile_erase`),
`Sh_i = ∑_{m ≤ J} (1/I) · [∏_k C(J_k, m_k) / C(I - 1, |m|)] · (w(m + e_h) - w(m))`: the weight is
`1/I` for the sample size `|m| ∈ {0, ..., I - 1}` times the hypergeometric probability of the
profile `m` in a sample of that size from the other players. -/
theorem c18_shapley_hypergeometric (w : (H → ℕ) → ℝ) (τ : Fin n → H) (i : Fin n) :
    WelfareBargaining.shapley (c18TypeGame w τ) i =
      ∑ m ∈ c18Box (c18Profile τ (Finset.univ.erase i)),
        (1 / n : ℝ) * ((∏ k, ((c18Profile τ (Finset.univ.erase i) k).choose (m k) : ℝ)) /
          ((n - 1).choose (∑ k, m k) : ℝ)) * (w (m + Pi.single (τ i) 1) - w m) := by
  rw [c18_shapley_types]
  simp_rw [c18_card_eq_sum_profile τ]
  refine (c18_sum_powerset_profile τ (Finset.univ.erase i) (fun m =>
    ((n - 1 - ∑ k, m k).factorial * (∑ k, m k).factorial / n.factorial : ℝ) *
      (w (m + Pi.single (τ i) 1) - w m))).trans ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  have hn : 0 < n := Fin.pos i
  have hJ : ∑ k, c18Profile τ (Finset.univ.erase i) k = n - 1 := by
    rw [← c18_card_eq_sum_profile, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  have hs : ∑ k, m k ≤ n - 1 := by
    rw [← hJ]
    refine Finset.sum_le_sum fun k _ => ?_
    have := (Fintype.mem_piFinset.1 hm) k
    rw [Finset.mem_range] at this
    omega
  have hc := Nat.choose_mul_factorial_mul_factorial hs
  have hf : n * (n - 1).factorial = n.factorial := Nat.mul_factorial_pred hn.ne'
  have hc' : ((n - 1).choose (∑ k, m k) : ℝ) * (∑ k, m k).factorial *
      (n - 1 - ∑ k, m k).factorial = (n - 1).factorial := by exact_mod_cast hc
  have hf' : (n : ℝ) * (n - 1).factorial = n.factorial := by exact_mod_cast hf
  have hpos : (0 : ℝ) < ((n - 1).choose (∑ k, m k) : ℝ) := by
    exact_mod_cast Nat.choose_pos hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ((n - 1 - ∑ k, m k).factorial * (∑ k, m k).factorial / n.factorial : ℝ) =
      1 / n / ((n - 1).choose (∑ k, m k) : ℝ) := by
    rw [← hf', ← hc']
    field_simp
  rw [hw]
  ring

/-- **Section 18.E** (MWG, p. 673). The weights of the hypergeometric-average formula form a
probability distribution: `∑_{m ≤ J} (1/I) ∏_k C(J_k, m_k) / C(I - 1, |m|) = 1` (apply the formula
to the additive game `w(m) = |m|`, whose Shapley value is `1` by Chapter 22). -/
theorem c18_hypergeometric_weights_sum (τ : Fin n → H) (i : Fin n) :
    ∑ m ∈ c18Box (c18Profile τ (Finset.univ.erase i)),
      (1 / n : ℝ) * ((∏ k, ((c18Profile τ (Finset.univ.erase i) k).choose (m k) : ℝ)) /
        ((n - 1).choose (∑ k, m k) : ℝ)) = 1 := by
  have hgame : c18TypeGame (fun m => ((∑ k, m k : ℕ) : ℝ)) τ =
      fun S => ∑ _j ∈ S, (1 : ℝ) := by
    funext S
    simp only [c18TypeGame, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← c18_card_eq_sum_profile]
  have h := c18_shapley_hypergeometric (fun m => ((∑ k, m k : ℕ) : ℝ)) τ i
  rw [hgame, WelfareBargaining.shapley_additive] at h
  have h' : (1 : ℝ) = _ := h
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) h'.symm
  have : ((∑ k, (m + Pi.single (τ i) (1 : ℕ) : H → ℕ) k : ℕ) : ℝ) - ((∑ k, m k : ℕ) : ℝ) =
      1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ↓reduceIte]
    push_cast
    ring
  rw [this, mul_one]

/-- **Section 18.E** (MWG, p. 673), the formula as printed: weight `1/I` times the hypergeometric
probability `∏_k C(I_k, I'_k) / C(I, |I'|)` of the profile `I'` in a sample of size `|I'|` from the
population `I`, times `Δ_h v(I') = v(I') - v(I' - e_h)`, summed over `I' ≤ I` with `I'_h ≥ 1`. -/
noncomputable def c18BookFormula (w : (H → ℕ) → ℝ) (I : H → ℕ) (h : H) : ℝ :=
  ∑ m ∈ c18Box I, if 1 ≤ m h then
    (1 / (∑ k, I k : ℕ) : ℝ) * ((∏ k, ((I k).choose (m k) : ℝ)) /
      ((∑ k, I k).choose (∑ k, m k) : ℝ)) * (w m - w (m - Pi.single h 1)) else 0

/-- **Section 18.E** (MWG, p. 673), correction: the formula as printed (`c18BookFormula`) is not
the Shapley value. With two types, one consumer of each (`τ = id` on `Fin 2`), and the additive
`v(I') = I'₁ + I'₂`, the Shapley value of the type-`1` consumer is `1`, while the printed formula
gives `3/4` (its weights over profiles with `I'_h ≥ 1` add up to `3/4`). The exact formula is
`c18_shapley_hypergeometric`. -/
theorem c18_book_formula_counterexample :
    WelfareBargaining.shapley
        (c18TypeGame (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (id : Fin 2 → Fin 2)) 0 = 1 ∧
      c18Profile (id : Fin 2 → Fin 2) Finset.univ = (fun _ => 1) ∧
      c18BookFormula (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (fun _ => 1) 0 = 3 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have hgame : c18TypeGame (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (id : Fin 2 → Fin 2) =
        fun S => ∑ _j ∈ S, (1 : ℝ) := by
      funext S
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [c18_card_eq_sum_profile (id : Fin 2 → Fin 2) S, Fin.sum_univ_two]
      rfl
    rw [hgame, WelfareBargaining.shapley_additive]
  · funext k
    simp only [c18Profile, id]
    rw [Finset.filter_eq' Finset.univ k]
    simp
  · have hbox : c18Box (fun _ : Fin 2 => 1) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
      decide
    rw [c18BookFormula, hbox]
    simp [Finset.sum_insert, Fin.sum_univ_two, Fin.prod_univ_two]
    norm_num

end MWG.CoreFoundations

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Proposition 18.D.1 for a continuum of types (MWG Section 18.D, p. 669)

Proposition 18.D.1: in an exchange economy with a continuum of consumer types whose
characteristics present cannot be split into two disconnected classes, a Pareto optimal,
self-selective, interior allocation with differentiable utilities is Walrasian. The book's proof
is "far from rigorous" and "limited to `L = 2`". `Redistribution` proves the main step assuming
that the net-trade path `z(t)` is continuous on `[0, 1]` and differentiable inside, with
aggregate feasibility a finite convex combination. Here the types are `t ∈ [0, 1]` with
characteristics `(u(·; t), ω(t))`, the population is a finite measure `ν` on the types, and:

* `c18_planar_flat_const`: (pure analysis, `L = 2`) if `z` is continuous on `[0, 1]` with values
  in `ℝ²` and `p·(z s - z t) = o(‖z s - z t‖)` uniformly, then `p·z` is constant on `[0, 1]`.
  The proof: locally `p·z` is a function of the orthogonal coordinate `q·z` with arbitrarily
  small Lipschitz constant (intermediate value theorem plus a partition of the `q·z` range), and
  `[0, 1]` is chained by short intervals.
* `c18_flat_of_noEnvy`: (any `L`) no envy among all types, differentiable utilities whose
  derivatives are uniformly equicontinuous near the bundles, and gradients `λ(t) p` with
  `λ(t) ≥ λ₀ > 0` (the first-order condition of the supporting price) give exactly that
  uniform flatness (mean value theorem on the segment from `x(t)` to `ω(t) + z(s)`).
* `c18_continuousOn_of_noEnvy`: the continuity of `z(t)`, which the book asserts informally, is
  DERIVED: from no envy, a common supporting price (each `x(t)` is best in its budget at `p`),
  utilities jointly continuous in `(t, x)` and strictly quasiconcave, continuous endowments,
  bounded net trades and interior bundles (a uniform margin `η`).
* `proposition_18_D_1_continuum`: for `L = 2`, with the measure-theoretic feasibility
  `∫_{[0,1]} z dν = 0` and `ν([0, 1]) ≠ 0`, every type's net trade has value `p·z(t) = 0` and
  every bundle is the type's Walrasian demand at `p`: the allocation is Walrasian.
* Definitions: `c18IsMeasureFeasible`, `c18IsMeasurePareto` (measure-theoretic Pareto
  optimality), `c18IsSelfSelective` (the book's anonymity: one generalized budget set `B` for
  all types present), with `c18_isSelfSelective_iff_noEnvy`.
* `c18_isMeasurePareto_of_supported`: the hypothesis "`p` supports `x`" (with local
  nonsatiation) implies measure-theoretic Pareto optimality, so the theorem applies to the
  price-supported Pareto optima.
* `proposition_18_D_1_continuum_instance`: all hypotheses hold in a concrete economy
  (quadratic utilities, `ω(t) = (1/2 + t, 3/2 - t)`, Lebesgue measure on `[0, 1]`).

Not formalised (see the source map, OPEN): the second welfare theorem for the continuum (that a
measure-theoretic Pareto optimum is supported by a common `p` with gradients `λ(t) p`), and the
case `L ≥ 3`, where the flatness step fails.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice

/-- A coordinate bound in `ℝ²`: with `q = (-p₂, p₁)`,
`(p₁² + p₂²) |Δ_l| ≤ (|p₁| + |p₂|)(|p·Δ| + |q·Δ|)`. -/
theorem c18_abs_coord_le (p Δ : Fin 2 → ℝ) (l : Fin 2) :
    (p 0 ^ 2 + p 1 ^ 2) * |Δ l| ≤
      (|p 0| + |p 1|) * (|p 0 * Δ 0 + p 1 * Δ 1| + |-p 1 * Δ 0 + p 0 * Δ 1|) := by
  have hP : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
  set a := p 0 * Δ 0 + p 1 * Δ 1
  set b := -p 1 * Δ 0 + p 0 * Δ 1
  have key : ∀ (j : Fin 2) (c d : ℝ), (p 0 ^ 2 + p 1 ^ 2) * Δ j = c * a + d * b →
      |c| ≤ |p 0| + |p 1| → |d| ≤ |p 0| + |p 1| →
      (p 0 ^ 2 + p 1 ^ 2) * |Δ j| ≤ (|p 0| + |p 1|) * (|a| + |b|) := by
    intro j c d e hc hd
    rw [← abs_of_nonneg hP, ← abs_mul, e]
    calc |c * a + d * b| ≤ |c * a| + |d * b| := abs_add_le _ _
      _ = |c| * |a| + |d| * |b| := by rw [abs_mul, abs_mul]
      _ ≤ (|p 0| + |p 1|) * |a| + (|p 0| + |p 1|) * |b| :=
          add_le_add (mul_le_mul_of_nonneg_right hc (abs_nonneg a))
            (mul_le_mul_of_nonneg_right hd (abs_nonneg b))
      _ = (|p 0| + |p 1|) * (|a| + |b|) := by ring
  fin_cases l
  · refine key 0 (p 0) (-p 1) (by simp only [a, b]; ring) ?_ ?_
    · linarith [abs_nonneg (p 1)]
    · rw [abs_neg]; linarith [abs_nonneg (p 0)]
  · refine key 1 (p 1) (p 0) (by simp only [a, b]; ring) ?_ ?_
    · linarith [abs_nonneg (p 0)]
    · linarith [abs_nonneg (p 1)]

/-- The dot product in `ℝ²`. -/
theorem c18_dot_two (p v : Fin 2 → ℝ) : p ⬝ᵥ v = p 0 * v 0 + p 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Two points of `[[s, t]]` are at most `|s - t|` apart. -/
theorem c18_abs_sub_le_of_mem_uIcc {s t x y : ℝ} (hx : x ∈ Set.uIcc s t)
    (hy : y ∈ Set.uIcc s t) : |x - y| ≤ |s - t| := by
  rw [Set.mem_uIcc] at hx hy
  rw [abs_sub_le_iff]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    constructor <;> cases abs_cases (s - t) <;> linarith

/-- `a + θ (b - a) ∈ [[a, b]]` for `θ ∈ [0, 1]`. -/
theorem c18_mem_uIcc_affine {a b θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    a + θ * (b - a) ∈ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  rcases le_total a b with h | h
  · left; constructor <;> nlinarith
  · right; constructor <;> nlinarith

/-- **Proposition 18.D.1**, the key analytic step for `L = 2` (MWG, p. 669: "the portion `M` of
the frontier of `B` containing all the net trades present ... is a straight segment with normal
`p`"). If `z : [0, 1] → ℝ²` is continuous, `p ≠ 0`, and `p·(z s - z t) = o(‖z s - z t‖)`
uniformly in `s, t`, then `p·z` is constant on `[0, 1]`. -/
theorem c18_planar_flat_const {z : ℝ → Fin 2 → ℝ} {p : Fin 2 → ℝ} (hp : p ≠ 0)
    (hz : ContinuousOn z (Set.Icc 0 1))
    (hflat : ∀ ε > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ (z s - z t)| ≤ ε * ‖z s - z t‖) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z s = p ⬝ᵥ z t := by
  set P := p 0 ^ 2 + p 1 ^ 2 with hP
  set A := |p 0| + |p 1| with hA
  have hPpos : 0 < P := by
    by_contra h
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    exact hp (by funext l; fin_cases l <;> simp [h0, h1])
  have hApos : 0 < A := by
    have h1 : P ≤ A ^ 2 := by
      rw [hP, hA, add_sq, sq_abs, sq_abs]
      nlinarith [mul_nonneg (abs_nonneg (p 0)) (abs_nonneg (p 1))]
    nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  -- the orthogonal coordinate `q·z`
  have hgd : ∀ s t, p ⬝ᵥ (z s - z t) = p ⬝ᵥ z s - p ⬝ᵥ z t := fun s t => dotProduct_sub _ _ _
  have hnorm : ∀ s t, P * ‖z s - z t‖ ≤ A * (|p ⬝ᵥ z s - p ⬝ᵥ z t| +
      |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) := by
    intro s t
    have hle : ‖z s - z t‖ ≤ A * (|p ⬝ᵥ z s - p ⬝ᵥ z t| +
        |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) / P := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ hPpos, mul_comm]
      have e1 : p ⬝ᵥ z s - p ⬝ᵥ z t = p 0 * (z s - z t) 0 + p 1 * (z s - z t) 1 := by
        rw [c18_dot_two, c18_dot_two, Pi.sub_apply, Pi.sub_apply]; ring
      have e2 : (-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1) =
          -p 1 * (z s - z t) 0 + p 0 * (z s - z t) 1 := by
        rw [Pi.sub_apply, Pi.sub_apply]; ring
      rw [e1, e2]
      exact c18_abs_coord_le p (z s - z t) l
    rwa [le_div_iff₀ hPpos, mul_comm] at hle
  -- (1) `|Δ(p·z)| ≤ ε' |Δ(q·z)|` for close values
  have hstar : ∀ ε' > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ z s - p ⬝ᵥ z t| ≤
        ε' * |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)| := by
    intro ε' hε'
    set m := min (1 / 2 : ℝ) (ε' / 2) with hm
    have hm0 : 0 < m := lt_min (by norm_num) (by linarith)
    have hm1 : m ≤ 1 / 2 := min_le_left _ _
    have hm2 : m ≤ ε' / 2 := min_le_right _ _
    obtain ⟨r, hr, hfl⟩ := hflat (P / A * m) (by positivity)
    refine ⟨r, hr, fun s hs t ht hst => ?_⟩
    have h1 := hfl s hs t ht hst
    rw [hgd] at h1
    have h2 := hnorm s t
    set g := |p ⬝ᵥ z s - p ⬝ᵥ z t|
    set a := |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|
    have h3 : P * g ≤ P * (m * (g + a)) := by
      calc P * g ≤ P * (P / A * m * ‖z s - z t‖) := mul_le_mul_of_nonneg_left h1 hPpos.le
        _ = P / A * m * (P * ‖z s - z t‖) := by ring
        _ ≤ P / A * m * (A * (g + a)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = P * (m * (g + a)) := by field_simp
    have h4 : g ≤ m * (g + a) := le_of_mul_le_mul_left h3 hPpos
    have hg0 : 0 ≤ g := abs_nonneg _
    have ha0 : 0 ≤ a := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hm1 hg0, mul_le_mul_of_nonneg_right hm2 ha0]
  -- (2) a window on which `z` moves little
  obtain ⟨r₁, hr₁, hst₁⟩ := hstar 1 one_pos
  obtain ⟨δ, hδ, hδz⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hz) r₁ hr₁
  have hwin : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |s - t| < δ →
      |p ⬝ᵥ z s - p ⬝ᵥ z t| ≤ |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)| ∧
      P * ‖z s - z t‖ ≤
        A * (2 * |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) := by
    intro s hs t ht hst
    have hd : ‖z s - z t‖ < r₁ := by
      have := hδz s hs t ht (by rwa [Real.dist_eq])
      rwa [dist_eq_norm] at this
    have h1 := hst₁ s hs t ht hd
    rw [one_mul] at h1
    refine ⟨h1, (hnorm s t).trans ?_⟩
    have := mul_le_mul_of_nonneg_left (add_le_add_left h1
      |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) hApos.le
    linarith
  -- the coordinate `q·z` is continuous
  have hac : ContinuousOn (fun u => -p 1 * z u 0 + p 0 * z u 1) (Set.Icc 0 1) :=
    (continuousOn_const.mul ((continuous_apply 0).comp_continuousOn hz)).add
      (continuousOn_const.mul ((continuous_apply 1).comp_continuousOn hz))
  -- (3) local constancy
  have hloc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |s - t| < δ →
      p ⬝ᵥ z s = p ⬝ᵥ z t := by
    intro s hs t ht hst
    by_contra hne
    set D := |(-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)| with hD
    set G := |p ⬝ᵥ z t - p ⬝ᵥ z s| with hG
    have hGpos : 0 < G := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
    have hD0 : 0 ≤ D := abs_nonneg _
    set ε' := G / (2 * (D + 1)) with hε'
    have hε'pos : 0 < ε' := by positivity
    obtain ⟨r, hr, hstr⟩ := hstar ε' hε'pos
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * A * D / (P * r))
    set N := N₀ + 1 with hN
    have hNpos : (0 : ℝ) < N := by positivity
    have hNbig : 2 * A * D / (P * r) < N := by
      have : (N₀ : ℝ) < N := by rw [hN]; push_cast; linarith
      linarith
    have hsub : Set.uIcc s t ⊆ Set.Icc 0 1 := Set.uIcc_subset_Icc hs ht
    have hivt := intermediate_value_uIcc (hac.mono hsub)
    have hval : ∀ k : ℕ, ∃ c ∈ Set.uIcc s t, -p 1 * z c 0 + p 0 * z c 1 =
        (-p 1 * z s 0 + p 0 * z s 1) + (min k N : ℕ) / (N : ℝ) *
          ((-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)) := by
      intro k
      have h0 : (0 : ℝ) ≤ (min k N : ℕ) / (N : ℝ) := by positivity
      have h1 : (min k N : ℕ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast min_le_right k N
      exact hivt (c18_mem_uIcc_affine h0 h1)
    choose c hc hca using hval
    have hcI : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1 := fun k => hsub (hc k)
    have hcδ : ∀ j k, |c j - c k| < δ := fun j k =>
      (c18_abs_sub_le_of_mem_uIcc (hc j) (hc k)).trans_lt hst
    -- the endpoints
    have hend : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| < δ →
        -p 1 * z x 0 + p 0 * z x 1 = -p 1 * z y 0 + p 0 * z y 1 → p ⬝ᵥ z x = p ⬝ᵥ z y := by
      intro x hx y hy hxy he
      have := (hwin x hx y hy hxy).1
      rw [he, sub_self, abs_zero] at this
      exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
    have hs0 : p ⬝ᵥ z (c 0) = p ⬝ᵥ z s := by
      refine hend _ (hcI 0) s hs ?_ ?_
      · exact (c18_abs_sub_le_of_mem_uIcc (hc 0) Set.left_mem_uIcc).trans_lt hst
      · rw [hca 0]; simp
    have htN : p ⬝ᵥ z (c N) = p ⬝ᵥ z t := by
      refine hend _ (hcI N) t ht ?_ ?_
      · exact (c18_abs_sub_le_of_mem_uIcc (hc N) Set.right_mem_uIcc).trans_lt hst
      · rw [hca N, min_self, div_self hNpos.ne']; ring
    -- consecutive points
    have hstep : ∀ k ∈ Finset.range N, |p ⬝ᵥ z (c (k + 1)) - p ⬝ᵥ z (c k)| ≤ ε' * (D / N) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hda : (-p 1 * z (c (k + 1)) 0 + p 0 * z (c (k + 1)) 1) -
          (-p 1 * z (c k) 0 + p 0 * z (c k) 1) =
          ((-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)) / N := by
        rw [hca, hca, min_eq_left (by omega : k + 1 ≤ N), min_eq_left hk.le]
        push_cast
        field_simp
        ring
      have hdaabs : |(-p 1 * z (c (k + 1)) 0 + p 0 * z (c (k + 1)) 1) -
          (-p 1 * z (c k) 0 + p 0 * z (c k) 1)| = D / N := by
        rw [hda, abs_div, abs_of_pos hNpos]
      have hw := (hwin _ (hcI (k + 1)) _ (hcI k) (hcδ (k + 1) k)).2
      rw [hdaabs] at hw
      have hzr : ‖z (c (k + 1)) - z (c k)‖ < r := by
        have h1 : ‖z (c (k + 1)) - z (c k)‖ ≤ A * (2 * (D / N)) / P := by
          rw [le_div_iff₀ hPpos, mul_comm]; exact hw
        refine h1.trans_lt ?_
        rw [div_lt_iff₀ hPpos]
        have h2 : 2 * A * D < N * (P * r) := by
          rwa [div_lt_iff₀ (by positivity)] at hNbig
        rw [show A * (2 * (D / N)) = 2 * A * D / N by ring, div_lt_iff₀ hNpos]
        linarith
      have := hstr _ (hcI (k + 1)) _ (hcI k) hzr
      rwa [hdaabs] at this
    have htel : p ⬝ᵥ z (c N) - p ⬝ᵥ z (c 0) =
        ∑ k ∈ Finset.range N, (p ⬝ᵥ z (c (k + 1)) - p ⬝ᵥ z (c k)) :=
      (Finset.sum_range_sub (fun k => p ⬝ᵥ z (c k)) N).symm
    have hbound : G ≤ ε' * D := by
      rw [hG, ← htN, ← hs0, htel]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl
    have : ε' * D < G := by
      rw [hε']
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- (4) chaining along `[0, 1]`
  intro s hs t ht
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (1 / δ)
  set M := M₀ + 1 with hM
  have hMpos : (0 : ℝ) < M := by positivity
  have hMδ : 1 / (M : ℝ) < δ := by
    have : (M₀ : ℝ) < M := by rw [hM]; push_cast; linarith
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hδ] at hM₀
    nlinarith
  have hy : ∀ j : ℕ, j ≤ M → s + (j : ℝ) / M * (t - s) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    have h0 : (0 : ℝ) ≤ (j : ℝ) / M := by positivity
    have h1 : (j : ℝ) / M ≤ 1 := by rw [div_le_one hMpos]; exact_mod_cast hj
    have := c18_mem_uIcc_affine (a := s) (b := t) h0 h1
    exact Set.uIcc_subset_Icc hs ht this
  have hchain : ∀ j : ℕ, j ≤ M → p ⬝ᵥ z (s + (j : ℝ) / M * (t - s)) = p ⬝ᵥ z s := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      refine hloc _ (hy _ hj) _ (hy _ (by omega)) ?_
      have hts : |t - s| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      have e : s + ((j + 1 : ℕ) : ℝ) / M * (t - s) - (s + (j : ℝ) / M * (t - s)) =
          (t - s) / M := by push_cast; ring
      rw [e, abs_div, abs_of_pos hMpos]
      refine lt_of_le_of_lt ?_ hMδ
      exact div_le_div_of_nonneg_right hts hMpos.le
  have := hchain M le_rfl
  rw [div_self hMpos.ne', one_mul, add_sub_cancel] at this
  exact this.symm

/-- **Proposition 18.D.1**, the flatness step for any `L` (MWG, p. 669: "if envy is to be
prevented, then similar individuals must be treated similarly"). If no type envies another type's
net trade, the bundles `x(t) = ω(t) + z(t)` are interior with a uniform margin `η`, every `u(·; t)`
is differentiable near the bundles with derivatives `D(t, y)` that are uniformly equicontinuous
(uniformly in `t`), and the derivative at `x(t)` is `λ(t) p` with `λ(t) ≥ λ₀ > 0`, then
`p·(z s - z t) = o(‖z s - z t‖)` uniformly in `s, t`. -/
theorem c18_flat_of_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ} {ω z : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {lam : ℝ → ℝ} {η lam₀ : ℝ}
    (hη : 0 < η) (hlam₀ : 0 < lam₀)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin L → ℝ, (∀ l, η / 2 ≤ y l) →
      HasFDerivAt (u t) (D t y) y)
    (hDuc : ∀ ε > 0, ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y y' : Fin L → ℝ,
      (∀ l, η / 2 ≤ y l) → (∀ l, η / 2 ≤ y' l) → ‖y - y'‖ < ρ → ‖D t y - D t y'‖ ≤ ε)
    (hgrad : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v, D t (ω t + z t) v = lam t * (p ⬝ᵥ v))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, lam₀ ≤ lam t) :
    ∀ ε > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ (z s - z t)| ≤ ε * ‖z s - z t‖ := by
  intro ε hε
  obtain ⟨ρ, hρ, hρD⟩ := hDuc (ε * lam₀) (by positivity)
  have hone : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < min ρ (η / 2) →
      lam t * (p ⬝ᵥ (z s - z t)) ≤ ε * lam₀ * ‖z s - z t‖ := by
    intro s hs t ht hst
    set x := ω t + z t with hx
    set Δ := z s - z t with hΔdef
    have hΔ : ‖Δ‖ < η / 2 := lt_of_lt_of_le hst (min_le_right _ _)
    have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ l, η / 2 ≤ (x + θ • Δ) l := by
      intro θ hθ l
      have h1 : |Δ l| ≤ ‖Δ‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm Δ l
      have h2 : |θ * Δ l| ≤ ‖Δ‖ := by
        rw [abs_mul, abs_of_nonneg hθ.1]
        nlinarith [abs_nonneg (Δ l), hθ.2]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hint t ht l
      simp only [hx, Pi.add_apply]
      linarith [neg_abs_le (θ * Δ l)]
    have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun θ : ℝ => u t (x + θ • Δ)) (D t (x + θ • Δ) Δ) θ := by
      intro θ hθ
      have hγ : HasDerivAt (fun θ : ℝ => x + θ • Δ) Δ θ := by
        simpa using ((hasDerivAt_id θ).smul_const Δ).const_add x
      exact (hD t ht _ (hseg θ hθ)).comp_hasDerivAt θ hγ
    obtain ⟨θ, hθ, hmv⟩ := exists_hasDerivAt_eq_slope (fun θ : ℝ => u t (x + θ • Δ))
      (fun θ => D t (x + θ • Δ) Δ) zero_lt_one
      (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => hderiv θ (Set.Ioo_subset_Icc_self hθ))
    have hx1 : x + (1 : ℝ) • Δ = ω t + z s := by
      rw [one_smul, hx, hΔdef]; abel
    have hfeas : ω t + z s ∈ nonnegOrthant L := fun l => by
      have := hseg 1 ⟨zero_le_one, le_rfl⟩ l
      rw [hx1] at this
      linarith
    have henv := henvy t ht s hs hfeas
    rw [hx1, zero_smul, add_zero, sub_zero, div_one] at hmv
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hθ
    have hclose : ‖x + θ • Δ - x‖ < ρ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθI.1]
      calc θ * ‖Δ‖ ≤ ‖Δ‖ := by nlinarith [norm_nonneg Δ, hθI.2]
        _ < ρ := lt_of_lt_of_le hst (min_le_left _ _)
    have hx0 : ∀ l, η / 2 ≤ x l := fun l => by
      have := hseg 0 ⟨le_rfl, zero_le_one⟩ l
      rwa [zero_smul, add_zero] at this
    have hdiff := hρD t ht (x + θ • Δ) x (hseg θ hθI) hx0 hclose
    have hop : (D t x - D t (x + θ • Δ)) Δ ≤ ε * lam₀ * ‖Δ‖ := by
      calc (D t x - D t (x + θ • Δ)) Δ ≤ ‖(D t x - D t (x + θ • Δ)) Δ‖ := Real.le_norm_self _
        _ ≤ ‖D t x - D t (x + θ • Δ)‖ * ‖Δ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * lam₀ * ‖Δ‖ := by
          rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
    rw [← hgrad t ht]
    have e : D t x Δ = D t (x + θ • Δ) Δ + (D t x - D t (x + θ • Δ)) Δ := by simp
    rw [e, hmv]
    linarith
  refine ⟨min ρ (η / 2), lt_min hρ (by positivity), fun s hs t ht hst => ?_⟩
  have h1 := hone s hs t ht hst
  have h2 := hone t ht s hs (by rwa [norm_sub_rev])
  rw [norm_sub_rev] at h2
  have e : p ⬝ᵥ (z t - z s) = -(p ⬝ᵥ (z s - z t)) := by rw [← dotProduct_neg, neg_sub]
  rw [e] at h2
  have hl1 := hlam t ht
  have hl2 := hlam s hs
  have hn := norm_nonneg (z s - z t)
  rw [abs_le]
  constructor
  · by_contra hc
    rw [not_le] at hc
    have h3 : lam s * (ε * ‖z s - z t‖) < lam s * -(p ⬝ᵥ (z s - z t)) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hl2 (mul_nonneg hε.le hn)]
  · by_contra hc
    rw [not_le] at hc
    have h3 : lam t * (ε * ‖z s - z t‖) < lam t * (p ⬝ᵥ (z s - z t)) :=
      mul_lt_mul_of_pos_left hc (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hl1 (mul_nonneg hε.le hn)]

open Filter Topology in
/-- **Proposition 18.D.1**, the continuity of `z(t)` (MWG, p. 669: "A key fact is that `z(t)` is
continuous as a function of `t`. This is intuitive."), DERIVED. Assume: no envy among the types
`t ∈ [0, 1]`; a common price `p` supports every bundle `x(t) = ω(t) + z(t)` (each is best in its
budget `{y ≥ 0 : p·y ≤ p·x(t)}`); interior bundles with a uniform margin `η > 0`; bounded net
trades; continuous endowments; utilities jointly continuous in `(t, x)` and strictly
quasiconcave (strictly convex preferences). Then `t ↦ z(t)` is continuous on `[0, 1]`. -/
theorem c18_continuousOn_of_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ} {ω z : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {η M : ℝ} (hη : 0 < η)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (hzb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖z t‖ ≤ M) (hω : ContinuousOn ω (Set.Icc 0 1))
    (hu : ContinuousOn (fun q : ℝ × (Fin L → ℝ) => u q.1 q.2)
      (Set.Icc 0 1 ×ˢ {y | ∀ l, η / 2 ≤ y l}))
    (hsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin L → ℝ, (∀ l, η / 2 ≤ x l) →
      (∀ l, η / 2 ≤ y l) → x ≠ y → min (u t x) (u t y) < u t ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y))
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t)) :
    ContinuousOn z (Set.Icc 0 1) := by
  intro t ht
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨hns1, hns2⟩ := tendsto_nhdsWithin_iff.1 hns
  obtain ⟨zb, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_closedBall (x := (0 : Fin L → ℝ)) (r := M))
    (hns2.mono fun k hk => mem_closedBall_zero_iff.2 (hzb _ hk)).frequently
  refine ⟨φ, ?_⟩
  set sk : ℕ → ℝ := fun k => ns (φ k) with hskdef
  have hsk : Tendsto sk atTop (𝓝 t) := hns1.comp hφ.tendsto_atTop
  have hskI : ∀ᶠ k in atTop, sk k ∈ Set.Icc (0 : ℝ) 1 := hφ.tendsto_atTop.eventually hns2
  have hzk : Tendsto (fun k => z (sk k)) atTop (𝓝 zb) := hlim
  have hωk : Tendsto (fun k => ω (sk k)) atTop (𝓝 (ω t)) :=
    (hω t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hsk, hskI⟩)
  set R : Set (Fin L → ℝ) := {y | ∀ l, η / 2 ≤ y l} with hR
  have hRc : IsClosed R := by
    rw [hR, Set.ofPred_forall]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have hjl : ∀ (y : ℕ → Fin L → ℝ) (yb : Fin L → ℝ), Tendsto y atTop (𝓝 yb) → yb ∈ R →
      (∀ᶠ k in atTop, y k ∈ R) → Tendsto (fun k => u (sk k) (y k)) atTop (𝓝 (u t yb)) := by
    intro y yb hy hyb hyR
    exact (hu (t, yb) ⟨ht, hyb⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hsk.prodMk_nhds hy, (hskI.and hyR).mono fun k hk => ⟨hk.1, hk.2⟩⟩)
  have hjl' : ∀ (y : ℕ → Fin L → ℝ) (yb : Fin L → ℝ), Tendsto y atTop (𝓝 yb) → yb ∈ R →
      (∀ᶠ k in atTop, y k ∈ R) → Tendsto (fun k => u t (y k)) atTop (𝓝 (u t yb)) := by
    intro y yb hy hyb hyR
    exact (hu (t, yb) ⟨ht, hyb⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.prodMk_nhds hy, hyR.mono fun k hk => ⟨ht, hk⟩⟩)
  set xb := ω t + zb with hxb
  set xt := ω t + z t with hxt
  have hxk : Tendsto (fun k => ω (sk k) + z (sk k)) atTop (𝓝 xb) := hωk.add hzk
  have hxbη : ∀ l, η ≤ xb l := fun l =>
    ge_of_tendsto (((continuous_apply l).tendsto _).comp hxk)
      (hskI.mono fun k hk => hint _ hk l)
  have hxbR : xb ∈ R := fun l => by linarith [hxbη l]
  have hxtR : xt ∈ R := fun l => by
    change η / 2 ≤ ω t l + z t l
    linarith [hint t ht l]
  have hωclose : ∀ᶠ k in atTop, dist (ω (sk k)) (ω t) < η / 2 :=
    Metric.tendsto_nhds.1 hωk (η / 2) (by positivity)
  have hcoord : ∀ k, dist (ω (sk k)) (ω t) < η / 2 → ∀ l, |ω (sk k) l - ω t l| < η / 2 :=
    fun k hk l => lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist _ _ l) hk
  have hxkR : ∀ᶠ k in atTop, ω (sk k) + z (sk k) ∈ R :=
    hskI.mono fun k hk l => by
      change η / 2 ≤ ω (sk k) l + z (sk k) l
      linarith [hint _ hk l]
  have hA : ∀ᶠ k in atTop, ω t + z (sk k) ∈ R := (hskI.and hωclose).mono fun k hk l => by
    have h1 := hint _ hk.1 l
    have h2 := hcoord k hk.2 l
    simp only [Pi.add_apply]
    linarith [le_abs_self (ω (sk k) l - ω t l)]
  have hB : ∀ᶠ k in atTop, ω (sk k) + z t ∈ R := hωclose.mono fun k hk l => by
    have h1 := hint t ht l
    have h2 := hcoord k hk l
    simp only [Pi.add_apply]
    linarith [neg_abs_le (ω (sk k) l - ω t l)]
  -- type `t` does not envy `z(s_k)`, type `s_k` does not envy `z(t)`
  have hF1 : u t xb ≤ u t xt := by
    refine le_of_tendsto (hjl' _ xb (tendsto_const_nhds.add hzk) hxbR hA) ?_
    exact (hskI.and hA).mono fun k hk => henvy t ht _ hk.1 fun l => by
      linarith [hk.2 l]
  have hF2 : u t xt ≤ u t xb := by
    refine le_of_tendsto_of_tendsto (hjl _ xt (hωk.add tendsto_const_nhds) hxtR hB)
      (hjl _ xb hxk hxbR hxkR) ?_
    exact (hskI.and hB).mono fun k hk => henvy _ hk.1 t ht fun l => by linarith [hk.2 l]
  have hzbt : zb = z t := by
    by_contra hne
    have hne' : xt ≠ xb := fun h => hne (add_left_cancel h).symm
    set m := (1 / 2 : ℝ) • xt + (1 / 2 : ℝ) • xb with hm
    have hstrict := hsq t ht xt xb hxtR hxbR hne'
    rw [min_eq_left hF2] at hstrict
    have hmR : m ∈ R := fun l => by
      simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hxtR l, hxbR l]
    have hm0 : m ∈ nonnegOrthant L := fun l => by linarith [hmR l]
    have hpm : p ⬝ᵥ m = (p ⬝ᵥ xt + p ⬝ᵥ xb) / 2 := by
      rw [hm, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rcases le_or_gt (p ⬝ᵥ xb) (p ⬝ᵥ xt) with h | h
    · have := hsupp t ht m hm0 (by rw [hpm]; linarith)
      linarith
    · have hdotc : Continuous fun x : Fin L → ℝ => p ⬝ᵥ x := by
        unfold dotProduct; fun_prop
      have hev : ∀ᶠ k in atTop, p ⬝ᵥ m < p ⬝ᵥ (ω (sk k) + z (sk k)) :=
        ((hdotc.tendsto xb).comp hxk).eventually (lt_mem_nhds (by rw [hpm]; linarith))
      have hle : u t m ≤ u t xb := by
        refine le_of_tendsto_of_tendsto (hjl _ m tendsto_const_nhds hmR
          (Eventually.of_forall fun _ => hmR)) (hjl _ xb hxk hxbR hxkR) ?_
        exact (hskI.and hev).mono fun k hk => hsupp _ hk.1 m hm0 hk.2.le
      linarith
  rw [← hzbt]
  exact hlim

open MeasureTheory in
/-- **Proposition 18.D.1** (MWG, p. 669), continuum form for `L = 2`. Types `t ∈ [0, 1]` with
utilities `u(·; t)` and endowments `ω(t)`, a population measure `ν` (finite on compacts, e.g.
Lebesgue measure) with `ν([0, 1]) ≠ 0`, and net trades `z(t)` that are feasible in the measure
sense, `∫_{[0,1]} z dν = 0`. Assume the allocation is self-selective (no type envies another
type's net trade, `c18_isSelfSelective_iff_noEnvy`), interior (uniform margin `η`), bounded,
and supported by a price `p ≠ 0` with first-order conditions `Du(x(t); t) = λ(t) p`,
`λ(t) ≥ λ₀ > 0`, as a Pareto optimum is (`c18_isMeasurePareto_of_supported`), with endowments
continuous in `t`, utilities jointly continuous, strictly quasiconcave and differentiable with
uniformly equicontinuous derivatives near the bundles. Then `z` is continuous (derived),
`p·z(t) = 0` for every type and every bundle is the type's Walrasian demand at `p`: the
allocation is a Walrasian equilibrium allocation. -/
theorem proposition_18_D_1_continuum {u : ℝ → (Fin 2 → ℝ) → ℝ} {ω z : ℝ → Fin 2 → ℝ}
    {p : Fin 2 → ℝ} {D : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ} {lam : ℝ → ℝ}
    {η lam₀ M : ℝ} (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν] (hp : p ≠ 0) (hη : 0 < η)
    (hlam₀ : 0 < lam₀)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (hzb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖z t‖ ≤ M) (hω : ContinuousOn ω (Set.Icc 0 1))
    (hu : ContinuousOn (fun q : ℝ × (Fin 2 → ℝ) => u q.1 q.2)
      (Set.Icc 0 1 ×ˢ {y | ∀ l, η / 2 ≤ y l}))
    (hsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin 2 → ℝ, (∀ l, η / 2 ≤ x l) →
      (∀ l, η / 2 ≤ y l) → x ≠ y → min (u t x) (u t y) < u t ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y))
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant 2 →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin 2 → ℝ, (∀ l, η / 2 ≤ y l) →
      HasFDerivAt (u t) (D t y) y)
    (hDuc : ∀ ε > 0, ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y y' : Fin 2 → ℝ,
      (∀ l, η / 2 ≤ y l) → (∀ l, η / 2 ≤ y' l) → ‖y - y'‖ < ρ → ‖D t y - D t y'‖ ≤ ε)
    (hgrad : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v, D t (ω t + z t) v = lam t * (p ⬝ᵥ v))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, lam₀ ≤ lam t)
    (hν : ν (Set.Icc 0 1) ≠ 0) (hfeas : ∀ l, ∫ t in Set.Icc 0 1, z t l ∂ν = 0) :
    ContinuousOn z (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = 0 ∧
      ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ ω t → u t y ≤ u t (ω t + z t) := by
  have hzc := c18_continuousOn_of_noEnvy hη hint hzb hω hu hsq henvy hsupp
  have hflat := c18_flat_of_noEnvy hη hlam₀ hint henvy hD hDuc hgrad hlam
  have hconst := c18_planar_flat_const hp hzc hflat
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hintl : ∀ l, IntegrableOn (fun t => z t l) (Set.Icc 0 1) ν := fun l =>
    ((continuous_apply l).comp_continuousOn hzc).integrableOn_compact isCompact_Icc
  have hI1 : ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = 0 := by
    calc ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ∫ t in Set.Icc 0 1, ∑ l, p l * z t l ∂ν := rfl
      _ = ∑ l, ∫ t in Set.Icc 0 1, p l * z t l ∂ν :=
          integral_finsetSum _ fun l _ => (hintl l).const_mul (p l)
      _ = ∑ l, p l * ∫ t in Set.Icc 0 1, z t l ∂ν := by
          simp only [integral_const_mul]
      _ = 0 := by simp [hfeas]
  have hI2 : ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ν.real (Set.Icc 0 1) * (p ⬝ᵥ z 0) := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => hconst t ht 0 h0I),
      setIntegral_const, smul_eq_mul]
  have hreal : ν.real (Set.Icc 0 1) ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hν, isCompact_Icc.measure_lt_top.ne⟩
  have hc : p ⬝ᵥ z 0 = 0 := by
    rw [hI1] at hI2
    exact (mul_eq_zero.1 hI2.symm).resolve_left hreal
  refine ⟨hzc, fun t ht => ?_⟩
  have hzt : p ⬝ᵥ z t = 0 := by rw [hconst t ht 0 h0I, hc]
  have he : p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t := by rw [dotProduct_add, hzt, add_zero]
  exact ⟨hzt, fun y hy hpy => hsupp t ht y hy (he ▸ hpy)⟩

/-! ### Definitions: self-selectivity, measure feasibility, measure-theoretic Pareto optimality -/

/-- **Definition 18.D.1** for a continuum of types (MWG, p. 666): the allocation with net trades
`z(t)` is self-selective (anonymous) if one generalized budget set `B` serves all types present:
`z(t) ∈ B` and `z(t)` is best for type `t` among the net trades `b ∈ B` with `ω(t) + b ≥ 0`. -/
def c18IsSelfSelective {L : ℕ} (u : ℝ → (Fin L → ℝ) → ℝ) (ω z : ℝ → Fin L → ℝ) : Prop :=
  ∃ B : Set (Fin L → ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1, z t ∈ B ∧
    ∀ b ∈ B, ω t + b ∈ nonnegOrthant L → u t (ω t + b) ≤ u t (ω t + z t)

/-- **Definition 18.D.1** for a continuum of types (MWG, p. 666): self-selective iff no type
envies another type's net trade (take `B = {z(s) : s ∈ [0, 1]}`). -/
theorem c18_isSelfSelective_iff_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ}
    {ω z : ℝ → Fin L → ℝ} :
    c18IsSelfSelective u ω z ↔ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ω t + z s ∈ nonnegOrthant L → u t (ω t + z s) ≤ u t (ω t + z t) := by
  constructor
  · rintro ⟨B, hB⟩ t ht s hs h
    exact (hB t ht).2 (z s) (hB s hs).1 h
  · intro h
    refine ⟨z '' Set.Icc 0 1, fun t ht => ⟨⟨t, ht, rfl⟩, ?_⟩⟩
    rintro b ⟨s, hs, rfl⟩ hb
    exact h t ht s hs hb

open MeasureTheory in
/-- **Section 18.D** for a continuum of types: the net trades `z(t)`, `t ∈ [0, 1]`, are feasible
for the population measure `ν` if they are integrable and `∫_{[0,1]} z dν = 0`. -/
def c18IsMeasureFeasible {L : ℕ} (ν : Measure ℝ) (z : ℝ → Fin L → ℝ) : Prop :=
  ∀ l, IntegrableOn (fun t => z t l) (Set.Icc 0 1) ν ∧ ∫ t in Set.Icc 0 1, z t l ∂ν = 0

open MeasureTheory in
/-- **Proposition 18.D.1** for a continuum of types: measure-theoretic Pareto optimality. The net
trades `z` are feasible and no feasible `z'` makes `ν`-almost every type weakly better off (with
`ω(t) + z'(t) ≥ 0`) and a set of types of positive measure strictly better off. -/
def c18IsMeasurePareto {L : ℕ} (ν : Measure ℝ) (u : ℝ → (Fin L → ℝ) → ℝ)
    (ω z : ℝ → Fin L → ℝ) : Prop :=
  c18IsMeasureFeasible ν z ∧ ¬ ∃ z' : ℝ → Fin L → ℝ, c18IsMeasureFeasible ν z' ∧
    (∀ᵐ t ∂(ν.restrict (Set.Icc 0 1)), ω t + z' t ∈ nonnegOrthant L ∧
      u t (ω t + z t) ≤ u t (ω t + z' t)) ∧
    ν.restrict (Set.Icc 0 1) {t | u t (ω t + z t) < u t (ω t + z' t)} ≠ 0

open MeasureTheory in
/-- The value of feasible net trades is zero: `∫_{[0,1]} p·z dν = 0`, with `p·z` integrable. -/
theorem c18_integral_dot_eq_zero {L : ℕ} {ν : Measure ℝ} {z : ℝ → Fin L → ℝ}
    (hf : c18IsMeasureFeasible ν z) (p : Fin L → ℝ) :
    IntegrableOn (fun t => p ⬝ᵥ z t) (Set.Icc 0 1) ν ∧
      ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = 0 := by
  have hi : ∀ l ∈ Finset.univ, Integrable (fun t => p l * z t l) (ν.restrict (Set.Icc 0 1)) :=
    fun l _ => (hf l).1.const_mul (p l)
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  calc ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ∫ t in Set.Icc 0 1, ∑ l, p l * z t l ∂ν := rfl
    _ = ∑ l, ∫ t in Set.Icc 0 1, p l * z t l ∂ν := integral_finsetSum _ hi
    _ = ∑ l, p l * ∫ t in Set.Icc 0 1, z t l ∂ν := by simp only [integral_const_mul]
    _ = 0 := by simp [fun l => (hf l).2]

open MeasureTheory in
/-- **Proposition 18.D.1**, the hypothesis "`p` supports `x`" (MWG, p. 669: "Let `p` be the price
vector supporting `x*` as a Pareto optimal allocation") is consistent with, and yields,
measure-theoretic Pareto optimality: if `p ≥ 0`, `p ≠ 0`, every type's bundle is best in its
budget at `p` and utilities are strictly increasing along the diagonal, then a feasible
allocation is Pareto optimal in the measure sense (the first welfare theorem for the
continuum). -/
theorem c18_isMeasurePareto_of_supported {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ}
    {ω z : ℝ → Fin L → ℝ} {p : Fin L → ℝ} (ν : Measure ℝ) (hfeas : c18IsMeasureFeasible ν z)
    (hpsum : 0 < ∑ l, p l)
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t))
    (hmono : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, ∀ δ : ℝ, 0 < δ →
      u t y < u t (y + fun _ => δ)) :
    c18IsMeasurePareto ν u ω z := by
  refine ⟨hfeas, ?_⟩
  rintro ⟨z', hf', hae, hS⟩
  have hcheap : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L,
      p ⬝ᵥ y < p ⬝ᵥ (ω t + z t) → u t y < u t (ω t + z t) := by
    intro t ht y hy hpy
    set δ := (p ⬝ᵥ (ω t + z t) - p ⬝ᵥ y) / ∑ l, p l with hδ
    have hδpos : 0 < δ := div_pos (by linarith) hpsum
    have hyδ : y + (fun _ => δ) ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hy l]
    have hpδ : p ⬝ᵥ (y + fun _ => δ) = p ⬝ᵥ (ω t + z t) := by
      rw [dotProduct_add]
      have : p ⬝ᵥ (fun _ : Fin L => δ) = δ * ∑ l, p l := by
        simp only [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      rw [this, hδ, div_mul_cancel₀ _ hpsum.ne']
      ring
    exact (hmono t ht y hy δ hδpos).trans_le (hsupp t ht _ hyδ hpδ.le)
  set μ := ν.restrict (Set.Icc (0 : ℝ) 1) with hμ
  have hmem : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hle : ∀ᵐ t ∂μ, p ⬝ᵥ z t ≤ p ⬝ᵥ z' t := by
    filter_upwards [hae, hmem] with t ht hti
    by_contra hc
    rw [not_le] at hc
    have := hcheap t hti _ ht.1 (by rw [dotProduct_add, dotProduct_add]; linarith)
    linarith [ht.2]
  have hlt : {t | u t (ω t + z t) < u t (ω t + z' t)} ≤ᵐ[μ] {t | p ⬝ᵥ z t < p ⬝ᵥ z' t} := by
    filter_upwards [hae, hmem] with t ht hti
    intro h
    by_contra hc
    have hc' : p ⬝ᵥ z' t ≤ p ⬝ᵥ z t := not_lt.1 hc
    have := hsupp t hti _ ht.1 (by rw [dotProduct_add, dotProduct_add]; linarith)
    exact absurd h (not_lt.2 this)
  obtain ⟨hi, hz0⟩ := c18_integral_dot_eq_zero hfeas p
  obtain ⟨hi', hz0'⟩ := c18_integral_dot_eq_zero hf' p
  have hg0 : 0 ≤ᵐ[μ] fun t => p ⬝ᵥ z' t - p ⬝ᵥ z t := hle.mono fun t ht => by
    simp only [Pi.zero_apply]; linarith
  have hpos : 0 < ∫ t, (p ⬝ᵥ z' t - p ⬝ᵥ z t) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hg0 (hi'.sub hi)]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hS) ((measure_mono_ae hlt).trans
      (measure_mono fun t ht => ?_))
    rw [Function.mem_support]
    rw [Set.mem_ofPred_eq] at ht
    linarith
  rw [integral_sub hi' hi, hz0, hz0', sub_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### An instance of all the hypotheses -/

/-- Instance data: the quadratic utility `u(y) = y₁ - y₁²/4 + y₂ - y₂²/4` (the same for all
types). -/
noncomputable def c18InstU : ℝ → (Fin 2 → ℝ) → ℝ :=
  fun _ y => y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4)

/-- Instance data: endowments `ω(t) = (1/2 + t, 3/2 - t)`. -/
noncomputable def c18InstOmega : ℝ → Fin 2 → ℝ := fun t => ![1 / 2 + t, 3 / 2 - t]

/-- Instance data: net trades `z(t) = (1/2 - t, t - 1/2)` (every type consumes `(1, 1)`). -/
noncomputable def c18InstZ : ℝ → Fin 2 → ℝ := fun t => ![1 / 2 - t, t - 1 / 2]

/-- Instance data: the derivative `Du(y) v = (1 - y₁/2) v₁ + (1 - y₂/2) v₂`. -/
noncomputable def c18InstD : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ := fun _ y =>
  (1 - y 0 / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    (1 - y 1 / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem c18InstD_apply (t : ℝ) (y v : Fin 2 → ℝ) :
    c18InstD t y v = (1 - y 0 / 2) * v 0 + (1 - y 1 / 2) * v 1 := by
  simp [c18InstD]

theorem c18InstU_mid (x y : Fin 2 → ℝ) :
    c18InstU 0 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) =
      (c18InstU 0 x + c18InstU 0 y) / 2 + ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) / 16 := by
  simp only [c18InstU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

open MeasureTheory in
/-- **Proposition 18.D.1** (MWG, p. 669), an instance of every hypothesis of
`proposition_18_D_1_continuum`: types `t ∈ [0, 1]` with Lebesgue measure, the quadratic utility
`c18InstU`, endowments `(1/2 + t, 3/2 - t)`, net trades `(1/2 - t, t - 1/2)`, `p = (1, 1)`,
`λ = 1/2`, margin `η = 1`; the conclusion (every type's bundle `(1, 1)` is her Walrasian demand)
follows. -/
theorem proposition_18_D_1_continuum_instance :
    ContinuousOn c18InstZ (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ![1, 1] ⬝ᵥ c18InstZ t = 0 ∧
      ∀ y ∈ nonnegOrthant 2, ![1, 1] ⬝ᵥ y ≤ ![1, 1] ⬝ᵥ c18InstOmega t →
        c18InstU t y ≤ c18InstU t (c18InstOmega t + c18InstZ t) := by
  have hx : ∀ t, c18InstOmega t + c18InstZ t = ![1, 1] := fun t => by
    funext l; fin_cases l <;> simp [c18InstOmega, c18InstZ] <;> ring
  have hu1 : ∀ t, c18InstU t ![1, 1] = 3 / 2 := fun t => by
    simp [c18InstU]; norm_num
  have hzc : Continuous c18InstZ := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_const.sub continuous_id
    · exact continuous_id.sub continuous_const
  refine proposition_18_D_1_continuum (D := c18InstD) (lam := fun _ => 1 / 2) (η := 1)
    (lam₀ := 1 / 2) (M := 1 / 2) (volume : Measure ℝ) (by
      intro h; have := congrFun h 0; simp at this) one_pos (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t _ l
    rw [← Pi.add_apply, hx]
    fin_cases l <;> simp
  · intro t ht
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun l => ?_
    rw [Real.norm_eq_abs, abs_le]
    fin_cases l <;> simp [c18InstZ] <;> constructor <;> linarith [ht.1, ht.2]
  · refine Continuous.continuousOn (continuous_pi fun l => ?_)
    fin_cases l
    · exact continuous_const.add continuous_id
    · exact continuous_const.sub continuous_id
  · refine Continuous.continuousOn ?_
    simp only [c18InstU]
    fun_prop
  · intro t _ x y _ _ hxy
    have hm := c18InstU_mid x y
    simp only [c18InstU] at hm ⊢
    have hpos : 0 < (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      by_contra hc
      have h0 : x 0 = y 0 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      have h1 : x 1 = y 1 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      exact hxy (by funext l; fin_cases l <;> simp [h0, h1])
    rw [hm]
    have := min_le_left (x 0 - x 0 ^ 2 / 4 + (x 1 - x 1 ^ 2 / 4))
      (y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4))
    have := min_le_right (x 0 - x 0 ^ 2 / 4 + (x 1 - x 1 ^ 2 / 4))
      (y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4))
    linarith
  · intro t _ s _ _
    rw [hx, hu1]
    simp only [c18InstU, c18InstOmega, c18InstZ, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith [sq_nonneg (1 / 2 + t + (1 / 2 - s) - (3 / 2 - t + (s - 1 / 2)))]
  · intro t _ y hy hpy
    rw [hx, hu1]
    rw [hx, c18_dot_two, c18_dot_two] at hpy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hpy
    simp only [c18InstU]
    have h0 := hy 0
    have h1 := hy 1
    nlinarith [sq_nonneg (y 0 - y 1), mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (y 0 + y 1))
      (by linarith : (0 : ℝ) ≤ 6 - (y 0 + y 1))]
  · intro t _ y _
    have ha : ∀ j : Fin 2, HasFDerivAt (fun x : Fin 2 → ℝ => x j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j) y := fun j =>
      hasFDerivAt_apply j y
    have h1 := (ha 0).sub (((ha 0).mul (ha 0)).const_smul (1 / 4 : ℝ))
    have h2 := (ha 1).sub (((ha 1).mul (ha 1)).const_smul (1 / 4 : ℝ))
    have h := h1.add h2
    have e : c18InstU t = fun x : Fin 2 → ℝ =>
        x 0 - (1 / 4 : ℝ) • (x 0 * x 0) + (x 1 - (1 / 4 : ℝ) • (x 1 * x 1)) := by
      funext x; simp only [c18InstU, smul_eq_mul]; ring
    rw [e]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [c18InstD_apply]
    simp
    ring
  · intro ε hε
    refine ⟨ε, hε, fun t _ y y' _ _ hyy => ?_⟩
    refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_).trans hyy.le
    rw [show (c18InstD t y - c18InstD t y') v = c18InstD t y v - c18InstD t y' v from rfl,
      c18InstD_apply, c18InstD_apply, Real.norm_eq_abs]
    have h0 : |y 0 - y' 0| ≤ ‖y - y'‖ := by
      rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ 0
    have h1 : |y 1 - y' 1| ≤ ‖y - y'‖ := by
      rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ 1
    have v0 : |v 0| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    have v1 : |v 1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 1
    have e : (1 - y 0 / 2) * v 0 + (1 - y 1 / 2) * v 1 -
        ((1 - y' 0 / 2) * v 0 + (1 - y' 1 / 2) * v 1) =
        -((y 0 - y' 0) * v 0) / 2 - (y 1 - y' 1) * v 1 / 2 := by ring
    rw [e]
    calc |-((y 0 - y' 0) * v 0) / 2 - (y 1 - y' 1) * v 1 / 2|
        ≤ |y 0 - y' 0| * |v 0| / 2 + |y 1 - y' 1| * |v 1| / 2 := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_div, abs_neg, abs_mul, abs_mul, abs_two]
      _ ≤ ‖y - y'‖ * ‖v‖ / 2 + ‖y - y'‖ * ‖v‖ / 2 := by
          gcongr
      _ = ‖y - y'‖ * ‖v‖ := by ring
  · intro t _ v
    rw [hx, c18InstD_apply, c18_dot_two]
    simp
    ring
  · intro t _
    exact le_rfl
  · simp [Real.volume_Icc]
  · intro l
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    fin_cases l
    · simp only [c18InstZ, Fin.zero_eta, Matrix.cons_val_zero]
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
    · simp only [c18InstZ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const]
      simp [integral_id]

end MWG.CoreFoundations

set_option linter.style.longLine false
#print axioms MWG.CoreFoundations.CoreEconomy
#print axioms MWG.CoreFoundations.CoreEconomy.mk
#print axioms MWG.CoreFoundations.CoreEconomy.pref
#print axioms MWG.CoreFoundations.CoreEconomy.ω
#print axioms MWG.CoreFoundations.CoreEconomy.Y
#print axioms MWG.CoreFoundations.IsCRSTechnology
#print axioms MWG.CoreFoundations.CoreEconomy.Standing
#print axioms MWG.CoreFoundations.CoreEconomy.IsFeasible
#print axioms MWG.CoreFoundations.CoreEconomy.Blocks
#print axioms MWG.CoreFoundations.CoreEconomy.HasCoreProperty
#print axioms MWG.CoreFoundations.CoreEconomy.core
#print axioms MWG.CoreFoundations.CoreEconomy.IsWalrasEqm
#print axioms MWG.CoreFoundations.CoreEconomy.IsWalrasAlloc
#print axioms MWG.CoreFoundations.definition_18_B_1
#print axioms MWG.CoreFoundations.definition_18_B_2
#print axioms MWG.CoreFoundations.profit_eq_zero_of_max
#print axioms MWG.CoreFoundations.CoreEconomy.toPriv
#print axioms MWG.CoreFoundations.isWalrasEqm_iff_toPriv
#print axioms MWG.CoreFoundations.CoreEconomy.replica
#print axioms MWG.CoreFoundations.typeAlloc
#print axioms MWG.CoreFoundations.EqualTreatment
#print axioms MWG.CoreFoundations.CoreEconomy.CN
#print axioms MWG.CoreFoundations.equalTreatment_typeAlloc
#print axioms MWG.CoreFoundations.sqrtU
#print axioms MWG.CoreFoundations.sqrtEconomy
#print axioms MWG.CoreFoundations.isCRSTechnology_nonposOrthant
#print axioms MWG.CoreFoundations.continuous_sqrtU
#print axioms MWG.CoreFoundations.sqrtU_lt_of_le_of_ne
#print axioms MWG.CoreFoundations.sqrtU_strict_concave
#print axioms MWG.CoreFoundations.sqrtEconomy_standing
#print axioms MWG.CoreFoundations.proposition_18_B_1
#print axioms MWG.CoreFoundations.exercise_18_B_1
#print axioms MWG.CoreFoundations.proposition_18_B_1_exchange
#print axioms MWG.CoreFoundations.CoreEconomy.ParetoDominates
#print axioms MWG.CoreFoundations.CoreEconomy.IsParetoOptimal
#print axioms MWG.CoreFoundations.CoreEconomy.IsIndividuallyRational
#print axioms MWG.CoreFoundations.isParetoOptimal_iff_toPriv
#print axioms MWG.CoreFoundations.exists_strict_all_of_weak
#print axioms MWG.CoreFoundations.footnote_18_2
#print axioms MWG.CoreFoundations.core_not_strictly_dominated
#print axioms MWG.CoreFoundations.core_isParetoOptimal
#print axioms MWG.CoreFoundations.core_isIndividuallyRational
#print axioms MWG.CoreFoundations.isIndividuallyRational_iff_exchange
#print axioms MWG.CoreFoundations.figure_18_B_1
#print axioms MWG.CoreFoundations.sqrtU_two
#print axioms MWG.CoreFoundations.sqrtU_vec
#print axioms MWG.CoreFoundations.two_mul_sqrt_le
#print axioms MWG.CoreFoundations.sqrtEconomy_diag_isParetoOptimal
#print axioms MWG.CoreFoundations.exampleEndow
#print axioms MWG.CoreFoundations.exampleShare
#print axioms MWG.CoreFoundations.exampleAlloc
#print axioms MWG.CoreFoundations.two_sqrt_third_lt
#print axioms MWG.CoreFoundations.two_sqrt_two_thirds_lt
#print axioms MWG.CoreFoundations.exampleAlloc_ir
#print axioms MWG.CoreFoundations.exampleAlloc_mem_core
#print axioms MWG.CoreFoundations.exampleAlloc_not_walras
#print axioms MWG.CoreFoundations.converse_18_B_1_false
#print axioms MWG.CoreFoundations.fig18B2Coalition
#print axioms MWG.CoreFoundations.fig18B2Bundle
#print axioms MWG.CoreFoundations.figure_18_B_2
#print axioms MWG.CoreFoundations.figure_18_B_2_identity
#print axioms MWG.CoreFoundations.figure_18_B_2_identity_instance
#print axioms MWG.CoreFoundations.convex_upper_of_strictlyConvex
#print axioms MWG.CoreFoundations.exists_worst
#print axioms MWG.CoreFoundations.avg_pref
#print axioms MWG.CoreFoundations.avg_strict
#print axioms MWG.CoreFoundations.footnote_18_5
#print axioms MWG.CoreFoundations.proposition_18_B_2
#print axioms MWG.CoreFoundations.replica_isFeasible_typeAlloc
#print axioms MWG.CoreFoundations.core_replica_eq_typeAlloc
#print axioms MWG.CoreFoundations.CN_succ_subset
#print axioms MWG.CoreFoundations.isWalrasEqm_typeAlloc_iff
#print axioms MWG.CoreFoundations.walrasTypeAllocs_eq
#print axioms MWG.CoreFoundations.walras_mem_CN
#print axioms MWG.CoreFoundations.exercise_18_B_3
#print axioms MWG.CoreFoundations.replica_walras_equalTreatment
#print axioms MWG.CoreFoundations.ex18B2U
#print axioms MWG.CoreFoundations.ex18B2U_vec
#print axioms MWG.CoreFoundations.ex18B2Economy
#print axioms MWG.CoreFoundations.ex18B2Alloc
#print axioms MWG.CoreFoundations.ex18B2U_lt_of_le_of_ne
#print axioms MWG.CoreFoundations.ex18B2Economy_standing
#print axioms MWG.CoreFoundations.ex18B2_tu_bound
#print axioms MWG.CoreFoundations.ex18B2_util
#print axioms MWG.CoreFoundations.exercise_18_B_2a
#print axioms MWG.CoreFoundations.exercise_18_B_2b
#print axioms MWG.CoreFoundations.not_maximal_one_zero
#print axioms MWG.CoreFoundations.oneZero_mem_core
#print axioms MWG.CoreFoundations.dsEconomy
#print axioms MWG.CoreFoundations.proposition_18_B_3_false
#print axioms MWG.CoreFoundations.convex_strictUpper
#print axioms MWG.CoreFoundations.exists_type_combination
#print axioms MWG.CoreFoundations.exists_rounding
#print axioms MWG.CoreFoundations.sum_replica_filter
#print axioms MWG.CoreFoundations.disjoint_improving_trades
#print axioms MWG.CoreFoundations.proposition_18_B_3
#print axioms MWG.CoreFoundations.exists_favoured_type
#print axioms MWG.CoreFoundations.grad_dot_pos_of_proportional
#print axioms MWG.CoreFoundations.special_coalition_identity
#print axioms MWG.CoreFoundations.special_coalition_blocks
#print axioms MWG.CoreFoundations.special_nonneg_eventually
#print axioms MWG.CoreFoundations.exercise_18_B_4
#print axioms MWG.CoreFoundations.exercise_18_B_4_grad
#print axioms MWG.CoreFoundations.proposition_18_B_3_special_case
#print axioms MWG.CoreFoundations.coreVset
#print axioms MWG.CoreFoundations.coreV
#print axioms MWG.CoreFoundations.sum_endow_mem_coreV
#print axioms MWG.CoreFoundations.core_not_mem_interior_coreV
#print axioms MWG.CoreFoundations.supporting_price_isWalrasEqm
#print axioms MWG.CoreFoundations.supporting_price_needs_positive_endowment
#print axioms MWG.CoreFoundations.coreVset_not_convex
#print axioms MWG.CoreFoundations.shoeU
#print axioms MWG.CoreFoundations.shoeFeasible
#print axioms MWG.CoreFoundations.shoeParetoOptimal
#print axioms MWG.CoreFoundations.shoeMatched
#print axioms MWG.CoreFoundations.shoeBlocks
#print axioms MWG.CoreFoundations.shoeCore
#print axioms MWG.CoreFoundations.shoeWealth
#print axioms MWG.CoreFoundations.shoeWalras
#print axioms MWG.CoreFoundations.shoe_card_right
#print axioms MWG.CoreFoundations.shoe_card_left
#print axioms MWG.CoreFoundations.shoe_sum_u_le
#print axioms MWG.CoreFoundations.shoe_eq_one_of_sum_le
#print axioms MWG.CoreFoundations.shoe_paretoOptimal_iff
#print axioms MWG.CoreFoundations.exercise_18_B_5a
#print axioms MWG.CoreFoundations.shoe_matched_not_paretoOptimal
#print axioms MWG.CoreFoundations.exercise_18_B_5a_converse
#print axioms MWG.CoreFoundations.shoeExample
#print axioms MWG.CoreFoundations.shoe_paretoOptimal_not_matched
#print axioms MWG.CoreFoundations.exercise_18_B_5b
#print axioms MWG.CoreFoundations.shoeWalras_pR_pos
#print axioms MWG.CoreFoundations.exercise_18_B_5c
#print axioms MWG.CoreFoundations.shoePairs
#print axioms MWG.CoreFoundations.shoeEndow
#print axioms MWG.CoreFoundations.shoe_sum_ite_right
#print axioms MWG.CoreFoundations.shoe_sum_ite_left
#print axioms MWG.CoreFoundations.shoeWalras_pairs
#print axioms MWG.CoreFoundations.shoeWalras_endowment
#print axioms MWG.CoreFoundations.exercise_18_B_5d
#print axioms MWG.CoreFoundations.TradingModel
#print axioms MWG.CoreFoundations.TradingModel.mk
#print axioms MWG.CoreFoundations.TradingModel.P
#print axioms MWG.CoreFoundations.TradingModel.A
#print axioms MWG.CoreFoundations.TradingModel.ω
#print axioms MWG.CoreFoundations.TradingModel.g
#print axioms MWG.CoreFoundations.TradingModel.price
#print axioms MWG.CoreFoundations.TradingModel.u
#print axioms MWG.CoreFoundations.TradingModel.IsValid
#print axioms MWG.CoreFoundations.TradingModel.payoff
#print axioms MWG.CoreFoundations.TradingModel.IsTradingEqm
#print axioms MWG.CoreFoundations.footnote_18_7
#print axioms MWG.CoreFoundations.definition_18_C_1
#print axioms MWG.CoreFoundations.TradingModel.effBudget
#print axioms MWG.CoreFoundations.TradingModel.isTradingEqm_maximal_effBudget
#print axioms MWG.CoreFoundations.footnote_18_8
#print axioms MWG.CoreFoundations.price_insensitivity
#print axioms MWG.CoreFoundations.cournotModel
#print axioms MWG.CoreFoundations.cournotModel_isValid
#print axioms MWG.CoreFoundations.cournotModel_payoff
#print axioms MWG.CoreFoundations.cournot_sum_update
#print axioms MWG.CoreFoundations.example_18_C_1_walras
#print axioms MWG.CoreFoundations.example_18_C_1
#print axioms MWG.CoreFoundations.example_18_C_1_not_walrasian
#print axioms MWG.CoreFoundations.cournotStepSel
#print axioms MWG.CoreFoundations.example_18_C_1_instance
#print axioms MWG.CoreFoundations.partialOne
#print axioms MWG.CoreFoundations.partialTwo
#print axioms MWG.CoreFoundations.complementsPrice
#print axioms MWG.CoreFoundations.complementsModel
#print axioms MWG.CoreFoundations.complementsModel_isValid
#print axioms MWG.CoreFoundations.partialOne_axis_eq_zero
#print axioms MWG.CoreFoundations.partialTwo_axis_eq_zero
#print axioms MWG.CoreFoundations.complements_sum_update_zero
#print axioms MWG.CoreFoundations.example_18_C_2
#print axioms MWG.CoreFoundations.fn13GeomMean
#print axioms MWG.CoreFoundations.footnote_18_13_psi
#print axioms MWG.CoreFoundations.footnote_18_13_psi_concave
#print axioms MWG.CoreFoundations.footnote_18_13_prices
#print axioms MWG.CoreFoundations.footnote_18_13_discontinuous
#print axioms MWG.CoreFoundations.footnote_18_13_not_differentiable
#print axioms MWG.CoreFoundations.tpPrice
#print axioms MWG.CoreFoundations.tpGood
#print axioms MWG.CoreFoundations.tpMoney
#print axioms MWG.CoreFoundations.example_18_C_3_rule
#print axioms MWG.CoreFoundations.tp_continuous_sum_fst
#print axioms MWG.CoreFoundations.tp_continuous_sum_snd
#print axioms MWG.CoreFoundations.example_18_C_3_continuous
#print axioms MWG.CoreFoundations.tpLoneBid
#print axioms MWG.CoreFoundations.tp_continuous_loneBid
#print axioms MWG.CoreFoundations.tpPrice_loneBid
#print axioms MWG.CoreFoundations.example_18_C_3_no_continuous_price
#print axioms MWG.CoreFoundations.footnote_18_14
#print axioms MWG.CoreFoundations.TradingPostEconomy
#print axioms MWG.CoreFoundations.TradingPostEconomy.mk
#print axioms MWG.CoreFoundations.TradingPostEconomy.ωg
#print axioms MWG.CoreFoundations.TradingPostEconomy.ωm
#print axioms MWG.CoreFoundations.TradingPostEconomy.u
#print axioms MWG.CoreFoundations.TradingPostEconomy.FeasibleBid
#print axioms MWG.CoreFoundations.TradingPostEconomy.goodsOut
#print axioms MWG.CoreFoundations.TradingPostEconomy.moneyOut
#print axioms MWG.CoreFoundations.TradingPostEconomy.IsEqm
#print axioms MWG.CoreFoundations.tp_lone_bidder
#print axioms MWG.CoreFoundations.tp_all_zero
#print axioms MWG.CoreFoundations.example_18_C_3_inactive_post
#print axioms MWG.CoreFoundations.example_18_C_3_no_money
#print axioms MWG.CoreFoundations.tpBudget
#print axioms MWG.CoreFoundations.tp_update_sums
#print axioms MWG.CoreFoundations.tp_outcome
#print axioms MWG.CoreFoundations.exercise_18_C_1_one_sided
#print axioms MWG.CoreFoundations.tpFrontier
#print axioms MWG.CoreFoundations.tp_outcome_on_frontier
#print axioms MWG.CoreFoundations.tpFrontier_eq
#print axioms MWG.CoreFoundations.tpFrontier_strictConcaveOn
#print axioms MWG.CoreFoundations.tpFrontier_antitoneOn
#print axioms MWG.CoreFoundations.tpMaxBuy
#print axioms MWG.CoreFoundations.tp_reachable
#print axioms MWG.CoreFoundations.exercise_18_C_1_eq
#print axioms MWG.CoreFoundations.exercise_18_C_1_convex
#print axioms MWG.CoreFoundations.exercise_18_C_1_boundary
#print axioms MWG.CoreFoundations.CoreEconomy.IsSelfSelectiveWith
#print axioms MWG.CoreFoundations.CoreEconomy.IsSelfSelective
#print axioms MWG.CoreFoundations.CoreEconomy.NoEnvyNetTrades
#print axioms MWG.CoreFoundations.definition_18_D_1
#print axioms MWG.CoreFoundations.selfSelective_iff_netTrades
#print axioms MWG.CoreFoundations.misprintEconomy
#print axioms MWG.CoreFoundations.selfSelective_consumptions_misprint
#print axioms MWG.CoreFoundations.walras_isParetoOptimal_selfSelective
#print axioms MWG.CoreFoundations.fig18D2Endow
#print axioms MWG.CoreFoundations.fig18D2Alloc
#print axioms MWG.CoreFoundations.fig18D2_sqrt_sq
#print axioms MWG.CoreFoundations.figure_18_D_2
#print axioms MWG.CoreFoundations.pref_add_of_pref_endow
#print axioms MWG.CoreFoundations.exercise_18_D_1
#print axioms MWG.CoreFoundations.proposition_18_D_1_supported_eq
#print axioms MWG.CoreFoundations.proposition_18_D_1_equal_treatment
#print axioms MWG.CoreFoundations.proposition_18_D_1_single_net_trade
#print axioms MWG.CoreFoundations.proposition_18_D_1_smooth
#print axioms MWG.CoreFoundations.proposition_18_D_1_walrasian
#print axioms MWG.CoreFoundations.prop18D1D
#print axioms MWG.CoreFoundations.proposition_18_D_1_instance
#print axioms MWG.CoreFoundations.QLEconomy
#print axioms MWG.CoreFoundations.QLEconomy.mk
#print axioms MWG.CoreFoundations.QLEconomy.ψ
#print axioms MWG.CoreFoundations.QLEconomy.ω
#print axioms MWG.CoreFoundations.QLEconomy.u
#print axioms MWG.CoreFoundations.qlPrice
#print axioms MWG.CoreFoundations.QLEconomy.IsFeasible
#print axioms MWG.CoreFoundations.QLEconomy.welfare
#print axioms MWG.CoreFoundations.QLEconomy.valueSet
#print axioms MWG.CoreFoundations.QLEconomy.v
#print axioms MWG.CoreFoundations.QLEconomy.IsOptimal
#print axioms MWG.CoreFoundations.QLEconomy.IsMarginalProduct
#print axioms MWG.CoreFoundations.QLEconomy.IsWalrasEqm
#print axioms MWG.CoreFoundations.qlPrice_sum
#print axioms MWG.CoreFoundations.qlPrice_sub
#print axioms MWG.CoreFoundations.qlPrice_mono
#print axioms MWG.CoreFoundations.QLEconomy.valueSet_nonempty
#print axioms MWG.CoreFoundations.QLEconomy.welfare_le_of_majorant
#print axioms MWG.CoreFoundations.QLEconomy.v_le_of_majorant
#print axioms MWG.CoreFoundations.QLEconomy.bddAbove_of_majorant
#print axioms MWG.CoreFoundations.ql_clm_apply_eq_sum
#print axioms MWG.CoreFoundations.ql_hasDerivAt_line
#print axioms MWG.CoreFoundations.ql_fderiv_single_nonneg
#print axioms MWG.CoreFoundations.QLEconomy.exists_majorant
#print axioms MWG.CoreFoundations.QLEconomy.valueSet_smul
#print axioms MWG.CoreFoundations.QLEconomy.v_zero
#print axioms MWG.CoreFoundations.QLEconomy.v_smul
#print axioms MWG.CoreFoundations.QLEconomy.v_div
#print axioms MWG.CoreFoundations.ql_convex_bundles
#print axioms MWG.CoreFoundations.QLEconomy.u_concaveOn
#print axioms MWG.CoreFoundations.QLEconomy.v_superadditive
#print axioms MWG.CoreFoundations.exercise_18_E_1
#print axioms MWG.CoreFoundations.QLEconomy.IsFeasibleFinite
#print axioms MWG.CoreFoundations.qlTypeCount
#print axioms MWG.CoreFoundations.ql_sum_fiber
#print axioms MWG.CoreFoundations.footnote_18_20
#print axioms MWG.CoreFoundations.footnote_18_20_sSup
#print axioms MWG.CoreFoundations.ql_euler
#print axioms MWG.CoreFoundations.ql_partial_eq_of_le_linear
#print axioms MWG.CoreFoundations.ql_eventually_nonneg_line
#print axioms MWG.CoreFoundations.ql_sum_perturb
#print axioms MWG.CoreFoundations.QLEconomy.foc_of_optimal
#print axioms MWG.CoreFoundations.QLEconomy.isOptimal_iff
#print axioms MWG.CoreFoundations.QLEconomy.walras_price_nonneg
#print axioms MWG.CoreFoundations.QLEconomy.walras_budget_eq
#print axioms MWG.CoreFoundations.QLEconomy.walras_majorant
#print axioms MWG.CoreFoundations.QLEconomy.v_le_linear
#print axioms MWG.CoreFoundations.QLEconomy.partial_v_of_walras
#print axioms MWG.CoreFoundations.proposition_18_E_1_of_walras
#print axioms MWG.CoreFoundations.QLEconomy.supporting_prices
#print axioms MWG.CoreFoundations.exercise_18_E_2
#print axioms MWG.CoreFoundations.QLEconomy.walras_of_optimal_of_partial
#print axioms MWG.CoreFoundations.proposition_18_E_1
#print axioms MWG.CoreFoundations.ql_eventually_nonneg_of_pos
#print axioms MWG.CoreFoundations.QLEconomy.deltaV
#print axioms MWG.CoreFoundations.claim_18_E_deltaV_ge_partial
#print axioms MWG.CoreFoundations.claim_18_E_sum_deltaV_ge
#print axioms MWG.CoreFoundations.claim_18_E_no_full_marginal
#print axioms MWG.CoreFoundations.claim_18_E_no_full_marginal_finite
#print axioms MWG.CoreFoundations.claim_18_E_finite_walras_iff
#print axioms MWG.CoreFoundations.sqrtQLEconomy
#print axioms MWG.CoreFoundations.sqrtQL_concave
#print axioms MWG.CoreFoundations.sqrtQL_mono
#print axioms MWG.CoreFoundations.sqrtQL_differentiableAt
#print axioms MWG.CoreFoundations.sqrtQL_omega_nonneg
#print axioms MWG.CoreFoundations.sqrtQL_welfare_le
#print axioms MWG.CoreFoundations.sqrtQL_v
#print axioms MWG.CoreFoundations.qlOnes
#print axioms MWG.CoreFoundations.sqrtQL_v_differentiableAt
#print axioms MWG.CoreFoundations.sqrtQLStar
#print axioms MWG.CoreFoundations.ql_sqrt_half
#print axioms MWG.CoreFoundations.ql_sqrt_tangent
#print axioms MWG.CoreFoundations.sqrtQL_walras
#print axioms MWG.CoreFoundations.sqrtQL_partial
#print axioms MWG.CoreFoundations.definition_18_E_1_instance
#print axioms MWG.CoreFoundations.proposition_18_E_1_instance
#print axioms MWG.CoreFoundations.sqrtQL_optimal
#print axioms MWG.CoreFoundations.sqrtQL_v_concave
#print axioms MWG.CoreFoundations.sqrtQL_deltaV
#print axioms MWG.CoreFoundations.example_18_E_finite_strict
#print axioms MWG.CoreFoundations.example_18_E_no_full_marginal
#print axioms MWG.CoreFoundations.example_18_E_walras_below_delta
#print axioms MWG.CoreFoundations.example_18_E_finite_claims
#print axioms MWG.CoreFoundations.leontiefQLEconomy
#print axioms MWG.CoreFoundations.leontief_concave
#print axioms MWG.CoreFoundations.leontief_mono
#print axioms MWG.CoreFoundations.leontief_welfare_le
#print axioms MWG.CoreFoundations.leontief_v
#print axioms MWG.CoreFoundations.leontief_line
#print axioms MWG.CoreFoundations.exercise_18_E_3_left_deriv
#print axioms MWG.CoreFoundations.exercise_18_E_3_right_deriv
#print axioms MWG.CoreFoundations.exercise_18_E_3_not_differentiable
#print axioms MWG.CoreFoundations.exercise_18_E_3_delta
#print axioms MWG.CoreFoundations.exercise_18_E_3
#print axioms MWG.CoreFoundations.exercise_18_E_3_eqm
#print axioms MWG.CoreFoundations.exercise_18_E_3_boundary
#print axioms MWG.CoreFoundations.exercise_18_E_3_hypotheses
#print axioms MWG.CoreFoundations.qlShapleyGame
#print axioms MWG.CoreFoundations.claim_18_E_shapley_sum
#print axioms MWG.CoreFoundations.projS
#print axioms MWG.CoreFoundations.IsUtilityPossibilitySet
#print axioms MWG.CoreFoundations.extS
#print axioms MWG.CoreFoundations.projS_extS
#print axioms MWG.CoreFoundations.continuous_projS
#print axioms MWG.CoreFoundations.continuous_extS
#print axioms MWG.CoreFoundations.isUtilityPossibilitySet_iff
#print axioms MWG.CoreFoundations.NTUGame
#print axioms MWG.CoreFoundations.IsCharacteristicForm
#print axioms MWG.CoreFoundations.IsSuperadditive
#print axioms MWG.CoreFoundations.econGame
#print axioms MWG.CoreFoundations.econGame_comprehensive
#print axioms MWG.CoreFoundations.econGame_nonempty
#print axioms MWG.CoreFoundations.example_18_AA_1_convex
#print axioms MWG.CoreFoundations.example_18_AA_1_superadditive
#print axioms MWG.CoreFoundations.openConeTech
#print axioms MWG.CoreFoundations.openConeTech_isCRS
#print axioms MWG.CoreFoundations.example_18_AA_1_not_closed
#print axioms MWG.CoreFoundations.example_18_AA_1_closed
#print axioms MWG.CoreFoundations.votingGame
#print axioms MWG.CoreFoundations.votingGame_isCharacteristicForm
#print axioms MWG.CoreFoundations.votingGame_superadditive
#print axioms MWG.CoreFoundations.votingPayoffs
#print axioms MWG.CoreFoundations.example_18_AA_2_not_convex
#print axioms MWG.CoreFoundations.tuSet
#print axioms MWG.CoreFoundations.tuSet_isCharacteristicForm
#print axioms MWG.CoreFoundations.tuSet_superadditive_iff
#print axioms MWG.CoreFoundations.tuMajority
#print axioms MWG.CoreFoundations.example_18_AA_3
#print axioms MWG.CoreFoundations.ntuBlocks
#print axioms MWG.CoreFoundations.ntuCore
#print axioms MWG.CoreFoundations.tuCore
#print axioms MWG.CoreFoundations.tu_blocks_iff
#print axioms MWG.CoreFoundations.ntuCore_tuSet
#print axioms MWG.CoreFoundations.exercise_18_AA_2
#print axioms MWG.CoreFoundations.example_18_AA_4_tu
#print axioms MWG.CoreFoundations.example_18_AA_4_ntu
#print axioms MWG.CoreFoundations.example_18_AA_5
#print axioms MWG.CoreFoundations.example_18_AA_5_game_core
#print axioms MWG.CoreFoundations.example_18_AA_5_walras
#print axioms MWG.CoreFoundations.prodGame
#print axioms MWG.CoreFoundations.propAlloc
#print axioms MWG.CoreFoundations.propAlloc_sum
#print axioms MWG.CoreFoundations.example_18_AA_6
#print axioms MWG.CoreFoundations.example_18_AA_6_convex
#print axioms MWG.CoreFoundations.exercise_18_AA_3
#print axioms MWG.CoreFoundations.footnote_18_28
#print axioms MWG.CoreFoundations.footnote_18_28_core_empty
#print axioms MWG.CoreFoundations.IsGeneralizedPartition
#print axioms MWG.CoreFoundations.IsBalanced
#print axioms MWG.CoreFoundations.exercise_18_AA_1_singletons
#print axioms MWG.CoreFoundations.exercise_18_AA_1_pairs
#print axioms MWG.CoreFoundations.isBalanced_of_core
#print axioms MWG.CoreFoundations.bsGen
#print axioms MWG.CoreFoundations.dotProduct_snoc
#print axioms MWG.CoreFoundations.snoc_apply_castSucc
#print axioms MWG.CoreFoundations.snoc_apply_last
#print axioms MWG.CoreFoundations.core_nonempty_of_isBalanced
#print axioms MWG.CoreFoundations.exercise_18_AA_1
#print axioms MWG.CoreFoundations.subgame
#print axioms MWG.CoreFoundations.IsEgalitarianSolution
#print axioms MWG.CoreFoundations.isEgalitarianSolution_congr
#print axioms MWG.CoreFoundations.egalitarian_unique
#print axioms MWG.CoreFoundations.egalitarian_recursion
#print axioms MWG.CoreFoundations.egalitarian_pair
#print axioms MWG.CoreFoundations.shapleyFamily
#print axioms MWG.CoreFoundations.powerset_filter_not_mem
#print axioms MWG.CoreFoundations.shapleyFamily_isEgalitarian
#print axioms MWG.CoreFoundations.shapleyMWG
#print axioms MWG.CoreFoundations.definition_18_AA_7
#print axioms MWG.CoreFoundations.formula_18_AA_1
#print axioms MWG.CoreFoundations.formula_18_AA_3
#print axioms MWG.CoreFoundations.footnote_18_31
#print axioms MWG.CoreFoundations.sum_marginal_contributions
#print axioms MWG.CoreFoundations.dividend_subgame
#print axioms MWG.CoreFoundations.shapley_subgame
#print axioms MWG.CoreFoundations.subsetFormula
#print axioms MWG.CoreFoundations.hockey_stick
#print axioms MWG.CoreFoundations.shapley_weight_sum_nat
#print axioms MWG.CoreFoundations.shapley_weight_sum
#print axioms MWG.CoreFoundations.sub_erase_eq_sum_dividend
#print axioms MWG.CoreFoundations.subsetFormula_eq_shapleyFamily
#print axioms MWG.CoreFoundations.formula_18_AA_4
#print axioms MWG.CoreFoundations.exercise_18_AA_4
#print axioms MWG.CoreFoundations.shapley_efficiency
#print axioms MWG.CoreFoundations.RolesPermuted
#print axioms MWG.CoreFoundations.map_swap_of_iff
#print axioms MWG.CoreFoundations.map_swap_of_mem_notMem
#print axioms MWG.CoreFoundations.rolesPermuted_iff
#print axioms MWG.CoreFoundations.shapley_symmetry_footnote_33
#print axioms MWG.CoreFoundations.shapley_linearity
#print axioms MWG.CoreFoundations.shapley_dummy_axiom
#print axioms MWG.CoreFoundations.MWGSymmetric
#print axioms MWG.CoreFoundations.shapley_mwgSymmetric
#print axioms MWG.CoreFoundations.IsUnanimityGame
#print axioms MWG.CoreFoundations.isUnanimityGame_unanimity
#print axioms MWG.CoreFoundations.exercise_18_AA_5
#print axioms MWG.CoreFoundations.exercise_18_AA_6_decomposition
#print axioms MWG.CoreFoundations.exercise_18_AA_6_unique
#print axioms MWG.CoreFoundations.exercise_18_AA_6
#print axioms MWG.CoreFoundations.shapley_characterization
#print axioms MWG.CoreFoundations.gloveInt
#print axioms MWG.CoreFoundations.gloveGame
#print axioms MWG.CoreFoundations.example_18_AA_7_values
#print axioms MWG.CoreFoundations.gloveMarg
#print axioms MWG.CoreFoundations.example_18_AA_7_orderings
#print axioms MWG.CoreFoundations.gloveGame_empty
#print axioms MWG.CoreFoundations.gloveGame_swap
#print axioms MWG.CoreFoundations.example_18_AA_7
#print axioms MWG.CoreFoundations.example_18_AA_7_check
#print axioms MWG.CoreFoundations.sum_glove_core
#print axioms MWG.CoreFoundations.example_18_AA_7_core
#print axioms MWG.CoreFoundations.example_18_AA_7_block
#print axioms MWG.CoreFoundations.example_18_AA_7_shapley_not_core
#print axioms MWG.CoreFoundations.shapley_not_core_majority
#print axioms MWG.CoreFoundations.IsConvexGame
#print axioms MWG.CoreFoundations.marginal_vector_mem_core
#print axioms MWG.CoreFoundations.proposition_18_AA_1
#print axioms MWG.CoreFoundations.IncreasingDifferences
#print axioms MWG.CoreFoundations.inputGame
#print axioms MWG.CoreFoundations.exercise_18_AA_7
#print axioms MWG.CoreFoundations.convexOn_increasing_differences
#print axioms MWG.CoreFoundations.example_18_AA_8_one_input
#print axioms MWG.CoreFoundations.example_18_AA_8_one_input_deriv
#print axioms MWG.CoreFoundations.example_18_AA_8_not_sufficient
#print axioms MWG.CoreFoundations.example_18_AA_8_not_necessary
#print axioms MWG.CoreFoundations.maxTech
#print axioms MWG.CoreFoundations.maxGame
#print axioms MWG.CoreFoundations.exercise_18_AA_8
#print axioms MWG.CoreFoundations.v9Int
#print axioms MWG.CoreFoundations.game9
#print axioms MWG.CoreFoundations.game9mod
#print axioms MWG.CoreFoundations.exercise_18_AA_9_table
#print axioms MWG.CoreFoundations.game9_empty
#print axioms MWG.CoreFoundations.omega9
#print axioms MWG.CoreFoundations.exercise_18_AA_9a
#print axioms MWG.CoreFoundations.sum_alpha_alloc
#print axioms MWG.CoreFoundations.alpha_alloc_mem_core
#print axioms MWG.CoreFoundations.exercise_18_AA_9b
#print axioms MWG.CoreFoundations.exercise_18_AA_9c
#print axioms MWG.CoreFoundations.exercise_18_AA_9c_compare
#print axioms MWG.CoreFoundations.game9_perm_invariant
#print axioms MWG.CoreFoundations.exercise_18_AA_9d
#print axioms MWG.CoreFoundations.exercise_18_AA_9e
#print axioms MWG.CoreFoundations.exercise_18_AA_9e_compare
#print axioms MWG.CoreFoundations.costGame
#print axioms MWG.CoreFoundations.psi1
#print axioms MWG.CoreFoundations.psi2
#print axioms MWG.CoreFoundations.exercise_18_AA_10a
#print axioms MWG.CoreFoundations.exercise_18_AA_10b
#print axioms MWG.CoreFoundations.exercise_18_AA_10c_unbounded
#print axioms MWG.CoreFoundations.exercise_18_AA_10c_no_max
#print axioms MWG.CoreFoundations.exercise_18_AA_10c_foc
#print axioms MWG.CoreFoundations.const_of_hasDerivAt_zero_Ioi
#print axioms MWG.CoreFoundations.exercise_18_AA_10d
#print axioms MWG.CoreFoundations.c18Partial
#print axioms MWG.CoreFoundations.c18_eq_sum_single
#print axioms MWG.CoreFoundations.c18_clm_apply_eq_sum
#print axioms MWG.CoreFoundations.c18_partial_differentiableAt
#print axioms MWG.CoreFoundations.c18_hasDerivAt_line
#print axioms MWG.CoreFoundations.c18_line_mem
#print axioms MWG.CoreFoundations.c18_partial_mono
#print axioms MWG.CoreFoundations.c18_fderiv_mono
#print axioms MWG.CoreFoundations.example_18_AA_8_increasingDifferences
#print axioms MWG.CoreFoundations.exercise_18_AA_7_crossPartials
#print axioms MWG.CoreFoundations.c18_product_crossPartials
#print axioms MWG.CoreFoundations.exercise_18_AA_7_product
#print axioms MWG.CoreFoundations.c18NegSum
#print axioms MWG.CoreFoundations.c18NegSum_continuous
#print axioms MWG.CoreFoundations.c18NegSum_smul
#print axioms MWG.CoreFoundations.c18_cone_bounded
#print axioms MWG.CoreFoundations.example_18_AA_1_closed_cone
#print axioms MWG.CoreFoundations.example_18_AA_1_closed_crs
#print axioms MWG.CoreFoundations.c18HalfPlane
#print axioms MWG.CoreFoundations.c18HalfPlane_hyp
#print axioms MWG.CoreFoundations.example_18_AA_1_closed_halfPlane
#print axioms MWG.CoreFoundations.example_18_AA_1_free_production
#print axioms MWG.CoreFoundations.c18Profile
#print axioms MWG.CoreFoundations.c18TypeGame
#print axioms MWG.CoreFoundations.c18Box
#print axioms MWG.CoreFoundations.c18_card_profile_fiber
#print axioms MWG.CoreFoundations.c18_profile_mono
#print axioms MWG.CoreFoundations.c18_sum_powerset_profile
#print axioms MWG.CoreFoundations.c18_profile_insert
#print axioms MWG.CoreFoundations.c18_card_eq_sum_profile
#print axioms MWG.CoreFoundations.c18_profile_erase
#print axioms MWG.CoreFoundations.c18_shapley_sub_const
#print axioms MWG.CoreFoundations.c18_shapley_types
#print axioms MWG.CoreFoundations.c18_shapley_hypergeometric
#print axioms MWG.CoreFoundations.c18_hypergeometric_weights_sum
#print axioms MWG.CoreFoundations.c18BookFormula
#print axioms MWG.CoreFoundations.c18_book_formula_counterexample
#print axioms MWG.CoreFoundations.c18_abs_coord_le
#print axioms MWG.CoreFoundations.c18_dot_two
#print axioms MWG.CoreFoundations.c18_abs_sub_le_of_mem_uIcc
#print axioms MWG.CoreFoundations.c18_mem_uIcc_affine
#print axioms MWG.CoreFoundations.c18_planar_flat_const
#print axioms MWG.CoreFoundations.c18_flat_of_noEnvy
#print axioms MWG.CoreFoundations.c18_continuousOn_of_noEnvy
#print axioms MWG.CoreFoundations.proposition_18_D_1_continuum
#print axioms MWG.CoreFoundations.c18IsSelfSelective
#print axioms MWG.CoreFoundations.c18_isSelfSelective_iff_noEnvy
#print axioms MWG.CoreFoundations.c18IsMeasureFeasible
#print axioms MWG.CoreFoundations.c18IsMeasurePareto
#print axioms MWG.CoreFoundations.c18_integral_dot_eq_zero
#print axioms MWG.CoreFoundations.c18_isMeasurePareto_of_supported
#print axioms MWG.CoreFoundations.c18InstU
#print axioms MWG.CoreFoundations.c18InstOmega
#print axioms MWG.CoreFoundations.c18InstZ
#print axioms MWG.CoreFoundations.c18InstD
#print axioms MWG.CoreFoundations.c18InstD_apply
#print axioms MWG.CoreFoundations.c18InstU_mid
#print axioms MWG.CoreFoundations.proposition_18_D_1_continuum_instance
