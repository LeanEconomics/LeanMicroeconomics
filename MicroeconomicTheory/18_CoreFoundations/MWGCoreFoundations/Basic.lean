/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Replica
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

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
