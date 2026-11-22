/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Basic

/-!
# Excess demand: the shared definitions of Chapter 17 (MWG Section 17.B, pp. 579-583)

The shared vocabulary of the chapter.

* Price domains: the strictly positive orthant `ℝ^L_{++}` (`posOrthant`) and the unit simplex
  `Δ = {p ∈ ℝ^L_+ : ∑ₗ pₗ = 1}` (`priceSimplex`, Section 17.C).
* An *excess demand function* is any `z : ℝ^L → ℝ^L`; it is only ever evaluated at the prices
  where the book defines it. The five properties of **Proposition 17.B.2** are named
  separately, on `p ≫ 0`: (i) `EDContinuous`, (ii) `EDHomogeneous`, (iii) `EDWalrasLaw`,
  (iv) `EDBoundedBelow`, (v) `EDBoundary`. `IsStandardExcessDemand` bundles them.
  Property (v), "`Max {z₁(pⁿ), …, z_L(pⁿ)} → ∞`", is stated as: for every bound `M`,
  eventually some `zₗ(pⁿ) > M` (the maximum of finitely many numbers exceeds `M` iff one of
  them does), for sequences `pⁿ ≫ 0` with `pⁿ → p ≠ 0` and `pₗ = 0` for some `ℓ`.
* The consumers of an exchange economy are Chapter 15's `ExchangeEconomy` (utility `uᵢ`,
  consumption set `Xᵢ`, endowment `ωᵢ`) with Walrasian demand `E.demand i p`
  (`= x_i(p, p·ωᵢ)`). When demand is a singleton (strictly convex preferences),
  `demandFn E i p` is its element (**Definition 17.B.2**): `zᵢ(p) = xᵢ(p, p·ωᵢ) - ωᵢ`
  (`indivExcessDemand`) and `z(p) = ∑ᵢ zᵢ(p)` (`excessDemand`).
* `StandardUtility u`: the chapter's standing assumption (p. 581) for a consumer on
  `Xᵢ = ℝ^L_+`: preferences continuous, strictly convex and strongly monotone, for the
  utility representation `u` (continuous, strictly quasiconcave, strongly monotone).
* `IsEqmPrice z p`: `z(p) = 0` (17.B.2); `ẑ(p)`, the first `L - 1` excess demands
  (`truncExcessDemand`), and the claim of p. 582 that with `p ≫ 0` and Walras' law
  `z(p) = 0` iff `ẑ(p) = 0` (`eqm_iff_trunc_eq_zero`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open Filter Topology

variable {L : ℕ}

/-! ### Price domains -/

/-- The strictly positive orthant `ℝ^L_{++} = {p : pₗ > 0 for all ℓ}`, the domain of excess
demand in Chapter 17 (MWG, p. 581). -/
def posOrthant (L : ℕ) : Set (Fin L → ℝ) := {p | StrictlyPositive p}

/-- **Section 17.C** (MWG, p. 586). The unit simplex `Δ = {p ∈ ℝ^L_+ : ∑ₗ pₗ = 1}`. -/
def priceSimplex (L : ℕ) : Set (Fin L → ℝ) := {p | (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1}

/-- Membership in `ℝ^L_{++}`. -/
theorem mem_posOrthant {p : Fin L → ℝ} : p ∈ posOrthant L ↔ ∀ l, 0 < p l := Iff.rfl

/-- `ℝ^L_{++}` is open. -/
theorem isOpen_posOrthant (L : ℕ) : IsOpen (posOrthant L) := by
  have : posOrthant L = ⋂ l : Fin L, {p : Fin L → ℝ | 0 < p l} := by
    ext p; simp [posOrthant, StrictlyPositive]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)

/-- `ℝ^L_{++}` is closed under positive scaling. -/
theorem smul_mem_posOrthant {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {α : ℝ} (hα : 0 < α) :
    α • p ∈ posOrthant L := fun l => by simpa using mul_pos hα (hp l)

/-! ### Excess demand functions and the properties of Proposition 17.B.2 -/

/-- **Proposition 17.B.2(i)** (MWG, p. 582). `z` is continuous on `ℝ^L_{++}`. -/
def EDContinuous (z : (Fin L → ℝ) → Fin L → ℝ) : Prop := ContinuousOn z (posOrthant L)

/-- **Proposition 17.B.2(ii)** (MWG, p. 582). `z` is homogeneous of degree zero on `ℝ^L_{++}`. -/
def EDHomogeneous (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → z (α • p) = z p

/-- **Proposition 17.B.2(iii)** (MWG, p. 582). Walras' law: `p·z(p) = 0` for all `p ≫ 0`. -/
def EDWalrasLaw (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, p ⬝ᵥ z p = 0

/-- **Proposition 17.B.2(iv)** (MWG, p. 582). There is `s > 0` with `zₗ(p) > -s` for every
commodity `ℓ` and all `p ≫ 0`. -/
def EDBoundedBelow (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ p ∈ posOrthant L, ∀ l, -s < z p l

/-- **Proposition 17.B.2(v)** (MWG, p. 582), the boundary condition. If `pⁿ → p` with `pⁿ ≫ 0`,
`p ≠ 0` and `pₗ = 0` for some `ℓ`, then `Max {z₁(pⁿ), …, z_L(pⁿ)} → ∞`: for every `M`,
eventually some `zₗ(pⁿ)` exceeds `M`. -/
def EDBoundary (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ (ps : ℕ → Fin L → ℝ) (p : Fin L → ℝ), (∀ n, ps n ∈ posOrthant L) →
    Tendsto ps atTop (𝓝 p) → p ≠ 0 → (∃ l, p l = 0) →
    ∀ M : ℝ, ∀ᶠ n in atTop, ∃ l, M < z (ps n) l

/-- **Proposition 17.B.2** (MWG, p. 582). The five properties (i)-(v) of the aggregate excess
demand function of an exchange economy with strongly monotone preferences. -/
structure IsStandardExcessDemand (z : (Fin L → ℝ) → Fin L → ℝ) : Prop where
  /-- (i) continuity on `ℝ^L_{++}`. -/
  continuous : EDContinuous z
  /-- (ii) homogeneity of degree zero. -/
  homogeneous : EDHomogeneous z
  /-- (iii) Walras' law. -/
  walras : EDWalrasLaw z
  /-- (iv) excess supply is bounded. -/
  boundedBelow : EDBoundedBelow z
  /-- (v) the boundary condition. -/
  boundary : EDBoundary z

/-- **(17.B.2)** (MWG, p. 581). `p` is an equilibrium price vector of the excess demand
function `z`: `p ≫ 0` and `zₗ(p) = 0` for every `ℓ`. -/
def IsEqmPrice (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) : Prop :=
  p ∈ posOrthant L ∧ z p = 0

/-- **Section 17.B** (MWG, p. 582). For `L ≥ 1`, the vector `ẑ(p) = (z₁(p), …, z_{L-1}(p))` of
the first `L - 1` excess demands, indexed by `Fin (L - 1)` via `Fin.castSucc`. -/
def truncExcessDemand {n : ℕ} (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (p : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun l => z p (Fin.castSucc l)

/-- **Section 17.B** (MWG, p. 582). With Walras' law, a price vector `p ≫ 0` is an equilibrium
iff it clears the first `L - 1` markets: `z(p) = 0 ⟺ ẑ(p) = 0`. -/
theorem eqm_iff_trunc_eq_zero {n : ℕ} {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hW : EDWalrasLaw z) {p : Fin (n + 1) → ℝ} (hp : p ∈ posOrthant (n + 1)) :
    z p = 0 ↔ truncExcessDemand z p = 0 := by
  constructor
  · intro h
    funext l
    simp [truncExcessDemand, h]
  · intro h
    have hl : ∀ l : Fin n, z p (Fin.castSucc l) = 0 := fun l => congrFun h l
    have hw := hW p hp
    rw [dotProduct, Fin.sum_univ_castSucc] at hw
    simp only [hl, mul_zero, Finset.sum_const_zero, zero_add] at hw
    have hlast : z p (Fin.last n) = 0 :=
      (mul_eq_zero.mp hw).resolve_left (hp (Fin.last n)).ne'
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simpa using hlast
    · simpa using hl l

/-- Equilibrium prices of a homogeneous excess demand form a cone: positive multiples of an
equilibrium price vector are equilibrium price vectors (MWG, p. 581). -/
theorem IsEqmPrice.smul {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    {p : Fin L → ℝ} (hp : IsEqmPrice z p) {α : ℝ} (hα : 0 < α) : IsEqmPrice z (α • p) :=
  ⟨smul_mem_posOrthant hp.1 hα, by rw [hH p hp.1 α hα, hp.2]⟩

/-! ### Consumers and the excess demand of an exchange economy -/

/-- **Section 17.B** (MWG, p. 581). The chapter's standing assumptions on a consumer with
`Xᵢ = ℝ^L_+`, for a utility representation `u` of `≿ᵢ`: `≿ᵢ` is continuous (`u` continuous on
`ℝ^L_+`), strictly convex (`u` strictly quasiconcave on `ℝ^L_+`) and strongly monotone. -/
def StandardUtility (u : (Fin L → ℝ) → ℝ) : Prop :=
  ContinuousOn u (nonnegOrthant L) ∧ StrictlyQuasiconcaveOn (nonnegOrthant L) u ∧
    UtilityStronglyMonotone u

variable {ι : Type*}

/-- **Definition 17.B.2** (MWG, p. 581). Consumer `i`'s demand `xᵢ(p, p·ωᵢ)` as a function: the
element of the demand set when it is nonempty (it is a singleton under `StandardUtility`), and
`0` otherwise (a junk value, never used at prices where demand is empty). -/
noncomputable def demandFn (E : ExchangeEconomy ι L) (i : ι)
    (p : Fin L → ℝ) : Fin L → ℝ :=
  open Classical in if h : (E.demand i p).Nonempty then h.some else 0

/-- **Definition 17.B.2** (MWG, p. 581). Consumer `i`'s excess demand
`zᵢ(p) = xᵢ(p, p·ωᵢ) - ωᵢ`. -/
noncomputable def indivExcessDemand (E : ExchangeEconomy ι L) (i : ι)
    (p : Fin L → ℝ) : Fin L → ℝ :=
  demandFn E i p - E.ω i

/-- **Definition 17.B.2** (MWG, p. 581). The aggregate excess demand function
`z(p) = ∑ᵢ zᵢ(p)`. -/
noncomputable def excessDemand [Fintype ι] (E : ExchangeEconomy ι L) (p : Fin L → ℝ) :
    Fin L → ℝ :=
  ∑ i, indivExcessDemand E i p

/-- When consumer `i`'s demand set is nonempty, `demandFn` is demanded. -/
theorem demandFn_mem (E : ExchangeEconomy ι L) {i : ι} {p : Fin L → ℝ}
    (h : (E.demand i p).Nonempty) : demandFn E i p ∈ E.demand i p := by
  unfold demandFn
  simp only [h, ↓reduceDIte]
  exact h.some_mem

/-- When consumer `i`'s demand set is the singleton `{x}`, `demandFn` is `x`. -/
theorem demandFn_eq (E : ExchangeEconomy ι L) {i : ι} {p x : Fin L → ℝ}
    (h : E.demand i p = {x}) : demandFn E i p = x := by
  have hne : (E.demand i p).Nonempty := by rw [h]; exact Set.singleton_nonempty x
  have := demandFn_mem E hne
  rw [h] at this
  exact this

/-- The excess demand evaluated coordinatewise. -/
theorem excessDemand_apply [Fintype ι] (E : ExchangeEconomy ι L) (p : Fin L → ℝ)
    (l : Fin L) : excessDemand E p l = ∑ i, (demandFn E i p l - E.ω i l) := by
  simp [excessDemand, indivExcessDemand, Finset.sum_apply]

/-- The excess demand is aggregate demand minus the total endowment. -/
theorem excessDemand_eq [Fintype ι] (E : ExchangeEconomy ι L) (p : Fin L → ℝ) :
    excessDemand E p = ∑ i, demandFn E i p - E.totalEndowment := by
  simp [excessDemand, indivExcessDemand,
    ExchangeEconomy.totalEndowment, Finset.sum_sub_distrib]

end MWG.PositiveEquilibriumTheory
