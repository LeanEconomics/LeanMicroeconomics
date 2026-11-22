import MWGWelfareTheorems.Basic
import MWGChoiceUnderUncertainty.StateDependent
import MWGWelfareTheorems.FirstWelfare
import MWGWelfareTheorems.SecondWelfare
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MWGClassicalDemand.AppendixMG
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A market economy with contingent commodities (MWG Section 19.B, pp. 688-691)

States of the world are `Fin S`, physical commodities `Fin L`. A contingent commodity vector
`x ∈ ℝ^{LS}` (**Definition 19.B.1**) is `x : Fin S → Fin L → ℝ`, `x s l = x_{ls}`; the
state-`s` bundle `x s ∈ ℝ^L` is what is delivered if `s` occurs, and the value of `x` at
contingent prices `p` is `p·x = ∑_s p_s·x_s` (`cval`). The book's ordering
`(x₁₁, …, x_{L1}, …, x_{1S}, …, x_{LS})` is the state-major ordering used by `flat` in
`ArrowDebreu`.

* **Definition 19.B.1**: `contingentUnit`, the decomposition of a contingent vector into units,
  and the random-variable view of a contingent vector (`randomVar`).
* **Example 19.B.1**: expected-utility preferences over contingent vectors are rational; for
  `L = 1` they are Chapter 6's extended expected utility (Definition 6.E.2, footnote 2).
* **Example 19.B.2**: the seeds-and-crops technology; `(-1, 1, -1, 0)` is feasible and
  `(-1, 1, 0, 0)` is not.
* **Footnote 3**: commodities consumed before the resolution of uncertainty.
* **Shares (p. 689)**: the printed normalization `∑ⱼ θⱼᵢ = 1` for every consumer `i` is a
  misprint for `∑ᵢ θⱼᵢ = 1` for every firm `j` (correction 1, `shares_printed_normalization_fails`).
* **Small type, pp. 690-691**: information structures (partitions), increasingly fine families,
  **Example 19.B.3**, unique predecessors of date-events, and measurability with respect to a
  family of information partitions.
-/

namespace MWG.EquilibriumUncertainty

open MWG.ClassicalDemand

/-- **Definition 19.B.1** (MWG, p. 688). A contingent commodity vector `x ∈ ℝ^{LS}`:
`x s l = x_{ls}` is the amount of physical good `l` received if state `s` occurs. -/
abbrev CVec (S L : ℕ) := Fin S → Fin L → ℝ

variable {S L : ℕ}

/-- The value `p·x = ∑_s ∑_l p_{ls} x_{ls}` of a contingent commodity vector. -/
def cval (p x : CVec S L) : ℝ := ∑ s, p s ⬝ᵥ x s

/-- **Definition 19.B.1** (MWG, p. 688). One unit of the contingent commodity `ls`: a title to
one unit of good `l` if and only if state `s` occurs. -/
def contingentUnit (l : Fin L) (s : Fin S) : CVec S L :=
  fun s' l' => if s' = s ∧ l' = l then 1 else 0

/-- **Definition 19.B.1** (MWG, p. 688). A contingent commodity vector is the bundle of its
contingent commodities: `x = ∑_{l,s} x_{ls} · (unit ls)`. -/
theorem definition_19_B_1 (x : CVec S L) :
    x = ∑ s, ∑ l, x s l • contingentUnit l s := by
  funext s' l'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, contingentUnit]
  rw [Finset.sum_eq_single s']
  · rw [Finset.sum_eq_single l']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [Ne.symm hb]
  · simp

/-- **p. 688**. The `l`-th random variable `(x_{l1}, …, x_{lS})` of a contingent vector. -/
def randomVar (x : CVec S L) (l : Fin L) : Fin S → ℝ := fun s => x s l

/-- **p. 688**. A contingent vector is the collection of its `L` random variables. -/
theorem randomVar_ext {x x' : CVec S L} (h : ∀ l, randomVar x l = randomVar x' l) : x = x' :=
  funext fun s => funext fun l => congrFun (h l) s

/-- The nonnegative orthant `ℝ^{LS}_+`. -/
def NonnegC (x : CVec S L) : Prop := ∀ s l, 0 ≤ x s l

/-- The expected utility `∑_s π_s u_s(x_s)` of a contingent vector (Example 19.B.1). -/
def expUtil (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) (x : CVec S L) : ℝ :=
  ∑ s, π s * u s (x s)

/-- **Example 19.B.1** (MWG, p. 689). The ex ante preference `x ≿ x'` iff
`∑_s π_s u_s(x_s) ≥ ∑_s π_s u_s(x'_s)`. -/
def euPref (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) (x x' : CVec S L) : Prop :=
  expUtil π u x' ≤ expUtil π u x

/-- **Example 19.B.1** (MWG, p. 689). Expected-utility preferences over contingent commodity
vectors are complete and transitive (a rational preference relation). -/
theorem example_19_B_1 (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) :
    (∀ x x', euPref π u x x' ∨ euPref π u x' x) ∧
      ∀ x x' x'', euPref π u x x' → euPref π u x' x'' → euPref π u x x'' :=
  ⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h2 h1⟩

/-- **Footnote 2** (MWG, p. 689). For `L = 1` the preference of Example 19.B.1 is Chapter 6's
extended expected utility representation (Definition 6.E.2) on `ℝ^S_+`. -/
theorem footnote_19_2 (π : Fin S → ℝ) (u : Fin S → (Fin 1 → ℝ) → ℝ) :
    MWG.ChoiceUnderUncertainty.HasExtendedEU π
      (fun a b => euPref π u (fun s _ => a s) (fun s _ => b s)) :=
  ⟨fun s t => u s (fun _ => t), fun _ _ _ _ => Iff.rfl⟩

/-! ## Example 19.B.2: seeds and crops -/

/-- **Example 19.B.2** (MWG, p. 689). With states `s₁` (good weather, index `0`) and `s₂`
(bad, index `1`) and goods seeds (index `0`) and crops (index `1`), the plans of the
technology plant `a ≥ 0` seeds in both states and harvest `a` crops in the good state only. -/
def seedsTech : Set (CVec 2 2) :=
  {y | ∃ a : ℝ, 0 ≤ a ∧ y = fun s l => if l = 0 then -a else if s = 0 then a else 0}

/-- The plan `(y₁₁, y₂₁, y₁₂, y₂₂)` as a contingent vector. -/
def plan2 (a b c d : ℝ) : CVec 2 2 := fun s l => if s = 0 then (if l = 0 then a else b)
  else (if l = 0 then c else d)

/-- **Example 19.B.2** (MWG, p. 689). `(-1, 1, -1, 0)` is a feasible plan, while
`(-1, 1, 0, 0)` is not: seeds are planted before the weather is known. -/
theorem example_19_B_2 : plan2 (-1) 1 (-1) 0 ∈ seedsTech ∧ plan2 (-1) 1 0 0 ∉ seedsTech := by
  refine ⟨⟨1, zero_le_one, ?_⟩, ?_⟩
  · funext s l
    fin_cases s <;> fin_cases l <;> simp [plan2]
  · rintro ⟨a, _, h⟩
    have h1 := congrFun (congrFun h 0) 0
    have h2 := congrFun (congrFun h 1) 0
    simp [plan2] at h1 h2
    linarith

/-- **Footnote 3** (MWG, p. 689). Good `l` is consumed before the resolution of uncertainty
when every `x ∈ X` has equal entries `x_{ls}` across states. -/
def ConsumedExAnte (X : Set (CVec S L)) (l : Fin L) : Prop :=
  ∀ x ∈ X, ∀ s s', x s l = x s' l

/-! ## Ownership shares -/

/-- **p. 689**, corrected. Shares `θ j i ≥ 0` of firm `j` owned by consumer `i`: every firm is
fully owned, `∑ᵢ θⱼᵢ = 1` for every `j`. -/
def SharesValid {ι κ : Type*} [Fintype ι] (θ : κ → ι → ℝ) : Prop :=
  (∀ j i, 0 ≤ θ j i) ∧ ∀ j, ∑ i, θ j i = 1

/-- **p. 689** (correction 1). The printed normalization `∑ⱼ θⱼᵢ = 1` for every `i` fails for
valid shares: one firm owned half-and-half by two consumers. -/
theorem shares_printed_normalization_fails :
    SharesValid (fun (_ : Fin 1) (_ : Fin 2) => (1 / 2 : ℝ)) ∧
      ∃ i : Fin 2, ∑ j : Fin 1, (fun (_ : Fin 1) (_ : Fin 2) => (1 / 2 : ℝ)) j i ≠ 1 := by
  refine ⟨⟨fun _ _ => by norm_num, fun _ => by simp⟩, 0, by simp⟩

/-! ## Information structures (small type, pp. 690-691) -/

/-- **p. 690**. An information structure: a partition of the states into events (every state is
in some event, and distinct events are disjoint). -/
def IsInfoStructure {Ω : Type*} [DecidableEq Ω] (P : Finset (Finset Ω)) : Prop :=
  (∀ s, ∃ E ∈ P, s ∈ E) ∧ ∀ E ∈ P, ∀ E' ∈ P, E ≠ E' → Disjoint E E'

/-- **p. 690**. `P'` is at least as fine as `P`: every nonempty event of `P'` lies in an event
of `P` (information is not forgotten). -/
def Refines {Ω : Type*} (P' P : Finset (Finset Ω)) : Prop :=
  ∀ E' ∈ P', E'.Nonempty → ∃ E ∈ P, E' ⊆ E

/-- **p. 690**. A family of information structures `(𝒮₀, …, 𝒮_T)` that becomes increasingly
fine. -/
def IsInfoFamily {Ω : Type*} [DecidableEq Ω] {T : ℕ} (F : Fin (T + 1) → Finset (Finset Ω)) :
    Prop :=
  (∀ t, IsInfoStructure (F t)) ∧ ∀ t : Fin T, Refines (F t.succ) (F t.castSucc)

/-- **Example 19.B.3** (MWG, p. 691), states `1, …, 6` as `0, …, 5`: the partitions of the tree
of Figure 19.B.2. -/
def example19B3 : Fin 3 → Finset (Finset (Fin 6)) :=
  ![{Finset.univ}, {{0, 1}, {2}, {3, 4, 5}}, {{0}, {1}, {2}, {3}, {4}, {5}}]

set_option maxRecDepth 100000 in
/-- **Example 19.B.3** (MWG, p. 691). The three partitions form an increasingly fine family of
information structures. -/
theorem example_19_B_3 : IsInfoFamily (T := 2) example19B3 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · unfold IsInfoStructure
    fin_cases t <;> decide
  · unfold Refines
    fin_cases t <;> decide

/-- **p. 691**. Each date-event other than the first has a unique predecessor: a nonempty
event of a finer information structure lies in exactly one event of the coarser one. -/
theorem unique_predecessor {Ω : Type*} [DecidableEq Ω] {P P' : Finset (Finset Ω)}
    (hP : IsInfoStructure P) (href : Refines P' P) {E' : Finset Ω} (hE' : E' ∈ P')
    (hne : E'.Nonempty) : ∃! E, E ∈ P ∧ E' ⊆ E := by
  obtain ⟨E, hE, hsub⟩ := href E' hE' hne
  refine ⟨E, ⟨hE, hsub⟩, fun E2 ⟨hE2, hsub2⟩ => ?_⟩
  by_contra hne2
  obtain ⟨s, hs⟩ := hne
  exact Finset.disjoint_left.mp (hP.2 E2 hE2 E hE hne2) (hsub2 hs) (hsub hs)

/-- **p. 691**. A double-indexed vector `z_{(ht)s}` (`H` basic goods, dates `0, …, T`) is
measurable with respect to the family `(𝒮₀, …, 𝒮_T)`: amounts at date `t` agree across states
that cannot be distinguished at `t`. -/
def IsMeasurable {Ω : Type*} {H T : ℕ} (F : Fin (T + 1) → Finset (Finset Ω))
    (z : Fin H → Fin (T + 1) → Ω → ℝ) : Prop :=
  ∀ h t s s', (∃ E ∈ F t, s ∈ E ∧ s' ∈ E) → z h t s = z h t s'

/-- **p. 691**. In the tree of Example 19.B.3, a measurable vector cannot assign different
date-0 amounts to two states, nor different date-1 amounts to states 1 and 2. -/
theorem example_19_B_3_measurable {H : ℕ} {z : Fin H → Fin 3 → Fin 6 → ℝ}
    (hz : IsMeasurable (T := 2) example19B3 z) (h : Fin H) :
    (∀ s s', z h 0 s = z h 0 s') ∧ z h 1 0 = z h 1 1 :=
  ⟨fun s s' => hz h 0 s s' ⟨Finset.univ, by simp [example19B3]⟩,
    hz h 1 0 1 ⟨{0, 1}, by simp [example19B3], by simp⟩⟩

/-! ## Monotonicity on contingent vectors -/

/-- Strong monotonicity of a utility on `ℝ^{LS}_+`: `x ≤ x'`, `x ≠ x'` imply `U(x) < U(x')`. -/
def StronglyMonotoneC (U : CVec S L → ℝ) : Prop :=
  ∀ x x', NonnegC x → x ≤ x' → x ≠ x' → U x < U x'

/-- Strong monotonicity on `ℝ^L_+`. -/
def StronglyMonotoneL (u : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ a b : Fin L → ℝ, (∀ l, 0 ≤ a l) → a ≤ b → a ≠ b → u a < u b

/-- **p. 703**. Expected utility with strictly positive probabilities and strongly monotone
Bernoulli utilities is strongly monotone (the example of strongly monotone preferences given
after Lemma 19.E.1). -/
theorem expUtil_stronglyMonotone {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin L → ℝ) → ℝ} (hu : ∀ s, StronglyMonotoneL (u s)) :
    StronglyMonotoneC (expUtil π u) := by
  intro x x' hx hle hne
  have hle' : ∀ s, u s (x s) ≤ u s (x' s) := by
    intro s
    by_cases h : x s = x' s
    · rw [h]
    · exact (hu s (x s) (x' s) (hx s) (hle s) h).le
  obtain ⟨s0, hs0⟩ : ∃ s, x s ≠ x' s := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  unfold expUtil
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle' s) (hπ s).le)
    ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hu s0 _ _ (hx s0) (hle s0) hs0) (hπ s0)⟩

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Arrow-Debreu equilibrium (MWG Section 19.C, pp. 691-693)

An economy with uncertainty (`CEconomy`) has consumption sets `Xᵢ ⊆ ℝ^{LS}`, preferences `≿ᵢ`,
endowments `ωᵢ ∈ ℝ^{LS}`, production sets `Yⱼ ⊆ ℝ^{LS}` and shares `θⱼᵢ`.

* **Definition 19.C.1**: Arrow-Debreu equilibrium (`CEconomy.IsADEqm`).
* An Arrow-Debreu equilibrium *is* a Walrasian equilibrium (Definition 16.B.3) of the economy
  with the `LS` contingent commodities, ordered as in Definition 19.B.1 (`flat`, `unflat`,
  `isADEqm_iff_isWalrasEqm`). Through this bridge the welfare theorems of Chapter 16 apply
  without modification (p. 692): `adEqm_paretoOptimal` (Proposition 16.C.1) and
  `paretoOptimal_supported` (Proposition 16.D.1).
* Exchange economies with utility functions on `ℝ^{LS}_+` (`IsADEqmU`, used from Section 19.D
  on) are the case of no firms (`isADEqmU_iff`).
* **Exercise 19.C.1** and the claim of p. 692: concave Bernoulli utilities give a concave
  expected utility on `ℝ^{LS}_+`, hence convex preferences (`exercise_19_C_1`,
  `euPref_convex`).
* The instance: expected utility with strictly positive probabilities and strongly monotone
  Bernoulli utilities is rational and locally nonsatiated, so Arrow-Debreu equilibria of such
  economies are Pareto optimal (`adEqm_paretoOptimal_eu`).
-/

namespace MWG.EquilibriumUncertainty

open MWG.ClassicalDemand MWG.ConsumerChoice MWG.Production MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {S L : ℕ}

/-! ## Ordering the contingent commodities -/

/-- The contingent vector as a vector of `ℝ^{LS}` with the book's ordering
`(x₁₁, …, x_{L1}, …, x_{1S}, …, x_{LS})` (Definition 19.B.1). -/
def flat (x : CVec S L) : Fin (S * L) → ℝ :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The inverse of `flat`. -/
def unflat (v : Fin (S * L) → ℝ) : CVec S L := fun s l => v (finProdFinEquiv (s, l))

theorem unflat_flat (x : CVec S L) : unflat (flat x) = x := by
  funext s l; simp [unflat, flat]

theorem flat_unflat (v : Fin (S * L) → ℝ) : flat (unflat v) = v := by
  funext k; simp only [unflat, flat]; rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem flat_injective : Function.Injective (flat (S := S) (L := L)) := fun a b h => by
  rw [← unflat_flat a, h, unflat_flat]

/-- The value `p·x` is the dot product in `ℝ^{LS}`. -/
theorem flat_dotProduct (p x : CVec S L) : flat p ⬝ᵥ flat x = cval p x := by
  unfold dotProduct cval flat
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [dotProduct]

theorem flat_add (x y : CVec S L) : flat (x + y) = flat x + flat y := rfl

theorem flat_smul (a : ℝ) (x : CVec S L) : flat (a • x) = a • flat x := rfl

theorem flat_sum {ι : Type*} (t : Finset ι) (x : ι → CVec S L) :
    flat (∑ i ∈ t, x i) = ∑ i ∈ t, flat (x i) := by
  funext k; simp [flat, Finset.sum_apply]

theorem unflat_add (v w : Fin (S * L) → ℝ) : unflat (v + w) = unflat v + unflat w := rfl

theorem unflat_smul (a : ℝ) (v : Fin (S * L) → ℝ) : unflat (a • v) = a • unflat v := rfl

/-! ## The economy and Definition 19.C.1 -/

/-- **Sections 19.B-19.C** (MWG, pp. 688-691). An economy under uncertainty: consumption sets
`Xᵢ ⊆ ℝ^{LS}`, preference relations (`pref i x x'` reads `x ≿ᵢ x'`), endowments `ωᵢ ∈ ℝ^{LS}`,
production sets `Yⱼ ⊆ ℝ^{LS}` and shares `θ j i` of firm `j` owned by consumer `i`. -/
structure CEconomy (ι κ : Type*) (S L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (CVec S L)
  /-- Preference relations. -/
  pref : ι → CVec S L → CVec S L → Prop
  /-- Endowments. -/
  ω : ι → CVec S L
  /-- Production sets. -/
  Y : κ → Set (CVec S L)
  /-- Shares: `θ j i` is the share of firm `j` owned by consumer `i`. -/
  θ : κ → ι → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θⱼᵢ p·yⱼ`. -/
def CEconomy.wealth (E : CEconomy ι κ S L) (y : κ → CVec S L) (p : CVec S L) (i : ι) : ℝ :=
  cval p (E.ω i) + ∑ j, E.θ j i * cval p (y j)

/-- **Definition 19.C.1** (MWG, p. 692). `(x*, y*)` and contingent prices `p ∈ ℝ^{LS}` form an
Arrow-Debreu equilibrium: (i) every `y*ⱼ` maximizes `p·yⱼ` on `Yⱼ`; (ii) every `x*ᵢ` is maximal
for `≿ᵢ` in `{xᵢ ∈ Xᵢ : p·xᵢ ≤ p·ωᵢ + ∑ⱼ θⱼᵢ p·y*ⱼ}`; (iii) `∑ᵢ x*ᵢ = ∑ⱼ y*ⱼ + ∑ᵢ ωᵢ`. -/
def CEconomy.IsADEqm (E : CEconomy ι κ S L) (x : ι → CVec S L) (y : κ → CVec S L)
    (p : CVec S L) : Prop :=
  (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, cval p y' ≤ cval p (y j)) ∧
    (∀ i, (x i ∈ E.X i ∧ cval p (x i) ≤ E.wealth y p i) ∧
      ∀ x' ∈ E.X i, cval p x' ≤ E.wealth y p i → E.pref i (x i) x') ∧
    ∑ i, x i = ∑ j, y j + ∑ i, E.ω i

/-- **p. 691**. The economy with the `LS` contingent commodities as an ordinary private ownership
economy of Chapter 16 (`L` there is `LS` here). -/
def CEconomy.toPriv (E : CEconomy ι κ S L) : PrivPrefEconomy ι κ (S * L) where
  X := fun i => unflat ⁻¹' E.X i
  pref := fun i a b => E.pref i (unflat a) (unflat b)
  Y := fun j => unflat ⁻¹' E.Y j
  ωi := fun i => flat (E.ω i)
  θ := fun i j => E.θ j i

/-- The allocation `(x, y)` in `ℝ^{LS}`. -/
def flatAlloc (x : ι → CVec S L) (y : κ → CVec S L) : Allocation ι κ (S * L) :=
  ⟨fun i => flat (x i), fun j => flat (y j)⟩

/-- **p. 692**. "The market economy just described is nothing but a particular case of the
economies we have studied": an Arrow-Debreu equilibrium is exactly a Walrasian equilibrium
(Definition 16.B.3) of the economy with `LS` contingent commodities. -/
theorem isADEqm_iff_isWalrasEqm (E : CEconomy ι κ S L) (x : ι → CVec S L)
    (y : κ → CVec S L) (p : CVec S L) :
    E.IsADEqm x y p ↔ E.toPriv.IsWalrasEqm (flatAlloc x y) (flat p) := by
  have hw : ∀ i, E.toPriv.wealth (flatAlloc x y) (flat p) i = E.wealth y p i := by
    intro i
    simp [PrivPrefEconomy.wealth, CEconomy.wealth, CEconomy.toPriv, flatAlloc,
      flat_dotProduct]
  rw [definition_16_B_3]
  simp only [hw]
  have hall : ∀ (P : (Fin (S * L) → ℝ) → Prop), (∀ v, P v) ↔ ∀ z : CVec S L, P (flat z) :=
    fun P => ⟨fun h z => h _, fun h v => by rw [← flat_unflat v]; exact h _⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [CEconomy.toPriv, flatAlloc, Set.mem_preimage, unflat_flat]; exact (h1 j).1
    · rw [hall]; intro z hz
      simp only [CEconomy.toPriv, Set.mem_preimage, unflat_flat] at hz
      simp only [flatAlloc, flat_dotProduct]; exact (h1 j).2 z hz
    · simp only [CEconomy.toPriv, flatAlloc, Set.mem_preimage, unflat_flat]
      exact (h2 i).1.1
    · simp only [flatAlloc, flat_dotProduct]; exact (h2 i).1.2
    · rw [hall]; intro z hz hb
      simp only [CEconomy.toPriv, Set.mem_preimage, unflat_flat, flatAlloc] at hz ⊢
      rw [flat_dotProduct] at hb
      exact (h2 i).2 z hz hb
    · simp only [flatAlloc, CEconomy.toPriv, ← flat_sum, ← flat_add]; rw [h3, add_comm]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨?_, fun y' hy' => ?_⟩, fun i => ⟨⟨?_, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
    · have := (h1 j).1
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · have := (h1 j).2 (flat y') (by simpa [CEconomy.toPriv, unflat_flat] using hy')
      simpa [flatAlloc, flat_dotProduct] using this
    · have := (h2 i).1.1
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · have := (h2 i).1.2
      simpa [flatAlloc, flat_dotProduct] using this
    · have := (h2 i).2 (flat x') (by simpa [CEconomy.toPriv, unflat_flat] using hx')
        (by rw [flat_dotProduct]; exact hb)
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · apply flat_injective
      simp only [flatAlloc, CEconomy.toPriv] at h3
      rw [flat_add, flat_sum, flat_sum, flat_sum, h3, add_comm]

/-- **Definition 16.B.2** for the contingent economy: Pareto optimality of `(x, y)` in `ℝ^{LS}`. -/
def CEconomy.IsParetoOptimal (E : CEconomy ι κ S L) (x : ι → CVec S L) (y : κ → CVec S L) :
    Prop :=
  E.toPriv.toEconomy.IsParetoOptimal (flatAlloc x y)

/-- **p. 692** (Proposition 16.C.1 applied). With rational, locally nonsatiated preferences and
shares summing to one, every Arrow-Debreu equilibrium allocation is Pareto optimal: trading in
contingent commodities leads to an efficient allocation of risk. -/
theorem adEqm_paretoOptimal {E : CEconomy ι κ S L}
    (hrat : ∀ i, RationalOn (E.toPriv.X i) (E.toPriv.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.toPriv.X i) (E.toPriv.pref i))
    (hθ : ∀ j, ∑ i, E.θ j i = 1) {x : ι → CVec S L} {y : κ → CVec S L} {p : CVec S L}
    (h : E.IsADEqm x y p) : E.IsParetoOptimal x y :=
  proposition_16_C_1_walras hrat hlns hθ ((isADEqm_iff_isWalrasEqm E x y p).mp h)

/-- **p. 692** (Proposition 16.D.1 applied). With convex production sets and rational, convex,
locally nonsatiated preferences, every Pareto optimal allocation is supported by contingent prices
`p ≠ 0` as a price quasiequilibrium with transfers (wealth levels `p·x*ᵢ`). -/
theorem paretoOptimal_supported [Nonempty ι] {E : CEconomy ι κ S L}
    (hY : ∀ j, Convex ℝ (E.toPriv.Y j)) (hrat : ∀ i, RationalOn (E.toPriv.X i) (E.toPriv.pref i))
    (hc : ∀ i, PrefConvex (E.toPriv.X i) (E.toPriv.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.toPriv.X i) (E.toPriv.pref i))
    {x : ι → CVec S L} {y : κ → CVec S L} (hpo : E.IsParetoOptimal x y) :
    ∃ p : CVec S L, p ≠ 0 ∧ E.toPriv.toEconomy.IsPriceQuasiEqmWithTransfers (flatAlloc x y)
      (flat p) (fun i => cval p (x i)) := by
  obtain ⟨v, hv, hq⟩ := proposition_16_D_1 (E := E.toPriv.toEconomy) hY hrat hc hlns hpo
  refine ⟨unflat v, fun h0 => hv ?_, ?_⟩
  · rw [← flat_unflat v, h0]; rfl
  · simp only [flat_unflat]
    convert hq using 2
    rename_i i
    rw [← flat_dotProduct, flat_unflat]; rfl

/-! ## Exchange economies with utility functions -/

/-- **Definition 19.C.1** for an exchange economy (no firms) with consumption sets `ℝ^{LS}_+` and
utility functions `Uᵢ`: `x*ᵢ` maximizes `Uᵢ` on `{xᵢ ≥ 0 : p·xᵢ ≤ p·ωᵢ}` and `∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`. -/
def IsADEqmU (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L) (p : CVec S L) :
    Prop :=
  (∀ i, (NonnegC (x i) ∧ cval p (x i) ≤ cval p (ω i)) ∧
    ∀ x', NonnegC x' → cval p x' ≤ cval p (ω i) → U i x' ≤ U i (x i)) ∧
    ∑ i, x i = ∑ i, ω i

/-- The exchange economy `({ℝ^{LS}_+, Uᵢ, ωᵢ})` with no firms. -/
def exchangeCE (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) : CEconomy ι (Fin 0) S L where
  X := fun _ => {x | NonnegC x}
  pref := fun i a b => U i b ≤ U i a
  ω := ω
  Y := fun _ => ∅
  θ := fun _ _ => 0

/-- `IsADEqmU` is Definition 19.C.1 for the exchange economy with no firms. -/
theorem isADEqmU_iff (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L)
    (p : CVec S L) : IsADEqmU U ω x p ↔ (exchangeCE U ω).IsADEqm x Fin.elim0 p := by
  simp [IsADEqmU, CEconomy.IsADEqm, exchangeCE, CEconomy.wealth]

/-! ## Convexity and Exercise 19.C.1 -/

/-- **Exercise 19.C.1** (MWG, p. 725). If every Bernoulli utility `u_s` is concave on `ℝ^L_+`
(and `π ≥ 0`), the expected utility `∑_s π_s u_s(x_s)` is concave on `ℝ^{LS}_+`. -/
theorem exercise_19_C_1 {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) :
    ConcaveOn ℝ {x : CVec S L | NonnegC x} (expUtil π u) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb _ s l
    have := hx s l; have := hy s l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro x hx y hy a b ha hb hab
    simp only [expUtil, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := (hu s).2 (hx s) (hy s) ha hb hab
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at h ⊢
    have h' : a * u s (x s) + b * u s (y s) ≤ u s (a • x s + b • y s) := h
    calc a * (π s * u s (x s)) + b * (π s * u s (y s))
        = π s * (a * u s (x s) + b * u s (y s)) := by ring
      _ ≤ π s * u s (a • x s + b • y s) := mul_le_mul_of_nonneg_left h' (hπ s)
      _ = π s * u s ((a • x + b • y) s) := rfl

/-- **p. 692** (Sections 6.C and 6.E recalled). With concave Bernoulli utilities the
expected-utility preference of Example 19.B.1 is convex: its upper contour sets in `ℝ^{LS}_+` are
convex. -/
theorem euPref_convex {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) (x : CVec S L) :
    Convex ℝ {x' : CVec S L | NonnegC x' ∧ euPref π u x' x} :=
  (exercise_19_C_1 hπ hu).convex_ge (expUtil π u x)

/-- The convexity of `euPref_convex` in Chapter 3's sense on `ℝ^{LS}` (`PrefConvex`). -/
theorem euPref_prefConvex {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) :
    PrefConvex (unflat ⁻¹' {x : CVec S L | NonnegC x})
      (fun a b => euPref π u (unflat a) (unflat b)) := by
  intro v _ a ha b hb α β hα hβ hαβ
  have h := euPref_convex hπ hu (unflat v) ⟨ha.1, ha.2⟩ ⟨hb.1, hb.2⟩ hα hβ hαβ
  exact ⟨h.1, h.2⟩

/-! ## The expected-utility instance of the welfare theorem -/

/-- With `S, L ≥ 1`, strictly positive probabilities and strongly monotone Bernoulli utilities,
the expected-utility preference on `ℝ^{LS}_+` is rational and locally nonsatiated. -/
theorem euPref_rational_lns [NeZero S] [NeZero L] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin L → ℝ) → ℝ} (hu : ∀ s, StronglyMonotoneL (u s)) :
    RationalOn (unflat ⁻¹' {x : CVec S L | NonnegC x})
        (fun a b => euPref π u (unflat a) (unflat b)) ∧
      LocallyNonsatiated (unflat ⁻¹' {x : CVec S L | NonnegC x})
        (fun a b => euPref π u (unflat a) (unflat b)) := by
  refine ⟨⟨fun a _ b _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => le_trans h2 h1⟩, ?_⟩
  intro v hv ε hε
  have hn : (0 : ℝ) < (S * L : ℕ) := by
    have := NeZero.pos S; have := NeZero.pos L; positivity
  set δ := ε / Real.sqrt (S * L : ℕ) with hδ
  have hδ0 : 0 < δ := div_pos hε (Real.sqrt_pos.mpr hn)
  refine ⟨v + fun _ => δ, ?_, ?_, ?_⟩
  · intro s l
    have := hv s l
    simp only [unflat, Pi.add_apply] at this ⊢
    linarith
  · unfold euclidDist
    simp only [Pi.add_apply, add_sub_cancel_left, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hδ0.le, hδ,
      mul_div_cancel₀ _ (Real.sqrt_pos.mpr hn).ne']
  · have hlt : expUtil π u (unflat v) < expUtil π u (unflat (v + fun _ => δ)) := by
      apply expUtil_stronglyMonotone hπ hu
      · exact hv
      · intro s l; simp only [unflat, Pi.add_apply]; linarith
      · intro h
        have := congrFun (congrFun h ⟨0, NeZero.pos S⟩) ⟨0, NeZero.pos L⟩
        simp only [unflat, Pi.add_apply] at this
        linarith
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- **p. 692**, instance of `adEqm_paretoOptimal`: in an economy whose consumers have consumption
sets `ℝ^{LS}_+` and expected-utility preferences with strictly positive probabilities and
strongly monotone Bernoulli utilities, every Arrow-Debreu equilibrium allocation is Pareto
optimal. -/
theorem adEqm_paretoOptimal_eu [NeZero S] [NeZero L] {E : CEconomy ι κ S L}
    {π : ι → Fin S → ℝ} (hπ : ∀ i s, 0 < π i s) {u : ι → Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ i s, StronglyMonotoneL (u i s)) (hX : ∀ i, E.X i = {x | NonnegC x})
    (hpref : ∀ i, E.pref i = euPref (π i) (u i)) (hθ : ∀ j, ∑ i, E.θ j i = 1)
    {x : ι → CVec S L} {y : κ → CVec S L} {p : CVec S L} (h : E.IsADEqm x y p) :
    E.IsParetoOptimal x y := by
  have hX' : ∀ i, E.toPriv.X i = unflat ⁻¹' {x : CVec S L | NonnegC x} := fun i => by
    simp [CEconomy.toPriv, hX i]
  have hp' : ∀ i, E.toPriv.pref i = fun a b => euPref (π i) (u i) (unflat a) (unflat b) :=
    fun i => by simp [CEconomy.toPriv, hpref i]
  refine adEqm_paretoOptimal (fun i => ?_) (fun i => ?_) hθ h
  · rw [hX' i, hp' i]; exact (euPref_rational_lns (hπ i) (hu i)).1
  · rw [hX' i, hp' i]; exact (euPref_rational_lns (hπ i) (hu i)).2

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order tools for Chapter 19

The chapter's examples and exercises use first-order conditions at interior optima. This module
proves the elementary facts they rest on, with no differentiability beyond what each statement
names.

* One-sided derivative tests: a positive derivative gives strict increase just to the right of
  the point (`eventually_lt_of_hasDerivAt_pos`); a one-sided maximum gives a nonpositive
  derivative (`hasDerivAt_nonpos_of_eventually_le`).
* The alternative for a single linear inequality: if `a·d ≤ 0` whenever `q·d ≤ 0`, then
  `a = α q` with `α ≥ 0` (`exists_nonneg_smul_of_dot_nonpos`), the Lagrange condition for one
  budget constraint.
* Directional first-order conditions for a consumer maximizing on `{x ≥ 0 : p·x ≤ w}` at an
  interior point (`foc_dir`), and the strict decrease of the derivative of a strictly concave
  function (`hasDerivAt_lt_of_strictConcaveOn`).
* Demand of a quasilinear consumer with utility `b ln x₁ + x₂` (`quasilinearLog_le`,
  `quasilinearLog_eq_iff`).
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology

variable {S L : ℕ}

/-- A positive derivative at `a` gives `g a < g t` for all `t > a` close to `a`. -/
theorem eventually_lt_of_hasDerivAt_pos {g : ℝ → ℝ} {g' a : ℝ} (hg : HasDerivAt g g' a)
    (hpos : 0 < g') : ∀ᶠ t in 𝓝[>] a, g a < g t := by
  have h1 := (hasDerivAt_iff_tendsto_slope.mp hg).eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ t in 𝓝[>] a, 0 < slope g a t := h1.filter_mono (nhdsGT_le_nhdsNE a)
  filter_upwards [h2, self_mem_nhdsWithin] with t ht hta
  rw [slope_def_field] at ht
  have hta' : 0 < t - a := sub_pos.mpr hta
  have := (div_pos_iff_of_pos_right hta').mp ht
  linarith

/-- A one-sided (right) local maximum at `a` gives a nonpositive derivative. -/
theorem hasDerivAt_nonpos_of_eventually_le {g : ℝ → ℝ} {g' a : ℝ} (hg : HasDerivAt g g' a)
    (hmax : ∀ᶠ t in 𝓝[>] a, g t ≤ g a) : g' ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨t, h1, h2⟩ := ((eventually_lt_of_hasDerivAt_pos hg h).and hmax).exists
  linarith

/-- **The alternative for one linear inequality** (the Lagrange condition behind every first-order
condition of the chapter). If `a·d ≤ 0` for every `d` with `q·d ≤ 0`, then `a = α q` for some
`α ≥ 0`. -/
theorem exists_nonneg_smul_of_dot_nonpos {n : Type*} [Fintype n] {a q : n → ℝ}
    (h : ∀ d, q ⬝ᵥ d ≤ 0 → a ⬝ᵥ d ≤ 0) : ∃ α : ℝ, 0 ≤ α ∧ a = α • q := by
  classical
  by_cases hq : q ⬝ᵥ q = 0
  · have hq0 : q = 0 := dotProduct_self_eq_zero.mp hq
    refine ⟨0, le_rfl, ?_⟩
    have ha : a ⬝ᵥ a = 0 := by
      apply le_antisymm (h a (by simp [hq0]))
      have := h (-a) (by simp [hq0])
      rw [dotProduct_neg] at this
      linarith
    rw [dotProduct_self_eq_zero.mp ha, zero_smul]
  · have hqq : 0 < q ⬝ᵥ q :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (q i)) (Ne.symm hq)
    set α := (a ⬝ᵥ q) / (q ⬝ᵥ q) with hα
    have hker : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0 := by
      intro d hd
      apply le_antisymm (h d hd.le)
      have := h (-d) (by rw [dotProduct_neg, hd, neg_zero])
      rw [dotProduct_neg] at this
      linarith
    have hα0 : 0 ≤ α := by
      have := h (-q) (by rw [dotProduct_neg]; linarith)
      rw [dotProduct_neg] at this
      exact div_nonneg (by linarith) hqq.le
    refine ⟨α, hα0, ?_⟩
    have hd : ∀ d, a ⬝ᵥ d = α * (q ⬝ᵥ d) := by
      intro d
      have h0 := hker (d - ((q ⬝ᵥ d) / (q ⬝ᵥ q)) • q) (by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hq, sub_self])
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h0
      rw [h0, hα, dotProduct_comm a q]
      field_simp
    funext k
    have := hd (Pi.single k 1)
    simpa [dotProduct_single] using this

/-- The value is linear along a ray. -/
theorem cval_add_smul (p x d : CVec S L) (t : ℝ) :
    cval p (x + t • d) = cval p x + t * cval p d := by
  simp only [cval, Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- **Directional first-order condition**. If `x*` is strictly positive and maximizes `U` on
`{x ≥ 0 : p·x ≤ w}`, then along every direction `d` with `p·d ≤ 0` the derivative of
`t ↦ U(x* + t d)` at `0` is nonpositive. -/
theorem foc_dir {U : CVec S L → ℝ} {p x : CVec S L} {w : ℝ} (hx : ∀ s l, 0 < x s l)
    (hb : cval p x ≤ w) (hmax : ∀ x', NonnegC x' → cval p x' ≤ w → U x' ≤ U x)
    {d : CVec S L} (hd : cval p d ≤ 0) {D : ℝ}
    (hD : HasDerivAt (fun t : ℝ => U (x + t • d)) D 0) :
    D ≤ 0 := by
  refine hasDerivAt_nonpos_of_eventually_le hD ?_
  have hpos : ∀ s l, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x s l + t * d s l := by
    intro s l
    have hc : Tendsto (fun t : ℝ => x s l + t * d s l) (𝓝 0) (𝓝 (x s l + 0 * d s l)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at hc
    exact (hc.eventually (lt_mem_nhds (hx s l))).filter_mono nhdsWithin_le_nhds |>.mono
      fun t ht => ht.le
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ s l, 0 ≤ x s l + t * d s l :=
    eventually_all.2 fun s => eventually_all.2 fun l => hpos s l
  filter_upwards [hall, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_smul, add_zero]
  apply hmax
  · intro s l; simpa using ht s l
  · rw [cval_add_smul]
    have : t * cval p d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt htpos) hd
    linarith

/-- The derivative of a strictly concave function is strictly decreasing (derivatives given as
`HasDerivAt` values). -/
theorem hasDerivAt_lt_of_strictConcaveOn {D : Set ℝ} {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ D u)
    {x y a b : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) (ha : HasDerivAt u a x)
    (hb : HasDerivAt u b y) : b < a :=
  (hu.lt_slope_of_hasDerivAt hx hy hxy hb).trans (hu.slope_lt_of_hasDerivAt hx hy hxy ha)

/-- The derivative of a strictly concave function determines the point. -/
theorem eq_of_hasDerivAt_eq_of_strictConcaveOn {D : Set ℝ} {u : ℝ → ℝ}
    (hu : StrictConcaveOn ℝ D u) {x y a : ℝ} (hx : x ∈ D) (hy : y ∈ D) (ha : HasDerivAt u a x)
    (hb : HasDerivAt u a y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (hasDerivAt_lt_of_strictConcaveOn hu hx hy h ha hb) (lt_irrefl a)
  · exact h
  · exact absurd (hasDerivAt_lt_of_strictConcaveOn hu hy hx h hb ha) (lt_irrefl a)

/-! ## Quasilinear logarithmic demand -/

/-- The quasilinear utility `b ln x₁ + x₂` is at most `b ln(b/p) - b + w` on the budget set
`{x₁ > 0, p x₁ + x₂ ≤ w}` (`b, p > 0`). -/
theorem quasilinearLog_le {b p w x₁ x₂ : ℝ} (hb : 0 < b) (hp : 0 < p) (hx : 0 < x₁)
    (hbud : p * x₁ + x₂ ≤ w) : b * Real.log x₁ + x₂ ≤ b * Real.log (b / p) - b + w := by
  have hr : 0 < x₁ / (b / p) := div_pos hx (div_pos hb hp)
  have hl := Real.log_le_sub_one_of_pos hr
  rw [Real.log_div hx.ne' (div_pos hb hp).ne'] at hl
  have h2 : b * (x₁ / (b / p)) = p * x₁ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hl hb.le]

/-- The maximum `b ln(b/p) - b + w` is attained exactly at `x₁ = b/p`, `x₂ = w - b`: a bundle of
the budget set attaining it has `x₁ = b/p` (and spends its whole budget). -/
theorem quasilinearLog_eq_iff {b p w x₁ x₂ : ℝ} (hb : 0 < b) (hp : 0 < p) (hx : 0 < x₁)
    (hbud : p * x₁ + x₂ ≤ w) (hge : b * Real.log (b / p) - b + w ≤ b * Real.log x₁ + x₂) :
    x₁ = b / p ∧ x₂ = w - b := by
  have hbp : 0 < b / p := div_pos hb hp
  by_contra hne
  have hx1 : x₁ = b / p := by
    by_contra h1
    have hr : 0 < x₁ / (b / p) := div_pos hx hbp
    have hr1 : x₁ / (b / p) ≠ 1 := by
      intro h; apply h1; rw [div_eq_one_iff_eq hbp.ne'] at h; exact h
    have hl : Real.log (x₁ / (b / p)) < x₁ / (b / p) - 1 := by
      have := Real.add_one_lt_exp (Real.log_ne_zero_of_pos_of_ne_one hr hr1)
      rw [Real.exp_log hr] at this; linarith
    rw [Real.log_div hx.ne' hbp.ne'] at hl
    have h2 : b * (x₁ / (b / p)) = p * x₁ := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hl hb]
  refine hne ⟨hx1, ?_⟩
  rw [hx1] at hbud hge
  have : p * (b / p) = b := by field_simp
  linarith

/-- A bundle `(b/p, w - b)` attains the maximum of `quasilinearLog_le`. -/
theorem quasilinearLog_at (b p w : ℝ) :
    b * Real.log (b / p) + (w - b) = b * Real.log (b / p) - b + w := by ring

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exchange economies under uncertainty: welfare and first-order tools

Pure exchange economies with consumption sets `ℝ^{LS}_+` and utility functions, the setting of
Examples 19.C.1-19.C.2 and of Sections 19.D-19.F.

* Pareto optimality with the feasibility condition `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ` used on pp. 694 and 710
  (`IsParetoOptimalU`).
* With strongly monotone utilities, Arrow-Debreu equilibrium prices are nonnegative, budgets bind,
  and every Arrow-Debreu equilibrium allocation is Pareto optimal (`adEqmU_paretoOptimal`, the
  first welfare theorem in this setting).
* **pp. 709-710** (the argument of Example 19.F.1, used for Example 19.C.1): with common
  probabilities, state-independent strictly concave Bernoulli utilities and a state-independent
  aggregate endowment, every Pareto optimal allocation is state independent
  (`po_stateIndependent`).
* The one-good expected utility `eu1`, its directional derivatives, the Lagrange condition of
  an interior optimum (`foc_eu1`), and the Pareto tangency condition for two consumers and two
  states (`po_tangency`).
* `GoodBernoulli`: a strictly concave, strictly increasing, differentiable Bernoulli utility,
  with the instance `√·` (`goodBernoulli_sqrt`); its derivative is positive.
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology

variable {S L : ℕ} {ι : Type*} [Fintype ι]

/-! ## Values, sums and cheap improvements -/

theorem cval_sum (p : CVec S L) (x : ι → CVec S L) :
    cval p (∑ i, x i) = ∑ i, cval p (x i) := by
  simp only [cval, Finset.sum_apply, dotProduct_sum]
  exact Finset.sum_comm

theorem cval_mono {p x y : CVec S L} (hp : ∀ s l, 0 ≤ p s l) (h : x ≤ y) :
    cval p x ≤ cval p y :=
  Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun l _ =>
    mul_le_mul_of_nonneg_left (h s l) (hp s l)

theorem cval_add (p x y : CVec S L) : cval p (x + y) = cval p x + cval p y := by
  simp [cval, dotProduct_add, Finset.sum_add_distrib]

theorem cval_sub (p x y : CVec S L) : cval p (x - y) = cval p x - cval p y := by
  simp [cval, dotProduct_sub, Finset.sum_sub_distrib]

theorem cval_smul (p x : CVec S L) (a : ℝ) : cval p (a • x) = a * cval p x := by
  simp [cval, dotProduct_smul, Finset.mul_sum]

theorem cval_unit (p : CVec S L) (l : Fin L) (s : Fin S) :
    cval p (contingentUnit l s) = p s l := by
  unfold cval contingentUnit
  rw [Finset.sum_eq_single s]
  · simp [dotProduct]
  · intro b _ hb; simp [dotProduct, hb]
  · simp

/-- Near any `x ≥ 0` there is a strictly larger bundle costing less than `p·x + g` (`g > 0`). -/
theorem exists_larger_cheap [NeZero S] [NeZero L] (p x : CVec S L) {g : ℝ} (hg : 0 < g) :
    ∃ x', x ≤ x' ∧ x ≠ x' ∧ cval p x' < cval p x + g := by
  set c := ∑ s, ∑ l, |p s l| + 1 with hc
  have hc0 : 0 < c := by
    have : 0 ≤ ∑ s, ∑ l, |p s l| :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun l _ => abs_nonneg _
    linarith
  set δ := g / c with hδ
  have hδ0 : 0 < δ := div_pos hg hc0
  refine ⟨x + fun _ _ => δ, fun s l => by simp [hδ0.le], fun h => ?_, ?_⟩
  · have := congrFun (congrFun h ⟨0, NeZero.pos S⟩) ⟨0, NeZero.pos L⟩
    simp at this; linarith
  · rw [cval_add]
    have h1 : cval p (fun _ _ => δ) ≤ δ * (∑ s, ∑ l, |p s l|) := by
      unfold cval
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [mul_comm δ]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hδ0.le
    have h2 : δ * (∑ s, ∑ l, |p s l|) < g := by
      have : δ * c = g := by rw [hδ]; field_simp
      nlinarith
    linarith

/-! ## Pareto optimality and the first welfare theorem -/

/-- **Pareto optimality** (Definition 16.B.2, with the feasibility `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ` of pp. 694 and
710): `x` is feasible and no feasible `x'` makes everyone at least as well off and someone
strictly better off. -/
def IsParetoOptimalU (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L) : Prop :=
  ((∀ i, NonnegC (x i)) ∧ ∑ i, x i ≤ ∑ i, ω i) ∧
    ¬ ∃ x' : ι → CVec S L, ((∀ i, NonnegC (x' i)) ∧ ∑ i, x' i ≤ ∑ i, ω i) ∧
      (∀ i, U i (x i) ≤ U i (x' i)) ∧ ∃ i, U i (x i) < U i (x' i)

/-- With strongly monotone utilities, Arrow-Debreu prices are nonnegative. -/
theorem adEqmU_price_nonneg {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i))
    {ω x : ι → CVec S L} {p : CVec S L} (h : IsADEqmU U ω x p) (i : ι) :
    ∀ s l, 0 ≤ p s l := by
  intro s l
  by_contra hneg
  push Not at hneg
  have hx := (h.1 i).1.1
  have hle : x i ≤ x i + contingentUnit l s := fun s' l' => by
    simp only [Pi.add_apply, contingentUnit]; split_ifs <;> simp
  have hne : x i ≠ x i + contingentUnit l s := fun h' => by
    have := congrFun (congrFun h' s) l
    simp [contingentUnit] at this
  have hlt := hU i _ _ hx hle hne
  have hge := (h.1 i).2 (x i + contingentUnit l s) (fun s' l' => (hx s' l').trans (hle s' l'))
    (by rw [cval_add, cval_unit]; linarith [(h.1 i).1.2])
  linarith

/-- With strongly monotone utilities (and `S, L ≥ 1`), the budget constraint binds at an
Arrow-Debreu equilibrium. -/
theorem adEqmU_budget_binds [NeZero S] [NeZero L] {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU U ω x p) (i : ι) : cval p (x i) = cval p (ω i) := by
  refine le_antisymm (h.1 i).1.2 (not_lt.mp fun hlt => ?_)
  obtain ⟨x', hle, hne, hc⟩ := exists_larger_cheap p (x i) (sub_pos.mpr hlt)
  have hx := (h.1 i).1.1
  have := (h.1 i).2 x' (fun s l => (hx s l).trans (hle s l)) (by linarith)
  linarith [hU i _ _ hx hle hne]

/-- **First welfare theorem** for exchange economies under uncertainty (p. 692, Proposition
16.C.1 in this setting): with strongly monotone utilities on `ℝ^{LS}_+`, every Arrow-Debreu
equilibrium allocation is Pareto optimal. -/
theorem adEqmU_paretoOptimal [NeZero S] [NeZero L] {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU U ω x p) : IsParetoOptimalU U ω x := by
  refine ⟨⟨fun i => (h.1 i).1.1, h.2.le⟩, ?_⟩
  rintro ⟨x', ⟨hx', hfeas⟩, hge, k, hk⟩
  have hp := adEqmU_price_nonneg hU h k
  have hweak : ∀ i, cval p (ω i) ≤ cval p (x' i) := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨x'', hle, hne, hc⟩ := exists_larger_cheap p (x' i) (sub_pos.mpr hlt)
    have h1 := hU i _ _ (hx' i) hle hne
    have h2 := (h.1 i).2 x'' (fun s l => (hx' i s l).trans (hle s l)) (by linarith)
    linarith [hge i]
  have hstrict : cval p (ω k) < cval p (x' k) := by
    by_contra hle
    push Not at hle
    linarith [(h.1 k).2 (x' k) (hx' k) hle]
  have hsum : ∑ i, cval p (ω i) < ∑ i, cval p (x' i) :=
    Finset.sum_lt_sum (fun i _ => hweak i) ⟨k, Finset.mem_univ _, hstrict⟩
  rw [← cval_sum, ← cval_sum] at hsum
  linarith [cval_mono hp hfeas]

/-! ## State independence of Pareto optima (pp. 709-710) -/

/-- The constant contingent vector delivering `a ∈ ℝ^L` in every state. -/
def constC (a : Fin L → ℝ) : CVec S L := fun _ => a

/-- **pp. 709-710** (the argument of Example 19.F.1, also behind Example 19.C.1(a)). Suppose the
probabilities `π ≫ 0` (with `∑_s π_s = 1`) are common, every consumer's Bernoulli utility `uᵢ` is
state independent and strictly concave on `ℝ^L_+`, and the aggregate endowment is the same in
every state. Then every Pareto optimal allocation is state independent: `x_{si} = x_{s'i}`. -/
theorem po_stateIndependent {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω : ι → CVec S L} (hω : ∀ s s', ∑ i, ω i s = ∑ i, ω i s') {x : ι → CVec S L}
    (hpo : IsParetoOptimalU (fun i => expUtil π (fun _ => u i)) ω x) :
    ∀ i s s', x i s = x i s' := by
  obtain ⟨⟨hx, hfeas⟩, hno⟩ := hpo
  set xbar : ι → Fin L → ℝ := fun i => ∑ s, π s • x i s with hxbar
  have hxbar0 : ∀ i, ∀ l, 0 ≤ xbar i l := fun i l => by
    simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s).le (hx i s l)
  have hjensen : ∀ i, expUtil π (fun _ => u i) (x i) ≤ u i (xbar i) := by
    intro i
    have := (hu i).concaveOn.le_map_sum (t := Finset.univ) (w := π) (p := x i)
      (fun s _ => (hπ s).le) hπ1 (fun s _ => hx i s)
    simpa [expUtil, smul_eq_mul] using this
  have hconst : ∀ i, expUtil π (fun _ => u i) (constC (S := S) (xbar i)) = u i (xbar i) := by
    intro i
    simp [expUtil, constC, ← Finset.sum_mul, hπ1]
  have hfeas' : ∑ i, constC (S := S) (xbar i) ≤ ∑ i, ω i := by
    intro s l
    obtain ⟨s0⟩ : Nonempty (Fin S) := ⟨s⟩
    have h1 : (∑ i, constC (S := S) (xbar i)) s l = ∑ s', π s' * (∑ i, x i s' l) := by
      simp only [Finset.sum_apply, constC, hxbar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm
    have h2 : ∀ s', ∑ i, x i s' l ≤ (∑ i, ω i) s l := by
      intro s'
      have := hfeas s' l
      simp only [Finset.sum_apply] at this ⊢
      have hω' := congrFun (hω s' s) l
      simp only [Finset.sum_apply] at hω'
      linarith
    rw [h1]
    calc ∑ s', π s' * (∑ i, x i s' l) ≤ ∑ s', π s' * (∑ i, ω i) s l :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h2 s') (hπ s').le
      _ = (∑ i, ω i) s l := by rw [← Finset.sum_mul, hπ1, one_mul]
  have heq : ∀ i, expUtil π (fun _ => u i) (x i) = u i (xbar i) := by
    intro i
    refine le_antisymm (hjensen i) (not_lt.mp fun hlt => hno ⟨fun i => constC (xbar i),
      ⟨fun i s l => hxbar0 i l, hfeas'⟩, fun j => ?_, i, ?_⟩)
    · dsimp only; rw [hconst]; exact hjensen j
    · dsimp only; rw [hconst]; exact hlt
  intro i s s'
  by_contra hne
  have := (hu i).lt_map_sum (t := Finset.univ) (w := π) (p := x i) (fun s _ => hπ s) hπ1
    (fun s _ => hx i s) ⟨s, Finset.mem_univ _, s', Finset.mem_univ _, hne⟩
  have h2 := heq i
  simp only [expUtil, smul_eq_mul] at this h2
  linarith

/-! ## One good: expected utility and first-order conditions -/

/-- The one-good expected utility `∑_s π_s u_s(x_s)` on `ℝ^S_+` (contingent vectors with
`L = 1`). -/
def eu1 (π : Fin S → ℝ) (u : Fin S → ℝ → ℝ) (x : CVec S 1) : ℝ := ∑ s, π s * u s (x s 0)

theorem eu1_eq_expUtil (π : Fin S → ℝ) (u : Fin S → ℝ → ℝ) :
    eu1 π u = expUtil π (fun s v => u s (v 0)) := rfl

/-- One-good expected utility with `π ≫ 0` and strictly increasing `u_s` on `ℝ_+` is strongly
monotone. -/
theorem eu1_stronglyMonotone {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → ℝ → ℝ}
    (hu : ∀ s, StrictMonoOn (u s) (Set.Ici 0)) : StronglyMonotoneC (eu1 π u) := by
  rw [eu1_eq_expUtil]
  refine expUtil_stronglyMonotone hπ fun s a b ha hab hne => ?_
  have h0 : a 0 ≠ b 0 := fun h => hne (funext fun l => by rw [Subsingleton.elim l 0]; exact h)
  exact hu s (Set.mem_Ici.mpr (ha 0)) (Set.mem_Ici.mpr ((ha 0).trans (hab 0)))
    (lt_of_le_of_ne (hab 0) h0)

/-- The direction `d ∈ ℝ^S` as a one-good contingent vector. -/
def dirC (d : Fin S → ℝ) : CVec S 1 := fun s _ => d s

theorem cval_dirC (p : CVec S 1) (d : Fin S → ℝ) : cval p (dirC d) = ∑ s, p s 0 * d s := by
  simp [cval, dirC, dotProduct]

/-- The derivative of `t ↦ ∑_s π_s u_s(x_s + t d_s)` at `0` is `∑_s π_s u_s'(x_s) d_s`. -/
theorem hasDerivAt_eu1_dir {π : Fin S → ℝ} {u : Fin S → ℝ → ℝ} {x : CVec S 1}
    {D : Fin S → ℝ} (hd : ∀ s, HasDerivAt (u s) (D s) (x s 0)) (d : Fin S → ℝ) :
    HasDerivAt (fun t : ℝ => eu1 π u (x + t • dirC d)) (∑ s, π s * (D s * d s)) 0 := by
  have hfun : (fun t : ℝ => eu1 π u (x + t • dirC d)) =
      fun t => ∑ s, π s * u s (x s 0 + t * d s) := by
    funext t; simp [eu1, dirC]
  rw [hfun]
  refine HasDerivAt.fun_sum fun s _ => HasDerivAt.const_mul _ ?_
  have hin : HasDerivAt (fun t : ℝ => x s 0 + t * d s) (d s) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (d s)).const_add (x s 0)
    simpa using this
  have hout : HasDerivAt (u s) (D s) (x s 0 + 0 * d s) := by simpa using hd s
  exact hout.comp (0 : ℝ) hin

/-- **Lagrange condition** for one good. If `x ≫ 0` maximizes `∑_s π_s u_s(x_s)` on
`{x ≥ 0 : p·x ≤ w}` and `u_s'(x_s) = D_s`, then `π_s D_s = λ p_s` for some `λ ≥ 0`. -/
theorem foc_eu1 {π : Fin S → ℝ} {u : Fin S → ℝ → ℝ} {p x : CVec S 1} {w : ℝ}
    (hx : ∀ s, 0 < x s 0) (hb : cval p x ≤ w)
    (hmax : ∀ x', NonnegC x' → cval p x' ≤ w → eu1 π u x' ≤ eu1 π u x) {D : Fin S → ℝ}
    (hd : ∀ s, HasDerivAt (u s) (D s) (x s 0)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ s, π s * D s = lam * p s 0 := by
  have hx' : ∀ s l, 0 < x s l := fun s l => by rw [Subsingleton.elim l 0]; exact hx s
  obtain ⟨lam, hlam, heq⟩ := exists_nonneg_smul_of_dot_nonpos
    (a := fun s => π s * D s) (q := fun s => p s 0) (fun d hd' => by
      have hcd : cval p (dirC d) ≤ 0 := by rw [cval_dirC]; exact hd'
      have := foc_dir hx' hb hmax hcd (hasDerivAt_eu1_dir hd d)
      simpa [dotProduct, mul_assoc] using this)
  exact ⟨lam, hlam, fun s => by simpa using congrFun heq s⟩

/-- **Pareto optimality excludes improving directions** (two consumers, one good). At an interior
Pareto optimum no direction `d` raises consumer 0's utility at `x₀ + t d` and consumer 1's at
`x₁ - t d` at once (to first order). -/
theorem po_no_improving_dir {U : Fin 2 → CVec S 1 → ℝ} {ω x : Fin 2 → CVec S 1}
    (hpo : IsParetoOptimalU U ω x) (hx : ∀ i s, 0 < x i s 0) (d : Fin S → ℝ) {D₀ D₁ : ℝ}
    (h0 : HasDerivAt (fun t : ℝ => U 0 (x 0 + t • dirC d)) D₀ 0)
    (h1 : HasDerivAt (fun t : ℝ => U 1 (x 1 + t • dirC (-d))) D₁ 0) (hD₀ : 0 < D₀)
    (hD₁ : 0 < D₁) : False := by
  obtain ⟨⟨_, hfeas⟩, hno⟩ := hpo
  have hpos : ∀ i s, ∀ (e : Fin S → ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x i s 0 + t * e s := by
    intro i s e
    have hc : Tendsto (fun t : ℝ => x i s 0 + t * e s) (𝓝 0) (𝓝 (x i s 0 + 0 * e s)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at hc
    exact (hc.eventually (lt_mem_nhds (hx i s))).filter_mono nhdsWithin_le_nhds |>.mono
      fun t ht => ht.le
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ s, 0 ≤ x 0 s 0 + t * d s) ∧
      ∀ s, 0 ≤ x 1 s 0 + t * (-d) s :=
    (eventually_all.2 fun s => hpos 0 s d).and (eventually_all.2 fun s => hpos 1 s (-d))
  obtain ⟨t, ⟨ht0, ht1⟩, hg0, hg1⟩ := (hall.and ((eventually_lt_of_hasDerivAt_pos h0 hD₀).and
    (eventually_lt_of_hasDerivAt_pos h1 hD₁))).exists
  simp only [zero_smul, add_zero] at hg0 hg1
  refine hno ⟨![x 0 + t • dirC d, x 1 + t • dirC (-d)], ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, ?_⟩
  · fin_cases i
    · intro s l; rw [Subsingleton.elim l 0]; simpa [dirC] using ht0 s
    · intro s l; rw [Subsingleton.elim l 0]; simpa [dirC] using ht1 s
  · have : ∑ i, ![x 0 + t • dirC d, x 1 + t • dirC (-d)] i = ∑ i, x i := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      funext s l; simp [dirC]; ring
    rw [this]; exact hfeas
  · fin_cases i
    · exact hg0.le
    · exact hg1.le
  · exact hg0

/-- **Pareto tangency** (two consumers, two states, one good, common probabilities, state-
independent utilities): at an interior Pareto optimum the marginal rates of substitution
`π₁ u₁'(x₁ᵢ) / (π₂ u₂'(x₂ᵢ))` of the two consumers are equal (in cross-multiplied form). -/
theorem po_tangency {π : Fin 2 → ℝ} {u : Fin 2 → ℝ → ℝ} {du : Fin 2 → Fin 2 → ℝ}
    {ω x : Fin 2 → CVec 2 1} (hpo : IsParetoOptimalU (fun i => eu1 π fun _ => u i) ω x)
    (hx : ∀ i s, 0 < x i s 0) (hd : ∀ i s, HasDerivAt (u i) (du i s) (x i s 0)) :
    π 0 * du 0 0 * (π 1 * du 1 1) = π 0 * du 1 0 * (π 1 * du 0 1) := by
  have hder : ∀ i (e : Fin 2 → ℝ), HasDerivAt (fun t : ℝ => eu1 π (fun _ => u i) (x i + t • dirC e))
      (π 0 * (du i 0 * e 0) + π 1 * (du i 1 * e 1)) 0 := by
    intro i e
    simpa [Fin.sum_univ_two] using hasDerivAt_eu1_dir (π := π) (fun s => hd i s) e
  set v : Fin 2 → ℝ := ![π 1 * du 0 1 + π 1 * du 1 1, -(π 0 * du 0 0 + π 0 * du 1 0)] with hv
  have hv0 : v 0 = π 1 * du 0 1 + π 1 * du 1 1 := rfl
  have hv1 : v 1 = -(π 0 * du 0 0 + π 0 * du 1 0) := rfl
  rcases lt_trichotomy (π 0 * du 0 0 * (π 1 * du 1 1)) (π 0 * du 1 0 * (π 1 * du 0 1))
    with hlt | heq | hgt
  · exfalso
    refine po_no_improving_dir hpo hx (-v) (hder 0 _) (hder 1 _) ?_ ?_
    · simp only [Pi.neg_apply, hv0, hv1]; nlinarith
    · simp only [Pi.neg_apply, neg_neg, hv0, hv1]; nlinarith
  · exact heq
  · exfalso
    refine po_no_improving_dir hpo hx v (hder 0 _) (hder 1 _) ?_ ?_
    · simp only [hv0, hv1]; nlinarith
    · simp only [Pi.neg_apply, hv0, hv1]; nlinarith

/-! ## Good Bernoulli utilities -/

/-- A strictly concave, strictly increasing Bernoulli utility on `ℝ_+`, differentiable on `ℝ_{++}`
with derivative `u'` (the standing assumptions of Examples 19.C.1-19.C.2 and Exercise 19.C.4). -/
def GoodBernoulli (u u' : ℝ → ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Ici 0) u ∧ StrictMonoOn u (Set.Ici 0) ∧
    ∀ y, 0 < y → HasDerivAt u (u' y) y

/-- The derivative of a good Bernoulli utility is positive on `ℝ_{++}`. -/
theorem GoodBernoulli.deriv_pos {u u' : ℝ → ℝ} (h : GoodBernoulli u u') {y : ℝ} (hy : 0 < y) :
    0 < u' y := by
  have hnn : ∀ z, 0 < z → 0 ≤ u' z := by
    intro z hz
    have := hasDerivAt_nonpos_of_eventually_le (h.2.2 z hz).neg (Filter.eventually_of_mem
      self_mem_nhdsWithin fun t (ht : z < t) => by
        rw [Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
        exact (h.2.1 (Set.mem_Ici.mpr hz.le) (Set.mem_Ici.mpr (hz.le.trans ht.le)) ht).le)
    linarith
  have hlt := hasDerivAt_lt_of_strictConcaveOn h.1 (Set.mem_Ici.mpr hy.le)
    (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ y + 1)) (by linarith) (h.2.2 y hy)
    (h.2.2 (y + 1) (by linarith))
  linarith [hnn (y + 1) (by linarith)]

/-- The derivative of a good Bernoulli utility is strictly decreasing. -/
theorem GoodBernoulli.deriv_lt {u u' : ℝ → ℝ} (h : GoodBernoulli u u') {y z : ℝ} (hy : 0 < y)
    (hyz : y < z) : u' z < u' y :=
  hasDerivAt_lt_of_strictConcaveOn h.1 (Set.mem_Ici.mpr hy.le)
    (Set.mem_Ici.mpr (hy.le.trans hyz.le)) hyz (h.2.2 y hy) (h.2.2 z (hy.trans hyz))

/-- `√·` is a good Bernoulli utility (an instance of the hypotheses). -/
theorem goodBernoulli_sqrt : GoodBernoulli Real.sqrt fun y => 1 / (2 * Real.sqrt y) :=
  ⟨Real.strictConcaveOn_sqrt, fun _ ha _ _ hab => Real.sqrt_lt_sqrt ha hab,
    fun _ hy => Real.hasDerivAt_sqrt hy.ne'⟩

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk sharing (MWG Section 19.C, Examples 19.C.1-19.C.2, Exercises 19.C.2-19.C.5)

One physical good (`L = 1`), contingent vectors `x : CVec S 1`, one-good expected utility `eu1`.

* **Example 19.C.1(a)**: no aggregate risk and common probabilities: every Arrow-Debreu
  equilibrium insures both consumers completely, and the Pareto set is the diagonal of the box
  (`example_19_C_1a`, `example_19_C_1a_diagonal`).
* **Example 19.C.1(b)**: different probabilities (`π₁₁ < π₁₂`): at an interior equilibrium each
  consumer consumes more in the state he thinks comparatively more likely (`example_19_C_1b`).
* **Example 19.C.2** and **Exercise 19.C.2**: aggregate endowment `(2, 1)`: along the interior
  Pareto set the marginal rate of substitution is below the probability ratio, so at an interior
  equilibrium `p₁/p₂ < π₁/π₂`, and `p₁ < p₂` when `π₁ = π₂` (`exercise_19_C_2`,
  `example_19_C_2`).
* **Exercise 19.C.3**: `∑_s (π_{si} p̄ - p_s) x_{si} ≥ 0` (revealed preference and Jensen).
* **Exercise 19.C.4(a)-(b)**: a risk-neutral and a risk-averse consumer.
* **Exercise 19.C.5**: with nonstochastic aggregate endowment, consuming the expected value of
  one's endowment in every state is an equilibrium allocation.
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ}

/-- A strictly concave Bernoulli utility of one good gives a strictly concave function on
`ℝ^1_+`. -/
theorem strictConcaveOn_fin1 {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ici 0) u) :
    StrictConcaveOn ℝ {a : Fin 1 → ℝ | ∀ l, 0 ≤ a l} (fun v => u (v 0)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb α β hα hβ _ l
    have := ha l; have := hb l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro a ha b hb hab α β hα hβ hαβ
    have h0 : a 0 ≠ b 0 := fun h => hab (funext fun l => by rw [Subsingleton.elim l 0]; exact h)
    exact hu.2 (Set.mem_Ici.mpr (ha 0)) (Set.mem_Ici.mpr (hb 0)) h0 hα hβ hαβ

/-- The endowments of Example 19.C.1: `ω₁ = (1, 0)`, `ω₂ = (0, 1)`. -/
def omega19C1 : Fin 2 → CVec 2 1 := ![dirC ![1, 0], dirC ![0, 1]]

/-- **Example 19.C.1(a)** (MWG, pp. 692-693). With no aggregate risk (`ω₁ + ω₂ = (1, 1)`),
common strictly positive probabilities and state-independent, strictly concave, strictly
increasing Bernoulli utilities, every Arrow-Debreu equilibrium insures both consumers completely:
consumption does not vary across the two states. -/
theorem example_19_C_1a {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : Fin 2 → ℝ → ℝ} (hc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 π fun _ => u i) omega19C1 x p) : ∀ i, x i 0 = x i 1 := by
  have hpo := adEqmU_paretoOptimal (fun i => eu1_stronglyMonotone hπ fun _ => hm i) h
  have := po_stateIndependent (u := fun i v => u i (v 0)) hπ hπ1
    (fun i => strictConcaveOn_fin1 (hc i)) (ω := omega19C1) (fun s s' => by
      fin_cases s <;> fin_cases s' <;> funext l <;> simp [omega19C1, dirC]) hpo
  exact fun i => this i 0 1

/-- **Example 19.C.1(a)** (MWG, p. 692, Figure 19.C.1(a)): the Pareto set is the diagonal. Every
full-insurance allocation `x₁ = (c, c)`, `x₂ = (1 - c, 1 - c)`, `0 ≤ c ≤ 1`, is Pareto optimal
(the converse is `po_stateIndependent`). -/
theorem example_19_C_1a_diagonal {π : Fin 2 → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : Fin 2 → ℝ → ℝ} (hc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsParetoOptimalU (fun i => eu1 π fun _ => u i) omega19C1
      ![fun _ _ => c, fun _ _ => 1 - c] := by
  refine ⟨⟨fun i => ?_, fun s l => ?_⟩, ?_⟩
  · fin_cases i <;> intro s l <;> simp <;> linarith
  · rw [Subsingleton.elim l 0]
    fin_cases s <;> simp [omega19C1, dirC]
  · rintro ⟨x', ⟨hx', hf⟩, hge, k, hk⟩
    set m : Fin 2 → ℝ := fun i => ∑ s, π s * x' i s 0 with hm'
    have hjen : ∀ i, eu1 π (fun _ => u i) (x' i) ≤ u i (m i) := by
      intro i
      have := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := fun s => x' i s 0)
        (fun s _ => hπ s) hπ1 (fun s _ => Set.mem_Ici.mpr (hx' i s 0))
      simp only [smul_eq_mul] at this
      exact this
    have hm0 : ∀ i, 0 ≤ m i := fun i =>
      Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' i s 0)
    have hconst : ∀ i (a : ℝ), eu1 π (fun _ => u i) (fun _ _ => a) = u i a := by
      intro i a; simp [eu1, ← Finset.sum_mul, hπ1]
    have hsum : m 0 + m 1 ≤ 1 := by
      have h0 := hf 0 0; have h1 := hf 1 0
      simp [Fin.sum_univ_two, omega19C1, dirC] at h0 h1
      simp only [hm', Fin.sum_univ_two] at *
      have hπ1' : π 0 + π 1 = 1 := by simpa [Fin.sum_univ_two] using hπ1
      nlinarith [hπ 0, hπ 1]
    have hle : ∀ i (a : ℝ), 0 ≤ a → u i a ≤ u i (m i) → a ≤ m i := fun i a ha h =>
      (hm i).le_iff_le (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (hm0 i)) |>.mp h
    have hlt : ∀ i (a : ℝ), 0 ≤ a → u i a < u i (m i) → a < m i := fun i a ha h =>
      (hm i).lt_iff_lt (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (hm0 i)) |>.mp h
    have h0 := hge 0; have h1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hconst] at h0 h1
    have hc0' := hle 0 c hc0 (h0.trans (hjen 0))
    have hc1' := hle 1 (1 - c) (by linarith) (h1.trans (hjen 1))
    fin_cases k
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, hconst] at hk
      linarith [hlt 0 c hc0 (hk.trans_le (hjen 0))]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hconst] at hk
      linarith [hlt 1 (1 - c) (by linarith) (hk.trans_le (hjen 1))]

/-- **Example 19.C.1(b)** (MWG, p. 693, Figure 19.C.1(b)). No aggregate risk, but different
subjective probabilities with `π₁₁ < π₁₂` (consumer 2 gives more probability to state 1; indices
`π i s`, consumers and states counted from `0`). At an interior Arrow-Debreu equilibrium, with
good Bernoulli utilities, each consumer's consumption is higher in the state he thinks
comparatively more likely: consumer 1 consumes more in state 2, consumer 2 more in state 1. -/
theorem example_19_C_1b {π : Fin 2 → Fin 2 → ℝ} (hπ : ∀ i s, 0 < π i s)
    (hπ1 : ∀ i, π i 0 + π i 1 = 1) (hlt : π 0 0 < π 1 0) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 (π i) fun _ => u i) omega19C1 x p) (hx : ∀ i s, 0 < x i s 0) :
    x 0 0 0 < x 0 1 0 ∧ x 1 1 0 < x 1 0 0 := by
  have hfoc : ∀ i, ∃ lam : ℝ, 0 ≤ lam ∧ ∀ s, π i s * u' i (x i s 0) = lam * p s 0 := fun i =>
    foc_eu1 (hx i) (h.1 i).1.2 (h.1 i).2 (fun s => (hu i).2.2 _ (hx i s))
  obtain ⟨l0, _, f0⟩ := hfoc 0
  obtain ⟨l1, _, f1⟩ := hfoc 1
  have hd : ∀ i s, 0 < u' i (x i s 0) := fun i s => (hu i).deriv_pos (hx i s)
  have hfeas : ∀ s, x 0 s 0 + x 1 s 0 = 1 := by
    intro s
    have := congrFun (congrFun h.2 s) 0
    fin_cases s <;> simpa [Fin.sum_univ_two, omega19C1, dirC] using this
  have key : π 0 0 * u' 0 (x 0 0 0) * (π 1 1 * u' 1 (x 1 1 0)) =
      π 0 1 * u' 0 (x 0 1 0) * (π 1 0 * u' 1 (x 1 0 0)) := by
    rw [f0 0, f0 1, f1 0, f1 1]; ring
  have hmain : x 0 0 0 < x 0 1 0 := by
    by_contra hge
    push Not at hge
    have hd0 : u' 0 (x 0 0 0) ≤ u' 0 (x 0 1 0) := by
      rcases hge.lt_or_eq with hlt' | heq
      · exact ((hu 0).deriv_lt (hx 0 1) hlt').le
      · rw [heq]
    have hd1 : u' 1 (x 1 1 0) ≤ u' 1 (x 1 0 0) := by
      have : x 1 0 0 ≤ x 1 1 0 := by linarith [hfeas 0, hfeas 1]
      rcases this.lt_or_eq with hlt' | heq
      · exact ((hu 1).deriv_lt (hx 1 0) hlt').le
      · rw [heq]
    have hA := hd 0 0; have hB := hd 0 1; have hC := hd 1 0; have hD := hd 1 1
    have hπ' : π 0 1 * π 1 0 ≤ π 0 0 * π 1 1 := by
      by_contra hc
      push Not at hc
      have h1 : π 0 0 * π 1 1 * (u' 0 (x 0 0 0) * u' 1 (x 1 1 0)) <
          π 0 1 * π 1 0 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) := by
        calc π 0 0 * π 1 1 * (u' 0 (x 0 0 0) * u' 1 (x 1 1 0))
            ≤ π 0 0 * π 1 1 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) := by
              apply mul_le_mul_of_nonneg_left _ (by nlinarith [hπ 0 0, hπ 1 1])
              exact mul_le_mul hd0 hd1 hD.le hB.le
          _ < π 0 1 * π 1 0 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) :=
              mul_lt_mul_of_pos_right hc (mul_pos hB hC)
      nlinarith [key]
    have e1 : π 0 1 = 1 - π 0 0 := by linarith [hπ1 0]
    have e2 : π 1 1 = 1 - π 1 0 := by linarith [hπ1 1]
    rw [e1, e2] at hπ'
    nlinarith
  exact ⟨hmain, by linarith [hfeas 0, hfeas 1]⟩

/-- Pareto optimal allocations of strongly monotone consumers exhaust the resources. -/
theorem po_exhausts {ι : Type*} [Fintype ι] {L : ℕ} {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} (hpo : IsParetoOptimalU U ω x)
    (i₀ : ι) : ∑ i, x i = ∑ i, ω i := by
  classical
  obtain ⟨⟨hx, hf⟩, hno⟩ := hpo
  by_contra hne
  set g := ∑ i, ω i - ∑ i, x i with hg
  have hg0 : ∀ s l, 0 ≤ g s l := fun s l => by
    have := hf s l
    simp only [Finset.sum_apply] at this
    simp only [hg, Pi.sub_apply, Finset.sum_apply]
    linarith
  refine hno ⟨Function.update x i₀ (x i₀ + g), ⟨fun i => ?_, ?_⟩, fun i => ?_, i₀, ?_⟩
  · by_cases hi : i = i₀
    · subst hi; intro s l; simp; linarith [hx i s l, hg0 s l]
    · rw [Function.update_of_ne hi]; exact hx i
  · rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    intro s l
    have : ∑ i ∈ Finset.univ \ {i₀}, x i + x i₀ = ∑ i, x i := by
      rw [← Finset.sum_sdiff (Finset.subset_univ {i₀}), Finset.sum_singleton]
    simp only [Pi.add_apply, hg, Pi.sub_apply]
    have h2 := congrFun (congrFun this s) l
    simp only [Pi.add_apply, Finset.sum_apply] at h2 ⊢
    linarith
  · by_cases hi : i = i₀
    · subst hi; rw [Function.update_self]
      by_cases hz : g = 0
      · rw [hz, add_zero]
      · exact (hU i _ _ (hx i) (fun s l => by simp [hg0 s l]) (fun h => hz (by
          funext s l; have := congrFun (congrFun h s) l; simpa using this))).le
    · rw [Function.update_of_ne hi]
  · rw [Function.update_self]
    refine hU i₀ _ _ (hx i₀) (fun s l => by simp [hg0 s l]) (fun h => hne ?_)
    funext s l
    have := congrFun (congrFun h s) l
    simp [hg] at this
    simp only [Finset.sum_apply]
    linarith

/-- The endowments of Example 19.C.2 have aggregate `(2, 1)`. -/
def AggregateTwoOne (ω : Fin 2 → CVec 2 1) : Prop :=
  ω 0 0 0 + ω 1 0 0 = 2 ∧ ω 0 1 0 + ω 1 1 0 = 1

/-- **Exercise 19.C.2** (MWG, p. 725), for Example 19.C.2. With aggregate risk `ω₁ + ω₂ = (2, 1)`,
common probabilities and state-independent good Bernoulli utilities, at every interior point of
the Pareto set both consumers' marginal rates of substitution
`π₁ uᵢ'(x₁ᵢ) / (π₂ uᵢ'(x₂ᵢ))` are below the probability ratio `π₁/π₂`, i.e.
`uᵢ'(x₁ᵢ) < uᵢ'(x₂ᵢ)`, and they are equal. -/
theorem exercise_19_C_2 {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω)
    (hpo : IsParetoOptimalU (fun i => eu1 π fun _ => u i) ω x) (hx : ∀ i s, 0 < x i s 0) :
    (∀ i, u' i (x i 0 0) < u' i (x i 1 0)) ∧
      π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) =
        π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) := by
  have htan := po_tangency hpo hx (fun i s => (hu i).2.2 _ (hx i s))
  have hex := po_exhausts (fun i => eu1_stronglyMonotone hπ fun _ => (hu i).2.1) hpo 0
  have h0 := congrFun (congrFun hex 0) 0
  have h1 := congrFun (congrFun hex 1) 0
  simp only [Fin.sum_univ_two, Pi.add_apply] at h0 h1
  have hd : ∀ i s, 0 < u' i (x i s 0) := fun i s => (hu i).deriv_pos (hx i s)
  have hπ0 := hπ 0; have hπ1 := hπ 1
  have hA := hd 0 0; have hB := hd 0 1; have hC := hd 1 0; have hD := hd 1 1
  refine ⟨?_, htan⟩
  rcases lt_or_ge (x 0 1 0) (x 0 0 0) with h00 | h00
  · have hlt0 := (hu 0).deriv_lt (hx 0 1) h00
    intro i; fin_cases i
    · exact hlt0
    · simp only [Fin.mk_one]
      by_contra hc
      push Not at hc
      have : π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) <
          π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) := by
        have e1 : u' 0 (x 0 0 0) * u' 1 (x 1 1 0) < u' 0 (x 0 1 0) * u' 1 (x 1 0 0) :=
          calc u' 0 (x 0 0 0) * u' 1 (x 1 1 0) < u' 0 (x 0 1 0) * u' 1 (x 1 1 0) :=
                mul_lt_mul_of_pos_right hlt0 hD
            _ ≤ u' 0 (x 0 1 0) * u' 1 (x 1 0 0) := mul_le_mul_of_nonneg_left hc hB.le
        nlinarith [mul_pos hπ0 hπ1]
      linarith
  · have hlt1 : x 1 1 0 < x 1 0 0 := by
      have : x 0 0 0 + x 1 0 0 = ω 0 0 0 + ω 1 0 0 := h0
      have : x 0 1 0 + x 1 1 0 = ω 0 1 0 + ω 1 1 0 := h1
      linarith [hω.1, hω.2]
    have hlt1' := (hu 1).deriv_lt (hx 1 1) hlt1
    intro i; fin_cases i
    · simp only [Fin.zero_eta]
      by_contra hc
      push Not at hc
      have : π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) <
          π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) := by
        have e1 : u' 1 (x 1 0 0) * u' 0 (x 0 1 0) < u' 1 (x 1 1 0) * u' 0 (x 0 0 0) :=
          calc u' 1 (x 1 0 0) * u' 0 (x 0 1 0) < u' 1 (x 1 1 0) * u' 0 (x 0 1 0) :=
                mul_lt_mul_of_pos_right hlt1' hB
            _ ≤ u' 1 (x 1 1 0) * u' 0 (x 0 0 0) := mul_le_mul_of_nonneg_left hc hD.le
        nlinarith [mul_pos hπ0 hπ1]
      linarith
    · exact hlt1'

/-- **Example 19.C.2** (MWG, p. 693). With aggregate risk `(2, 1)`, at every interior Arrow-Debreu
equilibrium `p₁/p₂ < π₁/π₂` (written `p₁ π₂ < p₂ π₁`): the contingent commodity is dearer, relative
to its probability, in the state where the good is scarcer. -/
theorem example_19_C_2 {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω)
    {p : CVec 2 1} (h : IsADEqmU (fun i => eu1 π fun _ => u i) ω x p)
    (hx : ∀ i s, 0 < x i s 0) : p 0 0 * π 1 < p 1 0 * π 0 := by
  have hpo := adEqmU_paretoOptimal (fun i => eu1_stronglyMonotone hπ fun _ => (hu i).2.1) h
  have hmrs := (exercise_19_C_2 hπ hu hω hpo hx).1 0
  obtain ⟨lam, hlam, hf⟩ := foc_eu1 (hx 0) (h.1 0).1.2 (h.1 0).2
    (fun s => (hu 0).2.2 _ (hx 0 s))
  have hA := (hu 0).deriv_pos (hx 0 0)
  have h0 := hf 0; have h1 := hf 1
  have hlam0 : 0 < lam := by
    rcases hlam.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at h0; nlinarith [hπ 0]
  have e0 : lam * (p 0 0 * π 1) = π 1 * (π 0 * u' 0 (x 0 0 0)) := by rw [h0]; ring
  have e1 : lam * (p 1 0 * π 0) = π 0 * (π 1 * u' 0 (x 0 1 0)) := by rw [h1]; ring
  have : lam * (p 0 0 * π 1) < lam * (p 1 0 * π 0) := by
    rw [e0, e1]
    have := mul_lt_mul_of_pos_left hmrs (mul_pos (hπ 0) (hπ 1))
    linarith
  exact lt_of_mul_lt_mul_left this hlam0.le

/-- **Example 19.C.2** (MWG, p. 693). If `π₁ = π₂ = 1/2`, then `p₁ < p₂`. -/
theorem example_19_C_2_equal {u u' : Fin 2 → ℝ → ℝ} (hu : ∀ i, GoodBernoulli (u i) (u' i))
    {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω) {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 (fun _ => 1 / 2) fun _ => u i) ω x p)
    (hx : ∀ i s, 0 < x i s 0) : p 0 0 < p 1 0 := by
  have := example_19_C_2 (π := fun _ => 1 / 2) (fun _ => by norm_num) hu hω h hx
  linarith

/-- **Exercise 19.C.3** (MWG, p. 726). At an Arrow-Debreu equilibrium with one good, a consumer
with strictly positive probabilities `πᵢ` (summing to one) and a state-independent, concave,
strictly increasing Bernoulli utility satisfies `∑_s (π_{si} p̄ - p_s) x_{si} ≥ 0`, where
`p̄ = ∑_s p_s` is the price of sure delivery of one unit. (Concavity suffices; the book assumes
strict concavity and continuity.) Interpretation: valued at the consumer's own probabilities and
the riskless price, his consumption is worth at least its market cost. -/
theorem exercise_19_C_3 [NeZero S] {ι : Type*} [Fintype ι] {π : ι → Fin S → ℝ}
    {u : ι → ℝ → ℝ} {ω x : ι → CVec S 1} {p : CVec S 1}
    (h : IsADEqmU (fun i => eu1 (π i) fun _ => u i) ω x p) (i : ι) (hπ : ∀ s, 0 < π i s)
    (hπ1 : ∑ s, π i s = 1) (hc : ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : StrictMonoOn (u i) (Set.Ici 0)) :
    0 ≤ ∑ s, (π i s * (∑ s', p s' 0) - p s 0) * x i s 0 := by
  have hsm : StronglyMonotoneC (eu1 (π i) fun _ => u i) := eu1_stronglyMonotone hπ fun _ => hm
  have hp : ∀ s, 0 ≤ p s 0 := by
    intro s
    by_contra hneg
    push Not at hneg
    have hx := (h.1 i).1.1
    have hle : x i ≤ x i + contingentUnit 0 s := fun s' l' => by
      simp only [Pi.add_apply, contingentUnit]; split_ifs <;> simp
    have hne : x i ≠ x i + contingentUnit 0 s := fun h' => by
      have := congrFun (congrFun h' s) 0
      simp [contingentUnit] at this
    have := (h.1 i).2 (x i + contingentUnit 0 s) (fun s' l' => (hx s' l').trans (hle s' l'))
      (by rw [cval_add, cval_unit]; linarith [(h.1 i).1.2])
    linarith [hsm _ _ hx hle hne]
  set pbar := ∑ s', p s' 0 with hpbar
  have hx := (h.1 i).1.1
  have hcost : cval p (x i) = ∑ s, p s 0 * x i s 0 := by simp [cval, dotProduct]
  have hpbar0 : 0 < pbar := by
    rcases (Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hp s).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz : ∀ s, p s 0 = 0 := fun s =>
        (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hp s).mp h'.symm s (Finset.mem_univ _)
      have hle : x i ≤ x i + fun _ _ => 1 := fun s l => by simp
      have hne : x i ≠ x i + fun _ _ => 1 := fun h' => by
        have := congrFun (congrFun h' ⟨0, NeZero.pos S⟩) 0; simp at this
      have := (h.1 i).2 (x i + fun _ _ => 1) (fun s l => by simp; linarith [hx s l])
        (by simp [cval, dotProduct, hz])
      linarith [hsm _ _ hx hle hne]
  set c := (∑ s, p s 0 * x i s 0) / pbar with hcdef
  have hc0 : 0 ≤ c := div_nonneg (Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (hx s 0))
    hpbar0.le
  have haff : cval p (fun _ _ => c) ≤ cval p (ω i) := by
    have : cval p (fun _ _ => c) = cval p (x i) := by
      rw [hcost]
      have e : cval p (fun _ _ => c) = pbar * c := by
        simp only [cval, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
          Finset.sum_singleton]
        rw [hpbar, Finset.sum_mul]
      rw [e, hcdef, mul_div_cancel₀ _ hpbar0.ne']
    rw [this]; exact (h.1 i).1.2
  have hrp := (h.1 i).2 (fun _ _ => c) (fun _ _ => hc0) haff
  have hconst : eu1 (π i) (fun _ => u i) (fun _ _ => c) = u i c := by
    simp [eu1, ← Finset.sum_mul, hπ1]
  set m := ∑ s, π i s * x i s 0 with hmdef
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun s _ => mul_nonneg (hπ s).le (hx s 0)
  have hjen : eu1 (π i) (fun _ => u i) (x i) ≤ u i m := by
    have := hc.le_map_sum (t := Finset.univ) (w := π i) (p := fun s => x i s 0)
      (fun s _ => (hπ s).le) hπ1 (fun s _ => Set.mem_Ici.mpr (hx s 0))
    simpa [eu1, smul_eq_mul] using this
  have hrp' : u i c ≤ eu1 (π i) (fun _ => u i) (x i) := by rw [← hconst]; exact hrp
  have hcm : c ≤ m := (hm.le_iff_le (Set.mem_Ici.mpr hc0) (Set.mem_Ici.mpr hm0)).mp
    (hrp'.trans hjen)
  have : ∑ s, p s 0 * x i s 0 ≤ pbar * m := by
    have := mul_le_mul_of_nonneg_left hcm hpbar0.le
    rwa [hcdef, mul_div_cancel₀ _ hpbar0.ne'] at this
  have hexp : ∑ s, (π i s * pbar - p s 0) * x i s 0 = pbar * m - ∑ s, p s 0 * x i s 0 := by
    rw [hmdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [hexp]; linarith

/-- The endowments of Exercise 19.C.4: each consumer has half of the aggregate `ω̄ ≫ 0`. -/
noncomputable def halfEndow (ωbar : Fin 2 → ℝ) : Fin 2 → CVec 2 1 :=
  fun _ => dirC fun s => ωbar s / 2

/-- **Exercise 19.C.4(a)** (MWG, p. 726). Consumer 1 is risk neutral (`u₁(x) = a x + b`, `a > 0`),
consumer 2 has a strictly concave Bernoulli utility, and the probabilities are common and strictly
positive. At an interior Arrow-Debreu equilibrium consumer 2 insures completely. (Only strict
concavity and differentiability of `u₂` at the equilibrium are used.) -/
theorem exercise_19_C_4a {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {a b : ℝ} (ha : 0 < a)
    {u₂ : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Set.Ici 0) u₂) {ωbar : Fin 2 → ℝ}
    {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU ![eu1 π fun _ t => a * t + b, eu1 π fun _ => u₂] (halfEndow ωbar) x p)
    (hx : ∀ i s, 0 < x i s 0) {D : Fin 2 → ℝ} (hD : ∀ s, HasDerivAt u₂ (D s) (x 1 s 0)) :
    x 1 0 0 = x 1 1 0 := by
  obtain ⟨l1, _, f1⟩ := foc_eu1 (u := fun _ t => a * t + b) (D := fun _ => a) (hx 0)
    (h.1 0).1.2 (h.1 0).2 (fun s => by simpa using ((hasDerivAt_id _).const_mul a).add_const b)
  obtain ⟨l2, _, f2⟩ := foc_eu1 (u := fun _ => u₂) (hx 1) (h.1 1).1.2 (h.1 1).2 hD
  have hl1 : 0 < l1 := by
    rcases (show (0 : ℝ) ≤ l1 by assumption).lt_or_eq with h' | h'
    · exact h'
    · have := f1 0; rw [← h', zero_mul] at this; nlinarith [hπ 0]
  have hDeq : D 0 = D 1 := by
    have e0 := f2 0; have e1 := f2 1; have g0 := f1 0; have g1 := f1 1
    have hp0 : p 0 0 = π 0 * a / l1 := by field_simp; linarith
    have hp1 : p 1 0 = π 1 * a / l1 := by field_simp; linarith
    rw [hp0] at e0; rw [hp1] at e1
    have h0' : D 0 = l2 * a / l1 := by
      have := hπ 0; field_simp at e0 ⊢; nlinarith
    have h1' : D 1 = l2 * a / l1 := by
      have := hπ 1; field_simp at e1 ⊢; nlinarith
    rw [h0', h1']
  exact eq_of_hasDerivAt_eq_of_strictConcaveOn hc (Set.mem_Ici.mpr (hx 1 0).le)
    (Set.mem_Ici.mpr (hx 1 1).le) (hD 0) (hDeq ▸ hD 1)

/-- **Exercise 19.C.4(b)** (MWG, p. 726). Consumer 1 risk neutral, consumer 2 with a good
Bernoulli utility, and different subjective probabilities. At an interior Arrow-Debreu equilibrium
consumer 2 does not insure completely: he consumes more in the state to which he gives relatively
more probability than consumer 1 does (`π₂₁/π₂₂ > π₁₁/π₁₂` gives `x₁₂ > x₂₂`); and consumer 1, the
risk-neutral agent, does not gain from trade (`U₁(x₁) = U₁(ω₁)`). -/
theorem exercise_19_C_4b {π : Fin 2 → Fin 2 → ℝ} (hπ : ∀ i s, 0 < π i s) {a b : ℝ}
    (ha : 0 < a) {u₂ u₂' : ℝ → ℝ} (hu : GoodBernoulli u₂ u₂') {ωbar : Fin 2 → ℝ}
    {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU ![eu1 (π 0) fun _ t => a * t + b, eu1 (π 1) fun _ => u₂] (halfEndow ωbar) x p)
    (hx : ∀ i s, 0 < x i s 0) (hbias : π 0 0 * π 1 1 < π 1 0 * π 0 1) :
    x 1 1 0 < x 1 0 0 ∧
      eu1 (π 0) (fun _ t => a * t + b) (x 0) = eu1 (π 0) (fun _ t => a * t + b) (halfEndow ωbar 0)
    := by
  obtain ⟨l1, _, f1⟩ := foc_eu1 (u := fun _ t => a * t + b) (D := fun _ => a) (hx 0)
    (h.1 0).1.2 (h.1 0).2 (fun s => by simpa using ((hasDerivAt_id _).const_mul a).add_const b)
  obtain ⟨l2, hl2, f2⟩ := foc_eu1 (u := fun _ => u₂) (hx 1) (h.1 1).1.2 (h.1 1).2
    (fun s => hu.2.2 _ (hx 1 s))
  have hl1 : 0 < l1 := by
    rcases (show (0 : ℝ) ≤ l1 by assumption).lt_or_eq with h' | h'
    · exact h'
    · have := f1 0; rw [← h', zero_mul] at this; nlinarith [hπ 0 0]
  have hd0 := hu.deriv_pos (hx 1 0)
  have hd1 := hu.deriv_pos (hx 1 1)
  have g0 := f1 0; have g1 := f1 1; have e0 := f2 0; have e1 := f2 1
  refine ⟨?_, ?_⟩
  · by_contra hge
    push Not at hge
    have hle : u₂' (x 1 1 0) ≤ u₂' (x 1 0 0) := by
      rcases hge.lt_or_eq with h' | h'
      · exact (hu.deriv_lt (hx 1 0) h').le
      · rw [h']
    have k1 : π 1 0 * u₂' (x 1 0 0) * π 0 1 = π 1 1 * u₂' (x 1 1 0) * π 0 0 := by
      have : (π 1 0 * u₂' (x 1 0 0) * π 0 1) * a = (π 1 1 * u₂' (x 1 1 0) * π 0 0) * a := by
        calc (π 1 0 * u₂' (x 1 0 0) * π 0 1) * a = (π 1 0 * u₂' (x 1 0 0)) * (π 0 1 * a) := by
              ring
          _ = (l2 * p 0 0) * (l1 * p 1 0) := by rw [e0, g1]
          _ = (l2 * p 1 0) * (l1 * p 0 0) := by ring
          _ = (π 1 1 * u₂' (x 1 1 0)) * (π 0 0 * a) := by rw [e1, g0]
          _ = (π 1 1 * u₂' (x 1 1 0) * π 0 0) * a := by ring
      exact mul_right_cancel₀ ha.ne' this
    have h3 : π 1 0 * π 0 1 * u₂' (x 1 0 0) ≤ π 1 1 * π 0 0 * u₂' (x 1 0 0) := by
      have h4 := mul_le_mul_of_nonneg_left hle (mul_pos (hπ 1 1) (hπ 0 0)).le
      nlinarith [k1]
    have := le_of_mul_le_mul_right h3 hd0
    linarith
  · have hsm : ∀ i, StronglyMonotoneC
        (![eu1 (π 0) fun _ t => a * t + b, eu1 (π 1) fun _ => u₂] i) := by
      intro i; fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        exact eu1_stronglyMonotone (hπ 0) fun _ _ _ _ _ hxy =>
          add_lt_add_left (mul_lt_mul_of_pos_left hxy ha) b
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact eu1_stronglyMonotone (hπ 1) fun _ => hu.2.1
    have hbind := adEqmU_budget_binds hsm h 0
    simp only [cval, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Fin.sum_univ_two] at hbind
    have hU : a * (π 0 0 * x 0 0 0 + π 0 1 * x 0 1 0) =
        a * (π 0 0 * halfEndow ωbar 0 0 0 + π 0 1 * halfEndow ωbar 0 1 0) := by
      have e : l1 * (p 0 0 * x 0 0 0 + p 1 0 * x 0 1 0) =
          l1 * (p 0 0 * halfEndow ωbar 0 0 0 + p 1 0 * halfEndow ωbar 0 1 0) := by rw [hbind]
      linear_combination e + (x 0 0 0 - halfEndow ωbar 0 0 0) * g0 +
        (x 0 1 0 - halfEndow ωbar 0 1 0) * g1
    simp only [eu1, Fin.sum_univ_two]
    linear_combination hU

/-- **Exercise 19.C.5** (MWG, p. 726). One good, risk-averse consumers (concave, nondecreasing
state-independent Bernoulli utilities), common probabilities and a nonstochastic aggregate
endowment. Then the allocation in which every consumer consumes, in every state, the expected
value `∑_s π_s ω_{si}` of his endowment is an Arrow-Debreu equilibrium allocation, supported by
the prices `p_s = π_s`. -/
theorem exercise_19_C_5 {ι : Type*} [Fintype ι] {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s)
    (hπ1 : ∑ s, π s = 1) {u : ι → ℝ → ℝ} (hc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, MonotoneOn (u i) (Set.Ici 0)) {ω : ι → CVec S 1} (hω0 : ∀ i, NonnegC (ω i))
    (hagg : ∀ s s', ∑ i, ω i s 0 = ∑ i, ω i s' 0) :
    IsADEqmU (fun i => eu1 π fun _ => u i) ω (fun i _ _ => ∑ s, π s * ω i s 0)
      (fun s _ => π s) := by
  have hm0 : ∀ i, 0 ≤ ∑ s, π s * ω i s 0 := fun i =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hω0 i s 0)
  have hval : ∀ y : CVec S 1, cval (fun s _ => π s) y = ∑ s, π s * y s 0 := fun y => by
    simp [cval, dotProduct]
  refine ⟨fun i => ⟨⟨fun _ _ => hm0 i, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
  · rw [hval, hval, ← Finset.sum_mul, hπ1, one_mul]
  · rw [hval, hval] at hb
    have hjen := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := fun s => x' s 0)
      (fun s _ => hπ s) hπ1 (fun s _ => Set.mem_Ici.mpr (hx' s 0))
    simp only [smul_eq_mul] at hjen
    have hconst : eu1 π (fun _ => u i) (fun _ _ => ∑ s, π s * ω i s 0) =
        u i (∑ s, π s * ω i s 0) := by simp [eu1, ← Finset.sum_mul, hπ1]
    dsimp only
    rw [hconst]
    exact hjen.trans (hm i (Set.mem_Ici.mpr (Finset.sum_nonneg fun s _ =>
      mul_nonneg (hπ s) (hx' s 0))) (Set.mem_Ici.mpr (hm0 i)) hb)
  · funext s l
    rw [Subsingleton.elim l 0]
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    calc ∑ s', ∑ i, π s' * ω i s' 0 = ∑ s', π s' * ∑ i, ω i s 0 :=
          Finset.sum_congr rfl fun s' _ => by rw [← Finset.mul_sum, hagg s' s]
      _ = ∑ i, ω i s 0 := by rw [← Finset.sum_mul, hπ1, one_mul]

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Sequential trade and Radner equilibrium (MWG Section 19.D, pp. 694-699)

Two dates, uncertainty resolved at `t = 1`, no consumption at `t = 0`. The physical good in which
contingent trade (and later asset returns) is denominated is a parameter `g : Fin L` (the book's
"good 1").

* The Radner budget set and Radner equilibrium for an asset structure with `S × K` return matrix
  `R` (`radnerFeasible`, `IsRadnerEqm`): this is Definition 19.E.2; **Definition 19.D.1** is the
  case `K = S`, `R = I` of contingent trade in good `g` (`IsRadnerEqmD`, `definition_19_D_1`).
* Homogeneity of the budget constraints (p. 696): budget sets are unchanged when each spot price
  vector and the date-0 prices are rescaled (`radnerFeasible_rescale`).
* **Proposition 19.D.1**: (i) Arrow-Debreu equilibria are Radner equilibria with `q_s = p_{gs}`;
  (ii) Radner equilibria with `q ≫ 0`, `p_{gs} > 0` give Arrow-Debreu budget sets for the prices
  `μ_s p_s`, `μ_s = q_s / p_{gs}`. As printed, (ii) concludes an Arrow-Debreu equilibrium, whose
  definition (19.C.1(iii)) requires market clearing with *equality*, while a Radner equilibrium
  only requires `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ`. Without monotonicity this fails
  (`proposition_19_D_1_ii_counterexample`); it holds with strongly monotone utilities
  (`proposition_19_D_1_ii`), and in general with the inequality (`proposition_19_D_1_ii_le`).
  Correction 2.
* **p. 694 and footnote 5**: at an Arrow-Debreu equilibrium there is no incentive to retrade
  ex post (`no_expost_trade`), and the state-`s` contingent prices are equilibrium spot prices
  (`footnote_19_5`).
* **Footnote 7** (initial endowments of contingent commodities), **footnote 8** and **Exercise
  19.D.1** (contingent commodities paying dollars, and the normalizations).
* **Example 19.D.1** and **Exercise 19.D.2**: the symmetric two-state, two-good economy.
* **Exercise 19.D.3** (consumption at `t = 0`) and **Exercise 19.D.4** (three dates, binary tree):
  Proposition 19.D.1 remains valid.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ} {ι : Type*} [Fintype ι]

/-- **Definition 19.E.2(i)** (MWG, p. 701; Definition 19.D.1 with `R = I`). The plan `(x, z)` is in
consumer's budget set: `x ≥ 0`, (a) `q·z ≤ 0`, (b) `p_s·x_s ≤ p_s·ω_s + p_{gs} ∑_k r_{sk} z_k` in
every state. -/
def radnerFeasible (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s

/-- **Definition 19.E.2** (MWG, p. 701). `(q, p, z*, x*)` is a Radner equilibrium: (i) every
`(z*ᵢ, x*ᵢ)` solves consumer `i`'s problem; (ii) `∑ᵢ z*_{ki} ≤ 0` and `∑ᵢ x*_{si} ≤ ∑ᵢ ω_{si}`. -/
def IsRadnerEqm (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S L → ℝ)
    (ω : ι → CVec S L) (q : Fin K → ℝ) (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin K → ℝ) :
    Prop :=
  (∀ i, radnerFeasible g R q p (ω i) (x i) (z i) ∧
    ∀ x' z', radnerFeasible g R q p (ω i) x' z' → U i x' ≤ U i (x i)) ∧
    (∀ k, ∑ i, z i k ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i

/-- **Definition 19.D.1** (MWG, p. 696). A Radner equilibrium with contingent trade in good `g`
only: the asset structure of the `S` contingent commodities `gs` (`R = I`). -/
def IsRadnerEqmD (g : Fin L) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin S → ℝ)
    (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin S → ℝ) : Prop :=
  IsRadnerEqm g (1 : Matrix (Fin S) (Fin S) ℝ) U ω q p x z

/-- **Definition 19.D.1** (MWG, p. 696), unfolded: problem (19.D.1) with constraints
(i) `∑_s q_s z_s ≤ 0` and (ii) `p_s·x_s ≤ p_s·ω_s + p_{gs} z_s`, and market clearing. -/
theorem definition_19_D_1 (g : Fin L) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L)
    (q : Fin S → ℝ) (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin S → ℝ) :
    IsRadnerEqmD g U ω q p x z ↔
      (∀ i, (NonnegC (x i) ∧ q ⬝ᵥ z i ≤ 0 ∧ ∀ s, p s ⬝ᵥ x i s ≤ p s ⬝ᵥ ω i s + p s g * z i s) ∧
        ∀ x' z', (NonnegC x' ∧ q ⬝ᵥ z' ≤ 0 ∧ ∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ ω i s + p s g * z' s) →
          U i x' ≤ U i (x i)) ∧
      (∀ s, ∑ i, z i s ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i := by
  simp [IsRadnerEqmD, IsRadnerEqm, radnerFeasible, one_mulVec]

/-- **p. 696**. All budget constraints are homogeneous of degree zero: rescaling the date-0 prices
by `c > 0` and the spot prices of state `s` by `d_s > 0` leaves the budget set unchanged (so one
can put `p_{gs} = 1` in every state and, say, `q₁ = 1`). -/
theorem radnerFeasible_rescale (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    (p ω x : CVec S L) (z : Fin K → ℝ) {c : ℝ} (hc : 0 < c) {d : Fin S → ℝ} (hd : ∀ s, 0 < d s) :
    radnerFeasible g R (c • q) (fun s => d s • p s) ω x z ↔ radnerFeasible g R q p ω x z := by
  unfold radnerFeasible
  simp only [smul_dotProduct, smul_eq_mul, Pi.smul_apply]
  refine and_congr Iff.rfl (and_congr ⟨fun h => ?_, fun h => mul_nonpos_of_nonneg_of_nonpos
    hc.le h⟩ (forall_congr' fun s => ?_))
  · exact nonpos_of_mul_nonpos_right h hc
  · constructor
    · intro h
      have : d s * (p s ⬝ᵥ x s) ≤ d s * (p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s) := by linarith
      exact le_of_mul_le_mul_left this (hd s)
    · intro h
      nlinarith [hd s]

/-! ## Proposition 19.D.1 -/

/-- The Arrow-Debreu budget set `{x ≥ 0 : ∑_s p_s·(x_s - ω_s) ≤ 0}` (proof of Proposition
19.D.1). -/
def adBudget (p ω : CVec S L) : Set (CVec S L) := {x | NonnegC x ∧ cval p x ≤ cval p ω}

/-- **Proposition 19.D.1, proof of (i)** (MWG, p. 697). With `q_s = p_{gs} > 0`, the Arrow-Debreu
budget set equals the Radner budget set `B_i^R`. -/
theorem adBudget_eq_radner (g : Fin L) {p : CVec S L} (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    x ∈ adBudget p ω ↔ ∃ z, radnerFeasible g 1 (fun s => p s g) p ω x z := by
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨fun s => p s ⬝ᵥ (x s - ω s) / p s g, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct, mul_div_cancel₀ _ (hp _).ne']
      have : cval p x - cval p ω = ∑ s, p s ⬝ᵥ (x s - ω s) := by
        simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
      simp only [dotProduct] at this
      linarith
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨hx, ?_⟩
    simp only [one_mulVec] at hs
    have h1 : ∑ s, (p s ⬝ᵥ x s - p s ⬝ᵥ ω s) ≤ ∑ s, p s g * z s :=
      Finset.sum_le_sum fun s _ => by linarith [hs s]
    simp only [dotProduct] at hq
    rw [Finset.sum_sub_distrib] at h1
    unfold cval
    linarith

/-- **Proposition 19.D.1(i)** (MWG, p. 697). If `x*` and `p` with `p_{gs} > 0` form an Arrow-Debreu
equilibrium, then `q_s = p_{gs}`, the spot prices `p_s` and the contingent trades
`z*_{si} = p_s·(x*_{si} - ω_{si}) / p_{gs}` form, with `x*`, a Radner equilibrium. -/
theorem proposition_19_D_1_i (g : Fin L) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    {p : CVec S L} (hp : ∀ s, 0 < p s g) (h : IsADEqmU U ω x p) :
    IsRadnerEqmD g U ω (fun s => p s g) p x
      (fun i s => p s ⬝ᵥ (x i s - ω i s) / p s g) := by
  refine ⟨fun i => ⟨?_, fun x' z' hf => ?_⟩, fun s => ?_, h.2.le⟩
  · obtain ⟨z, hz⟩ := (adBudget_eq_radner g hp (ω i) (x i)).mp (h.1 i).1
    refine ⟨hz.1, ?_, fun s => ?_⟩
    · simp only [dotProduct, mul_div_cancel₀ _ (hp _).ne']
      have : cval p (x i) - cval p (ω i) = ∑ s, p s ⬝ᵥ (x i s - ω i s) := by
        simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
      simp only [dotProduct] at this
      linarith [(h.1 i).1.2]
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith
  · exact (h.1 i).2 x' ((adBudget_eq_radner g hp (ω i) x').mpr ⟨z', hf⟩).1
      ((adBudget_eq_radner g hp (ω i) x').mpr ⟨z', hf⟩).2
  · rw [← Finset.sum_div, ← dotProduct_sum, Finset.sum_sub_distrib]
    have : ∑ i, x i s = ∑ i, ω i s := by
      have := congrFun h.2 s; simpa [Finset.sum_apply] using this
    rw [this, sub_self, dotProduct_zero, zero_div]

/-- **Proposition 19.D.1, proof of (ii)** (MWG, p. 697). With `q ≥ 0` and `p_{gs} > 0`, put
`μ_s = q_s / p_{gs}`; the Radner budget set equals the Arrow-Debreu budget set at the prices
`μ_s p_s`. -/
theorem radner_eq_adBudget (g : Fin L) {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    (∃ z, radnerFeasible g 1 q p ω x z) ↔
      x ∈ adBudget (fun s => (q s / p s g) • p s) ω := by
  constructor
  · rintro ⟨z, hx, hqz, hs⟩
    refine ⟨hx, ?_⟩
    simp only [one_mulVec] at hs
    simp only [cval, smul_dotProduct, smul_eq_mul]
    have h1 : ∀ s, q s / p s g * (p s ⬝ᵥ x s) ≤ q s / p s g * (p s ⬝ᵥ ω s) + q s * z s := by
      intro s
      have hμ : 0 ≤ q s / p s g := div_nonneg (hq s) (hp s).le
      have := mul_le_mul_of_nonneg_left (hs s) hμ
      rw [mul_add, ← mul_assoc, div_mul_cancel₀ _ (hp s).ne'] at this
      exact this
    have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
    rw [Finset.sum_add_distrib] at h2
    simp only [dotProduct] at hqz
    linarith
  · rintro ⟨hx, hb⟩
    refine ⟨fun s => p s ⬝ᵥ (x s - ω s) / p s g, hx, ?_, fun s => ?_⟩
    · simp only [cval, smul_dotProduct, smul_eq_mul] at hb
      have e : q ⬝ᵥ (fun s => p s ⬝ᵥ (x s - ω s) / p s g) =
          ∑ s, q s / p s g * (p s ⬝ᵥ x s) - ∑ s, q s / p s g * (p s ⬝ᵥ ω s) := by
        simp only [dotProduct_sub]
        rw [dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [e]; linarith
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith

/-- An allocation that clears with `≤` and has binding budgets at prices `c ≫ 0` clears exactly. -/
theorem clear_eq_of_binding {c : CVec S L} (hc : ∀ s l, 0 < c s l) {ω x : ι → CVec S L}
    (hle : ∑ i, x i ≤ ∑ i, ω i) (hbind : ∀ i, cval c (x i) = cval c (ω i)) :
    ∑ i, x i = ∑ i, ω i := by
  have hsum : cval c (∑ i, ω i - ∑ i, x i) = 0 := by
    rw [cval_sub, cval_sum, cval_sum, Finset.sum_congr rfl fun i _ => (hbind i).symm, sub_self]
  have hnn : ∀ s l, 0 ≤ (∑ i, ω i - ∑ i, x i) s l := fun s l => by
    have := hle s l; simp only [Pi.sub_apply]; linarith
  have hz : ∀ s l, (∑ i, ω i - ∑ i, x i) s l = 0 := by
    intro s l
    unfold cval dotProduct at hsum
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (hc s l).le (hnn s l)).mp hsum s (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ =>
      mul_nonneg (hc s l).le (hnn s l)).mp h1 l (Finset.mem_univ _)
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (hc s l).ne'
    · exact h
  funext s l
  have := hz s l
  simp only [Pi.sub_apply] at this
  linarith

/-- **Proposition 19.D.1(ii)**, the part that holds as stated for any utilities: if
`(q, p, z*, x*)` is a Radner equilibrium with `q ≥ 0` and `p_{gs} > 0`, then with
`μ_s = q_s / p_{gs}` every `x*ᵢ` is utility maximizing in the Arrow-Debreu budget set at the
prices `(μ_s p_s)`, and `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ`. -/
theorem proposition_19_D_1_ii_le (g : Fin L) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L} (hp : ∀ s, 0 < p s g)
    {z : ι → Fin S → ℝ} (h : IsRadnerEqmD g U ω q p x z) :
    (∀ i, (NonnegC (x i) ∧ cval (fun s => (q s / p s g) • p s) (x i) ≤
        cval (fun s => (q s / p s g) • p s) (ω i)) ∧
      ∀ x', NonnegC x' → cval (fun s => (q s / p s g) • p s) x' ≤
        cval (fun s => (q s / p s g) • p s) (ω i) → U i x' ≤ U i (x i)) ∧
      ∑ i, x i ≤ ∑ i, ω i := by
  refine ⟨fun i => ⟨(radner_eq_adBudget g hq hp (ω i) (x i)).mp ⟨z i, (h.1 i).1⟩,
    fun x' hx' hb => ?_⟩, h.2.2⟩
  obtain ⟨z', hz'⟩ := (radner_eq_adBudget g hq hp (ω i) x').mpr ⟨hx', hb⟩
  exact (h.1 i).2 x' z' hz'

/-- **Proposition 19.D.1(ii)** (MWG, p. 697), with strongly monotone utilities (and `S, L ≥ 1`):
a Radner equilibrium with `q ≫ 0` and `p ≫ 0` gives the Arrow-Debreu equilibrium `x*` at the
contingent prices `(μ₁ p₁, …, μ_S p_S)`, `μ_s = q_s / p_{gs} > 0`. -/
theorem proposition_19_D_1_ii [NeZero S] [NeZero L] (g : Fin L) {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {q : Fin S → ℝ}
    (hq : ∀ s, 0 < q s) {p : CVec S L} (hp : ∀ s l, 0 < p s l) {z : ι → Fin S → ℝ}
    (h : IsRadnerEqmD g U ω q p x z) :
    IsADEqmU U ω x (fun s => (q s / p s g) • p s) := by
  obtain ⟨hopt, hle⟩ := proposition_19_D_1_ii_le g (fun s => (hq s).le) (fun s => hp s g) h
  have hbind : ∀ i, cval (fun s => (q s / p s g) • p s) (x i) =
      cval (fun s => (q s / p s g) • p s) (ω i) := by
    intro i
    refine le_antisymm (hopt i).1.2 (not_lt.mp fun hlt => ?_)
    obtain ⟨x', hle', hne, hc⟩ := exists_larger_cheap (fun s => (q s / p s g) • p s) (x i)
      (sub_pos.mpr hlt)
    have hx := (hopt i).1.1
    have := (hopt i).2 x' (fun s l => (hx s l).trans (hle' s l)) (by linarith)
    linarith [hU i _ _ hx hle' hne]
  refine ⟨hopt, clear_eq_of_binding (fun s l => ?_) hle hbind⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (div_pos (hq s) (hp s g)) (hp s l)

/-- **Proposition 19.D.1(ii)** as printed fails without monotonicity (correction 2): one state,
one good, one consumer with endowment `1` and constant utility. `x* = 0`, `z* = 0` with `q = 1`,
`p = 1` is a Radner equilibrium, but no contingent price vector makes `x*` an Arrow-Debreu
equilibrium, since Definition 19.C.1(iii) requires `∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`. -/
theorem proposition_19_D_1_ii_counterexample :
    IsRadnerEqmD (S := 1) (L := 1) (ι := Fin 1) 0 (fun _ _ => 0) (fun _ _ _ => 1) (fun _ => 1)
        (fun _ _ => 1) (fun _ _ _ => 0) (fun _ _ => 0) ∧
      ∀ c : CVec 1 1,
        ¬ IsADEqmU (ι := Fin 1) (fun _ _ => 0) (fun _ _ _ => 1) (fun _ _ _ => 0) c := by
  refine ⟨⟨fun _ => ⟨⟨fun _ _ => le_rfl, by simp, fun _ => by simp [dotProduct]⟩,
    fun _ _ _ => le_rfl⟩,
    fun _ => by simp, fun _ _ => by simp⟩, fun c hc => ?_⟩
  have := congrFun (congrFun hc.2 0) 0
  simp at this

/-! ## No ex post trade (p. 694) and footnote 5 -/

/-- **p. 694**. If the allocation `x*` is Pareto optimal (as Arrow-Debreu equilibrium allocations
are, `adEqmU_paretoOptimal`), then after any state `s` is revealed no reallocation of the state-`s`
endowments makes every consumer at least as well off and some consumer better off: ex ante Pareto
optimality implies ex post Pareto optimality. -/
theorem no_expost_trade {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    (hpo : IsParetoOptimalU U ω x) (s : Fin S) :
    ¬ ∃ y : ι → Fin L → ℝ, (∀ i l, 0 ≤ y i l) ∧ ∑ i, y i ≤ ∑ i, ω i s ∧
      (∀ i, U i (x i) ≤ U i (Function.update (x i) s (y i))) ∧
      ∃ i, U i (x i) < U i (Function.update (x i) s (y i)) := by
  classical
  rintro ⟨y, hy, hys, hge, k, hk⟩
  refine hpo.2 ⟨fun i => Function.update (x i) s (y i), ⟨fun i s' l => ?_, fun s' l => ?_⟩,
    hge, k, hk⟩
  · by_cases hs : s' = s
    · subst hs; simp [hy i l]
    · have e : Function.update (x i) s (y i) s' = x i s' := Function.update_of_ne hs _ _
      simp only [e]; exact hpo.1.1 i s' l
  · by_cases hs : s' = s
    · subst hs
      have := hys l
      simpa [Finset.sum_apply] using this
    · have := hpo.1.2 s' l
      simpa [Finset.sum_apply, Function.update_of_ne hs] using this

/-- **Footnote 5** (MWG, p. 694). If `x*` maximizes `U` on the Arrow-Debreu budget set, then for
every state `s`, `x*_s` maximizes `U(x*₁, …, x_s, …, x*_S)` subject to
`p_s·(x_s - ω_s) ≤ p_s·(x*_s - ω_s)`: the state-`s` contingent prices are spot prices at which the
initial vector `(x*_{s1}, …, x*_{sI})` is an equilibrium with null excess demand. -/
theorem footnote_19_5 {U : CVec S L → ℝ} {p ω x : CVec S L} (hx : x ∈ adBudget p ω)
    (hmax : ∀ x' ∈ adBudget p ω, U x' ≤ U x) (s : Fin S) (y : Fin L → ℝ) (hy : ∀ l, 0 ≤ y l)
    (hb : p s ⬝ᵥ (y - ω s) ≤ p s ⬝ᵥ (x s - ω s)) : U (Function.update x s y) ≤ U x := by
  classical
  refine hmax _ ⟨fun s' l => ?_, ?_⟩
  · by_cases hs : s' = s
    · subst hs; simp [hy l]
    · rw [Function.update_of_ne hs]; exact hx.1 s' l
  · have h1 : cval p (Function.update x s y) = cval p x + p s ⬝ᵥ (y - x s) := by
      unfold cval
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ Finset.univ.erase s, p s' ⬝ᵥ Function.update x s y s' =
          ∑ s' ∈ Finset.univ.erase s, p s' ⬝ᵥ x s' :=
        Finset.sum_congr rfl fun s' hs' => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hs')]
      rw [this, Function.update_self, dotProduct_sub]; ring
    rw [h1]
    rw [dotProduct_sub, dotProduct_sub] at hb
    rw [dotProduct_sub]
    linarith [hx.2]

/-! ## Footnotes 7-8 and Exercise 19.D.1 -/

/-- **Footnote 7** (MWG, p. 696). If good `g` available at `t = 1` in state `s` is regarded as an
initial endowment of the `s`-contingent commodity, the constraints become
(i') `∑_s q_s(z'_s - ω_{gs}) ≤ 0` and (ii') `p_s·x_s ≤ ∑_{l ≠ g} p_{ls} ω_{ls} + p_{gs} z'_s`; with
`z'_s = z_s + ω_{gs}` they are exactly the constraints of (19.D.1). -/
theorem footnote_19_7 (g : Fin L) (q : Fin S → ℝ) (p ω x : CVec S L) (z : Fin S → ℝ) :
    (q ⬝ᵥ (fun s => (z s + ω s g) - ω s g) ≤ 0 ∧
      ∀ s, p s ⬝ᵥ x s ≤ (p s ⬝ᵥ ω s - p s g * ω s g) + p s g * (z s + ω s g)) ↔
      (q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * z s) := by
  have e1 : (fun s => (z s + ω s g) - ω s g) = z := by funext s; ring
  have e2 : ∀ s, (p s ⬝ᵥ ω s - p s g * ω s g) + p s g * (z s + ω s g) =
      p s ⬝ᵥ ω s + p s g * z s := fun s => by ring
  simp only [e1, e2]

/-- **Exercise 19.D.1** (MWG, p. 726; footnote 8). If the `s`-contingent commodity pays one
dollar (instead of one unit of good `g`), the budget constraints are `∑_s q_s z_s ≤ 0` and
`p_s·x_s ≤ p_s·ω_s + z_s`. -/
def dollarFeasible (q : Fin S → ℝ) (p ω x : CVec S L) (z : Fin S → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + z s

/-- **Exercise 19.D.1** (MWG, p. 726), the normalizations. The budget set is unchanged when
`q` is scaled by `c > 0` and, state by state, the spot prices are scaled by `d_s > 0` and `q_s` by
`1 / d_s` (the dollar claims are rescaled to `d_s z_s`). Hence one can normalize one price in
every spot market and one date-0 price, as in Section 19.D. -/
theorem exercise_19_D_1 (q : Fin S → ℝ) (p ω x : CVec S L) {c : ℝ} (hc : 0 < c)
    {d : Fin S → ℝ} (hd : ∀ s, 0 < d s) :
    (∃ z, dollarFeasible (fun s => c * q s / d s) (fun s => d s • p s) ω x z) ↔
      ∃ z, dollarFeasible q p ω x z := by
  constructor
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => z s / d s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, c * q s / d s * z s = c * ∑ s, q s * (z s / d s) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [this] at hq
      exact nonpos_of_mul_nonpos_right hq hc
    · have := hs s
      simp only [smul_dotProduct, smul_eq_mul] at this
      have h2 : d s * (p s ⬝ᵥ x s) ≤ d s * (p s ⬝ᵥ ω s + z s / d s) := by
        rw [mul_add, mul_div_cancel₀ _ (hd s).ne']; exact this
      exact le_of_mul_le_mul_left h2 (hd s)
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => d s * z s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, c * q s / d s * (d s * z s) = c * ∑ s, q s * z s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by field_simp [(hd s).ne']
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hq
    · simp only [smul_dotProduct, smul_eq_mul]
      nlinarith [hs s, hd s]

/-- **Exercise 19.D.1** (MWG, p. 726). With `p_{gs} > 0`, dollar-paying contingent commodities at
prices `q_s` give the same budget sets as good-`g`-paying ones at prices `q_s p_{gs}`. -/
theorem exercise_19_D_1_dollars_goods (g : Fin L) (q : Fin S → ℝ) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    (∃ z, dollarFeasible q p ω x z) ↔
      ∃ z, radnerFeasible g 1 (fun s => q s * p s g) p ω x z := by
  constructor
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => z s / p s g, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, q s * p s g * (z s / p s g) = ∑ s, q s * z s :=
        Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
      rw [this]; exact hq
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne']; exact hs s
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => p s g * z s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, q s * (p s g * z s) = ∑ s, q s * p s g * z s :=
        Finset.sum_congr rfl fun s _ => by ring
      rw [this]; exact hq
    · have := hs s; simp only [one_mulVec] at this; exact this

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Sequential trade: Example 19.D.1 and Exercises 19.D.2-19.D.4 (MWG pp. 697-699, 726-727)

* **Example 19.D.1**: two equally likely states, two goods, two consumers with the same
  state-independent concave Bernoulli utility; consumer 1 owns the aggregate endowment `ω̄` in
  state 1, consumer 2 in state 2. If `ω̄/2` is demanded at spot prices `p̂` with wealth `p̂·ω̄/2`
  (a symmetric spot equilibrium, as with `u = min`), giving everybody `ω̄/2` in each state is an
  Arrow-Debreu equilibrium with the same spot prices in both states (`example_19_D_1`), with an
  instance (`example_19_D_1_instance`); with a strictly concave, strongly monotone `u` every
  Arrow-Debreu equilibrium allocation is state independent (`example_19_D_1_stateIndependent`).
* **Exercise 19.D.2**: the contingent trades reaching it: consumer 1 sells `α` units of good 1
  contingent on state 1 and buys `β = α` contingent on state 2 (`exercise_19_D_2`).
* **Exercise 19.D.3**: with consumption at `t = 0`, the budget sets of the two formulations
  coincide in both directions (`exercise_19_D_3_i`, `exercise_19_D_3_ii`).
* **Exercise 19.D.4**: three dates and a binary tree: (a) the Arrow-Debreu budget constraint,
  (b) the Radner budget constraints with contingent trade in good `g` at `t = 0` and `t = 1`,
  (c) the budget sets coincide in both directions (`exercise_19_D_4c_i`, `exercise_19_D_4c_ii`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## Example 19.D.1 and Exercise 19.D.2 -/

/-- The endowments of Example 19.D.1: consumer 1 owns `ω̄` in state 1, consumer 2 in state 2. -/
def omega19D1 (ωbar : Fin 2 → ℝ) : Fin 2 → CVec 2 2 :=
  fun i s => if i = s then ωbar else 0

/-- **Example 19.D.1** (MWG, pp. 697-698). Equal probabilities, a common state-independent Bernoulli
utility `u` concave on `ℝ²_+`. If `ω̄/2` maximizes `u` on `{y ≥ 0 : p̂·y ≤ p̂·ω̄/2}`, then giving
each consumer half of the aggregate endowment in each state is an Arrow-Debreu equilibrium at the
contingent prices `(p̂, p̂)`: the spot prices are the same in the two states. -/
theorem example_19_D_1 {u : (Fin 2 → ℝ) → ℝ} (hu : ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u)
    {ωbar phat : Fin 2 → ℝ} (hω : ∀ l, 0 ≤ ωbar l)
    (hmax : ∀ y : Fin 2 → ℝ, (∀ l, 0 ≤ y l) → phat ⬝ᵥ y ≤ phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) →
      u y ≤ u ((1 / 2 : ℝ) • ωbar)) :
    IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar)
      (fun _ _ => (1 / 2 : ℝ) • ωbar) (fun _ => phat) := by
  have hval : ∀ i : Fin 2, cval (fun _ => phat) (omega19D1 ωbar i) = phat ⬝ᵥ ωbar := by
    intro i; fin_cases i <;> simp [cval, omega19D1, Fin.sum_univ_two]
  have hstar : cval (fun _ : Fin 2 => phat) (fun _ => (1 / 2 : ℝ) • ωbar) = phat ⬝ᵥ ωbar := by
    simp [cval]
  refine ⟨fun i => ⟨⟨fun s l => by simp; linarith [hω l], by rw [hstar, hval]⟩,
    fun x' hx' hb => ?_⟩, ?_⟩
  · rw [hval] at hb
    have hjen := hu.2 (hx' 0) (hx' 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hbud : phat ⬝ᵥ ((1 / 2 : ℝ) • x' 0 + (1 / 2 : ℝ) • x' 1) ≤
        phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      simp only [cval, Fin.sum_univ_two] at hb
      linarith
    have hm := hmax _ (fun l => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx' 0 l, hx' 1 l]) hbud
    simp only [expUtil, Fin.sum_univ_two, smul_eq_mul] at hjen ⊢
    linarith
  · funext s l
    fin_cases s <;> simp [omega19D1, Fin.sum_univ_two]

/-- **Example 19.D.1**, an instance: `u(y) = min(y₁, y₂)` (concave), `ω̄ = (1, 1)`,
`p̂ = (1, 1)`. -/
theorem example_19_D_1_instance :
    IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ (y : Fin 2 → ℝ) => min (y 0) (y 1))
      (omega19D1 fun _ => 1) (fun _ _ => (1 / 2 : ℝ) • fun _ => 1) (fun _ _ => 1) := by
  refine example_19_D_1 ⟨?_, ?_⟩ (fun _ => zero_le_one) ?_
  · intro a ha b hb α β hα hβ _ l
    have := ha l; have := hb l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro a _ b _ α β hα hβ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine le_min ?_ ?_
    · nlinarith [min_le_left (a 0) (a 1), min_le_left (b 0) (b 1)]
    · nlinarith [min_le_right (a 0) (a 1), min_le_right (b 0) (b 1)]
  · intro y _ hb
    have h1 : y 0 + y 1 ≤ 1 := by simpa [dotProduct, Fin.sum_univ_two] using hb
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, min_self]
    rcases le_or_gt (y 0) (1 / 2) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

/-- **Example 19.D.1** (MWG, p. 698): with a strictly concave, strongly monotone `u`, every
Arrow-Debreu equilibrium allocation is state independent (the aggregate endowment is the same in
both states). -/
theorem example_19_D_1_stateIndependent {u : (Fin 2 → ℝ) → ℝ}
    (hc : StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u) (hm : StronglyMonotoneL u)
    {ωbar : Fin 2 → ℝ} {x : Fin 2 → CVec 2 2} {p : CVec 2 2}
    (h : IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar) x p) :
    ∀ i, x i 0 = x i 1 := by
  have hpo := adEqmU_paretoOptimal (fun _ => expUtil_stronglyMonotone (fun _ => by norm_num)
    fun _ => hm) h
  have := po_stateIndependent (u := fun _ => u) (fun _ => by norm_num)
    (by simp) (fun _ => hc) (ω := omega19D1 ωbar)
    (fun s s' => by fin_cases s <;> fin_cases s' <;> simp [omega19D1]) hpo
  exact fun i => this i 0 1

/-- **Exercise 19.D.2** (MWG, p. 726), for Example 19.D.1. At the equilibrium of
`example_19_D_1` (with `p̂₁ > 0`), the contingent trades in good 1 of Proposition 19.D.1(i) are:
consumer 1 sells `α = p̂·ω̄ / (2 p̂₁)` units contingent on state 1 and buys `β = α` units contingent
on state 2; consumer 2 does the opposite; together with the common spot prices `p̂` they form a
Radner equilibrium. -/
theorem exercise_19_D_2 {u : (Fin 2 → ℝ) → ℝ} (hu : ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u)
    {ωbar phat : Fin 2 → ℝ} (hω : ∀ l, 0 ≤ ωbar l) (hp : 0 < phat 0)
    (hmax : ∀ y : Fin 2 → ℝ, (∀ l, 0 ≤ y l) → phat ⬝ᵥ y ≤ phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) →
      u y ≤ u ((1 / 2 : ℝ) • ωbar)) :
    let α := phat ⬝ᵥ ωbar / (2 * phat 0)
    let z : Fin 2 → Fin 2 → ℝ := fun i s =>
      (fun _ => phat) s ⬝ᵥ ((1 / 2 : ℝ) • ωbar - omega19D1 ωbar i s) / phat 0
    IsRadnerEqmD 0 (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar)
        (fun _ => phat 0) (fun _ => phat) (fun _ _ => (1 / 2 : ℝ) • ωbar) z ∧
      z 0 0 = -α ∧ z 0 1 = α ∧ z 1 0 = α ∧ z 1 1 = -α := by
  intro α z
  refine ⟨proposition_19_D_1_i 0 (fun _ => hp) (example_19_D_1 hu hω hmax), ?_⟩
  simp only [z, α, omega19D1, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> field_simp <;> ring

/-! ## Exercise 19.D.3: consumption at `t = 0` -/

variable {S L : ℕ}

/-- **Exercise 19.D.3** (MWG, p. 727). The Arrow-Debreu budget set with date-0 consumption
`x₀ ∈ ℝ^L_+` at prices `p₀`: `p₀·(x₀ - ω₀) + ∑_s p_s·(x_s - ω_s) ≤ 0`. -/
def adBudget0 (p₀ : Fin L → ℝ) (p : CVec S L) (ω₀ : Fin L → ℝ) (ω : CVec S L)
    (x₀ : Fin L → ℝ) (x : CVec S L) : Prop :=
  (∀ l, 0 ≤ x₀ l) ∧ NonnegC x ∧ p₀ ⬝ᵥ x₀ + cval p x ≤ p₀ ⬝ᵥ ω₀ + cval p ω

/-- **Exercise 19.D.3** (MWG, p. 727). The Radner budget set with a date-0 spot market:
`p₀·(x₀ - ω₀) + ∑_s q_s z_s ≤ 0` and `p_s·x_s ≤ p_s·ω_s + p_{gs} z_s`. -/
def radnerBudget0 (g : Fin L) (q : Fin S → ℝ) (p₀ : Fin L → ℝ) (p : CVec S L)
    (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ) (x : CVec S L) : Prop :=
  (∀ l, 0 ≤ x₀ l) ∧ NonnegC x ∧ ∃ z : Fin S → ℝ, p₀ ⬝ᵥ x₀ + q ⬝ᵥ z ≤ p₀ ⬝ᵥ ω₀ ∧
    ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * z s

/-- **Exercise 19.D.3** (MWG, p. 727), Proposition 19.D.1(i) remains valid: with `q_s = p_{gs} > 0`
(and the same date-0 prices) the two budget sets coincide, so Arrow-Debreu demands are Radner
demands; the contingent trades `z_s = p_s·(x_s - ω_s) / p_{gs}` clear when consumption does. -/
theorem exercise_19_D_3_i (g : Fin L) {p : CVec S L} (hp : ∀ s, 0 < p s g) (p₀ : Fin L → ℝ)
    (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ) (x : CVec S L) :
    adBudget0 p₀ p ω₀ ω x₀ x ↔ radnerBudget0 g (fun s => p s g) p₀ p ω₀ ω x₀ x := by
  have key : ∀ y : CVec S L, (fun s => p s g) ⬝ᵥ (fun s => p s ⬝ᵥ y s / p s g) = cval p y := by
    intro y
    simp only [dotProduct, cval]
    exact Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
  constructor
  · rintro ⟨h0, hx, hb⟩
    refine ⟨h0, hx, fun s => p s ⬝ᵥ (x s - ω s) / p s g, ?_, fun s => ?_⟩
    · have := key (x - ω)
      simp only [Pi.sub_apply] at this
      rw [this, cval_sub]; linarith
    · rw [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]; linarith
  · rintro ⟨h0, hx, z, hz0, hzs⟩
    refine ⟨h0, hx, ?_⟩
    have h1 : ∑ s, (p s ⬝ᵥ x s - p s ⬝ᵥ ω s) ≤ ∑ s, p s g * z s :=
      Finset.sum_le_sum fun s _ => by linarith [hzs s]
    rw [Finset.sum_sub_distrib] at h1
    simp only [dotProduct] at hz0
    unfold cval
    simp only [dotProduct] at h1 ⊢
    linarith

/-- **Exercise 19.D.3** (MWG, p. 727), Proposition 19.D.1(ii) remains valid: with `q ≥ 0`,
`p_{gs} > 0` and `μ_s = q_s / p_{gs}`, the Radner budget set equals the Arrow-Debreu budget set
at the prices `(p₀, μ₁ p₁, …, μ_S p_S)`. -/
theorem exercise_19_D_3_ii (g : Fin L) {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (p₀ : Fin L → ℝ) (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ)
    (x : CVec S L) :
    radnerBudget0 g q p₀ p ω₀ ω x₀ x ↔
      adBudget0 p₀ (fun s => (q s / p s g) • p s) ω₀ ω x₀ x := by
  constructor
  · rintro ⟨h0, hx, z, hz0, hzs⟩
    refine ⟨h0, hx, ?_⟩
    simp only [cval, smul_dotProduct, smul_eq_mul]
    have h1 : ∀ s, q s / p s g * (p s ⬝ᵥ x s) ≤ q s / p s g * (p s ⬝ᵥ ω s) + q s * z s := by
      intro s
      have := mul_le_mul_of_nonneg_left (hzs s) (div_nonneg (hq s) (hp s).le)
      rwa [mul_add, ← mul_assoc, div_mul_cancel₀ _ (hp s).ne'] at this
    have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
    rw [Finset.sum_add_distrib] at h2
    have hqz : q ⬝ᵥ z = ∑ s, q s * z s := rfl
    rw [hqz] at hz0
    linarith
  · rintro ⟨h0, hx, hb⟩
    refine ⟨h0, hx, fun s => p s ⬝ᵥ (x s - ω s) / p s g, ?_, fun s => ?_⟩
    · simp only [cval, smul_dotProduct, smul_eq_mul] at hb
      have e : q ⬝ᵥ (fun s => p s ⬝ᵥ (x s - ω s) / p s g) =
          ∑ s, q s / p s g * (p s ⬝ᵥ x s) - ∑ s, q s / p s g * (p s ⬝ᵥ ω s) := by
        simp only [dotProduct_sub]
        rw [dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [e]; linarith
    · rw [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]; linarith

/-! ## Exercise 19.D.4: three dates, a binary tree -/

variable {H : ℕ}

/-- **Exercise 19.D.4(a)** (MWG, p. 727). The Arrow-Debreu budget constraint for the tree with
`t = 0, 1, 2`, two branches at each node and `H` goods consumed at every date: date-0 prices `p₀`,
node prices `p₁ b` at `t = 1` and `p₂ b c` at `t = 2`. -/
def adBudgetTree (p₀ : Fin H → ℝ) (p₁ : Fin 2 → Fin H → ℝ) (p₂ : Fin 2 → Fin 2 → Fin H → ℝ)
    (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    Prop :=
  p₀ ⬝ᵥ (x₀ - ω₀) + ∑ b, p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ b, ∑ c, p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ 0

/-- **Exercise 19.D.4(b)** (MWG, p. 727). The Radner budget constraints: at `t = 0` spot trade
and contingent trade `z₀ b` in good `g` deliverable at node `b` (prices `q₀ b`); at node `b` spot
trade at `P₁ b` and contingent trade `z₁ b c` in good `g` deliverable at `(b, c)` (prices
`q₁ b c`), financed by the delivery `P₁ b g · z₀ b`; at `(b, c)` spot trade financed by
`P₂ b c g · z₁ b c`. -/
def radnerBudgetTree (g : Fin H) (q₀ : Fin 2 → ℝ) (q₁ : Fin 2 → Fin 2 → ℝ) (p₀ : Fin H → ℝ)
    (P₁ : Fin 2 → Fin H → ℝ) (P₂ : Fin 2 → Fin 2 → Fin H → ℝ) (ω₀ x₀ : Fin H → ℝ)
    (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) : Prop :=
  ∃ (z₀ : Fin 2 → ℝ) (z₁ : Fin 2 → Fin 2 → ℝ), p₀ ⬝ᵥ (x₀ - ω₀) + ∑ b, q₀ b * z₀ b ≤ 0 ∧
    (∀ b, P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c ≤ P₁ b g * z₀ b) ∧
    ∀ b c, P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ P₂ b c g * z₁ b c

/-- **Exercise 19.D.4(c)** (MWG, p. 727), the direction of Proposition 19.D.1(i). Given
Arrow-Debreu prices with `p₁ b g > 0` and `p₂ b c g > 0`, use them as spot prices and price the
contingent claims at `q₀ b = p₁ b g`, `q₁ b c = p₂ b c g`. Then the two budget sets coincide. -/
theorem exercise_19_D_4c_i (g : Fin H) (p₀ : Fin H → ℝ) {p₁ : Fin 2 → Fin H → ℝ}
    {p₂ : Fin 2 → Fin 2 → Fin H → ℝ} (h1 : ∀ b, 0 < p₁ b g) (h2 : ∀ b c, 0 < p₂ b c g)
    (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    adBudgetTree p₀ p₁ p₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ ↔
      radnerBudgetTree g (fun b => p₁ b g) (fun b c => p₂ b c g) p₀ p₁ p₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ := by
  constructor
  · intro h
    set z₁ : Fin 2 → Fin 2 → ℝ := fun b c => p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) / p₂ b c g with hz₁
    set z₀ : Fin 2 → ℝ := fun b =>
      (p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c g * z₁ b c) / p₁ b g with hz₀
    have e1 : ∀ b c, p₂ b c g * z₁ b c = p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) := fun b c => by
      rw [hz₁]; field_simp [(h2 b c).ne']
    have e0 : ∀ b, p₁ b g * z₀ b = p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c g * z₁ b c := fun b => by
      rw [hz₀]; field_simp [(h1 b).ne']
    refine ⟨z₀, z₁, ?_, fun b => (e0 b).ge, fun b c => (e1 b c).ge⟩
    simp only [e0, e1]
    unfold adBudgetTree at h
    rw [Finset.sum_add_distrib]
    linarith
  · rintro ⟨z₀, z₁, hr, hb, hbc⟩
    unfold adBudgetTree
    have k1 : ∀ b, p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ p₁ b g * z₀ b :=
      fun b => by
        have := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hbc b c
        linarith [hb b]
    have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => k1 b
    rw [Finset.sum_add_distrib] at this
    linarith

/-- **Exercise 19.D.4(c)** (MWG, p. 727), the direction of Proposition 19.D.1(ii). Given Radner
prices with `q₀, q₁ ≥ 0` and positive spot prices of good `g`, the multipliers
`μ₁ b = q₀ b / P₁ b g` and `μ₂ b c = μ₁ b q₁ b c / P₂ b c g` turn the Radner budget set into the
Arrow-Debreu budget set at the prices `(p₀, μ₁ b P₁ b, μ₂ b c P₂ b c)`. -/
theorem exercise_19_D_4c_ii (g : Fin H) {q₀ : Fin 2 → ℝ} {q₁ : Fin 2 → Fin 2 → ℝ}
    (hq₀ : ∀ b, 0 ≤ q₀ b) (hq₁ : ∀ b c, 0 ≤ q₁ b c) (p₀ : Fin H → ℝ)
    {P₁ : Fin 2 → Fin H → ℝ} {P₂ : Fin 2 → Fin 2 → Fin H → ℝ} (h1 : ∀ b, 0 < P₁ b g)
    (h2 : ∀ b c, 0 < P₂ b c g) (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ)
    (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    radnerBudgetTree g q₀ q₁ p₀ P₁ P₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ ↔
      adBudgetTree p₀ (fun b => (q₀ b / P₁ b g) • P₁ b)
        (fun b c => (q₀ b / P₁ b g * q₁ b c / P₂ b c g) • P₂ b c) ω₀ x₀ ω₁ x₁ ω₂ x₂ := by
  have hμ1 : ∀ b, 0 ≤ q₀ b / P₁ b g := fun b => div_nonneg (hq₀ b) (h1 b).le
  constructor
  · rintro ⟨z₀, z₁, hr, hb, hbc⟩
    unfold adBudgetTree
    simp only [smul_dotProduct, smul_eq_mul]
    have k2 : ∀ b c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) ≤
        q₀ b / P₁ b g * (q₁ b c * z₁ b c) := by
      intro b c
      have := mul_le_mul_of_nonneg_left (hbc b c)
        (div_nonneg (mul_nonneg (hμ1 b) (hq₁ b c)) (h2 b c).le)
      calc q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c))
          ≤ q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c g * z₁ b c) := this
        _ = q₀ b / P₁ b g * (q₁ b c * z₁ b c) := by field_simp [(h2 b c).ne']
    have k1 : ∀ b, q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b)) +
        ∑ c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) ≤ q₀ b * z₀ b := by
      intro b
      have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => k2 b c
      rw [← Finset.mul_sum] at hs
      have := mul_le_mul_of_nonneg_left (hb b) (hμ1 b)
      rw [mul_add] at this
      have e : q₀ b / P₁ b g * (P₁ b g * z₀ b) = q₀ b * z₀ b := by field_simp [(h1 b).ne']
      linarith
    have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => k1 b
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro h
    unfold adBudgetTree at h
    simp only [smul_dotProduct, smul_eq_mul] at h
    set z₁ : Fin 2 → Fin 2 → ℝ := fun b c => P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) / P₂ b c g with hz₁
    set z₀ : Fin 2 → ℝ := fun b =>
      (P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c) / P₁ b g with hz₀
    have e1 : ∀ b c, P₂ b c g * z₁ b c = P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) := fun b c => by
      rw [hz₁]; field_simp [(h2 b c).ne']
    have e0 : ∀ b, P₁ b g * z₀ b = P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c := fun b => by
      rw [hz₀]; field_simp [(h1 b).ne']
    refine ⟨z₀, z₁, ?_, fun b => (e0 b).ge, fun b c => (e1 b c).ge⟩
    have e2 : ∀ b, q₀ b * z₀ b = q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b)) +
        ∑ c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) := by
      intro b
      have : q₀ b * z₀ b = q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c) := by
        rw [hz₀]; field_simp
      rw [this, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [hz₁]; ring
    simp only [e2, Finset.sum_add_distrib]
    linarith

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Asset markets and arbitrage (MWG Section 19.E, pp. 699-704)

* **Definition 19.E.1**: an asset is a return vector `r ∈ ℝ^S`; an asset structure is an `S × K`
  return matrix `R` whose `k`-th column is `r_k` (`returnMatrix`).
* **Example 19.E.1**: the riskless asset, Arrow securities (whose return matrix is the identity,
  as in Example 19.E.4) and the asset paying `1` and an extra unit in even-labelled states.
* **Example 19.E.2**: call options `r(c)_s = max{0, r_s - c}` and the three printed return vectors.
* **Definition 19.E.2** (in `Sequential`), with the normalization `p_{gs} = 1` the budget set
  `B_i(p, q, R)` of p. 701 (`budgetSet_normalized`).
* **Proposition 19.E.1, Proof 1**: arbitrage-free prices (`ArbitrageFree`), their positivity
  (p. 702), **Lemma 19.E.1** by the separating hyperplane theorem (M.G.2, from Chapter 3) applied
  as in the book to `V = {Rz : q·z = 0}` and `ℝ^S_+ \ {0}`, restricted to the states with a nonzero
  row of `R` (footnote 17); equilibrium prices are arbitrage free when some consumer has strongly
  monotone preferences (`radner_arbitrageFree`, `proposition_19_E_1`).
* **Example 19.E.3**: with a riskless asset of price 1, `min_s r_{sk} ≤ q_k ≤ max_s r_{sk}`.
* **Definition 19.E.3** (`IsComplete`: `rank R = S`), **Example 19.E.4** (the identity and a
  triangular `3 × 3` matrix), **Example 19.E.5** (spanning through options on `r = (4, 3, 2, 1)`;
  if `r_s = r_{s'}` no option structure on `r` is complete), and **Exercise 19.E.2** (a primary
  asset with distinct positive returns generates a complete structure by options).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- **Definition 19.E.1** (MWG, p. 699). A unit of an asset is a title to `r_s` units of good `g`
(the numeraire) at `t = 1` if state `s` occurs; the asset is its return vector `r ∈ ℝ^S`. -/
abbrev ReturnVector (S : ℕ) := Fin S → ℝ

/-- **p. 701**. The `S × K` return matrix whose `k`-th column is the return vector `r_k`. -/
def returnMatrix (r : Fin K → ReturnVector S) : Matrix (Fin S) (Fin K) ℝ :=
  Matrix.of fun s k => r k s

/-- **Example 19.E.1(ii)** (MWG, p. 700). The Arrow security for state `s`: one unit of good `g` if
and only if `s` occurs. -/
def arrowSecurity (s : Fin S) : ReturnVector S := Pi.single s 1

/-- **Examples 19.E.1(ii) and 19.E.4** (MWG, pp. 700, 704). The return matrix of the `S` Arrow
securities is the `S × S` identity matrix; it has rank `S` (the canonical complete structure). -/
theorem example_19_E_1_arrow : returnMatrix (arrowSecurity (S := S)) = 1 := by
  ext s k
  simp only [returnMatrix, arrowSecurity, Matrix.of_apply, Matrix.one_apply, Pi.single_apply]

/-- **Example 19.E.1** (MWG, p. 700). (i) The riskless asset `(1, …, 1)`; (iii) the asset paying one
unit unconditionally and another unit in even-labelled states (states are counted from `0`, so the
book's even labels `2, 4, …` are the odd indices). -/
def example19E1iii : ReturnVector S := fun s => if s.val % 2 = 1 then 2 else 1

/-- **Example 19.E.1(iii)** (MWG, p. 700): it is the riskless asset plus the sum of the Arrow
securities of the even-labelled states. -/
theorem example_19_E_1_iii (s : Fin S) :
    example19E1iii s = 1 + ∑ t ∈ Finset.univ.filter (fun t : Fin S => t.val % 2 = 1),
      arrowSecurity t s := by
  have hsum : ∑ t ∈ Finset.univ.filter (fun t : Fin S => t.val % 2 = 1), arrowSecurity t s =
      if s.val % 2 = 1 then 1 else 0 := by
    rw [Finset.sum_filter, Finset.sum_eq_single s]
    · simp [arrowSecurity]
    · intro b _ hb; simp [arrowSecurity, Ne.symm hb]
    · simp
  rw [hsum]; unfold example19E1iii; split_ifs <;> norm_num

/-- **Example 19.E.2** (MWG, p. 700). The European call option with strike price `c` on the primary
asset `r`: `r(c)_s = max{0, r_s - c}`. -/
def callOption (r : ReturnVector S) (c : ℝ) : ReturnVector S := fun s => max 0 (r s - c)

/-- The primary asset `r = (4, 3, 2, 1)` of Examples 19.E.2 and 19.E.5. -/
def primary4321 : ReturnVector 4 := ![4, 3, 2, 1]

/-- **Example 19.E.2** (MWG, p. 700). For `r = (4, 3, 2, 1)`: `r(3.5) = (.5, 0, 0, 0)`,
`r(2.5) = (1.5, .5, 0, 0)` and `r(1.5) = (2.5, 1.5, .5, 0)`. -/
theorem example_19_E_2 :
    callOption primary4321 3.5 = ![0.5, 0, 0, 0] ∧ callOption primary4321 2.5 = ![1.5, 0.5, 0, 0] ∧
      callOption primary4321 1.5 = ![2.5, 1.5, 0.5, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext s <;> fin_cases s <;>
    simp [callOption, primary4321] <;> norm_num

/-- **p. 701**. With the normalization `p_{gs} = 1`, the budget set of Definition 19.E.2 is
`B_i(p, q, R) = {x ≥ 0 : ∃ z, q·z ≤ 0 and (p_s·(x_s - ω_s))_s ≤ R z}`. -/
theorem budgetSet_normalized (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    {p : CVec S L} (hp : ∀ s, p s g = 1) (ω x : CVec S L) (z : Fin K → ℝ) :
    radnerFeasible g R q p ω x z ↔
      NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ (x s - ω s) ≤ (R *ᵥ z) s := by
  unfold radnerFeasible
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun s => ?_))
  rw [hp s, one_mul, dotProduct_sub]
  constructor <;> intro h <;> linarith

/-! ## Arbitrage and Lemma 19.E.1 -/

/-- **Proof 1 of Proposition 19.E.1** (MWG, p. 702). Asset prices `q` are arbitrage free if no
portfolio `z` has `q·z ≤ 0`, `Rz ≥ 0` and `Rz ≠ 0`. -/
def ArbitrageFree (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) : Prop :=
  ¬ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ 0 ∧ (∀ s, 0 ≤ (R *ᵥ z) s) ∧ R *ᵥ z ≠ 0

/-- The standing assumption of Proposition 19.E.1: every return vector is nonnegative and
nonzero. -/
def NonnegNonzeroReturns (R : Matrix (Fin S) (Fin K) ℝ) : Prop :=
  (∀ s k, 0 ≤ R s k) ∧ ∀ k, ∃ s, R s k ≠ 0

theorem mulVec_single (R : Matrix (Fin S) (Fin K) ℝ) (k : Fin K) (s : Fin S) :
    (R *ᵥ Pi.single k 1) s = R s k := by
  simp [mulVec, dotProduct, Pi.single_apply]

/-- **Proof of Lemma 19.E.1** (MWG, p. 702). With nonnegative nonzero returns, an arbitrage-free
price vector is strictly positive. -/
theorem ArbitrageFree.pos {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q : Fin K → ℝ} (h : ArbitrageFree R q) (k : Fin K) : 0 < q k := by
  by_contra hle
  push Not at hle
  refine h ⟨Pi.single k 1, by simpa [dotProduct_single] using hle, fun s => ?_, fun h0 => ?_⟩
  · rw [mulVec_single]; exact hR.1 s k
  · obtain ⟨s, hs⟩ := hR.2 k
    have := congrFun h0 s
    rw [mulVec_single] at this
    exact hs this

/-- If `q ≠ 0` and `a·d = 0` whenever `q·d = 0`, then `a` is a multiple of `q`. -/
theorem eq_smul_of_ker_le {n : Type*} [Fintype n] {a q : n → ℝ} (hq : q ≠ 0)
    (h : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0) : a = ((a ⬝ᵥ q) / (q ⬝ᵥ q)) • q := by
  classical
  have hqq : q ⬝ᵥ q ≠ 0 := fun h0 => hq (dotProduct_self_eq_zero.mp h0)
  have hd : ∀ d, a ⬝ᵥ d = (a ⬝ᵥ q) / (q ⬝ᵥ q) * (q ⬝ᵥ d) := by
    intro d
    have h0 := h (d - ((q ⬝ᵥ d) / (q ⬝ᵥ q)) • q) (by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hqq, sub_self])
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h0
    rw [h0, dotProduct_comm a q]
    field_simp
  funext k
  have := hd (Pi.single k 1)
  simpa [dotProduct_single] using this

/-- The separating hyperplane theorem (Theorem M.G.2(ii), Chapter 3) for vectors indexed by a
nonempty finite type. -/
theorem separation_fintype {T : Type*} [Fintype T] [Nonempty T] {A B : Set (T → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) :
    ∃ p : T → ℝ, p ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ p ⬝ᵥ x) ∧ ∀ y ∈ B, p ⬝ᵥ y ≤ c := by
  set e := Fintype.equivFin T
  have hN : 0 < Fintype.card T := Fintype.card_pos
  let φ : (T → ℝ) → (Fin (Fintype.card T) → ℝ) := fun v j => v (e.symm j)
  have hφlin : ∀ (a b : ℝ) (v w : T → ℝ), φ (a • v + b • w) = a • φ v + b • φ w :=
    fun _ _ _ _ => rfl
  have hφinj : Function.Injective φ := fun v w h => funext fun t => by
    have := congrFun h (e t); simpa [φ] using this
  have hconv : ∀ C : Set (T → ℝ), Convex ℝ C → Convex ℝ (φ '' C) := by
    rintro C hC _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
    exact ⟨a • v + b • w, hC hv hw ha hb hab, hφlin a b v w⟩
  obtain ⟨p, hp, c, hcA, hcB⟩ := MWG.ClassicalDemand.theorem_M_G_2_ii hN (hconv A hA)
    (hconv B hB) (hAne.image φ) (hBne.image φ) (by
      rw [Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
      exact Set.disjoint_left.mp hdisj hv (hφinj hvw ▸ hw))
  have hdot : ∀ v : T → ℝ, p ⬝ᵥ φ v = (fun t => p (e t)) ⬝ᵥ v := by
    intro v
    simp only [dotProduct, φ]
    exact (e.sum_comp fun j => p j * v (e.symm j)).symm.trans
      (Finset.sum_congr rfl fun t _ => by simp)
  refine ⟨fun t => p (e t), fun h0 => hp (funext fun j => ?_), c, fun x hx => ?_,
    fun y hy => ?_⟩
  · have := congrFun h0 (e.symm j); simpa using this
  · rw [← hdot]; exact hcA _ ⟨x, hx, rfl⟩
  · rw [← hdot]; exact hcB _ ⟨y, hy, rfl⟩

/-- **Lemma 19.E.1** (MWG, p. 702), with the standing assumption of Proposition 19.E.1 (returns
nonnegative and nonzero). If `q` is arbitrage free, there are multipliers `μ ≥ 0` with
`q_k = ∑_s μ_s r_{sk}` (`qᵀ = μ·R`). The proof is the book's: separate `V = {Rz : q·z = 0}` from
`ℝ^S_+ \ {0}`, on the states whose row of `R` is nonzero (footnote 17); the normal `μ'` is
nonnegative, vanishes on `V`, and `q` is proportional to `μ'·R`. -/
theorem lemma_19_E_1 {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q : Fin K → ℝ} (h : ArbitrageFree R q) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 ≤ μ s) ∧ ∀ k, q k = ∑ s, μ s * R s k := by
  classical
  rcases isEmpty_or_nonempty (Fin K) with hK | ⟨⟨k₀⟩⟩
  · exact ⟨0, fun _ => le_rfl, fun k => isEmptyElim k⟩
  have hqpos := h.pos hR
  -- the states with a nonzero row
  set T := {s : Fin S // ∃ k, R s k ≠ 0} with hT
  obtain ⟨s₀, hs₀⟩ := hR.2 k₀
  have hTne : Nonempty T := ⟨⟨s₀, k₀, hs₀⟩⟩
  have hzero : ∀ s, (¬ ∃ k, R s k ≠ 0) → ∀ z : Fin K → ℝ, (R *ᵥ z) s = 0 := by
    intro s hs z
    push Not at hs
    simp [mulVec, dotProduct, hs]
  set V : Set (T → ℝ) := {v | ∃ z, q ⬝ᵥ z = 0 ∧ ∀ t : T, v t = (R *ᵥ z) t.1} with hV
  set P : Set (T → ℝ) := {y | (∀ t, 0 ≤ y t) ∧ y ≠ 0} with hP
  have hVconv : Convex ℝ V := by
    intro v hv w hw a b _ _ _
    obtain ⟨z, hz, hvz⟩ := hv
    obtain ⟨z', hz', hwz⟩ := hw
    refine ⟨a • z + b • z', ?_, fun t => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hz, hz']; simp
    · simp [hvz, hwz, mulVec_add, mulVec_smul]
  have hPconv : Convex ℝ P := by
    intro y hy w hw a b ha hb hab
    obtain ⟨hy, hy0⟩ := hy
    obtain ⟨hw, hw0⟩ := hw
    refine ⟨fun t => ?_, fun h0 => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hy t)) (mul_nonneg hb (hw t))
    · rcases ha.lt_or_eq with ha' | ha'
      · apply hy0
        funext t
        have h1 := congrFun h0 t
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        have := mul_nonneg hb (hw t)
        have h2 : a * y t = 0 := by linarith [mul_nonneg ha (hy t)]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ha'.ne'
        · simpa using h3
      · subst ha'
        have hb1 : b = 1 := by linarith
        subst hb1
        apply hw0; simpa using h0
  have hdisj : Disjoint P V := by
    rw [Set.disjoint_left]
    rintro y ⟨hy, hy0⟩ ⟨z, hz, hzy⟩
    refine h ⟨z, hz.le, fun s => ?_, fun h0 => hy0 (funext fun t => by
      rw [hzy t, h0]; rfl)⟩
    by_cases hs : ∃ k, R s k ≠ 0
    · have := hy ⟨s, hs⟩; rwa [hzy] at this
    · rw [hzero s hs]
  obtain ⟨μ', hμ'0, c, hcP, hcV⟩ := separation_fintype hPconv hVconv
    ⟨fun _ => 1, fun _ => zero_le_one, fun h0 => by
      have := congrFun h0 (Classical.arbitrary T); simp at this⟩
    ⟨0, 0, by simp, fun t => by simp⟩ hdisj
  -- `c ≥ 0` since `0 ∈ V`, and `μ'` vanishes on `V`
  have hc0 : 0 ≤ c := by simpa using hcV 0 ⟨0, by simp, fun t => by simp⟩
  have hVzero : ∀ z, q ⬝ᵥ z = 0 → μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) = 0 := by
    intro z hz
    have hmem : ∀ a : ℝ, (fun t : T => (R *ᵥ (a • z)) t.1) ∈ V :=
      fun a => ⟨a • z, by rw [dotProduct_smul, hz, smul_zero], fun t => rfl⟩
    have hlin : ∀ a : ℝ, μ' ⬝ᵥ (fun t : T => (R *ᵥ (a • z)) t.1) =
        a * μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) := fun a => by
      simp [mulVec_smul, dotProduct, Finset.mul_sum, mul_left_comm]
    by_contra hne
    have h1 := hcV _ (hmem ((c + 1) / μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1)))
    rw [hlin, div_mul_cancel₀ _ hne] at h1
    linarith
  -- `μ' ≥ 0`
  have hμ'nn : ∀ t, 0 ≤ μ' t := by
    intro t
    by_contra hneg
    push Not at hneg
    have := hcP (Pi.single t 1) ⟨fun t' => by simp [Pi.single_apply]; split_ifs <;> norm_num,
      fun h0 => by have := congrFun h0 t; simp at this⟩
    simp [dotProduct_single] at this
    linarith
  -- `a = μ'·R`
  set μ'' : Fin S → ℝ := fun s => if hs : ∃ k, R s k ≠ 0 then μ' ⟨s, hs⟩ else 0 with hμ''
  have hμ''nn : ∀ s, 0 ≤ μ'' s := fun s => by
    simp only [hμ'']; split_ifs <;> simp [hμ'nn]
  set a : Fin K → ℝ := fun k => ∑ s, μ'' s * R s k with ha
  have hadot : ∀ z, a ⬝ᵥ z = μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) := by
    intro z
    have e1 : a ⬝ᵥ z = ∑ s, μ'' s * (R *ᵥ z) s := by
      simp only [ha, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, ← Fintype.sum_subtype_add_sum_subtype (fun s => ∃ k, R s k ≠ 0)]
    have h2 : ∑ s : {s // ¬ ∃ k, R s k ≠ 0}, μ'' s.1 * (R *ᵥ z) s.1 = 0 :=
      Finset.sum_eq_zero fun s _ => by simp [hμ'', s.2]
    rw [h2, add_zero]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun t _ => by simp [hμ'', t.2]
  have hker : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0 := fun d hd => by rw [hadot]; exact hVzero d hd
  have hq0 : q ≠ 0 := fun h0 => by have := hqpos k₀; rw [h0] at this; simp at this
  have hprop := eq_smul_of_ker_le hq0 hker
  set β := (a ⬝ᵥ q) / (q ⬝ᵥ q) with hβ
  -- `a ≠ 0`, so `β > 0`
  obtain ⟨t₁, ht₁⟩ : ∃ t, 0 < μ' t := by
    by_contra hall
    push Not at hall
    exact hμ'0 (funext fun t => le_antisymm (hall t) (hμ'nn t))
  obtain ⟨k₁, hk₁⟩ := t₁.2
  have hak : 0 < a k₁ := by
    have hpos : 0 < μ'' t₁.1 * R t₁.1 k₁ := by
      have hR1 : 0 < R t₁.1 k₁ := lt_of_le_of_ne (hR.1 _ _) (Ne.symm hk₁)
      have e : μ'' t₁.1 = μ' t₁ := by simp [hμ'', t₁.2]
      rw [e]
      exact mul_pos ht₁ hR1
    calc 0 < μ'' t₁.1 * R t₁.1 k₁ := hpos
      _ ≤ ∑ s, μ'' s * R s k₁ := Finset.single_le_sum (f := fun s => μ'' s * R s k₁)
          (fun s _ => mul_nonneg (hμ''nn s) (hR.1 s k₁)) (Finset.mem_univ _)
  have hβpos : 0 < β := by
    have := congrFun hprop k₁
    simp only [Pi.smul_apply, smul_eq_mul] at this
    by_contra hb
    push Not at hb
    have : a k₁ ≤ 0 := by rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hb (hqpos k₁).le
    linarith
  refine ⟨fun s => μ'' s / β, fun s => div_nonneg (hμ''nn s) hβpos.le, fun k => ?_⟩
  have := congrFun hprop k
  simp only [Pi.smul_apply, smul_eq_mul, ha] at this
  have e : ∑ s, μ'' s / β * R s k = (∑ s, μ'' s * R s k) / β := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, this]; field_simp

/-! ## Proposition 19.E.1 -/

/-- **Proof 1 of Proposition 19.E.1** (MWG, p. 702). If some consumer's preferences are strongly
monotone, equilibrium asset prices are arbitrage free: adding an arbitrage portfolio to his
portfolio and consuming the extra returns in good `g` would be affordable and strictly better. -/
theorem radner_arbitrageFree {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ} {p : CVec S L}
    {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) : ArbitrageFree R q := by
  classical
  rintro ⟨w, hqw, hnn, hne⟩
  set δ : CVec S L := fun s l => if l = g then (R *ᵥ w) s else 0 with hδ
  have hδdot : ∀ s, p s ⬝ᵥ δ s = p s g * (R *ᵥ w) s := fun s => by
    simp [hδ, dotProduct]
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  have hle : x i ≤ x i + δ := fun s l => by
    simp only [Pi.add_apply, hδ]; split_ifs <;> linarith [hnn s]
  have hne' : x i ≠ x i + δ := by
    intro h0
    apply hne
    funext s
    have := congrFun (congrFun h0 s) g
    simp [hδ] at this
    simpa using this
  have hfeas : radnerFeasible g R q p (ω i) (x i + δ) (z i + w) := by
    refine ⟨fun s l => (hx s l).trans (hle s l), ?_, fun s => ?_⟩
    · rw [dotProduct_add]; linarith
    · rw [Pi.add_apply, dotProduct_add, hδdot, mulVec_add, Pi.add_apply, mul_add]
      linarith [hsp s]
  linarith [hopt _ _ hfeas, hU _ _ hx hle hne']

/-- **Proposition 19.E.1** (MWG, p. 701). Suppose every return vector is nonnegative and nonzero,
and some consumer's preferences are strongly monotone. Then for the asset prices `q` of any Radner
equilibrium there are multipliers `μ ≥ 0` with `q_k = ∑_s μ_s r_{sk}` for every asset (Proof 1:
`radner_arbitrageFree` and `lemma_19_E_1`). -/
theorem proposition_19_E_1 {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hR : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 ≤ μ s) ∧ ∀ k, q k = ∑ s, μ s * R s k :=
  lemma_19_E_1 hR (radner_arbitrageFree g h i hU)

/-- **Example 19.E.3** (MWG, p. 704). If asset `k₁` is riskless (`r_{k₁} = (1, …, 1)`) with price
`1`, the multipliers of Proposition 19.E.1 sum to one, and every asset price lies between the
smallest and the largest return of the asset: `min_s r_{sk} ≤ q_k ≤ max_s r_{sk}`. -/
theorem example_19_E_3 {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ} {μ : Fin S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hq : ∀ k, q k = ∑ s, μ s * R s k) {k₁ : Fin K} (hsafe : ∀ s, R s k₁ = 1)
    (hq1 : q k₁ = 1) (k : Fin K) :
    ∑ s, μ s = 1 ∧ (∀ m, (∀ s, m ≤ R s k) → m ≤ q k) ∧ ∀ M, (∀ s, R s k ≤ M) → q k ≤ M := by
  have hsum : ∑ s, μ s = 1 := by
    have := hq k₁; simp only [hsafe, mul_one] at this; linarith
  refine ⟨hsum, fun m hm => ?_, fun M hM => ?_⟩
  · rw [hq k]
    calc m = ∑ s, μ s * m := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ s, μ s * R s k := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hm s) (hμ s)
  · rw [hq k]
    calc ∑ s, μ s * R s k ≤ ∑ s, μ s * M :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hM s) (hμ s)
      _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-! ## Complete asset structures -/

/-- **Definition 19.E.3** (MWG, p. 704). An asset structure with return matrix `R` is complete if
`rank R = S`. -/
def IsComplete (R : Matrix (Fin S) (Fin K) ℝ) : Prop := R.rank = S

/-- **p. 704**. An asset structure is complete iff every wealth transfer `v ∈ ℝ^S` across states is
spanned: `v = Rz` for some portfolio `z`. -/
theorem isComplete_iff_surjective (R : Matrix (Fin S) (Fin K) ℝ) :
    IsComplete R ↔ ∀ v : Fin S → ℝ, ∃ z, R *ᵥ z = v := by
  unfold IsComplete Matrix.rank
  have hS : Module.finrank ℝ (Fin S → ℝ) = S := Module.finrank_fin_fun ℝ
  constructor
  · intro h v
    have htop : LinearMap.range R.mulVecLin = ⊤ :=
      Submodule.eq_top_iff_finrank_eq.mpr (by rw [h, hS])
    obtain ⟨z, hz⟩ := LinearMap.range_eq_top.mp htop v
    exact ⟨z, by simpa [Matrix.mulVecLin_apply] using hz⟩
  · intro h
    have htop : LinearMap.range R.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr fun v => by
      obtain ⟨z, hz⟩ := h v; exact ⟨z, by simpa [Matrix.mulVecLin_apply] using hz⟩
    rw [htop, finrank_top, hS]

/-- **Example 19.E.4** (MWG, p. 704). The `S × S` identity (the Arrow securities) is complete. -/
theorem example_19_E_4_identity : IsComplete (1 : Matrix (Fin S) (Fin S) ℝ) := by
  unfold IsComplete
  rw [Matrix.rank_one, Fintype.card_fin]

/-- **Example 19.E.4** (MWG, p. 704). The return matrix with rows `(1, 0, 0)`, `(1, 1, 0)`,
`(1, 1, 1)` has rank `3`, the number of states. -/
theorem example_19_E_4 : IsComplete !![(1 : ℝ), 0, 0; 1, 1, 0; 1, 1, 1] := by
  unfold IsComplete
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
  rw [Matrix.det_fin_three]
  simp

/-- **Example 19.E.5** (MWG, p. 704). The primary asset `r = (4, 3, 2, 1)` with the options of
strike prices `3.5`, `2.5`, `1.5`: the return matrix (columns `r(3.5), r(2.5), r(1.5), r`). -/
def optionStructure19E5 : Matrix (Fin 4) (Fin 4) ℝ :=
  returnMatrix ![callOption primary4321 3.5, callOption primary4321 2.5,
    callOption primary4321 1.5, primary4321]

/-- **Example 19.E.5** (MWG, p. 704). All entries of the return matrix below the diagonal are
zero, and the structure is complete. -/
theorem example_19_E_5 :
    optionStructure19E5.IsUpperTriangular ∧ IsComplete optionStructure19E5 := by
  have hM : optionStructure19E5 =
      !![0.5, 1.5, 2.5, 4; 0, 0.5, 1.5, 3; 0, 0, 0.5, 2; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [optionStructure19E5, returnMatrix, callOption, primary4321] <;> norm_num
  have hut : optionStructure19E5.IsUpperTriangular := by
    rw [hM]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨hut, ?_⟩
  unfold IsComplete
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
  rw [Matrix.det_of_isUpperTriangular hut, hM]
  simp [Fin.prod_univ_four]
  norm_num

/-- **Example 19.E.5** (MWG, p. 704). If two distinct states `s ≠ s'` are not distinguished by any
asset (`r_{sk} = r_{s'k}` for every column), the asset structure is not complete. -/
theorem not_complete_of_eq_rows {R : Matrix (Fin S) (Fin K) ℝ} {s s' : Fin S} (hss : s ≠ s')
    (h : ∀ k, R s k = R s' k) : ¬ IsComplete R := by
  classical
  rw [isComplete_iff_surjective]
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj (Pi.single s 1)
  have h1 := congrFun hz s
  have h2 := congrFun hz s'
  simp only [mulVec, dotProduct, h] at h1 h2
  rw [h1] at h2
  simp [hss.symm] at h2

/-- **Example 19.E.5** (MWG, p. 704). If the primary asset has `r_s = r_{s'}` for some `s ≠ s'`, no
asset structure made of `r` and options on `r` is complete. -/
theorem example_19_E_5_not_separating {r : ReturnVector S} {s s' : Fin S} (hss : s ≠ s')
    (hr : r s = r s') {c : Fin K → ℝ} :
    ¬ IsComplete (returnMatrix (Fin.cons r fun k => callOption r (c k))) :=
  not_complete_of_eq_rows hss fun k => by
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [returnMatrix, hr]
    · simp [returnMatrix, callOption, hr]

/-- Piecewise-linear interpolation by options: on a finite set `A` of positive reals, every
function is a combination of the identity and the call payoffs `max{0, · - c}`, `c ∈ A`. -/
theorem interpolate_by_options (A : Finset ℝ) (hA : ∀ x ∈ A, 0 < x) (f : ℝ → ℝ) :
    ∃ (a₀ : ℝ) (a : ℝ → ℝ), ∀ x ∈ A, f x = a₀ * x + ∑ c ∈ A, a c * max 0 (x - c) := by
  classical
  induction A using Finset.induction_on_max generalizing f with
  | empty => exact ⟨0, 0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert M A hlt ih =>
    have hM : 0 < M := hA M (Finset.mem_insert_self _ _)
    have hMA : M ∉ A := fun h => lt_irrefl M (hlt M h)
    obtain ⟨a₀, a, ha⟩ := ih (fun x hx => hA x (Finset.mem_insert_of_mem hx)) f
    rcases A.eq_empty_or_nonempty with hAe | hne
    · subst hAe
      refine ⟨f M / M, 0, fun x hx => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx
      subst hx
      simp; field_simp
    · set c := A.max' hne with hc
      have hcA : c ∈ A := A.max'_mem hne
      have hcM : c < M := hlt c hcA
      set gM := a₀ * M + ∑ d ∈ A, a d * max 0 (M - d) with hgM
      set δ := (f M - gM) / (M - c) with hδ
      have key : ∀ y, ∑ d ∈ A, Function.update a c (a c + δ) d * max 0 (y - d) =
          ∑ d ∈ A, a d * max 0 (y - d) + δ * max 0 (y - c) := by
        intro y
        rw [← Finset.add_sum_erase _ _ hcA, ← Finset.add_sum_erase _ _ hcA,
          Function.update_self]
        rw [Finset.sum_congr rfl fun d hd => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]]
        ring
      refine ⟨a₀, Function.update a c (a c + δ), fun x hx => ?_⟩
      rw [Finset.sum_insert hMA, key]
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · have hmax : max 0 (x - c) = x - c := max_eq_right (by linarith)
        simp only [sub_self, max_self, mul_zero, zero_add, hmax]
        rw [hδ]
        field_simp [(sub_pos.mpr hcM).ne']
        rw [hgM]; ring
      · have hxc : x ≤ c := A.le_max' x hxA
        have hxM : x < M := hlt x hxA
        have h1 : max 0 (x - M) = 0 := max_eq_left (by linarith)
        have h2 : max 0 (x - c) = 0 := max_eq_left (by linarith)
        rw [h1, h2, ha x hxA]
        ring

/-- **Exercise 19.E.2** (MWG, p. 727). If the primary asset `r` separates states (`r_s ≠ r_{s'}`
for `s ≠ s'`) and `r_s > 0`, the structure made of `r` and the call options on `r` with strike
prices `r_1, …, r_S` is complete. -/
theorem exercise_19_E_2 {r : ReturnVector S} (hsep : Function.Injective r) (hpos : ∀ s, 0 < r s) :
    IsComplete (returnMatrix (Fin.cons r fun t => callOption r (r t))) := by
  classical
  rw [isComplete_iff_surjective]
  intro v
  rcases isEmpty_or_nonempty (Fin S) with hS | hS
  · exact ⟨0, funext fun s => isEmptyElim s⟩
  obtain ⟨a₀, a, ha⟩ := interpolate_by_options (Finset.univ.image r)
    (fun x hx => by obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx; exact hpos s)
    (fun y => v (Function.invFun r y))
  refine ⟨Fin.cons a₀ fun t => a (r t), funext fun s => ?_⟩
  have := ha (r s) (Finset.mem_image_of_mem _ (Finset.mem_univ s))
  rw [Function.leftInverse_invFun hsep s, Finset.sum_image fun x _ y _ h => hsep h] at this
  rw [this]
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, returnMatrix, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ, callOption]
  rw [Finset.sum_congr rfl fun t _ => mul_comm (max 0 (r s - r t)) (a (r t))]
  ring

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Proof 2 of Proposition 19.E.1 and Exercise 19.E.1 (MWG pp. 703, 727)

* `foc_halfspace`: if `y` maximizes `F` near `y` on the half-space `{q·y' ≤ c}` and `F` has
  directional derivatives `a·d`, then `a = α q` with `α ≥ 0`.
* **Proof 2 of Proposition 19.E.1** for the reduced portfolio problem of footnote 18,
  `max ∑_s π_s v_s(p_s·ω_s + ∑_k r_{sk} z_k)` s.t. `q·z ≤ 0`, with `v_s` differentiable at the
  optimal wealth with positive derivative: `α q_k = ∑_s π_s v_s'(w*_s) r_{sk}` with `α > 0`, so
  `μ_s = π_s v_s'(w*_s) / α` (`proposition_19_E_1_proof2`). The book assumes the indirect
  utilities `v_s(p_s, ·)` differentiable; this is a hypothesis here (correction 4 records it).
* For one good (`L = 1`, `v_s = u_s`) the Radner problem reduces to footnote 18's
  (`proposition_19_E_1_proof2_radner`), with no differentiability assumption beyond `u_s`.
* **Exercise 19.E.1(a)-(b)**: consumption also at `t = 0` (utility `u₀(x₀) + ∑_s π_s v_s`): the
  conclusion holds, and with one good `μ_s = π_s u₁'(x_{1s}) / u₀'(x₀)`.
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology Matrix

variable {S L K : ℕ}

/-- **Lagrange condition on a half-space.** If `y` maximizes `F` on `N ∩ {q·y' ≤ c}` for a
neighborhood `N` of `y`, and the derivative of `F` at `y` in every direction `d` is `a·d`, then
`a = α q` for some `α ≥ 0`. -/
theorem foc_halfspace {n : Type*} [Fintype n] {F : (n → ℝ) → ℝ} {y q a : n → ℝ} {c : ℝ}
    {N : Set (n → ℝ)} (hN : N ∈ 𝓝 y) (hmax : ∀ y' ∈ N, q ⬝ᵥ y' ≤ c → F y' ≤ F y)
    (hy : q ⬝ᵥ y ≤ c) (hder : ∀ d, HasDerivAt (fun t : ℝ => F (y + t • d)) (a ⬝ᵥ d) 0) :
    ∃ α : ℝ, 0 ≤ α ∧ a = α • q := by
  refine exists_nonneg_smul_of_dot_nonpos fun d hd => hasDerivAt_nonpos_of_eventually_le
    (hder d) ?_
  have hc : Tendsto (fun t : ℝ => y + t • d) (𝓝 0) (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).add ((tendsto_id (x := 𝓝 (0 : ℝ))).smul_const d)
    simpa using this
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • d ∈ N :=
    (hc.eventually (Filter.eventually_of_mem hN fun _ h => h)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_smul, add_zero]
  refine hmax _ ht ?_
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have : t * (q ⬝ᵥ d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt htpos) hd
  linarith

/-- The reduced portfolio objective of footnote 18: `∑_s π_s v_s(w₀_s + (Rz)_s)`. -/
def portfolioObjective (π : Fin S → ℝ) (v : Fin S → ℝ → ℝ) (w₀ : Fin S → ℝ)
    (R : Matrix (Fin S) (Fin K) ℝ) (z : Fin K → ℝ) : ℝ :=
  ∑ s, π s * v s (w₀ s + (R *ᵥ z) s)

/-- The directional derivative of the portfolio objective. -/
theorem hasDerivAt_portfolioObjective {π : Fin S → ℝ} {v : Fin S → ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {z : Fin K → ℝ} {dv : Fin S → ℝ}
    (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s)) (d : Fin K → ℝ) :
    HasDerivAt (fun t : ℝ => portfolioObjective π v w₀ R (z + t • d))
      ((fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ d) 0 := by
  have hval : (fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ d = ∑ s, π s * (dv s * (R *ᵥ d) s) := by
    simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hval]
  have hfun : (fun t : ℝ => portfolioObjective π v w₀ R (z + t • d)) =
      fun t => ∑ s, π s * v s (w₀ s + (R *ᵥ z) s + t * (R *ᵥ d) s) := by
    funext t
    simp only [portfolioObjective, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_assoc]
  rw [hfun]
  refine HasDerivAt.fun_sum fun s _ => HasDerivAt.const_mul _ ?_
  have hin : HasDerivAt (fun t : ℝ => w₀ s + (R *ᵥ z) s + t * (R *ᵥ d) s) ((R *ᵥ d) s) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const ((R *ᵥ d) s)).const_add (w₀ s + (R *ᵥ z) s)
    simpa using this
  have hout : HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s + 0 * (R *ᵥ d) s) := by
    simpa using hdv s
  exact hout.comp (0 : ℝ) hin

/-- **Proposition 19.E.1, Proof 2** (MWG, p. 703), for the reduced problem of footnote 18. Let the
portfolio `z*` maximize `∑_s π_s v_s(w₀_s + (Rz)_s)` subject to `q·z ≤ 0` near `z*` (short sales
are unlimited, so `z*` is interior), with `π ≫ 0`, nonnegative nonzero returns and `v_s`
differentiable at `w*_s` with `v_s'(w*_s) > 0`. Then for some `α > 0`,
`α q_k = ∑_s π_s v_s'(w*_s) r_{sk}` (the first-order conditions), and with
`μ_s = π_s v_s'(w*_s) / α ≥ 0`, `q_k = ∑_s μ_s r_{sk}`. -/
theorem proposition_19_E_1_proof2 {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {v : Fin S → ℝ → ℝ}
    {w₀ : Fin S → ℝ} {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q z : Fin K → ℝ} {N : Set (Fin K → ℝ)} (hN : N ∈ 𝓝 z)
    (hmax : ∀ z' ∈ N, q ⬝ᵥ z' ≤ 0 →
      portfolioObjective π v w₀ R z' ≤ portfolioObjective π v w₀ R z) (hz : q ⬝ᵥ z ≤ 0)
    {dv : Fin S → ℝ} (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s))
    (hpos : ∀ s, 0 < dv s) :
    ∃ α : ℝ, 0 < α ∧ (∀ k, α * q k = ∑ s, π s * dv s * R s k) ∧
      ∀ k, q k = ∑ s, (π s * dv s / α) * R s k := by
  obtain ⟨α, hα, ha⟩ := foc_halfspace hN hmax hz (hasDerivAt_portfolioObjective hdv)
  have hfoc : ∀ k, α * q k = ∑ s, π s * dv s * R s k := fun k => by
    have := congrFun ha k; simp only [Pi.smul_apply, smul_eq_mul] at this; linarith
  have hαpos : 0 < α ∨ IsEmpty (Fin K) := by
    rcases isEmpty_or_nonempty (Fin K) with hK | ⟨⟨k⟩⟩
    · exact Or.inr hK
    · left
      obtain ⟨s, hs⟩ := hR.2 k
      have hRs : 0 < R s k := lt_of_le_of_ne (hR.1 s k) (Ne.symm hs)
      have hsum : 0 < ∑ s, π s * dv s * R s k :=
        lt_of_lt_of_le (mul_pos (mul_pos (hπ s) (hpos s)) hRs)
          (Finset.single_le_sum (f := fun s => π s * dv s * R s k)
            (fun s _ => mul_nonneg (mul_nonneg (hπ s).le (hpos s).le) (hR.1 s k))
            (Finset.mem_univ s))
      rcases hα.lt_or_eq with h' | h'
      · exact h'
      · have := hfoc k; rw [← h', zero_mul] at this; linarith
  rcases hαpos with hαpos | hK
  · refine ⟨α, hαpos, hfoc, fun k => ?_⟩
    have : ∑ s, π s * dv s / α * R s k = (∑ s, π s * dv s * R s k) / α := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, ← hfoc k]; field_simp
  · exact ⟨1, one_pos, fun k => isEmptyElim k, fun k => isEmptyElim k⟩

/-- **Proposition 19.E.1, Proof 2** (MWG, p. 703), from a Radner equilibrium with one good
(`L = 1`, spot price `p_s = 1`, so `v_s = u_s`). A consumer with expected utility
`∑_s π_s u_s(x_s)`, `π ≫ 0`, strictly increasing `u_s` differentiable at `x*_s` with
`u_s'(x*_s) > 0`, and interior consumption `x* ≫ 0` solves the reduced portfolio problem;
hence `q_k = ∑_s μ_s r_{sk}` with `μ_s = π_s u_s'(x*_s) / α`. -/
theorem proposition_19_E_1_proof2_radner {ι : Type*} [Fintype ι] {R : Matrix (Fin S) (Fin K) ℝ}
    (hR : NonnegNonzeroReturns R) {U : ι → CVec S 1 → ℝ} {ω x : ι → CVec S 1} {q : Fin K → ℝ}
    {z : ι → Fin K → ℝ} (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) (i : ι)
    {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → ℝ → ℝ} (hU : U i = eu1 π u)
    (hsm : ∀ s, StrictMonoOn (u s) (Set.Ici 0)) (hx : ∀ s, 0 < x i s 0) {du : Fin S → ℝ}
    (hdu : ∀ s, HasDerivAt (u s) (du s) (x i s 0)) (hpos : ∀ s, 0 < du s) :
    ∃ α : ℝ, 0 < α ∧ ∀ k, q k = ∑ s, (π s * du s / α) * R s k := by
  -- the spot budgets bind, since every `u_s` is strictly increasing
  have hbind : ∀ s, x i s 0 = ω i s 0 + (R *ᵥ z i) s := by
    intro s
    obtain ⟨⟨hx0, hqz, hsp⟩, hopt⟩ := h.1 i
    have hle : x i s 0 ≤ ω i s 0 + (R *ᵥ z i) s := by simpa [dotProduct] using hsp s
    by_contra hne
    have hlt : x i s 0 < ω i s 0 + (R *ᵥ z i) s := lt_of_le_of_ne hle hne
    set x' : CVec S 1 := Function.update (x i) s fun _ => ω i s 0 + (R *ᵥ z i) s
    have hfeas : radnerFeasible 0 R q (fun _ _ => 1) (ω i) x' (z i) := by
      refine ⟨fun s' l => ?_, hqz, fun s' => ?_⟩
      · by_cases hs : s' = s
        · subst hs; simp only [x', Function.update_self]; linarith [hx0 s' 0, hle]
        · simp only [x', Function.update_of_ne hs]; exact hx0 s' l
      · by_cases hs : s' = s
        · subst hs; simp [x', dotProduct]
        · simp only [x', Function.update_of_ne hs]; exact hsp s'
    have h1 := (h.1 i).2 _ _ hfeas
    rw [hU] at h1
    have h2 : eu1 π u (x i) < eu1 π u x' := by
      unfold eu1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have e : ∑ t ∈ Finset.univ.erase s, π t * u t (x' t 0) =
          ∑ t ∈ Finset.univ.erase s, π t * u t (x i t 0) :=
        Finset.sum_congr rfl fun t ht => by
          simp only [x', Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      rw [e]
      simp only [x', Function.update_self]
      have := hsm s (Set.mem_Ici.mpr (hx s).le) (Set.mem_Ici.mpr ((hx s).le.trans hle)) hlt
      nlinarith [hπ s]
    linarith
  have hcs : ∀ s, Continuous fun z' : Fin K → ℝ => ω i s 0 + (R *ᵥ z') s := fun s =>
    continuous_const.add ((continuous_apply s).comp
      (continuous_const.matrix_mulVec continuous_id))
  set N : Set (Fin K → ℝ) := {z' | ∀ s, 0 < ω i s 0 + (R *ᵥ z') s} with hNdef
  have hNopen : IsOpen N := by
    have : N = ⋂ s, {z' | 0 < ω i s 0 + (R *ᵥ z') s} := by ext; simp [hNdef]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (hcs s)
  have hzN : z i ∈ N := fun s => by rw [← hbind s]; exact hx s
  have hmax : ∀ z' ∈ N, q ⬝ᵥ z' ≤ 0 → portfolioObjective π u (fun s => ω i s 0) R z' ≤
      portfolioObjective π u (fun s => ω i s 0) R (z i) := by
    intro z' hz' hq
    -- the plan `x' = ω + R z'` is Radner feasible
    have hfeas : radnerFeasible 0 R q (fun _ _ => 1) (ω i)
        (fun s _ => ω i s 0 + (R *ᵥ z') s) z' := by
      refine ⟨fun s l => (hz' s).le, hq, fun s => ?_⟩
      simp [dotProduct]
    have h1 := (h.1 i).2 _ _ hfeas
    rw [hU] at h1
    have h2 : eu1 π u (x i) = portfolioObjective π u (fun s => ω i s 0) R (z i) := by
      simp only [eu1, portfolioObjective, hbind]
    have h3 : eu1 π u (fun s _ => ω i s 0 + (R *ᵥ z') s) =
        portfolioObjective π u (fun s => ω i s 0) R z' := rfl
    rw [← h2, ← h3]
    exact h1
  obtain ⟨α, hα, -, hμ⟩ := proposition_19_E_1_proof2 (v := u) (w₀ := fun s => ω i s 0) hπ hR
    (hNopen.mem_nhds hzN) hmax (h.1 i).1.2.1 (fun s => by rw [← hbind s]; exact hdu s) hpos
  exact ⟨α, hα, hμ⟩

/-! ## Exercise 19.E.1: consumption at `t = 0` -/

/-- **Exercise 19.E.1(a)** (MWG, p. 727). With consumption also at `t = 0` and utility
`u₀(x₀) + ∑_s π_s v_s(w_s)`, let `(x₀*, z*)` maximize it near `(x₀*, z*)` subject to
`p₀·x₀ + q·z ≤ p₀·ω₀`, with `u₀` having gradient `∇u₀` (directional derivatives `∇u₀·d`) and the
hypotheses of Proof 2. Then `∇u₀(x₀*) = α p₀` and `α q_k = ∑_s π_s v_s' r_{sk}` for one `α ≥ 0`;
if `α > 0` (e.g. `u₀` strictly increasing in a good with positive price), the conclusion of
Proposition 19.E.1 holds with `μ_s = π_s v_s' / α`. -/
theorem exercise_19_E_1a {π : Fin S → ℝ} {v : Fin S → ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {u₀ : (Fin L → ℝ) → ℝ} {p₀ ω₀ x₀ : Fin L → ℝ} {q z : Fin K → ℝ}
    {N : Set ((Fin L ⊕ Fin K) → ℝ)} (hN : N ∈ 𝓝 (Sum.elim x₀ z))
    (hmax : ∀ y' ∈ N, p₀ ⬝ᵥ (y' ∘ Sum.inl) + q ⬝ᵥ (y' ∘ Sum.inr) ≤ p₀ ⬝ᵥ ω₀ →
      u₀ (y' ∘ Sum.inl) + portfolioObjective π v w₀ R (y' ∘ Sum.inr) ≤
        u₀ x₀ + portfolioObjective π v w₀ R z)
    (hb : p₀ ⬝ᵥ x₀ + q ⬝ᵥ z ≤ p₀ ⬝ᵥ ω₀) {gu : Fin L → ℝ}
    (hgu : ∀ d, HasDerivAt (fun t : ℝ => u₀ (x₀ + t • d)) (gu ⬝ᵥ d) 0) {dv : Fin S → ℝ}
    (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s)) :
    ∃ α : ℝ, 0 ≤ α ∧ gu = α • p₀ ∧ ∀ k, α * q k = ∑ s, π s * dv s * R s k := by
  set F : ((Fin L ⊕ Fin K) → ℝ) → ℝ :=
    fun y' => u₀ (y' ∘ Sum.inl) + portfolioObjective π v w₀ R (y' ∘ Sum.inr) with hF
  set a : (Fin L ⊕ Fin K) → ℝ := Sum.elim gu fun k => ∑ s, π s * dv s * R s k with ha
  have hdot : ∀ y' : (Fin L ⊕ Fin K) → ℝ,
      Sum.elim p₀ q ⬝ᵥ y' = p₀ ⬝ᵥ (y' ∘ Sum.inl) + q ⬝ᵥ (y' ∘ Sum.inr) := by
    intro y'
    rw [← Sum.elim_comp_inl_inr y', sumElim_dotProduct_sumElim, Sum.elim_comp_inl_inr]
  obtain ⟨α, hα, hav⟩ := foc_halfspace (F := F) (q := Sum.elim p₀ q) (c := p₀ ⬝ᵥ ω₀) (a := a)
    hN (fun y' hy' hq => by rw [hdot] at hq; exact hmax y' hy' hq)
    (by rw [hdot]; simpa using hb) (fun d => by
      have h1 := hgu (d ∘ Sum.inl)
      have h2 := hasDerivAt_portfolioObjective (π := π) (w₀ := w₀) hdv (d ∘ Sum.inr)
      have e : a ⬝ᵥ d = gu ⬝ᵥ (d ∘ Sum.inl) +
          (fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ (d ∘ Sum.inr) := by
        rw [ha, ← Sum.elim_comp_inl_inr d, sumElim_dotProduct_sumElim, Sum.elim_comp_inl_inr]
      rw [e]
      have hfun : (fun t : ℝ => F (Sum.elim x₀ z + t • d)) =
          (fun t : ℝ => u₀ (x₀ + t • (d ∘ Sum.inl))) +
            fun t : ℝ => portfolioObjective π v w₀ R (z + t • (d ∘ Sum.inr)) := by
        funext t
        simp only [hF, Pi.add_apply]
        congr 2
      rw [hfun]
      exact h1.add h2)
  refine ⟨α, hα, funext fun l => ?_, fun k => ?_⟩
  · have := congrFun hav (Sum.inl l); simpa [ha] using this
  · have := congrFun hav (Sum.inr k); simp [ha] at this; linarith

/-- **Exercise 19.E.1(b)** (MWG, p. 727). With a single good at both dates (price `1` at `t = 0`
and spot prices `1`), the multipliers are `μ_s = π_s u₁'(x_{1s}) / u₀'(x₀)`: the ratio of the
marginal utility of one unit of consumption in state `s` (weighted by `π_s`) to the marginal
utility of consumption at `t = 0`. -/
theorem exercise_19_E_1b {π : Fin S → ℝ} {u₁ : ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {u₀ : ℝ → ℝ} {ω₀ x₀ : ℝ} {q z : Fin K → ℝ}
    {N : Set ((Fin 1 ⊕ Fin K) → ℝ)} (hN : N ∈ 𝓝 (Sum.elim (fun _ => x₀) z))
    (hmax : ∀ y' ∈ N, y' (Sum.inl 0) + q ⬝ᵥ (y' ∘ Sum.inr) ≤ ω₀ →
      u₀ (y' (Sum.inl 0)) + portfolioObjective π (fun _ => u₁) w₀ R (y' ∘ Sum.inr) ≤
        u₀ x₀ + portfolioObjective π (fun _ => u₁) w₀ R z)
    (hb : x₀ + q ⬝ᵥ z ≤ ω₀) {du₀ : ℝ} (hdu₀ : HasDerivAt u₀ du₀ x₀) (hpos : 0 < du₀)
    {du₁ : Fin S → ℝ} (hdu₁ : ∀ s, HasDerivAt u₁ (du₁ s) (w₀ s + (R *ᵥ z) s)) :
    ∀ k, q k = ∑ s, (π s * du₁ s / du₀) * R s k := by
  have hgu : ∀ d : Fin 1 → ℝ, HasDerivAt (fun t : ℝ => u₀ (((fun (_ : Fin 1) => x₀) + t • d) 0))
      ((fun _ => du₀) ⬝ᵥ d) 0 := by
    intro d
    have hin : HasDerivAt (fun t : ℝ => x₀ + t * d 0) (d 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add x₀
    have := (show HasDerivAt u₀ du₀ (x₀ + 0 * d 0) by simpa using hdu₀).comp (0 : ℝ) hin
    have e : (fun _ => du₀) ⬝ᵥ d = du₀ * d 0 := by simp [dotProduct]
    rw [e]
    exact this
  obtain ⟨α, _, hg, hq⟩ := exercise_19_E_1a (L := 1) (u₀ := fun y => u₀ (y 0))
    (p₀ := fun _ => 1) (ω₀ := fun _ => ω₀) (x₀ := fun _ => x₀) (v := fun _ => u₁) (π := π)
    (w₀ := w₀) (R := R) (q := q) (z := z) (N := N) hN
    (fun y' hy' hq' => by
      have := hmax y' hy' (by simpa [dotProduct] using hq')
      simpa using this) (by simpa [dotProduct] using hb) hgu hdu₁
  have hα : α = du₀ := by have := congrFun hg 0; simp at this; linarith
  subst hα
  intro k
  have : ∑ s, π s * du₁ s / α * R s k = (∑ s, π s * du₁ s * R s k) / α := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, ← hq k]; field_simp

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Complete asset structures, spanning and pricing by arbitrage (MWG pp. 705-707, 727-728)

* **Proposition 19.E.2(i)** with **Exercise 19.E.3**: with a complete asset structure, an
  Arrow-Debreu equilibrium is a Radner equilibrium with `q_k = ∑_s p_{gs} r_{sk}`
  (`proposition_19_E_2_i`).
* **Proposition 19.E.2(ii)**: a Radner equilibrium with a complete structure is an Arrow-Debreu
  equilibrium at prices `μ_s p_s`, `μ ≫ 0` (`proposition_19_E_2_ii`). As with Proposition
  19.D.1(ii), exact market clearing needs monotone preferences (strong monotonicity is assumed;
  correction 2).
* Uniqueness of the multipliers when `rank R = S` (p. 703), and `μ_s` is the price of the Arrow
  security of state `s` (p. 707).
* **Proposition 19.E.3**: if `Range R' = Range R`, Radner equilibrium allocations for `R` are Radner
  equilibrium allocations for `R'` (with strongly monotone preferences, used as in the book's
  proof), and redundant assets do not change the range (p. 706).
* **Exercise 19.E.4**: pricing by arbitrage of a redundant asset.
* **Example 19.E.6**: pricing an option; the formula (19.E.2), its monotonicity in `c` and `q₂`,
  and in the dispersion `α`. The printed argument for the last claim prices `r'₂(c) - r₂(c)` and
  `r₂(c)` with the multipliers of the original economy; the identity `q'₂(c) = q₃ + q₂(c)` it uses
  fails (`example_19_E_6_identity_fails`), but the conclusion is true
  (`example_19_E_6_dispersion`). Correction 5.
* **Exercise 19.E.6(a)-(f)**: pricing derived assets on `r₁ = (64, 16, 4)`, `r₂ = (0, 0, 1)`. In (d)
  the added riskless asset at price `1` creates an arbitrage (correction 6).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- `q·z = ∑_s ν_s (Rz)_s` when `q_k = ∑_s ν_s r_{sk}`. -/
theorem dot_eq_of_pricing {R : Matrix (Fin S) (Fin K) ℝ} {ν : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, ν s * R s k) (z : Fin K → ℝ) : q ⬝ᵥ z = ν ⬝ᵥ (R *ᵥ z) := by
  simp only [dotProduct, mulVec, hq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

/-! ## Proposition 19.E.2 -/

/-- **Proposition 19.E.2(i)** (MWG, p. 705) with **Exercise 19.E.3** (p. 727). Suppose the asset
structure is complete. If `x*` and `p` with `p_{gs} > 0` form an Arrow-Debreu equilibrium, then with
`q_k = ∑_s p_{gs} r_{sk}` there are portfolios `z*` such that `(q, p, z*, x*)` is a Radner
equilibrium: each `z*ᵢ` finances the Arrow-Debreu transfers `p_s·(x*_{si} - ω_{si})`, and the
Arrow-Debreu consumptions are utility maximizing in the Radner budget sets (Exercise 19.E.3). -/
theorem proposition_19_E_2_i {ι : Type*} [Fintype ι] [Nonempty ι] (g : Fin L)
    {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) {U : ι → CVec S L → ℝ}
    {ω x : ι → CVec S L} {p : CVec S L} (hp : ∀ s, 0 < p s g) (h : IsADEqmU U ω x p) :
    ∃ z : ι → Fin K → ℝ, IsRadnerEqm g R U ω (fun k => ∑ s, p s g * R s k) p x z := by
  classical
  have hsurj := (isComplete_iff_surjective R).mp hR
  set m : ι → Fin S → ℝ := fun i s => p s ⬝ᵥ (x i s - ω i s) / p s g with hm
  choose z₀ hz₀ using fun i => hsurj (m i)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set W := ∑ i, z₀ i with hW
  have hsum_m : ∑ i, m i = 0 := by
    funext s
    simp only [hm, Finset.sum_apply, Pi.zero_apply, ← Finset.sum_div, ← dotProduct_sum,
      Finset.sum_sub_distrib]
    have : ∑ i, x i s = ∑ i, ω i s := by
      have := congrFun h.2 s; simpa [Finset.sum_apply] using this
    rw [this, sub_self, dotProduct_zero, zero_div]
  have hRW : R *ᵥ W = 0 := by
    rw [hW, mulVec_sum]; simp only [hz₀]; exact hsum_m
  set z : ι → Fin K → ℝ := fun i => z₀ i - if i = i₀ then W else 0 with hz
  have hRz : ∀ i, R *ᵥ z i = m i := by
    intro i
    simp only [hz, mulVec_sub]
    split_ifs
    · rw [hRW, sub_zero, hz₀]
    · rw [mulVec_zero, sub_zero, hz₀]
  have hzsum : ∑ i, z i = 0 := by
    simp only [hz, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hW, sub_self]
  have hq := dot_eq_of_pricing (R := R) (ν := fun s => p s g) (q := fun k => ∑ s, p s g * R s k)
    (fun k => rfl)
  have hval : ∀ (i : ι) (x' : CVec S L) (z' : Fin K → ℝ),
      radnerFeasible g R (fun k => ∑ s, p s g * R s k) p (ω i) x' z' → x' ∈ adBudget p (ω i) := by
    rintro i x' z' ⟨hx', hqz, hs⟩
    refine ⟨hx', ?_⟩
    rw [hq] at hqz
    have h1 : ∑ s, (p s ⬝ᵥ x' s - p s ⬝ᵥ ω i s) ≤ ∑ s, p s g * (R *ᵥ z') s :=
      Finset.sum_le_sum fun s _ => by linarith [hs s]
    rw [Finset.sum_sub_distrib] at h1
    simp only [dotProduct] at hqz h1
    unfold cval
    simp only [dotProduct]
    linarith
  refine ⟨z, ⟨fun i => ⟨⟨(h.1 i).1.1, ?_, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => ?_,
    h.2.le⟩⟩
  · rw [hq, hRz]
    have e1 : (fun s => p s g) ⬝ᵥ m i = ∑ s, p s ⬝ᵥ (x i s - ω i s) := by
      simp only [dotProduct, hm]
      exact Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
    have e2 : ∑ s, p s ⬝ᵥ (x i s - ω i s) = cval p (x i) - cval p (ω i) := by
      simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
    rw [e1, e2]; linarith [(h.1 i).1.2]
  · rw [hRz, hm]
    simp only [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
    linarith
  · exact (h.1 i).2 x' (hval i x' z' hf).1 (hval i x' z' hf).2
  · have := congrFun hzsum k
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this]

/-- With a complete structure and strongly monotone preferences, the multipliers of Proposition
19.E.1 are strictly positive: `ν_s` is the price of the Arrow security of state `s`, which is
spanned. -/
theorem multipliers_pos_of_complete {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R)
    {q : Fin K → ℝ} (haf : ArbitrageFree R q) {ν : Fin S → ℝ}
    (hq : ∀ k, q k = ∑ s, ν s * R s k) (s : Fin S) : 0 < ν s := by
  classical
  obtain ⟨zs, hzs⟩ := (isComplete_iff_surjective R).mp hR (Pi.single s 1)
  have hval : q ⬝ᵥ zs = ν s := by rw [dot_eq_of_pricing hq, hzs]; simp [dotProduct_single]
  by_contra hle
  push Not at hle
  refine haf ⟨zs, by rw [hval]; exact hle, fun s' => ?_, ?_⟩
  · rw [hzs]; simp [Pi.single_apply]; split_ifs <;> norm_num
  · rw [hzs]; intro h0; have := congrFun h0 s; simp at this

/-- **Proposition 19.E.2(ii)** (MWG, p. 705). Suppose the asset structure is complete, returns are
nonnegative and nonzero, preferences are strongly monotone and spot prices are strictly positive.
If `(q, p, z*, x*)` is a Radner equilibrium, there are multipliers `μ ≫ 0` such that `x*` and the
contingent prices `(μ₁ p₁, …, μ_S p_S)` form an Arrow-Debreu equilibrium. (`μ_s` is the value at
`t = 0` of a unit of the numeraire good in state `s`, divided by its spot price.) -/
theorem proposition_19_E_2_ii [NeZero S] [NeZero L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) (hRn : NonnegNonzeroReturns R)
    {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L}
    {q : Fin K → ℝ} {p : CVec S L} (hp : ∀ s l, 0 < p s l) {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm g R U ω q p x z) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 < μ s) ∧ IsADEqmU U ω x (fun s => μ s • p s) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have haf := radner_arbitrageFree g h i₀ (hU i₀)
  obtain ⟨ν, -, hq⟩ := lemma_19_E_1 hRn haf
  have hν := multipliers_pos_of_complete hR haf hq
  have hsurj := (isComplete_iff_surjective R).mp hR
  set μ : Fin S → ℝ := fun s => ν s / p s g with hμ
  have hμpos : ∀ s, 0 < μ s := fun s => div_pos (hν s) (hp s g)
  have hcv : ∀ y : CVec S L, cval (fun s => μ s • p s) y = ∑ s, μ s * (p s ⬝ᵥ y s) := by
    intro y; simp [cval, smul_dotProduct]
  have hequiv : ∀ (i : ι) (x' : CVec S L), (∃ z', radnerFeasible g R q p (ω i) x' z') ↔
      x' ∈ adBudget (fun s => μ s • p s) (ω i) := by
    intro i x'
    constructor
    · rintro ⟨z', hx', hqz, hs⟩
      refine ⟨hx', ?_⟩
      rw [hcv, hcv]
      have h1 : ∀ s, μ s * (p s ⬝ᵥ x' s) ≤ μ s * (p s ⬝ᵥ ω i s) + ν s * (R *ᵥ z') s := by
        intro s
        have := mul_le_mul_of_nonneg_left (hs s) (hμpos s).le
        rw [mul_add, ← mul_assoc, hμ, div_mul_cancel₀ _ (hp s g).ne'] at this
        exact this
      have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
      rw [Finset.sum_add_distrib] at h2
      rw [dot_eq_of_pricing hq] at hqz
      simp only [dotProduct] at hqz
      linarith
    · rintro ⟨hx', hb⟩
      obtain ⟨z', hz'⟩ := hsurj fun s => p s ⬝ᵥ (x' s - ω i s) / p s g
      refine ⟨z', hx', ?_, fun s => ?_⟩
      · rw [dot_eq_of_pricing hq, hz']
        rw [hcv, hcv] at hb
        have e : ν ⬝ᵥ (fun s => p s ⬝ᵥ (x' s - ω i s) / p s g) =
            ∑ s, μ s * (p s ⬝ᵥ x' s) - ∑ s, μ s * (p s ⬝ᵥ ω i s) := by
          simp only [dotProduct_sub]
          rw [dotProduct, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [hμ]; field_simp
        rw [e]; linarith
      · rw [hz']; simp only [mul_div_cancel₀ _ (hp s g).ne', dotProduct_sub]; linarith
  have hopt : ∀ i, (NonnegC (x i) ∧ cval (fun s => μ s • p s) (x i) ≤
      cval (fun s => μ s • p s) (ω i)) ∧ ∀ x', NonnegC x' →
        cval (fun s => μ s • p s) x' ≤ cval (fun s => μ s • p s) (ω i) → U i x' ≤ U i (x i) := by
    intro i
    refine ⟨(hequiv i (x i)).mp ⟨z i, (h.1 i).1⟩, fun x' hx' hb => ?_⟩
    obtain ⟨z', hz'⟩ := (hequiv i x').mpr ⟨hx', hb⟩
    exact (h.1 i).2 x' z' hz'
  have hbind : ∀ i, cval (fun s => μ s • p s) (x i) = cval (fun s => μ s • p s) (ω i) := by
    intro i
    refine le_antisymm (hopt i).1.2 (not_lt.mp fun hlt => ?_)
    obtain ⟨x', hle', hne, hc⟩ := exists_larger_cheap (fun s => μ s • p s) (x i)
      (sub_pos.mpr hlt)
    have hx := (hopt i).1.1
    have := (hopt i).2 x' (fun s l => (hx s l).trans (hle' s l)) (by linarith)
    linarith [hU i _ _ hx hle' hne]
  refine ⟨μ, hμpos, hopt, clear_eq_of_binding (fun s l => ?_) h.2.2 hbind⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (hμpos s) (hp s l)

/-- **p. 703**. With `rank R = S` the multipliers are unique. -/
theorem multipliers_unique {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) {μ μ' : Fin S → ℝ}
    (h : ∀ k, ∑ s, μ s * R s k = ∑ s, μ' s * R s k) : μ = μ' := by
  classical
  funext s
  obtain ⟨zs, hzs⟩ := (isComplete_iff_surjective R).mp hR (Pi.single s 1)
  have h1 := dot_eq_of_pricing (q := fun k => ∑ s, μ s * R s k) (fun k => rfl) zs
  have h2 := dot_eq_of_pricing (q := fun k => ∑ s, μ s * R s k) (ν := μ') (fun k => h k) zs
  rw [hzs] at h1 h2
  simp only [dotProduct_single, mul_one] at h1 h2
  rw [← h1, ← h2]

/-- **p. 707**. `μ_s` is the price of the Arrow security of state `s` (when it is spanned). -/
theorem arrow_price {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, μ s * R s k) {s : Fin S} {z : Fin K → ℝ}
    (hz : R *ᵥ z = Pi.single s 1) : q ⬝ᵥ z = μ s := by
  classical
  rw [dot_eq_of_pricing hq, hz, dotProduct_single, mul_one]

/-! ## Proposition 19.E.3 and redundant assets -/

/-- With strongly monotone preferences and nonnegative nonzero returns, the date-0 budget
constraint binds at a Radner equilibrium. -/
theorem radner_date0_binds {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) : q ⬝ᵥ z i = 0 := by
  classical
  have hqpos := (radner_arbitrageFree g h i hU).pos hRn
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  refine le_antisymm hqz (not_lt.mp fun hlt => ?_)
  obtain ⟨k₀⟩ : Nonempty (Fin K) := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    simp [dotProduct] at hlt
  set ε := -(q ⬝ᵥ z i) / q k₀ with hε
  have hεpos : 0 < ε := div_pos (by linarith) (hqpos k₀)
  set δ : CVec S L := fun s l => if l = g then ε * R s k₀ else 0 with hδ
  have hle : x i ≤ x i + δ := fun s l => by
    simp only [Pi.add_apply, hδ]; split_ifs
    · nlinarith [hRn.1 s k₀]
    · linarith
  have hne : x i ≠ x i + δ := by
    intro h0
    obtain ⟨s, hs⟩ := hRn.2 k₀
    have h1 := congrFun (congrFun h0 s) g
    simp only [Pi.add_apply, hδ, ite_true] at h1
    have : ε * R s k₀ = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hεpos.ne'
    · exact hs h'
  have hfeas : radnerFeasible g R q p (ω i) (x i + δ) (z i + ε • Pi.single k₀ 1) := by
    refine ⟨fun s l => (hx s l).trans (hle s l), ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hε]
      field_simp [(hqpos k₀).ne']
      linarith
    · have hd : p s ⬝ᵥ δ s = p s g * (ε * R s k₀) := by simp [hδ, dotProduct]
      rw [Pi.add_apply, dotProduct_add, hd, mulVec_add, mulVec_smul, Pi.add_apply,
        Pi.smul_apply, mulVec_single, smul_eq_mul]
      linarith [hsp s]
  linarith [hopt _ _ hfeas, hU _ _ hx hle hne]

/-- **Proposition 19.E.3** (MWG, p. 706). Let `(q, p, z*, x*)` be a Radner equilibrium for the
return matrix `R` (nonnegative nonzero returns; strongly monotone preferences, as used in the
book's proof), and let `R'` be an `S × K'` return matrix with `Range R' = Range R`. Then `x*` is
also a Radner equilibrium allocation for `R'`, with asset prices `q' = μ·R'` and the same spot
prices. -/
theorem proposition_19_E_3 {ι : Type*} [Fintype ι] [Nonempty ι] (g : Fin L) {K' : ℕ}
    {R : Matrix (Fin S) (Fin K) ℝ} (hRn : NonnegNonzeroReturns R)
    {R' : Matrix (Fin S) (Fin K') ℝ} (hrange : ∀ v, (∃ z, R *ᵥ z = v) ↔ ∃ z', R' *ᵥ z' = v)
    {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L}
    {q : Fin K → ℝ} {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) :
    ∃ (q' : Fin K' → ℝ) (z' : ι → Fin K' → ℝ), IsRadnerEqm g R' U ω q' p x z' := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have haf := radner_arbitrageFree g h i₀ (hU i₀)
  have hqpos := haf.pos hRn
  obtain ⟨μ, -, hq⟩ := lemma_19_E_1 hRn haf
  set q' : Fin K' → ℝ := fun k => ∑ s, μ s * R' s k with hq'
  have hdot := dot_eq_of_pricing hq
  have hdot' := dot_eq_of_pricing (R := R') (q := q') (fun k => rfl)
  -- the budget sets coincide (19.E.1)
  have hequiv : ∀ (i : ι) (x' : CVec S L), (∃ z', radnerFeasible g R' q' p (ω i) x' z') →
      ∃ z'', radnerFeasible g R q p (ω i) x' z'' := by
    rintro i x' ⟨z', hx', hqz, hs⟩
    obtain ⟨z'', hz''⟩ := (hrange (R' *ᵥ z')).mpr ⟨z', rfl⟩
    refine ⟨z'', hx', ?_, fun s => ?_⟩
    · rw [hdot, hz'', ← hdot']; exact hqz
    · rw [hz'']; exact hs s
  -- the date-0 budgets bind and the asset markets clear exactly
  have hbind : ∀ i, q ⬝ᵥ z i = 0 := fun i => radner_date0_binds g hRn h i (hU i)
  have hzsum : ∑ i, z i = 0 := by
    have hq0 : q ⬝ᵥ ∑ i, z i = 0 := by rw [dotProduct_sum]; simp [hbind]
    have hnp : ∀ k, q k * (∑ i, z i) k ≤ 0 := fun k =>
      mul_nonpos_of_nonneg_of_nonpos (hqpos k).le (by simpa [Finset.sum_apply] using h.2.1 k)
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hnp k).mp hq0 k (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (hqpos k).ne'
    · exact h'
  choose z₀ hz₀ using fun i => (hrange (R *ᵥ z i)).mp ⟨z i, rfl⟩
  set W := ∑ i, z₀ i with hW
  have hRW : R' *ᵥ W = 0 := by
    rw [hW, mulVec_sum]; simp only [hz₀]; rw [← mulVec_sum, hzsum, mulVec_zero]
  set z' : ι → Fin K' → ℝ := fun i => z₀ i - if i = i₀ then W else 0 with hz'
  have hRz' : ∀ i, R' *ᵥ z' i = R *ᵥ z i := by
    intro i
    simp only [hz', mulVec_sub]
    split_ifs
    · rw [hRW, sub_zero, hz₀]
    · rw [mulVec_zero, sub_zero, hz₀]
  have hz'sum : ∑ i, z' i = 0 := by
    simp only [hz', Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hW, sub_self]
  refine ⟨q', z', ⟨fun i => ⟨⟨(h.1 i).1.1, ?_, fun s => ?_⟩, fun x' z'' hf => ?_⟩,
    fun k => ?_, h.2.2⟩⟩
  · rw [hdot', hRz', ← hdot]; exact (h.1 i).1.2.1
  · rw [hRz']; exact (h.1 i).1.2.2 s
  · obtain ⟨w, hw⟩ := hequiv i x' ⟨z'', hf⟩
    exact (h.1 i).2 x' w hw
  · have := congrFun hz'sum k
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this]

/-- The asset structure `R` with one more asset `r` appended. -/
def appendAsset (R : Matrix (Fin S) (Fin K) ℝ) (r : ReturnVector S) :
    Matrix (Fin S) (Fin (K + 1)) ℝ :=
  Matrix.of fun s k => Fin.lastCases (r s) (fun k => R s k) k

/-- **p. 706**. A redundant asset (one whose return vector is a combination of the others) does
not change the space `Range R` of spannable wealth transfers; by Proposition 19.E.3 its addition
or deletion does not change the Radner equilibrium allocations. -/
theorem redundant_range {R : Matrix (Fin S) (Fin K) ℝ} {r : ReturnVector S}
    (hr : ∃ a, R *ᵥ a = r) (v : Fin S → ℝ) :
    (∃ z, R *ᵥ z = v) ↔ ∃ z', appendAsset R r *ᵥ z' = v := by
  obtain ⟨a, ha⟩ := hr
  have hmv : ∀ z' : Fin (K + 1) → ℝ, appendAsset R r *ᵥ z' =
      R *ᵥ (fun k => z' k.castSucc) + z' (Fin.last K) • r := by
    intro z'
    funext s
    simp [appendAsset, mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Fin.snoc z 0, by rw [hmv]; simp⟩
  · rintro ⟨z', rfl⟩
    exact ⟨(fun k => z' k.castSucc) + z' (Fin.last K) • a, by
      rw [hmv, mulVec_add, mulVec_smul, ha]⟩

/-- **Exercise 19.E.4** (MWG, p. 706). Pricing by arbitrage: if `r₃ = α₁ r₁ + α₂ r₂` and the asset
prices are given by multipliers (`q_k = ∑_s μ_s r_{sk}`, Proposition 19.E.1), then
`q₃ = α₁ q₁ + α₂ q₂`. -/
theorem exercise_19_E_4 {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, μ s * R s k) {k₁ k₂ k₃ : Fin K} {α₁ α₂ : ℝ}
    (hr : ∀ s, R s k₃ = α₁ * R s k₁ + α₂ * R s k₂) : q k₃ = α₁ * q k₁ + α₂ * q k₂ := by
  rw [hq, hq, hq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [hr]; ring

/-- **Exercise 19.E.4** (MWG, p. 706), at a Radner equilibrium: with unlimited short sales,
nonnegative nonzero returns and some strongly monotone consumer, `r₃ = α₁ r₁ + α₂ r₂` forces
`q₃ = α₁ q₁ + α₂ q₂`. -/
theorem exercise_19_E_4_eqm {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) {k₁ k₂ k₃ : Fin K} {α₁ α₂ : ℝ}
    (hr : ∀ s, R s k₃ = α₁ * R s k₁ + α₂ * R s k₂) : q k₃ = α₁ * q k₁ + α₂ * q k₂ := by
  obtain ⟨μ, -, hq⟩ := proposition_19_E_1 g hRn h i hU
  exact exercise_19_E_4 hq hr

/-! ## Example 19.E.6: pricing an option -/

/-- The two assets of Example 19.E.6: `r₁ = (1, 1)` and `r₂ = (3 + α, 1 - α)`. -/
def r2_19E6 (α : ℝ) : ReturnVector 2 := ![3 + α, 1 - α]

/-- **Example 19.E.6** (MWG, p. 707). For `α > 0` and `c ∈ (1, 3)`, the call option on `r₂` with
strike `c` returns `(3 + α - c, 0)`, and
`r₂(c) = (3 + α - c)/(2 + 2α) · r₂ - (1 - α)(3 + α - c)/(2 + 2α) · r₁`. -/
theorem example_19_E_6_returns {α c : ℝ} (hα : 0 < α) (hc1 : 1 < c) (hc3 : c < 3) :
    callOption (r2_19E6 α) c = ![3 + α - c, 0] ∧
      ∀ s, callOption (r2_19E6 α) c s = (3 + α - c) / (2 + 2 * α) * r2_19E6 α s -
        (1 - α) * (3 + α - c) / (2 + 2 * α) * 1 := by
  have h1 : callOption (r2_19E6 α) c = ![3 + α - c, 0] := by
    funext s
    fin_cases s
    · simp [callOption, r2_19E6]; linarith
    · simp [callOption, r2_19E6]; linarith
  refine ⟨h1, fun s => ?_⟩
  rw [h1]
  have hpos : (2 + 2 * α) ≠ 0 := by positivity
  fin_cases s <;> simp [r2_19E6] <;> field_simp <;> ring

/-- **Example 19.E.6** (MWG, p. 707). The multipliers are determined by `(1, q₂) = μ·R`:
`μ₁ = (q₂ - (1 - α))/(2 + 2α)`, `μ₂ = 1 - μ₁`, and the arbitrage price of the option is (19.E.2):
`q₂(c) = μ·r₂(c) = (3 + α - c)/(2 + 2α) · (q₂ - (1 - α))`. -/
theorem example_19_E_6_price {α c q₂ : ℝ} (hα : 0 < α) (hc1 : 1 < c) (hc3 : c < 3)
    {μ : Fin 2 → ℝ} (h1 : μ 0 + μ 1 = 1) (h2 : μ 0 * (3 + α) + μ 1 * (1 - α) = q₂) :
    μ 0 = (q₂ - (1 - α)) / (2 + 2 * α) ∧ μ 1 = 1 - μ 0 ∧
      μ ⬝ᵥ callOption (r2_19E6 α) c = (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α)) := by
  have hpos : (2 + 2 * α) ≠ 0 := by positivity
  have hμ0 : μ 0 = (q₂ - (1 - α)) / (2 + 2 * α) := by
    field_simp; nlinarith
  refine ⟨hμ0, by linarith, ?_⟩
  rw [(example_19_E_6_returns hα hc1 hc3).1]
  simp [dotProduct, Fin.sum_univ_two, hμ0]
  ring

/-- **Example 19.E.6** (MWG, p. 707). If the prices of `r₁` and `r₂` are arbitrage free
(`μ ≥ 0`), then `3 + α ≥ q₂ ≥ 1 - α`; hence `q₂(c) ≥ 0`, `q₂(c)` is decreasing in `c` and
increasing in `q₂`. -/
theorem example_19_E_6_bounds {α q₂ : ℝ} (hα : 0 < α) {μ : Fin 2 → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (h1 : μ 0 + μ 1 = 1) (h2 : μ 0 * (3 + α) + μ 1 * (1 - α) = q₂) :
    1 - α ≤ q₂ ∧ q₂ ≤ 3 + α ∧
      (∀ c, c < 3 + α → 0 ≤ (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))) ∧
      (∀ c c', c ≤ c' → (3 + α - c') / (2 + 2 * α) * (q₂ - (1 - α)) ≤
        (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))) ∧
      ∀ c q₂', c ≤ 3 + α → q₂ ≤ q₂' → (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α)) ≤
        (3 + α - c) / (2 + 2 * α) * (q₂' - (1 - α)) := by
  have hlo : 1 - α ≤ q₂ := by nlinarith [hμ 0, hμ 1]
  have hhi : q₂ ≤ 3 + α := by nlinarith [hμ 0, hμ 1]
  have hd : 0 < 2 + 2 * α := by positivity
  refine ⟨hlo, hhi, fun c hc => ?_, fun c c' hcc => ?_, fun c q₂' hc hq => ?_⟩
  · exact mul_nonneg (div_nonneg (by linarith) hd.le) (by linarith)
  · apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  · exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hd.le)

/-- The option price `q₂(c)` of (19.E.2) as a function of the dispersion `α`. -/
noncomputable def optionPrice19E6 (α c q₂ : ℝ) : ℝ := (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))

/-- **Example 19.E.6** (MWG, p. 707), the dispersion claim, proved directly: if `q₂` stays constant
and `α' > α`, the option becomes (weakly) more valuable: `q'₂(c) ≥ q₂(c)` (for `c ∈ (1, 3)` and
arbitrage-free `q₂`, i.e. `1 - α ≤ q₂ ≤ 3 + α`). -/
theorem example_19_E_6_dispersion {α α' c q₂ : ℝ} (hα : 0 < α) (hαα : α ≤ α') (hc1 : 1 < c)
    (hc3 : c < 3) (hlo : 1 - α ≤ q₂) (hhi : q₂ ≤ 3 + α) :
    optionPrice19E6 α c q₂ ≤ optionPrice19E6 α' c q₂ := by
  unfold optionPrice19E6
  have h1 : 0 < 2 + 2 * α := by positivity
  have h2 : 0 < 2 + 2 * α' := by linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ h1 h2]
  -- `(A+a')(Q+a')(1+a) - (A+a)(Q+a)(1+a') = (a'-a)((1+a)(1+a') - (1-A)(1-Q))`
  have key : (3 + α' - c) * (q₂ - (1 - α')) * (2 + 2 * α) -
      (3 + α - c) * (q₂ - (1 - α)) * (2 + 2 * α') =
      2 * (α' - α) * ((1 + α) * (1 + α') - (c - 2) * (2 - q₂)) := by ring
  have hb : (c - 2) * (2 - q₂) ≤ (1 + α) * (1 + α') := by
    have hc : |c - 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hq : |2 - q₂| ≤ 1 + α := abs_le.mpr ⟨by linarith, by linarith⟩
    calc (c - 2) * (2 - q₂) ≤ |c - 2| * |2 - q₂| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ 1 * (1 + α) := mul_le_mul hc hq (abs_nonneg _) zero_le_one
      _ ≤ (1 + α) * (1 + α') := by nlinarith
  nlinarith [key, hb, mul_nonneg (sub_nonneg.mpr hαα) (sub_nonneg.mpr hb)]

/-- **Example 19.E.6** (MWG, p. 707), correction 5: the printed argument claims
`q'₂(c) = q₃ + q₂(c)` with `q₃` the arbitrage price of `r₃ = r'₂(c) - r₂(c)`. With `α = 1/2`,
`α' = 1`, `q₂ = 3`, `c = 2`, this fails whether `q₃` is priced with the multipliers `μ` of the
original economy or `μ'` of the new one: `q₂(c) = 5/4`, `q'₂(c) = 3/2`, while `μ·r₃ = 5/12` and
`μ'·r₃ = 3/8`. -/
theorem example_19_E_6_identity_fails :
    let μ : Fin 2 → ℝ := ![5 / 6, 1 / 6]
    let μ' : Fin 2 → ℝ := ![3 / 4, 1 / 4]
    let r₃ := callOption (r2_19E6 1) 2 - callOption (r2_19E6 (1 / 2)) 2
    μ 0 + μ 1 = 1 ∧ μ 0 * (3 + 1 / 2) + μ 1 * (1 - 1 / 2) = 3 ∧
      μ' 0 + μ' 1 = 1 ∧ μ' 0 * (3 + 1) + μ' 1 * (1 - 1) = 3 ∧
      optionPrice19E6 (1 / 2) 2 3 = 5 / 4 ∧ optionPrice19E6 1 2 3 = 3 / 2 ∧
      μ ⬝ᵥ r₃ = 5 / 12 ∧ μ' ⬝ᵥ r₃ = 3 / 8 ∧
      optionPrice19E6 1 2 3 ≠ μ ⬝ᵥ r₃ + optionPrice19E6 (1 / 2) 2 3 ∧
      optionPrice19E6 1 2 3 ≠ μ' ⬝ᵥ r₃ + optionPrice19E6 (1 / 2) 2 3 := by
  intro μ μ' r₃
  have hr : r₃ = ![1 / 2, 0] := by
    funext s; fin_cases s <;> simp [r₃, callOption, r2_19E6] <;> norm_num
  simp only [hr, optionPrice19E6, μ, μ', dotProduct, Fin.sum_univ_two]
  norm_num

/-! ## Exercise 19.E.6 -/

/-- The primary assets of Exercise 19.E.6: `r₁ = (64, 16, 4)`, `r₂ = (0, 0, 1)`. -/
def r1_19E6x : ReturnVector 3 := ![64, 16, 4]

/-- `r₂ = (0, 0, 1)`. -/
def r2_19E6x : ReturnVector 3 := ![0, 0, 1]

/-- State prices consistent with `q₁ = 32`, `q₂ = 1`. -/
def ConsistentStatePrices (μ : Fin 3 → ℝ) : Prop :=
  μ ⬝ᵥ r1_19E6x = 32 ∧ μ ⬝ᵥ r2_19E6x = 1

/-- **Exercise 19.E.6(a)** (MWG, p. 727). "The right to buy one unit of asset 1 at 75% of its spot
value": returns `max{0, r₁ - 0.75 r₁} = (16, 4, 1) = r₁/4`, price `q₁/4 = 8`. -/
theorem exercise_19_E_6a :
    (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ →
        μ ⬝ᵥ (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = 8 := by
  have h : (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ ⟨h1, _⟩ => ?_⟩
  rw [h]
  simp [r1_19E6x, dotProduct, Fin.sum_univ_three] at h1 ⊢
  linarith

/-- **Exercise 19.E.6(b)** (MWG, p. 727). Exercisable only if the spot value is at least `10`:
returns `(16, 4, 0) = r₁/4 - r₂`, price `8 - 1 = 7`. -/
theorem exercise_19_E_6b :
    (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
        ![16, 4, 0] ∧
      ∀ μ, ConsistentStatePrices μ → μ ⬝ᵥ
        (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) = 7 := by
  have h : (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
      ![16, 4, 0] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ ⟨h1, h2⟩ => ?_⟩
  rw [h]
  simp [r1_19E6x, r2_19E6x, dotProduct, Fin.sum_univ_three] at h1 h2 ⊢
  linarith

/-- **Exercise 19.E.6(c)** (MWG, p. 727). With "at least 19" the returns are `(16, 0, 0)`, which is
not a combination of `r₁` and `r₂`; it cannot be priced by arbitrage: two nonnegative state-price
vectors consistent with `q₁ = 32`, `q₂ = 1` give it the prices `7` and `0`. -/
theorem exercise_19_E_6c :
    (fun s => if 19 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
        ![16, 0, 0] ∧
      (¬ ∃ a b : ℝ, ∀ s, ![(16 : ℝ), 0, 0] s = a * r1_19E6x s + b * r2_19E6x s) ∧
      ConsistentStatePrices ![7 / 16, 0, 1] ∧ ConsistentStatePrices ![0, 7 / 4, 1] ∧
      ![(7 : ℝ) / 16, 0, 1] ⬝ᵥ ![16, 0, 0] = 7 ∧ ![(0 : ℝ), 7 / 4, 1] ⬝ᵥ ![16, 0, 0] = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  · rintro ⟨a, b, h⟩
    have h0 := h 0; have h1 := h 1
    simp [r1_19E6x, r2_19E6x] at h0 h1
    linarith
  all_goals simp [ConsistentStatePrices, r1_19E6x, r2_19E6x, dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- **Exercise 19.E.6(d)** (MWG, p. 727), correction 6. Adding a riskless asset `(1, 1, 1)` makes
the structure complete, but at the price `1` the three prices admit an arbitrage (buy the riskless
asset, sell `r₂`: cost `0`, returns `(1, 1, 0)`); the unique linear state prices are
`(7/12, -7/12, 1)`, not nonnegative. So the prices cannot arise at an equilibrium with strongly
monotone preferences; linear pricing would give `(16, 0, 0)` the value `28/3`. -/
theorem exercise_19_E_6d :
    let R : Matrix (Fin 3) (Fin 3) ℝ := returnMatrix ![r1_19E6x, r2_19E6x, fun _ => 1]
    IsComplete R ∧ ¬ ArbitrageFree R ![32, 1, 1] ∧
      (∀ μ : Fin 3 → ℝ, (∀ k, ![(32 : ℝ), 1, 1] k = ∑ s, μ s * R s k) → μ = ![7 / 12, -7 / 12, 1]) ∧
      ![(7 : ℝ) / 12, -7 / 12, 1] ⬝ᵥ ![16, 0, 0] = 28 / 3 := by
  intro R
  have hR : R = !![64, 0, 1; 16, 0, 1; 4, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, returnMatrix, r1_19E6x, r2_19E6x]
  refine ⟨?_, ?_, fun μ hμ => ?_, ?_⟩
  · unfold IsComplete
    rw [hR, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
    rw [Matrix.det_fin_three]; norm_num
  · intro h
    apply h
    refine ⟨![0, -1, 1], by simp [dotProduct, Fin.sum_univ_three], fun s => ?_, fun h0 => ?_⟩
    · rw [hR]; fin_cases s <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
    · have := congrFun h0 0
      rw [hR] at this
      simp [mulVec, dotProduct, Fin.sum_univ_three] at this
  · have h0 := hμ 0; have h1 := hμ 1; have h2 := hμ 2
    rw [hR] at h0 h1 h2
    simp [Fin.sum_univ_three] at h0 h1 h2
    funext s
    fin_cases s <;> simp <;> linarith
  · simp [dotProduct, Fin.sum_univ_three]; norm_num

/-- **Exercise 19.E.6(e)** (MWG, pp. 727-728). At the holder's choice, `1` dollar or the right of
(a): returns `max{1, r₁/4} = (16, 4, 1)`, price `8`. -/
theorem exercise_19_E_6e :
    (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ →
        μ ⬝ᵥ (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = 8 := by
  have h : (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ hμ => ?_⟩
  rw [h, ← (exercise_19_E_6a.1)]
  exact exercise_19_E_6a.2 μ hμ

/-- **Exercise 19.E.6(f)** (MWG, p. 728). As in (e), with the right exercisable only if the spot
value is at least `10`: returns `(16, 4, 1)` again (in state 3 the dollar is chosen), price `8`. -/
theorem exercise_19_E_6f :
    (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) else 1) =
        ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ → μ ⬝ᵥ
        (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))
          else 1) = 8 := by
  have h : (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))
      else 1) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ hμ => ?_⟩
  rw [h, ← (exercise_19_E_6a.1)]
  exact exercise_19_E_6a.2 μ hμ

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Long-lived assets in a tree (MWG pp. 707-708, Example 19.E.7, Exercise 19.E.5)

* **Small type, pp. 707-708**: with short-lived assets at every date-event `tE`, completeness means
  `rank R(tE) = S(tE)` at every node (`IsCompleteTree`).
* **Example 19.E.7**: the tree of Figure 19.B.2 with `T = 2` (nodes `a`, `b`, `c` and terminal
  states `1-4`), two long-lived assets `r₁ = (1, 1, 1, 1)`, `r₂ = (0, 1, 0, 1)` traded at `a`,
  `b`, `c`.
  Arbitrage at `b`, `c` and `a` (Lemma 19.E.1) gives `μ`, `λ ≥ 0` with `μ₁ + μ₂ = 1`, `μ₂ = q_b`,
  `μ₃ + μ₄ = 1`, `μ₄ = q_c`, `λ_b + λ_c = 1`, `q_a = λ_b q_b + λ_c q_c` (`example_19_E_7`), and
  Arrow-Debreu prices `p = (λ_b μ₁, λ_b μ₂, λ_c μ₃, λ_c μ₄)`.
* **Exercise 19.E.5**: if `q_b ≠ q_c`, the final consumptions reachable by sequential trade in the
  two assets are exactly those affordable at the Arrow-Debreu prices `p` (`exercise_19_E_5`).
* **Footnote 21**: the martingale property: each asset price is the conditional expectation of the
  final returns under the Arrow-Debreu prices (`footnote_19_21`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-- **pp. 707-708**. A tree asset structure with short-lived assets: at each admissible
date-event `n` the return matrix `R n` has one row per successor; it is complete when
`rank R(tE) = S(tE)` at every node (Definition 19.E.3 node by node). -/
def IsCompleteTree {N : Type*} {succ : N → ℕ} {K : N → ℕ}
    (R : ∀ n, Matrix (Fin (succ n)) (Fin (K n)) ℝ) : Prop :=
  ∀ n, IsComplete (R n)

/-- The return matrix at node `b` (states 1, 2) or `c` (states 3, 4): asset 1 pays `(1, 1)` and
asset 2 pays `(0, 1)`. -/
def nodeMatrix19E7 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The values at `t = 1` of the two assets seen from node `a`: `(1, q_b)` at `b`, `(1, q_c)` at
`c`. -/
def rootMatrix19E7 (qb qc : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, qb; 1, qc]

/-- **Example 19.E.7** (MWG, p. 708). If asset prices are arbitrage free at `b` (prices `(1, q_b)`),
at `c` (prices `(1, q_c)`) and at `a` (prices `(1, q_a)`, with `q_b, q_c ≥ 0` not both zero), there
are `μ, λ ≥ 0` with `μ₁ + μ₂ = 1`, `μ₂ = q_b`, `μ₃ + μ₄ = 1`, `μ₄ = q_c`, `λ_b + λ_c = 1` and
`q_a = λ_b q_b + λ_c q_c` (Proposition 19.E.1 at each node). -/
theorem example_19_E_7 {qa qb qc : ℝ} (hb : ArbitrageFree nodeMatrix19E7 ![1, qb])
    (hc : ArbitrageFree nodeMatrix19E7 ![1, qc])
    (hRa : NonnegNonzeroReturns (rootMatrix19E7 qb qc))
    (ha : ArbitrageFree (rootMatrix19E7 qb qc) ![1, qa]) :
    ∃ μ : Fin 4 → ℝ, ∃ lam : Fin 2 → ℝ, (∀ s, 0 ≤ μ s) ∧ (∀ n, 0 ≤ lam n) ∧
      μ 0 + μ 1 = 1 ∧ μ 1 = qb ∧ μ 2 + μ 3 = 1 ∧ μ 3 = qc ∧ lam 0 + lam 1 = 1 ∧
      qa = lam 0 * qb + lam 1 * qc := by
  have hN : NonnegNonzeroReturns nodeMatrix19E7 := by
    refine ⟨fun s k => ?_, fun k => ⟨1, ?_⟩⟩
    · fin_cases s <;> fin_cases k <;> simp [nodeMatrix19E7]
    · fin_cases k <;> simp [nodeMatrix19E7]
  obtain ⟨μb, hμb, hqb⟩ := lemma_19_E_1 hN hb
  obtain ⟨μc, hμc, hqc⟩ := lemma_19_E_1 hN hc
  obtain ⟨lam, hlam, hqa⟩ := lemma_19_E_1 hRa ha
  have b0 := hqb 0; have b1 := hqb 1; have c0 := hqc 0; have c1 := hqc 1
  have a0 := hqa 0; have a1 := hqa 1
  simp [nodeMatrix19E7, rootMatrix19E7, Fin.sum_univ_two] at b0 b1 c0 c1 a0 a1
  refine ⟨![μb 0, μb 1, μc 0, μc 1], lam, fun s => ?_, hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases s <;> simp [hμb, hμc]
  all_goals first | linarith | (simp; linarith)

/-- The Arrow-Debreu prices of Example 19.E.7: `p = (λ_b μ₁, λ_b μ₂, λ_c μ₃, λ_c μ₄)`. -/
def adPrices19E7 (μ : Fin 4 → ℝ) (lam : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![lam 0 * μ 0, lam 0 * μ 1, lam 1 * μ 2, lam 1 * μ 3]

/-- **Exercise 19.E.5** (MWG, p. 727). The net trades `m ∈ ℝ⁴` in final consumption reachable by
sequential trade: at `a` buy `y_a` units of asset 1 and `z_a` of asset 2 with
`y_a + q_a z_a ≤ 0`; at `b` rebalance to `(y_b, z_b)` with `y_b + q_b z_b ≤ y_a + q_b z_a`, and
similarly at `c`; then `m₁ ≤ y_b`, `m₂ ≤ y_b + z_b`, `m₃ ≤ y_c`, `m₄ ≤ y_c + z_c`. -/
def SeqReachable19E7 (qa qb qc : ℝ) (m : Fin 4 → ℝ) : Prop :=
  ∃ ya za yb zb yc zc : ℝ, ya + qa * za ≤ 0 ∧ yb + qb * zb ≤ ya + qb * za ∧
    yc + qc * zc ≤ ya + qc * za ∧ m 0 ≤ yb ∧ m 1 ≤ yb + zb ∧ m 2 ≤ yc ∧ m 3 ≤ yc + zc

/-- **Exercise 19.E.5** (MWG, p. 727). Under the weak condition `q_b ≠ q_c`, the net trades in
final consumption achievable through sequential trade at the prices `(q_a, q_b, q_c)` are exactly
those affordable with the four Arrow-Debreu contingent commodities at prices `p` (so the sets of
achievable final consumptions `ω + m`, `x ≥ 0`, coincide). -/
theorem exercise_19_E_5 {qa qb qc : ℝ} (hbc : qb ≠ qc) {μ : Fin 4 → ℝ} {lam : Fin 2 → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hlam : ∀ n, 0 ≤ lam n) (h01 : μ 0 + μ 1 = 1) (h1 : μ 1 = qb)
    (h23 : μ 2 + μ 3 = 1) (h3 : μ 3 = qc) (hl : lam 0 + lam 1 = 1)
    (hqa : qa = lam 0 * qb + lam 1 * qc) (m : Fin 4 → ℝ) :
    SeqReachable19E7 qa qb qc m ↔ adPrices19E7 μ lam ⬝ᵥ m ≤ 0 := by
  have hval : adPrices19E7 μ lam ⬝ᵥ m =
      lam 0 * (μ 0 * m 0 + μ 1 * m 1) + lam 1 * (μ 2 * m 2 + μ 3 * m 3) := by
    simp [adPrices19E7, dotProduct, Fin.sum_univ_four]; ring
  rw [hval]
  constructor
  · rintro ⟨ya, za, yb, zb, yc, zc, ha, hb, hc, m0, m1, m2, m3⟩
    have kb : μ 0 * m 0 + μ 1 * m 1 ≤ ya + qb * za := by
      have := mul_le_mul_of_nonneg_left m0 (hμ 0)
      have := mul_le_mul_of_nonneg_left m1 (hμ 1)
      have e : μ 0 * yb + μ 1 * (yb + zb) = yb + qb * zb := by
        rw [← h1]; linear_combination yb * h01
      linarith
    have kc : μ 2 * m 2 + μ 3 * m 3 ≤ ya + qc * za := by
      have := mul_le_mul_of_nonneg_left m2 (hμ 2)
      have := mul_le_mul_of_nonneg_left m3 (hμ 3)
      have e : μ 2 * yc + μ 3 * (yc + zc) = yc + qc * zc := by
        rw [← h3]; linear_combination yc * h23
      linarith
    have := mul_le_mul_of_nonneg_left kb (hlam 0)
    have := mul_le_mul_of_nonneg_left kc (hlam 1)
    have e : lam 0 * (ya + qb * za) + lam 1 * (ya + qc * za) = ya + qa * za := by
      rw [hqa]; linear_combination ya * hl
    linarith
  · intro hle
    set Vb := μ 0 * m 0 + μ 1 * m 1 with hVb
    set Vc := μ 2 * m 2 + μ 3 * m 3 with hVc
    have hd : qb - qc ≠ 0 := sub_ne_zero.mpr hbc
    set za := (Vb - Vc) / (qb - qc) with hza
    set ya := Vb - qb * za with hya
    refine ⟨ya, za, m 0, m 1 - m 0, m 2, m 3 - m 2, ?_, ?_, ?_, le_rfl, by linarith, le_rfl,
      by linarith⟩
    · have e1 : ya + qb * za = Vb := by rw [hya]; ring
      have e2 : ya + qc * za = Vc := by
        rw [hya, hza]; field_simp; ring
      have e : ya + qa * za = lam 0 * Vb + lam 1 * Vc := by
        linear_combination lam 0 * e1 + lam 1 * e2 + za * hqa - ya * hl
      linarith
    · have e1 : ya + qb * za = Vb := by rw [hya]; ring
      have e3 : m 0 + qb * (m 1 - m 0) = Vb := by
        rw [hVb, ← h1]; linear_combination (-(m 0)) * h01
      rw [e1]; linarith
    · have e2 : ya + qc * za = Vc := by rw [hya, hza]; field_simp; ring
      have e3 : m 2 + qc * (m 3 - m 2) = Vc := by
        rw [hVc, ← h3]; linear_combination (-(m 2)) * h23
      rw [e2]; linarith

/-- **Footnote 21** (MWG, p. 708). The martingale property of asset prices: at node `b` the price
`q_b` of asset 2 is the conditional expectation of its final returns `(0, 1)` under the
Arrow-Debreu prices (normalized on the event `{1, 2}`), and similarly at `c`; at `a`, `q_a` is the
expectation of the final returns under `p` (which sums to one). -/
theorem footnote_19_21 {qa qb qc : ℝ} {μ : Fin 4 → ℝ} {lam : Fin 2 → ℝ}
    (hlb : 0 < lam 0) (hlc : 0 < lam 1) (h01 : μ 0 + μ 1 = 1) (h1 : μ 1 = qb)
    (h23 : μ 2 + μ 3 = 1) (h3 : μ 3 = qc) (hl : lam 0 + lam 1 = 1)
    (hqa : qa = lam 0 * qb + lam 1 * qc) :
    let p := adPrices19E7 μ lam
    qb = (p 0 * 0 + p 1 * 1) / (p 0 + p 1) ∧ qc = (p 2 * 0 + p 3 * 1) / (p 2 + p 3) ∧
      ∑ s, p s = 1 ∧ qa = ∑ s, p s * ![0, 1, 0, 1] s := by
  intro p
  have e0 : p 0 = lam 0 * μ 0 := rfl
  have e1 : p 1 = lam 0 * μ 1 := rfl
  have e2 : p 2 = lam 1 * μ 2 := rfl
  have e3 : p 3 = lam 1 * μ 3 := rfl
  have v0 : (![0, 1, 0, 1] : Fin 4 → ℝ) 0 = 0 := rfl
  have v1 : (![0, 1, 0, 1] : Fin 4 → ℝ) 1 = 1 := rfl
  have v2 : (![0, 1, 0, 1] : Fin 4 → ℝ) 2 = 0 := rfl
  have v3 : (![0, 1, 0, 1] : Fin 4 → ℝ) 3 = 1 := rfl
  rw [Fin.sum_univ_four, Fin.sum_univ_four, e0, e1, e2, e3, v0, v1, v2, v3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_zero, mul_one, zero_add, ← mul_add, h01, mul_one, ← h1]; field_simp
  · rw [mul_zero, mul_one, zero_add, ← mul_add, h23, mul_one, ← h3]; field_simp
  · linear_combination lam 0 * h01 + lam 1 * h23 + hl
  · rw [hqa, h1, h3]; ring

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Incomplete markets (MWG Section 19.F, pp. 709-713, Exercises 19.F.1-19.F.2)

* **Example 19.F.1 (sunspots)**: with common probabilities `π ≫ 0`, state-uniform strictly concave
  Bernoulli utilities and uniform endowments, Pareto optimal allocations are state independent
  (`example_19_F_1_po`); the printed argument needs `π_s > 0` (`example_19_F_1_needs_pos`,
  correction 7). Hence complete markets give sunspot-free equilibria (`example_19_F_1_complete`).
  With no assets (`K = 0`) a Radner equilibrium is exactly a choice of spot Walrasian equilibrium
  in each state (`radner_noAssets_iff`); selecting different spot equilibria gives a sunspot
  equilibrium (`sunspot_radnerEqm`), which is Pareto inefficient (`sunspot_not_po`). The spot
  economy with Leontief consumers has a continuum of equilibria (`leontief_spot_eqm`).
* **Exercise 19.F.1**: a sunspot-free Radner equilibrium exists for every asset structure, given a
  spot Walrasian equilibrium (`exercise_19_F_1`), and it is Pareto optimal when the spot
  equilibrium allocation is (`exercise_19_F_1_po`).
* **Definition 19.F.1** (constrained Pareto optimality, `L = 1`), footnote 26 and
  **Proposition 19.F.1**: Radner equilibria with one good are constrained Pareto optimal
  (`proposition_19_F_1`), assuming strongly monotone utilities and nonnegative nonzero returns.
* **Example 19.F.2 (Hart)**: Pareto-ranked Radner equilibria (`example_19_F_2`).
* **Exercise 19.F.2**: continuity, concavity and monotonicity of the induced utility `U*ᵢ`.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ} {ι : Type*} [Fintype ι]

/-! ## Example 19.F.1: sunspots -/

/-- **Example 19.F.1** (MWG, pp. 709-710). A sunspot set: common probabilities `π ≫ 0`, a state
uniform strictly concave Bernoulli utility `uᵢ` and endowments `ω_{si} = ωᵢ`. Every Pareto
optimal allocation is state independent. -/
theorem example_19_F_1_po {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L}
    (hpo : IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x) :
    ∀ i s s', x i s = x i s' :=
  po_stateIndependent hπ hπ1 hu (fun _ _ => rfl) hpo

/-- **Example 19.F.1** (correction 7). The argument needs `π_s > 0`: with `π = (1, 0)`, one
consumer, one good, `u = √·` and `ω = (1, 1)`, the allocation `x = (1, 0)` is Pareto optimal but
not state independent. -/
theorem example_19_F_1_needs_pos :
    IsParetoOptimalU (ι := Fin 1) (fun _ => expUtil ![1, 0] fun _ (v : Fin 1 → ℝ) => √(v 0))
        (fun _ _ _ => 1) (fun _ => ![fun _ => 1, fun _ => 0]) ∧
      (fun (_ : Fin 1) => (![fun _ => 1, fun _ => 0] : CVec 2 1)) 0 0 ≠
        (fun (_ : Fin 1) => (![fun _ => 1, fun _ => 0] : CVec 2 1)) 0 1 := by
  refine ⟨⟨⟨fun _ s l => ?_, fun s l => ?_⟩, ?_⟩, ?_⟩
  · fin_cases s <;> simp
  · fin_cases s <;> simp
  · rintro ⟨x', ⟨hx', hf⟩, -, k, hk⟩
    fin_cases k
    have h1 : x' 0 0 0 ≤ 1 := by simpa using hf 0 0
    have hk' : 1 < √(x' 0 0 0) := by simpa [expUtil, Fin.sum_univ_two] using hk
    have : √(x' 0 0 0) ≤ 1 := by rw [Real.sqrt_le_one]; exact h1
    linarith
  · intro h
    have := congrFun h 0
    simp at this

/-- **Example 19.F.1** (MWG, p. 710). With complete markets (an Arrow-Debreu equilibrium, strongly
monotone utilities) the equilibria in a sunspot set are sunspot free. -/
theorem example_19_F_1_complete [NeZero S] [NeZero L] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) {u : ι → (Fin L → ℝ) → ℝ}
    (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i)) (hm : ∀ i, StronglyMonotoneL (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x p) :
    ∀ i s s', x i s = x i s' :=
  example_19_F_1_po hπ hπ1 hu
    (adEqmU_paretoOptimal (fun i => expUtil_stronglyMonotone hπ fun _ => hm i) h)

/-- A spot Walrasian equilibrium (with the clearing condition `∑ yᵢ ≤ ∑ ωᵢ` of Definition 19.E.2)
of the exchange economy `{(uᵢ, ωᵢ)}` with `L` goods, at prices `p`. -/
def IsSpotEqm (u : ι → (Fin L → ℝ) → ℝ) (ω₀ : ι → Fin L → ℝ) (p : Fin L → ℝ)
    (y : ι → Fin L → ℝ) : Prop :=
  (∀ i, ((∀ l, 0 ≤ y i l) ∧ p ⬝ᵥ y i ≤ p ⬝ᵥ ω₀ i) ∧
    ∀ y' : Fin L → ℝ, (∀ l, 0 ≤ y' l) → p ⬝ᵥ y' ≤ p ⬝ᵥ ω₀ i → u i y' ≤ u i (y i)) ∧
    ∑ i, y i ≤ ∑ i, ω₀ i

/-- **Example 19.F.1** (MWG, p. 710). With no assets (`K = 0`), `(p₁, …, p_S)` and `x` form a Radner
equilibrium if and only if every `p_s` is a Walrasian equilibrium price vector, with allocation
`(x_{s1}, …, x_{sI})`, of the spot economy `{(uᵢ, ωᵢ)}` (probabilities `π ≫ 0`). -/
theorem radner_noAssets_iff (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : ι → (Fin L → ℝ) → ℝ} {ω₀ : ι → Fin L → ℝ} {p : CVec S L} {x : ι → CVec S L}
    {q : Fin 0 → ℝ} {z : ι → Fin 0 → ℝ} (R : Matrix (Fin S) (Fin 0) ℝ) :
    IsRadnerEqm g R (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) q p x z ↔
      ∀ s, IsSpotEqm u ω₀ (p s) (fun i => x i s) := by
  classical
  have hR : ∀ w : Fin 0 → ℝ, R *ᵥ w = 0 := fun w => by funext s; simp [mulVec, dotProduct]
  have hfeas : ∀ i x' (z' : Fin 0 → ℝ), radnerFeasible g R q p (fun _ => ω₀ i) x' z' ↔
      NonnegC x' ∧ ∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ ω₀ i := by
    intro i x' z'
    simp [radnerFeasible, hR, dotProduct]
  constructor
  · intro h s
    refine ⟨fun i => ⟨⟨fun l => (h.1 i).1.1 s l, ((hfeas i _ _).mp (h.1 i).1).2 s⟩,
      fun y' hy' hb => ?_⟩, fun l => ?_⟩
    · have hf : radnerFeasible g R q p (fun _ => ω₀ i) (Function.update (x i) s y') (z i) := by
        rw [hfeas]
        refine ⟨fun s' l => ?_, fun s' => ?_⟩
        · by_cases hs : s' = s
          · subst hs; simp [hy' l]
          · rw [Function.update_of_ne hs]; exact (h.1 i).1.1 s' l
        · by_cases hs : s' = s
          · subst hs; simpa using hb
          · rw [Function.update_of_ne hs]; exact ((hfeas i _ _).mp (h.1 i).1).2 s'
      have := (h.1 i).2 _ _ hf
      simp only [expUtil] at this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s), Function.update_self] at this
      have e : ∑ t ∈ Finset.univ.erase s, π t * u i (Function.update (x i) s y' t) =
          ∑ t ∈ Finset.univ.erase s, π t * u i (x i t) :=
        Finset.sum_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      rw [e] at this
      exact le_of_mul_le_mul_left (by linarith) (hπ s)
    · have := h.2.2 s l
      simpa [Finset.sum_apply] using this
  · intro h
    refine ⟨fun i => ⟨(hfeas i _ _).mpr ⟨fun s l => ((h s).1 i).1.1 l,
      fun s => ((h s).1 i).1.2⟩, fun x' z' hf => ?_⟩, fun k => Fin.elim0 k, fun s l => ?_⟩
    · obtain ⟨hx', hb⟩ := (hfeas i _ _).mp hf
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (((h s).1 i).2 (x' s) (hx' s) (hb s)) (hπ s).le
    · have := (h s).2 l
      simpa [Finset.sum_apply] using this

/-- **Example 19.F.1** (MWG, p. 710). Selecting a spot equilibrium in every state (possibly a
different one in different states) gives a Radner equilibrium without assets: a sunspot
equilibrium when the selected allocations differ. -/
theorem sunspot_radnerEqm (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : ι → (Fin L → ℝ) → ℝ} {ω₀ : ι → Fin L → ℝ} {P : Fin S → Fin L → ℝ}
    {Y : Fin S → ι → Fin L → ℝ} (h : ∀ s, IsSpotEqm u ω₀ (P s) (Y s)) :
    IsRadnerEqm g (0 : Matrix (Fin S) (Fin 0) ℝ) (fun i => expUtil π fun _ => u i)
      (fun i _ => ω₀ i) Fin.elim0 P (fun i s => Y s i) fun _ => Fin.elim0 :=
  (radner_noAssets_iff g hπ _).mpr h

/-- **Example 19.F.1** (MWG, p. 710). A sunspot equilibrium allocation (state dependent) is not
Pareto optimal (common `π ≫ 0`, strictly concave `uᵢ`, uniform endowments). -/
theorem sunspot_not_po {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L} {i : ι} {s s' : Fin S} (hne : x i s ≠ x i s') :
    ¬ IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x :=
  fun hpo => hne (example_19_F_1_po hπ hπ1 hu hpo i s s')

/-- A spot economy with a continuum of equilibria (the possibility invoked in Example 19.F.1):
two consumers with `u(y) = min(y₁, y₂)`, endowments `(1, 0)` and `(0, 1)`; for every `a ∈ [0, 1]`
the prices `(a, 1 - a)` with allocation `((a, a), (1 - a, 1 - a))` are an equilibrium. -/
theorem leontief_spot_eqm {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsSpotEqm (fun (_ : Fin 2) (y : Fin 2 → ℝ) => min (y 0) (y 1)) ![![1, 0], ![0, 1]] ![a, 1 - a]
      ![![a, a], ![1 - a, 1 - a]] := by
  refine ⟨fun i => ⟨⟨fun l => ?_, ?_⟩, fun y' hy' hb => ?_⟩, fun l => ?_⟩
  · fin_cases i <;> fin_cases l <;> simp <;> linarith
  · fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> nlinarith
  · fin_cases i
    · have hb' : a * y' 0 + (1 - a) * y' 1 ≤ a := by
        simpa [dotProduct, Fin.sum_univ_two] using hb
      change min (y' 0) (y' 1) ≤ min a a
      rw [min_self]
      rcases le_total (y' 0) (y' 1) with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    · have hb' : a * y' 0 + (1 - a) * y' 1 ≤ 1 - a := by
        simpa [dotProduct, Fin.sum_univ_two] using hb
      change min (y' 0) (y' 1) ≤ min (1 - a) (1 - a)
      rw [min_self]
      rcases le_total (y' 0) (y' 1) with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
  · fin_cases l <;> simp [Fin.sum_univ_two]

/-! ## Exercise 19.F.1 -/

/-- **Exercise 19.F.1** (MWG, p. 728). In the sunspot model (common `π ≥ 0` summing to one,
state-uniform concave `uᵢ`, uniform endowments), for any asset structure `R` and any spot Walrasian
equilibrium `(p̂, ŷ)`, there is a sunspot-free Radner equilibrium: spot prices `p̂` in every state,
consumption `ŷᵢ` in every state, no trade in assets, and asset prices
`q_k = p̂_g ∑_s π_s r_{sk}` (the market "does not pay attention" to the sunspot). -/
theorem exercise_19_F_1 (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hc : ∀ i, ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {phat : Fin L → ℝ} {yhat : ι → Fin L → ℝ}
    (h : IsSpotEqm u ω₀ phat yhat) (R : Matrix (Fin S) (Fin K) ℝ) :
    IsRadnerEqm g R (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i)
      (fun k => ∑ s, (phat g * π s) * R s k) (fun _ => phat) (fun i _ => yhat i) (fun _ => 0) := by
  have hdot := dot_eq_of_pricing (R := R) (ν := fun s => phat g * π s)
    (q := fun k => ∑ s, (phat g * π s) * R s k) (fun k => rfl)
  refine ⟨fun i => ⟨⟨fun _ l => ((h.1 i).1.1 l), by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩,
    fun k => by simp, fun s l => ?_⟩
  · simpa using (h.1 i).1.2
  · obtain ⟨hx', hqz, hs⟩ := hf
    set xbar := ∑ s, π s • x' s with hxbar
    have hxbar0 : ∀ l, 0 ≤ xbar l := fun l => by
      simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' s l)
    have hbud : phat ⬝ᵥ xbar ≤ phat ⬝ᵥ ω₀ i := by
      have h1 : phat ⬝ᵥ xbar = ∑ s, π s * (phat ⬝ᵥ x' s) := by
        simp [hxbar, dotProduct_sum, dotProduct_smul]
      have h2 : ∀ s, π s * (phat ⬝ᵥ x' s) ≤ π s * (phat ⬝ᵥ ω₀ i) + π s * (phat g * (R *ᵥ z') s) :=
        fun s => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hs s) (hπ s)
      have h3 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hπ1, one_mul] at h3
      rw [hdot] at hqz
      have h4 : ∑ s, π s * (phat g * (R *ᵥ z') s) = (fun s => phat g * π s) ⬝ᵥ (R *ᵥ z') := by
        simp only [dotProduct]; exact Finset.sum_congr rfl fun s _ => by ring
      linarith
    have hjen := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := x') (fun s _ => hπ s) hπ1
      (fun s _ => hx' s)
    have hconst : expUtil π (fun _ => u i) (fun _ => yhat i) = u i (yhat i) := by
      simp [expUtil, ← Finset.sum_mul, hπ1]
    simp only [smul_eq_mul] at hjen
    change expUtil π (fun _ => u i) x' ≤ expUtil π (fun _ => u i) (fun _ => yhat i)
    rw [hconst]
    exact hjen.trans ((h.1 i).2 xbar hxbar0 hbud)
  · have := h.2 l
    simpa [Finset.sum_apply] using this

/-- **Exercise 19.F.1** (MWG, p. 710): the sunspot-free equilibrium is Pareto optimal when the spot
equilibrium allocation is Pareto optimal in the spot economy (as it is under local nonsatiation,
by the first welfare theorem). -/
theorem exercise_19_F_1_po {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hc : ∀ i, ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ yhat : ι → Fin L → ℝ}
    (hpo : IsParetoOptimalU (S := 1) (fun i v => u i (v 0)) (fun i _ => ω₀ i)
      (fun i _ => yhat i)) :
    IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i)
      (fun i _ => yhat i) := by
  obtain ⟨⟨hy, hf⟩, hno⟩ := hpo
  refine ⟨⟨fun i s l => hy i 0 l, fun s l => by simpa using hf 0 l⟩, ?_⟩
  rintro ⟨x', ⟨hx', hf'⟩, hge, k, hk⟩
  set xbar : ι → Fin L → ℝ := fun i => ∑ s, π s • x' i s with hxbar
  have hjen : ∀ i, expUtil π (fun _ => u i) (x' i) ≤ u i (xbar i) := fun i => by
    have := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := x' i) (fun s _ => hπ s) hπ1
      (fun s _ => hx' i s)
    simpa [expUtil, smul_eq_mul] using this
  have hconst : ∀ i, expUtil π (fun _ => u i) (fun _ => yhat i) = u i (yhat i) := fun i => by
    simp [expUtil, ← Finset.sum_mul, hπ1]
  refine hno ⟨fun i _ => xbar i, ⟨fun i _ l => ?_, fun _ l => ?_⟩, fun i => ?_, k, ?_⟩
  · simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' i s l)
  · have : ∀ s, ∑ i, x' i s l ≤ ∑ i, ω₀ i l := fun s => by
      have := hf' s l; simpa [Finset.sum_apply] using this
    simp only [Finset.sum_apply, hxbar, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ s, ∑ i, π s * x' i s l = ∑ s, π s * ∑ i, x' i s l := by
          simp [Finset.mul_sum]
      _ ≤ ∑ s, π s * ∑ i, ω₀ i l :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (this s) (hπ s)
      _ = ∑ i, ω₀ i l := by rw [← Finset.sum_mul, hπ1, one_mul]
  · have := hge i; dsimp only at this ⊢; rw [hconst] at this; exact this.trans (hjen i)
  · have := hk; dsimp only at this ⊢; rw [hconst] at this; exact this.trans_le (hjen k)

/-! ## Constrained Pareto optimality: Definition 19.F.1 and Proposition 19.F.1 -/

/-- **p. 711**. With one good (`L = 1`) the portfolio `zᵢ` determines consumption
`x_{si} = ∑_k z_{ki} r_{sk} + ω_{si}`; the induced utility is `U*ᵢ(zᵢ) = Uᵢ(ωᵢ + R zᵢ)`. -/
def inducedConsumption (R : Matrix (Fin S) (Fin K) ℝ) (ω : CVec S 1) (z : Fin K → ℝ) : CVec S 1 :=
  fun s _ => ω s 0 + (R *ᵥ z) s

/-- **Definition 19.F.1** (MWG, p. 711). The asset allocation `(z₁, …, z_I)` is constrained Pareto
optimal if it is feasible (`∑ᵢ zᵢ ≤ 0`, with nonnegative induced consumption) and no feasible asset
allocation gives every consumer at least the induced utility `U*ᵢ` and some consumer more. -/
def IsConstrainedPO (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S 1 → ℝ) (ω : ι → CVec S 1)
    (z : ι → Fin K → ℝ) : Prop :=
  ((∀ i, NonnegC (inducedConsumption R (ω i) (z i))) ∧ ∀ k, ∑ i, z i k ≤ 0) ∧
    ¬ ∃ z' : ι → Fin K → ℝ, ((∀ i, NonnegC (inducedConsumption R (ω i) (z' i))) ∧
      ∀ k, ∑ i, z' i k ≤ 0) ∧
      (∀ i, U i (inducedConsumption R (ω i) (z i)) ≤ U i (inducedConsumption R (ω i) (z' i))) ∧
      ∃ i, U i (inducedConsumption R (ω i) (z i)) < U i (inducedConsumption R (ω i) (z' i))

/-- **Footnote 26** (MWG, p. 711). With one good and strongly monotone utility, at a Radner optimum
consumption is the portfolio-induced consumption: `x*ᵢ = ωᵢ + R z*ᵢ` (spot price `1`). -/
theorem radner_consumption_induced {R : Matrix (Fin S) (Fin K) ℝ} {U : ι → CVec S 1 → ℝ}
    {ω x : ι → CVec S 1} {q : Fin K → ℝ} {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) (i : ι) (hU : StronglyMonotoneC (U i)) :
    x i = inducedConsumption R (ω i) (z i) := by
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  have hle : x i ≤ inducedConsumption R (ω i) (z i) := fun s l => by
    rw [Subsingleton.elim l 0]; simpa [inducedConsumption, dotProduct] using hsp s
  by_contra hne
  have hf : radnerFeasible 0 R q (fun _ _ => 1) (ω i) (inducedConsumption R (ω i) (z i)) (z i) :=
    ⟨fun s l => (hx s l).trans (hle s l), hqz, fun s => by
      simp [inducedConsumption, dotProduct]⟩
  linarith [hopt _ _ hf, hU _ _ hx hle hne]

/-- **Proposition 19.F.1** (MWG, p. 711). Two periods and one consumption good: with strongly
monotone utilities and nonnegative nonzero returns, every Radner equilibrium asset allocation is
constrained Pareto optimal: no redistribution of assets in the first period leaves every consumer
as well off and someone strictly better off. (The book's proof applies the first welfare
theorem to the economy with `K` commodities; here it is carried out directly.) -/
theorem proposition_19_F_1 [Nonempty ι] {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S 1 → ℝ} (hU : ∀ i, StronglyMonotoneC (U i))
    {ω x : ι → CVec S 1} {q : Fin K → ℝ} {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) : IsConstrainedPO R U ω z := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hqpos := (radner_arbitrageFree 0 h i₀ (hU i₀)).pos hRn
  have hind := fun i => radner_consumption_induced h i (hU i)
  refine ⟨⟨fun i => hind i ▸ (h.1 i).1.1, h.2.1⟩, ?_⟩
  rintro ⟨z', ⟨hx', hsum⟩, hge, k, hk⟩
  have hfeas : ∀ i w, NonnegC (inducedConsumption R (ω i) w) → q ⬝ᵥ w ≤ 0 →
      radnerFeasible 0 R q (fun _ _ => 1) (ω i) (inducedConsumption R (ω i) w) w :=
    fun i w hw hq => ⟨hw, hq, fun s => by simp [inducedConsumption, dotProduct]⟩
  -- strictly better consumers spend more than their (zero) budget
  have hstrict : 0 < q ⬝ᵥ z' k := by
    by_contra hle
    push Not at hle
    have := (h.1 k).2 _ _ (hfeas k (z' k) (hx' k) hle)
    rw [hind k] at this
    linarith
  -- weakly better consumers spend at least zero
  have hweak : ∀ i, 0 ≤ q ⬝ᵥ z' i := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨k₀⟩ : Nonempty (Fin K) := by
      by_contra hK
      rw [not_nonempty_iff] at hK
      simp [dotProduct] at hlt
    set ε := -(q ⬝ᵥ z' i) / q k₀ with hε
    have hεpos : 0 < ε := div_pos (by linarith) (hqpos k₀)
    set w := z' i + ε • Pi.single k₀ 1 with hw
    have hle : inducedConsumption R (ω i) (z' i) ≤ inducedConsumption R (ω i) w := by
      intro s l
      simp only [inducedConsumption, hw, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
        mulVec_single, smul_eq_mul]
      nlinarith [hRn.1 s k₀]
    have hne : inducedConsumption R (ω i) (z' i) ≠ inducedConsumption R (ω i) w := by
      intro h0
      obtain ⟨s, hs⟩ := hRn.2 k₀
      have := congrFun (congrFun h0 s) 0
      simp only [inducedConsumption, hw, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
        mulVec_single, smul_eq_mul] at this
      have : ε * R s k₀ = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact hεpos.ne' h'
      · exact hs h'
    have hqw : q ⬝ᵥ w ≤ 0 := by
      rw [hw, dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hε]
      field_simp [(hqpos k₀).ne']
      linarith
    have h1 := (h.1 i).2 _ _ (hfeas i w (fun s l => (hx' i s l).trans (hle s l)) hqw)
    have h2 := hU i _ _ (hx' i) hle hne
    rw [hind i] at h1
    linarith [hge i]
  have hpos : 0 < q ⬝ᵥ ∑ i, z' i := by
    rw [dotProduct_sum]
    exact Finset.sum_pos' (fun i _ => hweak i) ⟨k, Finset.mem_univ _, hstrict⟩
  have hnp : q ⬝ᵥ ∑ i, z' i ≤ 0 := Finset.sum_nonpos fun k' _ =>
    mul_nonpos_of_nonneg_of_nonpos (hqpos k').le (by simpa [Finset.sum_apply] using hsum k')
  linarith

/-! ## Example 19.F.2 (Hart) -/

/-- **Example 19.F.2** (MWG, p. 712). Two spot equilibria with prices `p'`, `p''` and spot utilities
`vᵢ(p')`, `vᵢ(p'')`. (1) If the `p''` allocation is Pareto optimal in the spot market (the
`p'` allocation does not Pareto dominate it) and `v₁(p') > v₁(p'')`, then `v₂(p') < v₂(p'')`.
(2) With no assets, `(p', p'')` and `(p'', p')` are
Radner equilibrium price systems for any probabilities (`radner_noAssets_iff`); if `π₁₁ > 1/2` and
`π₂₂ > 1/2`, the first Pareto dominates the second. -/
theorem example_19_F_2 {v1' v1'' v2' v2'' : ℝ}
    (hpo'' : ¬ (v1'' ≤ v1' ∧ v2'' ≤ v2' ∧ (v1'' < v1' ∨ v2'' < v2'))) (h1 : v1'' < v1')
    {π11 π21 π12 π22 : ℝ} (hπ1 : π11 + π21 = 1) (hπ2 : π12 + π22 = 1) (h11 : 1 / 2 < π11)
    (h22 : 1 / 2 < π22) :
    v2' < v2'' ∧ π11 * v1'' + π21 * v1' < π11 * v1' + π21 * v1'' ∧
      π12 * v2'' + π22 * v2' < π12 * v2' + π22 * v2'' := by
  have hv2 : v2' < v2'' := by
    by_contra hle
    push Not at hle
    exact hpo'' ⟨h1.le, hle, Or.inl h1⟩
  refine ⟨hv2, by nlinarith, by nlinarith⟩

/-! ## Exercise 19.F.2 -/

/-- **Exercise 19.F.2** (MWG, p. 728). Sufficient conditions on `U*ᵢ(z) = Uᵢ(ωᵢ + Rz)`: if `Uᵢ` is
continuous (concave) on `ℝ^S_+`, then `U*ᵢ` is continuous (concave) on the convex set of portfolios
with nonnegative induced consumption. -/
theorem exercise_19_F_2_concave {R : Matrix (Fin S) (Fin K) ℝ} {ω : CVec S 1}
    {U : CVec S 1 → ℝ} (hc : ConcaveOn ℝ {x | NonnegC x} U) :
    ConcaveOn ℝ {z | NonnegC (inducedConsumption R ω z)}
      (fun z => U (inducedConsumption R ω z)) := by
  have hlin : ∀ (a b : ℝ) (z z' : Fin K → ℝ), a + b = 1 →
      inducedConsumption R ω (a • z + b • z') =
        a • inducedConsumption R ω z + b • inducedConsumption R ω z' := by
    intro a b z z' hab
    funext s l
    simp only [inducedConsumption, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have : ω s 0 = a * ω s 0 + b * ω s 0 := by rw [← add_mul, hab, one_mul]
    linarith
  refine ⟨fun z hz z' hz' a b ha hb hab => ?_, fun z hz z' hz' a b ha hb hab => ?_⟩
  · change NonnegC (inducedConsumption R ω (a • z + b • z'))
    rw [hlin a b z z' hab]
    intro s l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hz s l)) (mul_nonneg hb (hz' s l))
  · simp only [smul_eq_mul]
    rw [hlin a b z z' hab]
    exact hc.2 hz hz' ha hb hab

/-- **Exercise 19.F.2** (MWG, p. 728), continuity. -/
theorem exercise_19_F_2_continuous {R : Matrix (Fin S) (Fin K) ℝ} {ω : CVec S 1}
    {U : CVec S 1 → ℝ} (hU : Continuous U) :
    Continuous fun z => U (inducedConsumption R ω z) := by
  refine hU.comp (continuous_pi fun s => continuous_pi fun _ => ?_)
  exact continuous_const.add ((continuous_apply s).comp
    (continuous_const.matrix_mulVec continuous_id))

/-- **Exercise 19.F.2** (MWG, p. 728). If all returns are strictly positive and `Uᵢ` is strongly
monotone, then `U*ᵢ` is strictly increasing: `z ≤ z'`, `z ≠ z'` imply `U*ᵢ(z) < U*ᵢ(z')` (for
`z` with nonnegative induced consumption). -/
theorem exercise_19_F_2_increasing {R : Matrix (Fin S) (Fin K) ℝ} (hR : ∀ s k, 0 < R s k)
    [NeZero S] {ω : CVec S 1} {U : CVec S 1 → ℝ} (hU : StronglyMonotoneC U) {z z' : Fin K → ℝ}
    (hz : NonnegC (inducedConsumption R ω z)) (hle : z ≤ z') (hne : z ≠ z') :
    U (inducedConsumption R ω z) < U (inducedConsumption R ω z') := by
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ z' k := by
    by_contra h; push Not at h; exact hne (funext h)
  have hlt : z k < z' k := lt_of_le_of_ne (hle k) hk
  refine hU _ _ hz (fun s l => ?_) (fun h0 => ?_)
  · simp only [inducedConsumption, mulVec, dotProduct]
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hle k) (hR s k).le
    linarith
  · have h1 := congrFun (congrFun h0 ⟨0, NeZero.pos S⟩) 0
    simp only [inducedConsumption, mulVec, dotProduct, add_right_inj] at h1
    have h2 : ∑ k, R ⟨0, NeZero.pos S⟩ k * z k < ∑ k, R ⟨0, NeZero.pos S⟩ k * z' k :=
      Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hR _ k).le)
        ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hR _ k)⟩
    linarith

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Firm behavior under uncertainty (MWG Section 19.G, pp. 713-716, Exercises 19.G.1-19.G.4)

A firm chooses a return vector `a ∈ A ⊆ ℝ^S` (in units of the numeraire good `g`); consumer `i`
owns the share `θᵢ ≥ 0`.

* **Definition 19.G.1**: `A` is spanned by `R` (`IsSpanned`). The market value of a spanned plan
  `a = Rα` is `v(a, q) = q·α`; with arbitrage prices it does not depend on the representation
  (`marketValue_wellDefined`).
* **(19.G.1)** and **Exercise 19.G.1**: if the firm is introduced as a new asset priced at its
  arbitrage value, every consumption plan affordable with trade in its shares is affordable
  without purchasing shares, and the budget set is (19.G.1) (`exercise_19_G_1`).
* **Unanimity (p. 715)**: if `v(a, q) ≥ v(a', q)` then `B_{a'i} ⊆ B_{ai}` for every owner, so all
  owners prefer the plan of higher market value (`unanimity`).
* **Exercise 19.G.2**: the printed request (an example where one consumer becomes significantly
  worse off) cannot be met: with `L = 1`, a single initial asset, strongly monotone utilities and
  `εa ≥ 0`, at any Radner equilibrium after the firm is introduced every consumer is at least as
  well off as at any equilibrium before (`exercise_19_G_2_no_one_worse_off`, correction 9).
* **Exercise 19.G.3**: with a spanned firm, trading its shares at `t = 0` or adding `θᵢ a` to the
  endowments gives the same budget sets (`exercise_19_G_3`).
* **Exercise 19.G.4**: without spanning, owners need not be unanimous (`exercise_19_G_4`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- **Definition 19.G.1** (MWG, p. 714). A set `A ⊆ ℝ^S` is spanned by the asset structure `R` if
every `a ∈ A` is in the range of `R`. -/
def IsSpanned (R : Matrix (Fin S) (Fin K) ℝ) (A : Set (Fin S → ℝ)) : Prop :=
  ∀ a ∈ A, ∃ α, R *ᵥ α = a

/-- **p. 714**. With arbitrage prices `q = μ·R`, the market value `v(a, q) = ∑_k α_k q_k` of a
spanned plan `a = Rα` does not depend on the representation: it is `μ·a`. -/
theorem marketValue_wellDefined {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ}
    {q : Fin K → ℝ} (hq : ∀ k, q k = ∑ s, μ s * R s k) {a : Fin S → ℝ} {α : Fin K → ℝ}
    (hα : R *ᵥ α = a) : q ⬝ᵥ α = μ ⬝ᵥ a := by
  rw [dot_eq_of_pricing hq, hα]

/-- **(19.G.1)** (MWG, p. 715). The budget set of consumer `i` with share `θᵢ` when the firm
chooses `a` of market value `v = v(a, q)`: some portfolio `z` has `q·z ≤ θᵢ v` and
`p_s·(x_s - ω_s) ≤ p_{gs} ∑_k r_{sk} z_k` in every state. -/
def firmBudget (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (θ v : ℝ) : Set (CVec S L) :=
  {x | NonnegC x ∧ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ θ * v ∧
    ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s}

/-- **p. 715**. Unanimity: if `v(a, q) ≥ v(a', q)`, every owner (`θᵢ ≥ 0`) has
`B_{a'i} ⊆ B_{ai}`. -/
theorem unanimity (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    {θ v v' : ℝ} (hθ : 0 ≤ θ) (hv : v' ≤ v) :
    firmBudget g R q p ω θ v' ⊆ firmBudget g R q p ω θ v := by
  rintro x ⟨hx, z, hq, hs⟩
  exact ⟨hx, z, hq.trans (mul_le_mul_of_nonneg_left hv hθ), hs⟩

/-- **p. 715**. Hence every owner prefers the plan with the higher market value: the maximal
attainable utility over `B_{ai}` is at least that over `B_{a'i}`. -/
theorem unanimity_utility (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    (p ω : CVec S L) {θ v v' : ℝ} (hθ : 0 ≤ θ) (hv : v' ≤ v) (U : CVec S L → ℝ)
    {x : CVec S L} (hmax : ∀ y ∈ firmBudget g R q p ω θ v, U y ≤ U x) :
    ∀ y ∈ firmBudget g R q p ω θ v', U y ≤ U x :=
  fun y hy => hmax y (unanimity g R q p ω hθ hv hy)

/-- The asset structure with the firm added as asset `K + 1` (return vector `a`). -/
def withFirm (R : Matrix (Fin S) (Fin K) ℝ) (a : Fin S → ℝ) : Matrix (Fin S) (Fin (K + 1)) ℝ :=
  appendAsset R a

/-- **Exercise 19.G.1** (MWG, p. 729). Suppose `a = Rα` is spanned and the firm is added as a new
asset priced at its arbitrage value `v = q·α`, consumer `i` holding `θᵢ` shares initially. The plans
affordable when shares can be traded (holding `y` shares at cost `v(y - θᵢ)`) are exactly the
plans of (19.G.1), which can be reached holding no shares of the firm (`y = 0`), i.e. without
purchasing any. -/
theorem exercise_19_G_1 (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ}
    {p ω : CVec S L} {θ : ℝ} {a : Fin S → ℝ} {α : Fin K → ℝ} (hα : R *ᵥ α = a) (x : CVec S L) :
    (NonnegC x ∧ ∃ (z : Fin K → ℝ) (y : ℝ), q ⬝ᵥ z + (q ⬝ᵥ α) * (y - θ) ≤ 0 ∧
      ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * ((R *ᵥ z) s + y * a s)) ↔
      x ∈ firmBudget g R q p ω θ (q ⬝ᵥ α) := by
  constructor
  · rintro ⟨hx, z, y, hq, hs⟩
    refine ⟨hx, z + y • α, ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_add, mulVec_smul, hα, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hs s
  · rintro ⟨hx, z, hq, hs⟩
    exact ⟨hx, z, 0, by linarith, fun s => by simpa using hs s⟩

/-- **Exercise 19.G.3** (MWG, p. 729). With a spanned plan `a = Rα`, the budget set when the shares
are traded at `t = 0` (19.G.1, value `v = q·α`) equals the budget set when they are not traded and
`θᵢ a` (in good `g`) is added to consumer `i`'s endowment. -/
theorem exercise_19_G_3 (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ}
    {p ω : CVec S L} {θ : ℝ} {a : Fin S → ℝ} {α : Fin K → ℝ} (hα : R *ᵥ α = a) (x : CVec S L) :
    x ∈ firmBudget g R q p ω θ (q ⬝ᵥ α) ↔
      (NonnegC x ∧ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ 0 ∧
        ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (θ * a s) + p s g * (R *ᵥ z) s) := by
  constructor
  · rintro ⟨hx, z, hq, hs⟩
    refine ⟨hx, z - θ • α, ?_, fun s => ?_⟩
    · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_sub, mulVec_smul, hα, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have := hs s; nlinarith
  · rintro ⟨hx, z, hq, hs⟩
    refine ⟨hx, z + θ • α, ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_add, mulVec_smul, hα, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hs s; nlinarith

/-- A Radner budget with initial asset holdings `e`: `q·(z - e) ≤ 0` and
`p_s·x_s ≤ p_s·ω_s + p_{gs}(Rz)_s` (used when the firm's shares are an endowment). -/
def radnerFeasibleE (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (e : Fin K → ℝ) (x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ (z - e) ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s

/-- **Exercise 19.G.2** (MWG, p. 729), correction 9. With `L = 1` and a single asset `r ≥ 0`,
`r ≠ 0`, consider consumer `i` with a strongly monotone utility. (1) At any Radner equilibrium
before the firm is introduced, `Uᵢ(x_old) ≤ Uᵢ(ωᵢ)`. (2) After the firm (returns `εa ≥ 0`, share
`θᵢ ≥ 0`) is introduced as a tradeable asset, any utility-maximizing plan in the new budget gives
`Uᵢ(x_new) ≥ Uᵢ(ωᵢ)`: the consumer can keep his shares and not trade. So no consumer is made
worse off, however `a` and `ε` are chosen, and the requested example does not exist. -/
theorem exercise_19_G_2_no_one_worse_off {ι : Type*} [Fintype ι] {r : Fin S → ℝ}
    (hr : NonnegNonzeroReturns (returnMatrix ![r])) {U : ι → CVec S 1 → ℝ}
    {ω x : ι → CVec S 1} {q : Fin 1 → ℝ} {z : ι → Fin 1 → ℝ}
    (hold : IsRadnerEqm 0 (returnMatrix ![r]) U ω q (fun _ _ => 1) x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) (hω : NonnegC (ω i))
    {a : Fin S → ℝ} {ε θ : ℝ} (hεa : ∀ s, 0 ≤ ε * a s) (hθ : 0 ≤ θ) {q' : Fin 2 → ℝ}
    {xnew : CVec S 1}
    (hnew : ∀ x' z', radnerFeasibleE 0 (withFirm (returnMatrix ![r]) (fun s => ε * a s)) q'
      (fun _ _ => 1) (ω i) (Pi.single (Fin.last 1) θ) x' z' → U i x' ≤ U i xnew) :
    U i (x i) ≤ U i (ω i) ∧ U i (ω i) ≤ U i xnew := by
  classical
  have hmono : ∀ y y' : CVec S 1, NonnegC y → y ≤ y' → U i y ≤ U i y' := fun y y' hy hle => by
    by_cases h : y = y'
    · rw [h]
    · exact (hU y y' hy hle h).le
  refine ⟨?_, ?_⟩
  · -- before: `q > 0`, so the budget forces `z ≤ 0` and `x ≤ ω`
    have hq := (radner_arbitrageFree 0 hold i hU).pos hr 0
    obtain ⟨⟨hx, hqz, hsp⟩, -⟩ := hold.1 i
    have hz : z i 0 ≤ 0 := by
      simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        at hqz
      by_contra h; push Not at h; nlinarith
    refine hmono _ _ hx fun s l => ?_
    rw [Subsingleton.elim l 0]
    have := hsp s
    simp [dotProduct, returnMatrix, mulVec] at this
    nlinarith [hr.1 s 0, (show 0 ≤ r s by simpa [returnMatrix] using hr.1 s 0)]
  · -- after: keeping the shares (`z = θ e_firm`) is affordable
    refine (hmono _ _ hω (fun s l => ?_)).trans (hnew (fun s l => ω i s l + θ * (ε * a s))
      (Pi.single (Fin.last 1) θ) ⟨fun s l => ?_, by simp, fun s => ?_⟩)
    · simp only; nlinarith [hεa s]
    · nlinarith [hω s l, hεa s]
    · have hR : (withFirm (returnMatrix ![r]) (fun s => ε * a s) *ᵥ
          Pi.single (Fin.last 1) θ) s = θ * (ε * a s) := by
        simp only [withFirm, appendAsset, mulVec, dotProduct, Matrix.of_apply,
          Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, Pi.single_eq_same,
          Finset.univ_unique, Finset.sum_singleton]
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last _).ne]
        ring
      rw [hR]
      simp [dotProduct]

/-- **Exercise 19.G.4** (MWG, p. 729). Two consumers, `L = 1`, no assets, a firm with possible plans
`a¹ = (1, 0)` and `a² = (0, 1)`, shares `1/2` each (not traded), added to the endowments `(1, 1)`.
With risk-neutral expected utilities and probabilities `(9/10, 1/10)` for consumer 1 and
`(1/10, 9/10)` for consumer 2, consumer 1 strictly prefers `a¹` and consumer 2 strictly prefers
`a²`: the owners are not unanimous. -/
theorem exercise_19_G_4 :
    let U₁ : (Fin 2 → ℝ) → ℝ := fun c => 9 / 10 * c 0 + 1 / 10 * c 1
    let U₂ : (Fin 2 → ℝ) → ℝ := fun c => 1 / 10 * c 0 + 9 / 10 * c 1
    let endow : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun a s => 1 + 1 / 2 * a s
    U₁ (endow ![0, 1]) < U₁ (endow ![1, 0]) ∧ U₂ (endow ![1, 0]) < U₂ (endow ![0, 1]) := by
  intro U₁ U₂ endow
  simp only [U₁, U₂, endow]
  norm_num

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Imperfect information: signals and the value of information (MWG Section 19.H, pp. 716-719)

States `Fin S` with prior `π ≫ 0`; a signal function `σ : Fin S → β`.

* Measurability of endowments and plans with respect to a signal (p. 716), symmetric information
  (p. 717), posterior probabilities `π_{s'}|σ(s)` and conditional expected utility (p. 717).
* **Definition 19.H.1**: at least as informative / more informative; **footnote 43**: in terms of
  partitions, the finer signal's cells refine the coarser one's (`footnote_19_43`).
* The single-consumer problem: the plan `x^σ` (`IsSignalPlan`), **Proposition 19.H.1**
  (`proposition_19_H_1`) with its two steps (**Exercise 19.H.3**), the state-dependent budgets of
  **Exercise 19.H.2**, and **Exercise 19.H.1(a)-(d)** (ex post optimality under full revelation and
  a counterexample otherwise, interim optimality, and the two conditional comparisons).
* **Example 19.H.1** (Hirshleifer): without information both consumers get `1/√2`; with perfect
  information every spot equilibrium gives them `1` in one state and `0` in the other, so ex ante
  `1/2 < 1/√2` (`example_19_H_1`).
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ} {β α : Type*}

/-! ## Signals -/

/-- **p. 716**. `x` (an endowment or a plan) is measurable with respect to the signal `σ`:
`x_s = x_{s'}` whenever `σ(s) = σ(s')`. -/
def SigmaMeas (σ : Fin S → β) (x : Fin S → α) : Prop := ∀ s s', σ s = σ s' → x s = x s'

/-- **p. 717**. Symmetric information: two states are distinguished by one consumer iff they are
distinguished by every other consumer. -/
def SymmetricInfo {ι : Type*} (σ : ι → Fin S → β) : Prop :=
  ∀ i k s s', σ i s ≠ σ i s' ↔ σ k s ≠ σ k s'

/-- **Definition 19.H.1** (MWG, p. 717). `σ'` is at least as informative as `σ`:
`σ(s) ≠ σ(s')` implies `σ'(s) ≠ σ'(s')`. -/
def AtLeastAsInformative {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) : Prop :=
  ∀ s s', σ s ≠ σ s' → σ' s ≠ σ' s'

/-- **Definition 19.H.1** (MWG, p. 717). `σ'` is more informative than `σ`: at least as informative,
and `σ'(s) ≠ σ'(s')` for some `s, s'` with `σ(s) = σ(s')`. -/
def MoreInformative {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) : Prop :=
  AtLeastAsInformative σ' σ ∧ ∃ s s', σ s = σ s' ∧ σ' s ≠ σ' s'

/-- **Footnote 43** (MWG, p. 717). `σ'` is at least as informative as `σ` iff the information
partition of `σ'` refines that of `σ`: states in the same `σ'`-cell are in the same `σ`-cell. -/
theorem footnote_19_43 {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) :
    AtLeastAsInformative σ' σ ↔ ∀ s s', σ' s = σ' s' → σ s = σ s' :=
  ⟨fun h s s' h' => by by_contra hne; exact h s s' hne h',
    fun h s s' hne h' => hne (h s s' h')⟩

/-- A `σ`-measurable plan is `σ'`-measurable when `σ'` is at least as informative. -/
theorem SigmaMeas.mono {β' : Type*} {σ' : Fin S → β'} {σ : Fin S → β}
    (h : AtLeastAsInformative σ' σ) {x : Fin S → α} (hx : SigmaMeas σ x) : SigmaMeas σ' x :=
  fun s s' h' => hx s s' ((footnote_19_43 σ' σ).mp h s s' h')

variable [DecidableEq β]

/-- The prior mass of the `σ`-cell of `s`. -/
def cellMass (π : Fin S → ℝ) (σ : Fin S → β) (s : Fin S) : ℝ :=
  ∑ t, if σ t = σ s then π t else 0

/-- **p. 717**. The posterior `π_{s'}|σ(s) = π_{s'} / ∑_{s'' : σ(s'') = σ(s)} π_{s''}` for
`σ(s') = σ(s)` and `0` otherwise. -/
noncomputable def posterior (π : Fin S → ℝ) (σ : Fin S → β) (s t : Fin S) : ℝ :=
  if σ t = σ s then π t / cellMass π σ s else 0

/-- **p. 717**. Conditional expected utility `∑_{s'} (π_{s'}|σ(s)) u_{s'}(y)`. -/
noncomputable def condEU (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (s : Fin S)
    (y : α) : ℝ :=
  ∑ t, posterior π σ s t * u t y

theorem cellMass_pos {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (σ : Fin S → β) (s : Fin S) :
    0 < cellMass π σ s :=
  lt_of_lt_of_le (by simpa using hπ s) (Finset.single_le_sum (f := fun t =>
    if σ t = σ s then π t else 0) (fun t _ => by split_ifs <;> simp [(hπ t).le])
    (Finset.mem_univ s))

/-- **p. 717**. Posterior probabilities sum to one. -/
theorem posterior_sum {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (σ : Fin S → β) (s : Fin S) :
    ∑ t, posterior π σ s t = 1 := by
  have hM := cellMass_pos hπ σ s
  unfold posterior
  rw [show (∑ t, if σ t = σ s then π t / cellMass π σ s else 0) =
    (∑ t, if σ t = σ s then π t else 0) / cellMass π σ s by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp]
  exact div_self hM.ne'

theorem cellMass_congr {π : Fin S → ℝ} {σ : Fin S → β} {s s' : Fin S} (h : σ s = σ s') :
    cellMass π σ s = cellMass π σ s' := by
  simp [cellMass, h]

/-- Conditional expected utility is the cell sum divided by the cell mass. -/
theorem condEU_eq (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (s : Fin S) (y : α) :
    condEU π u σ s y = (∑ t, if σ t = σ s then π t * u t y else 0) / cellMass π σ s := by
  unfold condEU posterior
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring

/-- **p. 718**. The plan `x^σ`: it is `σ`-measurable, feasible in every state's budget `B_s`, and
for every state `s`, `x^σ_s` maximizes expected utility conditional on `σ(s)` in `B_s`. -/
def IsSignalPlan (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (B : Fin S → Set α)
    (x : Fin S → α) : Prop :=
  SigmaMeas σ x ∧ (∀ s, x s ∈ B s) ∧ ∀ s, ∀ y ∈ B s, condEU π u σ s y ≤ condEU π u σ s (x s)

/-- The key identity: for a `σ`-measurable `y` and a set `C` of states that is a union of
`σ`-cells, `∑_{s∈C} π_s u_s(y_s) = ∑_{s∈C} (π_s / M_s) ∑_{t ∼ s} π_t u_t(y_s)`. -/
theorem sum_eq_sum_cells {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (u : Fin S → α → ℝ)
    (σ : Fin S → β) (C : Fin S → Prop) [DecidablePred C]
    (hC : ∀ s t, σ s = σ t → (C s ↔ C t)) {y : Fin S → α} (hy : SigmaMeas σ y) :
    (∑ s, if C s then π s * u s (y s) else 0) =
      ∑ s, if C s then π s / cellMass π σ s *
        (∑ t, if σ t = σ s then π t * u t (y s) else 0) else 0 := by
  symm
  calc (∑ s, if C s then π s / cellMass π σ s *
        (∑ t, if σ t = σ s then π t * u t (y s) else 0) else 0)
      = ∑ s, ∑ t, if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with hs
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases ht : σ t = σ s
          · simp [hs, ht, hy t s ht]
          · simp [ht]
        · simp [hs]
    _ = ∑ t, ∑ s, if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0 :=
        Finset.sum_comm
    _ = ∑ t, if C t then π t * u t (y t) else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hM := cellMass_pos hπ σ t
        have e : ∀ s, (if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0)
            = (if C t then (if σ s = σ t then π s else 0) / cellMass π σ t * (π t * u t (y t))
              else 0) := by
          intro s
          by_cases hst : σ t = σ s
          · have hCs := hC s t hst.symm
            rw [cellMass_congr hst.symm]
            by_cases hCt : C t
            · simp [hCs.mpr hCt, hst, hCt]
            · simp [hCt, show ¬ C s from fun h => hCt (hCs.mp h)]
          · have : ¬ σ s = σ t := fun h => hst h.symm
            simp [hst, this]
        simp only [e]
        split_ifs with hCt
        · rw [← Finset.sum_mul, ← Finset.sum_div]
          have : (∑ s, if σ s = σ t then π s else 0) = cellMass π σ t := rfl
          rw [this, div_self hM.ne', one_mul]
        · simp

/-- **Optimality of `x^σ` on unions of cells.** If `x` is a signal plan for `σ` and `y` is a
`σ`-measurable plan feasible in every state, then `∑_{s∈C} π_s u_s(y_s) ≤ ∑_{s∈C} π_s u_s(x_s)`
for every union `C` of `σ`-cells. -/
theorem signalPlan_optimal_on {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (C : Fin S → Prop) [DecidablePred C] (hC : ∀ s t, σ s = σ t → (C s ↔ C t))
    {y : Fin S → α} (hy : SigmaMeas σ y) (hyB : ∀ s, y s ∈ B s) :
    (∑ s, if C s then π s * u s (y s) else 0) ≤ ∑ s, if C s then π s * u s (x s) else 0 := by
  rw [sum_eq_sum_cells hπ u σ C hC hy, sum_eq_sum_cells hπ u σ C hC hx.1]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs with hs
  · have hM := cellMass_pos hπ σ s
    have h1 := hx.2.2 s (y s) (hyB s)
    rw [condEU_eq, condEU_eq, div_le_div_iff_of_pos_right hM] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hM]
    exact mul_le_mul_of_nonneg_left h1 (hπ s).le
  · exact le_rfl

/-- **Exercise 19.H.3** (MWG, p. 729), first step of the proof of Proposition 19.H.1: `x^σ` solves
`max ∑_s π_s u_s(x_s)` over `B^σ`, the `σ`-measurable plans in the budget sets. -/
theorem exercise_19_H_3_max {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x)
    {y : Fin S → α} (hy : SigmaMeas σ y) (hyB : ∀ s, y s ∈ B s) :
    ∑ s, π s * u s (y s) ≤ ∑ s, π s * u s (x s) := by
  simpa using signalPlan_optimal_on hπ hx (fun _ => True) (fun _ _ _ => Iff.rfl) hy hyB

omit [DecidableEq β] in
/-- **Exercise 19.H.3** (MWG, p. 729), second step: if `σ'` is at least as informative as `σ`,
`B^σ ⊆ B^{σ'}`. -/
theorem exercise_19_H_3_subset {β' : Type*} {σ : Fin S → β} {σ' : Fin S → β'}
    (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {y : Fin S → α} (hy : SigmaMeas σ y ∧ ∀ s, y s ∈ B s) :
    SigmaMeas σ' y ∧ ∀ s, y s ∈ B s :=
  ⟨hy.1.mono h, hy.2⟩

/-- **Proposition 19.H.1** (MWG, p. 718), with the state-dependent budgets of **Exercise 19.H.2**
(the book's case is `B_s = {y : p y₁ + y₂ ≤ w}` for all `s`). In the single-consumer problem, if
`σ'` is at least as informative as `σ`, the ex ante utility of `x^{σ'}` is at least that of
`x^σ`. -/
theorem proposition_19_H_1 {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → α → ℝ} {σ : Fin S → β} {σ' : Fin S → β'} (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {x x' : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (hx' : IsSignalPlan π u σ' B x') :
    ∑ s, π s * u s (x s) ≤ ∑ s, π s * u s (x' s) :=
  exercise_19_H_3_max hπ hx' (hx.1.mono h) hx.2.1

/-- **Exercise 19.H.2** (MWG, p. 729). For Proposition 19.H.1 the spot price and wealth may depend
on the state provided they are `σ`-measurable (then they are `σ'`-measurable as well, and the
budget of the signal `σ(s)` is well defined): with `B_s = {y : p_s y₁ + y₂ ≤ w_s}`. -/
theorem exercise_19_H_2 {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin 2 → ℝ) → ℝ} {σ : Fin S → β} {σ' : Fin S → β'}
    (h : AtLeastAsInformative σ' σ) {p w : Fin S → ℝ} (hp : SigmaMeas σ p) (hw : SigmaMeas σ w)
    {x x' : Fin S → Fin 2 → ℝ}
    (hx : IsSignalPlan π u σ (fun s => {y | p s * y 0 + y 1 ≤ w s}) x)
    (hx' : IsSignalPlan π u σ' (fun s => {y | p s * y 0 + y 1 ≤ w s}) x') :
    SigmaMeas σ' p ∧ SigmaMeas σ' w ∧ ∑ s, π s * u s (x s) ≤ ∑ s, π s * u s (x' s) :=
  ⟨hp.mono h, hw.mono h, proposition_19_H_1 hπ h hx hx'⟩

/-! ## Exercise 19.H.1 -/

/-- With a completely revealing signal, conditional expected utility is the state's utility. -/
theorem condEU_of_injective {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {σ : Fin S → β}
    (hσ : Function.Injective σ) (u : Fin S → α → ℝ) (s : Fin S) (y : α) :
    condEU π u σ s y = u s y := by
  rw [condEU_eq]
  have hcell : cellMass π σ s = π s := by
    unfold cellMass
    rw [Finset.sum_eq_single s (fun t _ ht => by simp [hσ.ne ht]) (by simp)]
    simp
  rw [hcell, Finset.sum_eq_single s (fun t _ ht => by simp [hσ.ne ht]) (by simp)]
  simp only [ite_true]
  field_simp [(hπ s).ne']

/-- **Exercise 19.H.1(a)** (MWG, p. 729). If `σ` is completely revealing, `x^σ` is ex post optimal:
in every state the consumption is optimal for that state's spot economy. -/
theorem exercise_19_H_1a {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} (hσ : Function.Injective σ) {B : Fin S → Set α} {x : Fin S → α}
    (hx : IsSignalPlan π u σ B x) : ∀ s, ∀ y ∈ B s, u s y ≤ u s (x s) := by
  intro s y hy
  have := hx.2.2 s y hy
  rwa [condEU_of_injective hπ hσ, condEU_of_injective hπ hσ] at this

/-- **Exercise 19.H.1(a)** (MWG, p. 729): without complete revelation `x^σ` need not be ex post
optimal. Two equally likely states, no information (`σ` constant), `u_s(y) = -(y₁ - t_s)²` with
`t = (1, -1)` and budget `y₁ + y₂ ≤ 0`: the plan `x = (0, 0)` in both states is `x^σ`, but in state
`1` the bundle `(1, -1)` is affordable and better. -/
theorem exercise_19_H_1a_counterexample :
    IsSignalPlan (fun _ : Fin 2 => (1 / 2 : ℝ)) ![fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2,
        fun y => -(y 0 + 1) ^ 2] (fun _ => (0 : ℕ)) (fun _ => {y | y 0 + y 1 ≤ 0})
        (fun _ => 0) ∧
      (![(1 : ℝ), -1] ∈ {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0}) ∧
      (fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2) (0 : Fin 2 → ℝ) <
        (fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2) ![1, -1] := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ => by simp, fun s y _ => ?_⟩, by simp, by norm_num⟩
  rw [condEU_eq, condEU_eq]
  simp [cellMass, Fin.sum_univ_two]
  nlinarith [sq_nonneg (y 0)]

/-- **Exercise 19.H.1(b)** (MWG, p. 729). `x^σ` is interim optimal: no `σ`-measurable feasible plan
has a higher expected utility conditional on `σ(s)` for any `s`. -/
theorem exercise_19_H_1b {π : Fin S → ℝ} {u : Fin S → α → ℝ} {σ : Fin S → β}
    {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x) :
    ¬ ∃ y : Fin S → α, SigmaMeas σ y ∧ (∀ s, y s ∈ B s) ∧
      ∃ s, condEU π u σ s (x s) < condEU π u σ s (y s) := by
  rintro ⟨y, -, hyB, s, hs⟩
  linarith [hx.2.2 s (y s) (hyB s)]

/-- **Exercise 19.H.1(c)** (MWG, p. 729). If `σ'` is at least as informative as `σ`, then for every
`s` the expected utility of `x^{σ'}` conditional on `σ'(s)` is at least that of `x^σ`. -/
theorem exercise_19_H_1c {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} {u : Fin S → α → ℝ}
    {σ : Fin S → β} {σ' : Fin S → β'} {B : Fin S → Set α} {x x' : Fin S → α}
    (hx : IsSignalPlan π u σ B x) (hx' : IsSignalPlan π u σ' B x') (s : Fin S) :
    condEU π u σ' s (x s) ≤ condEU π u σ' s (x' s) :=
  hx'.2.2 s (x s) (hx.2.1 s)

/-- **Exercise 19.H.1(d)** (MWG, p. 729). If `σ'` is at least as informative as `σ`, then for every
`s` the expected utility of the plan `x^{σ'}` conditional on `σ(s)` is at least that of `x^σ`. -/
theorem exercise_19_H_1d {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → α → ℝ} {σ : Fin S → β} {σ' : Fin S → β'} (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {x x' : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (hx' : IsSignalPlan π u σ' B x') (s : Fin S) :
    ∑ t, posterior π σ s t * u t (x t) ≤ ∑ t, posterior π σ s t * u t (x' t) := by
  have hC : ∀ t t', σ' t = σ' t' → (σ t = σ s ↔ σ t' = σ s) := fun t t' h' => by
    rw [(footnote_19_43 σ' σ).mp h t t' h']
  have key := signalPlan_optimal_on hπ hx' (fun t => σ t = σ s) hC (hx.1.mono h) hx.2.1
  have hM := cellMass_pos hπ σ s
  have e : ∀ z : Fin S → α, ∑ t, posterior π σ s t * u t (z t) =
      (∑ t, if σ t = σ s then π t * u t (z t) else 0) / cellMass π σ s := by
    intro z
    unfold posterior
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
  rw [e, e]
  exact div_le_div_of_nonneg_right key hM.le

/-! ## Example 19.H.1 (Hirshleifer) -/

/-- **Example 19.H.1** (MWG, pp. 718-719), no information: both consumers maximize
`½√x₁ + ½√x₂`; at prices `(1, 1)` each consumer gets `(½, ½)`, an equilibrium, with expected
utility `1/√2 = √(1/2)`. -/
theorem example_19_H_1_noinfo :
    IsSpotEqm (fun (_ : Fin 2) (y : Fin 2 → ℝ) => 1 / 2 * √(y 0) + 1 / 2 * √(y 1))
        ![![1, 0], ![0, 1]] ![1, 1] ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]] ∧
      1 / 2 * √(1 / 2 : ℝ) + 1 / 2 * √(1 / 2) = √(1 / 2) := by
  refine ⟨⟨fun i => ⟨⟨fun l => ?_, ?_⟩, fun y hy hb => ?_⟩, fun l => ?_⟩, by ring⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> norm_num
  · have hb' : y 0 + y 1 ≤ 1 := by
      fin_cases i <;> simpa [dotProduct, Fin.sum_univ_two] using hb
    have h0 := hy 0; have h1 := hy 1
    have hs : (√(y 0) + √(y 1)) ^ 2 ≤ 2 := by
      have e0 := Real.sq_sqrt h0; have e1 := Real.sq_sqrt h1
      nlinarith [sq_nonneg (√(y 0) - √(y 1)), Real.sqrt_nonneg (y 0), Real.sqrt_nonneg (y 1)]
    have hle : 1 / 2 * √(y 0) + 1 / 2 * √(y 1) ≤ √(1 / 2) := by
      rw [show 1 / 2 * √(y 0) + 1 / 2 * √(y 1) = (√(y 0) + √(y 1)) / 2 by ring]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    fin_cases i <;>
      (change 1 / 2 * √(y 0) + 1 / 2 * √(y 1) ≤ 1 / 2 * √(1 / 2) + 1 / 2 * √(1 / 2)
       linarith [hle])
  · fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- In any spot equilibrium where both consumers value only good `0` (utility `√y₀`), the
consumer owning the unit of good `0` consumes it all and the other consumes none: utilities `1`
and `0` (perfect information, state 1 of Example 19.H.1). -/
theorem example_19_H_1_state1 {p : Fin 2 → ℝ} {y : Fin 2 → Fin 2 → ℝ}
    (h : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 0)) ![![1, 0], ![0, 1]] p y) :
    √(y 0 0) = 1 ∧ √(y 1 0) = 0 := by
  obtain ⟨hc, hclear⟩ := h
  obtain ⟨⟨hy0, hb0⟩, hopt0⟩ := hc 0
  obtain ⟨⟨hy1, -⟩, -⟩ := hc 1
  simp only [Matrix.cons_val_zero, dotProduct, Fin.sum_univ_two, Matrix.cons_val_one] at hb0 hopt0
  simp only [mul_one, mul_zero, add_zero] at hb0 hopt0
  have hp0 : 0 < p 0 := by
    by_contra hle
    push Not at hle
    have := hopt0 ![y 0 0 + 1, 0] (fun l => by
      fin_cases l
      · change 0 ≤ y 0 0 + 1; linarith [hy0 0]
      · simp)
      (by change p 0 * (y 0 0 + 1) + p 1 * 0 ≤ p 0; nlinarith [hy0 0])
    change √(y 0 0 + 1) ≤ √(y 0 0) at this
    linarith [Real.sqrt_lt_sqrt (hy0 0) (lt_add_one (y 0 0))]
  have hp1 : 0 ≤ p 1 := by
    by_contra hneg
    push Not at hneg
    have := hopt0 ![y 0 0 + 1, p 0 * y 0 0 / (-p 1)]
      (fun l => by
        fin_cases l
        · change 0 ≤ y 0 0 + 1; linarith [hy0 0]
        · change 0 ≤ p 0 * y 0 0 / (-p 1)
          exact div_nonneg (mul_nonneg hp0.le (hy0 0)) (by linarith))
      (by
        change p 0 * (y 0 0 + 1) + p 1 * (p 0 * y 0 0 / (-p 1)) ≤ p 0
        have : p 1 * (p 0 * y 0 0 / (-p 1)) = -(p 0 * y 0 0) := by
          have := hneg.ne; field_simp
        linarith)
    change √(y 0 0 + 1) ≤ √(y 0 0) at this
    linarith [Real.sqrt_lt_sqrt (hy0 0) (lt_add_one (y 0 0))]
  have hle1 : y 0 0 ≤ 1 := by nlinarith [hy0 1]
  have hge1 : 1 ≤ y 0 0 := by
    have := hopt0 ![1, 0] (fun l => by fin_cases l <;> simp) (by simp)
    change √1 ≤ √(y 0 0) at this
    rwa [Real.sqrt_one, Real.one_le_sqrt] at this
  have hy00 : y 0 0 = 1 := le_antisymm hle1 hge1
  have hy10 : y 1 0 = 0 := by
    have := hclear 0
    simp [Fin.sum_univ_two] at this
    linarith [hy1 0]
  exact ⟨by rw [hy00, Real.sqrt_one], by rw [hy10, Real.sqrt_zero]⟩

/-- In state 2 of Example 19.H.1 only good `1` is valued; its owner (consumer 2) gets utility `1`
and consumer 1 gets `0`. -/
theorem example_19_H_1_state2 {p : Fin 2 → ℝ} {y : Fin 2 → Fin 2 → ℝ}
    (h : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 1)) ![![1, 0], ![0, 1]] p y) :
    √(y 1 1) = 1 ∧ √(y 0 1) = 0 := by
  obtain ⟨hc, hclear⟩ := h
  obtain ⟨⟨hy1, hb1⟩, hopt1⟩ := hc 1
  obtain ⟨⟨hy0, -⟩, -⟩ := hc 0
  simp only [Matrix.cons_val_one, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero] at hb1 hopt1
  simp only [mul_one, mul_zero, zero_add] at hb1 hopt1
  have hp1 : 0 < p 1 := by
    by_contra hle
    push Not at hle
    have := hopt1 ![0, y 1 1 + 1] (fun l => by
      fin_cases l
      · simp
      · change 0 ≤ y 1 1 + 1; linarith [hy1 1])
      (by change p 0 * 0 + p 1 * (y 1 1 + 1) ≤ p 1; nlinarith [hy1 1])
    change √(y 1 1 + 1) ≤ √(y 1 1) at this
    linarith [Real.sqrt_lt_sqrt (hy1 1) (lt_add_one (y 1 1))]
  have hp0 : 0 ≤ p 0 := by
    by_contra hneg
    push Not at hneg
    have := hopt1 ![p 1 * y 1 1 / (-p 0), y 1 1 + 1]
      (fun l => by
        fin_cases l
        · change 0 ≤ p 1 * y 1 1 / (-p 0)
          exact div_nonneg (mul_nonneg hp1.le (hy1 1)) (by linarith)
        · change 0 ≤ y 1 1 + 1; linarith [hy1 1])
      (by
        change p 0 * (p 1 * y 1 1 / (-p 0)) + p 1 * (y 1 1 + 1) ≤ p 1
        have : p 0 * (p 1 * y 1 1 / (-p 0)) = -(p 1 * y 1 1) := by
          have := hneg.ne; field_simp
        linarith)
    change √(y 1 1 + 1) ≤ √(y 1 1) at this
    linarith [Real.sqrt_lt_sqrt (hy1 1) (lt_add_one (y 1 1))]
  have hle1 : y 1 1 ≤ 1 := by nlinarith [hy1 0]
  have hge1 : 1 ≤ y 1 1 := by
    have := hopt1 ![0, 1] (fun l => by fin_cases l <;> simp) (by simp)
    change √1 ≤ √(y 1 1) at this
    rwa [Real.sqrt_one, Real.one_le_sqrt] at this
  have hy11 : y 1 1 = 1 := le_antisymm hle1 hge1
  have hy01 : y 0 1 = 0 := by
    have := hclear 1
    simp [Fin.sum_univ_two] at this
    linarith [hy0 1]
  exact ⟨by rw [hy11, Real.sqrt_one], by rw [hy01, Real.sqrt_zero]⟩

/-- **Example 19.H.1** (MWG, p. 719). With perfect information each consumer gets utility `1` in one
state and `0` in the other at every spot equilibrium, hence an ex ante utility of `1/2`, which is
less than the `1/√2` of the no-information equilibrium: better information makes everybody worse
off. -/
theorem example_19_H_1 {p₁ p₂ : Fin 2 → ℝ} {y₁ y₂ : Fin 2 → Fin 2 → ℝ}
    (h₁ : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 0)) ![![1, 0], ![0, 1]] p₁ y₁)
    (h₂ : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 1)) ![![1, 0], ![0, 1]] p₂ y₂) :
    1 / 2 * √(y₁ 0 0) + 1 / 2 * √(y₂ 0 1) = 1 / 2 ∧
      1 / 2 * √(y₁ 1 0) + 1 / 2 * √(y₂ 1 1) = 1 / 2 ∧ (1 / 2 : ℝ) < √(1 / 2) := by
  obtain ⟨a1, a2⟩ := example_19_H_1_state1 h₁
  obtain ⟨b1, b2⟩ := example_19_H_1_state2 h₂
  refine ⟨by rw [a1, b2]; ring, by rw [a2, b1]; ring, ?_⟩
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Rational expectations equilibrium (MWG Section 19.H, pp. 719-724, Exercises 19.H.4, 19.H.7)

* **Definition 19.H.2** in general form: a price function `P` is a rational expectations
  equilibrium price function if for every state the price clears the spot market when every
  consumer knows the event `{s' : P(s') = P(s), σᵢ(s') = σᵢ(s)}` (`IsREE`, for any notion of
  market clearing `Clears`). The pooled information price function, full revelation, and the
  theorem of p. 721: a fully revealing pooled information price function is a rational
  expectations equilibrium (`pooled_fullyRevealing_isREE`).
* The quasilinear economies of Examples 19.H.2-19.H.5 and Exercise 19.H.7: utilities
  `β_{s} ln x₁ + x₂`, updated utilities `∑_{s'} π(s'|E) u_{s'}`, demand `x₁ = b/p` (`qlOptimal_iff`)
  and the clearing price `p = ∑ bᵢ / ∑ eᵢ` (`qlSpotEqm_iff`).
* **Example 19.H.2**: the naive price `p(β) = (3 + 2β)/4` reveals `β` and is not a rational
  expectations equilibrium; the pooled price `β` is (`example_19_H_2`, `example_19_H_2_continued`).
* **Example 19.H.3** (Kreps): no rational expectations equilibrium exists (`example_19_H_3`).
* Examples 19.H.4-19.H.6 and Exercises 19.H.4-19.H.7 are in `REExamples`.
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ} {ι : Type*} [Fintype ι]

/-! ## Definition 19.H.2 and the pooled information price function -/

variable {β : Type*} [DecidableEq β]

/-- The event `{s' : P(s') = P(s), σᵢ(s') = σᵢ(s)}` known to consumer `i` at `s` (p. 720). -/
noncomputable def reeEvent (P : Fin S → ℝ) (σ : ι → Fin S → β) (i : ι) (s : Fin S) :
    Finset (Fin S) :=
  Finset.univ.filter fun s' => P s' = P s ∧ σ i s' = σ i s

/-- The pooled information event `{s' : σ_k(s') = σ_k(s) for all k}` (p. 721). -/
def pooledEvent (σ : ι → Fin S → β) (s : Fin S) : Finset (Fin S) :=
  Finset.univ.filter fun s' => ∀ k, σ k s' = σ k s

/-- **Definition 19.H.2** (MWG, p. 721). `P` is a rational expectations equilibrium price function
if for every `s`, `P(s)` clears the spot market when every consumer `i` knows that
`s ∈ E_{P(s), σᵢ(s)}` and evaluates bundles with the updated utility. Market clearing given the
consumers' events is the parameter `Clears s E p`. -/
def IsREE (Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop) (P : Fin S → ℝ)
    (σ : ι → Fin S → β) : Prop :=
  ∀ s, Clears s (fun i => reeEvent P σ i s) (P s)

/-- **p. 721**. The pooled information equilibrium price function: `P(s)` clears the market when
every consumer knows the vector of all signals. -/
def IsPooledPrice (Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop) (P : Fin S → ℝ)
    (σ : ι → Fin S → β) : Prop :=
  ∀ s, Clears s (fun _ => pooledEvent σ s) (P s)

/-- **p. 721**. `P` is fully revealing: it distinguishes any two states distinguished by some
consumer. -/
def FullyRevealing (P : Fin S → ℝ) (σ : ι → Fin S → β) : Prop :=
  ∀ s s', (∃ i, σ i s ≠ σ i s') → P s ≠ P s'

/-- **p. 721**. The price depends only on the vector of signals, `P(s) = P̂(σ₁(s), …, σ_I(s))`. -/
def DependsOnSignals (P : Fin S → ℝ) (σ : ι → Fin S → β) : Prop :=
  ∀ s s', (∀ i, σ i s = σ i s') → P s = P s'

/-- **p. 721**. A fully revealing pooled information price function generates, for every consumer,
exactly the pooled event. -/
theorem reeEvent_eq_pooled {P : Fin S → ℝ} {σ : ι → Fin S → β} (hfr : FullyRevealing P σ)
    (hdep : DependsOnSignals P σ) (i : ι) (s : Fin S) : reeEvent P σ i s = pooledEvent σ s := by
  ext s'
  simp only [reeEvent, pooledEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hP, -⟩ k
    by_contra hk
    exact hfr s' s ⟨k, hk⟩ hP
  · intro h
    exact ⟨hdep s' s h, h i⟩

/-- **p. 721**. If the pooled information equilibrium price function is fully revealing, it is a
rational expectations equilibrium price function: the information used by consumers is obtained
from the public price signal. -/
theorem pooled_fullyRevealing_isREE {Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop}
    {P : Fin S → ℝ} {σ : ι → Fin S → β} (hpool : IsPooledPrice Clears P σ)
    (hfr : FullyRevealing P σ) (hdep : DependsOnSignals P σ) : IsREE Clears P σ := by
  intro s
  have : (fun i => reeEvent P σ i s) = fun _ => pooledEvent σ s :=
    funext fun i => reeEvent_eq_pooled hfr hdep i s
  rw [this]
  exact hpool s

/-! ## Quasilinear economies -/

/-- The bundle `y = (y₁, y₂)` maximizes `b ln y₁ + y₂` on `{y₁ > 0, p y₁ + y₂ ≤ p e}`. -/
def QLOptimal (b p e : ℝ) (y : ℝ × ℝ) : Prop :=
  0 < y.1 ∧ p * y.1 + y.2 ≤ p * e ∧
    ∀ y' : ℝ × ℝ, 0 < y'.1 → p * y'.1 + y'.2 ≤ p * e → b * Real.log y'.1 + y'.2 ≤
      b * Real.log y.1 + y.2

/-- The demand of a quasilinear consumer: `y₁ = b/p`, `y₂ = p e - b`. -/
theorem qlOptimal_iff {b p e : ℝ} (hb : 0 < b) (hp : 0 < p) (y : ℝ × ℝ) :
    QLOptimal b p e y ↔ y.1 = b / p ∧ y.2 = p * e - b := by
  constructor
  · rintro ⟨hy, hbud, hmax⟩
    have hbp : 0 < b / p := div_pos hb hp
    have h1 := hmax (b / p, p * e - b) hbp (by simp; field_simp; linarith)
    exact quasilinearLog_eq_iff hb hp hy hbud (by simpa using h1.trans_eq' (by ring))
  · rintro ⟨h1, h2⟩
    have hbp : 0 < b / p := div_pos hb hp
    refine ⟨h1 ▸ hbp, by rw [h1, h2]; field_simp; linarith, fun y' hy' hb' => ?_⟩
    rw [h1, h2]
    have := quasilinearLog_le hb hp hy' hb'
    linarith

/-- A quasilinear consumer with `b > 0` has no optimal bundle when `p ≤ 0`. -/
theorem qlOptimal_price_pos {b p e : ℝ} (hb : 0 < b) {y : ℝ × ℝ} (h : QLOptimal b p e y) :
    0 < p := by
  by_contra hp
  push Not at hp
  have := h.2.2 (y.1 + 1, y.2) (by linarith [h.1]) (by simp; nlinarith [h.2.1])
  have hlog := Real.log_lt_log h.1 (lt_add_one y.1)
  simp at this
  nlinarith

/-- A spot equilibrium price of the quasilinear economy with coefficients `bᵢ` and endowments `eᵢ`
of good 1: optimal bundles that clear the market for good 1. -/
def QLSpotEqm (b e : ι → ℝ) (p : ℝ) : Prop :=
  ∃ y : ι → ℝ × ℝ, (∀ i, QLOptimal (b i) p (e i) (y i)) ∧ ∑ i, (y i).1 = ∑ i, e i

/-- The spot equilibrium price is `p = ∑ bᵢ / ∑ eᵢ` (with `bᵢ > 0`, `∑ eᵢ > 0`). -/
theorem qlSpotEqm_iff {b e : ι → ℝ} (hb : ∀ i, 0 < b i) (he : 0 < ∑ i, e i) (p : ℝ) :
    QLSpotEqm b e p ↔ p = (∑ i, b i) / ∑ i, e i := by
  constructor
  · rintro ⟨y, hy, hcl⟩
    obtain ⟨i₀⟩ : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at he
    have hp := qlOptimal_price_pos (hb i₀) (hy i₀)
    have h1 : ∀ i, (y i).1 = b i / p := fun i => ((qlOptimal_iff (hb i) hp _).mp (hy i)).1
    simp only [h1, ← Finset.sum_div] at hcl
    rw [eq_div_iff he.ne']
    field_simp at hcl
    linarith
  · intro hp
    have hbs : 0 < ∑ i, b i := by
      obtain ⟨i₀⟩ : Nonempty ι := by
        by_contra h; rw [not_nonempty_iff] at h; simp at he
      exact Finset.sum_pos (fun i _ => hb i) ⟨i₀, Finset.mem_univ _⟩
    have hp0 : 0 < p := by rw [hp]; exact div_pos hbs he
    refine ⟨fun i => (b i / p, p * e i - b i), fun i => (qlOptimal_iff (hb i) hp0 _).mpr
      ⟨rfl, rfl⟩, ?_⟩
    simp only [← Finset.sum_div]
    rw [div_eq_iff hp0.ne', hp]
    field_simp

/-- The posterior mean coefficient `∑_{s∈E} π_s β_s / ∑_{s∈E} π_s`. -/
noncomputable def postCoef (π β : Fin S → ℝ) (E : Finset (Fin S)) : ℝ :=
  (∑ s ∈ E, π s * β s) / ∑ s ∈ E, π s

/-- The updated utility `∑_{s' ∈ E} (π_{s'} / π(E)) (β_{s'} ln y₁ + y₂)` (Definition 19.H.2). -/
noncomputable def updU (π β : Fin S → ℝ) (E : Finset (Fin S)) (y : ℝ × ℝ) : ℝ :=
  ∑ s ∈ E, π s / (∑ t ∈ E, π t) * (β s * Real.log y.1 + y.2)

/-- The updated utility is `postCoef · ln y₁ + y₂`. -/
theorem updU_eq {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (β : Fin S → ℝ) {E : Finset (Fin S)}
    (hE : E.Nonempty) (y : ℝ × ℝ) :
    updU π β E y = postCoef π β E * Real.log y.1 + y.2 := by
  have hM : 0 < ∑ t ∈ E, π t := Finset.sum_pos (fun t _ => hπ t) hE
  unfold updU postCoef
  have e : ∀ s ∈ E, π s / (∑ t ∈ E, π t) * (β s * Real.log y.1 + y.2) =
      π s * β s / (∑ t ∈ E, π t) * Real.log y.1 + π s / (∑ t ∈ E, π t) * y.2 :=
    fun s _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_div, ← Finset.sum_div, div_self hM.ne', one_mul]

/-- Market clearing in the quasilinear economy at state `s` when consumer `i` knows the event
`E i`: optimal bundles for the updated utilities clear the market for good 1. -/
def QLClears (π : Fin S → ℝ) (βc : ι → Fin S → ℝ) (e : ι → Fin S → ℝ) (s : Fin S)
    (E : ι → Finset (Fin S)) (p : ℝ) : Prop :=
  ∃ y : ι → ℝ × ℝ, (∀ i, 0 < (y i).1 ∧ p * (y i).1 + (y i).2 ≤ p * e i s ∧
    ∀ y' : ℝ × ℝ, 0 < y'.1 → p * y'.1 + y'.2 ≤ p * e i s →
      updU π (βc i) (E i) y' ≤ updU π (βc i) (E i) (y i)) ∧ ∑ i, (y i).1 = ∑ i, e i s

/-- Clearing with updated utilities is the spot equilibrium with the posterior coefficients. -/
theorem qlClears_iff {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (βc : ι → Fin S → ℝ)
    (e : ι → Fin S → ℝ) (s : Fin S) {E : ι → Finset (Fin S)} (hE : ∀ i, (E i).Nonempty)
    (p : ℝ) :
    QLClears π βc e s E p ↔ QLSpotEqm (fun i => postCoef π (βc i) (E i)) (fun i => e i s) p := by
  unfold QLClears QLSpotEqm QLOptimal
  simp only [updU_eq hπ _ (hE _)]

theorem postCoef_singleton {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (β : Fin S → ℝ) (s : Fin S) :
    postCoef π β {s} = β s := by
  simp [postCoef, (hπ s).ne']

theorem postCoef_const {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {β : Fin S → ℝ} {E : Finset (Fin S)}
    (hE : E.Nonempty) {c : ℝ} (hc : ∀ s ∈ E, β s = c) : postCoef π β E = c := by
  have hM : 0 < ∑ t ∈ E, π t := Finset.sum_pos (fun t _ => hπ t) hE
  unfold postCoef
  rw [show (∑ s ∈ E, π s * β s) = (∑ s ∈ E, π s) * c from by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s hs => by rw [hc s hs]]
  field_simp

omit [Fintype ι] in
theorem reeEvent_nonempty (P : Fin S → ℝ) (σ : ι → Fin S → β) (i : ι) (s : Fin S) :
    (reeEvent P σ i s).Nonempty := ⟨s, by simp [reeEvent]⟩

theorem pooledEvent_nonempty (σ : ι → Fin S → β) (s : Fin S) : (pooledEvent σ s).Nonempty :=
  ⟨s, by simp [pooledEvent]⟩

/-- Two consumers: the clearing price is `(b₀ + b₁)/(e₀ + e₁)`. -/
theorem qlSpotEqm_two {b e : Fin 2 → ℝ} (hb0 : 0 < b 0) (hb1 : 0 < b 1) (he : 0 < e 0 + e 1)
    (p : ℝ) : QLSpotEqm b e p ↔ p = (b 0 + b 1) / (e 0 + e 1) := by
  rw [qlSpotEqm_iff (fun i => by fin_cases i <;> assumption) (by simpa [Fin.sum_univ_two]),
    Fin.sum_univ_two, Fin.sum_univ_two]

/-! ## Examples 19.H.2 and 19.H.3 -/

/-- The two equally likely states of Examples 19.H.2-19.H.3: `β = 1` (state `0`), `β = 2`
(state `1`). -/
def beta19H (s : Fin 2) : ℝ := s.val + 1

theorem beta19H_pos (s : Fin 2) : 0 < beta19H s := by unfold beta19H; positivity

/-- Equal prior probabilities. -/
noncomputable def half2 : Fin 2 → ℝ := fun _ => 1 / 2

theorem half2_pos : ∀ s, 0 < half2 s := fun _ => by norm_num [half2]

theorem postCoef_univ_beta : postCoef half2 beta19H Finset.univ = 3 / 2 := by
  simp [postCoef, half2, beta19H, Fin.sum_univ_two]; norm_num

/-- The coefficients of Example 19.H.2: both consumers have `β ln x₁ + x₂`. -/
def betaBoth : Fin 2 → Fin 2 → ℝ := fun _ => beta19H

/-- One unit of good 1 for each consumer in each state. -/
def ones2 : Fin 2 → Fin 2 → ℝ := fun _ _ => 1

/-- The signals of Example 19.H.2: consumer `0` observes the state, consumer `1` observes
nothing. -/
def sig19H2 (i : Fin 2) (s : Fin 2) : ℕ := if i = 0 then s.val else 0

/-- Two consumers: clearing with updated utilities at the price
`(c₀ + c₁)/(e₀ + e₁)`, `cᵢ` the posterior coefficients. -/
theorem qlClears_two {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {βc e : Fin 2 → Fin S → ℝ} {s : Fin S}
    {E : Fin 2 → Finset (Fin S)} (hE : ∀ i, (E i).Nonempty)
    (hb : ∀ i, 0 < postCoef π (βc i) (E i)) (he : 0 < e 0 s + e 1 s) (p : ℝ) :
    QLClears π βc e s E p ↔
      p = (postCoef π (βc 0) (E 0) + postCoef π (βc 1) (E 1)) / (e 0 s + e 1 s) := by
  rw [qlClears_iff hπ βc e s hE, qlSpotEqm_two (hb 0) (hb 1) he]

/-- The events of Example 19.H.2 without learning from prices: consumer 1 knows the state,
consumer 2 knows nothing. -/
def naiveEvents19H2 (s : Fin 2) : Fin 2 → Finset (Fin 2) := ![{s}, Finset.univ]

/-- **Example 19.H.2** (MWG, p. 720). Both consumers have `u = β ln x₁ + x₂` and one unit of good 1;
consumer 1 knows `β`, consumer 2 does not. If consumer 2 does not learn from the price, the
clearing price is `p(β) = (3 + 2β)/4`, which reveals `β` (`p(1) ≠ p(2)`); but this price function
is not a rational expectations equilibrium: once consumer 2 infers `β` from it, it no longer
clears the market. -/
theorem example_19_H_2 :
    (∀ s, QLClears half2 betaBoth ones2 s (naiveEvents19H2 s) ((3 + 2 * beta19H s) / 4)) ∧
      (3 + 2 * beta19H 0) / 4 ≠ (3 + 2 * beta19H 1) / 4 ∧
      ¬ IsREE (QLClears half2 betaBoth ones2) (fun s => (3 + 2 * beta19H s) / 4) sig19H2 := by
  have hones : ∀ s, ones2 0 s + ones2 1 s = 2 := fun s => by norm_num [ones2]
  refine ⟨fun s => ?_, by norm_num [beta19H], fun h => ?_⟩
  · have c0 : postCoef half2 (betaBoth 0) (naiveEvents19H2 s 0) = beta19H s :=
      postCoef_singleton half2_pos _ s
    have c1 : postCoef half2 (betaBoth 1) (naiveEvents19H2 s 1) = 3 / 2 := postCoef_univ_beta
    rw [qlClears_two half2_pos (fun i => by fin_cases i <;> simp [naiveEvents19H2])
      (fun i => by fin_cases i
                   · exact c0 ▸ beta19H_pos s
                   · exact c1 ▸ by norm_num) (by rw [hones]; norm_num), c0, c1, hones]
    ring
  · have h0 := h 0
    have hev : (fun i => reeEvent (fun s => (3 + 2 * beta19H s) / 4) sig19H2 i 0) =
        fun _ => {0} := by
      funext i
      ext s'
      fin_cases i <;> fin_cases s' <;> simp [reeEvent, sig19H2, beta19H]
    unfold IsREE at h
    rw [hev] at h0
    have c : ∀ i, postCoef half2 (betaBoth i) {0} = 1 := fun i => by
      rw [postCoef_singleton half2_pos]; simp [betaBoth, beta19H]
    rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; norm_num)
      (by rw [hones]; norm_num), c, c, hones] at h0
    norm_num [beta19H] at h0

/-- **Example 19.H.2 continued** (MWG, p. 721). If both consumers are informed, the pooled
information price function is `p̂(β) = β`; it is fully revealing and therefore a rational
expectations equilibrium. -/
theorem example_19_H_2_continued :
    IsPooledPrice (QLClears half2 betaBoth ones2) beta19H sig19H2 ∧
      IsREE (QLClears half2 betaBoth ones2) beta19H sig19H2 := by
  have hones : ∀ s, ones2 0 s + ones2 1 s = 2 := fun s => by norm_num [ones2]
  have hpool : ∀ s, pooledEvent sig19H2 s = {s} := by
    intro s; ext s'
    fin_cases s <;> fin_cases s' <;> simp [pooledEvent, sig19H2, Fin.forall_fin_two]
  have hP : IsPooledPrice (QLClears half2 betaBoth ones2) beta19H sig19H2 := by
    intro s
    have c : ∀ i, postCoef half2 (betaBoth i) {s} = beta19H s := fun i =>
      postCoef_singleton half2_pos _ s
    simp only [hpool]
    rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact beta19H_pos s)
      (by rw [hones]; norm_num), c, c, hones]
    ring
  refine ⟨hP, pooled_fullyRevealing_isREE hP ?_ ?_⟩
  · rintro s s' ⟨i, hi⟩ hst
    fin_cases s <;> fin_cases s' <;> simp_all [beta19H]
  · intro s s' h
    have : s.val = s'.val := by simpa [sig19H2] using h 0
    rw [Fin.ext_iff.mpr this]

/-- The coefficients of Example 19.H.3: `β` for consumer 1 and `3 - β` for consumer 2. -/
def beta19H3 : Fin 2 → Fin 2 → ℝ := ![beta19H, fun s => 3 - beta19H s]

theorem beta19H3_pos (i s : Fin 2) : 0 < beta19H3 i s := by
  fin_cases i <;> fin_cases s <;> norm_num [beta19H3, beta19H]

/-- **Example 19.H.3** (MWG, p. 722; Kreps 1977). Utilities `β ln x₁₁ + x₂₁` and
`(3 - β) ln x₁₂ + x₂₂`, total endowment of good 1 equal to `3` in both states, consumer 1 informed,
consumer 2 not. The pooled information price is `1` in both states (so it is not revealing), and
no price function is a rational expectations equilibrium. -/
theorem example_19_H_3 {e : Fin 2 → Fin 2 → ℝ} (he : ∀ s, e 0 s + e 1 s = 3) :
    (∀ s, QLClears half2 beta19H3 e s (fun _ => {s}) 1) ∧
      ∀ P : Fin 2 → ℝ, ¬ IsREE (QLClears half2 beta19H3 e) P sig19H2 := by
  have hsing : ∀ i s, postCoef half2 (beta19H3 i) {s} = beta19H3 i s := fun i s =>
    postCoef_singleton half2_pos _ s
  have hsum : ∀ s, beta19H3 0 s + beta19H3 1 s = 3 := fun s => by simp [beta19H3]
  have he' : ∀ s, 0 < e 0 s + e 1 s := fun s => by rw [he s]; norm_num
  refine ⟨fun s => ?_, fun P hP => ?_⟩
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [hsing]; exact beta19H3_pos i s)
      (he' s), hsing, hsing, hsum, he]
    norm_num
  · by_cases hrev : P 0 = P 1
    · -- not revealing: consumer 2 stays uninformed
      have hev : ∀ s, (fun i => reeEvent P sig19H2 i s) = naiveEvents19H2 s := by
        intro s; funext i; ext s'
        fin_cases i <;> fin_cases s <;> fin_cases s' <;>
          simp [reeEvent, sig19H2, hrev, naiveEvents19H2]
      have hpr : ∀ s, P s = (beta19H s + 3 / 2) / 3 := by
        intro s
        have hu : postCoef half2 (beta19H3 1) (naiveEvents19H2 s 1) = 3 / 2 := by
          simp [postCoef, half2, beta19H3, beta19H, Fin.sum_univ_two, naiveEvents19H2]
          norm_num
        have h0 : postCoef half2 (beta19H3 0) (naiveEvents19H2 s 0) = beta19H s := by
          rw [show naiveEvents19H2 s 0 = {s} from rfl, hsing]; rfl
        have := hP s
        rw [hev s, qlClears_two half2_pos (fun i => by fin_cases i <;> simp [naiveEvents19H2])
          (fun i => by
            fin_cases i
            · exact h0 ▸ beta19H_pos s
            · exact hu ▸ by norm_num) (he' s), h0, hu, he] at this
        exact this
      rw [hpr 0, hpr 1] at hrev
      norm_num [beta19H] at hrev
    · -- revealing: both informed, so the price is `1` in both states
      have hrev' : P 1 ≠ P 0 := Ne.symm hrev
      have hev : ∀ s, (fun i => reeEvent P sig19H2 i s) = fun _ => {s} := by
        intro s; funext i; ext s'
        fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H2, hrev, hrev']
      have hpr : ∀ s, P s = 1 := by
        intro s
        have := hP s
        rw [hev s, qlClears_two half2_pos (fun _ => by simp)
          (fun i => by rw [hsing]; exact beta19H3_pos i s) (he' s), hsing, hsing, hsum, he]
          at this
        linarith
      exact hrev ((hpr 0).trans (hpr 1).symm)

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Rational expectations: Examples 19.H.4-19.H.6, Exercises 19.H.4, 19.H.5, 19.H.7

* **Exercise 19.H.7(a)-(d)** (MWG, pp. 730-731): spot prices with full information
  `(1, 6/(6+ε))`, with consumer 1 uninformed `(7/6, 5/(6+ε))`; for `ε ≠ 0` the full-information
  prices are a (revealing) rational expectations equilibrium; for `ε = 0` there is none.
* **Example 19.H.4** and **Exercise 19.H.4** (pp. 722-723): the 50 states `(β, ε₁, ε₂)` of
  footnote 47, signals `σᵢ = β² + εᵢ`. The pooled information price is `2` if some `σᵢ ∈ {4,5,6}`,
  `1` if some `σᵢ ∈ {-1,0,1}`, and `3/2` otherwise; it is not fully revealing but is a rational
  expectations equilibrium price function. The book prints `β/2` and `3/4`, which are the prices
  when each consumer owns two units of good 1, not one as in Example 19.H.2 (correction 8).
* **Example 19.H.5** and **Exercise 19.H.5** (p. 723): the pooled price `β + (1/I)∑ εᵢ`, its
  separation of the two values of `β`, the identification of `εᵢ` from `β` and `σᵢ`, and a `δ > 0`
  independent of `I` and of the price for which a consumer pays `δ` for his signal.
* **Example 19.H.6** (the lemons market, p. 724, footnote 49).
-/

namespace MWG.EquilibriumUncertainty

/-! ## Exercise 19.H.7 -/

/-- The coefficients of Exercise 19.H.7: consumer 1 has `2 ln x₁₁ + x₂₁` in state 1 and
`4 ln x₁₁ + x₂₁` in state 2; consumer 2 has `4` and `2`. -/
def coef19H7 : Fin 2 → Fin 2 → ℝ := ![![2, 4], ![4, 2]]

/-- The endowments of good 1 in Exercise 19.H.7: all held by consumer 2, `6` in state 1 and
`6 + ε` in state 2. -/
def endow19H7 (ε : ℝ) : Fin 2 → Fin 2 → ℝ := ![fun _ => 0, ![6, 6 + ε]]

/-- The signals of Exercise 19.H.7: consumer 1 is uninformed, consumer 2 observes the state. -/
def sig19H7 (i : Fin 2) (s : Fin 2) : ℕ := if i = 0 then 0 else s.val

theorem coef19H7_pos (i s : Fin 2) : 0 < coef19H7 i s := by
  fin_cases i <;> fin_cases s <;> norm_num [coef19H7]

/-- **Exercise 19.H.7(a)** (MWG, p. 730). With both consumers informed the spot prices are
`p̂₁ = 1` and `p̂₂(ε) = 6/(6 + ε)`. -/
theorem exercise_19_H_7a {ε : ℝ} (hε : -6 < ε) :
    QLClears half2 coef19H7 (endow19H7 ε) 0 (fun _ => {0}) 1 ∧
      QLClears half2 coef19H7 (endow19H7 ε) 1 (fun _ => {1}) (6 / (6 + ε)) := by
  have c : ∀ i s, postCoef half2 (coef19H7 i) {s} = coef19H7 i s := fun i s =>
    postCoef_singleton half2_pos _ s
  refine ⟨?_, ?_⟩
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact coef19H7_pos i 0)
      (by norm_num [endow19H7]), c, c]
    norm_num [coef19H7, endow19H7]
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact coef19H7_pos i 1)
      (by simp [endow19H7]; linarith), c, c]
    simp [coef19H7, endow19H7]
    norm_num

/-- The events of Exercise 19.H.7(b): consumer 1 knows nothing, consumer 2 knows the state. -/
def events19H7b (s : Fin 2) : Fin 2 → Finset (Fin 2) := ![Finset.univ, {s}]

theorem u0_19H7 (s : Fin 2) : postCoef half2 (coef19H7 0) (events19H7b s 0) = 3 := by
  simp [postCoef, half2, coef19H7, events19H7b, Fin.sum_univ_two]; norm_num

theorem u1_19H7 (s : Fin 2) : postCoef half2 (coef19H7 1) (events19H7b s 1) = coef19H7 1 s :=
  postCoef_singleton half2_pos _ s

theorem pos_19H7b (s i : Fin 2) : 0 < postCoef half2 (coef19H7 i) (events19H7b s i) := by
  fin_cases i
  · exact (u0_19H7 s) ▸ by norm_num
  · exact (u1_19H7 s) ▸ coef19H7_pos 1 s

theorem ne_19H7b (s i : Fin 2) : (events19H7b s i).Nonempty := by
  fin_cases i <;> simp [events19H7b]

/-- **Exercise 19.H.7(b)** (MWG, p. 730). With consumer 1 uninformed (and prices not used as
signals) the spot prices are `p̄₁ = 7/6` and `p̄₂(ε) = 5/(6 + ε)`. -/
theorem exercise_19_H_7b {ε : ℝ} (hε : -6 < ε) :
    QLClears half2 coef19H7 (endow19H7 ε) 0 (events19H7b 0) (7 / 6) ∧
      QLClears half2 coef19H7 (endow19H7 ε) 1 (events19H7b 1) (5 / (6 + ε)) := by
  refine ⟨?_, ?_⟩
  · rw [qlClears_two half2_pos (ne_19H7b 0) (pos_19H7b 0) (by norm_num [endow19H7]), u0_19H7,
      u1_19H7]
    norm_num [coef19H7, endow19H7]
  · rw [qlClears_two half2_pos (ne_19H7b 1) (pos_19H7b 1) (by simp [endow19H7]; linarith),
      u0_19H7, u1_19H7]
    simp [coef19H7, endow19H7]
    norm_num

/-- **Exercise 19.H.7(c)** (MWG, pp. 730-731). For `ε ≠ 0` the full-information prices
`(1, 6/(6+ε))` differ, so consumer 1 learns the state from them, and they form a rational
expectations equilibrium. -/
theorem exercise_19_H_7c {ε : ℝ} (hε : -6 < ε) (hε0 : ε ≠ 0) :
    IsREE (QLClears half2 coef19H7 (endow19H7 ε)) ![1, 6 / (6 + ε)] sig19H7 := by
  have hne : (1 : ℝ) ≠ 6 / (6 + ε) := by
    rw [ne_eq, eq_div_iff (by linarith)]; intro h; apply hε0; linarith
  have hev : ∀ s, (fun i => reeEvent ![1, 6 / (6 + ε)] sig19H7 i s) = fun _ => {s} := by
    intro s; funext i; ext s'
    fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hne, hne.symm]
  intro s
  rw [hev s]
  fin_cases s
  · exact (exercise_19_H_7a hε).1
  · exact (exercise_19_H_7a hε).2

/-- **Exercise 19.H.7(d)** (MWG, p. 731). If `ε = 0` there is no rational expectations equilibrium
pair of prices: revealing prices would be `(1, 1)`, which do not reveal, and non-revealing prices
would be `(7/6, 5/6)`, which reveal (compare Example 19.H.3). -/
theorem exercise_19_H_7d (P : Fin 2 → ℝ) :
    ¬ IsREE (QLClears half2 coef19H7 (endow19H7 0)) P sig19H7 := by
  intro hP
  have he : ∀ s : Fin 2, 0 < endow19H7 0 0 s + endow19H7 0 1 s := fun s => by
    fin_cases s <;> norm_num [endow19H7]
  by_cases hrev : P 0 = P 1
  · have hev : ∀ s, (fun i => reeEvent P sig19H7 i s) = events19H7b s := by
      intro s; funext i; ext s'
      fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hrev, events19H7b]
    have h0 := hP 0
    have h1 := hP 1
    rw [hev, qlClears_two half2_pos (ne_19H7b 0) (pos_19H7b 0) (he 0), u0_19H7, u1_19H7] at h0
    rw [hev, qlClears_two half2_pos (ne_19H7b 1) (pos_19H7b 1) (he 1), u0_19H7, u1_19H7] at h1
    rw [h0, h1] at hrev
    norm_num [coef19H7, endow19H7] at hrev
  · have hrev' : P 1 ≠ P 0 := Ne.symm hrev
    have hev : ∀ s, (fun i => reeEvent P sig19H7 i s) = fun _ => {s} := by
      intro s; funext i; ext s'
      fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hrev, hrev']
    have c : ∀ i s, postCoef half2 (coef19H7 i) {s} = coef19H7 i s := fun i s =>
      postCoef_singleton half2_pos _ s
    have h0 := hP 0
    have h1 := hP 1
    rw [hev, qlClears_two half2_pos (fun _ => by simp)
      (fun i => by rw [c]; exact coef19H7_pos i 0) (he 0), c, c] at h0
    rw [hev, qlClears_two half2_pos (fun _ => by simp)
      (fun i => by rw [c]; exact coef19H7_pos i 1) (he 1), c, c] at h1
    apply hrev
    rw [h0, h1]
    norm_num [coef19H7, endow19H7]

/-! ## Example 19.H.4 and Exercise 19.H.4 -/

/-- **Footnote 47** (MWG, p. 722). The `2 × 5 × 5 = 50` states `s = (β, ε₁, ε₂)`, coded as
`s = 25 b + 5 k₁ + k₂` with `β = b + 1`, `εᵢ = kᵢ - 2`. -/
def bOf (s : Fin 50) : ℕ := s.val / 25

/-- `εᵢ + 2` in state `s`. -/
def kOf (i : Fin 2) (s : Fin 50) : ℕ := if i = 0 then s.val / 5 % 5 else s.val % 5

/-- **Example 19.H.4** (MWG, p. 722). The signal `σᵢ = β² + εᵢ`. -/
def sig19H4 (i : Fin 2) (s : Fin 50) : ℤ := ((bOf s : ℤ) + 1) ^ 2 + (kOf i s : ℤ) - 2

/-- `β` in state `s`. -/
def beta19H4 (s : Fin 50) : ℝ := (bOf s : ℝ) + 1

/-- The three cases of Example 19.H.4: some `σᵢ ∈ {4, 5, 6}` (`0`), some `σᵢ ∈ {-1, 0, 1}` (`1`),
both `σᵢ ∈ {2, 3}` (`2`). -/
def case19H4 (s : Fin 50) : Fin 3 :=
  if 4 ≤ sig19H4 0 s ∨ 4 ≤ sig19H4 1 s then 0
  else if sig19H4 0 s ≤ 1 ∨ sig19H4 1 s ≤ 1 then 1 else 2

/-- The pooled information price of Example 19.H.4 (correct values for one unit each). -/
noncomputable def price19H4 (s : Fin 50) : ℝ := ![2, 1, 3 / 2] (case19H4 s)

/-- The uniform prior on the 50 states. -/
noncomputable def unif50 : Fin 50 → ℝ := fun _ => 1 / 50

/-- Both consumers have `β ln x₁ + x₂`. -/
def betaBoth19H4 : Fin 2 → Fin 50 → ℝ := fun _ => beta19H4

/-- With a uniform prior, the posterior coefficient is `(n₀ + 2 n₁)/(n₀ + n₁)` where `n_b` counts
the states of the event with `β = b + 1`. -/
theorem postCoef_unif50 (E : Finset (Fin 50)) (hE : E.Nonempty) :
    postCoef unif50 beta19H4 E = (((E.filter fun s => bOf s = 0).card : ℝ) +
      2 * (E.filter fun s => bOf s ≠ 0).card) /
      (((E.filter fun s => bOf s = 0).card : ℝ) + (E.filter fun s => bOf s ≠ 0).card) := by
  have hb : ∀ s : Fin 50, bOf s ≠ 0 → bOf s = 1 := fun s h => by
    have : bOf s < 2 := by unfold bOf; omega
    omega
  unfold postCoef
  rw [← Finset.sum_filter_add_sum_filter_not E (fun s => bOf s = 0),
    ← Finset.sum_filter_add_sum_filter_not E (fun s => bOf s = 0) (f := unif50)]
  have e1 : ∑ x ∈ E.filter (fun s => bOf s = 0), unif50 x * beta19H4 x =
      (1 / 50) * ((E.filter fun s => bOf s = 0).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => by
      simp [unif50, beta19H4, (Finset.mem_filter.mp hs).2]
  have e2 : ∑ x ∈ E.filter (fun s => ¬ bOf s = 0), unif50 x * beta19H4 x =
      (1 / 50) * (2 * ((E.filter fun s => bOf s ≠ 0).card : ℝ)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => by
      simp [unif50, beta19H4, hb s (Finset.mem_filter.mp hs).2]; norm_num
  have e3 : ∀ F : Finset (Fin 50), ∑ x ∈ F, unif50 x = (1 / 50) * (F.card : ℝ) := fun F => by
    simp [unif50, Finset.sum_const]; ring
  rw [e1, e2, e3, e3]
  have hpos : (0 : ℝ) < ((E.filter fun s => bOf s = 0).card : ℝ) +
      (E.filter fun s => bOf s ≠ 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := E) (fun s => bOf s = 0)
    rw [← Nat.cast_add, this]
    exact_mod_cast hE.card_pos
  field_simp

set_option maxRecDepth 100000 in
/-- The decidable facts behind Example 19.H.4: in case (i) every state with the same signal
values has `β = 2`, in case (ii) `β = 1`, and in case (iii) the pooled event has one state with each
value of `β`. -/
theorem facts19H4 :
    (∀ s s' : Fin 50, case19H4 s = 0 → (∀ k, sig19H4 k s' = sig19H4 k s) → bOf s' ≠ 0) ∧
    (∀ s s' : Fin 50, case19H4 s = 1 → (∀ k, sig19H4 k s' = sig19H4 k s) → bOf s' = 0) ∧
    (∀ s : Fin 50, case19H4 s = 2 →
      (((pooledEvent sig19H4 s).filter fun s' => bOf s' = 0).card = 1 ∧
       ((pooledEvent sig19H4 s).filter fun s' => bOf s' ≠ 0).card = 1)) := by
  decide

set_option maxRecDepth 100000 in
/-- The decidable facts behind the rational expectations property: within one case and one own
signal value, case (i) states have `β = 2`, case (ii) states `β = 1`, and in case (iii) the two
values of `β` are equally frequent (two states each). -/
theorem factsREE19H4 :
    (∀ s s' : Fin 50, case19H4 s = 0 → case19H4 s' = 0 → bOf s' ≠ 0) ∧
    (∀ s s' : Fin 50, case19H4 s = 1 → case19H4 s' = 1 → bOf s' = 0) ∧
    (∀ (i : Fin 2) (s : Fin 50), case19H4 s = 2 →
      (((Finset.univ.filter fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s).filter
          fun s' => bOf s' = 0).card = 2 ∧
       ((Finset.univ.filter fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s).filter
          fun s' => bOf s' ≠ 0).card = 2)) ∧
    (∃ s s' : Fin 50, case19H4 s = 2 ∧ case19H4 s' = 2 ∧ sig19H4 0 s ≠ sig19H4 0 s') := by
  decide

theorem price19H4_eq_iff (s s' : Fin 50) :
    price19H4 s' = price19H4 s ↔ case19H4 s' = case19H4 s := by
  unfold price19H4
  constructor
  · intro h
    generalize case19H4 s = a at h
    generalize case19H4 s' = b at h
    fin_cases a <;> fin_cases b <;> first | rfl | (norm_num at h)
  · intro h; rw [h]

/-- The pooled coefficient (and price) of Example 19.H.4 in each case. -/
theorem postCoef_pooled19H4 (s : Fin 50) :
    postCoef unif50 beta19H4 (pooledEvent sig19H4 s) = price19H4 s := by
  obtain ⟨f0, f1, f2⟩ := facts19H4
  have hne := pooledEvent_nonempty sig19H4 s
  have hcase : case19H4 s = 0 ∨ case19H4 s = 1 ∨ case19H4 s = 2 := by
    generalize case19H4 s = a; fin_cases a <;> simp
  rcases hcase with h | h | h
  · rw [postCoef_const (fun _ => by norm_num [unif50]) hne (c := 2) fun s' hs' => by
      have := f0 s s' h (by simpa [pooledEvent] using hs')
      have hb : bOf s' = 1 := by have : bOf s' < 2 := by unfold bOf; omega
                                 omega
      simp [beta19H4, hb]; norm_num]
    simp [price19H4, h]
  · rw [postCoef_const (fun _ => by norm_num [unif50]) hne (c := 1) fun s' hs' => by
      simp [beta19H4, f1 s s' h (by simpa [pooledEvent] using hs')]]
    simp [price19H4, h]
  · rw [postCoef_unif50 _ hne]
    rw [(f2 s h).1, (f2 s h).2]
    simp [price19H4, h]; norm_num

/-- **Example 19.H.4** (MWG, pp. 722-723) and **Exercise 19.H.4**, with the endowments of
Example 19.H.2 (one unit of good 1 each): the pooled information price is `2` in case (i), `1` in
case (ii) and `3/2` in case (iii) (the posterior on `β` stays `1/2`); it is not fully revealing,
yet it is a rational expectations equilibrium price function: the price is a sufficient statistic
for the signals. -/
theorem example_19_H_4 :
    IsPooledPrice (QLClears unif50 betaBoth19H4 (fun _ _ => 1)) price19H4 sig19H4 ∧
      ¬ FullyRevealing price19H4 sig19H4 ∧
      IsREE (QLClears unif50 betaBoth19H4 (fun _ _ => 1)) price19H4 sig19H4 := by
  have hu : ∀ s, 0 < unif50 s := fun _ => by norm_num [unif50]
  have hpr : ∀ s, 0 < price19H4 s := fun s => by
    unfold price19H4; generalize case19H4 s = a; fin_cases a <;> norm_num
  obtain ⟨g0, g1, g2, ⟨s₁, s₂, hs₁, hs₂, hsig⟩⟩ := factsREE19H4
  refine ⟨fun s => ?_, fun hfr => ?_, fun s => ?_⟩
  · have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (pooledEvent sig19H4 s) = price19H4 s :=
      fun _ => postCoef_pooled19H4 s
    rw [qlClears_two hu (fun _ => pooledEvent_nonempty _ _) (fun i => by rw [c]; exact hpr s)
      (by norm_num), c, c]
    ring
  · exact hfr s₁ s₂ ⟨0, hsig⟩ ((price19H4_eq_iff s₂ s₁).mpr (hs₁.trans hs₂.symm))
  · have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (reeEvent price19H4 sig19H4 i s) =
        price19H4 s := by
      intro i
      have hev : reeEvent price19H4 sig19H4 i s = Finset.univ.filter
          fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s := by
        ext s'; simp [reeEvent, price19H4_eq_iff]
      have hne := reeEvent_nonempty price19H4 sig19H4 i s
      rw [hev] at hne ⊢
      have hcase : case19H4 s = 0 ∨ case19H4 s = 1 ∨ case19H4 s = 2 := by
        generalize case19H4 s = a; fin_cases a <;> simp
      rcases hcase with h | h | h
      · rw [postCoef_const hu hne (c := 2) fun s' hs' => by
          have hc := (Finset.mem_filter.mp hs').2.1
          have := g0 s s' h (hc.trans h)
          have hb : bOf s' = 1 := by have : bOf s' < 2 := by unfold bOf; omega
                                     omega
          simp [betaBoth19H4, beta19H4, hb]; norm_num]
        simp [price19H4, h]
      · rw [postCoef_const hu hne (c := 1) fun s' hs' => by
          have hc := (Finset.mem_filter.mp hs').2.1
          simp [betaBoth19H4, beta19H4, g1 s s' h (hc.trans h)]]
        simp [price19H4, h]
      · rw [show betaBoth19H4 i = beta19H4 from rfl, postCoef_unif50 _ hne]
        rw [(g2 i s h).1, (g2 i s h).2]
        simp [price19H4, h]; norm_num
    rw [qlClears_two hu (fun i => reeEvent_nonempty _ _ i s) (fun i => by rw [c]; exact hpr s)
      (by norm_num), c, c]
    ring

/-- **Example 19.H.4**, correction 8: the printed prices `β/2 = 1`, `β/2 = 1/2` and `3/4` are not
the clearing prices with one unit of good 1 per consumer (they are `2`, `1`, `3/2`); they are the
clearing prices when each consumer owns two units. -/
theorem example_19_H_4_printed (s : Fin 50) :
    QLClears unif50 betaBoth19H4 (fun _ _ => 2) s (fun _ => pooledEvent sig19H4 s)
      (price19H4 s / 2) ∧ price19H4 s / 2 ≠ price19H4 s := by
  have hu : ∀ s, 0 < unif50 s := fun _ => by norm_num [unif50]
  have hpr : 0 < price19H4 s := by
    unfold price19H4; generalize case19H4 s = a; fin_cases a <;> norm_num
  have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (pooledEvent sig19H4 s) = price19H4 s :=
    fun _ => postCoef_pooled19H4 s
  refine ⟨?_, by linarith⟩
  rw [qlClears_two hu (fun _ => pooledEvent_nonempty _ _) (fun i => by rw [c]; exact hpr)
    (by norm_num), c, c]
  ring

/-! ## Example 19.H.5 and Exercise 19.H.5 -/

/-- **Example 19.H.5** (MWG, p. 723). With `I` consumers, one unit of good 1 each, utilities
`(β + εᵢ) ln x₁ + x₂` and pooled information (`β` and all `εᵢ` known), the clearing price is
`p̂ = β + (1/I) ∑ εᵢ`. -/
theorem example_19_H_5_pooled {I : ℕ} [NeZero I] {β : ℝ} (hβ : 1 ≤ β) {ε : Fin I → ℝ}
    (hε : ∀ i, |ε i| ≤ 1 / 2) :
    QLSpotEqm (fun i => β + ε i) (fun _ => 1) (β + (∑ i, ε i) / I) := by
  have hI : (0 : ℝ) < I := by exact_mod_cast NeZero.pos I
  rw [qlSpotEqm_iff (fun i => by linarith [(abs_le.mp (hε i)).1]) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact hI)]
  simp [Finset.sum_add_distrib]
  field_simp

/-- **Example 19.H.5** (MWG, p. 723). If at most half of the consumers have noise terms in
`[-1/2, 1/2]` and the others are perfectly informed (`εᵢ = 0`), then `|(1/I) ∑ εᵢ| ≤ 1/4`: the
pooled price is below `1.5` when `β = 1` and above `1.5` when `β = 2`, so it reveals `β`. -/
theorem example_19_H_5_separates {I : ℕ} [NeZero I] {ε : Fin I → ℝ} {N : Finset (Fin I)}
    (hN : 2 * N.card ≤ I) (hε : ∀ i, |ε i| ≤ 1 / 2) (h0 : ∀ i ∉ N, ε i = 0) :
    1 + (∑ i, ε i) / I < 3 / 2 ∧ 3 / 2 < 2 + (∑ i, ε i) / I := by
  have hI : (0 : ℝ) < I := by exact_mod_cast NeZero.pos I
  have hsum : |∑ i, ε i| ≤ N.card / 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ N) (fun i _ hi => h0 i hi)]
    calc |∑ i ∈ N, ε i| ≤ ∑ i ∈ N, |ε i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ N, (1 / 2 : ℝ) := Finset.sum_le_sum fun i _ => hε i
      _ = N.card / 2 := by simp; ring
  have hN' : (N.card : ℝ) / 2 ≤ I / 4 := by
    have : (2 * N.card : ℝ) ≤ I := by exact_mod_cast hN
    linarith
  have hb := abs_le.mp (hsum.trans hN')
  have h1 : (∑ i, ε i) / I ≤ 1 / 4 := by rw [div_le_iff₀ hI]; linarith
  have h2 : -(1 / 4) ≤ (∑ i, ε i) / I := by rw [le_div_iff₀ hI]; linarith
  constructor <;> linarith

/-- **Example 19.H.5** (MWG, p. 723). A consumer who knows `β` and his signal `σᵢ = β² + εᵢ` knows
`εᵢ`; with the price revealing `β`, the consumer's information `(p̂, σᵢ)` determines his pooled
demand coefficient `β + εᵢ`, so his demand at `p̂` is the pooled demand and the pooled
information equilibrium is a rational expectations equilibrium. -/
theorem example_19_H_5_identifies {β β' εi εi' p p' : ℝ} (hβ : β = 1 ∨ β = 2)
    (hβ' : β' = 1 ∨ β' = 2) (hp : β = 1 → p < 3 / 2) (hp2 : β = 2 → 3 / 2 < p)
    (hp' : β' = 1 → p' < 3 / 2) (hp2' : β' = 2 → 3 / 2 < p') (hpp : p = p')
    (hσ : β ^ 2 + εi = β' ^ 2 + εi') : β = β' ∧ β + εi = β' + εi' := by
  have hb : β = β' := by
    rcases hβ with h | h <;> rcases hβ' with h' | h'
    · rw [h, h']
    · have := hp h; have := hp2' h'; linarith
    · have := hp2 h; have := hp' h'; linarith
    · rw [h, h']
  subst hb
  exact ⟨rfl, by linarith⟩

/-- The gain from knowing `εᵢ` (Exercise 19.H.5): `(β + ε) ln((β + ε)/β) - ε`. -/
noncomputable def infoGain (β ε : ℝ) : ℝ := (β + ε) * Real.log ((β + ε) / β) - ε

/-- **Exercise 19.H.5** (MWG, p. 730). At any price `p > 0` and wealth `w`, the realized utility of
a consumer who knows `εᵢ` (demand `(β + ε)/p`) exceeds that of one who only knows `β` (demand
`β/p`) by `infoGain β ε`, independent of `p`, `w` and `I`. -/
theorem infoGain_eq {β ε p w : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) (hp : 0 < p) :
    ((β + ε) * Real.log ((β + ε) / p) + (w - (β + ε))) -
      ((β + ε) * Real.log (β / p) + (w - β)) = infoGain β ε := by
  unfold infoGain
  rw [Real.log_div hpos.ne' hp.ne', Real.log_div hβ.ne' hp.ne', Real.log_div hpos.ne' hβ.ne']
  ring

theorem infoGain_nonneg {β ε : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) : 0 ≤ infoGain β ε := by
  unfold infoGain
  have hx : 0 < (β + ε) / β := div_pos hpos hβ
  have := Real.one_sub_inv_le_log_of_pos hx
  rw [inv_div] at this
  have h2 : (β + ε) * (1 - β / (β + ε)) = ε := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

theorem infoGain_pos {β ε : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) (hε : ε ≠ 0) :
    0 < infoGain β ε := by
  unfold infoGain
  have hx : 0 < β / (β + ε) := div_pos hβ hpos
  have hx1 : β / (β + ε) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hpos.ne']; intro h; apply hε; linarith
  have := Real.log_lt_sub_one_of_pos hx hx1
  rw [Real.log_div hβ.ne' hpos.ne'] at this
  rw [Real.log_div hpos.ne' hβ.ne']
  have h2 : (β + ε) * (β / (β + ε) - 1) = -ε := by field_simp; ring
  nlinarith [mul_lt_mul_of_pos_left this hpos]

theorem continuousOn_infoGain {β : ℝ} (hβ : 1 ≤ β) :
    ContinuousOn (infoGain β) (Set.uIcc (-1 / 2) (1 / 2)) := by
  have hpos : ∀ ε ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2), 0 < β + ε := fun ε hε => by
    rw [Set.uIcc_of_le (by norm_num)] at hε; linarith [hε.1]
  unfold infoGain
  refine ((continuousOn_const.add continuousOn_id).mul ?_).sub continuousOn_id
  exact ((continuousOn_const.add continuousOn_id).div_const β).log fun ε hε =>
    (div_pos (hpos ε hε) (by linarith)).ne'

/-- **Exercise 19.H.5** (MWG, p. 723). With `εᵢ` uniform on `[-1/2, 1/2]` the expected gain from
the private signal, `∫_{-1/2}^{1/2} infoGain β ε dε`, is strictly positive (for `β ≥ 1`). -/
theorem integral_infoGain_pos {β : ℝ} (hβ : 1 ≤ β) :
    0 < ∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain β ε := by
  have hβ0 : 0 < β := by linarith
  have hc := continuousOn_infoGain hβ
  have hint : ∀ a b : ℝ, -1 / 2 ≤ a → a ≤ b → b ≤ 1 / 2 →
      IntervalIntegrable (infoGain β) MeasureTheory.volume a b := fun a b ha hab hb =>
    (hc.mono (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num)]
      exact Set.Icc_subset_Icc ha hb)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hint _ _ le_rfl (by norm_num) (by norm_num)) (hint _ _ (by norm_num) (by norm_num) le_rfl)]
  have h1 : 0 ≤ ∫ ε in (-1 / 2 : ℝ)..0, infoGain β ε :=
    intervalIntegral.integral_nonneg (by norm_num) fun ε hε =>
      infoGain_nonneg hβ0 (by linarith [hε.1])
  have h2 : 0 < ∫ ε in (0 : ℝ)..(1 / 2), infoGain β ε :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _ (by norm_num) (by norm_num) le_rfl)
      (fun ε hε => infoGain_pos hβ0 (by linarith [hε.1]) hε.1.ne') (by norm_num)
  linarith

/-- **Exercise 19.H.5** (MWG, p. 723). There is `δ > 0`, independent of the number `I` of consumers
and of the price `p`, such that a consumer with noise uniform on `[-1/2, 1/2]` who already knows
`β ∈ {1, 2}` strictly gains (in expectation) from buying his signal at cost `δ`. -/
theorem exercise_19_H_5 : ∃ δ > 0, ∀ β : ℝ, (β = 1 ∨ β = 2) →
    δ < ∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain β ε := by
  have ha := integral_infoGain_pos (β := 1) le_rfl
  have hb := integral_infoGain_pos (β := 2) (by norm_num)
  refine ⟨min (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
    (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε) / 2, half_pos (lt_min ha hb), fun β hβ => ?_⟩
  rcases hβ with rfl | rfl
  · linarith [min_le_left (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
      (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε)]
  · linarith [min_le_right (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
      (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε)]

/-! ## Example 19.H.6: the lemons market -/

/-- **Example 19.H.6** (MWG, p. 724). Supply of good units: none if `p < 1`, all `N` if `p > 1`,
anything in `[0, N]` if `p = 1` (good units are worth `1` to sellers); the `N` bad units are always
supplied at `p > 0`. -/
def GoodSupply (N p g : ℝ) : Prop :=
  (p < 1 ∧ g = 0) ∨ (p = 1 ∧ 0 ≤ g ∧ g ≤ N) ∨ (1 < p ∧ g = N)

/-- **Example 19.H.6** (MWG, p. 724). The pair `(α, p)` is admissible: `α = 0` for `p < 1`,
`α ∈ [0, 1/2]` for `p = 1`, `α = 1/2` for `p > 1`. -/
def LemonsAdmissible (α p : ℝ) : Prop :=
  (p < 1 → α = 0) ∧ (p = 1 → 0 ≤ α ∧ α ≤ 1 / 2) ∧ (1 < p → α = 1 / 2)

/-- **Example 19.H.6** (MWG, p. 724). Admissibility is consistency of the state of the market `α`
(the fraction of good units supplied) with the supply decisions. -/
theorem lemons_admissible_iff {N α p : ℝ} (hN : 0 < N) :
    LemonsAdmissible α p ↔ ∃ g, GoodSupply N p g ∧ α = g / (g + N) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_trichotomy p 1 with hp | hp | hp
    · exact ⟨0, Or.inl ⟨hp, rfl⟩, by rw [h1 hp]; simp⟩
    · obtain ⟨ha0, ha1⟩ := h2 hp
      refine ⟨α * N / (1 - α), Or.inr (Or.inl ⟨hp, ?_, ?_⟩), ?_⟩
      · exact div_nonneg (mul_nonneg ha0 hN.le) (by linarith)
      · rw [div_le_iff₀ (by linarith)]; nlinarith
      · have h1α : 1 - α ≠ 0 := by intro h; linarith
        field_simp
        ring
    · exact ⟨N, Or.inr (Or.inr ⟨hp, rfl⟩), by rw [h3 hp]; field_simp; ring⟩
  · rintro ⟨g, hg, rfl⟩
    rcases hg with ⟨hp, rfl⟩ | ⟨hp, hg0, hgN⟩ | ⟨hp, rfl⟩
    · exact ⟨fun _ => by simp, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨fun h => by linarith, fun _ => ⟨by positivity, ?_⟩, fun h => by linarith⟩
      rw [div_le_iff₀ (by linarith)]; linarith
    · exact ⟨fun h => by linarith, fun h => by linarith, fun _ => by field_simp; ring⟩

/-- **Example 19.H.6** (MWG, p. 724). Equivalently, the admissible pairs (with `p > 0`) are
`α = 0, p ≤ 1`; `α ∈ (0, 1/2), p = 1`; and `α = 1/2, p ≥ 1`. -/
theorem lemons_admissible_cases {α p : ℝ} (hα : 0 ≤ α) :
    LemonsAdmissible α p ↔
      (α = 0 ∧ p ≤ 1) ∨ (0 < α ∧ α < 1 / 2 ∧ p = 1) ∨ (α = 1 / 2 ∧ 1 ≤ p) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_trichotomy p 1 with hp | hp | hp
    · exact Or.inl ⟨h1 hp, hp.le⟩
    · obtain ⟨_, ha1⟩ := h2 hp
      rcases hα.lt_or_eq with h | h
      · rcases ha1.lt_or_eq with h' | h'
        · exact Or.inr (Or.inl ⟨h, h', hp⟩)
        · exact Or.inr (Or.inr ⟨h', hp.ge⟩)
      · exact Or.inl ⟨h.symm, hp.le⟩
    · exact Or.inr (Or.inr ⟨h3 hp, hp.le⟩)
  · rintro (⟨rfl, hp⟩ | ⟨h0, h1, rfl⟩ | ⟨rfl, hp⟩)
    · exact ⟨fun _ => rfl, fun _ => ⟨le_rfl, by norm_num⟩, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun _ => ⟨h0.le, h1.le⟩, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun _ => ⟨by norm_num, le_rfl⟩, fun _ => rfl⟩

/-- **Example 19.H.6** (MWG, p. 724). Every admissible pair is a rational expectations equilibrium:
with `N` buyers (each demanding at most one unit, only if `4α - p ≥ 0`) and `2N` sellers, demand is
at most `N`, while at `p > 0` the `N` bad units are always supplied; so demand never exceeds
supply. At `α = 1/2`, `p = 3` no demand is expressed (`4α - p < 0`). -/
theorem example_19_H_6 {N d g : ℝ} (hd : d ≤ N) (hg : 0 ≤ g) :
    d ≤ N + g ∧ 4 * (1 / 2 : ℝ) - 3 < 0 := ⟨by linarith, by norm_num⟩

/-- **Footnote 49** (MWG, p. 724). At `α = 1/2`, `p = 1.5`, every buyer wants a unit
(`4α - p > 0`) and every seller supplies: total supply `2` per buyer, total demand `1`. -/
theorem footnote_19_49 : 0 < 4 * (1 / 2 : ℝ) - 1.5 ∧ LemonsAdmissible (1 / 2) 1.5 ∧
    GoodSupply 1 1.5 1 := by
  refine ⟨by norm_num, ⟨fun h => by norm_num at h, fun h => by norm_num at h, fun _ => rfl⟩,
    Or.inr (Or.inr ⟨by norm_num, rfl⟩)⟩

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 19.F.5 and 19.H.6 (MWG pp. 728-730)

* **Exercise 19.F.5** (insurance with unobservable disability): (a) with a full set of
  Arrow-Debreu markets the allocation equates marginal utilities, `U_a'(c_a) = U_d'(c_d)` and
  `c_a + c_d = k` (`exercise_19_F_5a`); (b) if this gives `c_a > c_d` it is incentive compatible and
  is the competitive outcome with unobservable disability (`exercise_19_F_5b`); (c) if it gives
  `c_a < c_d` it is not reachable, and the best incentive-compatible zero-profit allocation, the
  competitive outcome, is `c_a = c_d = k/2`, which is optimal among the allocations a government
  that cannot observe disability can achieve (`exercise_19_F_5c`).
* **Exercise 19.H.6**: (a) the Arrow-Debreu equilibrium: consumer 2 consumes `1/4` of good 1 in
  every state (`exercise_19_H_6a`); total surplus is maximal exactly when consumer 2's good-1
  consumption is `1/4` in every state (`exercise_19_H_6_surplus`), so allocations where it varies
  across states (as with non-contingent trade in (b), and in (c) within the event `{2, 3}`) are not
  Pareto optimal (`exercise_19_H_6_not_po`), while the allocations of (a) and (d) are.
-/

namespace MWG.EquilibriumUncertainty

/-! ## Exercise 19.F.5 -/

/-- The tangent-line inequality for a strictly concave differentiable function. -/
theorem strictConcave_tangent {D : Set ℝ} {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ D u) {x y a : ℝ}
    (hx : x ∈ D) (hy : y ∈ D) (ha : HasDerivAt u a x) : u y ≤ u x + a * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hu.slope_lt_of_hasDerivAt hx hy h ha
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr h)] at this
    linarith
  · subst h; simp
  · have := hu.lt_slope_of_hasDerivAt hy hx h ha
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr h)] at this
    linarith

/-- Ex ante expected utility `½ U_a(c_a) + ½ U_d(c_d)` of a worker able (probability `1/2`) or
disabled (probability `1/2`). -/
noncomputable def welfare19F5 (Ua Ud : ℝ → ℝ) (ca cd : ℝ) : ℝ := Ua ca / 2 + Ud cd / 2

/-- **Exercise 19.F.5(a)** (MWG, p. 728). With Arrow-Debreu markets open before disability is known
(actuarially fair prices, output `k` per able worker, so `c_a + c_d ≤ k` in expected value), the
equilibrium allocation is the solution of `max ½U_a(c_a) + ½U_d(c_d)`: if `U_a, U_d` are strictly
concave and increasing and `U_a'(c_a) = U_d'(c_d) ≥ 0` with `c_a + c_d = k`, then `(c_a, c_d)` is
optimal. -/
theorem exercise_19_F_5a {Ua Ud : ℝ → ℝ} (hca : StrictConcaveOn ℝ (Set.Ici 0) Ua)
    (hcd : StrictConcaveOn ℝ (Set.Ici 0) Ud) {k ca cd lam : ℝ} (hca0 : 0 ≤ ca) (hcd0 : 0 ≤ cd)
    (hk : ca + cd = k) (hlam : 0 ≤ lam) (hda : HasDerivAt Ua lam ca) (hdd : HasDerivAt Ud lam cd)
    {ya yd : ℝ} (hya : 0 ≤ ya) (hyd : 0 ≤ yd) (hy : ya + yd ≤ k) :
    welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd := by
  have h1 := strictConcave_tangent hca hca0 hya hda
  have h2 := strictConcave_tangent hcd hcd0 hyd hdd
  unfold welfare19F5
  nlinarith

/-- **Exercise 19.F.5(b)** (MWG, p. 728). If disability is unobservable, an able worker can claim
disability and consume `c_d` (with utility `U_a(c_d)`). If the full-insurance allocation of (a) has
`c_a > c_d` (as when `U_a'(c_a) = U_d'(c_d)` implies `c_a > c_d`) and `U_a` is increasing, it is
incentive compatible; being optimal among all feasible allocations it is optimal among the
incentive-compatible zero-profit contracts, i.e. it is the competitive equilibrium. -/
theorem exercise_19_F_5b {Ua Ud : ℝ → ℝ} (hma : StrictMonoOn Ua (Set.Ici 0)) {ca cd : ℝ}
    (hcd0 : 0 ≤ cd) (hgt : cd < ca) (hopt : ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ ca + cd →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd) :
    Ua cd < Ua ca ∧ ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ ca + cd → Ua yd ≤ Ua ya →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud ca cd :=
  ⟨hma (Set.mem_Ici.mpr hcd0) (Set.mem_Ici.mpr (hcd0.trans hgt.le)) hgt,
    fun ya yd hya hyd hy _ => hopt ya yd hya hyd hy⟩

/-- **Exercise 19.F.5(c)** (MWG, pp. 728-729). If the allocation of (a) has `c_a < c_d`, it is not
incentive compatible (an able worker prefers to claim disability), so it is not reachable. If at
equal consumption the disabled have the higher marginal utility (`U_a'(k/2) ≤ U_d'(k/2)`, the
counterpart of "`U_a'(c_a) = U_d'(c_d)` implies `c_a < c_d`"), the best allocation subject to
feasibility and incentive compatibility (`c_a ≥ c_d`) is `c_a = c_d = k/2`: this is the competitive
equilibrium, and it is optimal relative to everything a government that cannot observe disability
can achieve (the same constraints). -/
theorem exercise_19_F_5c {Ua Ud : ℝ → ℝ} (hma : StrictMonoOn Ua (Set.Ici 0))
    (hca : StrictConcaveOn ℝ (Set.Ici 0) Ua) (hcd : StrictConcaveOn ℝ (Set.Ici 0) Ud)
    {k A D : ℝ} (hk : 0 ≤ k) (hA : HasDerivAt Ua A (k / 2)) (hD : HasDerivAt Ud D (k / 2))
    (hA0 : 0 ≤ A) (hAD : A ≤ D) {ca cd : ℝ} (hca0 : 0 ≤ ca) (hlt : ca < cd) :
    Ua ca < Ua cd ∧ ∀ ya yd, 0 ≤ ya → 0 ≤ yd → ya + yd ≤ k → yd ≤ ya →
      welfare19F5 Ua Ud ya yd ≤ welfare19F5 Ua Ud (k / 2) (k / 2) := by
  refine ⟨hma (Set.mem_Ici.mpr hca0) (Set.mem_Ici.mpr (hca0.trans hlt.le)) hlt,
    fun ya yd hya hyd hy hic => ?_⟩
  have hk2 : (0 : ℝ) ≤ k / 2 := by linarith
  have h1 := strictConcave_tangent hca (Set.mem_Ici.mpr hk2) (Set.mem_Ici.mpr hya) hA
  have h2 := strictConcave_tangent hcd (Set.mem_Ici.mpr hk2) (Set.mem_Ici.mpr hyd) hD
  have hbr : A * (ya - k / 2) + D * (yd - k / 2) ≤ 0 := by
    rcases le_or_gt (k / 2) ya with ht | ht
    · nlinarith
    · nlinarith
  unfold welfare19F5
  linarith

/-! ## Exercise 19.H.6 -/

/-- Consumer 1's expected utility `∑_s ⅓ (x_{1s} + x_{2s})` (three equally likely states). -/
noncomputable def U1_19H6 (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * (x s 0 + x s 1)

/-- Consumer 2's expected utility `∑_s ⅓ (√x_{1s} + x_{2s})`. -/
noncomputable def U2_19H6 (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * (√(x s 0) + x s 1)

/-- Endowments: consumer 1 has `ω₂₁` of good 2 in every state; consumer 2 has `w_s` of good 1. -/
def omega19H6 (w21 : ℝ) (w : Fin 3 → ℝ) : Fin 2 → CVec 3 2 :=
  ![fun _ => ![0, w21], fun s => ![w s, 0]]

/-- The Arrow-Debreu allocation of Exercise 19.H.6(a). -/
noncomputable def x19H6 (w21 : ℝ) (w : Fin 3 → ℝ) : Fin 2 → CVec 3 2 :=
  ![fun s => ![w s - 1 / 4, w21 - w s + 1 / 4], fun s => ![1 / 4, w s - 1 / 4]]

theorem sqrt_le_add_quarter (t : ℝ) (ht : 0 ≤ t) : √t ≤ t + 1 / 4 := by
  nlinarith [Real.sq_sqrt ht, sq_nonneg (√t - 1 / 2)]

/-- **Exercise 19.H.6(a)** (MWG, p. 730). With interior parameters (`w_s ≥ 1/4`,
`ω₂₁ ≥ w_s - 1/4`), all contingent prices equal (`1/3`) and the allocation in which consumer 2
consumes `1/4` of good 1 in every state form an Arrow-Debreu equilibrium. -/
theorem exercise_19_H_6a {w21 : ℝ} {w : Fin 3 → ℝ} (hw : ∀ s, 1 / 4 ≤ w s)
    (hw21 : ∀ s, w s - 1 / 4 ≤ w21) :
    IsADEqmU ![U1_19H6, U2_19H6] (omega19H6 w21 w) (x19H6 w21 w) (fun _ _ => 1 / 3) := by
  have hcv : ∀ y : CVec 3 2, cval (fun _ _ => 1 / 3) y = ∑ s, (1 / 3) * (y s 0 + y s 1) := by
    intro y; simp [cval, dotProduct, Fin.sum_univ_two, mul_add]
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hw1 : cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1) = ∑ s, (1 / 3) * w s := by
    rw [hcv]; simp [omega19H6]
  have hx1 : cval (fun _ _ => 1 / 3) (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s := by
    rw [hcv]; simp [x19H6]
  have hw0 : cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0) = w21 := by
    rw [hcv]; simp [omega19H6]
  have hx0 : cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) = w21 := by
    rw [hcv]; simp [x19H6]
  have c0 : (NonnegC (x19H6 w21 w 0) ∧ cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) ≤
      cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0)) ∧ ∀ x', NonnegC x' →
        cval (fun _ _ => 1 / 3) x' ≤ cval (fun _ _ => 1 / 3) (omega19H6 w21 w 0) →
          U1_19H6 x' ≤ U1_19H6 (x19H6 w21 w 0) := by
    refine ⟨⟨fun s l => ?_, by rw [hx0, hw0]⟩, fun x' _ hb => ?_⟩
    · fin_cases l <;> simp [x19H6] <;> linarith [hw s, hw21 s]
    · rw [hw0, hcv] at hb
      have : U1_19H6 (x19H6 w21 w 0) = cval (fun _ _ => 1 / 3) (x19H6 w21 w 0) := by
        rw [hcv]; rfl
      rw [this, hx0]; exact hb
  have c1 : (NonnegC (x19H6 w21 w 1) ∧ cval (fun _ _ => 1 / 3) (x19H6 w21 w 1) ≤
      cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1)) ∧ ∀ x', NonnegC x' →
        cval (fun _ _ => 1 / 3) x' ≤ cval (fun _ _ => 1 / 3) (omega19H6 w21 w 1) →
          U2_19H6 x' ≤ U2_19H6 (x19H6 w21 w 1) := by
    refine ⟨⟨fun s l => ?_, by rw [hx1, hw1]⟩, fun x' hx' hb => ?_⟩
    · fin_cases l
      · simp [x19H6]
      · change (0 : ℝ) ≤ w s - 1 / 4; linarith [hw s]
    · rw [hw1, hcv] at hb
      have hval : U2_19H6 (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s + 1 / 4 := by
        simp only [U2_19H6, x19H6, Matrix.cons_val_one, Matrix.cons_val_zero, hq,
          Fin.sum_univ_three]
        ring
      have h2 : U2_19H6 x' ≤ ∑ s, (1 / 3) * (x' s 0 + x' s 1) + 1 / 4 := by
        calc U2_19H6 x' ≤ ∑ s, ((1 / 3) * (x' s 0 + x' s 1) + 1 / 12) :=
              Finset.sum_le_sum fun s _ => by
                nlinarith [sqrt_le_add_quarter (x' s 0) (hx' s 0)]
          _ = ∑ s, (1 / 3) * (x' s 0 + x' s 1) + 1 / 4 := by
              norm_num [Finset.sum_add_distrib]
      rw [hval]; linarith
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact c0
    · exact c1
  · funext s l
    fin_cases l <;> simp [x19H6, omega19H6, Fin.sum_univ_two]

/-- **Exercise 19.H.6(e)** (MWG, p. 730), the surplus comparison. For any allocation that uses up
the endowments, `U₁ + U₂ = ∑_s ⅓ (w_s + ω₂₁) + ∑_s ⅓ (√y_s - y_s)` where `y_s` is consumer 2's
good-1 consumption: it is at most the value at the Arrow-Debreu allocation, with equality iff
`y_s = 1/4` in every state. -/
theorem exercise_19_H_6_surplus {w21 : ℝ} {w : Fin 3 → ℝ} {x : Fin 2 → CVec 3 2}
    (hx : ∑ i, x i = ∑ i, omega19H6 w21 w i) (hy : ∀ s, 0 ≤ x 1 s 0) :
    U1_19H6 (x 0) + U2_19H6 (x 1) ≤
        U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) ∧
      (U1_19H6 (x 0) + U2_19H6 (x 1) = U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) →
        ∀ s, x 1 s 0 = 1 / 4) := by
  have hc : ∀ s l, x 0 s l + x 1 s l = omega19H6 w21 w 0 s l + omega19H6 w21 w 1 s l := by
    intro s l
    have := congrFun (congrFun hx s) l
    simpa [Fin.sum_univ_two] using this
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have key : U1_19H6 (x19H6 w21 w 0) + U2_19H6 (x19H6 w21 w 1) -
      (U1_19H6 (x 0) + U2_19H6 (x 1)) = ∑ s, (1 / 3) * (√(x 1 s 0) - 1 / 2) ^ 2 := by
    unfold U1_19H6 U2_19H6
    simp only [x19H6, Matrix.cons_val_zero, Matrix.cons_val_one, hq, Fin.sum_univ_three]
    have h0 := hc 0 0; have h1 := hc 0 1; have h2 := hc 1 0; have h3 := hc 1 1
    have h4 := hc 2 0; have h5 := hc 2 1
    simp [omega19H6] at h0 h1 h2 h3 h4 h5
    nlinarith [Real.sq_sqrt (hy 0), Real.sq_sqrt (hy 1), Real.sq_sqrt (hy 2)]
  have hnn : 0 ≤ ∑ s, (1 / 3 : ℝ) * (√(x 1 s 0) - 1 / 2) ^ 2 :=
    Finset.sum_nonneg fun s _ => by positivity
  refine ⟨by linarith, fun heq s => ?_⟩
  have hz : ∑ s, (1 / 3 : ℝ) * (√(x 1 s 0) - 1 / 2) ^ 2 = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => by positivity).mp hz s (Finset.mem_univ s)
  have hs : √(x 1 s 0) = 1 / 2 := by nlinarith [sq_nonneg (√(x 1 s 0) - 1 / 2)]
  have := Real.sq_sqrt (hy s)
  rw [hs] at this
  linarith

/-- **Exercise 19.H.6(b)-(c)** (MWG, p. 730). An allocation in which consumer 2's consumption of
good 1 is not `1/4` in some state (as with non-contingent trade when `w_s` varies, `y_s = w_s + z`)
is not Pareto optimal (when the compensating reallocation keeps consumption nonnegative): giving
consumer 2 `1/4` of good 1 and compensating him in good 2 makes consumer 1 strictly better off. -/
theorem exercise_19_H_6_not_po {w21 : ℝ} {w : Fin 3 → ℝ} {x : Fin 2 → CVec 3 2}
    (hpo : IsParetoOptimalU ![U1_19H6, U2_19H6] (omega19H6 w21 w) x) {s₀ : Fin 3}
    (hne : x 1 s₀ 0 ≠ 1 / 4)
    (hnn : ∀ s, 0 ≤ x 1 s 1 + √(x 1 s 0) - 1 / 2 ∧ 0 ≤ x 0 s 1 - √(x 1 s 0) + 1 / 2 ∧
      1 / 4 ≤ x 0 s 0 + x 1 s 0) : False := by
  obtain ⟨⟨hx, hf⟩, hno⟩ := hpo
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  set x' : Fin 2 → CVec 3 2 :=
    ![fun s => ![x 0 s 0 + x 1 s 0 - 1 / 4, x 0 s 1 - √(x 1 s 0) + 1 / 2],
      fun s => ![1 / 4, x 1 s 1 + √(x 1 s 0) - 1 / 2]] with hx'
  have hsq : √(x 1 s₀ 0) ≠ 1 / 2 := by
    intro h
    have := Real.sq_sqrt (hx 1 s₀ 0)
    rw [h] at this; apply hne; linarith
  refine hno ⟨x', ⟨fun i s l => ?_, fun s l => ?_⟩, fun i => ?_, 0, ?_⟩
  · fin_cases i <;> fin_cases l <;> simp [hx'] <;> linarith [hnn s, hx 0 s 0, hx 1 s 0]
  · have := hf s l
    fin_cases l <;> simp [hx', Fin.sum_univ_two] at this ⊢ <;> linarith
  · fin_cases i
    · change U1_19H6 (x 0) ≤ U1_19H6 (x' 0)
      unfold U1_19H6
      refine Finset.sum_le_sum fun s _ => ?_
      simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (hx 1 s 0), sq_nonneg (√(x 1 s 0) - 1 / 2)]
    · change U2_19H6 (x 1) ≤ U2_19H6 (x' 1)
      unfold U2_19H6
      refine le_of_eq (Finset.sum_congr rfl fun s _ => ?_)
      simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one, hq]
      ring
  · change U1_19H6 (x 0) < U1_19H6 (x' 0)
    unfold U1_19H6
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, Finset.mem_univ _, ?_⟩
    · simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (hx 1 s 0), sq_nonneg (√(x 1 s 0) - 1 / 2)]
    · simp only [hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      have hpos : 0 < (√(x 1 s₀ 0) - 1 / 2) ^ 2 := by
        have : √(x 1 s₀ 0) - 1 / 2 ≠ 0 := sub_ne_zero.mpr hsq
        positivity
      nlinarith [Real.sq_sqrt (hx 1 s₀ 0)]

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 19.F.3: more assets, everybody worse off (MWG p. 728)

* **(a)** A two-consumer, two-good economy with two equally likely states and linear Bernoulli
  utilities (`U19F3`, `omega19F3`). Its spot-market (no-asset, incomplete markets) Radner
  equilibrium (`exercise_19_F_3a_spot`) gives the utilities `(2, 1)`; its Arrow-Debreu (complete
  markets) equilibrium (`exercise_19_F_3a_AD`, also a Radner equilibrium with contingent trade,
  `exercise_19_F_3a_complete_radner`) gives `(3/2, 11/8)`. The sum of utilities is `23/8 < 3`
  (`exercise_19_F_3a`).
* **(b)** The four-state economy (`doubleU19F3`, `double19F3`): states 1, 2 as in (a), states 3, 4
  as in (a) with the roles of the consumers reversed, all equally likely (`exercise_19_F_3b`).
  For an allocation built from an allocation of (a) in the same way, each consumer's utility is
  half the sum of utilities in (a) (`doubleU19F3_double`).
* **(c)** With the single asset `r_A = (-1, -1, 2, 2)` (a transfer of wealth from states 1, 2
  to states 3, 4) the spot allocations of (a) form a Radner equilibrium; adding
  `r_B = (8, -9, 0, 0)` (a transfer between states 1 and 2) and `r_C = (0, 0, 8, -9)` (between
  states 3 and 4), the Arrow-Debreu allocations of (a) form a Radner equilibrium; every
  consumer's utility falls from `3/2` to `23/16` (`exercise_19_F_3c`).

The book speaks of "the" equilibrium; the theorems exhibit the equilibria and compare them
(uniqueness is not claimed). Utilities are linear, so each optimality claim is a linear
programming bound.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## (a): the two-state economy -/

/-- A linear (expected) utility `∑_s ∑_l c_{sl} x_{sl}`; the probabilities are in `c`. -/
def linU {S L : ℕ} (c x : CVec S L) : ℝ := ∑ s, ∑ l, c s l * x s l

/-- Coefficients of Exercise 19.F.3(a), states equally likely: consumer 1 has Bernoulli utility
`x₁ + x₂/2` in both states; consumer 2 has `(3/4) x₁ + x₂` in state 1 and `(1/4) x₁ + x₂` in
state 2 (each multiplied by the probability `1/2`). -/
noncomputable def coef19F3 : Fin 2 → CVec 2 2 :=
  ![![![1 / 2, 1 / 4], ![1 / 2, 1 / 4]], ![![3 / 8, 1 / 2], ![1 / 8, 1 / 2]]]

/-- The utilities of Exercise 19.F.3(a). -/
noncomputable def U19F3 : Fin 2 → CVec 2 2 → ℝ := fun i => linU (coef19F3 i)

/-- Endowments of Exercise 19.F.3(a): consumer 1 owns one unit of good 2 in each state;
consumer 2 owns `1` unit of good 1 in state 1 and `3` units in state 2. -/
def omega19F3 : Fin 2 → CVec 2 2 := ![![![0, 1], ![0, 1]], ![![1, 0], ![3, 0]]]

/-- Spot prices of the no-asset equilibrium (good 1 is the numeraire in each state). -/
def pSpot19F3 : CVec 2 2 := ![![1, 1], ![1, 3]]

/-- The spot (incomplete markets) allocation: consumer 1 gets all of good 1. -/
def xSpot19F3 : Fin 2 → CVec 2 2 := ![![![1, 0], ![3, 0]], ![![0, 1], ![0, 1]]]

/-- Arrow-Debreu prices of Exercise 19.F.3(a). -/
noncomputable def pAD19F3 : CVec 2 2 := ![![9 / 8, 3 / 2], ![1, 3 / 2]]

/-- The Arrow-Debreu (complete markets) allocation: consumer 2 consumes good 1 in state 1. -/
def xAD19F3 : Fin 2 → CVec 2 2 := ![![![0, 0], ![3, 0]], ![![1, 1], ![0, 1]]]

/-- **Exercise 19.F.3(a)** (MWG, p. 728), incomplete markets: with no assets the spot prices
`(1, 1)` and `(1, 3)` and the allocation `xSpot19F3` form a Radner equilibrium. -/
theorem exercise_19_F_3a_spot :
    IsRadnerEqm (0 : Fin 2) (0 : Matrix (Fin 2) (Fin 0) ℝ) U19F3 omega19F3 Fin.elim0 pSpot19F3
      xSpot19F3 (fun _ => Fin.elim0) := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => k.elim0,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;> simp [xSpot19F3]
  · fin_cases i <;> fin_cases s <;> simp [xSpot19F3, omega19F3, pSpot19F3, dotProduct]
  · obtain ⟨hx, -, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      simp [pSpot19F3, omega19F3, dotProduct, Fin.sum_univ_two] at h0 h1
      simp [U19F3, linU, coef19F3, xSpot19F3, Fin.sum_univ_two]
      linarith
  · simp only [xSpot19F3, Finset.sum_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
      Fin.isValue, cons_val_zero, cons_val_one, omega19F3]
    fin_cases s <;> fin_cases l <;> simp

/-- **Exercise 19.F.3(a)** (MWG, p. 728), complete markets: the prices `pAD19F3` and the
allocation `xAD19F3` form an Arrow-Debreu equilibrium. -/
theorem exercise_19_F_3a_AD : IsADEqmU U19F3 omega19F3 xAD19F3 pAD19F3 := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_⟩, fun x' hx hb => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;> simp [xAD19F3]
  · fin_cases i <;> norm_num [cval, xAD19F3, omega19F3, pAD19F3, dotProduct]
  · have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    fin_cases i <;>
    · simp [cval, pAD19F3, omega19F3, dotProduct, Fin.sum_univ_two] at hb
      simp [U19F3, linU, coef19F3, xAD19F3, Fin.sum_univ_two]
      linarith
  · funext s l
    simp only [xAD19F3, Finset.sum_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
        Fin.isValue, cons_val_zero, cons_val_one, omega19F3]
    fin_cases s <;> fin_cases l <;> simp

/-- **Exercise 19.F.3(a)** (MWG, p. 728), complete markets as a Radner equilibrium: with trade in
the contingent commodities `(good 1, s)` at prices `q_s = p_{1s}` (Proposition 19.D.1(i)). -/
theorem exercise_19_F_3a_complete_radner :
    IsRadnerEqmD (0 : Fin 2) U19F3 omega19F3 (fun s => pAD19F3 s 0) pAD19F3 xAD19F3
      (fun i s => pAD19F3 s ⬝ᵥ (xAD19F3 i s - omega19F3 i s) / pAD19F3 s 0) :=
  proposition_19_D_1_i 0 (fun s => by fin_cases s <;> simp [pAD19F3]) exercise_19_F_3a_AD

/-- **Exercise 19.F.3(a)** (MWG, p. 728). The utilities are `(2, 1)` at the spot (incomplete
markets) equilibrium and `(3/2, 11/8)` at the Arrow-Debreu (complete markets) equilibrium: the sum
of utilities with complete markets, `23/8`, is smaller than with incomplete markets, `3`. -/
theorem exercise_19_F_3a :
    U19F3 0 (xSpot19F3 0) = 2 ∧ U19F3 1 (xSpot19F3 1) = 1 ∧
      U19F3 0 (xAD19F3 0) = 3 / 2 ∧ U19F3 1 (xAD19F3 1) = 11 / 8 ∧
      U19F3 0 (xAD19F3 0) + U19F3 1 (xAD19F3 1) <
        U19F3 0 (xSpot19F3 0) + U19F3 1 (xSpot19F3 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [U19F3, linU, coef19F3, xSpot19F3, xAD19F3, Fin.sum_univ_two] <;> norm_num

/-! ## (b): the four-state economy -/

/-- States 1, 2 of a four-state contingent vector. -/
def firstHalf19F3 {L : ℕ} (x : CVec 4 L) : CVec 2 L := fun s => x (Fin.castAdd 2 s)

/-- States 3, 4 of a four-state contingent vector. -/
def secondHalf19F3 {L : ℕ} (x : CVec 4 L) : CVec 2 L := fun s => x (Fin.natAdd 2 s)

/-- Exercise 19.F.3(b): from data `y` of the two-state economy (endowments, allocations), the
four-state data in which states 1, 2 are as in (a) and in states 3, 4 the roles of the two
consumers are reversed. -/
def double19F3 {L : ℕ} (y : Fin 2 → CVec 2 L) : Fin 2 → CVec 4 L :=
  ![Fin.append (y 0) (y 1), Fin.append (y 1) (y 0)]

/-- Exercise 19.F.3(b): the utilities of the four-state economy, four equally likely states.
Consumer 1 evaluates states 1, 2 as consumer 1 of (a) and states 3, 4 as consumer 2 of (a), and
vice versa; the factor `1/2` turns the probabilities `1/2` of (a) into `1/4`. -/
noncomputable def doubleU19F3 {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) : Fin 2 → CVec 4 L → ℝ :=
  ![fun x => (U 0 (firstHalf19F3 x) + U 1 (secondHalf19F3 x)) / 2,
    fun x => (U 1 (firstHalf19F3 x) + U 0 (secondHalf19F3 x)) / 2]

theorem append4_zero {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 0 = a 0 :=
  rfl

theorem append4_one {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 1 = a 1 :=
  rfl

theorem append4_two {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 2 = b 0 :=
  rfl

theorem append4_three {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 3 = b 1 :=
  rfl

/-- **Exercise 19.F.3(b)** (MWG, p. 728). The four-state economy built from (a): in states 1, 2
each consumer has his own endowment of (a), in states 3, 4 the other consumer's; and each
consumer's utility is the expected utility, with probability `1/4` per state, of the Bernoulli
utilities of his own role of (a) in states 1, 2 and of the other role in states 3, 4. -/
theorem exercise_19_F_3b {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) (ω : Fin 2 → CVec 2 L) :
    (firstHalf19F3 (double19F3 ω 0) = ω 0 ∧ secondHalf19F3 (double19F3 ω 0) = ω 1 ∧
      firstHalf19F3 (double19F3 ω 1) = ω 1 ∧ secondHalf19F3 (double19F3 ω 1) = ω 0) ∧
    ∀ x, doubleU19F3 U 0 x = (U 0 (firstHalf19F3 x) + U 1 (secondHalf19F3 x)) / 2 ∧
      doubleU19F3 U 1 x = (U 1 (firstHalf19F3 x) + U 0 (secondHalf19F3 x)) / 2 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun x => ⟨rfl, rfl⟩⟩ <;>
    · funext s; fin_cases s <;> rfl

/-- Exercise 19.F.3(b): with the coefficients of (a), the four-state utilities are linear
expected utilities, `1/4` times the Bernoulli coefficients of the role in each state. -/
theorem doubleU19F3_linU (i : Fin 2) (x : CVec 4 2) :
    doubleU19F3 U19F3 i x = linU ((1 / 2 : ℝ) • double19F3 coef19F3 i) x := by
  fin_cases i <;>
  · simp [doubleU19F3, U19F3, linU, Fin.sum_univ_two, Fin.sum_univ_four, firstHalf19F3,
      secondHalf19F3, double19F3, coef19F3, append4_zero, append4_one, append4_two,
      append4_three]
    ring

/-- Exercise 19.F.3(b): for four-state allocations built from an allocation `y` of (a), every
consumer's utility is half the sum of the utilities of `y` in (a). -/
theorem doubleU19F3_double {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) (y : Fin 2 → CVec 2 L)
    (i : Fin 2) : doubleU19F3 U i (double19F3 y i) = (U 0 (y 0) + U 1 (y 1)) / 2 := by
  have h0 : firstHalf19F3 (double19F3 y 0) = y 0 := by
    funext s; fin_cases s <;> rfl
  have h1 : secondHalf19F3 (double19F3 y 0) = y 1 := by
    funext s; fin_cases s <;> rfl
  have h2 : firstHalf19F3 (double19F3 y 1) = y 1 := by
    funext s; fin_cases s <;> rfl
  have h3 : secondHalf19F3 (double19F3 y 1) = y 0 := by
    funext s; fin_cases s <;> rfl
  fin_cases i
  · change (U 0 (firstHalf19F3 (double19F3 y 0)) + U 1 (secondHalf19F3 (double19F3 y 0))) / 2 = _
    rw [h0, h1]
  · change (U 1 (firstHalf19F3 (double19F3 y 1)) + U 0 (secondHalf19F3 (double19F3 y 1))) / 2 = _
    rw [h2, h3, add_comm]

/-! ## (c): one asset versus three assets -/

/-- Exercise 19.F.3(c): the single asset `r_A = (-1, -1, 2, 2)`, which transfers wealth (in
good 1) from states 1, 2 to states 3, 4. -/
def R1_19F3 : Matrix (Fin 4) (Fin 1) ℝ := Matrix.of ![![-1], ![-1], ![2], ![2]]

/-- Exercise 19.F.3(c): `r_A` together with `r_B = (8, -9, 0, 0)` (a transfer between states 1
and 2) and `r_C = (0, 0, 8, -9)` (a transfer between states 3 and 4). -/
def R3_19F3 : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of ![![-1, 8, 0], ![-1, -9, 0], ![2, 0, 8], ![2, 0, -9]]

/-- Spot prices of the Arrow-Debreu equilibrium of (a), good 1 as numeraire in each state. -/
noncomputable def pADspot19F3 : CVec 2 2 := ![![1, 4 / 3], ![1, 3 / 2]]

/-- Asset trades in the three-asset equilibrium. -/
noncomputable def z3_19F3 : Fin 2 → Fin 3 → ℝ := ![![0, -1 / 6, 1 / 6], ![0, 1 / 6, -1 / 6]]

/-- **Exercise 19.F.3(c)** (MWG, p. 728), the single asset: at asset price `q_A = 1` and the spot
prices of (a) in each half, no asset trade and the spot allocations of (a) (consumer `i`'s role
in each half) form a Radner equilibrium of the four-state economy. -/
theorem exercise_19_F_3c_one :
    IsRadnerEqm (0 : Fin 2) R1_19F3 (doubleU19F3 U19F3) (double19F3 omega19F3) ![1]
      (Fin.append pSpot19F3 pSpot19F3) (double19F3 xSpot19F3) (fun _ _ => 0) := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => by simp,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;>
      simp [double19F3, xSpot19F3, append4_zero, append4_one, append4_two, append4_three]
  · fin_cases i <;> fin_cases s <;>
      norm_num [double19F3, xSpot19F3, omega19F3, pSpot19F3, dotProduct, append4_zero,
        append4_one, append4_two, append4_three, Matrix.mulVec]
  · obtain ⟨hx, hq, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    have n20 := hx 2 0; have n21 := hx 2 1; have n30 := hx 3 0; have n31 := hx 3 1
    simp [dotProduct] at hq
    rw [doubleU19F3_linU, doubleU19F3_linU]
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      have h2 := hb 2
      have h3 := hb 3
      simp [pSpot19F3, omega19F3, double19F3, dotProduct, Fin.sum_univ_two, R1_19F3,
        Matrix.mulVec, append4_zero, append4_one, append4_two, append4_three] at h0 h1 h2 h3
      simp [linU, coef19F3, xSpot19F3, double19F3, Fin.sum_univ_two, Fin.sum_univ_four,
        append4_zero, append4_one, append4_two, append4_three]
      linarith
  · fin_cases s <;> fin_cases l <;>
      norm_num [double19F3, xSpot19F3, omega19F3, Fin.sum_univ_two, append4_zero, append4_one,
        append4_two, append4_three]

/-- **Exercise 19.F.3(c)** (MWG, p. 728), three assets: at asset prices `(1, 0, 0)` and the
spot-normalized Arrow-Debreu prices of (a) in each half, the trades `z3_19F3` (only in `r_B`,
`r_C`) and the Arrow-Debreu allocations of (a) form a Radner equilibrium of the four-state
economy. -/
theorem exercise_19_F_3c_three :
    IsRadnerEqm (0 : Fin 2) R3_19F3 (doubleU19F3 U19F3) (double19F3 omega19F3) ![1, 0, 0]
      (Fin.append pADspot19F3 pADspot19F3) (double19F3 xAD19F3) z3_19F3 := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => ?_,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;>
      simp [double19F3, xAD19F3, append4_zero, append4_one, append4_two, append4_three]
  · fin_cases i <;> simp [z3_19F3, dotProduct, Fin.sum_univ_three]
  · fin_cases i <;> fin_cases s <;>
      norm_num [double19F3, xAD19F3, omega19F3, pADspot19F3, dotProduct, append4_zero,
        append4_one, append4_two, append4_three, R3_19F3, Matrix.mulVec, z3_19F3,
        Fin.sum_univ_three]
  · obtain ⟨hx, hq, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    have n20 := hx 2 0; have n21 := hx 2 1; have n30 := hx 3 0; have n31 := hx 3 1
    simp [dotProduct, Fin.sum_univ_three] at hq
    rw [doubleU19F3_linU, doubleU19F3_linU]
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      have h2 := hb 2
      have h3 := hb 3
      simp [pADspot19F3, omega19F3, double19F3, dotProduct, Fin.sum_univ_two, R3_19F3,
        Matrix.mulVec, Fin.sum_univ_three, append4_zero, append4_one, append4_two,
        append4_three] at h0 h1 h2 h3
      simp [linU, coef19F3, xAD19F3, double19F3, Fin.sum_univ_two, Fin.sum_univ_four,
        append4_zero, append4_one, append4_two, append4_three]
      linarith
  · fin_cases k <;> norm_num [z3_19F3, Fin.sum_univ_two]
  · fin_cases s <;> fin_cases l <;>
      norm_num [double19F3, xAD19F3, omega19F3, Fin.sum_univ_two, append4_zero, append4_one,
        append4_two, append4_three]

/-- **Exercise 19.F.3(c)** (MWG, p. 728). The single-asset equilibrium is better for every
consumer than the equilibrium after the two new assets are added: each consumer's utility is
`3/2` with one asset and `23/16` with three (half the sums `3` and `23/8` of (a)). -/
theorem exercise_19_F_3c (i : Fin 2) :
    doubleU19F3 U19F3 i (double19F3 xSpot19F3 i) = 3 / 2 ∧
      doubleU19F3 U19F3 i (double19F3 xAD19F3 i) = 23 / 16 ∧
      doubleU19F3 U19F3 i (double19F3 xAD19F3 i) <
        doubleU19F3 U19F3 i (double19F3 xSpot19F3 i) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := exercise_19_F_3a
  rw [doubleU19F3_double, doubleU19F3_double, h1, h2, h3, h4]
  norm_num

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 19.H.6(b)-(e): non-contingent markets and the value of information (MWG p. 730)

Consumer 1 has `u₁ = x₁₁ + x₂₁` and `ω₂₁` units of good 2; consumer 2 has `u₂ = √x₁₂ + x₂₂` and
`w_s` units of good 1 in state `s` (three equally likely states).

* **(b), (c)**: trade in non-contingent deliveries within an event `E` of states that the
  consumers know (`E` = all states in (b); `{1}` and `{2, 3}` in (c)) is `IsNCEqm19H6`. If `t ≤ 0`
  solves `∑_{s ∈ E} 1/√(w_s + t) = 2|E|`, the prices `(1, 1)` and the trades `(-t, t)` for
  consumer 1 and `(t, -t)` for consumer 2 form an equilibrium (`ncEqm19H6`): consumer 2's
  good-1 consumption is `w_s + t`, which varies with `s` when `w_s` does, so the allocation of (b)
  is not Pareto optimal (`exercise_19_H_6b_not_po` in the instance). In (c), after state 1,
  `t = 1/4 - w₁`.
* **(d)**: contingent trade within an event: prices `1` and the allocation of (a) form an
  equilibrium in every event (`cEqm19H6`).
* **(e)**: consumer 1's ex ante utility is `ω₂₁` in all four equilibria; consumer 2's satisfies
  `(b) ≤ (c) ≤ (a) = (d) = ∑_s w_s/3 + 1/4` (`exercise_19_H_6e`). So the information of (c) is
  (weakly) socially valuable with non-contingent markets, and the information of (d) has no value
  with contingent markets (the allocation is that of (a)).
* An instance with every equilibrium in closed form (`w = (1205/1156, 13/4, 541/100)`,
  `ω₂₁ = 6`): `t = -1` in (b), `t = -229/289` and `t = -79/25` in (c); consumer 2's ex ante
  utilities are strictly increasing from (b) to (c) to (a) (`exercise_19_H_6_instance`).

The equilibria are constructed (sufficiency); uniqueness is not claimed.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-- The Bernoulli utilities of Exercise 19.H.6: `u₁(y) = y₁ + y₂`, `u₂(y) = √y₁ + y₂`. -/
noncomputable def bern19H6 : Fin 2 → (Fin 2 → ℝ) → ℝ :=
  ![fun y => y 0 + y 1, fun y => √(y 0) + y 1]

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730): the budget for non-contingent trade `τ` (a net
trade of the two goods, delivered whatever the state) at prices `P`, when the consumers know that
the state is in `E`: `P·τ ≤ 0` and `ωᵢₛ + τ ≥ 0` for every `s ∈ E`. -/
def ncFeasible19H6 (E : Finset (Fin 3)) (P : Fin 2 → ℝ) (ωi : CVec 3 2) (τ : Fin 2 → ℝ) :
    Prop :=
  P ⬝ᵥ τ ≤ 0 ∧ ∀ s ∈ E, ∀ l, 0 ≤ ωi s l + τ l

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730): equilibrium with non-contingent markets within the
event `E` (the conditional expected utility is proportional to the sum over `E`). -/
def IsNCEqm19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (E : Finset (Fin 3)) (P : Fin 2 → ℝ)
    (τ : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ i, ncFeasible19H6 E P (omega19H6 w21 w i) (τ i) ∧
    ∀ τ', ncFeasible19H6 E P (omega19H6 w21 w i) τ' →
      ∑ s ∈ E, bern19H6 i (omega19H6 w21 w i s + τ') ≤
        ∑ s ∈ E, bern19H6 i (omega19H6 w21 w i s + τ i)) ∧
    ∑ i, τ i = 0

/-- The trades `(-t, t)` (consumer 1) and `(t, -t)` (consumer 2). -/
def ncTrade19H6 (t : ℝ) : Fin 2 → Fin 2 → ℝ := ![![-t, t], ![t, -t]]

/-- The tangent-line bound for `√`: `√a ≤ √b + (a - b)/2 · (1/√b)` for `a ≥ 0`, `b > 0`. -/
theorem sqrt_le_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    √a ≤ √b + (a - b) / 2 * (1 / √b) := by
  have hs : 0 < √b := Real.sqrt_pos.mpr hb
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb.le
  have : √a - √b ≤ (a - b) / 2 * (1 / √b) := by
    rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (√a - √b)]
  linarith

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730), the equilibrium problem solved. If `t ≤ 0` solves
consumer 2's first-order condition `∑_{s ∈ E} 1/√(w_s + t) = 2|E|` (with `w_s + t > 0` on `E`)
and consumer 1 can deliver `-t` of good 2, then prices `(1, 1)` and the trades
`ncTrade19H6 t` form an equilibrium with non-contingent markets within `E`. -/
theorem ncEqm19H6 {w21 t : ℝ} {w : Fin 3 → ℝ} {E : Finset (Fin 3)} (ht : t ≤ 0)
    (hw21 : 0 ≤ w21 + t) (hy : ∀ s ∈ E, 0 < w s + t)
    (hfoc : ∑ s ∈ E, 1 / √(w s + t) = 2 * E.card) :
    IsNCEqm19H6 w21 w E ![1, 1] (ncTrade19H6 t) := by
  refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, ?_⟩
  · · refine ⟨⟨by simp [ncTrade19H6, dotProduct], fun s _ l => ?_⟩, fun τ' hf => ?_⟩
      · fin_cases l <;> simp [omega19H6, ncTrade19H6] <;> linarith
      · have hb := hf.1
        simp [dotProduct] at hb
        refine Finset.sum_le_sum fun s _ => ?_
        simp [bern19H6, omega19H6, ncTrade19H6, Matrix.vecHead, Matrix.vecTail]
        linarith
  · · refine ⟨⟨by simp [ncTrade19H6, dotProduct], fun s hs l => ?_⟩, fun τ' hf => ?_⟩
      · fin_cases l <;> simp [omega19H6, ncTrade19H6] <;> linarith [hy s hs]
      · obtain ⟨hb, hnn⟩ := hf
        simp only [dotProduct, Fin.sum_univ_two, Fin.isValue, cons_val_zero, one_mul, cons_val_one,
            cons_val_fin_one] at hb
        have key : ∀ s ∈ E, bern19H6 1 (omega19H6 w21 w 1 s + τ') ≤
            (√(w s + t) - t) + ((τ' 0 - t) / 2 * (1 / √(w s + t)) + (τ' 1 + t)) := by
          intro s hs
          have h0 := hnn s hs 0
          simp only [omega19H6, Fin.isValue, cons_val', Nat.succ_eq_add_one, Nat.reduceAdd,
              cons_val_fin_one, cons_val_zero, cons_val_one] at h0
          have := sqrt_le_tangent h0 (hy s hs)
          rw [show w s + τ' 0 - (w s + t) = τ' 0 - t by ring, one_div] at this
          simp [bern19H6, omega19H6, Matrix.vecHead, Matrix.vecTail]
          linarith
        have hval : ∀ s ∈ E, bern19H6 1 (omega19H6 w21 w 1 s + ncTrade19H6 t 1) =
            √(w s + t) - t := by
          intro s _
          simp [bern19H6, omega19H6, ncTrade19H6]
          ring
        rw [Finset.sum_congr rfl hval]
        refine (Finset.sum_le_sum key).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hfoc,
          Finset.sum_const, nsmul_eq_mul]
        have hc : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
        nlinarith
  · funext l
    fin_cases l <;> simp [ncTrade19H6]

/-- **Exercise 19.H.6(d)** (and (a)) (MWG, p. 730): contingent trade within the event `E`, at
contingent prices `p` (only the states of `E` are traded). -/
def IsCEqm19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (E : Finset (Fin 3)) (p : CVec 3 2)
    (x : Fin 2 → CVec 3 2) : Prop :=
  (∀ i, ((∀ s ∈ E, ∀ l, 0 ≤ x i s l) ∧
      ∑ s ∈ E, p s ⬝ᵥ (x i s - omega19H6 w21 w i s) ≤ 0) ∧
    ∀ x' : CVec 3 2, (∀ s ∈ E, ∀ l, 0 ≤ x' s l) →
      ∑ s ∈ E, p s ⬝ᵥ (x' s - omega19H6 w21 w i s) ≤ 0 →
        ∑ s ∈ E, bern19H6 i (x' s) ≤ ∑ s ∈ E, bern19H6 i (x i s)) ∧
    ∀ s ∈ E, ∑ i, x i s = ∑ i, omega19H6 w21 w i s

/-- **Exercise 19.H.6(d)** (MWG, p. 730). After the information is revealed, contingent trade
within either event (`{1}` or `{2, 3}`) at prices `1` gives the allocation of (a), in which
consumer 2 consumes `1/4` of good 1 in every state (interior parameters on `E`). -/
theorem cEqm19H6 {w21 : ℝ} {w : Fin 3 → ℝ} {E : Finset (Fin 3)} (hw : ∀ s ∈ E, 1 / 4 ≤ w s)
    (hw21 : ∀ s ∈ E, w s - 1 / 4 ≤ w21) :
    IsCEqm19H6 w21 w E (fun _ _ => 1) (x19H6 w21 w) := by
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun i => ?_, fun s _ => ?_⟩
  · fin_cases i
    · refine ⟨⟨fun s hs l => ?_, ?_⟩, fun x' _ hb => ?_⟩
      · fin_cases l <;> simp [x19H6] <;> linarith [hw s hs, hw21 s hs]
      · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
        simp [x19H6, omega19H6, dotProduct]
      · simp only [dotProduct, Fin.sum_univ_two, one_mul] at hb
        refine le_of_sub_nonpos ?_
        rw [← Finset.sum_sub_distrib]
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_)) hb
        simp [bern19H6, x19H6, omega19H6]
        ring
    · refine ⟨⟨fun s hs l => ?_, ?_⟩, fun x' hx' hb => ?_⟩
      · fin_cases l
        · simp [x19H6]
        · simp [x19H6]; linarith [hw s hs]
      · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
        simp [x19H6, omega19H6, dotProduct]
      · simp only [dotProduct, Fin.sum_univ_two, one_mul] at hb
        refine le_of_sub_nonpos ?_
        rw [← Finset.sum_sub_distrib]
        refine le_trans (Finset.sum_le_sum fun s hs => ?_) hb
        have := sqrt_le_add_quarter (x' s 0) (hx' s hs 0)
        simp [bern19H6, x19H6, omega19H6]
        linarith
  · funext l
    fin_cases l <;> simp [x19H6, omega19H6, Fin.sum_univ_two]

/-- Ex ante expected utility `∑_s ⅓ uᵢ(x_s)` in Exercise 19.H.6. -/
noncomputable def exAnte19H6 (i : Fin 2) (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * bern19H6 i (x s)

/-- The allocation of (b): `ωᵢₛ + τᵢ` with the trades `ncTrade19H6 t`. -/
def xB19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (t : ℝ) : Fin 2 → CVec 3 2 :=
  fun i s => omega19H6 w21 w i s + ncTrade19H6 t i

/-- The allocation of (c): after state 1 the trade `ncTrade19H6 (1/4 - w₁)`, after `{2, 3}` the
trade `ncTrade19H6 t'`. -/
noncomputable def xC19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (t' : ℝ) : Fin 2 → CVec 3 2 :=
  fun i s => omega19H6 w21 w i s + ncTrade19H6 (if s = 0 then 1 / 4 - w 0 else t') i

/-- **Exercise 19.H.6(e)** (MWG, p. 730). Ex ante utilities in the equilibria of (a)-(d):
consumer 1 obtains `ω₂₁` in all of them (the allocation of (a) is also that of (d)); consumer 2
obtains `∑_s w_s/3 + 1/4` in (a) and (d), and less in (c), and less again in (b). Hence
information in (c) is socially valuable (weakly Pareto improving) relative to (b), while with
contingent markets (d) it has no value relative to (a). Only consumer 2's first-order condition
in the event `{2, 3}` of (c) is used. -/
theorem exercise_19_H_6e {w21 t t' : ℝ} {w : Fin 3 → ℝ} (hy : ∀ s, 0 ≤ w s + t)
    (hy1 : 0 < w 1 + t') (hy2 : 0 < w 2 + t')
    (hfoc : 1 / √(w 1 + t') + 1 / √(w 2 + t') = 4) :
    exAnte19H6 0 (xB19H6 w21 w t 0) = w21 ∧ exAnte19H6 0 (xC19H6 w21 w t' 0) = w21 ∧
      exAnte19H6 0 (x19H6 w21 w 0) = w21 ∧
      exAnte19H6 1 (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s + 1 / 4 ∧
      exAnte19H6 1 (xB19H6 w21 w t 1) ≤ exAnte19H6 1 (xC19H6 w21 w t' 1) ∧
      exAnte19H6 1 (xC19H6 w21 w t' 1) ≤ exAnte19H6 1 (x19H6 w21 w 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [exAnte19H6, bern19H6, xB19H6, omega19H6, ncTrade19H6]
  · simp [exAnte19H6, bern19H6, xC19H6, omega19H6, ncTrade19H6]
  · simp [exAnte19H6, bern19H6, x19H6]
  · simp [exAnte19H6, bern19H6, x19H6, Fin.sum_univ_three]; ring
  · have t1 := sqrt_le_tangent (hy 1) hy1
    have t2 := sqrt_le_tangent (hy 2) hy2
    have q0 := sqrt_le_add_quarter (w 0 + t) (hy 0)
    have hsum : (w 1 + t - (w 1 + t')) / 2 * (1 / √(w 1 + t')) +
        (w 2 + t - (w 2 + t')) / 2 * (1 / √(w 2 + t')) = 2 * (t - t') := by
      rw [show w 1 + t - (w 1 + t') = t - t' by ring, show w 2 + t - (w 2 + t') = t - t' by ring,
        ← mul_add, hfoc]
      ring
    simp [exAnte19H6, bern19H6, xB19H6, xC19H6, omega19H6, ncTrade19H6, Fin.sum_univ_three]
    linarith
  · have q1 := sqrt_le_add_quarter (w 1 + t') hy1.le
    have q2 := sqrt_le_add_quarter (w 2 + t') hy2.le
    simp [exAnte19H6, bern19H6, xC19H6, x19H6, omega19H6, ncTrade19H6, Fin.sum_univ_three]
    linarith

/-! ## An instance with every equilibrium in closed form -/

/-- Consumer 2's good-1 endowments of the instance: `(1205/1156, 13/4, 541/100)`. -/
noncomputable def wInst19H6 : Fin 3 → ℝ := ![1205 / 1156, 13 / 4, 541 / 100]

theorem wInst19H6_sqrt :
    √(wInst19H6 0 + -1) = 7 / 34 ∧ √(wInst19H6 1 + -1) = 3 / 2 ∧
      √(wInst19H6 2 + -1) = 21 / 10 ∧ √(wInst19H6 1 + -79 / 25) = 3 / 10 ∧
      √(wInst19H6 2 + -79 / 25) = 3 / 2 ∧ √(wInst19H6 0 + (1 / 4 - wInst19H6 0)) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show wInst19H6 0 + -1 = (7 / 34) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 1 + -1 = (3 / 2) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 2 + -1 = (21 / 10) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 1 + -79 / 25 = (3 / 10) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 2 + -79 / 25 = (3 / 2) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 0 + (1 / 4 - wInst19H6 0) = (1 / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by norm_num)

/-- **Exercise 19.H.6(b)-(e)** (MWG, p. 730), an instance computed in closed form (`ω₂₁ = 6`,
`w = (1205/1156, 13/4, 541/100)`, interior for (a)). (b): `t = -1`, so consumer 2 consumes
`(49/1156, 9/4, 441/100)` of good 1. (c): after state 1, `t = 1/4 - w₁ = -229/289`; after
`{2, 3}`, `t = -79/25`, so he consumes `(1/4, 9/100, 9/4)`. (d): the allocation of (a) in both
events. Consumer 2's ex ante utility rises strictly from (b) to (c) to (a) = (d). -/
theorem exercise_19_H_6_instance :
    IsNCEqm19H6 6 wInst19H6 Finset.univ ![1, 1] (ncTrade19H6 (-1)) ∧
      IsNCEqm19H6 6 wInst19H6 {0} ![1, 1] (ncTrade19H6 (1 / 4 - wInst19H6 0)) ∧
      IsNCEqm19H6 6 wInst19H6 {1, 2} ![1, 1] (ncTrade19H6 (-79 / 25)) ∧
      IsCEqm19H6 6 wInst19H6 {0} (fun _ _ => 1) (x19H6 6 wInst19H6) ∧
      IsCEqm19H6 6 wInst19H6 {1, 2} (fun _ _ => 1) (x19H6 6 wInst19H6) ∧
      exAnte19H6 1 (xB19H6 6 wInst19H6 (-1) 1) < exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ∧
      exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) < exAnte19H6 1 (x19H6 6 wInst19H6 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := wInst19H6_sqrt
  have h4' : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hw : ∀ s, 1 / 4 ≤ wInst19H6 s := by
    intro s; fin_cases s <;> norm_num [wInst19H6]
  have hw21 : ∀ s, wInst19H6 s - 1 / 4 ≤ 6 := by
    intro s; fin_cases s <;> norm_num [wInst19H6]
  refine ⟨?_, ?_, ?_, cEqm19H6 (fun s _ => hw s) (fun s _ => hw21 s),
    cEqm19H6 (fun s _ => hw s) (fun s _ => hw21 s), ?_, ?_⟩
  · refine ncEqm19H6 (by norm_num) (by norm_num) (fun s _ => ?_) ?_
    · fin_cases s <;> norm_num [wInst19H6]
    · rw [Fin.sum_univ_three, h0, h1, h2]; norm_num
  · refine ncEqm19H6 (by norm_num [wInst19H6]) (by norm_num [wInst19H6]) (fun s hs => ?_) ?_
    · rw [Finset.mem_singleton.mp hs]; norm_num
    · rw [Finset.sum_singleton, h5]; norm_num
  · refine ncEqm19H6 (by norm_num) (by norm_num) (fun s hs => ?_) ?_
    · fin_cases s <;> simp at hs <;> norm_num [wInst19H6]
    · rw [Finset.sum_pair (by decide), h3, h4]; norm_num
  · simp only [exAnte19H6, one_div, bern19H6, Fin.isValue, xB19H6, omega19H6, cons_val',
      Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg,
      add_cons, head_cons, tail_cons, zero_add, empty_add_empty, cons_val_zero,
      neg_add_cancel_right, Fin.sum_univ_three, xC19H6, add_neg_cancel_right, ↓reduceIte,
      add_sub_cancel, Real.sqrt_inv, neg_sub, one_ne_zero, Fin.reduceEq]
    rw [h0, h1, h2, h3, h4, h4']
    norm_num [wInst19H6]
  · simp only [exAnte19H6, one_div, bern19H6, Fin.isValue, xC19H6, omega19H6, cons_val',
      Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, add_cons,
      head_cons, tail_cons, zero_add, empty_add_empty, cons_val_zero, add_neg_cancel_right,
      Fin.sum_univ_three, ↓reduceIte, add_sub_cancel, Real.sqrt_inv, neg_sub, one_ne_zero,
      Fin.reduceEq, x19H6]
    rw [h3, h4, h4']
    norm_num [wInst19H6]

/-- **Exercise 19.H.6(b)** (MWG, p. 730), Pareto optimality: in the instance, the equilibrium
allocation with non-contingent markets is not Pareto optimal (consumer 2's good-1 consumption
`49/1156` in state 1 is not `1/4`; `exercise_19_H_6_not_po`). -/
theorem exercise_19_H_6b_not_po :
    ¬ IsParetoOptimalU ![U1_19H6, U2_19H6] (omega19H6 6 wInst19H6) (xB19H6 6 wInst19H6 (-1)) := by
  intro hpo
  obtain ⟨h0, h1, h2, -, -, -⟩ := wInst19H6_sqrt
  refine exercise_19_H_6_not_po hpo (s₀ := 0) ?_ fun s => ?_
  · simp [xB19H6, omega19H6, ncTrade19H6]
    norm_num [wInst19H6]
  · fin_cases s
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.zero_eta, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h0]
      norm_num [wInst19H6]
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.mk_one, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h1]
      norm_num [wInst19H6]
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.reduceFinMk, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h2]
      norm_num [wInst19H6]

/-- **Exercise 19.H.6(e)** (MWG, p. 730) in the instance: the hypotheses of `exercise_19_H_6e`
hold, so its comparisons apply (consumer 1 obtains `6` throughout). -/
theorem exercise_19_H_6e_instance :
    exAnte19H6 0 (xB19H6 6 wInst19H6 (-1) 0) = 6 ∧
      exAnte19H6 0 (xC19H6 6 wInst19H6 (-79 / 25) 0) = 6 ∧
      exAnte19H6 0 (x19H6 6 wInst19H6 0) = 6 ∧
      exAnte19H6 1 (x19H6 6 wInst19H6 1) = ∑ s, (1 / 3) * wInst19H6 s + 1 / 4 ∧
      exAnte19H6 1 (xB19H6 6 wInst19H6 (-1) 1) ≤ exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ∧
      exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ≤ exAnte19H6 1 (x19H6 6 wInst19H6 1) := by
  obtain ⟨-, -, -, h3, h4, -⟩ := wInst19H6_sqrt
  refine exercise_19_H_6e (fun s => ?_) (by norm_num [wInst19H6]) (by norm_num [wInst19H6]) ?_
  · fin_cases s <;> norm_num [wInst19H6]
  · rw [h3, h4]; norm_num

end MWG.EquilibriumUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 19.F.4: nonexistence of Radner equilibrium with real assets (MWG p. 728)

* Real assets (returns are bundles of goods, valued at the spot prices) and the corresponding
  Radner equilibrium with unlimited short sales (`radnerFeasibleReal`, `IsRadnerEqmReal`); with
  returns in a single good this is Definition 19.E.2 (`radnerFeasibleReal_single`,
  `isRadnerEqmReal_single`).
* The maximizer of `∑ⱼ cⱼ √yⱼ` on a budget set is unique and explicit (`sqrtDemand`).
* Hart's example (`A19F4`, `U19F4`, `omega19F4`): two equally likely states, two goods, consumers
  with Bernoulli utilities `2√x₁ + √x₂` and `√x₁ + 2√x₂`, endowments `(2, 1), (0, 1)` and
  `(0, 1), (2, 1)`, and two real assets, asset `k` paying one unit of good `k` in each state.
  The Arrow-Debreu equilibrium (all prices `1`) makes the two assets' values equal
  (`exercise_19_F_4_AD`); at any Arrow-Debreu prices the relative price of good 2 is the same in
  both states (`ad19F4_det`), while at any spot-market equilibrium without transfers it differs
  (`spot19F4_det`). Hence no Radner equilibrium exists (`exercise_19_F_4`): with independent
  asset values markets are complete and the equilibrium would be Arrow-Debreu, whose prices make
  the values dependent; with dependent values the assets allow no transfer that no-arbitrage
  leaves profitable, and the spot equilibrium prices make the values independent.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## Real assets -/

/-- **Exercise 19.F.4** (MWG, p. 728): the Radner budget with real assets. Asset `k` pays the
bundle `A s k ∈ ℝ^L` in state `s`, worth `p_s·A_{sk}` at the spot prices; short sales are
unlimited. -/
def radnerFeasibleReal {S L K : ℕ} (A : Fin S → Fin K → Fin L → ℝ) (q : Fin K → ℝ)
    (p ω x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + ∑ k, (p s ⬝ᵥ A s k) * z k

/-- **Exercise 19.F.4** (MWG, p. 728): Radner equilibrium with real assets (Definition 19.E.2 with
returns valued at the spot prices). -/
def IsRadnerEqmReal {S L K : ℕ} {ι : Type*} [Fintype ι] (A : Fin S → Fin K → Fin L → ℝ)
    (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin K → ℝ) (p : CVec S L)
    (x : ι → CVec S L) (z : ι → Fin K → ℝ) : Prop :=
  (∀ i, radnerFeasibleReal A q p (ω i) (x i) (z i) ∧
    ∀ x' z', radnerFeasibleReal A q p (ω i) x' z' → U i x' ≤ U i (x i)) ∧
    (∀ k, ∑ i, z i k ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i

/-- Returns denominated in one good `g` are the case `A_{sk} = r_{sk} e_g`: the real-asset budget
is then the budget of Definition 19.E.2. -/
theorem radnerFeasibleReal_single {S L K : ℕ} (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ)
    (q : Fin K → ℝ) (p ω x : CVec S L) (z : Fin K → ℝ) :
    radnerFeasibleReal (fun s k => Pi.single g (R s k)) q p ω x z ↔
      radnerFeasible g R q p ω x z := by
  have h : ∀ s, ∑ k, (p s ⬝ᵥ Pi.single g (R s k)) * z k = p s g * (R *ᵥ z) s := by
    intro s
    simp only [dotProduct_single]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [radnerFeasibleReal, radnerFeasible, h]

/-- With returns in one good, `IsRadnerEqmReal` is `IsRadnerEqm` (Definition 19.E.2). -/
theorem isRadnerEqmReal_single {S L K : ℕ} {ι : Type*} [Fintype ι] (g : Fin L)
    (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin K → ℝ)
    (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin K → ℝ) :
    IsRadnerEqmReal (fun s k => Pi.single g (R s k)) U ω q p x z ↔
      IsRadnerEqm g R U ω q p x z := by
  simp only [IsRadnerEqmReal, IsRadnerEqm, radnerFeasibleReal_single]

/-! ## Demand for `∑ⱼ cⱼ √yⱼ` -/

/-- The unique maximizer of `∑ⱼ cⱼ √yⱼ` on `{y ≥ 0 : ∑ⱼ Pⱼ yⱼ ≤ W}` (`c, P ≫ 0`, `W > 0`):
every maximizer satisfies `yⱼ Pⱼ² C = W cⱼ²` with `C = ∑ₖ cₖ²/Pₖ`, and spends `W`. -/
theorem sqrtDemand {n : Type*} [Fintype n] [Nonempty n] {c P y : n → ℝ} {W : ℝ}
    (hc : ∀ j, 0 < c j) (hP : ∀ j, 0 < P j) (hW : 0 < W) (hy : ∀ j, 0 ≤ y j)
    (hb : ∑ j, P j * y j ≤ W)
    (hopt : ∀ y' : n → ℝ, (∀ j, 0 ≤ y' j) → ∑ j, P j * y' j ≤ W →
      ∑ j, c j * √(y' j) ≤ ∑ j, c j * √(y j)) :
    (∀ j, y j * P j ^ 2 * (∑ k, c k ^ 2 / P k) = W * c j ^ 2) ∧ ∑ j, P j * y j = W := by
  set C := ∑ k, c k ^ 2 / P k with hCdef
  have hC : 0 < C := Finset.sum_pos (fun k _ => div_pos (pow_pos (hc k) 2) (hP k))
    Finset.univ_nonempty
  have hsC := Real.sqrt_pos.mpr hC
  have hsW := Real.sqrt_pos.mpr hW
  have hC2 := Real.sq_sqrt hC.le
  have hW2 := Real.sq_sqrt hW.le
  -- the candidate
  set ys : n → ℝ := fun j => (√W * c j / (√C * P j)) ^ 2 with hys
  have hys_sqrt : ∀ j, √(ys j) = √W * c j / (√C * P j) := fun j =>
    Real.sqrt_sq (div_nonneg (mul_nonneg hsW.le (hc j).le) (mul_nonneg hsC.le (hP j).le))
  have hys_budget : ∑ j, P j * ys j = W := by
    have : ∀ j, P j * ys j = W / C * (c j ^ 2 / P j) := by
      intro j
      simp only [hys]
      have := hP j
      field_simp
      rw [hC2, hW2]
      ring
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, ← hCdef]
    field_simp
  have hys_val : ∑ j, c j * √(ys j) = √W * √C := by
    have : ∀ j, c j * √(ys j) = √W / √C * (c j ^ 2 / P j) := by
      intro j
      rw [hys_sqrt]
      have := hP j
      field_simp
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, ← hCdef]
    field_simp
    rw [hC2]
  have hlow : √W * √C ≤ ∑ j, c j * √(y j) := by
    rw [← hys_val]
    refine hopt ys (fun j => sq_nonneg _) hys_budget.le
  -- the gaps
  set θ := √C / (2 * √W) with hθ
  have hθpos : 0 < θ := by positivity
  have gap : ∀ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 =
      θ * (P j * y j) - c j * √(y j) + c j ^ 2 / P j / (4 * θ) := by
    intro j
    have := hP j
    have hsq := Real.sq_sqrt (hy j)
    field_simp
    linear_combination 16 * θ ^ 2 * P j ^ 2 * hsq
  have hsum : ∑ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 =
      θ * ∑ j, P j * y j - ∑ j, c j * √(y j) + C / (4 * θ) := by
    rw [Finset.sum_congr rfl fun j _ => gap j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hCdef, Finset.sum_div]
  have hCθ : C / (4 * θ) = √W * √C / 2 := by
    rw [hθ]
    field_simp
    rw [hC2]
    ring
  have hθW : θ * W = √W * √C / 2 := by
    rw [hθ]
    field_simp
    rw [hW2]
  have hnn : ∀ j, 0 ≤ θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 := fun j =>
    mul_nonneg (mul_nonneg hθpos.le (hP j).le) (sq_nonneg _)
  have hle0 : ∑ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 ≤ 0 := by
    rw [hsum, hCθ]
    nlinarith [mul_le_mul_of_nonneg_left hb hθpos.le]
  have hzero : ∀ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 = 0 := by
    intro j
    have h0 := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j) |>.mp
      (le_antisymm hle0 (Finset.sum_nonneg fun j _ => hnn j))
    exact h0 j (Finset.mem_univ j)
  refine ⟨fun j => ?_, ?_⟩
  · have hj := hzero j
    have hPj := hP j
    have hsq0 : √(y j) - c j / (2 * θ * P j) = 0 := by
      rcases mul_eq_zero.mp hj with h | h
      · exact absurd h (by positivity)
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hrt : √(y j) = c j / (2 * θ * P j) := by linarith
    have hyj : y j = (c j / (2 * θ * P j)) ^ 2 := by
      rw [← hrt, Real.sq_sqrt (hy j)]
    rw [hyj, hθ]
    field_simp
    rw [hC2, hW2]
    ring
  · have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hnn j
    rw [hsum, hCθ] at this
    nlinarith [mul_le_mul_of_nonneg_left hb hθpos.le]

/-! ## The economy -/

/-- Exercise 19.F.4: two real assets; asset `k` pays one unit of good `k` in every state. -/
def A19F4 : Fin 2 → Fin 2 → Fin 2 → ℝ := fun _ k => Pi.single k 1

/-- Exercise 19.F.4: expected-utility coefficients, two equally likely states: consumer 1 has
Bernoulli utility `2√x₁ + √x₂`, consumer 2 has `√x₁ + 2√x₂` (times the probability `1/2`). -/
noncomputable def c19F4 : Fin 2 → Fin 2 → ℝ := ![![1, 1 / 2], ![1 / 2, 1]]

/-- Exercise 19.F.4: `Uᵢ(x) = ∑_s ∑_l c_{il} √x_{sl}`. -/
noncomputable def U19F4 (i : Fin 2) (x : CVec 2 2) : ℝ := ∑ s, ∑ l, c19F4 i l * √(x s l)

/-- Exercise 19.F.4: endowments. Both consumers own one unit of good 2 in each state; consumer 1
owns two units of good 1 in state 1, consumer 2 two units in state 2. The aggregate endowment is
`(2, 2)` in both states. -/
def omega19F4 : Fin 2 → CVec 2 2 := ![![![2, 1], ![0, 1]], ![![0, 1], ![2, 1]]]

theorem c19F4_pos (i l : Fin 2) : 0 < c19F4 i l := by
  fin_cases i <;> fin_cases l <;> norm_num [c19F4]

theorem ret19F4 (p : CVec 2 2) (s : Fin 2) (z : Fin 2 → ℝ) :
    ∑ k, (p s ⬝ᵥ A19F4 s k) * z k = p s 0 * z 0 + p s 1 * z 1 := by
  simp [A19F4, dotProduct_single, Fin.sum_univ_two]

/-- **Exercise 19.F.4**, the complete-markets benchmark: with all contingent prices `1`, each
consumer consuming his preferred good `8/5` and the other `2/5` in every state is an
Arrow-Debreu equilibrium. At these prices the two real assets have the same value `(1, 1)`:
the return matrix `(p_s·A_{sk})` has rank `1`. -/
theorem exercise_19_F_4_AD :
    IsADEqmU U19F4 omega19F4 ![fun _ => ![8 / 5, 2 / 5], fun _ => ![2 / 5, 8 / 5]]
      (fun _ _ => 1) ∧ ∀ s k, (fun _ _ => (1 : ℝ)) s ⬝ᵥ A19F4 s k = 1 := by
  refine ⟨?_, fun s k => by simp [A19F4, dotProduct_single]⟩
  set r := √(2 / 5 : ℝ) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 / 5 := Real.sq_sqrt (by norm_num)
  have h8 : √(8 / 5 : ℝ) = 2 * r := by
    rw [show (8 / 5 : ℝ) = (2 * r) ^ 2 by rw [mul_pow, hr2]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have bound : ∀ (a y : ℝ), 0 ≤ y → a * √y ≤ y / (4 * r) + a ^ 2 * r := by
    intro a y hy
    have h1 := sq_nonneg (√y - 2 * a * r)
    have h2 := Real.sq_sqrt hy
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hr' : √(2 : ℝ) / √5 = r := by rw [hrdef, Real.sqrt_div (by norm_num)]
  have hinv : 1 / r = 5 * r / 2 := by
    field_simp
    nlinarith
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · fin_cases i <;> norm_num [cval, omega19F4, dotProduct, Fin.sum_univ_two]
  · have hb' : x' 0 0 + x' 0 1 + (x' 1 0 + x' 1 1) ≤ 4 := by
      fin_cases i <;> norm_num [cval, omega19F4, dotProduct, Fin.sum_univ_two] at hb <;>
        linarith
    have b00 := bound (c19F4 i 0) (x' 0 0) (hx' 0 0)
    have b01 := bound (c19F4 i 1) (x' 0 1) (hx' 0 1)
    have b10 := bound (c19F4 i 0) (x' 1 0) (hx' 1 0)
    have b11 := bound (c19F4 i 1) (x' 1 1) (hx' 1 1)
    have hsum : x' 0 0 / (4 * r) + x' 0 1 / (4 * r) + (x' 1 0 / (4 * r) + x' 1 1 / (4 * r)) ≤
        1 / r := by
      rw [show x' 0 0 / (4 * r) + x' 0 1 / (4 * r) + (x' 1 0 / (4 * r) + x' 1 1 / (4 * r)) =
        (x' 0 0 + x' 0 1 + (x' 1 0 + x' 1 1)) / (4 * r) by ring, div_le_div_iff₀ (by positivity)
        hr0]
      nlinarith
    fin_cases i <;>
    · simp only [c19F4, one_div, Fin.zero_eta, Fin.isValue, cons_val', cons_val_zero,
        cons_val_fin_one, one_mul, one_pow, cons_val_one, inv_pow, U19F4, Fin.sum_univ_two,
        Nat.succ_eq_add_one, Nat.reduceAdd, h8, Nat.ofNat_nonneg, Real.sqrt_div, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_ofNat, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀, ge_iff_le, Fin.mk_one]
        at b00 b01 b10 b11 ⊢
      rw [hr']
      linarith
  · funext s l
    fin_cases s <;> fin_cases l <;> simp [omega19F4, Fin.sum_univ_two] <;> norm_num

/-- **Exercise 19.F.4**, complete markets: at any Arrow-Debreu prices `Π ≫ 0` (optimal demands,
`∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ`), good 2's relative price is the same in both states, `Π₁₁Π₂₂ = Π₁₂Π₂₁`.
So at the Arrow-Debreu spot prices the two real assets have proportional values: the return
matrix drops rank. -/
theorem ad19F4_det {Pr : CVec 2 2} (hP : ∀ s l, 0 < Pr s l) {x : Fin 2 → CVec 2 2}
    (hx : ∀ i, NonnegC (x i) ∧ cval Pr (x i) ≤ cval Pr (omega19F4 i))
    (hopt : ∀ i x', NonnegC x' → cval Pr x' ≤ cval Pr (omega19F4 i) →
      U19F4 i x' ≤ U19F4 i (x i))
    (hcl : ∑ i, x i ≤ ∑ i, omega19F4 i) :
    Pr 0 0 * Pr 1 1 = Pr 0 1 * Pr 1 0 := by
  have hcv : ∀ y : CVec 2 2, cval Pr y = ∑ j : Fin 2 × Fin 2, Pr j.1 j.2 * y j.1 j.2 := by
    intro y; simp [cval, dotProduct, Fintype.sum_prod_type]
  have hU : ∀ i y, U19F4 i y = ∑ j : Fin 2 × Fin 2, c19F4 i j.2 * √(y j.1 j.2) := by
    intro i y; simp [U19F4, Fintype.sum_prod_type]
  have hW : ∀ i, 0 < cval Pr (omega19F4 i) := by
    intro i
    have := hP 0 0; have := hP 0 1; have := hP 1 0; have := hP 1 1
    fin_cases i <;> simp [cval, omega19F4, dotProduct, Fin.sum_univ_two] <;> linarith
  have hd : ∀ i, (∀ j : Fin 2 × Fin 2, x i j.1 j.2 * Pr j.1 j.2 ^ 2 *
      (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) = cval Pr (omega19F4 i) *
        c19F4 i j.2 ^ 2) ∧
      ∑ j : Fin 2 × Fin 2, Pr j.1 j.2 * x i j.1 j.2 = cval Pr (omega19F4 i) := by
    intro i
    refine sqrtDemand (c := fun j : Fin 2 × Fin 2 => c19F4 i j.2)
      (P := fun j : Fin 2 × Fin 2 => Pr j.1 j.2) (y := fun j : Fin 2 × Fin 2 => x i j.1 j.2)
      (fun j => c19F4_pos _ _) (fun j => hP _ _) (hW i)
      (fun j => (hx i).1 _ _) (by rw [← hcv]; exact (hx i).2) fun y' hy' hb' => ?_
    have := hopt i (fun s l => y' (s, l)) (fun s l => hy' _) (by simpa [hcv] using hb')
    simpa [hU] using this
  have hC : ∀ i, 0 < ∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2 := fun i =>
    Finset.sum_pos (fun k _ => div_pos (pow_pos (c19F4_pos _ _) 2) (hP _ _))
      Finset.univ_nonempty
  -- market clearing holds with equality
  have hcl' : ∀ s l, x 0 s l + x 1 s l ≤ omega19F4 0 s l + omega19F4 1 s l := by
    intro s l; simpa [Fin.sum_univ_two] using hcl s l
  have hb0 := (hd 0).2
  have hb1 := (hd 1).2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hb0 hb1
  simp only [cval, dotProduct, Fin.sum_univ_two] at hb0 hb1
  have m00 := mul_nonpos_of_nonneg_of_nonpos (hP 0 0).le (sub_nonpos.mpr (hcl' 0 0))
  have m01 := mul_nonpos_of_nonneg_of_nonpos (hP 0 1).le (sub_nonpos.mpr (hcl' 0 1))
  have m10 := mul_nonpos_of_nonneg_of_nonpos (hP 1 0).le (sub_nonpos.mpr (hcl' 1 0))
  have m11 := mul_nonpos_of_nonneg_of_nonpos (hP 1 1).le (sub_nonpos.mpr (hcl' 1 1))
  have z00 : Pr 0 0 * (x 0 0 0 + x 1 0 0 - (omega19F4 0 0 0 + omega19F4 1 0 0)) = 0 := by
    linarith
  have z01 : Pr 0 1 * (x 0 0 1 + x 1 0 1 - (omega19F4 0 0 1 + omega19F4 1 0 1)) = 0 := by
    linarith
  have z10 : Pr 1 0 * (x 0 1 0 + x 1 1 0 - (omega19F4 0 1 0 + omega19F4 1 1 0)) = 0 := by
    linarith
  have z11 : Pr 1 1 * (x 0 1 1 + x 1 1 1 - (omega19F4 0 1 1 + omega19F4 1 1 1)) = 0 := by
    linarith
  have e00 : x 0 0 0 + x 1 0 0 = 2 := by
    have := (mul_eq_zero.mp z00).resolve_left (hP 0 0).ne'
    simp [omega19F4] at this; linarith
  have e01 : x 0 0 1 + x 1 0 1 = 2 := by
    have := (mul_eq_zero.mp z01).resolve_left (hP 0 1).ne'
    simp [omega19F4] at this; norm_num at this; linarith
  have e10 : x 0 1 0 + x 1 1 0 = 2 := by
    have := (mul_eq_zero.mp z10).resolve_left (hP 1 0).ne'
    simp [omega19F4] at this; linarith
  have e11 : x 0 1 1 + x 1 1 1 = 2 := by
    have := (mul_eq_zero.mp z11).resolve_left (hP 1 1).ne'
    simp [omega19F4] at this; norm_num at this; linarith
  -- the demands: `x_{isl} Π_{sl}²` does not depend on `s`
  have st : ∀ i l, x i 0 l * Pr 0 l ^ 2 = x i 1 l * Pr 1 l ^ 2 := by
    intro i l
    have h0 := (hd i).1 (0, l)
    have h1 := (hd i).1 (1, l)
    have : (x i 0 l * Pr 0 l ^ 2) * (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) =
        (x i 1 l * Pr 1 l ^ 2) * (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) := by
      simp only at h0 h1; rw [h0, h1]
    exact mul_right_cancel₀ (hC i).ne' this
  have sq0 : Pr 0 0 ^ 2 = Pr 1 0 ^ 2 := by
    have := st 0 0; have := st 1 0
    nlinarith
  have sq1 : Pr 0 1 ^ 2 = Pr 1 1 ^ 2 := by
    have := st 0 1; have := st 1 1
    nlinarith
  have q0 : Pr 0 0 = Pr 1 0 := (pow_left_inj₀ (hP 0 0).le (hP 1 0).le two_ne_zero).mp sq0
  have q1 : Pr 0 1 = Pr 1 1 := (pow_left_inj₀ (hP 0 1).le (hP 1 1).le two_ne_zero).mp sq1
  rw [q0, q1, mul_comm]

/-- **Exercise 19.F.4**, spot markets only: at any spot prices `p ≫ 0` with optimal spot
demands in every state and `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ`, good 2's relative price differs between the
states, `p₁₁p₂₂ ≠ p₁₂p₂₁`: the asset values are linearly independent. -/
theorem spot19F4_det {p : CVec 2 2} (hp : ∀ s l, 0 < p s l) {x : Fin 2 → CVec 2 2}
    (hx : ∀ i s, (∀ l, 0 ≤ x i s l) ∧ p s ⬝ᵥ x i s ≤ p s ⬝ᵥ omega19F4 i s)
    (hopt : ∀ i s (y : Fin 2 → ℝ), (∀ l, 0 ≤ y l) → p s ⬝ᵥ y ≤ p s ⬝ᵥ omega19F4 i s →
      ∑ l, c19F4 i l * √(y l) ≤ ∑ l, c19F4 i l * √(x i s l))
    (hcl : ∑ i, x i ≤ ∑ i, omega19F4 i) :
    p 0 0 * p 1 1 ≠ p 0 1 * p 1 0 := by
  intro hdet
  have hW : ∀ i s, 0 < p s ⬝ᵥ omega19F4 i s := by
    intro i s
    fin_cases i <;> fin_cases s <;> simp [omega19F4, dotProduct, Fin.sum_univ_two] <;>
      linarith [hp 0 0, hp 0 1, hp 1 0, hp 1 1]
  have hd : ∀ i s, (∀ l, x i s l * p s l ^ 2 * (∑ k, c19F4 i k ^ 2 / p s k) =
      p s ⬝ᵥ omega19F4 i s * c19F4 i l ^ 2) ∧ ∑ l, p s l * x i s l = p s ⬝ᵥ omega19F4 i s :=
    fun i s => sqrtDemand (fun l => c19F4_pos i l) (fun l => hp s l) (hW i s) (hx i s).1
      (hx i s).2 (hopt i s)
  have hcl' : ∀ s l, x 0 s l + x 1 s l ≤ omega19F4 0 s l + omega19F4 1 s l := by
    intro s l; simpa [Fin.sum_univ_two] using hcl s l
  have eq0 : ∀ s, x 0 s 0 + x 1 s 0 = omega19F4 0 s 0 + omega19F4 1 s 0 := by
    intro s
    have b0 := (hd 0 s).2
    have b1 := (hd 1 s).2
    simp only [dotProduct, Fin.sum_univ_two] at b0 b1
    have m0 := mul_nonpos_of_nonneg_of_nonpos (hp s 0).le (sub_nonpos.mpr (hcl' s 0))
    have m1 := mul_nonpos_of_nonneg_of_nonpos (hp s 1).le (sub_nonpos.mpr (hcl' s 1))
    have z0 : p s 0 * (x 0 s 0 + x 1 s 0 - (omega19F4 0 s 0 + omega19F4 1 s 0)) = 0 := by
      linarith
    have := (mul_eq_zero.mp z0).resolve_left (hp s 0).ne'
    linarith
  have f1 := (hd 0 0).1 0
  have f2 := (hd 1 0).1 0
  have f3 := (hd 0 1).1 0
  have f4 := (hd 1 1).1 0
  have c0 := eq0 0
  have c1 := eq0 1
  simp only [Fin.isValue, c19F4, one_div, cons_val', cons_val_fin_one, cons_val_zero,
      Fin.sum_univ_two, one_pow, cons_val_one, inv_pow, dotProduct, omega19F4, mul_one, mul_zero,
      zero_add, add_zero] at f1 f2 f3 f4 c0 c1
  set P := p 0 1 / p 0 0 with hPdef
  have hu := hp 0 0
  have hu' := hp 1 0
  have hPpos : 0 < P := div_pos (hp 0 1) hu
  have hv : p 0 1 = P * p 0 0 := by rw [hPdef]; field_simp
  have hv' : p 1 1 = P * p 1 0 := by
    rw [hPdef]; field_simp; linarith
  rw [hv] at f1 f2
  rw [hv'] at f3 f4
  field_simp at f1 f2 f3 f4
  have h30 : 30 * P = 0 := by
    linear_combination (-(P + 4)) * f1 + (P + 4) * f3 - (4 * P + 1) * f2 + (4 * P + 1) * f4 +
      (P + 4) * (4 * P + 1) * c0 - (P + 4) * (4 * P + 1) * c1
  linarith

theorem U19F4_lt_bump (i : Fin 2) {x : CVec 2 2} (hx : NonnegC x) (s l : Fin 2) {δ : ℝ}
    (hδ : 0 < δ) : U19F4 i x < U19F4 i (x + δ • contingentUnit l s) := by
  have hu : ∀ s' l', 0 ≤ (δ • contingentUnit l s) s' l' := by
    intro s' l'
    simp only [Pi.smul_apply, smul_eq_mul, contingentUnit]
    split_ifs <;> simp [hδ.le]
  unfold U19F4
  refine Finset.sum_lt_sum (fun s' _ => Finset.sum_le_sum fun l' _ => ?_)
    ⟨s, Finset.mem_univ _, Finset.sum_lt_sum (fun l' _ => ?_) ⟨l, Finset.mem_univ _, ?_⟩⟩
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (c19F4_pos i l').le
    simp only [Pi.add_apply]; linarith [hu s' l']
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (c19F4_pos i l').le
    simp only [Pi.add_apply]; linarith [hu s l']
  · refine mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (hx s l) ?_) (c19F4_pos i l)
    simp [contingentUnit, hδ]

theorem dot_bump19F4 (p x : CVec 2 2) (s l s' : Fin 2) (δ : ℝ) :
    p s' ⬝ᵥ (x + δ • contingentUnit l s) s' =
      p s' ⬝ᵥ x s' + if s' = s then p s l * δ else 0 := by
  fin_cases s <;> fin_cases l <;> fin_cases s' <;>
    simp [contingentUnit, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Exercise 19.F.4** (MWG, p. 728). With unlimited short sales and returns denominated in more
than one good, a Radner equilibrium may fail to exist: in the economy `omega19F4`, `U19F4`
(strictly increasing, strictly concave in each good) with the two real assets `A19F4` (asset `k`
pays one unit of good `k` in each state), there is no Radner equilibrium. If the asset values
`(p_{sk})` are linearly independent, the structure is complete, so the equilibrium is an
Arrow-Debreu equilibrium (no-arbitrage gives state prices `ν ≫ 0`) and its spot prices make the
values dependent (`ad19F4_det`); if they are dependent, the assets only transfer wealth along
`(p₁₁, p₂₁)` and no-arbitrage leaves only the spot budgets, whose equilibria make the values
independent (`spot19F4_det`). -/
theorem exercise_19_F_4 :
    ¬ ∃ (q : Fin 2 → ℝ) (p : CVec 2 2) (x : Fin 2 → CVec 2 2) (z : Fin 2 → Fin 2 → ℝ),
      IsRadnerEqmReal A19F4 U19F4 omega19F4 q p x z := by
  rintro ⟨q, p, x, z, hopt, -, hcl⟩
  have hfe : ∀ i, NonnegC (x i) ∧ q ⬝ᵥ z i ≤ 0 ∧ ∀ s, p s ⬝ᵥ x i s ≤
      p s ⬝ᵥ omega19F4 i s + (p s 0 * z i 0 + p s 1 * z i 1) := by
    intro i
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hopt i
    exact ⟨h1, h2, fun s => by rw [← ret19F4]; exact h3 s⟩
  have hbest : ∀ i x' (z' : Fin 2 → ℝ), NonnegC x' → q ⬝ᵥ z' ≤ 0 →
      (∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ omega19F4 i s + (p s 0 * z' 0 + p s 1 * z' 1)) →
      U19F4 i x' ≤ U19F4 i (x i) := fun i x' z' h1 h2 h3 =>
    (hopt i).2 x' z' ⟨h1, h2, fun s => by rw [ret19F4]; exact h3 s⟩
  -- consumer 1 cannot gain `δ` of good `l` in state `s` with an extra portfolio `z'`
  have nodev : ∀ (s l : Fin 2) (δ : ℝ) (z' : Fin 2 → ℝ), 0 < δ → q ⬝ᵥ (z 0 + z') ≤ 0 →
      (∀ s', (if s' = s then p s l * δ else 0) ≤ p s' 0 * z' 0 + p s' 1 * z' 1) → False := by
    intro s l δ z' hδ hq hs
    have hnn : NonnegC (x 0 + δ • contingentUnit l s) := by
      intro s' l'
      have h1 := (hfe 0).1 s' l'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, contingentUnit]
      split_ifs <;> simp <;> linarith
    have := hbest 0 (x 0 + δ • contingentUnit l s) (z 0 + z') hnn hq fun s' => by
      rw [dot_bump19F4]
      have h1 := (hfe 0).2.2 s'
      have h2 := hs s'
      simp only [Pi.add_apply]
      linarith
    exact absurd this (not_le.mpr (U19F4_lt_bump 0 (hfe 0).1 s l hδ))
  have hp : ∀ s l, 0 < p s l := by
    intro s l
    by_contra h
    push Not at h
    refine nodev s l 1 0 one_pos (by simpa using (hfe 0).2.1) fun s' => ?_
    split_ifs <;> simp [h]
  by_cases hdet : p 0 0 * p 1 1 = p 0 1 * p 1 0
  · -- the asset values are dependent
    set P := p 0 1 / p 0 0 with hPdef
    have hu := hp 0 0
    have hv : p 0 1 = P * p 0 0 := by rw [hPdef]; field_simp
    have hv' : p 1 1 = P * p 1 0 := by
      rw [hPdef]; field_simp; linarith
    have hc : ∀ z' : Fin 2 → ℝ, q ⬝ᵥ z' ≤ 0 → z' 0 + P * z' 1 ≤ 0 := by
      intro z' hq'
      by_contra h
      push Not at h
      refine nodev 0 0 (z' 0 + P * z' 1) z' h
        (by rw [dotProduct_add]; linarith [(hfe 0).2.1]) fun s' => ?_
      fin_cases s'
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
        rw [hv]; nlinarith
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [hv']; nlinarith [hp 1 0]
    have hsp : ∀ i s, p s ⬝ᵥ x i s ≤ p s ⬝ᵥ omega19F4 i s := by
      intro i s
      have h1 := (hfe i).2.2 s
      have h2 := hc (z i) (hfe i).2.1
      fin_cases s
      · simp only [Fin.zero_eta, Fin.isValue] at h1 ⊢
        rw [hv] at h1; nlinarith
      · simp only [Fin.mk_one, Fin.isValue] at h1 ⊢
        rw [hv'] at h1; nlinarith [hp 1 0]
    refine spot19F4_det hp (fun i s => ⟨fun l => (hfe i).1 s l, hsp i s⟩)
      (fun i s y hy hb => ?_) hcl hdet
    have hnn : NonnegC (Function.update (x i) s y) := by
      intro s' l
      by_cases h : s' = s
      · subst h; simp [hy l]
      · simp [h, (hfe i).1 s' l]
    have := hbest i (Function.update (x i) s y) 0 hnn (by simp) fun s' => by
      by_cases h : s' = s
      · subst h; rw [Function.update_self]; simpa using hb
      · rw [Function.update_of_ne h]; simpa using hsp i s'
    unfold U19F4 at this
    fin_cases s <;> simp [Function.update, Fin.sum_univ_two] at this ⊢ <;> linarith
  · -- the asset values are independent: complete markets
    set D := p 0 0 * p 1 1 - p 0 1 * p 1 0 with hD
    have hD0 : D ≠ 0 := sub_ne_zero.mpr hdet
    set ν0 := (p 1 1 * q 0 - p 1 0 * q 1) / D with hν0
    set ν1 := (p 0 0 * q 1 - p 0 1 * q 0) / D with hν1
    have solve : ∀ m0 m1 : ℝ, ∃ z' : Fin 2 → ℝ, p 0 0 * z' 0 + p 0 1 * z' 1 = m0 ∧
        p 1 0 * z' 0 + p 1 1 * z' 1 = m1 := by
      intro m0 m1
      refine ⟨![(p 1 1 * m0 - p 0 1 * m1) / D, (p 0 0 * m1 - p 1 0 * m0) / D], ?_, ?_⟩ <;>
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hD]
        ring
    have hq : ∀ z' : Fin 2 → ℝ, q ⬝ᵥ z' =
        ν0 * (p 0 0 * z' 0 + p 0 1 * z' 1) + ν1 * (p 1 0 * z' 0 + p 1 1 * z' 1) := by
      intro z'
      simp only [dotProduct, Fin.sum_univ_two, hν0, hν1]
      field_simp
      rw [hD]
      ring
    have hpos0 : 0 < ν0 := by
      by_contra h
      push Not at h
      obtain ⟨z', h0, h1⟩ := solve (p 0 0) 0
      refine nodev 0 0 1 z' one_pos ?_ fun s' => ?_
      · rw [dotProduct_add, hq z', h0, h1]
        nlinarith [(hfe 0).2.1, hp 0 0]
      · fin_cases s' <;> simp [h0, h1]
    have hpos1 : 0 < ν1 := by
      by_contra h
      push Not at h
      obtain ⟨z', h0, h1⟩ := solve 0 (p 1 0)
      refine nodev 1 0 1 z' one_pos ?_ fun s' => ?_
      · rw [dotProduct_add, hq z', h0, h1]
        nlinarith [(hfe 0).2.1, hp 1 0]
      · fin_cases s' <;> simp [h0, h1]
    set Pr : CVec 2 2 := fun s l => ![ν0, ν1] s * p s l with hPr
    have hcv : ∀ y : CVec 2 2, cval Pr y = ν0 * (p 0 ⬝ᵥ y 0) + ν1 * (p 1 ⬝ᵥ y 1) := by
      intro y
      simp [hPr, cval, dotProduct, Fin.sum_univ_two]
      ring
    have hPpos : ∀ s l, 0 < Pr s l := by
      intro s l
      fin_cases s
      · exact mul_pos hpos0 (hp 0 l)
      · exact mul_pos hpos1 (hp 1 l)
    have key := ad19F4_det hPpos (x := x) (fun i => ⟨(hfe i).1, ?_⟩) (fun i x' hx' hb => ?_) hcl
    · have : ν0 * ν1 * D = 0 := by
        simp only [hPr, Matrix.cons_val_zero, Matrix.cons_val_one] at key
        rw [hD]
        linear_combination key
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_pos hpos0 hpos1).ne' h
      · exact hD0 h
    · rw [hcv, hcv]
      have h0 := mul_le_mul_of_nonneg_left ((hfe i).2.2 0) hpos0.le
      have h1 := mul_le_mul_of_nonneg_left ((hfe i).2.2 1) hpos1.le
      have h2 := (hfe i).2.1
      rw [hq] at h2
      nlinarith
    · obtain ⟨z', h0, h1⟩ := solve (p 0 ⬝ᵥ x' 0 - p 0 ⬝ᵥ omega19F4 i 0)
        (p 1 ⬝ᵥ x' 1 - p 1 ⬝ᵥ omega19F4 i 1)
      refine hbest i x' z' hx' ?_ fun s => ?_
      · rw [hq, h0, h1]
        rw [hcv, hcv] at hb
        linarith
      · fin_cases s
        · simp only [Fin.zero_eta, Fin.isValue]; rw [h0]; linarith
        · simp only [Fin.mk_one, Fin.isValue]; rw [h1]; linarith

end MWG.EquilibriumUncertainty

set_option linter.style.longLine false
#print axioms MWG.EquilibriumUncertainty.CVec
#print axioms MWG.EquilibriumUncertainty.cval
#print axioms MWG.EquilibriumUncertainty.contingentUnit
#print axioms MWG.EquilibriumUncertainty.definition_19_B_1
#print axioms MWG.EquilibriumUncertainty.randomVar
#print axioms MWG.EquilibriumUncertainty.randomVar_ext
#print axioms MWG.EquilibriumUncertainty.NonnegC
#print axioms MWG.EquilibriumUncertainty.expUtil
#print axioms MWG.EquilibriumUncertainty.euPref
#print axioms MWG.EquilibriumUncertainty.example_19_B_1
#print axioms MWG.EquilibriumUncertainty.footnote_19_2
#print axioms MWG.EquilibriumUncertainty.seedsTech
#print axioms MWG.EquilibriumUncertainty.plan2
#print axioms MWG.EquilibriumUncertainty.example_19_B_2
#print axioms MWG.EquilibriumUncertainty.ConsumedExAnte
#print axioms MWG.EquilibriumUncertainty.SharesValid
#print axioms MWG.EquilibriumUncertainty.shares_printed_normalization_fails
#print axioms MWG.EquilibriumUncertainty.IsInfoStructure
#print axioms MWG.EquilibriumUncertainty.Refines
#print axioms MWG.EquilibriumUncertainty.IsInfoFamily
#print axioms MWG.EquilibriumUncertainty.example19B3
#print axioms MWG.EquilibriumUncertainty.example_19_B_3
#print axioms MWG.EquilibriumUncertainty.unique_predecessor
#print axioms MWG.EquilibriumUncertainty.IsMeasurable
#print axioms MWG.EquilibriumUncertainty.example_19_B_3_measurable
#print axioms MWG.EquilibriumUncertainty.StronglyMonotoneC
#print axioms MWG.EquilibriumUncertainty.StronglyMonotoneL
#print axioms MWG.EquilibriumUncertainty.expUtil_stronglyMonotone
#print axioms MWG.EquilibriumUncertainty.flat
#print axioms MWG.EquilibriumUncertainty.unflat
#print axioms MWG.EquilibriumUncertainty.unflat_flat
#print axioms MWG.EquilibriumUncertainty.flat_unflat
#print axioms MWG.EquilibriumUncertainty.flat_injective
#print axioms MWG.EquilibriumUncertainty.flat_dotProduct
#print axioms MWG.EquilibriumUncertainty.flat_add
#print axioms MWG.EquilibriumUncertainty.flat_smul
#print axioms MWG.EquilibriumUncertainty.flat_sum
#print axioms MWG.EquilibriumUncertainty.unflat_add
#print axioms MWG.EquilibriumUncertainty.unflat_smul
#print axioms MWG.EquilibriumUncertainty.CEconomy
#print axioms MWG.EquilibriumUncertainty.CEconomy.mk
#print axioms MWG.EquilibriumUncertainty.CEconomy.X
#print axioms MWG.EquilibriumUncertainty.CEconomy.pref
#print axioms MWG.EquilibriumUncertainty.CEconomy.ω
#print axioms MWG.EquilibriumUncertainty.CEconomy.Y
#print axioms MWG.EquilibriumUncertainty.CEconomy.θ
#print axioms MWG.EquilibriumUncertainty.CEconomy.wealth
#print axioms MWG.EquilibriumUncertainty.CEconomy.IsADEqm
#print axioms MWG.EquilibriumUncertainty.CEconomy.toPriv
#print axioms MWG.EquilibriumUncertainty.flatAlloc
#print axioms MWG.EquilibriumUncertainty.isADEqm_iff_isWalrasEqm
#print axioms MWG.EquilibriumUncertainty.CEconomy.IsParetoOptimal
#print axioms MWG.EquilibriumUncertainty.adEqm_paretoOptimal
#print axioms MWG.EquilibriumUncertainty.paretoOptimal_supported
#print axioms MWG.EquilibriumUncertainty.IsADEqmU
#print axioms MWG.EquilibriumUncertainty.exchangeCE
#print axioms MWG.EquilibriumUncertainty.isADEqmU_iff
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_1
#print axioms MWG.EquilibriumUncertainty.euPref_convex
#print axioms MWG.EquilibriumUncertainty.euPref_prefConvex
#print axioms MWG.EquilibriumUncertainty.euPref_rational_lns
#print axioms MWG.EquilibriumUncertainty.adEqm_paretoOptimal_eu
#print axioms MWG.EquilibriumUncertainty.eventually_lt_of_hasDerivAt_pos
#print axioms MWG.EquilibriumUncertainty.hasDerivAt_nonpos_of_eventually_le
#print axioms MWG.EquilibriumUncertainty.exists_nonneg_smul_of_dot_nonpos
#print axioms MWG.EquilibriumUncertainty.cval_add_smul
#print axioms MWG.EquilibriumUncertainty.foc_dir
#print axioms MWG.EquilibriumUncertainty.hasDerivAt_lt_of_strictConcaveOn
#print axioms MWG.EquilibriumUncertainty.eq_of_hasDerivAt_eq_of_strictConcaveOn
#print axioms MWG.EquilibriumUncertainty.quasilinearLog_le
#print axioms MWG.EquilibriumUncertainty.quasilinearLog_eq_iff
#print axioms MWG.EquilibriumUncertainty.quasilinearLog_at
#print axioms MWG.EquilibriumUncertainty.cval_sum
#print axioms MWG.EquilibriumUncertainty.cval_mono
#print axioms MWG.EquilibriumUncertainty.cval_add
#print axioms MWG.EquilibriumUncertainty.cval_sub
#print axioms MWG.EquilibriumUncertainty.cval_smul
#print axioms MWG.EquilibriumUncertainty.cval_unit
#print axioms MWG.EquilibriumUncertainty.exists_larger_cheap
#print axioms MWG.EquilibriumUncertainty.IsParetoOptimalU
#print axioms MWG.EquilibriumUncertainty.adEqmU_price_nonneg
#print axioms MWG.EquilibriumUncertainty.adEqmU_budget_binds
#print axioms MWG.EquilibriumUncertainty.adEqmU_paretoOptimal
#print axioms MWG.EquilibriumUncertainty.constC
#print axioms MWG.EquilibriumUncertainty.po_stateIndependent
#print axioms MWG.EquilibriumUncertainty.eu1
#print axioms MWG.EquilibriumUncertainty.eu1_eq_expUtil
#print axioms MWG.EquilibriumUncertainty.eu1_stronglyMonotone
#print axioms MWG.EquilibriumUncertainty.dirC
#print axioms MWG.EquilibriumUncertainty.cval_dirC
#print axioms MWG.EquilibriumUncertainty.hasDerivAt_eu1_dir
#print axioms MWG.EquilibriumUncertainty.foc_eu1
#print axioms MWG.EquilibriumUncertainty.po_no_improving_dir
#print axioms MWG.EquilibriumUncertainty.po_tangency
#print axioms MWG.EquilibriumUncertainty.GoodBernoulli
#print axioms MWG.EquilibriumUncertainty.GoodBernoulli.deriv_pos
#print axioms MWG.EquilibriumUncertainty.GoodBernoulli.deriv_lt
#print axioms MWG.EquilibriumUncertainty.goodBernoulli_sqrt
#print axioms MWG.EquilibriumUncertainty.strictConcaveOn_fin1
#print axioms MWG.EquilibriumUncertainty.omega19C1
#print axioms MWG.EquilibriumUncertainty.example_19_C_1a
#print axioms MWG.EquilibriumUncertainty.example_19_C_1a_diagonal
#print axioms MWG.EquilibriumUncertainty.example_19_C_1b
#print axioms MWG.EquilibriumUncertainty.po_exhausts
#print axioms MWG.EquilibriumUncertainty.AggregateTwoOne
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_2
#print axioms MWG.EquilibriumUncertainty.example_19_C_2
#print axioms MWG.EquilibriumUncertainty.example_19_C_2_equal
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_3
#print axioms MWG.EquilibriumUncertainty.halfEndow
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_4a
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_4b
#print axioms MWG.EquilibriumUncertainty.exercise_19_C_5
#print axioms MWG.EquilibriumUncertainty.radnerFeasible
#print axioms MWG.EquilibriumUncertainty.IsRadnerEqm
#print axioms MWG.EquilibriumUncertainty.IsRadnerEqmD
#print axioms MWG.EquilibriumUncertainty.definition_19_D_1
#print axioms MWG.EquilibriumUncertainty.radnerFeasible_rescale
#print axioms MWG.EquilibriumUncertainty.adBudget
#print axioms MWG.EquilibriumUncertainty.adBudget_eq_radner
#print axioms MWG.EquilibriumUncertainty.proposition_19_D_1_i
#print axioms MWG.EquilibriumUncertainty.radner_eq_adBudget
#print axioms MWG.EquilibriumUncertainty.clear_eq_of_binding
#print axioms MWG.EquilibriumUncertainty.proposition_19_D_1_ii_le
#print axioms MWG.EquilibriumUncertainty.proposition_19_D_1_ii
#print axioms MWG.EquilibriumUncertainty.proposition_19_D_1_ii_counterexample
#print axioms MWG.EquilibriumUncertainty.no_expost_trade
#print axioms MWG.EquilibriumUncertainty.footnote_19_5
#print axioms MWG.EquilibriumUncertainty.footnote_19_7
#print axioms MWG.EquilibriumUncertainty.dollarFeasible
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_1
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_1_dollars_goods
#print axioms MWG.EquilibriumUncertainty.omega19D1
#print axioms MWG.EquilibriumUncertainty.example_19_D_1
#print axioms MWG.EquilibriumUncertainty.example_19_D_1_instance
#print axioms MWG.EquilibriumUncertainty.example_19_D_1_stateIndependent
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_2
#print axioms MWG.EquilibriumUncertainty.adBudget0
#print axioms MWG.EquilibriumUncertainty.radnerBudget0
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_3_i
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_3_ii
#print axioms MWG.EquilibriumUncertainty.adBudgetTree
#print axioms MWG.EquilibriumUncertainty.radnerBudgetTree
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_4c_i
#print axioms MWG.EquilibriumUncertainty.exercise_19_D_4c_ii
#print axioms MWG.EquilibriumUncertainty.ReturnVector
#print axioms MWG.EquilibriumUncertainty.returnMatrix
#print axioms MWG.EquilibriumUncertainty.arrowSecurity
#print axioms MWG.EquilibriumUncertainty.example_19_E_1_arrow
#print axioms MWG.EquilibriumUncertainty.example19E1iii
#print axioms MWG.EquilibriumUncertainty.example_19_E_1_iii
#print axioms MWG.EquilibriumUncertainty.callOption
#print axioms MWG.EquilibriumUncertainty.primary4321
#print axioms MWG.EquilibriumUncertainty.example_19_E_2
#print axioms MWG.EquilibriumUncertainty.budgetSet_normalized
#print axioms MWG.EquilibriumUncertainty.ArbitrageFree
#print axioms MWG.EquilibriumUncertainty.NonnegNonzeroReturns
#print axioms MWG.EquilibriumUncertainty.mulVec_single
#print axioms MWG.EquilibriumUncertainty.ArbitrageFree.pos
#print axioms MWG.EquilibriumUncertainty.eq_smul_of_ker_le
#print axioms MWG.EquilibriumUncertainty.separation_fintype
#print axioms MWG.EquilibriumUncertainty.lemma_19_E_1
#print axioms MWG.EquilibriumUncertainty.radner_arbitrageFree
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_1
#print axioms MWG.EquilibriumUncertainty.example_19_E_3
#print axioms MWG.EquilibriumUncertainty.IsComplete
#print axioms MWG.EquilibriumUncertainty.isComplete_iff_surjective
#print axioms MWG.EquilibriumUncertainty.example_19_E_4_identity
#print axioms MWG.EquilibriumUncertainty.example_19_E_4
#print axioms MWG.EquilibriumUncertainty.optionStructure19E5
#print axioms MWG.EquilibriumUncertainty.example_19_E_5
#print axioms MWG.EquilibriumUncertainty.not_complete_of_eq_rows
#print axioms MWG.EquilibriumUncertainty.example_19_E_5_not_separating
#print axioms MWG.EquilibriumUncertainty.interpolate_by_options
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_2
#print axioms MWG.EquilibriumUncertainty.foc_halfspace
#print axioms MWG.EquilibriumUncertainty.portfolioObjective
#print axioms MWG.EquilibriumUncertainty.hasDerivAt_portfolioObjective
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_1_proof2
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_1_proof2_radner
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_1a
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_1b
#print axioms MWG.EquilibriumUncertainty.dot_eq_of_pricing
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_2_i
#print axioms MWG.EquilibriumUncertainty.multipliers_pos_of_complete
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_2_ii
#print axioms MWG.EquilibriumUncertainty.multipliers_unique
#print axioms MWG.EquilibriumUncertainty.arrow_price
#print axioms MWG.EquilibriumUncertainty.radner_date0_binds
#print axioms MWG.EquilibriumUncertainty.proposition_19_E_3
#print axioms MWG.EquilibriumUncertainty.appendAsset
#print axioms MWG.EquilibriumUncertainty.redundant_range
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_4
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_4_eqm
#print axioms MWG.EquilibriumUncertainty.r2_19E6
#print axioms MWG.EquilibriumUncertainty.example_19_E_6_returns
#print axioms MWG.EquilibriumUncertainty.example_19_E_6_price
#print axioms MWG.EquilibriumUncertainty.example_19_E_6_bounds
#print axioms MWG.EquilibriumUncertainty.optionPrice19E6
#print axioms MWG.EquilibriumUncertainty.example_19_E_6_dispersion
#print axioms MWG.EquilibriumUncertainty.example_19_E_6_identity_fails
#print axioms MWG.EquilibriumUncertainty.r1_19E6x
#print axioms MWG.EquilibriumUncertainty.r2_19E6x
#print axioms MWG.EquilibriumUncertainty.ConsistentStatePrices
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6a
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6b
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6c
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6d
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6e
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_6f
#print axioms MWG.EquilibriumUncertainty.IsCompleteTree
#print axioms MWG.EquilibriumUncertainty.nodeMatrix19E7
#print axioms MWG.EquilibriumUncertainty.rootMatrix19E7
#print axioms MWG.EquilibriumUncertainty.example_19_E_7
#print axioms MWG.EquilibriumUncertainty.adPrices19E7
#print axioms MWG.EquilibriumUncertainty.SeqReachable19E7
#print axioms MWG.EquilibriumUncertainty.exercise_19_E_5
#print axioms MWG.EquilibriumUncertainty.footnote_19_21
#print axioms MWG.EquilibriumUncertainty.example_19_F_1_po
#print axioms MWG.EquilibriumUncertainty.example_19_F_1_needs_pos
#print axioms MWG.EquilibriumUncertainty.example_19_F_1_complete
#print axioms MWG.EquilibriumUncertainty.IsSpotEqm
#print axioms MWG.EquilibriumUncertainty.radner_noAssets_iff
#print axioms MWG.EquilibriumUncertainty.sunspot_radnerEqm
#print axioms MWG.EquilibriumUncertainty.sunspot_not_po
#print axioms MWG.EquilibriumUncertainty.leontief_spot_eqm
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_1
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_1_po
#print axioms MWG.EquilibriumUncertainty.inducedConsumption
#print axioms MWG.EquilibriumUncertainty.IsConstrainedPO
#print axioms MWG.EquilibriumUncertainty.radner_consumption_induced
#print axioms MWG.EquilibriumUncertainty.proposition_19_F_1
#print axioms MWG.EquilibriumUncertainty.example_19_F_2
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_2_concave
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_2_continuous
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_2_increasing
#print axioms MWG.EquilibriumUncertainty.IsSpanned
#print axioms MWG.EquilibriumUncertainty.marketValue_wellDefined
#print axioms MWG.EquilibriumUncertainty.firmBudget
#print axioms MWG.EquilibriumUncertainty.unanimity
#print axioms MWG.EquilibriumUncertainty.unanimity_utility
#print axioms MWG.EquilibriumUncertainty.withFirm
#print axioms MWG.EquilibriumUncertainty.exercise_19_G_1
#print axioms MWG.EquilibriumUncertainty.exercise_19_G_3
#print axioms MWG.EquilibriumUncertainty.radnerFeasibleE
#print axioms MWG.EquilibriumUncertainty.exercise_19_G_2_no_one_worse_off
#print axioms MWG.EquilibriumUncertainty.exercise_19_G_4
#print axioms MWG.EquilibriumUncertainty.SigmaMeas
#print axioms MWG.EquilibriumUncertainty.SymmetricInfo
#print axioms MWG.EquilibriumUncertainty.AtLeastAsInformative
#print axioms MWG.EquilibriumUncertainty.MoreInformative
#print axioms MWG.EquilibriumUncertainty.footnote_19_43
#print axioms MWG.EquilibriumUncertainty.SigmaMeas.mono
#print axioms MWG.EquilibriumUncertainty.cellMass
#print axioms MWG.EquilibriumUncertainty.posterior
#print axioms MWG.EquilibriumUncertainty.condEU
#print axioms MWG.EquilibriumUncertainty.cellMass_pos
#print axioms MWG.EquilibriumUncertainty.posterior_sum
#print axioms MWG.EquilibriumUncertainty.cellMass_congr
#print axioms MWG.EquilibriumUncertainty.condEU_eq
#print axioms MWG.EquilibriumUncertainty.IsSignalPlan
#print axioms MWG.EquilibriumUncertainty.sum_eq_sum_cells
#print axioms MWG.EquilibriumUncertainty.signalPlan_optimal_on
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_3_max
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_3_subset
#print axioms MWG.EquilibriumUncertainty.proposition_19_H_1
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_2
#print axioms MWG.EquilibriumUncertainty.condEU_of_injective
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_1a
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_1a_counterexample
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_1b
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_1c
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_1d
#print axioms MWG.EquilibriumUncertainty.example_19_H_1_noinfo
#print axioms MWG.EquilibriumUncertainty.example_19_H_1_state1
#print axioms MWG.EquilibriumUncertainty.example_19_H_1_state2
#print axioms MWG.EquilibriumUncertainty.example_19_H_1
#print axioms MWG.EquilibriumUncertainty.reeEvent
#print axioms MWG.EquilibriumUncertainty.pooledEvent
#print axioms MWG.EquilibriumUncertainty.IsREE
#print axioms MWG.EquilibriumUncertainty.IsPooledPrice
#print axioms MWG.EquilibriumUncertainty.FullyRevealing
#print axioms MWG.EquilibriumUncertainty.DependsOnSignals
#print axioms MWG.EquilibriumUncertainty.reeEvent_eq_pooled
#print axioms MWG.EquilibriumUncertainty.pooled_fullyRevealing_isREE
#print axioms MWG.EquilibriumUncertainty.QLOptimal
#print axioms MWG.EquilibriumUncertainty.qlOptimal_iff
#print axioms MWG.EquilibriumUncertainty.qlOptimal_price_pos
#print axioms MWG.EquilibriumUncertainty.QLSpotEqm
#print axioms MWG.EquilibriumUncertainty.qlSpotEqm_iff
#print axioms MWG.EquilibriumUncertainty.postCoef
#print axioms MWG.EquilibriumUncertainty.updU
#print axioms MWG.EquilibriumUncertainty.updU_eq
#print axioms MWG.EquilibriumUncertainty.QLClears
#print axioms MWG.EquilibriumUncertainty.qlClears_iff
#print axioms MWG.EquilibriumUncertainty.postCoef_singleton
#print axioms MWG.EquilibriumUncertainty.postCoef_const
#print axioms MWG.EquilibriumUncertainty.reeEvent_nonempty
#print axioms MWG.EquilibriumUncertainty.pooledEvent_nonempty
#print axioms MWG.EquilibriumUncertainty.qlSpotEqm_two
#print axioms MWG.EquilibriumUncertainty.beta19H
#print axioms MWG.EquilibriumUncertainty.beta19H_pos
#print axioms MWG.EquilibriumUncertainty.half2
#print axioms MWG.EquilibriumUncertainty.half2_pos
#print axioms MWG.EquilibriumUncertainty.postCoef_univ_beta
#print axioms MWG.EquilibriumUncertainty.betaBoth
#print axioms MWG.EquilibriumUncertainty.ones2
#print axioms MWG.EquilibriumUncertainty.sig19H2
#print axioms MWG.EquilibriumUncertainty.qlClears_two
#print axioms MWG.EquilibriumUncertainty.naiveEvents19H2
#print axioms MWG.EquilibriumUncertainty.example_19_H_2
#print axioms MWG.EquilibriumUncertainty.example_19_H_2_continued
#print axioms MWG.EquilibriumUncertainty.beta19H3
#print axioms MWG.EquilibriumUncertainty.beta19H3_pos
#print axioms MWG.EquilibriumUncertainty.example_19_H_3
#print axioms MWG.EquilibriumUncertainty.coef19H7
#print axioms MWG.EquilibriumUncertainty.endow19H7
#print axioms MWG.EquilibriumUncertainty.sig19H7
#print axioms MWG.EquilibriumUncertainty.coef19H7_pos
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_7a
#print axioms MWG.EquilibriumUncertainty.events19H7b
#print axioms MWG.EquilibriumUncertainty.u0_19H7
#print axioms MWG.EquilibriumUncertainty.u1_19H7
#print axioms MWG.EquilibriumUncertainty.pos_19H7b
#print axioms MWG.EquilibriumUncertainty.ne_19H7b
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_7b
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_7c
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_7d
#print axioms MWG.EquilibriumUncertainty.bOf
#print axioms MWG.EquilibriumUncertainty.kOf
#print axioms MWG.EquilibriumUncertainty.sig19H4
#print axioms MWG.EquilibriumUncertainty.beta19H4
#print axioms MWG.EquilibriumUncertainty.case19H4
#print axioms MWG.EquilibriumUncertainty.price19H4
#print axioms MWG.EquilibriumUncertainty.unif50
#print axioms MWG.EquilibriumUncertainty.betaBoth19H4
#print axioms MWG.EquilibriumUncertainty.postCoef_unif50
#print axioms MWG.EquilibriumUncertainty.facts19H4
#print axioms MWG.EquilibriumUncertainty.factsREE19H4
#print axioms MWG.EquilibriumUncertainty.price19H4_eq_iff
#print axioms MWG.EquilibriumUncertainty.postCoef_pooled19H4
#print axioms MWG.EquilibriumUncertainty.example_19_H_4
#print axioms MWG.EquilibriumUncertainty.example_19_H_4_printed
#print axioms MWG.EquilibriumUncertainty.example_19_H_5_pooled
#print axioms MWG.EquilibriumUncertainty.example_19_H_5_separates
#print axioms MWG.EquilibriumUncertainty.example_19_H_5_identifies
#print axioms MWG.EquilibriumUncertainty.infoGain
#print axioms MWG.EquilibriumUncertainty.infoGain_eq
#print axioms MWG.EquilibriumUncertainty.infoGain_nonneg
#print axioms MWG.EquilibriumUncertainty.infoGain_pos
#print axioms MWG.EquilibriumUncertainty.continuousOn_infoGain
#print axioms MWG.EquilibriumUncertainty.integral_infoGain_pos
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_5
#print axioms MWG.EquilibriumUncertainty.GoodSupply
#print axioms MWG.EquilibriumUncertainty.LemonsAdmissible
#print axioms MWG.EquilibriumUncertainty.lemons_admissible_iff
#print axioms MWG.EquilibriumUncertainty.lemons_admissible_cases
#print axioms MWG.EquilibriumUncertainty.example_19_H_6
#print axioms MWG.EquilibriumUncertainty.footnote_19_49
#print axioms MWG.EquilibriumUncertainty.strictConcave_tangent
#print axioms MWG.EquilibriumUncertainty.welfare19F5
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_5a
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_5b
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_5c
#print axioms MWG.EquilibriumUncertainty.U1_19H6
#print axioms MWG.EquilibriumUncertainty.U2_19H6
#print axioms MWG.EquilibriumUncertainty.omega19H6
#print axioms MWG.EquilibriumUncertainty.x19H6
#print axioms MWG.EquilibriumUncertainty.sqrt_le_add_quarter
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6a
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6_surplus
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6_not_po
#print axioms MWG.EquilibriumUncertainty.linU
#print axioms MWG.EquilibriumUncertainty.coef19F3
#print axioms MWG.EquilibriumUncertainty.U19F3
#print axioms MWG.EquilibriumUncertainty.omega19F3
#print axioms MWG.EquilibriumUncertainty.pSpot19F3
#print axioms MWG.EquilibriumUncertainty.xSpot19F3
#print axioms MWG.EquilibriumUncertainty.pAD19F3
#print axioms MWG.EquilibriumUncertainty.xAD19F3
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3a_spot
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3a_AD
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3a_complete_radner
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3a
#print axioms MWG.EquilibriumUncertainty.firstHalf19F3
#print axioms MWG.EquilibriumUncertainty.secondHalf19F3
#print axioms MWG.EquilibriumUncertainty.double19F3
#print axioms MWG.EquilibriumUncertainty.doubleU19F3
#print axioms MWG.EquilibriumUncertainty.append4_zero
#print axioms MWG.EquilibriumUncertainty.append4_one
#print axioms MWG.EquilibriumUncertainty.append4_two
#print axioms MWG.EquilibriumUncertainty.append4_three
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3b
#print axioms MWG.EquilibriumUncertainty.doubleU19F3_linU
#print axioms MWG.EquilibriumUncertainty.doubleU19F3_double
#print axioms MWG.EquilibriumUncertainty.R1_19F3
#print axioms MWG.EquilibriumUncertainty.R3_19F3
#print axioms MWG.EquilibriumUncertainty.pADspot19F3
#print axioms MWG.EquilibriumUncertainty.z3_19F3
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3c_one
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3c_three
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_3c
#print axioms MWG.EquilibriumUncertainty.bern19H6
#print axioms MWG.EquilibriumUncertainty.ncFeasible19H6
#print axioms MWG.EquilibriumUncertainty.IsNCEqm19H6
#print axioms MWG.EquilibriumUncertainty.ncTrade19H6
#print axioms MWG.EquilibriumUncertainty.sqrt_le_tangent
#print axioms MWG.EquilibriumUncertainty.ncEqm19H6
#print axioms MWG.EquilibriumUncertainty.IsCEqm19H6
#print axioms MWG.EquilibriumUncertainty.cEqm19H6
#print axioms MWG.EquilibriumUncertainty.exAnte19H6
#print axioms MWG.EquilibriumUncertainty.xB19H6
#print axioms MWG.EquilibriumUncertainty.xC19H6
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6e
#print axioms MWG.EquilibriumUncertainty.wInst19H6
#print axioms MWG.EquilibriumUncertainty.wInst19H6_sqrt
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6_instance
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6b_not_po
#print axioms MWG.EquilibriumUncertainty.exercise_19_H_6e_instance
#print axioms MWG.EquilibriumUncertainty.radnerFeasibleReal
#print axioms MWG.EquilibriumUncertainty.IsRadnerEqmReal
#print axioms MWG.EquilibriumUncertainty.radnerFeasibleReal_single
#print axioms MWG.EquilibriumUncertainty.isRadnerEqmReal_single
#print axioms MWG.EquilibriumUncertainty.sqrtDemand
#print axioms MWG.EquilibriumUncertainty.A19F4
#print axioms MWG.EquilibriumUncertainty.c19F4
#print axioms MWG.EquilibriumUncertainty.U19F4
#print axioms MWG.EquilibriumUncertainty.omega19F4
#print axioms MWG.EquilibriumUncertainty.c19F4_pos
#print axioms MWG.EquilibriumUncertainty.ret19F4
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_4_AD
#print axioms MWG.EquilibriumUncertainty.ad19F4_det
#print axioms MWG.EquilibriumUncertainty.spot19F4_det
#print axioms MWG.EquilibriumUncertainty.U19F4_lt_bump
#print axioms MWG.EquilibriumUncertainty.dot_bump19F4
#print axioms MWG.EquilibriumUncertainty.exercise_19_F_4
