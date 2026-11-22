import MWGPreferenceChoice.PreferenceRelations
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Sign.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Profiles, social welfare functionals and their axioms

MWG, Section 21.C, pp. 792-795, with footnotes 3, 4 and 7.

This module fixes the reusable vocabulary of Chapters 21-23. A *profile* assigns to every agent
`i : ι` a preference relation on the alternatives `X` (read `p i x y` as `x ≿ᵢ y`). The set
`𝓡` of rational preference relations is `RationalPrefs X` (Kreps's `Rational`: complete and
transitive), and the set `𝓟` of rational relations with no indifference between distinct
alternatives is `StrictPrefs X`. A *social welfare functional* on a domain `A` (Definition
21.C.1) is an aggregator `F : Profile ι X → X → X → Prop` that is rational on every profile of
`A` (`IsSWF`). We define the Pareto property (Definition 21.C.2), pairwise independence
(Definition 21.C.3), dictatorship and the pairwise majority relation, and prove footnote 4
(the members of `𝓟` are exactly the reflexive, transitive and total relations) and footnote 7
(pairwise independence is independence of the restrictions to `{x, y}`).

Two profile builders are provided for later constructions: `scorePref s` is the linear order
ranking alternatives by a score `s : X → ℕ`, ties broken by a fixed well-ordering of `X`; it
lies in `𝓟`. `natPref u` is the rational relation represented by `u : X → ℕ`; it may have
indifferences. No departures from the book.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility

variable {ι X : Type*}

/-- A profile of preference relations, one for each agent (MWG, p. 793). -/
abbrev Profile (ι X : Type*) := ι → X → X → Prop

/-- No two distinct alternatives are indifferent (MWG, p. 793). -/
def NoIndifference (r : X → X → Prop) : Prop := ∀ x y, r x y → r y x → x = y

/-- **Section 21.C** (MWG, p. 793). The set `𝓡` of rational preference relations on `X`. -/
def RationalPrefs (X : Type*) : Set (X → X → Prop) := {r | Rational r}

/-- **Section 21.C** (MWG, p. 793). The set `𝓟` of rational preference relations on `X` in
which no two distinct alternatives are indifferent. -/
def StrictPrefs (X : Type*) : Set (X → X → Prop) := {r | Rational r ∧ NoIndifference r}

/-- The universal domain `𝓡^I` of profiles of rational preferences. -/
def RationalProfiles (ι X : Type*) : Set (Profile ι X) := {p | ∀ i, p i ∈ RationalPrefs X}

/-- The domain `𝓟^I` of profiles of rational preferences without indifference. -/
def StrictProfiles (ι X : Type*) : Set (Profile ι X) := {p | ∀ i, p i ∈ StrictPrefs X}

/-- **Section 21.C** (MWG, p. 793). `𝓟 ⊂ 𝓡`. -/
theorem strictPrefs_subset : StrictPrefs X ⊆ RationalPrefs X := fun _ h => h.1

/-- `𝓟^I ⊆ 𝓡^I`. -/
theorem strictProfiles_subset : StrictProfiles ι X ⊆ RationalProfiles ι X :=
  fun _ h i => (h i).1

/-- **Footnote 4** (MWG, p. 793). A relation belongs to `𝓟` iff it is reflexive, transitive
and total: for distinct `x, y`, either `x ≿ y` or `y ≿ x`, but not both. -/
theorem footnote_21_4 (r : X → X → Prop) :
    r ∈ StrictPrefs X ↔ (∀ x, r x x) ∧ TransitivePref r ∧
      ∀ x y, x ≠ y → (r x y ∨ r y x) ∧ ¬(r x y ∧ r y x) := by
  constructor
  · rintro ⟨⟨hc, ht⟩, hn⟩
    exact ⟨complete_refl hc, ht, fun x y hxy => ⟨hc x y, fun h => hxy (hn x y h.1 h.2)⟩⟩
  · rintro ⟨hrefl, ht, htot⟩
    refine ⟨⟨fun x y => ?_, ht⟩, fun x y hxy hyx => ?_⟩
    · by_cases h : x = y
      · subst h
        exact Or.inl (hrefl x)
      · exact (htot x y h).1
    · by_contra h
      exact (htot x y h).2 ⟨hxy, hyx⟩

/-- **Footnote 3** (MWG, p. 793). For a rational `≿ᵢ`, strict preference is irreflexive and
transitive (MWG Proposition 1.B.1(i), imported from Chapter 1). -/
theorem footnote_21_3_strict {r : X → X → Prop} (hr : Rational r) :
    (∀ x, ¬Strict r x x) ∧ (∀ x y z, Strict r x y → Strict r y z → Strict r x z) :=
  MWG.PreferenceChoice.proposition_1_B_1_i hr

/-- **Footnote 3** (MWG, p. 793). For a rational `≿ᵢ`, indifference is reflexive, transitive
and symmetric (MWG Proposition 1.B.1(ii), imported from Chapter 1). -/
theorem footnote_21_3_indifferent {r : X → X → Prop} (hr : Rational r) :
    (∀ x, Indifferent r x x) ∧
      (∀ x y z, Indifferent r x y → Indifferent r y z → Indifferent r x z) ∧
      (∀ x y, Indifferent r x y → Indifferent r y x) :=
  MWG.PreferenceChoice.proposition_1_B_1_ii hr

/-- Strict preference is transitive for a rational relation. -/
theorem strict_trans {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : Strict r x y) (hyz : Strict r y z) : Strict r x z :=
  (MWG.PreferenceChoice.proposition_1_B_1_i hr).2 x y z hxy hyz

/-- `x ≿ y ≻ z` implies `x ≻ z` for a rational relation. -/
theorem strict_of_weak_strict {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨hr.2 x y z hxy hyz.1, fun hzx => hyz.2 (hr.2 z x y hzx hxy)⟩

/-- For a complete relation, failure of `x ≻ y` means `y ≿ x`. -/
theorem weak_of_not_strict {r : X → X → Prop} (hc : Complete r) {x y : X}
    (h : ¬Strict r x y) : r y x := by
  rcases hc y x with h' | h'
  · exact h'
  · by_contra hyx
    exact h ⟨h', hyx⟩

/-- Strict preference is asymmetric. -/
theorem strict_asymm {r : X → X → Prop} {x y : X} (h : Strict r x y) : ¬Strict r y x :=
  fun h' => h.2 h'.1

/-- **Definition 21.C.1** (MWG, p. 793). `F` is a social welfare functional on the domain `A`:
it assigns a rational social preference `F p` to every profile `p ∈ A`. -/
def IsSWF (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) : Prop :=
  ∀ p ∈ A, Rational (F p)

/-- **Definition 21.C.2** (MWG, p. 794). `F` is Paretian on `A`: unanimous strict preference
for `x` over `y` makes `x` socially strictly preferred to `y`. -/
def Paretian (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) : Prop :=
  ∀ p ∈ A, ∀ x y, (∀ i, Strict (p i) x y) → Strict (F p) x y

/-- **Definition 21.C.3** (MWG, pp. 794-795). Pairwise independence (independence of
irrelevant alternatives): if two profiles of `A` rank `x` and `y` identically for every agent,
the social rankings of `x` and `y` coincide. -/
def PairwiseIndependent (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) : Prop :=
  ∀ p ∈ A, ∀ p' ∈ A, ∀ x y, (∀ i, (p i x y ↔ p' i x y) ∧ (p i y x ↔ p' i y x)) →
    (F p x y ↔ F p' x y) ∧ (F p y x ↔ F p' y x)

/-- **Proposition 21.C.1** (MWG, p. 796). Agent `h` is a dictator for `F` on `A`: for every
profile of `A`, `x ≻ₕ y` implies that `x` is socially strictly preferred to `y`. -/
def IsDictator (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (h : ι) : Prop :=
  ∀ p ∈ A, ∀ x y, Strict (p h) x y → Strict (F p) x y

/-- **Proposition 21.C.1** (MWG, p. 796). `F` is dictatorial on `A` if it has a dictator. -/
def Dictatorial (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) : Prop :=
  ∃ h, IsDictator A F h

/-- The restriction `≿|{x, y}` of a relation to the pair `{x, y}` (footnote 7, p. 794). -/
def restrictPair (r : X → X → Prop) (x y : X) : X → X → Prop :=
  fun a b => (a = x ∨ a = y) ∧ (b = x ∨ b = y) ∧ r a b

/-- Two reflexive relations have equal restrictions to `{x, y}` iff they agree on the ordered
pairs `(x, y)` and `(y, x)`. -/
theorem restrictPair_eq_iff {r r' : X → X → Prop} (hr : ∀ a, r a a) (hr' : ∀ a, r' a a)
    (x y : X) :
    restrictPair r x y = restrictPair r' x y ↔ (r x y ↔ r' x y) ∧ (r y x ↔ r' y x) := by
  constructor
  · intro h
    have h1 := congrFun (congrFun h x) y
    have h2 := congrFun (congrFun h y) x
    simp only [restrictPair, true_or, or_true, true_and, eq_iff_iff] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    funext a b
    simp only [restrictPair, eq_iff_iff]
    constructor
    · rintro ⟨ha, hb, hab⟩
      refine ⟨ha, hb, ?_⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hr' _
      · exact h1.1 hab
      · exact h2.1 hab
      · exact hr' _
    · rintro ⟨ha, hb, hab⟩
      refine ⟨ha, hb, ?_⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hr _
      · exact h1.2 hab
      · exact h2.2 hab
      · exact hr _

/-- **Footnote 7** (MWG, p. 794). For a social welfare functional on a domain of rational
profiles, pairwise independence is equivalent to: if `≿ᵢ|{x,y} = ≿'ᵢ|{x,y}` for all `i`, then
`F(≿)|{x,y} = F(≿')|{x,y}`. -/
theorem footnote_21_7 {A : Set (Profile ι X)} {F : Profile ι X → X → X → Prop}
    (hA : A ⊆ RationalProfiles ι X) (hF : IsSWF A F) :
    PairwiseIndependent A F ↔ ∀ p ∈ A, ∀ p' ∈ A, ∀ x y,
      (∀ i, restrictPair (p i) x y = restrictPair (p' i) x y) →
        restrictPair (F p) x y = restrictPair (F p') x y := by
  have hrefl : ∀ p ∈ A, ∀ i a, p i a a := fun p hp i a => complete_refl (hA hp i).1 a
  have hFrefl : ∀ p ∈ A, ∀ a, F p a a := fun p hp a => complete_refl (hF p hp).1 a
  constructor
  · intro hI p hp p' hp' x y h
    refine (restrictPair_eq_iff (hFrefl p hp) (hFrefl p' hp') x y).2 (hI p hp p' hp' x y ?_)
    exact fun i => (restrictPair_eq_iff (hrefl p hp i) (hrefl p' hp' i) x y).1 (h i)
  · intro h p hp p' hp' x y hi
    refine (restrictPair_eq_iff (hFrefl p hp) (hFrefl p' hp') x y).1 (h p hp p' hp' x y ?_)
    exact fun i => (restrictPair_eq_iff (hrefl p hp i) (hrefl p' hp' i) x y).2 (hi i)

/-- Two relations that rank `x` against `y` the same way (both strictly one way, or both
indifferent) agree on the ordered pairs `(x, y)` and `(y, x)`. -/
theorem agree_of_same_ranking {r r' : X → X → Prop} {x y : X}
    (h : (Strict r x y ∧ Strict r' x y) ∨ (Strict r y x ∧ Strict r' y x) ∨
      (Indifferent r x y ∧ Indifferent r' x y)) :
    (r x y ↔ r' x y) ∧ (r y x ↔ r' y x) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨iff_of_true h1.1 h2.1, iff_of_false h1.2 h2.2⟩
  · exact ⟨iff_of_false h1.2 h2.2, iff_of_true h1.1 h2.1⟩
  · exact ⟨iff_of_true h1.1 h2.1, iff_of_true h1.2 h2.2⟩

/-- Pairwise independence transports a strict social ranking of `x` over `y` between two
profiles that rank `x` against `y` identically, agent by agent. -/
theorem PairwiseIndependent.strict_transfer {A : Set (Profile ι X)}
    {F : Profile ι X → X → X → Prop} (hI : PairwiseIndependent A F) {p q : Profile ι X}
    (hp : p ∈ A) (hq : q ∈ A) {x y : X}
    (h : ∀ i, (Strict (p i) x y ∧ Strict (q i) x y) ∨ (Strict (p i) y x ∧ Strict (q i) y x) ∨
      (Indifferent (p i) x y ∧ Indifferent (q i) x y))
    (hF : Strict (F q) x y) : Strict (F p) x y := by
  have := hI p hp q hq x y fun i => agree_of_same_ranking (h i)
  exact ⟨this.1.2 hF.1, fun h' => hF.2 (this.2.1 h')⟩

/-- The pairwise majority relation (MWG, p. 802 and Example 21.C.2, p. 796): `x` is socially at
least as good as `y` iff at least as many agents strictly prefer `x` to `y` as strictly prefer
`y` to `x`. -/
noncomputable def majorityRel [Fintype ι] (p : Profile ι X) (x y : X) : Prop :=
  by classical exact
    (Finset.univ.filter fun i => Strict (p i) y x).card ≤
      (Finset.univ.filter fun i => Strict (p i) x y).card

/-- Unfolding the majority relation with any decidability instances. -/
theorem majorityRel_iff [Fintype ι] (p : Profile ι X) (x y : X)
    [DecidablePred fun i => Strict (p i) y x] [DecidablePred fun i => Strict (p i) x y] :
    majorityRel p x y ↔ (Finset.univ.filter fun i => Strict (p i) y x).card ≤
      (Finset.univ.filter fun i => Strict (p i) x y).card := by
  unfold majorityRel
  convert Iff.rfl

/-- **Section 21.D** (MWG, p. 802). Pairwise majority voting is complete on any domain. -/
theorem majorityRel_complete [Fintype ι] (p : Profile ι X) : Complete (majorityRel p) := by
  classical
  intro x y
  simp only [majorityRel_iff]
  exact le_total _ _

/-- The linear order ranking alternatives by the score `s`, higher scores first, ties broken
by a fixed well-ordering of `X`. -/
def scorePref (s : X → ℕ) : X → X → Prop :=
  fun a b => s b < s a ∨ (s a = s b ∧ ¬WellOrderingRel a b)

/-- `scorePref s` is a rational relation with no indifference: it belongs to `𝓟`. -/
theorem scorePref_mem (s : X → ℕ) : scorePref s ∈ StrictPrefs X := by
  refine ⟨⟨fun a b => ?_, fun a b c hab hbc => ?_⟩, fun a b hab hba => ?_⟩
  · rcases lt_trichotomy (s a) (s b) with h | h | h
    · exact Or.inr (Or.inl h)
    · by_cases hw : WellOrderingRel a b
      · exact Or.inr (Or.inr ⟨h.symm, asymm_of WellOrderingRel hw⟩)
      · exact Or.inl (Or.inr ⟨h, hw⟩)
    · exact Or.inl (Or.inl h)
  · unfold scorePref at *
    rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
    · exact Or.inl (lt_trans h2 h1)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · refine Or.inr ⟨h1.trans h2, fun hac => ?_⟩
      rcases trichotomous_of WellOrderingRel a b with h | h | h
      · exact h1' h
      · subst h
        exact h2' hac
      · exact h2' (trans_of WellOrderingRel h hac)
  · unfold scorePref at hab hba
    rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hba with h2 | ⟨h2, h2'⟩
    · exact absurd (lt_trans h1 h2) (lt_irrefl _)
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · rcases trichotomous_of WellOrderingRel a b with h | h | h
      · exact absurd h h1'
      · exact h
      · exact absurd h h2'

/-- A higher score is strictly preferred under `scorePref`. -/
theorem scorePref_strict_of_lt {s : X → ℕ} {a b : X} (h : s b < s a) :
    Strict (scorePref s) a b :=
  ⟨Or.inl h, fun h' => by
    rcases h' with h' | ⟨h', _⟩
    · exact absurd (lt_trans h h') (lt_irrefl _)
    · omega⟩

/-- The rational relation represented by a natural-number utility `u`. -/
def natPref (u : X → ℕ) : X → X → Prop := fun a b => u b ≤ u a

/-- `natPref u` is rational. -/
theorem natPref_rational (u : X → ℕ) : Rational (natPref u) :=
  ⟨fun a b => le_total (u b) (u a), fun _ _ _ hab hbc => le_trans hbc hab⟩

/-- `natPref u` lies in `𝓟` when `u` is injective. -/
theorem natPref_mem_strict {u : X → ℕ} (hu : Function.Injective u) :
    natPref u ∈ StrictPrefs X :=
  ⟨natPref_rational u, fun _ _ h1 h2 => hu (le_antisymm h2 h1)⟩

/-- Strict preference under `natPref`. -/
theorem natPref_strict_iff (u : X → ℕ) (a b : X) : Strict (natPref u) a b ↔ u b < u a := by
  simp only [Strict, natPref, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Indifference under `natPref`. -/
theorem natPref_indifferent_iff (u : X → ℕ) (a b : X) :
    Indifferent (natPref u) a b ↔ u a = u b := by
  simp only [Indifferent, natPref]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- A score putting `a`, `b`, `c` on top in this order (scores 3, 2, 1), everything else
below. -/
noncomputable def rank3 (a b c : X) : X → ℕ :=
  by classical exact fun w => if w = a then 3 else if w = b then 2 else if w = c then 1 else 0

/-- Under `scorePref (rank3 a b c)` with distinct `a, b, c`: `a ≻ b`, `b ≻ c`, `a ≻ c`. -/
theorem rank3_strict {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Strict (scorePref (rank3 a b c)) a b ∧ Strict (scorePref (rank3 a b c)) b c ∧
      Strict (scorePref (rank3 a b c)) a c := by
  classical
  have ha : rank3 a b c a = 3 := by simp [rank3]
  have hb : rank3 a b c b = 2 := by simp [rank3, hab.symm]
  have hc : rank3 a b c c = 1 := by simp [rank3, hac.symm, hbc.symm]
  refine ⟨scorePref_strict_of_lt ?_, scorePref_strict_of_lt ?_, scorePref_strict_of_lt ?_⟩ <;>
    omega

/-- At least three alternatives: any two alternatives leave a third one distinct from both. -/
theorem exists_third {x y : X} (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ z, z ≠ x ∧ z ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hX
  by_cases ha : a ≠ x ∧ a ≠ y
  · exact ⟨a, ha⟩
  by_cases hb : b ≠ x ∧ b ≠ y
  · exact ⟨b, hb⟩
  refine ⟨c, ?_, ?_⟩ <;> rintro rfl <;> grind

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Social preferences over two alternatives and May's theorem

MWG, Section 21.B, pp. 790-792, and Exercises 21.B.1-21.B.3, p. 812.

With two alternatives `x` and `y`, a profile is a vector `α : ι → ℤ` with entries in
`{-1, 0, 1}` (agent `i` prefers `x`, is indifferent, prefers `y`), and a social welfare
functional is a map `F : (ι → ℤ) → ℤ` with values in `{-1, 0, 1}` on such profiles
(Definition 21.B.1). We prove the Pareto property of the weighted rules `sign ∑ βᵢ αᵢ`
(Example 21.B.1), the dictatorship remarks of Example 21.B.2, and May's theorem (Proposition
21.B.1): `F` is majority voting iff it is symmetric among agents, neutral between alternatives
and positively responsive. Our proof of sufficiency follows the book; instead of the book's
"without loss of generality" reordering of agents (which itself appeals to symmetry) it lowers
the excess `x`-supporters to indifference directly. May's characterization is proved for
every `F : (ι → ℤ) → ℤ`: the range condition of Definition 21.B.1 is not needed.

Exercise 21.B.2 gives, for each of the three properties, a rule satisfying the other two and
differing from majority voting. Exercise 21.B.3 shows that majority voting over a public
project is Pareto optimal among the two levels without transfers, characterizes Pareto
optimality with transfers by the sign of `∑ vᵢ` (the "mean"), and gives a majority decision
that transfers Pareto-dominate.

The Part Five introduction (MWG, p. 787) contains no precise mathematical claim.
-/

namespace MWG.SocialChoice

open Finset

variable {ι : Type*} [Fintype ι]

/-- The profiles over two alternatives: vectors with entries in `{-1, 0, 1}` (MWG, p. 790). -/
def TwoAltProfiles (ι : Type*) : Set (ι → ℤ) := {α | ∀ i, α i = -1 ∨ α i = 0 ∨ α i = 1}

/-- **Definition 21.B.1** (MWG, p. 790). A social welfare functional for two alternatives
assigns a social preference in `{-1, 0, 1}` to every profile. -/
def IsTwoAltSWF (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, F α = -1 ∨ F α = 0 ∨ F α = 1

/-- **Definition 21.B.2** (MWG, p. 790). `F` is Paretian: `F(1, …, 1) = 1` and
`F(-1, …, -1) = -1`. -/
def TwoAltParetian (F : (ι → ℤ) → ℤ) : Prop := F (fun _ => 1) = 1 ∧ F (fun _ => -1) = -1

/-- **Example 21.B.1** (MWG, p. 791). The weighted rule `F(α) = sign ∑ βᵢ αᵢ`. -/
noncomputable def weightedVoting (β : ι → ℝ) (α : ι → ℤ) : ℤ :=
  ((SignType.sign (∑ i, β i * (α i : ℝ)) : SignType) : ℤ)

/-- **Example 21.B.1** (MWG, p. 791). Majority voting: `F(α) = sign ∑ αᵢ`. -/
def majorityVoting (α : ι → ℤ) : ℤ := Int.sign (∑ i, α i)

/-- The sign of a real number, cast to `ℤ`, lies in `{-1, 0, 1}`. -/
theorem signType_cast_cases (a : ℝ) :
    ((SignType.sign a : SignType) : ℤ) = -1 ∨ ((SignType.sign a : SignType) : ℤ) = 0 ∨
      ((SignType.sign a : SignType) : ℤ) = 1 := by
  rcases lt_trichotomy a 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- **Example 21.B.1** (MWG, p. 791). Every weighted rule is a social welfare functional. -/
theorem weightedVoting_isSWF (β : ι → ℝ) : IsTwoAltSWF (weightedVoting β) :=
  fun _ _ => signType_cast_cases _

/-- **Example 21.B.1** (MWG, pp. 790-791). With nonnegative weights, not all zero, the
weighted rule is Paretian. -/
theorem example_21_B_1 (β : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) (hne : ∃ i, β i ≠ 0) :
    TwoAltParetian (weightedVoting β) := by
  obtain ⟨j, hj⟩ := hne
  have hpos : 0 < ∑ i, β i := by
    have hj' : 0 < β j := lt_of_le_of_ne (hβ j) (Ne.symm hj)
    calc (0 : ℝ) < β j := hj'
      _ ≤ ∑ i, β i := single_le_sum (fun i _ => hβ i) (mem_univ j)
  constructor
  · simp [weightedVoting, sign_pos hpos]
  · have hneg : ∑ i, β i * ((-1 : ℤ) : ℝ) < 0 := by
      simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, sum_neg_distrib]
      linarith
    simp only [weightedVoting, sign_neg hneg]
    rfl

/-- Majority voting is the weighted rule with all weights equal to one (MWG, p. 791). -/
theorem majorityVoting_eq_weighted (α : ι → ℤ) :
    majorityVoting α = weightedVoting (fun _ => 1) α := by
  unfold majorityVoting weightedVoting
  have hs : ∑ i, (1 : ℝ) * (α i : ℝ) = ((∑ i, α i : ℤ) : ℝ) := by simp
  rw [hs]
  rcases lt_trichotomy (∑ i, α i) 0 with h | h | h
  · have h' : ((∑ i, α i : ℤ) : ℝ) < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h, sign_neg h']
    rfl
  · rw [h]
    simp
  · have h' : (0 : ℝ) < ((∑ i, α i : ℤ) : ℝ) := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h, sign_pos h']
    rfl

/-- The integer sign lies in `{-1, 0, 1}`. -/
theorem int_sign_cases (n : ℤ) : n.sign = -1 ∨ n.sign = 0 ∨ n.sign = 1 := by
  rcases lt_trichotomy n 0 with h | h | h
  · exact Or.inl (Int.sign_eq_neg_one_of_neg h)
  · exact Or.inr (Or.inl (by simp [h]))
  · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos h))

/-- Majority voting is a social welfare functional. -/
theorem majorityVoting_isSWF : IsTwoAltSWF (ι := ι) majorityVoting :=
  fun _ _ => int_sign_cases _

/-- Number of agents preferring `x` (`n⁺`, MWG, p. 792). -/
def nPlus (α : ι → ℤ) : ℕ := (univ.filter fun i => α i = 1).card

/-- Number of agents preferring `y` (`n⁻`, MWG, p. 792). -/
def nMinus (α : ι → ℤ) : ℕ := (univ.filter fun i => α i = -1).card

/-- For a profile, `∑ αᵢ = n⁺ - n⁻`. -/
theorem sum_eq_nPlus_sub_nMinus {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    ∑ i, α i = (nPlus α : ℤ) - nMinus α := by
  have h : ∀ i, α i = (if α i = 1 then 1 else 0) - (if α i = -1 then 1 else 0) := by
    intro i
    rcases hα i with h | h | h <;> simp [h]
  rw [sum_congr rfl fun i _ => h i, sum_sub_distrib, sum_boole, sum_boole]
  rfl

/-- **Example 21.B.1** (MWG, p. 791). Majority voting gives `1` iff more agents prefer `x`
than `y`, `-1` iff more prefer `y`, and `0` in case of equality. -/
theorem majorityVoting_spec {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    (majorityVoting α = 1 ↔ nMinus α < nPlus α) ∧
      (majorityVoting α = -1 ↔ nPlus α < nMinus α) ∧
      (majorityVoting α = 0 ↔ nPlus α = nMinus α) := by
  unfold majorityVoting
  rw [sum_eq_nPlus_sub_nMinus hα]
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.sign_eq_one_iff_pos]
    omega
  · rw [Int.sign_eq_neg_one_iff_neg]
    omega
  · rw [Int.sign_eq_zero_iff_zero]
    omega

/-- **Example 21.B.2** (MWG, p. 791). Agent `h` is a dictator: `αₕ = 1` forces `F(α) = 1` and
`αₕ = -1` forces `F(α) = -1`. -/
def IsTwoAltDictator (F : (ι → ℤ) → ℤ) (h : ι) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, (α h = 1 → F α = 1) ∧ (α h = -1 → F α = -1)

omit [Fintype ι] in
/-- **Example 21.B.2** (MWG, p. 791). A dictatorial social welfare functional is Paretian. -/
theorem example_21_B_2_paretian {F : (ι → ℤ) → ℤ} {h : ι} (hF : IsTwoAltDictator F h) :
    TwoAltParetian F :=
  ⟨(hF _ (fun _ => Or.inr (Or.inr rfl))).1 rfl, (hF _ (fun _ => Or.inl rfl)).2 rfl⟩

/-- **Example 21.B.2** (MWG, p. 791). For the weighted rule with `βₕ > 0` and `βᵢ = 0` for
`i ≠ h`, `F(α) = αₕ`; in particular `h` is a dictator. -/
theorem example_21_B_2 (β : ι → ℝ) (h : ι) (hh : 0 < β h)
    (h0 : ∀ i, i ≠ h → β i = 0) :
    (∀ α ∈ TwoAltProfiles ι, weightedVoting β α = α h) ∧
      IsTwoAltDictator (weightedVoting β) h := by
  classical
  have key : ∀ α ∈ TwoAltProfiles ι, weightedVoting β α = α h := by
    intro α hα
    have hs : ∑ i, β i * (α i : ℝ) = β h * (α h : ℝ) :=
      sum_eq_single h (fun i _ hi => by rw [h0 i hi, zero_mul]) (fun hn => absurd (mem_univ h) hn)
    unfold weightedVoting
    rw [hs]
    rcases hα h with ha | ha | ha
    · have : β h * (α h : ℝ) < 0 := by rw [ha]; simp; linarith
      rw [sign_neg this, ha]
      rfl
    · simp [ha]
    · have : 0 < β h * (α h : ℝ) := by rw [ha]; simp; linarith
      rw [sign_pos this, ha]
      rfl
  exact ⟨key, fun α hα => ⟨fun h1 => (key α hα).trans h1, fun h1 => (key α hα).trans h1⟩⟩

/-- **Definition 21.B.3** (MWG, p. 791). `F` is symmetric among agents (anonymous): permuting
the agents' preferences by any onto map `π` does not change the social preference. -/
def SymmetricAmongAgents (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ π : ι → ι, Function.Surjective π → ∀ α ∈ TwoAltProfiles ι, F α = F (α ∘ π)

/-- **Definition 21.B.4** (MWG, p. 791). `F` is neutral between alternatives:
`F(α) = -F(-α)`. -/
def NeutralBetweenAlternatives (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, F α = -F (-α)

/-- **Definition 21.B.5** (MWG, p. 791). `F` is positively responsive: `α ≥ α'`, `α ≠ α'` and
`F(α') ≥ 0` imply `F(α) = 1`. -/
def PositivelyResponsive (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, ∀ α' ∈ TwoAltProfiles ι, (∀ i, α' i ≤ α i) → α ≠ α' →
    0 ≤ F α' → F α = 1

omit [Fintype ι] in
/-- Negating a profile gives a profile. -/
theorem neg_mem_twoAltProfiles {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    -α ∈ TwoAltProfiles ι := by
  intro i
  rcases hα i with h | h | h <;> simp [h]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is symmetric among agents. -/
theorem exercise_21_B_1_symmetric : SymmetricAmongAgents (ι := ι) majorityVoting := by
  intro π hπ α _
  have hinj : Function.Injective π := Finite.injective_iff_surjective.mpr hπ
  unfold majorityVoting
  congr 1
  exact (Equiv.sum_comp (Equiv.ofBijective π ⟨hinj, hπ⟩) α).symm

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is neutral between alternatives. -/
theorem exercise_21_B_1_neutral : NeutralBetweenAlternatives (ι := ι) majorityVoting := by
  intro α _
  simp [majorityVoting, sum_neg_distrib, Int.sign_neg]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is positively responsive. -/
theorem exercise_21_B_1_responsive : PositivelyResponsive (ι := ι) majorityVoting := by
  intro α _ α' _ hle hne h0
  have hlt : ∑ i, α' i < ∑ i, α i := by
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    exact sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, lt_of_le_of_ne (hle j) (Ne.symm hj)⟩
  have h0' : 0 ≤ ∑ i, α' i := by
    unfold majorityVoting at h0
    rcases lt_or_ge (∑ i, α' i) 0 with h | h
    · rw [Int.sign_eq_neg_one_of_neg h] at h0
      omega
    · exact h
  exact Int.sign_eq_one_of_pos (by omega)

/-- Under symmetry and neutrality, a tie `n⁺ = n⁻` forces social indifference (first step of
the proof of Proposition 21.B.1, MWG, p. 792). -/
theorem may_tie {F : (ι → ℤ) → ℤ} (hS : SymmetricAmongAgents F)
    (hN : NeutralBetweenAlternatives F) {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι)
    (h : nPlus α = nMinus α) : F α = 0 := by
  classical
  set P := univ.filter fun i => α i = 1 with hP
  set N := univ.filter fun i => α i = -1 with hN'
  have hcard : Fintype.card P = Fintype.card N := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h
  let e : P ≃ N := Fintype.equivOfCardEq hcard
  have memP : ∀ i, i ∈ P ↔ α i = 1 := fun i => by simp [hP]
  have memN : ∀ i, i ∈ N ↔ α i = -1 := fun i => by simp [hN']
  have hPN : ∀ i, i ∈ N → i ∉ P := fun i hi hi' => by
    have h1 := (memP i).1 hi'
    rw [(memN i).1 hi] at h1
    exact absurd h1 (by decide)
  let π : ι → ι := fun i =>
    if h1 : i ∈ P then (e ⟨i, h1⟩ : ι) else if h2 : i ∈ N then (e.symm ⟨i, h2⟩ : ι) else i
  have hπα : ∀ i, α (π i) = -α i := by
    intro i
    by_cases h1 : i ∈ P
    · have : π i = (e ⟨i, h1⟩ : ι) := by simp only [π, h1, ↓reduceDIte]
      rw [this, (memN _).1 (e ⟨i, h1⟩).2, (memP i).1 h1]
    · by_cases h2 : i ∈ N
      · have : π i = (e.symm ⟨i, h2⟩ : ι) := by simp only [π, h1, h2, ↓reduceDIte]
        rw [this, (memP _).1 (e.symm ⟨i, h2⟩).2, (memN i).1 h2]
        rfl
      · have : π i = i := by simp only [π, h1, h2, ↓reduceDIte]
        rw [this]
        rcases hα i with h3 | h3 | h3
        · exact absurd ((memN i).2 h3) h2
        · rw [h3]; rfl
        · exact absurd ((memP i).2 h3) h1
  have hsurj : Function.Surjective π := by
    intro j
    by_cases h1 : j ∈ P
    · refine ⟨(e ⟨j, h1⟩ : ι), ?_⟩
      have hk1 : (e ⟨j, h1⟩ : ι) ∈ N := (e ⟨j, h1⟩).2
      have hk2 : (e ⟨j, h1⟩ : ι) ∉ P := hPN _ hk1
      simp only [π, hk2, hk1, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
    · by_cases h2 : j ∈ N
      · refine ⟨(e.symm ⟨j, h2⟩ : ι), ?_⟩
        have hk1 : (e.symm ⟨j, h2⟩ : ι) ∈ P := (e.symm ⟨j, h2⟩).2
        simp only [π, hk1, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]
      · exact ⟨j, by simp only [π, h1, h2, ↓reduceDIte]⟩
  have hcomp : α ∘ π = -α := funext fun i => hπα i
  have h1 := hS π hsurj α hα
  rw [hcomp] at h1
  have h2 := hN α hα
  omega

/-- Under symmetry, neutrality and positive responsiveness, `n⁺ > n⁻` forces `F(α) = 1`
(second step of the proof of Proposition 21.B.1, MWG, p. 792). -/
theorem may_plus {F : (ι → ℤ) → ℤ} (hS : SymmetricAmongAgents F)
    (hN : NeutralBetweenAlternatives F) (hR : PositivelyResponsive F) {α : ι → ℤ}
    (hα : α ∈ TwoAltProfiles ι) (h : nMinus α < nPlus α) : F α = 1 := by
  classical
  set P := univ.filter fun i => α i = 1 with hP
  obtain ⟨Q, hQP, hQcard⟩ := exists_subset_card_eq (s := P) (n := nPlus α - nMinus α)
    (by simp [nPlus, hP])
  let α' : ι → ℤ := fun i => if i ∈ Q then 0 else α i
  have hαQ : ∀ i ∈ Q, α i = 1 := fun i hi => by
    have := hQP hi
    simpa [hP] using this
  have hα' : α' ∈ TwoAltProfiles ι := by
    intro i
    by_cases hi : i ∈ Q
    · simp [α', hi]
    · simpa [α', hi] using hα i
  have hplus : nPlus α' = nMinus α := by
    have hfilter : (univ.filter fun i => α' i = 1) = P \ Q := by
      ext i
      by_cases hi : i ∈ Q <;> simp [α', hi, hP]
    have hsd : (P \ Q).card = P.card - Q.card := card_sdiff_of_subset hQP
    change (univ.filter fun i => α' i = 1).card = nMinus α
    rw [hfilter, hsd, hQcard]
    have hPc : P.card = nPlus α := rfl
    omega
  have hminus : nMinus α' = nMinus α := by
    unfold nMinus
    congr 1
    ext i
    by_cases hi : i ∈ Q
    · simp [α', hi, hαQ i hi]
    · simp [α', hi]
  have h0 : F α' = 0 := may_tie hS hN hα' (hplus.trans hminus.symm)
  have hQne : Q.Nonempty := by
    rw [← card_pos, hQcard]
    omega
  obtain ⟨j, hj⟩ := hQne
  refine hR α hα α' hα' (fun i => ?_) (fun heq => ?_) h0.ge
  · by_cases hi : i ∈ Q
    · simp [α', hi, hαQ i hi]
    · simp [α', hi]
  · have := congrFun heq j
    simp [α', hj, hαQ j hj] at this

/-- **Proposition 21.B.1 (May's theorem)** (MWG, p. 792). A social welfare functional over two
alternatives is majority voting iff it is symmetric among agents, neutral between
alternatives and positively responsive. (Proved for every `F : (ι → ℤ) → ℤ`.) -/
theorem proposition_21_B_1 (F : (ι → ℤ) → ℤ) :
    (∀ α ∈ TwoAltProfiles ι, F α = majorityVoting α) ↔
      SymmetricAmongAgents F ∧ NeutralBetweenAlternatives F ∧ PositivelyResponsive F := by
  constructor
  · intro h
    refine ⟨fun π hπ α hα => ?_, fun α hα => ?_, fun α hα α' hα' hle hne h0 => ?_⟩
    · have hα' : α ∘ π ∈ TwoAltProfiles ι := fun i => hα (π i)
      rw [h α hα, h _ hα']
      exact exercise_21_B_1_symmetric π hπ α hα
    · rw [h α hα, h _ (neg_mem_twoAltProfiles hα)]
      exact exercise_21_B_1_neutral α hα
    · rw [h α hα]
      rw [h α' hα'] at h0
      exact exercise_21_B_1_responsive α hα α' hα' hle hne h0
  · rintro ⟨hS, hN, hR⟩ α hα
    rcases lt_trichotomy (nMinus α) (nPlus α) with hlt | heq | hgt
    · rw [may_plus hS hN hR hα hlt, ((majorityVoting_spec hα).1).2 hlt]
    · rw [may_tie hS hN hα heq.symm, ((majorityVoting_spec hα).2.2).2 heq.symm]
    · have hα' := neg_mem_twoAltProfiles hα
      have hc1 : nPlus (-α) = nMinus α := by
        unfold nPlus nMinus
        congr 1
        ext i
        simp [neg_eq_iff_eq_neg]
      have hc2 : nMinus (-α) = nPlus α := by
        unfold nPlus nMinus
        congr 1
        ext i
        simp [neg_eq_iff_eq_neg]
      have h1 : F (-α) = 1 := may_plus hS hN hR hα' (by omega)
      rw [hN α hα, h1, ((majorityVoting_spec hα).2.1).2 hgt]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting satisfies the three properties. -/
theorem exercise_21_B_1 :
    SymmetricAmongAgents (ι := ι) majorityVoting ∧
      NeutralBetweenAlternatives (ι := ι) majorityVoting ∧
      PositivelyResponsive (ι := ι) majorityVoting :=
  ⟨exercise_21_B_1_symmetric, exercise_21_B_1_neutral, exercise_21_B_1_responsive⟩

/-- Weighted integer voting `sign ∑ wᵢ αᵢ` with weight `2` for agent `i₀` and `1` otherwise
(Exercise 21.B.2). -/
def tiltedVoting [DecidableEq ι] (i₀ : ι) (α : ι → ℤ) : ℤ :=
  Int.sign (∑ i, (if i = i₀ then 2 else 1) * α i)

/-- **Exercise 21.B.2**, symmetry dropped (MWG, p. 812). With two distinct agents, the tilted
rule is neutral and positively responsive but not symmetric, hence not majority voting. -/
theorem exercise_21_B_2_symmetry [DecidableEq ι] {i₀ i₁ : ι} (h01 : i₀ ≠ i₁) :
    NeutralBetweenAlternatives (tiltedVoting i₀) ∧ PositivelyResponsive (tiltedVoting i₀) ∧
      ¬SymmetricAmongAgents (tiltedVoting i₀) ∧
      ¬∀ α ∈ TwoAltProfiles ι, tiltedVoting i₀ α = majorityVoting α := by
  have hN : NeutralBetweenAlternatives (tiltedVoting i₀) := by
    intro α _
    simp [tiltedVoting, mul_neg, sum_neg_distrib, Int.sign_neg]
  have hR : PositivelyResponsive (tiltedVoting i₀) := by
    intro α _ α' _ hle hne h0
    have hlt : ∑ i, (if i = i₀ then 2 else 1) * α' i < ∑ i, (if i = i₀ then 2 else 1) * α i := by
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
        by_contra hc
        push Not at hc
        exact hne (funext hc)
      refine sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
      · split_ifs <;> linarith [hle i]
      · have := lt_of_le_of_ne (hle j) (Ne.symm hj)
        split_ifs <;> linarith
    have h0' : 0 ≤ ∑ i, (if i = i₀ then 2 else 1) * α' i := by
      unfold tiltedVoting at h0
      rcases lt_or_ge (∑ i, (if i = i₀ then 2 else 1) * α' i) 0 with h | h
      · rw [Int.sign_eq_neg_one_of_neg h] at h0
        omega
      · exact h
    exact Int.sign_eq_one_of_pos (by omega)
  let α : ι → ℤ := fun i => if i = i₀ then 1 else if i = i₁ then -1 else 0
  have hα : α ∈ TwoAltProfiles ι := by
    intro i
    by_cases h0 : i = i₀ <;> by_cases h1 : i = i₁ <;> simp [α, h0, h1, Ne.symm h01]
  have hsum : ∑ i, (if i = i₀ then 2 else 1) * α i = 1 := by
    rw [Fintype.sum_eq_add i₀ i₁ h01 (fun i hi => by simp [α, hi.1, hi.2])]
    simp [α, Ne.symm h01]
  let π : ι → ι := Equiv.swap i₀ i₁
  have hsum' : ∑ i, (if i = i₀ then 2 else 1) * (α ∘ π) i = -1 := by
    rw [Fintype.sum_eq_add i₀ i₁ h01 (fun i hi => by
      simp [α, π, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, hi.1, hi.2])]
    simp [α, π, Ne.symm h01]
  have hnotS : ¬SymmetricAmongAgents (tiltedVoting i₀) := by
    intro hS
    have := hS π (Equiv.surjective _) α hα
    simp only [tiltedVoting, hsum, hsum'] at this
    norm_num at this
  refine ⟨hN, hR, hnotS, fun h => hnotS ?_⟩
  intro π' hπ' β hβ
  have hβ' : β ∘ π' ∈ TwoAltProfiles ι := fun i => hβ (π' i)
  rw [h β hβ, h _ hβ']
  exact exercise_21_B_1_symmetric π' hπ' β hβ

/-- The rule `F(α) = 1` if `n⁺ ≥ n⁻` and `-1` otherwise (Exercise 21.B.2). -/
def xBiasedVoting (α : ι → ℤ) : ℤ := if 0 ≤ ∑ i, α i then 1 else -1

/-- **Exercise 21.B.2**, neutrality dropped (MWG, p. 812). The `x`-biased rule is symmetric
and positively responsive but not neutral, hence not majority voting. -/
theorem exercise_21_B_2_neutrality :
    SymmetricAmongAgents (ι := ι) xBiasedVoting ∧ PositivelyResponsive (ι := ι) xBiasedVoting ∧
      ¬NeutralBetweenAlternatives (ι := ι) xBiasedVoting ∧
      ¬∀ α ∈ TwoAltProfiles ι, xBiasedVoting α = majorityVoting α := by
  have hS : SymmetricAmongAgents (ι := ι) xBiasedVoting := by
    intro π hπ α _
    have hinj : Function.Injective π := Finite.injective_iff_surjective.mpr hπ
    unfold xBiasedVoting
    rw [show ∑ i, (α ∘ π) i = ∑ i, α i from
      Equiv.sum_comp (Equiv.ofBijective π ⟨hinj, hπ⟩) α]
  have hR : PositivelyResponsive (ι := ι) xBiasedVoting := by
    intro α _ α' _ hle hne h0
    have hlt : ∑ i, α' i < ∑ i, α i := by
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
        by_contra hc
        push Not at hc
        exact hne (funext hc)
      exact sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, lt_of_le_of_ne (hle j) (Ne.symm hj)⟩
    have h0' : 0 ≤ ∑ i, α' i := by
      unfold xBiasedVoting at h0
      split_ifs at h0 with h
      · exact h
      · omega
    unfold xBiasedVoting
    simp [show (0 : ℤ) ≤ ∑ i, α i by omega]
  have hnot : ¬NeutralBetweenAlternatives (ι := ι) xBiasedVoting := by
    intro hN
    have := hN 0 (fun _ => Or.inr (Or.inl rfl))
    simp [xBiasedVoting] at this
  refine ⟨hS, hR, hnot, fun h => hnot ?_⟩
  intro β hβ
  rw [h β hβ, h _ (neg_mem_twoAltProfiles hβ)]
  exact exercise_21_B_1_neutral β hβ

/-- **Exercise 21.B.2**, positive responsiveness dropped (MWG, p. 812). With at least one
agent, the constant rule `F ≡ 0` is symmetric and neutral but not positively responsive, hence
not majority voting. -/
theorem exercise_21_B_2_responsiveness (i₀ : ι) :
    SymmetricAmongAgents (fun _ : ι → ℤ => (0 : ℤ)) ∧
      NeutralBetweenAlternatives (fun _ : ι → ℤ => (0 : ℤ)) ∧
      ¬PositivelyResponsive (fun _ : ι → ℤ => (0 : ℤ)) ∧
      ¬∀ α ∈ TwoAltProfiles ι, (0 : ℤ) = majorityVoting α := by
  classical
  have hnot : ¬PositivelyResponsive (fun _ : ι → ℤ => (0 : ℤ)) := by
    intro hR
    have h1 : (fun i => if i = i₀ then (1 : ℤ) else 0) ∈ TwoAltProfiles ι := by
      intro i
      by_cases h : i = i₀ <;> simp [h]
    have := hR _ h1 0 (fun _ => Or.inr (Or.inl rfl)) (fun i => by split_ifs <;> simp)
      (fun h => by simpa using congrFun h i₀) le_rfl
    simp at this
  refine ⟨fun _ _ _ _ => rfl, fun _ _ => by simp, hnot, fun h => hnot ?_⟩
  intro β hβ β' hβ' hle hne _
  have e1 := h β hβ
  have e2 := h β' hβ'
  have := exercise_21_B_1_responsive β hβ β' hβ' hle hne (by rw [← e2])
  change (0 : ℤ) = 1
  omega

/-- The level `k ∈ {0, 1}` is Pareto optimal among the two levels with no transfers, when
agent `i` gains `vᵢ k` from level `k` (Exercise 21.B.3). -/
def ParetoOptimalNoTransfers (v : ι → ℝ) (k : ℕ) : Prop :=
  ¬∃ k' ∈ ({0, 1} : Set ℕ), (∀ i, v i * k ≤ v i * k') ∧ ∃ i, v i * k < v i * k'

/-- The level `k ∈ {0, 1}` is a majority decision: `k = 1` only if at least as many agents
strictly gain from the project as strictly lose, and `k = 0` only if at least as many lose as
gain (Exercise 21.B.3). -/
def MajorityDecision (v : ι → ℝ) (k : ℕ) : Prop :=
  (k = 0 ∨ k = 1) ∧
    (k = 1 → (univ.filter fun i => v i < 0).card ≤ (univ.filter fun i => 0 < v i).card) ∧
    (k = 0 → (univ.filter fun i => 0 < v i).card ≤ (univ.filter fun i => v i < 0).card)

/-- **Exercise 21.B.3**, first claim (MWG, p. 812). A majority decision over the two levels of
the public project is Pareto optimal among the two levels when no transfers take place. -/
theorem exercise_21_B_3_pareto_no_transfers {v : ι → ℝ} {k : ℕ} (hk : MajorityDecision v k) :
    ParetoOptimalNoTransfers v k := by
  rintro ⟨k', hk', hall, j, hj⟩
  rcases hk.1 with rfl | rfl <;> rcases hk' with rfl | rfl
  · simp at hj
  · have hpos : (univ.filter fun i => v i < 0) = ∅ := by
      ext i
      have := hall i
      simp only [Nat.cast_zero, mul_zero, Nat.cast_one, mul_one] at this
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
      exact this
    have hj' : 0 < v j := by simpa using hj
    have := hk.2.2 rfl
    rw [hpos, card_empty] at this
    have hmem : j ∈ univ.filter fun i => 0 < v i := by simp [hj']
    have := card_pos.mpr ⟨j, hmem⟩
    omega
  · have hneg : (univ.filter fun i => 0 < v i) = ∅ := by
      ext i
      have := hall i
      simp only [Nat.cast_one, mul_one, Nat.cast_zero, mul_zero] at this
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
      exact this
    have hj' : v j < 0 := by simpa using hj
    have := hk.2.1 rfl
    rw [hneg, card_empty] at this
    have hmem : j ∈ univ.filter fun i => v i < 0 := by simp [hj']
    have := card_pos.mpr ⟨j, hmem⟩
    omega
  · simp at hj

/-- A policy with transfers: a level `k ∈ {0, 1}` and transfers `t` with `∑ tᵢ = 0`; agent `i`
gets `vᵢ k + tᵢ` (Exercise 21.B.3). -/
def FeasibleWithTransfers (k : ℕ) (t : ι → ℝ) : Prop := (k = 0 ∨ k = 1) ∧ ∑ i, t i = 0

/-- Pareto optimality among policies with transfers (Exercise 21.B.3). -/
def ParetoOptimalWithTransfers (v : ι → ℝ) (k : ℕ) (t : ι → ℝ) : Prop :=
  ¬∃ k' t', FeasibleWithTransfers k' t' ∧ (∀ i, v i * k + t i ≤ v i * k' + t' i) ∧
    ∃ i, v i * k + t i < v i * k' + t' i

/-- **Exercise 21.B.3**, the "mean" rule (MWG, p. 812). With at least one agent, a feasible
policy with transfers is Pareto optimal iff its level maximizes total willingness to pay
`∑ vᵢ k`, i.e. `k = 1` needs `∑ vᵢ ≥ 0` and `k = 0` needs `∑ vᵢ ≤ 0`. -/
theorem exercise_21_B_3_mean [Nonempty ι] (v : ι → ℝ) {k : ℕ} {t : ι → ℝ}
    (hf : FeasibleWithTransfers k t) :
    ParetoOptimalWithTransfers v k t ↔ ∀ k' ∈ ({0, 1} : Set ℕ),
      ∑ i, v i * k' ≤ ∑ i, v i * k := by
  constructor
  · intro hpo k' hk'
    by_contra hlt
    push Not at hlt
    set δ := (∑ i, v i * k' - ∑ i, v i * k) / Fintype.card ι with hδ
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hδpos : 0 < δ := div_pos (by linarith) hcard
    refine hpo ⟨k', fun i => v i * k + t i - v i * k' + δ, ⟨hk', ?_⟩, fun i => ?_, ?_⟩
    · rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, hf.2, sum_const, card_univ,
        nsmul_eq_mul, hδ]
      rw [mul_div_cancel₀ _ hcard.ne']
      ring
    · linarith
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, by linarith⟩
  · rintro hmax ⟨k', t', hf', hle, j, hj⟩
    have h1 : ∑ i, (v i * k + t i) < ∑ i, (v i * k' + t' i) :=
      sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, hj⟩
    rw [sum_add_distrib, sum_add_distrib, hf.2, hf'.2] at h1
    have := hmax k' hf'.1
    linarith

/-- **Exercise 21.B.3**, majority versus Pareto with transfers (MWG, p. 812). With
willingness to pay `v = (1, 1, -10)`, building the project (`k = 1`) is a majority decision
but is Pareto dominated, once transfers are allowed, by not building and transferring
`(1, 1, -2)`. -/
theorem exercise_21_B_3_not_pareto_with_transfers :
    MajorityDecision (![1, 1, -10] : Fin 3 → ℝ) 1 ∧
      ¬ParetoOptimalWithTransfers (![1, 1, -10] : Fin 3 → ℝ) 1 (fun _ => 0) := by
  constructor
  · refine ⟨Or.inr rfl, fun _ => ?_, fun h => absurd h (by norm_num)⟩
    have h1 : (univ.filter fun i : Fin 3 => (![1, 1, -10] : Fin 3 → ℝ) i < 0) = {2} := by
      ext i
      fin_cases i <;> simp
    have h2 : (univ.filter fun i : Fin 3 => 0 < (![1, 1, -10] : Fin 3 → ℝ) i) = {0, 1} := by
      ext i
      fin_cases i <;> simp
    rw [h1, h2]
    decide
  · intro h
    refine h ⟨0, ![1, 1, -2], ⟨Or.inl rfl, ?_⟩, fun i => ?_, ⟨2, ?_⟩⟩
    · simp [Fin.sum_univ_succ]
      norm_num
    · fin_cases i <;> norm_num
    · simp
      norm_num

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Borda count and the Condorcet paradox

MWG, Section 21.C, pp. 794-796 (Example 21.C.1 with footnote 6, Example 21.C.2 with footnote 8)
and the agenda remark of Section 21.D, p. 799.

The Borda count gives agent `i` the points `cᵢ(x)` = (average) rank of `x`; with indifference,
`x` occupies the ranks `k + 1, …, k + m`, where `k` is the number of alternatives strictly
better than `x` and `m` the number indifferent to `x` (including `x`), so
`cᵢ(x) = k + (m + 1) / 2`. Socially, `x ≿ y` iff `∑ᵢ cᵢ(x) ≤ ∑ᵢ cᵢ(y)`. We prove that this is a
rational (Definition 21.C.1) and, with at least one agent, Paretian social welfare functional,
the rank and averaging claims of footnote 6, and the three numerical illustrations showing that
the Borda count violates pairwise independence.

Example 21.C.2 (the Condorcet paradox) reuses the three member preferences of Chapter 1's
Condorcet example (`MWG.PreferenceChoice.condorcetRank`): pairwise majority voting is cyclic,
hence not transitive. Finally, with these preferences a two-round agenda always elects the
alternative taken up last (MWG, p. 799).

**Departure.** The Pareto property of the Borda count needs at least one agent (with no agents
every alternative gets zero points); the book takes `I ≥ 1` for granted.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- **Example 21.C.1** (MWG, p. 794). The Borda points of `x` for the preference `r`:
`#{y : y ≻ x} + (#{y : y ∼ x} + 1) / 2`, the average rank of the alternatives indifferent
to `x`. -/
noncomputable def bordaPoints [Fintype X] (r : X → X → Prop) (x : X) : ℚ :=
  by classical exact ((univ.filter fun y => Strict r y x).card : ℚ) +
    (((univ.filter fun y => Indifferent r y x).card : ℚ) + 1) / 2

/-- **Example 21.C.1** (MWG, p. 794). The Borda count: `x ≿ y` socially iff
`∑ᵢ cᵢ(x) ≤ ∑ᵢ cᵢ(y)`. -/
noncomputable def bordaSWF [Fintype ι] [Fintype X] (p : Profile ι X) (x y : X) : Prop :=
  ∑ i, bordaPoints (p i) x ≤ ∑ i, bordaPoints (p i) y

/-- **Example 21.C.1** (MWG, p. 794). The Borda count is a social welfare functional on `𝓡^I`
(indeed on every domain): it is represented by the utility `-∑ᵢ cᵢ(·)`. -/
theorem example_21_C_1_rational [Fintype ι] [Fintype X] (A : Set (Profile ι X)) :
    IsSWF A bordaSWF :=
  fun _ _ => ⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h1 h2⟩

/-- For a rational relation, `x ≻ y` implies that `x` gets strictly fewer Borda points. -/
theorem bordaPoints_lt [Fintype X] {r : X → X → Prop} (hr : Rational r) {x y : X}
    (hxy : Strict r x y) : bordaPoints r x < bordaPoints r y := by
  classical
  unfold bordaPoints
  set U : X → Finset X := fun a => univ.filter fun w => Strict r w a with hU
  set E : X → Finset X := fun a => univ.filter fun w => Indifferent r w a with hE
  change ((U x).card : ℚ) + (((E x).card : ℚ) + 1) / 2 <
    ((U y).card : ℚ) + (((E y).card : ℚ) + 1) / 2
  have hdisj : Disjoint (U x) (E x) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [hU, hE, mem_filter, mem_univ, true_and] at hw hw'
    exact hw.2 hw'.2
  have hsub : U x ∪ E x ⊆ U y := by
    intro w hw
    simp only [hU, hE, mem_union, mem_filter, mem_univ, true_and] at hw ⊢
    rcases hw with hw | hw
    · exact strict_trans hr hw hxy
    · exact strict_of_weak_strict hr hw.1 hxy
  have hcard : (U x).card + (E x).card ≤ (U y).card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card hsub
  have hEx : 1 ≤ (E x).card :=
    card_pos.2 ⟨x, by
      simp only [hE, mem_filter, mem_univ, true_and]
      exact ⟨complete_refl hr.1 x, complete_refl hr.1 x⟩⟩
  have hc : ((U x).card : ℚ) + (E x).card ≤ (U y).card := by exact_mod_cast hcard
  have hE1 : (1 : ℚ) ≤ (E x).card := by exact_mod_cast hEx
  have hEy : (0 : ℚ) ≤ (E y).card := by positivity
  linarith

/-- **Example 21.C.1** (MWG, p. 794). With at least one agent, the Borda count is Paretian on
`𝓡^I`. -/
theorem example_21_C_1_paretian [Fintype ι] [Nonempty ι] [Fintype X] :
    Paretian (RationalProfiles ι X) bordaSWF := by
  intro p hp x y hall
  have hlt : ∑ i, bordaPoints (p i) x < ∑ i, bordaPoints (p i) y :=
    sum_lt_sum_of_nonempty univ_nonempty fun i _ => bordaPoints_lt (hp i) (hall i)
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- Borda points of a preference given by a natural-number utility, with computable counts. -/
theorem bordaPoints_natPref [Fintype X] (u : X → ℕ) (x : X) :
    bordaPoints (natPref u) x = ((univ.filter fun y => u x < u y).card : ℚ) +
      (((univ.filter fun y => u y = u x).card : ℚ) + 1) / 2 := by
  classical
  have h1 : (univ.filter fun y => Strict (natPref u) y x) = univ.filter fun y => u x < u y := by
    ext y
    simp [natPref_strict_iff]
  have h2 : (univ.filter fun y => Indifferent (natPref u) y x) =
      univ.filter fun y => u y = u x := by
    ext y
    simp [natPref_indifferent_iff]
  unfold bordaPoints
  rw [h1, h2]

open Classical in
/-- **Example 21.C.1** (MWG, p. 794). Without indifference, the Borda points of the `n`-th
ranked alternative are `n`: one plus the number of strictly better alternatives. -/
theorem example_21_C_1_rank [Fintype X] {r : X → X → Prop} (hr : r ∈ StrictPrefs X) (x : X) :
    bordaPoints r x = ((univ.filter fun y => Strict r y x).card : ℚ) + 1 := by
  unfold bordaPoints
  have hE : (univ.filter fun y => Indifferent r y x) = {x} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => hr.2 y x h.1 h.2, fun h => h ▸ ⟨complete_refl hr.1.1 y,
      complete_refl hr.1.1 y⟩⟩
  rw [hE, card_singleton]
  norm_num

/-- **Footnote 6** (MWG, p. 794). If `x ≻ y ∼ z` on `X = {x, y, z}` then `c(x) = 1` and
`c(y) = c(z) = 2.5` (alternatives `x, y, z` are `0, 1, 2`). -/
theorem footnote_21_6 :
    bordaPoints (natPref (![2, 1, 1] : Fin 3 → ℕ)) 0 = 1 ∧
      bordaPoints (natPref (![2, 1, 1] : Fin 3 → ℕ)) 1 = 5 / 2 ∧
      bordaPoints (natPref (![2, 1, 1] : Fin 3 → ℕ)) 2 = 5 / 2 := by
  simp only [bordaPoints_natPref, Finset.card_filter, Fin.sum_univ_three]
  norm_num

/-- The Borda total of `x` for a profile of natural-number utilities on two agents. -/
theorem bordaSWF_two [Fintype X] (u : Fin 2 → X → ℕ) (x y : X) :
    bordaSWF (fun i => natPref (u i)) x y ↔
      bordaPoints (natPref (u 0)) x + bordaPoints (natPref (u 1)) x ≤
        bordaPoints (natPref (u 0)) y + bordaPoints (natPref (u 1)) y := by
  simp [bordaSWF, Fin.sum_univ_two]

/-- The Borda total of `x` for a profile of natural-number utilities on three agents. -/
theorem bordaSWF_three [Fintype X] (u : Fin 3 → X → ℕ) (x y : X) :
    bordaSWF (fun i => natPref (u i)) x y ↔
      bordaPoints (natPref (u 0)) x + bordaPoints (natPref (u 1)) x +
          bordaPoints (natPref (u 2)) x ≤
        bordaPoints (natPref (u 0)) y + bordaPoints (natPref (u 1)) y +
          bordaPoints (natPref (u 2)) y := by
  simp [bordaSWF, Fin.sum_univ_three]

/-- Profile `x ≻₁ z ≻₁ y`, `y ≻₂ x ≻₂ z` on `{x, y, z} = {0, 1, 2}` (Example 21.C.1). -/
def bordaProfileA : Fin 2 → Fin 3 → ℕ := ![![3, 1, 2], ![2, 3, 1]]

/-- Profile `x ≻₁' y ≻₁' z`, `y ≻₂' z ≻₂' x` (Example 21.C.1). -/
def bordaProfileB : Fin 2 → Fin 3 → ℕ := ![![3, 2, 1], ![1, 3, 2]]

/-- **Example 21.C.1, continued** (MWG, p. 795). For `x ≻₁ z ≻₁ y`, `y ≻₂ x ≻₂ z`, the Borda
totals are `c(x) = 3 < 4 = c(y)`, so `x` is socially preferred to `y`; for
`x ≻₁' y ≻₁' z`, `y ≻₂' z ≻₂' x` they are `c(x) = 4 > 3 = c(y)`. Each agent ranks `x`
against `y` identically in both profiles, so the Borda count violates pairwise independence. -/
theorem example_21_C_1_two_agents :
    ∑ i, bordaPoints (natPref (bordaProfileA i)) 0 = 3 ∧
      ∑ i, bordaPoints (natPref (bordaProfileA i)) 1 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileB i)) 0 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileB i)) 1 = 3 ∧
      ¬PairwiseIndependent (RationalProfiles (Fin 2) (Fin 3)) bordaSWF := by
  have vals : ∑ i, bordaPoints (natPref (bordaProfileA i)) 0 = 3 ∧
      ∑ i, bordaPoints (natPref (bordaProfileA i)) 1 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileB i)) 0 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileB i)) 1 = 3 := by
    simp only [Fin.sum_univ_two, bordaPoints_natPref, Finset.card_filter, Fin.sum_univ_three,
      bordaProfileA, bordaProfileB]
    norm_num
  refine ⟨vals.1, vals.2.1, vals.2.2.1, vals.2.2.2, fun hI => ?_⟩
  have hA : (fun i => natPref (bordaProfileA i)) ∈ RationalProfiles (Fin 2) (Fin 3) :=
    fun i => natPref_rational _
  have hB : (fun i => natPref (bordaProfileB i)) ∈ RationalProfiles (Fin 2) (Fin 3) :=
    fun i => natPref_rational _
  have h := hI _ hA _ hB 0 1 fun i => by
    fin_cases i <;> simp [natPref, bordaProfileA, bordaProfileB]
  have h1 : bordaSWF (fun i => natPref (bordaProfileA i)) 0 1 := by
    unfold bordaSWF
    rw [vals.1, vals.2.1]
    norm_num
  have h2 := h.1.1 h1
  unfold bordaSWF at h2
  rw [vals.2.2.1, vals.2.2.2] at h2
  norm_num at h2

/-- Profile `z ≻ x ≻ y ≻ w` (agents 1, 2), `y ≻ z ≻ w ≻ x` (agent 3), with
`x, y, z, w = 0, 1, 2, 3` (Example 21.C.1). -/
def bordaProfileC : Fin 3 → Fin 4 → ℕ := ![![3, 2, 4, 1], ![3, 2, 4, 1], ![1, 4, 3, 2]]

/-- Profile (21.C.1): `x ≻ y ≻ z ≻ w` (agents 1, 2), `y ≻ x ≻ z ≻ w` (agent 3). -/
def bordaProfileD : Fin 3 → Fin 4 → ℕ := ![![4, 3, 2, 1], ![4, 3, 2, 1], ![3, 4, 2, 1]]

/-- Profile `x ≻ y ≻ z ≻ w` (agents 1, 2), `y ≻ z ≻ w ≻ x` (agent 3). -/
def bordaProfileE : Fin 3 → Fin 4 → ℕ := ![![4, 3, 2, 1], ![4, 3, 2, 1], ![1, 4, 3, 2]]

/-- **Example 21.C.1, continued** (MWG, p. 795), three agents and four alternatives. In the
first profile `c(x) = 8 > 7 = c(y)`, so `y` is socially preferred to `x`; moving `z` and `w` to
the bottom (21.C.1) gives `c(x) = 4 < 5 = c(y)`, so `x` is socially preferred; then moving `x`
to the bottom for agent 3 gives `c(x) = 6 > 5 = c(y)`, so `y` is socially preferred again. -/
theorem example_21_C_1_three_agents :
    ∑ i, bordaPoints (natPref (bordaProfileC i)) 0 = 8 ∧
      ∑ i, bordaPoints (natPref (bordaProfileC i)) 1 = 7 ∧
      ∑ i, bordaPoints (natPref (bordaProfileD i)) 0 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileD i)) 1 = 5 ∧
      ∑ i, bordaPoints (natPref (bordaProfileE i)) 0 = 6 ∧
      ∑ i, bordaPoints (natPref (bordaProfileE i)) 1 = 5 ∧
      Strict (bordaSWF fun i => natPref (bordaProfileC i)) 1 0 ∧
      Strict (bordaSWF fun i => natPref (bordaProfileD i)) 0 1 ∧
      Strict (bordaSWF fun i => natPref (bordaProfileE i)) 1 0 := by
  have vals : ∑ i, bordaPoints (natPref (bordaProfileC i)) 0 = 8 ∧
      ∑ i, bordaPoints (natPref (bordaProfileC i)) 1 = 7 ∧
      ∑ i, bordaPoints (natPref (bordaProfileD i)) 0 = 4 ∧
      ∑ i, bordaPoints (natPref (bordaProfileD i)) 1 = 5 ∧
      ∑ i, bordaPoints (natPref (bordaProfileE i)) 0 = 6 ∧
      ∑ i, bordaPoints (natPref (bordaProfileE i)) 1 = 5 := by
    simp only [Fin.sum_univ_three, bordaPoints_natPref, Finset.card_filter, Fin.sum_univ_four,
      bordaProfileC, bordaProfileD, bordaProfileE]
    norm_num
  obtain ⟨c0, c1, d0, d1, e0, e1⟩ := vals
  refine ⟨c0, c1, d0, d1, e0, e1, ?_, ?_, ?_⟩ <;> simp only [Strict, bordaSWF, c0, c1, d0, d1,
    e0, e1] <;> norm_num

/-- With a profile of natural-number utilities, the majority relation counts strict utility
comparisons. -/
theorem majorityRel_natPref [Fintype ι] (u : ι → X → ℕ) (a b : X) :
    majorityRel (fun i => natPref (u i)) a b ↔
      (univ.filter fun i => u i a < u i b).card ≤ (univ.filter fun i => u i b < u i a).card := by
  classical
  rw [majorityRel_iff]
  simp only [natPref_strict_iff]

/-- The Condorcet profile of Example 21.C.2 (MWG, p. 796), `x ≻₁ y ≻₁ z`, `z ≻₂ x ≻₂ y`,
`y ≻₃ z ≻₃ x` with `x, y, z = 0, 1, 2`: the member preferences of Chapter 1's Condorcet
example (footnote 8). -/
def condorcetProfile : Profile (Fin 3) (Fin 3) :=
  fun i => natPref (MWG.PreferenceChoice.condorcetRank i)

/-- The Condorcet profile consists of strict (no-indifference) rational preferences. -/
theorem condorcetProfile_mem : condorcetProfile ∈ StrictProfiles (Fin 3) (Fin 3) := by
  intro i
  refine natPref_mem_strict ?_
  fin_cases i <;> decide

/-- The pairwise majority comparisons of the Condorcet profile. -/
theorem condorcet_majority :
    Strict (majorityRel condorcetProfile) 0 1 ∧ Strict (majorityRel condorcetProfile) 1 2 ∧
      Strict (majorityRel condorcetProfile) 2 0 := by
  have key : condorcetProfile = fun i => natPref (MWG.PreferenceChoice.condorcetRank i) := rfl
  rw [key]
  simp only [Strict, majorityRel_natPref]
  unfold MWG.PreferenceChoice.condorcetRank
  decide

/-- **Example 21.C.2 (the Condorcet paradox)** (MWG, p. 796). With the Condorcet profile,
pairwise majority voting makes `x` socially preferred to `y`, `y` to `z` and `z` to `x`; this
violates transitivity, so majority voting is not a social welfare functional on `𝓡^I` (or
`𝓟^I`). -/
theorem example_21_C_2 :
    Strict (majorityRel condorcetProfile) 0 1 ∧ Strict (majorityRel condorcetProfile) 1 2 ∧
      Strict (majorityRel condorcetProfile) 2 0 ∧
      ¬TransitivePref (majorityRel condorcetProfile) ∧
      ¬IsSWF (StrictProfiles (Fin 3) (Fin 3)) majorityRel ∧
      ¬IsSWF (RationalProfiles (Fin 3) (Fin 3)) majorityRel := by
  obtain ⟨h01, h12, h20⟩ := condorcet_majority
  have hnt : ¬TransitivePref (majorityRel condorcetProfile) := fun ht =>
    h20.2 (ht 0 1 2 h01.1 h12.1)
  refine ⟨h01, h12, h20, hnt, fun h => hnt (h _ condorcetProfile_mem).2,
    fun h => hnt (h _ (strictProfiles_subset condorcetProfile_mem)).2⟩

open Classical in
/-- The winner of a vote between `a` and `b` under the social relation `R`: `a` if `a ≻ b`,
otherwise `b`. -/
noncomputable def pairWinner (R : X → X → Prop) (a b : X) : X :=
  if Strict R a b then a else b

/-- The two-round agenda `(a, b, c)`: majority vote between `a` and `b`, then between the
winner and `c` (MWG, p. 799). -/
noncomputable def agendaWinner (R : X → X → Prop) (a b c : X) : X :=
  pairWinner R (pairWinner R a b) c

/-- **Section 21.D** (MWG, p. 799). With the preferences of the Condorcet paradox, whichever
alternative is taken up last survives the two-round agenda. -/
theorem condorcet_agenda (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    agendaWinner (majorityRel condorcetProfile) a b c = c := by
  classical
  obtain ⟨h01, h12, h20⟩ := condorcet_majority
  have n10 := strict_asymm h01
  have n21 := strict_asymm h12
  have n02 := strict_asymm h20
  unfold agendaWinner pairWinner
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Arrow's impossibility theorem

MWG, Section 21.C, pp. 796-799: Definition 21.C.4, Proposition 21.C.1 and Exercise 21.C.1.

We follow the book's decisive-set proof, Steps 1-10, for a fixed social welfare functional `F`
that is Paretian and pairwise independent on a domain `A` that is either `𝓡^I` or `𝓟^I`, with
finitely many agents and at least three alternatives (the set of alternatives may be
infinite). Profiles needed in the steps are built with `scorePref`, which lies in `𝓟` and hence
in both domains.

**Departure (proof repair).** In Step 9 the book takes, for the agents of `T ⊆ I \ S` who
regard `x` as at least as good as `y`, a profile with `x ≻ᵢ y ≻ᵢ z`. On `𝓡^I` an agent of `T`
may be indifferent between `x` and `y`, and then pairwise independence does not relate the two
profiles. We use `x ∼ᵢ y ≻ᵢ z` for such agents (a profile in `𝓡^I`; on `𝓟^I` the case does
not arise); the rest of the argument is unchanged.

Non-vacuity: `dictatorSWF h` (`F(≿) = ≿ₕ`) is a Paretian, pairwise independent social welfare
functional on both domains, so the hypotheses of Proposition 21.C.1 have instances (e.g. two
agents and three alternatives), and its conclusion is attained.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility

variable {ι X : Type*}

/-- The two domains of Proposition 21.C.1: `A = 𝓡^I` or `A = 𝓟^I`. -/
def StandardDomain (A : Set (Profile ι X)) : Prop :=
  A = RationalProfiles ι X ∨ A = StrictProfiles ι X

/-- Profiles of score orders lie in both standard domains. -/
theorem StandardDomain.score_mem {A : Set (Profile ι X)} (hA : StandardDomain A)
    (s : ι → X → ℕ) : (fun i => scorePref (s i)) ∈ A := by
  rcases hA with rfl | rfl
  · exact fun i => strictPrefs_subset (scorePref_mem (s i))
  · exact fun i => scorePref_mem (s i)

/-- Standard domains consist of rational profiles. -/
theorem StandardDomain.rational {A : Set (Profile ι X)} (hA : StandardDomain A)
    {p : Profile ι X} (hp : p ∈ A) (i : ι) : Rational (p i) := by
  rcases hA with rfl | rfl
  · exact hp i
  · exact (hp i).1

/-- **Definition 21.C.4(i)** (MWG, p. 797). `S` is decisive for `x` over `y`: whenever every
agent in `S` prefers `x` to `y` and every agent outside `S` prefers `y` to `x`, `x` is socially
preferred to `y`. -/
def DecisiveFor (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι)
    (x y : X) : Prop :=
  ∀ p ∈ A, (∀ i ∈ S, Strict (p i) x y) → (∀ i ∉ S, Strict (p i) y x) → Strict (F p) x y

/-- **Definition 21.C.4(ii)** (MWG, p. 797). `S` is decisive: decisive for `x` over `y` for
every pair of (distinct) alternatives. -/
def Decisive (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι) : Prop :=
  ∀ x y, x ≠ y → DecisiveFor A F S x y

/-- **Definition 21.C.4(iii)** (MWG, p. 797). `S` is completely decisive for `x` over `y`:
whenever every agent in `S` prefers `x` to `y`, `x` is socially preferred to `y`. -/
def CompletelyDecisiveFor (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι)
    (x y : X) : Prop :=
  ∀ p ∈ A, (∀ i ∈ S, Strict (p i) x y) → Strict (F p) x y

variable {A : Set (Profile ι X)} {F : Profile ι X → X → X → Prop}

/-- **Step 1** of the proof of Proposition 21.C.1 (MWG, p. 797). If `S` is decisive for `x`
over `y`, then it is decisive for `x` over any `z ≠ x`. -/
theorem arrow_step_1 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzx : z ≠ x) : DecisiveFor A F S x z := by
  classical
  by_cases hzy : z = y
  · subst hzy
    exact h
  intro p hp hS hN
  let q : Profile ι X := fun i =>
    scorePref (if i ∈ S then rank3 x y z else rank3 y z x)
  have hq : q ∈ A := hA.score_mem _
  have r1 := rank3_strict hxy (Ne.symm hzx) (Ne.symm hzy)
  have r2 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have h1 : Strict (F q) x y := h q hq (fun i hi => by simpa only [q, hi, ↓reduceIte] using r1.1)
    (fun i hi => by simpa only [q, hi, ↓reduceIte] using r2.2.2)
  have h2 : Strict (F q) y z := hP q hq y z fun i => by
    by_cases hi : i ∈ S
    · simpa only [q, hi, ↓reduceIte] using r1.2.1
    · simpa only [q, hi, ↓reduceIte] using r2.1
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) h1 h2)
  by_cases hi : i ∈ S
  · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using r1.2.2⟩
  · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using r2.2.1⟩)

/-- **Exercise 21.C.1** (MWG, p. 812), the second half of Step 1 (MWG, p. 797). If `S` is
decisive for `x` over `y`, then it is decisive for any `z ≠ y` over `y`. -/
theorem exercise_21_C_1 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzy : z ≠ y) : DecisiveFor A F S z y := by
  classical
  by_cases hzx : z = x
  · subst hzx
    exact h
  intro p hp hS hN
  let q : Profile ι X := fun i =>
    scorePref (if i ∈ S then rank3 z x y else rank3 y z x)
  have hq : q ∈ A := hA.score_mem _
  have rs := rank3_strict hzx hzy hxy
  have rn := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have h1 : Strict (F q) z x := hP q hq z x fun i => by
    by_cases hi : i ∈ S
    · simpa only [q, hi, ↓reduceIte] using rs.1
    · simpa only [q, hi, ↓reduceIte] using rn.2.1
  have h2 : Strict (F q) x y := h q hq (fun i hi => by simpa only [q, hi, ↓reduceIte] using rs.2.1)
    (fun i hi => by simpa only [q, hi, ↓reduceIte] using rn.2.2)
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) h1 h2)
  by_cases hi : i ∈ S
  · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using rs.2.2⟩
  · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using rn.1⟩)

/-- **Step 2** of the proof of Proposition 21.C.1 (MWG, p. 797). If `S` is decisive for `x`
over `y` and `z` is a third alternative, then `S` is decisive for `z` over `w` and for `w`
over `z`, for every `w ≠ z`. -/
theorem arrow_step_2 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z w : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzx : z ≠ x) (hzy : z ≠ y) (hwz : w ≠ z) :
    DecisiveFor A F S z w ∧ DecisiveFor A F S w z := by
  have hxz : DecisiveFor A F S x z := arrow_step_1 hA hF hP hI hxy h hzx
  have hzy' : DecisiveFor A F S z y := exercise_21_C_1 hA hF hP hI hxy h hzy
  exact ⟨arrow_step_1 hA hF hP hI hzy hzy' hwz,
    exercise_21_C_1 hA hF hP hI (Ne.symm hzx) hxz hwz⟩

/-- **Step 3** of the proof of Proposition 21.C.1 (MWG, p. 797). With at least three
alternatives, a set decisive for some `x` over some `y ≠ x` is decisive. -/
theorem arrow_step_3 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S : Set ι}
    {x y : X} (hxy : x ≠ y) (h : DecisiveFor A F S x y) : Decisive A F S := by
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  intro v w hvw
  by_cases hv : v = z
  · subst hv
    exact (arrow_step_2 hA hF hP hI hxy h hzx hzy (Ne.symm hvw)).1
  by_cases hw : w = z
  · subst hw
    exact (arrow_step_2 hA hF hP hI hxy h hzx hzy hvw).2
  have hzw : DecisiveFor A F S z w := (arrow_step_2 hA hF hP hI hxy h hzx hzy hw).1
  exact exercise_21_C_1 hA hF hP hI (Ne.symm hw) hzw hvw

/-- **Step 4** of the proof of Proposition 21.C.1 (MWG, p. 798). The intersection of two
decisive sets is decisive. -/
theorem arrow_step_4 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S T : Set ι}
    (hS : Decisive A F S) (hT : Decisive A F T) : Decisive A F (S ∩ T) := by
  classical
  obtain ⟨x, y, -, hxy, -, -⟩ := id hX
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  refine arrow_step_3 hX hA hF hP hI hxy fun p hp hST hN => ?_
  let q : Profile ι X := fun i => scorePref
    (if i ∈ S then (if i ∈ T then rank3 x z y else rank3 z y x)
      else (if i ∈ T then rank3 y x z else rank3 y z x))
  have hq : q ∈ A := hA.score_mem _
  have a1 := rank3_strict (Ne.symm hzx) hxy hzy
  have a2 := rank3_strict hzy hzx (Ne.symm hxy)
  have a3 := rank3_strict (Ne.symm hxy) (Ne.symm hzy) (Ne.symm hzx)
  have a4 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have hzy' : Strict (F q) z y := hS z y hzy q hq (fun i hi => by
      by_cases hiT : i ∈ T
      · simpa only [q, hi, hiT, ↓reduceIte] using a1.2.1
      · simpa only [q, hi, hiT, ↓reduceIte] using a2.1) (fun i hi => by
      by_cases hiT : i ∈ T
      · simpa only [q, hi, hiT, ↓reduceIte] using a3.2.2
      · simpa only [q, hi, hiT, ↓reduceIte] using a4.1)
  have hxz : Strict (F q) x z := hT x z (Ne.symm hzx) q hq (fun i hi => by
      by_cases hiS : i ∈ S
      · simpa only [q, hi, hiS, ↓reduceIte] using a1.1
      · simpa only [q, hi, hiS, ↓reduceIte] using a3.2.1) (fun i hi => by
      by_cases hiS : i ∈ S
      · simpa only [q, hi, hiS, ↓reduceIte] using a2.2.2
      · simpa only [q, hi, hiS, ↓reduceIte] using a4.2.1)
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) hxz hzy')
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact Or.inl ⟨hST i ⟨hiS, hiT⟩, by simpa only [q, hiS, hiT, ↓reduceIte] using a1.2.2⟩
  · refine Or.inr (Or.inl ⟨hN i fun h => hiT h.2, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a2.2.1
  · refine Or.inr (Or.inl ⟨hN i fun h => hiS h.1, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a3.1
  · refine Or.inr (Or.inl ⟨hN i fun h => hiS h.1, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a4.2.2

/-- **Step 5** of the proof of Proposition 21.C.1 (MWG, p. 798). For any `S`, either `S` or
its complement is decisive. -/
theorem arrow_step_5 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) (S : Set ι) :
    Decisive A F S ∨ Decisive A F Sᶜ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hX
  let q : Profile ι X := fun i => scorePref (if i ∈ S then rank3 x z y else rank3 y x z)
  have hq : q ∈ A := hA.score_mem _
  have a1 := rank3_strict hxz hxy (Ne.symm hyz)
  have a2 := rank3_strict (Ne.symm hxy) hyz hxz
  by_cases hF1 : Strict (F q) x y
  · left
    refine arrow_step_3 ⟨x, y, z, hxy, hxz, hyz⟩ hA hF hP hI hxy fun p hp hS hN => ?_
    refine hI.strict_transfer hp hq (fun i => ?_) hF1
    by_cases hi : i ∈ S
    · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using a1.2.2⟩
    · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using a2.1⟩)
  · right
    have hyx : F q y x := weak_of_not_strict (hF q hq).1 hF1
    have hxz' : Strict (F q) x z := hP q hq x z fun i => by
      by_cases hi : i ∈ S
      · simpa only [q, hi, ↓reduceIte] using a1.1
      · simpa only [q, hi, ↓reduceIte] using a2.2.1
    have hyz' : Strict (F q) y z := strict_of_weak_strict (hF q hq) hyx hxz'
    refine arrow_step_3 ⟨x, y, z, hxy, hxz, hyz⟩ hA hF hP hI hyz fun p hp hS hN => ?_
    refine hI.strict_transfer hp hq (fun i => ?_) hyz'
    by_cases hi : i ∈ S
    · refine Or.inr (Or.inl ⟨hN i (by simpa using hi), ?_⟩)
      simpa only [q, hi, ↓reduceIte] using a1.2.1
    · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using a2.2.2⟩

/-- **Step 6** of the proof of Proposition 21.C.1 (MWG, p. 798), first remark: by the Pareto
property the empty set of agents is not decisive. -/
theorem arrow_empty_not_decisive (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hP : Paretian A F) : ¬Decisive A F ∅ := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hX
  intro hD
  let q : Profile ι X := fun _ => scorePref (rank3 y x z)
  have hq : q ∈ A := hA.score_mem _
  have a := rank3_strict (Ne.symm hxy) hyz hxz
  have h1 : Strict (F q) x y := hD x y hxy q hq (fun _ hi => absurd hi (Set.notMem_empty _))
    (fun _ _ => a.1)
  exact strict_asymm h1 (hP q hq y x fun _ => a.1)

/-- **Step 6** of the proof of Proposition 21.C.1 (MWG, p. 798). A superset of a decisive set
is decisive. -/
theorem arrow_step_6 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S T : Set ι}
    (hS : Decisive A F S) (hST : S ⊆ T) : Decisive A F T := by
  rcases arrow_step_5 hX hA hF hP hI T with h | h
  · exact h
  · exfalso
    have h' := arrow_step_4 hX hA hF hP hI hS h
    have he : S ∩ Tᶜ = ∅ := by
      ext i
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      exact fun hi => hST hi
    rw [he] at h'
    exact arrow_empty_not_decisive hX hA hP h'

/-- **Step 7** of the proof of Proposition 21.C.1 (MWG, p. 798). A decisive set with more than
one agent has a decisive strict subset. -/
theorem arrow_step_7 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) (S : Finset ι) (hS : Decisive A F ↑S)
    (hcard : 1 < S.card) : ∃ S' ⊂ S, Decisive A F ↑S' := by
  classical
  obtain ⟨h, hh⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  by_cases hD : Decisive A F ↑(S.erase h)
  · exact ⟨S.erase h, Finset.erase_ssubset hh, hD⟩
  · rcases arrow_step_5 hX hA hF hP hI ↑(S.erase h) with h1 | h1
    · exact absurd h1 hD
    · have h2 := arrow_step_4 hX hA hF hP hI hS h1
      have he : (↑S ∩ (↑(S.erase h) : Set ι)ᶜ : Set ι) = ↑({h} : Finset ι) := by
        ext i
        simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_compl_iff, Finset.mem_erase,
          not_and, Finset.coe_singleton, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hi, hi'⟩
          by_contra hne
          exact hi' hne hi
        · rintro rfl
          exact ⟨hh, fun h' => absurd rfl h'⟩
      rw [he] at h2
      refine ⟨{h}, ?_, h2⟩
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.singleton_subset_iff.2 hh, fun he' => ?_⟩
      rw [← he', Finset.card_singleton] at hcard
      exact lt_irrefl _ hcard

/-- **Step 8** of the proof of Proposition 21.C.1 (MWG, p. 798). Some single agent forms a
decisive set (the set of all agents is decisive by the Pareto property, and Step 7 is
iterated; we take a decisive set of minimal cardinality). -/
theorem arrow_step_8 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) : ∃ h, Decisive A F {h} := by
  classical
  have := Fintype.ofFinite ι
  have huniv : Decisive A F ↑(Finset.univ : Finset ι) :=
    fun x y _ p hp hS _ => hP p hp x y fun i => hS i (by simp)
  let D := (Finset.univ : Finset (Finset ι)).filter fun T : Finset ι => Decisive A F (↑T : Set ι)
  have hmem : (Finset.univ : Finset ι) ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huniv
  have hne : D.Nonempty := ⟨Finset.univ, hmem⟩
  obtain ⟨T, hT, hmin⟩ := D.exists_min_image Finset.card hne
  have hTd : Decisive A F ↑T := (Finset.mem_filter.1 hT).2
  rcases Nat.lt_or_ge 1 T.card with h2 | h1
  · obtain ⟨S', hS'T, hS'⟩ := arrow_step_7 hX hA hF hP hI T hTd h2
    have h3 := hmin S' (by simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
                           exact hS')
    have h4 := Finset.card_lt_card hS'T
    omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1'
    · rw [Finset.card_eq_zero] at h0
      subst h0
      exact absurd (by simpa using hTd) (arrow_empty_not_decisive hX hA hP)
    · obtain ⟨h, rfl⟩ := Finset.card_eq_one.1 h1'
      exact ⟨h, by simpa using hTd⟩

/-- Scores putting `x` and `y` jointly on top (score 2), `z` next (score 1). -/
noncomputable def pairTop (x y z : X) : X → ℕ :=
  by classical exact fun w => if w = x ∨ w = y then 2 else if w = z then 1 else 0

/-- **Step 9** of the proof of Proposition 21.C.1 (MWG, pp. 798-799). A decisive set is
completely decisive for every `x` over every `y`. (For agents outside `S` indifferent between
`x` and `y` we use `x ∼ y ≻ z`; see the module docstring.) -/
theorem arrow_step_9 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S : Set ι}
    (hS : Decisive A F S) {x y : X} (hxy : x ≠ y) : CompletelyDecisiveFor A F S x y := by
  classical
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  intro p hp hSp
  let q : Profile ι X := fun i =>
    if i ∈ S then scorePref (rank3 x z y)
    else if Strict (p i) y x then scorePref (rank3 y z x)
    else if Strict (p i) x y then scorePref (rank3 x y z)
    else natPref (pairTop x y z)
  have ptx : pairTop x y z x = 2 := by simp [pairTop]
  have pty : pairTop x y z y = 2 := by simp [pairTop]
  have ptz : pairTop x y z z = 1 := by simp [pairTop, hzx, hzy]
  have a1 := rank3_strict (Ne.symm hzx) hxy hzy
  have a2 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have a3 := rank3_strict hxy (Ne.symm hzx) (Ne.symm hzy)
  have nxz : Strict (natPref (pairTop x y z)) x z := (natPref_strict_iff _ _ _).2 (by omega)
  have nyz : Strict (natPref (pairTop x y z)) y z := (natPref_strict_iff _ _ _).2 (by omega)
  have nxy : Indifferent (natPref (pairTop x y z)) x y :=
    (natPref_indifferent_iff _ _ _).2 (by omega)
  have hq : q ∈ A := by
    rcases hA with rfl | rfl
    · intro i
      simp only [q]
      split_ifs
      · exact strictPrefs_subset (scorePref_mem _)
      · exact strictPrefs_subset (scorePref_mem _)
      · exact strictPrefs_subset (scorePref_mem _)
      · exact natPref_rational _
    · intro i
      simp only [q]
      split_ifs with h1 h2 h3
      · exact scorePref_mem _
      · exact scorePref_mem _
      · exact scorePref_mem _
      · exfalso
        have hc := (hp i).1.1
        exact hxy ((hp i).2 x y (weak_of_not_strict hc h2) (weak_of_not_strict hc h3))
  let U : Set ι := S ∪ {i | ¬Strict (p i) y x}
  have hU : Decisive A F U := arrow_step_6 hX hA hF hP hI hS Set.subset_union_left
  have hxz : Strict (F q) x z := hU x z (Ne.symm hzx) q hq (fun i hi => by
      by_cases h1 : i ∈ S
      · simpa only [q, h1, ↓reduceIte] using a1.1
      · have h2 : ¬Strict (p i) y x := by
          rcases hi with hi | hi
          · exact absurd hi h1
          · exact hi
        by_cases h3 : Strict (p i) x y
        · simpa only [q, h1, h2, h3, ↓reduceIte] using a3.2.2
        · simpa only [q, h1, h2, h3, ↓reduceIte] using nxz) (fun i hi => by
      have h1 : i ∉ S := fun h => hi (Or.inl h)
      have h2 : Strict (p i) y x := by
        by_contra h
        exact hi (Or.inr h)
      simpa only [q, h1, h2, ↓reduceIte] using a2.2.1)
  have hzy' : Strict (F q) z y := hS z y hzy q hq (fun i hi => by
      simpa only [q, hi, ↓reduceIte] using a1.2.1) (fun i hi => by
      by_cases h2 : Strict (p i) y x
      · simpa only [q, hi, h2, ↓reduceIte] using a2.1
      · by_cases h3 : Strict (p i) x y
        · simpa only [q, hi, h2, h3, ↓reduceIte] using a3.2.1
        · simpa only [q, hi, h2, h3, ↓reduceIte] using nyz)
  have hagree : ∀ i, (p i x y ↔ q i x y) ∧ (p i y x ↔ q i y x) := by
    intro i
    apply agree_of_same_ranking
    by_cases h1 : i ∈ S
    · exact Or.inl ⟨hSp i h1, by simpa only [q, h1, ↓reduceIte] using a1.2.2⟩
    · by_cases h2 : Strict (p i) y x
      · exact Or.inr (Or.inl ⟨h2, by simpa only [q, h1, h2, ↓reduceIte] using a2.2.2⟩)
      · by_cases h3 : Strict (p i) x y
        · exact Or.inl ⟨h3, by simpa only [q, h1, h2, h3, ↓reduceIte] using a3.1⟩
        · have hc := (hA.rational hp i).1
          refine Or.inr (Or.inr ⟨⟨weak_of_not_strict hc h2, weak_of_not_strict hc h3⟩, ?_⟩)
          simpa only [q, h1, h2, h3, ↓reduceIte] using nxy
  have hfin := strict_trans (hF q hq) hxz hzy'
  have := hI p hp q hq x y hagree
  exact ⟨this.1.2 hfin.1, fun h' => hfin.2 (this.2.1 h')⟩

/-- **Step 10** of the proof of Proposition 21.C.1 (MWG, p. 799). If `{h}` is decisive, then
`h` is a dictator. -/
theorem arrow_step_10 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {h : ι}
    (hh : Decisive A F {h}) : IsDictator A F h := by
  intro p hp x y hxy
  have hne : x ≠ y := by
    rintro rfl
    exact hxy.2 hxy.1
  exact arrow_step_9 hX hA hF hP hI hh hne p hp fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    exact hi ▸ hxy

/-- **Proposition 21.C.1 (Arrow's impossibility theorem)** (MWG, p. 796). With at least three
alternatives, finitely many agents and domain `𝓡^I` or `𝓟^I`, every Paretian social welfare
functional satisfying the pairwise independence condition is dictatorial. -/
theorem proposition_21_C_1 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) : Dictatorial A F := by
  obtain ⟨h, hh⟩ := arrow_step_8 hX hA hF hP hI
  exact ⟨h, arrow_step_10 hX hA hF hP hI hh⟩

/-- The dictatorial social welfare functional `F(≿) = ≿ₕ`. -/
def dictatorSWF (h : ι) : Profile ι X → X → X → Prop := fun p => p h

/-- The dictatorial functional is a Paretian, pairwise independent social welfare functional
with dictator `h`, on any standard domain. -/
theorem dictatorSWF_spec {A : Set (Profile ι X)} (hA : StandardDomain A) (h : ι) :
    IsSWF A (dictatorSWF h) ∧ Paretian A (dictatorSWF h) ∧
      PairwiseIndependent A (dictatorSWF h) ∧ IsDictator A (dictatorSWF h) h :=
  ⟨fun _ hp => hA.rational hp h, fun _ _ _ _ hall => hall h,
    fun _ _ _ _ _ _ hagree => hagree h, fun _ _ _ _ hxy => hxy⟩

/-- **Proposition 21.C.1**, non-vacuity (MWG, p. 796). Its hypotheses are jointly satisfiable
(two agents, three alternatives, both domains), and the dictatorship it asserts occurs. -/
theorem proposition_21_C_1_nonvacuous :
    (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      (∀ A : Set (Profile (Fin 2) (Fin 3)), StandardDomain A →
        IsSWF A (dictatorSWF 0) ∧ Paretian A (dictatorSWF 0) ∧
          PairwiseIndependent A (dictatorSWF 0) ∧ Dictatorial A (dictatorSWF 0)) ∧
      StandardDomain (RationalProfiles (Fin 2) (Fin 3)) ∧
      StandardDomain (StrictProfiles (Fin 2) (Fin 3)) := by
  refine ⟨⟨0, 1, 2, by decide, by decide, by decide⟩, fun A hA => ?_, Or.inl rfl, Or.inr rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := dictatorSWF_spec hA (0 : Fin 2)
  exact ⟨h1, h2, h3, ⟨0, h4⟩⟩

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Less than full social rationality: quasitransitivity and acyclicity

MWG, Section 21.D, pp. 799-801: Definition 21.D.1, footnote 9, Examples 21.D.1 (oligarchy) and
21.D.2 (vetoers), and Exercises 21.D.1-21.D.3.

For a complete (hence reflexive) relation `≿`, quasitransitivity asks that the strict part be
transitive, and acyclicity that every finite set of alternatives have a `≿`-maximal element.
We prove footnote 9 (quasitransitive implies acyclic; rational implies quasitransitive), that
the oligarchy aggregator is Paretian, pairwise independent and quasitransitive but not
transitive (Exercise 21.D.2) and, with two or more oligarchs, not dictatorial; that the vetoers
aggregator is acyclic but not quasitransitive, with a profile where `x` is the only maximal
alternative despite agent 2's veto (Exercise 21.D.3); that the Condorcet relation is not
acyclic; and Exercise 21.D.1.

**Correction.** Definition 21.D.1(ii) and Exercise 21.D.1 quantify over *every* finite subset
(resp. every strict subset), including the empty set, which has no maximal element; read
literally no relation is acyclic (`acyclic_as_printed_false`). We require the subsets to be
nonempty.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- **Definition 21.D.1(i)** (MWG, p. 800). `≿` is quasitransitive: its strict part is
transitive. (MWG assumes `≿` reflexive and complete.) -/
def Quasitransitive (r : X → X → Prop) : Prop :=
  ∀ x y z, Strict r x y → Strict r y z → Strict r x z

/-- **Definition 21.D.1(ii)** (MWG, p. 800), corrected. `≿` is acyclic: every nonempty finite
set of alternatives has a maximal element. -/
def Acyclic (r : X → X → Prop) : Prop :=
  ∀ Y : Finset X, Y.Nonempty → ∃ x ∈ Y, ∀ y ∈ Y, r x y

/-- **Definition 21.D.1(ii)** (MWG, p. 800), as printed: a maximal element in every finite
subset, the empty set included. -/
def AcyclicAsPrinted (r : X → X → Prop) : Prop :=
  ∀ Y : Finset X, ∃ x ∈ Y, ∀ y ∈ Y, r x y

/-- **Definition 21.D.1(ii)**, correction (MWG, p. 800). Read literally, no relation is
acyclic: the empty subset has no maximal element. -/
theorem acyclic_as_printed_false (r : X → X → Prop) : ¬AcyclicAsPrinted r := by
  intro h
  obtain ⟨x, hx, -⟩ := h ∅
  exact absurd hx (Finset.notMem_empty x)

/-- **Footnote 9** (MWG, p. 800). A complete quasitransitive relation is acyclic. (Proved by
induction on the finite set rather than by the book's chain argument.) -/
theorem footnote_21_9_acyclic {r : X → X → Prop} (hc : Complete r) (hq : Quasitransitive r) :
    Acyclic r := by
  classical
  intro Y hY
  induction Y using Finset.induction_on with
  | empty => exact absurd hY (by simp)
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, by simp, fun y hy => ?_⟩
      have hya : y = a := by simpa using hy
      rw [hya]
      exact complete_refl hc a
    · obtain ⟨m, hm, hmax⟩ := ih hs
      by_cases ham : Strict r a m
      · refine ⟨a, mem_insert_self a s, fun y hy => ?_⟩
        rcases mem_insert.1 hy with rfl | hy
        · exact complete_refl hc y
        · by_contra hay
          have hya : Strict r y a := ⟨(hc a y).resolve_left hay, hay⟩
          exact (hq y a m hya ham).2 (hmax y hy)
      · refine ⟨m, mem_insert_of_mem hm, fun y hy => ?_⟩
        rcases mem_insert.1 hy with rfl | hy
        · exact weak_of_not_strict hc ham
        · exact hmax y hy

/-- **Section 21.D** (MWG, p. 800). A rational relation is quasitransitive. -/
theorem rational_quasitransitive {r : X → X → Prop} (hr : Rational r) : Quasitransitive r :=
  fun _ _ _ h1 h2 => strict_trans hr h1 h2

/-- **Section 21.D** (MWG, p. 800). A rational relation has a maximal element on every
nonempty finite set (MWG Chapter 1, footnote 6). -/
theorem rational_acyclic {r : X → X → Prop} (hr : Rational r) : Acyclic r :=
  footnote_21_9_acyclic hr.1 (rational_quasitransitive hr)

/-- **Example 21.D.1** (MWG, p. 800). The oligarchy aggregator for the oligarchy `S`:
`x` is socially at least as good as `y` iff some oligarch `h ∈ S` has `x ≿ₕ y`. -/
def oligarchyRel (S : Set ι) (p : Profile ι X) (x y : X) : Prop := ∃ h ∈ S, p h x y

/-- **Example 21.D.1** (MWG, p. 800). `x` is socially preferred to `y` iff every oligarch
strictly prefers `x` to `y` (for a nonempty oligarchy and complete individual preferences). -/
theorem example_21_D_1_strict {S : Set ι} (hS : S.Nonempty) {p : Profile ι X}
    (hp : ∀ i, Complete (p i)) (x y : X) :
    Strict (oligarchyRel S p) x y ↔ ∀ h ∈ S, Strict (p h) x y := by
  constructor
  · rintro ⟨-, hn⟩ h hh
    refine ⟨(hp h x y).resolve_right fun hyx => hn ⟨h, hh, hyx⟩, fun hyx => hn ⟨h, hh, hyx⟩⟩
  · intro hall
    obtain ⟨h, hh⟩ := hS
    exact ⟨⟨h, hh, (hall h hh).1⟩, fun ⟨k, hk, hyx⟩ => (hall k hk).2 hyx⟩

/-- **Example 21.D.1** (MWG, p. 800). For a nonempty oligarchy and a rational profile, the
social relation is reflexive, complete and quasitransitive (Exercise 21.D.2, first part). -/
theorem exercise_21_D_2_quasitransitive {S : Set ι} (hS : S.Nonempty) {p : Profile ι X}
    (hp : ∀ i, Rational (p i)) :
    (∀ x, oligarchyRel S p x x) ∧ Complete (oligarchyRel S p) ∧
      Quasitransitive (oligarchyRel S p) := by
  obtain ⟨h, hh⟩ := hS
  refine ⟨fun x => ⟨h, hh, complete_refl (hp h).1 x⟩, fun x y => ?_, fun x y z hxy hyz => ?_⟩
  · rcases (hp h).1 x y with h1 | h1
    · exact Or.inl ⟨h, hh, h1⟩
    · exact Or.inr ⟨h, hh, h1⟩
  · have hc : ∀ i, Complete (p i) := fun i => (hp i).1
    rw [example_21_D_1_strict ⟨h, hh⟩ hc] at hxy hyz ⊢
    exact fun k hk => strict_trans (hp k) (hxy k hk) (hyz k hk)

/-- **Example 21.D.1** (MWG, p. 800). The oligarchy aggregator is Paretian and pairwise
independent on `𝓡^I`. -/
theorem example_21_D_1_paretian_independent {S : Set ι} (hS : S.Nonempty) :
    Paretian (RationalProfiles ι X) (oligarchyRel S) ∧
      PairwiseIndependent (RationalProfiles ι X) (oligarchyRel S) := by
  refine ⟨fun p hp x y hall => ?_, fun p _ p' _ x y hag => ?_⟩
  · exact (example_21_D_1_strict hS (fun i => (hp i).1) x y).2 fun h _ => hall h
  · exact ⟨⟨fun ⟨h, hh, h1⟩ => ⟨h, hh, (hag h).1.1 h1⟩, fun ⟨h, hh, h1⟩ =>
      ⟨h, hh, (hag h).1.2 h1⟩⟩, ⟨fun ⟨h, hh, h1⟩ => ⟨h, hh, (hag h).2.1 h1⟩,
      fun ⟨h, hh, h1⟩ => ⟨h, hh, (hag h).2.2 h1⟩⟩⟩

/-- **Example 21.D.1** (MWG, p. 800). A one-member oligarchy `{h}` is the dictatorship of `h`;
the oligarchy of all agents expresses a strict preference only under unanimity. -/
theorem example_21_D_1_extremes (p : Profile ι X) (h : ι) (hp : ∀ i, Complete (p i))
    [Nonempty ι] (x y : X) :
    oligarchyRel {h} p = p h ∧
      (Strict (oligarchyRel Set.univ p) x y ↔ ∀ i, Strict (p i) x y) := by
  refine ⟨?_, ?_⟩
  · funext a b
    simp [oligarchyRel]
  · rw [example_21_D_1_strict Set.univ_nonempty hp]
    simp

/-- **Example 21.D.1** (MWG, p. 800). With two distinct oligarchs and two distinct
alternatives, the oligarchy aggregator has no dictator on `𝓡^I`: the Pareto and pairwise
independence conditions hold, the dictatorship conclusion of Arrow's theorem fails, and it is
transitivity that is lost. -/
theorem example_21_D_1_not_dictatorial {S : Set ι} {h₁ h₂ : ι} (h1 : h₁ ∈ S)
    (h2 : h₂ ∈ S) (h12 : h₁ ≠ h₂) {x y : X} (hxy : x ≠ y) :
    ¬Dictatorial (RationalProfiles ι X) (oligarchyRel S) := by
  classical
  rintro ⟨h, hh⟩
  let sx : X → ℕ := fun w => if w = x then 1 else 0
  let sy : X → ℕ := fun w => if w = y then 1 else 0
  let p : Profile ι X := fun i => scorePref (if i = h then sx else sy)
  have hp : p ∈ RationalProfiles ι X := fun i => strictPrefs_subset (scorePref_mem _)
  have hhx : Strict (p h) x y := by
    simp only [p, ↓reduceIte]
    exact scorePref_strict_of_lt (by simp [sx, Ne.symm hxy])
  have hoth : ∀ i, i ≠ h → Strict (p i) y x := fun i hi => by
    simp only [p, hi, ↓reduceIte]
    exact scorePref_strict_of_lt (by simp [sy, hxy])
  obtain ⟨k, hk, hkh⟩ : ∃ k ∈ S, k ≠ h := by
    by_cases e : h₁ = h
    · exact ⟨h₂, h2, fun e' => h12 (e.trans e'.symm)⟩
    · exact ⟨h₁, h1, e⟩
  exact (hh p hp x y hhx).2 ⟨k, hk, (hoth k hkh).1⟩

/-- **Exercise 21.D.2** (MWG, p. 812). For the oligarchy of two agents with `x ≻₁ y ≻₁ z` and
`y ≻₂ z ≻₂ x` (alternatives `0, 1, 2`), `x` and `y` are socially indifferent, as are `x` and
`z`, but `y` is socially preferred to `z`: social indifference is not transitive, so the social
preference is not transitive. -/
theorem exercise_21_D_2_not_transitive :
    let p : Profile (Fin 2) (Fin 3) := fun i => natPref (![![3, 2, 1], ![1, 3, 2]] i)
    Indifferent (oligarchyRel Set.univ p) 0 1 ∧ Indifferent (oligarchyRel Set.univ p) 0 2 ∧
      Strict (oligarchyRel Set.univ p) 1 2 ∧ ¬TransitivePref (oligarchyRel Set.univ p) := by
  intro p
  have key : ∀ a b, oligarchyRel Set.univ p a b ↔
      (![![3, 2, 1], ![1, 3, 2]] 0 b ≤ ![![3, 2, 1], ![1, 3, 2]] 0 a ∨
        ![![3, 2, 1], ![1, 3, 2]] 1 b ≤ ![![3, 2, 1], ![1, 3, 2]] 1 a) := by
    intro a b
    simp only [oligarchyRel, Set.mem_univ, true_and, p, natPref, Fin.exists_fin_two]
  have hs : Strict (oligarchyRel Set.univ p) 1 2 := by
    simp only [Strict, key]
    decide
  refine ⟨by simp only [Indifferent, key]; decide, by simp only [Indifferent, key]; decide, hs,
    fun ht => ?_⟩
  have h21 : oligarchyRel Set.univ p 2 0 := (key 2 0).2 (by decide)
  have h01 : oligarchyRel Set.univ p 0 1 := (key 0 1).2 (by decide)
  exact hs.2 (ht 2 0 1 h21 h01)

/-- **Example 21.D.2** (MWG, pp. 800-801). Vetoers, with alternatives `x, y, z = 0, 1, 2` and
agents `1, 2 = 0, 1`: social preference is agent 1's, except that agent 2 can veto `x` being
socially preferred to `y`: `v` is socially at least as good as `w` iff `v ≿₁ w`, or `v = y`,
`w = x` and `y ≻₂ x`. -/
def vetoRel (p : Profile (Fin 2) (Fin 3)) (v w : Fin 3) : Prop :=
  p 0 v w ∨ (v = 1 ∧ w = 0 ∧ Strict (p 1) 1 0)

/-- Strict social preference under the vetoers rule implies agent 1's strict preference. -/
theorem vetoRel_strict {p : Profile (Fin 2) (Fin 3)} (hc : Complete (p 0)) {v w : Fin 3}
    (h : Strict (vetoRel p) v w) : Strict (p 0) v w :=
  ⟨(hc v w).resolve_right fun h' => h.2 (Or.inl h'), fun h' => h.2 (Or.inl h')⟩

/-- **Exercise 21.D.3**, first part (MWG, p. 813). For any rational profile, the vetoers
relation is reflexive, complete and acyclic. -/
theorem exercise_21_D_3_acyclic {p : Profile (Fin 2) (Fin 3)} (hp : ∀ i, Rational (p i)) :
    (∀ v, vetoRel p v v) ∧ Complete (vetoRel p) ∧ Acyclic (vetoRel p) := by
  refine ⟨fun v => Or.inl (complete_refl (hp 0).1 v), fun v w => ?_, fun Y hY => ?_⟩
  · rcases (hp 0).1 v w with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · obtain ⟨m, hm, hmax⟩ := rational_acyclic (hp 0) Y hY
    exact ⟨m, hm, fun y hy => Or.inl (hmax y hy)⟩

/-- **Exercise 21.D.3**, second and third parts (MWG, p. 813). With `x ≻₁ z ≻₁ y` and
`y ≻₂ x` (here `y ≻₂ x ≻₂ z`), socially `x ≻ z` and `z ≻ y` but `x ∼ y`: the vetoers relation
is not quasitransitive. Yet `x` is the only maximal alternative for the social preference, in
spite of agent 2's veto power. -/
theorem exercise_21_D_3_not_quasitransitive :
    let p : Profile (Fin 2) (Fin 3) := fun i => natPref (![![3, 1, 2], ![2, 3, 1]] i)
    Strict (vetoRel p) 0 2 ∧ Strict (vetoRel p) 2 1 ∧ Indifferent (vetoRel p) 0 1 ∧
      ¬Quasitransitive (vetoRel p) ∧
      ∀ m : Fin 3, (∀ v, vetoRel p m v) ↔ m = 0 := by
  intro p
  have key : ∀ v w, vetoRel p v w ↔ (![![3, 1, 2], ![2, 3, 1]] 0 w ≤
      ![![3, 1, 2], ![2, 3, 1]] 0 v ∨ (v = 1 ∧ w = 0 ∧
        (![![3, 1, 2], ![2, 3, 1]] 1 0 < ![![3, 1, 2], ![2, 3, 1]] 1 1))) := by
    intro v w
    simp only [vetoRel, p, natPref_strict_iff]
    rfl
  have h02 : Strict (vetoRel p) 0 2 := by simp only [Strict, key]; decide
  have h21 : Strict (vetoRel p) 2 1 := by simp only [Strict, key]; decide
  have h01 : Indifferent (vetoRel p) 0 1 := by simp only [Indifferent, key]; decide
  refine ⟨h02, h21, h01, fun hq => (hq 0 2 1 h02 h21).2 h01.2, fun m => ?_⟩
  simp only [key]
  revert m
  decide

/-- **Section 21.D** (MWG, p. 800). The social preference of the Condorcet paradox (Example
21.C.2) violates acyclicity: `{x, y, z}` has no maximal element. -/
theorem condorcet_not_acyclic : ¬Acyclic (majorityRel condorcetProfile) := by
  intro h
  obtain ⟨m, hm, hmax⟩ := h {0, 1, 2} (by simp)
  obtain ⟨h01, h12, h20⟩ := condorcet_majority
  fin_cases m
  · exact h20.2 (hmax 2 (by simp))
  · exact h01.2 (hmax 0 (by simp))
  · exact h12.2 (hmax 1 (by simp))

/-- The cyclic relation `x ≻ y ≻ z ≻ x` on `{x, y, z} = {0, 1, 2}`, made reflexive
(Exercise 21.D.1). -/
def cyclicRel (a b : Fin 3) : Prop := a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

/-- **Exercise 21.D.1** (MWG, p. 812), corrected to nonempty subsets. On the finite set
`X = {x, y, z}`, the reflexive, complete relation `x ≻ y ≻ z ≻ x` has a maximal element on every
nonempty strict subset of `X`, and yet it is not acyclic. (As printed, "every strict subset"
includes `∅`, on which no relation has a maximal element.) -/
theorem exercise_21_D_1 :
    (∀ a, cyclicRel a a) ∧ Complete cyclicRel ∧
      (∀ Y : Finset (Fin 3), Y ≠ univ → Y.Nonempty → ∃ x ∈ Y, ∀ y ∈ Y, cyclicRel x y) ∧
      ¬Acyclic cyclicRel := by
  refine ⟨fun a => Or.inl rfl, ?_, ?_, ?_⟩
  · unfold Complete cyclicRel
    decide
  · unfold cyclicRel
    decide
  · intro h
    obtain ⟨m, -, hmax⟩ := h univ univ_nonempty
    revert hmax
    unfold cyclicRel
    revert m
    decide

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Single-peaked preferences and the median voter

MWG, Section 21.D, pp. 801-804: Definitions 21.D.2-21.D.5, Example 21.D.3, Propositions 21.D.1
and 21.D.2 and the surrounding claims, and Exercises 21.D.5, 21.D.6 and 21.D.11.

The linear order `≥` on the alternatives is a `LinearOrder X` instance (Definition 21.D.2 is
also stated for relations, with the bridge `linearOrderRel_of_linearOrder` and its converse
`linearOrderOfRel`). A rational `≿` is single peaked with peak `x` if preference strictly
increases towards `x` on each side of it (Definition 21.D.3); the peak is then the unique best
alternative. We prove: a median agent exists (with at least one agent) and is unique when
peaks are distinct and the number of agents is odd; Proposition 21.D.1 (the median peak is a
Condorcet winner, and with an odd number of agents it strictly defeats every other
alternative); the claim that pairwise majority voting on `𝓡_≥^I` is acyclic; Proposition
21.D.2 (with an odd number of agents, majority voting on `𝓟_≥^I` is transitive, a social
welfare functional with values in `𝓟`); Exercise 21.D.5 (the Condorcet preferences are single
peaked for no linear order); Exercise 21.D.6 (two agents, intransitive majority); Exercise
21.D.11 (a Paretian, pairwise independent functional on `𝓟_≥^I` that is not majority voting
by an odd oligarchy).

**Proof note (acyclicity).** MWG says Proposition 21.D.1 "guarantees" acyclicity. Restricting a
single-peaked preference with indifferences to a finite subset need not give a single-peaked
preference (ties across the peak), so Proposition 21.D.1 does not apply directly. We split each
agent into two agents that break ties to the left and to the right; this doubles every margin
`#{x ≻ y} - #{y ≻ x}` and yields linear single-peaked orders, whose restrictions are single
peaked.

**Corrections.** A median agent exists only if there is at least one agent (the book's "always
exists" fails for `I = 0`).
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- **Definition 21.D.2** (MWG, p. 801). A binary relation `≥` (written `ge a b` for `a ≥ b`)
is a linear order: reflexive, transitive and total (for distinct `x, y`, exactly one of
`x ≥ y`, `y ≥ x`). -/
def IsLinearOrderRel (ge : X → X → Prop) : Prop :=
  (∀ x, ge x x) ∧ (∀ x y z, ge x y → ge y z → ge x z) ∧
    ∀ x y, x ≠ y → (ge x y ∨ ge y x) ∧ ¬(ge x y ∧ ge y x)

/-- **Example 21.D.3** (MWG, p. 801), generalized: the `≥` of any linear order is a linear order
in the sense of Definition 21.D.2; in particular the natural order of any `X ⊆ ℝ`. -/
theorem linearOrderRel_of_linearOrder [LinearOrder X] :
    IsLinearOrderRel fun a b : X => b ≤ a :=
  ⟨fun _ => le_rfl, fun _ _ _ h1 h2 => le_trans h2 h1, fun _ _ hxy =>
    ⟨le_total _ _, fun h => hxy (le_antisymm h.2 h.1)⟩⟩

/-- The reversed order `≤` of a linear order is again a linear order in the sense of
Definition 21.D.2. -/
theorem linearOrderRel_dual [LinearOrder X] : IsLinearOrderRel fun a b : X => a ≤ b :=
  ⟨fun _ => le_rfl, fun _ _ _ h1 h2 => le_trans h1 h2, fun _ _ hxy =>
    ⟨le_total _ _, fun h => hxy (le_antisymm h.1 h.2)⟩⟩

/-- **Example 21.D.3** (MWG, p. 801). For `X ⊆ ℝ`, the natural order is a linear order. -/
theorem example_21_D_3 (S : Set ℝ) : IsLinearOrderRel fun a b : S => (b : ℝ) ≤ a :=
  linearOrderRel_of_linearOrder

/-- Every linear order in the sense of Definition 21.D.2 comes from a `LinearOrder` structure,
with `a ≤ b` iff `b ≥ a`. -/
noncomputable abbrev linearOrderOfRel (ge : X → X → Prop) (h : IsLinearOrderRel ge) :
    LinearOrder X where
  le a b := ge b a
  le_refl a := h.1 a
  le_trans a b c hab hbc := h.2.1 c b a hbc hab
  le_antisymm a b hab hba := by
    by_contra hne
    exact (h.2.2 a b hne).2 ⟨hba, hab⟩
  le_total a b := by
    by_cases hab : a = b
    · subst hab
      exact Or.inl (h.1 a)
    · exact ((h.2.2 a b hab).1).symm
  toDecidableLE := Classical.decRel _

variable [LinearOrder X]

/-- **Definition 21.D.3** (MWG, p. 801). `x` is a peak of `≿` with respect to `≥`: if
`x ≥ z > y` then `z ≻ y`, and if `y > z ≥ x` then `z ≻ y`. -/
def IsPeak (r : X → X → Prop) (x : X) : Prop :=
  ∀ y z, (z ≤ x → y < z → Strict r z y) ∧ (x ≤ z → z < y → Strict r z y)

/-- **Definition 21.D.3** (MWG, p. 801). A rational `≿` is single peaked with respect to `≥`. -/
def SinglePeaked (r : X → X → Prop) : Prop := Rational r ∧ ∃ x, IsPeak r x

/-- **Definition 21.D.3** (MWG, p. 801). The peak is strictly preferred to every other
alternative ("a peak of satisfaction"). -/
theorem IsPeak.strict_best {r : X → X → Prop} {x : X} (hx : IsPeak r x) {y : X} (hy : y ≠ x) :
    Strict r x y := by
  rcases lt_or_gt_of_ne hy with h | h
  · exact (hx y x).1 le_rfl h
  · exact (hx y x).2 le_rfl h

/-- **Definition 21.D.3** (MWG, p. 801). There cannot be any other peak. -/
theorem IsPeak.unique {r : X → X → Prop} {x x' : X} (hx : IsPeak r x) (hx' : IsPeak r x') :
    x = x' := by
  by_contra hne
  exact strict_asymm (hx.strict_best (Ne.symm hne)) (hx'.strict_best hne)

/-- **Definition 21.D.4** (MWG, p. 801). The set `𝓡_≥` of rational preferences single peaked
with respect to `≥`. -/
def SinglePeakedPrefs (X : Type*) [LinearOrder X] : Set (X → X → Prop) := {r | SinglePeaked r}

/-- The set `𝓟_≥` of single-peaked preferences with no indifference (MWG, p. 803). -/
def StrictSinglePeakedPrefs (X : Type*) [LinearOrder X] : Set (X → X → Prop) :=
  {r | SinglePeaked r ∧ NoIndifference r}

/-- The domain `𝓡_≥^I`. -/
def SinglePeakedProfiles (ι X : Type*) [LinearOrder X] : Set (Profile ι X) :=
  {p | ∀ i, p i ∈ SinglePeakedPrefs X}

/-- The domain `𝓟_≥^I`. -/
def StrictSinglePeakedProfiles (ι X : Type*) [LinearOrder X] : Set (Profile ι X) :=
  {p | ∀ i, p i ∈ StrictSinglePeakedPrefs X}

/-- `𝓟_≥^I ⊆ 𝓡_≥^I`. -/
theorem strictSinglePeaked_subset :
    StrictSinglePeakedProfiles ι X ⊆ SinglePeakedProfiles ι X := fun _ hp i => (hp i).1

/-- `𝓟_≥^I ⊆ 𝓟^I`. -/
theorem strictSinglePeaked_subset_strict :
    StrictSinglePeakedProfiles ι X ⊆ StrictProfiles ι X :=
  fun _ hp i => ⟨(hp i).1.1, (hp i).2⟩

/-- A Condorcet winner: an alternative that no other alternative defeats by majority voting
(MWG, p. 802). -/
def IsCondorcetWinner [Fintype ι] (p : Profile ι X) (x : X) : Prop := ∀ y, majorityRel p x y

/-- **Definition 21.D.5** (MWG, p. 802). Agent `h` is a median agent for the peaks `pk`:
`#{i : xᵢ ≥ xₕ} ≥ I/2` and `#{i : xₕ ≥ xᵢ} ≥ I/2` (stated as `I ≤ 2 #…`). -/
def IsMedianAgent [Fintype ι] (pk : ι → X) (h : ι) : Prop :=
  Fintype.card ι ≤ 2 * (univ.filter fun i => pk h ≤ pk i).card ∧
    Fintype.card ι ≤ 2 * (univ.filter fun i => pk i ≤ pk h).card

/-- **Definition 21.D.5** (MWG, p. 802). A median agent exists, provided there is at least one
agent. -/
theorem median_exists [Fintype ι] [Nonempty ι] (pk : ι → X) : ∃ h, IsMedianAgent pk h := by
  classical
  let M := univ.filter fun h : ι => Fintype.card ι ≤ 2 * (univ.filter fun i => pk h ≤ pk i).card
  obtain ⟨h₀, -, hmin⟩ := (univ : Finset ι).exists_min_image pk univ_nonempty
  have hM : M.Nonempty := ⟨h₀, by
    simp only [M, mem_filter, mem_univ, true_and]
    have : (univ.filter fun i => pk h₀ ≤ pk i) = univ :=
      filter_true_of_mem fun i _ => hmin i (mem_univ i)
    rw [this, card_univ]
    omega⟩
  obtain ⟨h, hhM, hmax⟩ := M.exists_max_image pk hM
  refine ⟨h, (mem_filter.1 hhM).2, ?_⟩
  by_contra hlt
  push Not at hlt
  set G := univ.filter fun i => pk h < pk i with hG
  have hsplit : (univ.filter fun i => pk i ≤ pk h).card + G.card = Fintype.card ι := by
    have e : (univ.filter fun i => ¬pk i ≤ pk h) = G := by
      ext i
      simp [hG]
    have := card_filter_add_card_filter_not (s := univ) (fun i => pk i ≤ pk h)
    rw [e, card_univ] at this
    exact this
  have hGne : G.Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨h', hh'G, hmin'⟩ := G.exists_min_image pk hGne
  have hsub : G ⊆ univ.filter fun i => pk h' ≤ pk i := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact hmin' i hi
  have hh'M : h' ∈ M := by
    simp only [M, mem_filter, mem_univ, true_and]
    have := card_le_card hsub
    omega
  have := hmax h' hh'M
  have hlt' : pk h < pk h' := by simpa [hG] using hh'G
  exact absurd this (not_le.2 hlt')

/-- **Section 21.D** (MWG, p. 802). With no ties in peaks and an odd number of agents, a median
agent has `(I - 1)/2` peaks strictly below and `(I - 1)/2` strictly above its own, and it is
unique. -/
theorem median_odd_unique [Fintype ι] {pk : ι → X} (hinj : Function.Injective pk)
    (hodd : Odd (Fintype.card ι)) {h : ι} (hh : IsMedianAgent pk h) :
    2 * (univ.filter fun i => pk i < pk h).card + 1 = Fintype.card ι ∧
      2 * (univ.filter fun i => pk h < pk i).card + 1 = Fintype.card ι ∧
      ∀ h', IsMedianAgent pk h' → h' = h := by
  classical
  have hcount : ∀ k : ι, (univ.filter fun i => pk i < pk k).card +
      (univ.filter fun i => pk k < pk i).card + 1 = Fintype.card ι := by
    intro k
    have e1 : (univ.filter fun i => pk k ≤ pk i) = insert k (univ.filter fun i => pk k < pk i) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le hi with e | e
        · exact Or.inl (hinj e).symm
        · exact Or.inr e
      · rintro (rfl | e)
        · exact le_rfl
        · exact e.le
    have hk : k ∉ univ.filter fun i => pk k < pk i := by simp
    have e2 := card_filter_add_card_filter_not (s := univ) (fun i => pk i < pk k)
    have e3 : (univ.filter fun i => ¬pk i < pk k) = univ.filter fun i => pk k ≤ pk i := by
      ext i
      simp
    rw [e3, e1, card_insert_of_notMem hk, card_univ] at e2
    omega
  have hle : ∀ k : ι, (univ.filter fun i => pk k ≤ pk i).card =
      (univ.filter fun i => pk k < pk i).card + 1 := by
    intro k
    have : (univ.filter fun i => pk k ≤ pk i) = insert k (univ.filter fun i => pk k < pk i) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le hi with e | e
        · exact Or.inl (hinj e).symm
        · exact Or.inr e
      · rintro (rfl | e)
        · exact le_rfl
        · exact e.le
    rw [this, card_insert_of_notMem (by simp)]
  have hge : ∀ k : ι, (univ.filter fun i => pk i ≤ pk k).card =
      (univ.filter fun i => pk i < pk k).card + 1 := by
    intro k
    have : (univ.filter fun i => pk i ≤ pk k) = insert k (univ.filter fun i => pk i < pk k) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le hi with e | e
        · exact Or.inl (hinj e)
        · exact Or.inr e
      · rintro (rfl | e)
        · exact le_rfl
        · exact e.le
    rw [this, card_insert_of_notMem (by simp)]
  obtain ⟨m, hm⟩ := hodd
  have key : ∀ k, IsMedianAgent pk k →
      2 * (univ.filter fun i => pk i < pk k).card + 1 = Fintype.card ι ∧
      2 * (univ.filter fun i => pk k < pk i).card + 1 = Fintype.card ι := by
    intro k hk
    have h1 := hk.1
    have h2 := hk.2
    rw [hle k] at h1
    rw [hge k] at h2
    have := hcount k
    omega
  refine ⟨(key h hh).1, (key h hh).2, fun h' hh' => ?_⟩
  by_contra hne
  have hk1 := key h hh
  have hk2 := key h' hh'
  rcases lt_or_gt_of_ne (fun e => hne (hinj e)) with hlt | hlt
  · have hsub : insert h' (univ.filter fun i => pk i < pk h') ⊆
        univ.filter fun i => pk i < pk h := by
      intro i hi
      simp only [mem_insert, mem_filter, mem_univ, true_and] at hi ⊢
      rcases hi with rfl | hi
      · exact hlt
      · exact hi.trans hlt
    have := card_le_card hsub
    rw [card_insert_of_notMem (by simp)] at this
    omega
  · have hsub : insert h (univ.filter fun i => pk i < pk h) ⊆
        univ.filter fun i => pk i < pk h' := by
      intro i hi
      simp only [mem_insert, mem_filter, mem_univ, true_and] at hi ⊢
      rcases hi with rfl | hi
      · exact hlt
      · exact hi.trans hlt
    have := card_le_card hsub
    rw [card_insert_of_notMem (by simp)] at this
    omega

open Classical in
omit [LinearOrder X] in
/-- Counting core of Proposition 21.D.1: if a set `S` of at least half the agents strictly
prefers `m` to `y`, then `m` is not defeated by `y`; with an odd number of agents, `m`
strictly defeats `y`. -/
theorem majority_of_supporters [Fintype ι] (p : Profile ι X) {m y : X} (S : Finset ι)
    (hS : Fintype.card ι ≤ 2 * S.card) (hpref : ∀ i ∈ S, Strict (p i) m y) :
    majorityRel p m y ∧ (Odd (Fintype.card ι) →
      (univ.filter fun i => Strict (p i) y m).card <
        (univ.filter fun i => Strict (p i) m y).card) := by
  classical
  have h1 : S ⊆ univ.filter fun i => Strict (p i) m y := fun i hi => by
    simpa using hpref i hi
  have h2 : (univ.filter fun i => Strict (p i) y m) ⊆ univ \ S := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_sdiff, mem_univ, true_and]
    exact fun hiS => strict_asymm (hpref i hiS) hi
  have c1 := card_le_card h1
  have c2 := card_le_card h2
  rw [card_sdiff_of_subset (subset_univ S), card_univ] at c2
  refine ⟨?_, fun ⟨k, hk⟩ => ?_⟩
  · rw [majorityRel_iff]
    omega
  · omega

open Classical in
/-- **Proposition 21.D.1** (MWG, p. 802). If every agent's preference is single peaked with
peak `xᵢ` and `h` is a median agent, then `xₕ` is not defeated by any alternative in pairwise
majority voting: it is a Condorcet winner. With an odd number of agents it strictly defeats
every other alternative. -/
theorem proposition_21_D_1 [Fintype ι] {p : Profile ι X} {pk : ι → X}
    (hpk : ∀ i, IsPeak (p i) (pk i)) {h : ι} (hh : IsMedianAgent pk h) :
    IsCondorcetWinner p (pk h) ∧ (Odd (Fintype.card ι) → ∀ y, y ≠ pk h →
      (univ.filter fun i => Strict (p i) y (pk h)).card <
        (univ.filter fun i => Strict (p i) (pk h) y).card) := by
  classical
  have key : ∀ y, y ≠ pk h → majorityRel p (pk h) y ∧ (Odd (Fintype.card ι) →
      (univ.filter fun i => Strict (p i) y (pk h)).card <
        (univ.filter fun i => Strict (p i) (pk h) y).card) := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · exact majority_of_supporters p _ hh.1 fun i hi =>
        (hpk i y (pk h)).1 (by simpa using hi) hlt
    · exact majority_of_supporters p _ hh.2 fun i hi =>
        (hpk i y (pk h)).2 (by simpa using hi) hgt
  refine ⟨fun y => ?_, fun hodd y hy => (key y hy).2 hodd⟩
  by_cases hy : y = pk h
  · subst hy
    rw [majorityRel_iff]
  · exact (key y hy).1

/-- **Proposition 21.D.1** (MWG, p. 802). A Condorcet winner exists whenever all preferences
are single peaked with respect to the same linear order (and there is at least one agent; with
no agents every alternative is a Condorcet winner). -/
theorem proposition_21_D_1_exists [Fintype ι] [Nonempty X] {p : Profile ι X}
    (hp : p ∈ SinglePeakedProfiles ι X) : ∃ x, IsCondorcetWinner p x := by
  classical
  by_cases hι : Nonempty ι
  · choose pk hpk using fun i => (hp i).2
    obtain ⟨h, hh⟩ := median_exists pk
    exact ⟨pk h, (proposition_21_D_1 hpk hh).1⟩
  · obtain ⟨x⟩ := ‹Nonempty X›
    refine ⟨x, fun y => ?_⟩
    rw [majorityRel_iff]
    have : IsEmpty ι := not_nonempty_iff.1 hι
    simp [Finset.univ_eq_empty]

/-- Restricted peak: for a single-peaked linear order (no indifference) with peak `x`, and a
`≿`-best element `b` of a set `Y`, preference strictly increases towards `b` within `Y`. -/
theorem IsPeak.restrict {r : X → X → Prop} {x : X} (hx : IsPeak r x)
    (hn : NoIndifference r) {Y : Set X} {b : X} (hbest : ∀ w ∈ Y, r b w) {y z : X}
    (hy : y ∈ Y) (hz : z ∈ Y) :
    (z ≤ b → y < z → Strict r z y) ∧ (b ≤ z → z < y → Strict r z y) := by
  have best_strict : ∀ w ∈ Y, w ≠ b → Strict r b w := fun w hw hwb =>
    ⟨hbest w hw, fun h => hwb (hn w b h (hbest w hw))⟩
  constructor
  · intro hzb hyz
    by_cases hzx : z ≤ x
    · exact (hx y z).1 hzx hyz
    · push Not at hzx
      rcases eq_or_lt_of_le hzb with e | e
      · subst e
        exact best_strict y hy (ne_of_lt hyz)
      · exact absurd (hbest z hz) ((hx b z).2 hzx.le e).2
  · intro hbz hzy
    by_cases hxz : x ≤ z
    · exact (hx y z).2 hxz hzy
    · push Not at hxz
      rcases eq_or_lt_of_le hbz with e | e
      · subst e
        exact best_strict y hy (ne_of_gt hzy)
      · exact absurd (hbest z hz) ((hx b z).1 hxz.le e).2

open Classical in
/-- Majority voting over a profile of single-peaked linear orders has a Condorcet winner within
every nonempty finite set `Y`; with an odd number of agents it strictly defeats every other
member of `Y`. -/
theorem strict_singlePeaked_condorcet_finset [Fintype ι] {p : Profile ι X}
    (hp : p ∈ StrictSinglePeakedProfiles ι X) (Y : Finset X) (hY : Y.Nonempty) :
    ∃ m ∈ Y, ∀ y ∈ Y, majorityRel p m y ∧ (Odd (Fintype.card ι) → y ≠ m →
      (univ.filter fun i => Strict (p i) y m).card <
        (univ.filter fun i => Strict (p i) m y).card) := by
  classical
  by_cases hι : Nonempty ι
  · have hb : ∀ i, ∃ b ∈ Y, ∀ w ∈ Y, p i b w := fun i => rational_acyclic (hp i).1.1 Y hY
    choose b hbY hbest using hb
    obtain ⟨h, hh⟩ := median_exists b
    refine ⟨b h, hbY h, fun y hy => ?_⟩
    have hpk : ∀ i, ∃ x, IsPeak (p i) x := fun i => (hp i).1.2
    choose pk hpk using hpk
    have hres : ∀ i, ∀ y ∈ Y, ∀ z ∈ Y, (z ≤ b i → y < z → Strict (p i) z y) ∧
        (b i ≤ z → z < y → Strict (p i) z y) := fun i y hy z hz =>
      (hpk i).restrict (hp i).2 (Y := ↑Y) (fun w hw => hbest i w hw) hy hz
    by_cases hym : y = b h
    · subst hym
      refine ⟨by rw [majorityRel_iff], fun _ hne => absurd rfl hne⟩
    · rcases lt_or_gt_of_ne hym with hlt | hgt
      · obtain ⟨h1, h2⟩ := majority_of_supporters p _ hh.1 fun i hi =>
          (hres i y hy (b h) (hbY h)).1 (by simpa using hi) hlt
        exact ⟨h1, fun hodd _ => h2 hodd⟩
      · obtain ⟨h1, h2⟩ := majority_of_supporters p _ hh.2 fun i hi =>
          (hres i y hy (b h) (hbY h)).2 (by simpa using hi) hgt
        exact ⟨h1, fun hodd _ => h2 hodd⟩
  · obtain ⟨m, hm⟩ := hY
    have : IsEmpty ι := not_nonempty_iff.1 hι
    refine ⟨m, hm, fun y _ => ⟨by rw [majorityRel_iff]; simp [Finset.univ_eq_empty], ?_⟩⟩
    intro hodd
    rw [Fintype.card_eq_zero] at hodd
    exact absurd hodd (by decide)

omit [LinearOrder X] in
/-- Break the ties of `≿` with a linear order: towards smaller alternatives (`left = true`) or
towards larger ones (`left = false`). -/
def tieBreak (le : X → X → Prop) (r : X → X → Prop) : X → X → Prop :=
  fun a b => Strict r a b ∨ (Indifferent r a b ∧ le a b)

omit [LinearOrder X] in
/-- Breaking the ties of a rational relation with a linear order gives a rational relation with
no indifference that keeps every strict preference. -/
theorem tieBreak_spec {le : X → X → Prop} (hle : IsLinearOrderRel fun a b => le b a)
    {r : X → X → Prop} (hr : Rational r) :
    tieBreak le r ∈ StrictPrefs X ∧ ∀ a b, Strict r a b → Strict (tieBreak le r) a b := by
  have hrefl : ∀ a, le a a := hle.1
  have htrans : ∀ a b c, le a b → le b c → le a c := fun a b c h1 h2 => hle.2.1 c b a h2 h1
  have hstr : ∀ a b, Strict r a b → Strict (tieBreak le r) a b := fun a b h =>
    ⟨Or.inl h, fun h' => by
      rcases h' with h' | h'
      · exact strict_asymm h h'
      · exact h.2 h'.1.1⟩
  refine ⟨⟨⟨fun a b => ?_, fun a b c hab hbc => ?_⟩, fun a b hab hba => ?_⟩, hstr⟩
  · by_cases h1 : Strict r a b
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : Strict r b a
      · exact Or.inr (Or.inl h2)
      · have hi : Indifferent r a b := ⟨weak_of_not_strict hr.1 h2, weak_of_not_strict hr.1 h1⟩
        by_cases hab : a = b
        · subst hab
          exact Or.inl (Or.inr ⟨hi, hrefl a⟩)
        · rcases (hle.2.2 b a (Ne.symm hab)).1 with h | h
          · exact Or.inl (Or.inr ⟨hi, h⟩)
          · exact Or.inr (Or.inr ⟨⟨hi.2, hi.1⟩, h⟩)
  · rcases hab with hab | hab <;> rcases hbc with hbc | hbc
    · exact Or.inl (strict_trans hr hab hbc)
    · exact Or.inl ⟨hr.2 a b c hab.1 hbc.1.1, fun hca => hab.2 (hr.2 b c a hbc.1.1 hca)⟩
    · exact Or.inl (strict_of_weak_strict hr hab.1.1 hbc)
    · exact Or.inr ⟨⟨hr.2 a b c hab.1.1 hbc.1.1, hr.2 c b a hbc.1.2 hab.1.2⟩,
        htrans a b c hab.2 hbc.2⟩
  · rcases hab with hab | hab
    · rcases hba with hba | hba
      · exact absurd hba (strict_asymm hab)
      · exact absurd hba.1.1 hab.2
    · rcases hba with hba | hba
      · exact absurd hab.1.1 hba.2
      · by_contra hne
        exact (hle.2.2 b a (Ne.symm hne)).2 ⟨hab.2, hba.2⟩

/-- The doubled profile: agent `(i, false)` breaks `≿ᵢ`'s ties to the left, agent `(i, true)`
to the right. -/
def doubleProfile (p : Profile ι X) : Profile (ι × Bool) X :=
  fun j => if j.2 then tieBreak (fun a b => b ≤ a) (p j.1) else tieBreak (fun a b => a ≤ b) (p j.1)

open Classical in
/-- The doubled profile counts every strict preference twice and every indifference between
distinct alternatives once, in each direction. -/
theorem doubleProfile_card [Fintype ι] {p : Profile ι X} (hp : ∀ i, Rational (p i)) {a b : X}
    (hab : a ≠ b) :
    (univ.filter fun j => Strict (doubleProfile p j) a b).card =
      2 * (univ.filter fun i => Strict (p i) a b).card +
        (univ.filter fun i => Indifferent (p i) a b).card := by
  classical
  have hL := fun i => tieBreak_spec (le := fun a b : X => a ≤ b)
    (linearOrderRel_of_linearOrder (X := X)) (hp i)
  have hR := fun i => tieBreak_spec (le := fun a b : X => b ≤ a)
    (linearOrderRel_dual (X := X)) (hp i)
  simp only [card_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, doubleProfile, ↓reduceIte, Bool.false_eq_true]
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases h1 : Strict (p i) a b
  · have e1 := (hR i).2 a b h1
    have e2 := (hL i).2 a b h1
    have h3 : ¬Indifferent (p i) a b := fun h => h1.2 h.2
    simp [e1, e2, h1, h3]
  · by_cases h2 : Strict (p i) b a
    · have e1 := strict_asymm ((hR i).2 b a h2)
      have e2 := strict_asymm ((hL i).2 b a h2)
      have h3 : ¬Indifferent (p i) a b := fun h => h2.2 h.1
      simp [e1, e2, h1, h3]
    · have hi : Indifferent (p i) a b :=
        ⟨weak_of_not_strict (hp i).1 h2, weak_of_not_strict (hp i).1 h1⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have e1 : ¬Strict (tieBreak (fun a b : X => b ≤ a) (p i)) a b := fun h => by
          rcases h.1 with h' | h'
          · exact h1 h'
          · exact absurd h'.2 (not_le.2 hlt)
        have e2 : Strict (tieBreak (fun a b : X => a ≤ b) (p i)) a b :=
          ⟨Or.inr ⟨hi, hlt.le⟩, fun h => by
            rcases h with h' | h'
            · exact h2 h'
            · exact absurd h'.2 (not_le.2 hlt)⟩
        simp [e1, e2, h1, hi]
      · have e1 : Strict (tieBreak (fun a b : X => b ≤ a) (p i)) a b :=
          ⟨Or.inr ⟨hi, hgt.le⟩, fun h => by
            rcases h with h' | h'
            · exact h2 h'
            · exact absurd h'.2 (not_le.2 hgt)⟩
        have e2 : ¬Strict (tieBreak (fun a b : X => a ≤ b) (p i)) a b := fun h => by
          rcases h.1 with h' | h'
          · exact h1 h'
          · exact absurd h'.2 (not_le.2 hgt)
        simp [e1, e2, h1, hi]

/-- The doubled profile has the same majority relation as the original one. -/
theorem majorityRel_doubleProfile [Fintype ι] {p : Profile ι X} (hp : ∀ i, Rational (p i))
    (a b : X) : majorityRel (doubleProfile p) a b ↔ majorityRel p a b := by
  classical
  by_cases hab : a = b
  · subst hab
    simp only [majorityRel_iff, le_refl]
  rw [majorityRel_iff, majorityRel_iff, doubleProfile_card hp hab,
    doubleProfile_card hp (Ne.symm hab)]
  have : (univ.filter fun i => Indifferent (p i) b a) =
      univ.filter fun i => Indifferent (p i) a b := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [this]
  omega

/-- The doubled profile of a single-peaked profile consists of single-peaked linear orders. -/
theorem doubleProfile_mem {p : Profile ι X} (hp : p ∈ SinglePeakedProfiles ι X) :
    doubleProfile p ∈ StrictSinglePeakedProfiles (ι × Bool) X := by
  intro j
  obtain ⟨i, s⟩ := j
  obtain ⟨hr, x, hx⟩ := hp i
  have key : ∀ le : X → X → Prop, IsLinearOrderRel (fun a b => le b a) →
      tieBreak le (p i) ∈ StrictSinglePeakedPrefs X := fun le hle => by
    obtain ⟨hm, hs⟩ := tieBreak_spec hle hr
    exact ⟨⟨hm.1, x, fun y z => ⟨fun h1 h2 => hs z y ((hx y z).1 h1 h2),
      fun h1 h2 => hs z y ((hx y z).2 h1 h2)⟩⟩, hm.2⟩
  cases s
  · exact key _ (linearOrderRel_of_linearOrder (X := X))
  · exact key _ (linearOrderRel_dual (X := X))

/-- **Section 21.D** (MWG, p. 803). On `𝓡_≥^I`, the social preference generated by pairwise
majority voting is acyclic (Definition 21.D.1). -/
theorem majorityRel_acyclic [Fintype ι] {p : Profile ι X} (hp : p ∈ SinglePeakedProfiles ι X) :
    Acyclic (majorityRel p) := by
  intro Y hY
  obtain ⟨m, hm, hmax⟩ := strict_singlePeaked_condorcet_finset (doubleProfile_mem hp) Y hY
  exact ⟨m, hm, fun y hy => (majorityRel_doubleProfile (fun i => (hp i).1) m y).1
    (hmax y hy).1⟩

omit [LinearOrder X] in
open Classical in
/-- **Section 21.D** (MWG, p. 803). With an odd number of agents and preferences in `𝓟_≥`,
for every pair of distinct alternatives there is a strict majority for one of them. -/
theorem strict_majority_odd [Fintype ι] {p : Profile ι X} (hp : p ∈ StrictProfiles ι X)
    (hodd : Odd (Fintype.card ι)) {a b : X} (hab : a ≠ b) :
    (univ.filter fun i => Strict (p i) a b).card ≠
      (univ.filter fun i => Strict (p i) b a).card := by
  classical
  have hsplit : (univ.filter fun i => Strict (p i) a b).card +
      (univ.filter fun i => Strict (p i) b a).card = Fintype.card ι := by
    have e : (univ.filter fun i => ¬Strict (p i) a b) =
        univ.filter fun i => Strict (p i) b a := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h
        rcases (hp i).1.1 a b with h1 | h1
        · exact absurd ⟨h1, fun h2 => hab ((hp i).2 a b h1 h2)⟩ h
        · exact ⟨h1, fun h2 => hab ((hp i).2 a b h2 h1)⟩
      · intro h h'
        exact strict_asymm h h'
    have := card_filter_add_card_filter_not (s := univ) (fun i => Strict (p i) a b)
    rw [e, card_univ] at this
    exact this
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Proposition 21.D.2** (MWG, p. 803). If the number of agents is odd, pairwise majority
voting is a social welfare functional on `𝓟_≥^I`: the social relation is complete and
transitive. It moreover has no indifference between distinct alternatives (values in `𝓟`). -/
theorem proposition_21_D_2 [Fintype ι] (hodd : Odd (Fintype.card ι)) :
    IsSWF (StrictSinglePeakedProfiles ι X) majorityRel ∧
      ∀ p ∈ StrictSinglePeakedProfiles ι X, majorityRel p ∈ StrictPrefs X := by
  classical
  have hnoind : ∀ p ∈ StrictSinglePeakedProfiles ι X, NoIndifference (majorityRel p) := by
    intro p hp a b hab hba
    by_contra hne
    rw [majorityRel_iff] at hab hba
    exact strict_majority_odd (strictSinglePeaked_subset_strict hp) hodd hne (by omega)
  have htrans : ∀ p ∈ StrictSinglePeakedProfiles ι X, TransitivePref (majorityRel p) := by
    intro p hp x y z hxy hyz
    by_cases e1 : x = y
    · subst e1
      exact hyz
    by_cases e2 : y = z
    · subst e2
      exact hxy
    by_cases e3 : x = z
    · subst e3
      rw [majorityRel_iff]
    obtain ⟨m, hm, hmax⟩ := strict_singlePeaked_condorcet_finset hp {x, y, z} (by simp)
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact (hmax z (by simp)).1
    · exact absurd (hnoind p hp _ _ hxy (hmax x (by simp)).1) e1
    · exact absurd (hnoind p hp _ _ hyz (hmax y (by simp)).1) e2
  refine ⟨fun p hp => ⟨majorityRel_complete p, htrans p hp⟩, fun p hp =>
    ⟨⟨majorityRel_complete p, htrans p hp⟩, hnoind p hp⟩⟩

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises on single-peaked preferences

MWG, Exercises 21.D.5, 21.D.6 and 21.D.11, pp. 813-814, and the claim of Exercise 21.D.11 that
majority voting by an odd oligarchy is a Paretian, pairwise independent social welfare
functional `𝓟_≥^I → 𝓟`.

Exercise 21.D.5 is proved for every linear order on `{x, y, z}` (each alternative is the worst
one for some agent of the Condorcet paradox, and the middle alternative of a single-peaked
preference is never the worst). Exercise 21.D.6 uses two agents on `{0, 1, 2}`. For Exercise
21.D.11 we add two "phantom" voters with the fixed preference `0 ≻ 1 ≻ 2` to three agents and
take majority voting among the five voters.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- Three distinct elements of a linear order: one of them lies strictly between the other
two. -/
theorem three_middle {α : Type*} [LinearOrder α] {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    (x < y ∧ y < z) ∨ (z < y ∧ y < x) ∨ (y < x ∧ x < z) ∨ (z < x ∧ x < y) ∨
      (x < z ∧ z < y) ∨ (y < z ∧ z < x) := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxz with h3 | h3 <;> grind

/-- An alternative lying strictly between two others is never the worst alternative of a
single-peaked preference. -/
theorem IsPeak.middle_not_worst [LinearOrder X] {r : X → X → Prop} {x : X} (hx : IsPeak r x)
    {a m c : X} (ham : a < m) (hmc : m < c) : Strict r m a ∨ Strict r m c := by
  by_cases h : m ≤ x
  · exact Or.inl ((hx a m).1 h ham)
  · push Not at h
    exact Or.inr ((hx c m).2 h.le hmc)

/-- **Exercise 21.D.5** (MWG, p. 813). For none of the linear orders on `{x, y, z}` are the
three preferences of the Condorcet paradox (Example 21.C.2) single peaked. -/
theorem exercise_21_D_5 (L : LinearOrder (Fin 3)) :
    ¬∀ i, @SinglePeaked (Fin 3) L (condorcetProfile i) := by
  intro h
  choose pk hpk using fun i => (h i).2
  have worst : ∀ i m a, MWG.PreferenceChoice.condorcetRank i m = 0 →
      ¬Strict (condorcetProfile i) m a := by
    intro i m a h0 hs
    rw [condorcetProfile, natPref_strict_iff, h0] at hs
    exact Nat.not_lt_zero _ hs
  have mid := fun i (a m c : Fin 3) h1 h2 (h0 : MWG.PreferenceChoice.condorcetRank i m = 0) =>
    (@IsPeak.middle_not_worst (Fin 3) L _ _ (hpk i) a m c h1 h2).elim (worst i m a h0)
      (worst i m c h0)
  have w0 : MWG.PreferenceChoice.condorcetRank 2 0 = 0 := rfl
  have w1 : MWG.PreferenceChoice.condorcetRank 1 1 = 0 := rfl
  have w2 : MWG.PreferenceChoice.condorcetRank 0 2 = 0 := rfl
  rcases @three_middle (Fin 3) L 0 1 2 (by decide) (by decide) (by decide)
    with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mid 1 0 1 2 h1 h2 w1
  · exact mid 1 2 1 0 h1 h2 w1
  · exact mid 2 1 0 2 h1 h2 w0
  · exact mid 2 2 0 1 h1 h2 w0
  · exact mid 0 0 2 1 h1 h2 w2
  · exact mid 0 1 2 0 h1 h2 w2

/-- A preference on `Fin 3` given by a utility, single peaked at `x` for the natural order, can
be checked by computation. -/
theorem natPref_singlePeaked_of_isPeak {u : Fin 3 → ℕ} {x : Fin 3}
    (h : ∀ y z : Fin 3, (z ≤ x → y < z → u y < u z) ∧ (x ≤ z → z < y → u y < u z)) :
    SinglePeaked (natPref u) :=
  ⟨natPref_rational u, x, fun y z => ⟨fun h1 h2 => (natPref_strict_iff u z y).2 ((h y z).1 h1 h2),
    fun h1 h2 => (natPref_strict_iff u z y).2 ((h y z).2 h1 h2)⟩⟩

/-- The profile of Exercise 21.D.6: agent 1 has `0 ≻ 1 ≻ 2` (peak `0`), agent 2 has
`1 ≻ 2 ≻ 0` (peak `1`). -/
def exercise21D6Profile : Profile (Fin 2) (Fin 3) := fun i => natPref (![![2, 1, 0], ![0, 2, 1]] i)

/-- **Exercise 21.D.6** (MWG, p. 813). With an even number of agents (two) and preferences
single peaked for the natural order of `{0, 1, 2}`, pairwise majority voting is not
transitive: `2 ∼ 0` and `0 ∼ 1` socially, but `1 ≻ 2`. -/
theorem exercise_21_D_6 :
    exercise21D6Profile ∈ SinglePeakedProfiles (Fin 2) (Fin 3) ∧
      Indifferent (majorityRel exercise21D6Profile) 2 0 ∧
      Indifferent (majorityRel exercise21D6Profile) 0 1 ∧
      Strict (majorityRel exercise21D6Profile) 1 2 ∧
      ¬TransitivePref (majorityRel exercise21D6Profile) := by
  have key : exercise21D6Profile = fun i => natPref (![![2, 1, 0], ![0, 2, 1]] i) := rfl
  have hs : Strict (majorityRel exercise21D6Profile) 1 2 := by
    rw [key]
    simp only [Strict, majorityRel_natPref]
    decide
  refine ⟨fun i => ?_, ?_, ?_, hs, fun ht => ?_⟩
  · fin_cases i
    · exact natPref_singlePeaked_of_isPeak (x := 0) (by decide)
    · exact natPref_singlePeaked_of_isPeak (x := 1) (by decide)
  · rw [key]
    simp only [Indifferent, majorityRel_natPref]
    decide
  · rw [key]
    simp only [Indifferent, majorityRel_natPref]
    decide
  · have h20 : majorityRel exercise21D6Profile 2 0 := by
      rw [key, majorityRel_natPref]
      decide
    have h01 : majorityRel exercise21D6Profile 0 1 := by
      rw [key, majorityRel_natPref]
      decide
    exact hs.2 (ht 2 0 1 h20 h01)

/-- Majority voting by the oligarchy `S` (Exercise 21.D.11): pairwise majority among the
members of `S`. -/
noncomputable def oligarchyMajority (S : Finset ι) (p : Profile ι X) :
    X → X → Prop :=
  majorityRel fun i : S => p i

/-- **Exercise 21.D.11** (MWG, p. 814), the class it describes. For an odd number of oligarchs,
majority voting by the oligarchy is a Paretian, pairwise independent social welfare functional
`𝓟_≥^I → 𝓟` (Proposition 21.D.2 applied to the oligarchs). -/
theorem exercise_21_D_11_oligarchy [LinearOrder X] {S : Finset ι}
    (hS : Odd S.card) :
    (∀ p ∈ StrictSinglePeakedProfiles ι X, oligarchyMajority S p ∈ StrictPrefs X) ∧
      Paretian (StrictSinglePeakedProfiles ι X) (oligarchyMajority S) ∧
      PairwiseIndependent (StrictSinglePeakedProfiles ι X) (oligarchyMajority S) := by
  classical
  have hcard : Odd (Fintype.card S) := by simpa using hS
  refine ⟨fun p hp => (proposition_21_D_2 hcard).2 _ fun i => hp i, ?_, ?_⟩
  · intro p _ x y hall
    obtain ⟨k, hk⟩ := hS
    have hne : (univ : Finset S).Nonempty := by
      rw [univ_nonempty_iff]
      obtain ⟨a, ha⟩ : S.Nonempty := by
        rw [← card_pos]
        omega
      exact ⟨⟨a, ha⟩⟩
    unfold oligarchyMajority
    rw [Strict, majorityRel_iff, majorityRel_iff]
    have e1 : (univ.filter fun i : S => Strict (p i) y x) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact strict_asymm (hall i)
    have e2 : (univ.filter fun i : S => Strict (p i) x y) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact hall i
    rw [e1, e2, card_empty]
    have := card_pos.2 hne
    omega
  · intro p _ p' _ x y hag
    unfold oligarchyMajority
    have e : ∀ i : ι, (Strict (p i) x y ↔ Strict (p' i) x y) ∧
        (Strict (p i) y x ↔ Strict (p' i) y x) := fun i => by
      refine ⟨?_, ?_⟩ <;> simp only [Strict, (hag i).1, (hag i).2]
    have f1 : (univ.filter fun i : S => Strict (p i) x y) =
        univ.filter fun i : S => Strict (p' i) x y := by
      ext i
      simp [(e i).1]
    have f2 : (univ.filter fun i : S => Strict (p i) y x) =
        univ.filter fun i : S => Strict (p' i) y x := by
      ext i
      simp [(e i).2]
    rw [majorityRel_iff, majorityRel_iff, majorityRel_iff, majorityRel_iff, f1, f2]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- The preference `0 ≻ 1 ≻ 2` of the phantom voters (Exercise 21.D.11). -/
def phantomUtil : Fin 3 → ℕ := ![2, 1, 0]

/-- Three agents and two phantom voters with the preference `0 ≻ 1 ≻ 2`. -/
def withPhantoms (p : Profile (Fin 3) (Fin 3)) : Profile (Fin 3 ⊕ Fin 2) (Fin 3) :=
  Sum.elim p fun _ => natPref phantomUtil

/-- The functional of Exercise 21.D.11: majority voting among the three agents and the two
phantom voters. -/
noncomputable def phantomMajority (p : Profile (Fin 3) (Fin 3)) : Fin 3 → Fin 3 → Prop :=
  majorityRel (withPhantoms p)

/-- The phantom preference is single peaked (at `0`) with no indifference. -/
theorem phantom_mem : natPref phantomUtil ∈ StrictSinglePeakedPrefs (Fin 3) :=
  ⟨natPref_singlePeaked_of_isPeak (x := 0) (by decide),
    (natPref_mem_strict (by unfold phantomUtil; decide)).2⟩

/-- Two profiles separating the phantom rule from every odd-oligarchy majority rule. -/
def phantomTestA : Fin 3 → Fin 3 → ℕ := ![![0, 1, 2], ![0, 1, 2], ![2, 1, 0]]

/-- See `phantomTestA`. -/
def phantomTestB : Fin 3 → Fin 3 → ℕ := ![![2, 1, 0], ![2, 1, 0], ![0, 1, 2]]

/-- **Exercise 21.D.11** (MWG, p. 814). Majority voting among three agents and two phantom
voters with `0 ≻ 1 ≻ 2` is a Paretian, pairwise independent social welfare functional
`𝓟_≥^I → 𝓟` (for the natural order of `{0, 1, 2}`), but it is not majority voting by any odd
oligarchy `S ⊆ I`. -/
theorem exercise_21_D_11 :
    (∀ p ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3), phantomMajority p ∈ StrictPrefs (Fin 3)) ∧
      Paretian (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) phantomMajority ∧
      PairwiseIndependent (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) phantomMajority ∧
      ∀ S : Finset (Fin 3), Odd S.card →
        ∃ p ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3),
          phantomMajority p ≠ oligarchyMajority S p := by
  classical
  have hmem : ∀ p ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3),
      withPhantoms p ∈ StrictSinglePeakedProfiles (Fin 3 ⊕ Fin 2) (Fin 3) := by
    intro p hp j
    cases j with
    | inl i => exact hp i
    | inr _ => exact phantom_mem
  have h5 : Odd (Fintype.card (Fin 3 ⊕ Fin 2)) := by decide
  refine ⟨fun p hp => (proposition_21_D_2 h5).2 _ (hmem p hp), ?_, ?_, ?_⟩
  · intro p _ x y hall
    unfold phantomMajority
    rw [Strict, majorityRel_iff, majorityRel_iff]
    have hL : (univ.filter fun j : Fin 3 ⊕ Fin 2 => j.isLeft) ⊆
        univ.filter fun j => Strict (withPhantoms p j) x y := by
      intro j hj
      cases j with
      | inl i => exact Finset.mem_filter.2 ⟨mem_univ _, hall i⟩
      | inr _ => simp at hj
    have hR : (univ.filter fun j => Strict (withPhantoms p j) y x) ⊆
        univ.filter fun j : Fin 3 ⊕ Fin 2 => j.isRight := by
      intro j hj
      cases j with
      | inl i =>
        exact absurd (Finset.mem_filter.1 hj).2 (strict_asymm (hall i))
      | inr _ => simp
    have c1 := card_le_card hL
    have c2 := card_le_card hR
    have e1 : (univ.filter fun j : Fin 3 ⊕ Fin 2 => j.isLeft).card = 3 := by decide
    have e2 : (univ.filter fun j : Fin 3 ⊕ Fin 2 => j.isRight).card = 2 := by decide
    omega
  · intro p _ p' _ x y hag
    unfold phantomMajority
    have e : ∀ j, (Strict (withPhantoms p j) x y ↔ Strict (withPhantoms p' j) x y) ∧
        (Strict (withPhantoms p j) y x ↔ Strict (withPhantoms p' j) y x) := by
      intro j
      cases j with
      | inl i =>
        refine ⟨?_, ?_⟩ <;>
          simp only [withPhantoms, Sum.elim_inl, Strict, (hag i).1, (hag i).2]
      | inr _ => exact ⟨Iff.rfl, Iff.rfl⟩
    have f1 : (univ.filter fun j => Strict (withPhantoms p j) x y) =
        univ.filter fun j => Strict (withPhantoms p' j) x y := by
      ext j
      simp [(e j).1]
    have f2 : (univ.filter fun j => Strict (withPhantoms p j) y x) =
        univ.filter fun j => Strict (withPhantoms p' j) y x := by
      ext j
      simp [(e j).2]
    rw [majorityRel_iff, majorityRel_iff, majorityRel_iff, majorityRel_iff, f1, f2]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · have hA : (fun i => natPref (phantomTestA i)) ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3) := by
      intro i
      fin_cases i
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 2) (by decide),
          (natPref_mem_strict (by decide)).2⟩
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 2) (by decide),
          (natPref_mem_strict (by decide)).2⟩
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 0) (by decide),
          (natPref_mem_strict (by decide)).2⟩
    have hB : (fun i => natPref (phantomTestB i)) ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3) := by
      intro i
      fin_cases i
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 0) (by decide),
          (natPref_mem_strict (by decide)).2⟩
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 0) (by decide),
          (natPref_mem_strict (by decide)).2⟩
      · exact ⟨natPref_singlePeaked_of_isPeak (x := 2) (by decide),
          (natPref_mem_strict (by decide)).2⟩
    have wA : withPhantoms (fun i => natPref (phantomTestA i)) =
        fun j => natPref (Sum.elim phantomTestA (fun _ => phantomUtil) j) := by
      funext j
      cases j <;> rfl
    have wB : withPhantoms (fun i => natPref (phantomTestB i)) =
        fun j => natPref (Sum.elim phantomTestB (fun _ => phantomUtil) j) := by
      funext j
      cases j <;> rfl
    have fA : ¬phantomMajority (fun i => natPref (phantomTestA i)) 2 0 := by
      unfold phantomMajority
      rw [wA, majorityRel_natPref]
      decide
    have fB : ¬phantomMajority (fun i => natPref (phantomTestB i)) 2 0 := by
      unfold phantomMajority
      rw [wB, majorityRel_natPref]
      decide
    have oA : ∀ S : Finset (Fin 3), Odd S.card → S ≠ {2} →
        oligarchyMajority S (fun i => natPref (phantomTestA i)) 2 0 := by
      intro S
      unfold oligarchyMajority
      rw [majorityRel_natPref (fun i : S => phantomTestA i)]
      revert S
      decide
    have oB : oligarchyMajority {2} (fun i => natPref (phantomTestB i)) 2 0 := by
      unfold oligarchyMajority
      rw [majorityRel_natPref (fun i : ({2} : Finset (Fin 3)) => phantomTestB i)]
      decide
    intro S hS
    by_cases h2 : S = {2}
    · subst h2
      exact ⟨_, hB, fun he => fB (by rw [he]; exact oB)⟩
    · exact ⟨_, hA, fun he => fA (by rw [he]; exact oA S hS h2)⟩

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The conditions of Arrow's theorem are independent; lexical dictatorship

MWG, Exercises 21.C.2 and 21.C.3, p. 812.

Exercise 21.C.2 lists six assumptions of Arrow's theorem: (a) at least three alternatives,
(b) universal domain `𝓡^I`, (c) social rationality, (d) pairwise independence, (e) the Pareto
property, (f) no dictatorship. For each we exhibit a social aggregator satisfying the other five
and failing it: majority voting with two alternatives (a); majority voting on the single-peaked
domain `𝓟_≥^I` with three agents (b); majority voting on `𝓡^I` (c, by the Condorcet paradox);
the Borda count (d); total social indifference (e); a dictatorship (f).

Exercise 21.C.3: the lexical dictatorship (the `n`-th agent's strict preference prevails if all
earlier agents are indifferent) is a rational, Paretian, pairwise independent social welfare
functional on `𝓡^I` (dictatorial, as Arrow's theorem requires), whose social preference need
not coincide with the preference of any individual.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- Pairwise majority voting is Paretian on any domain, provided there is at least one agent. -/
theorem majorityRel_paretian [Fintype ι] [Nonempty ι] (A : Set (Profile ι X)) :
    Paretian A majorityRel := by
  classical
  intro p _ x y hall
  rw [Strict, majorityRel_iff, majorityRel_iff]
  have e1 : (univ.filter fun i => Strict (p i) y x) = ∅ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact strict_asymm (hall i)
  have e2 : (univ.filter fun i => Strict (p i) x y) = univ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, iff_true]
    exact hall i
  rw [e1, e2, card_empty, card_univ]
  have := Fintype.card_pos (α := ι)
  omega

/-- Pairwise majority voting satisfies the pairwise independence condition on any domain. -/
theorem majorityRel_independent [Fintype ι] (A : Set (Profile ι X)) :
    PairwiseIndependent A majorityRel := by
  classical
  intro p _ p' _ x y hag
  have f : ∀ a b, (a = x ∧ b = y) ∨ (a = y ∧ b = x) →
      (univ.filter fun i => Strict (p i) a b) = univ.filter fun i => Strict (p' i) a b := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext i <;> rw [mem_filter, mem_filter] <;>
      simp only [mem_univ, true_and, Strict, (hag i).1, (hag i).2]
  rw [majorityRel_iff, majorityRel_iff, majorityRel_iff, majorityRel_iff,
    f x y (Or.inl ⟨rfl, rfl⟩), f y x (Or.inr ⟨rfl, rfl⟩)]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- With at least three agents, majority voting has no dictator on a domain containing, for
every agent `h`, a profile where `h` strictly prefers `x` to `y` and all others strictly prefer
`y` to `x`. -/
theorem majorityRel_not_dictatorial [Fintype ι] (hI : 3 ≤ Fintype.card ι)
    {A : Set (Profile ι X)} {x y : X}
    (hA : ∀ h, ∃ p ∈ A, Strict (p h) x y ∧ ∀ i, i ≠ h → Strict (p i) y x) :
    ¬Dictatorial A majorityRel := by
  classical
  rintro ⟨h, hh⟩
  obtain ⟨p, hp, hph, hoth⟩ := hA h
  have hs := hh p hp x y hph
  have c1 : (univ.filter fun i => Strict (p i) x y) ⊆ {h} := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    by_contra hne
    exact strict_asymm hi (hoth i (by simpa using hne))
  have c2 : univ.erase h ⊆ univ.filter fun i => Strict (p i) y x := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact hoth i (ne_of_mem_erase hi)
  have d1 := card_le_card c1
  have d2 := card_le_card c2
  rw [card_singleton] at d1
  rw [card_erase_of_mem (mem_univ h), card_univ] at d2
  have := hs.1
  rw [majorityRel_iff] at this
  omega

/-- A profile of natural-number utilities where agent `h` has utility `u` and the others `v`. -/
def splitProfile [DecidableEq ι] (h : ι) (u v : X → ℕ) : Profile ι X :=
  fun i => natPref (if i = h then u else v)

/-- **Exercise 21.C.2(a)** (MWG, p. 812). With two alternatives, majority voting (three agents,
domain `𝓡^I`) is a Paretian, pairwise independent, nondictatorial social welfare functional:
only the assumption of at least three alternatives fails. -/
theorem exercise_21_C_2a :
    ¬(∃ a b c : Fin 2, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      IsSWF (RationalProfiles (Fin 3) (Fin 2)) majorityRel ∧
      Paretian (RationalProfiles (Fin 3) (Fin 2)) majorityRel ∧
      PairwiseIndependent (RationalProfiles (Fin 3) (Fin 2)) majorityRel ∧
      ¬Dictatorial (RationalProfiles (Fin 3) (Fin 2)) majorityRel := by
  refine ⟨by decide, fun p _ => ⟨majorityRel_complete p, fun x y z hxy hyz => ?_⟩,
    majorityRel_paretian _, majorityRel_independent _, ?_⟩
  · by_cases e1 : x = y
    · subst e1
      exact hyz
    by_cases e2 : y = z
    · subst e2
      exact hxy
    have e3 : x = z := by omega
    subst e3
    classical
    rw [majorityRel_iff]
  · refine majorityRel_not_dictatorial (by decide) (x := 0) (y := 1) fun h => ?_
    refine ⟨splitProfile h ![1, 0] ![0, 1], fun i => natPref_rational _, ?_, fun i hi => ?_⟩
    · simp [splitProfile, natPref_strict_iff]
    · simp [splitProfile, hi, natPref_strict_iff]

/-- **Exercise 21.C.2(b)** (MWG, p. 812). On the single-peaked domain `𝓟_≥^I` (three agents,
alternatives `0 < 1 < 2`), majority voting is a Paretian, pairwise independent, nondictatorial
social welfare functional, with three alternatives; only the universal domain fails (the
Condorcet profile is in `𝓡^I` but not in the domain). -/
theorem exercise_21_C_2b :
    (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      StrictSinglePeakedProfiles (Fin 3) (Fin 3) ≠ RationalProfiles (Fin 3) (Fin 3) ∧
      IsSWF (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) majorityRel ∧
      Paretian (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) majorityRel ∧
      PairwiseIndependent (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) majorityRel ∧
      ¬Dictatorial (StrictSinglePeakedProfiles (Fin 3) (Fin 3)) majorityRel := by
  refine ⟨⟨0, 1, 2, by decide, by decide, by decide⟩, fun he => ?_,
    (proposition_21_D_2 (by decide)).1, majorityRel_paretian _, majorityRel_independent _, ?_⟩
  · have hc : condorcetProfile ∈ StrictSinglePeakedProfiles (Fin 3) (Fin 3) := by
      rw [he]
      exact strictProfiles_subset condorcetProfile_mem
    exact exercise_21_D_5 inferInstance fun i => (hc i).1
  · refine majorityRel_not_dictatorial (by decide) (x := 0) (y := 2) fun h => ?_
    refine ⟨splitProfile h ![2, 1, 0] ![0, 1, 2], fun i => ?_, ?_, fun i hi => ?_⟩
    · by_cases hi : i = h
      · simp only [splitProfile, hi, ↓reduceIte]
        exact ⟨natPref_singlePeaked_of_isPeak (x := 0) (by decide),
          (natPref_mem_strict (by decide)).2⟩
      · simp only [splitProfile, hi, ↓reduceIte]
        exact ⟨natPref_singlePeaked_of_isPeak (x := 2) (by decide),
          (natPref_mem_strict (by decide)).2⟩
    · simp [splitProfile, natPref_strict_iff]
    · simp [splitProfile, hi, natPref_strict_iff]

/-- **Exercise 21.C.2(c)** (MWG, p. 812). On `𝓡^I` with three agents and three alternatives,
majority voting is Paretian, pairwise independent and nondictatorial, but social rationality
fails (Example 21.C.2). -/
theorem exercise_21_C_2c :
    Paretian (RationalProfiles (Fin 3) (Fin 3)) majorityRel ∧
      PairwiseIndependent (RationalProfiles (Fin 3) (Fin 3)) majorityRel ∧
      ¬Dictatorial (RationalProfiles (Fin 3) (Fin 3)) majorityRel ∧
      ¬IsSWF (RationalProfiles (Fin 3) (Fin 3)) majorityRel := by
  refine ⟨majorityRel_paretian _, majorityRel_independent _, ?_, example_21_C_2.2.2.2.2.2⟩
  refine majorityRel_not_dictatorial (by decide) (x := 0) (y := 1) fun h => ?_
  refine ⟨splitProfile h ![1, 0, 0] ![0, 1, 0], fun i => natPref_rational _, ?_, fun i hi => ?_⟩
  · simp [splitProfile, natPref_strict_iff]
  · simp [splitProfile, hi, natPref_strict_iff]

/-- **Exercise 21.C.2(d)** (MWG, p. 812). The Borda count (two agents, three alternatives) is a
Paretian, nondictatorial social welfare functional on `𝓡^I` that violates pairwise
independence. -/
theorem exercise_21_C_2d :
    IsSWF (RationalProfiles (Fin 2) (Fin 3)) bordaSWF ∧
      Paretian (RationalProfiles (Fin 2) (Fin 3)) bordaSWF ∧
      ¬Dictatorial (RationalProfiles (Fin 2) (Fin 3)) bordaSWF ∧
      ¬PairwiseIndependent (RationalProfiles (Fin 2) (Fin 3)) bordaSWF := by
  refine ⟨example_21_C_1_rational _, example_21_C_1_paretian, ?_,
    example_21_C_1_two_agents.2.2.2.2⟩
  rintro ⟨h, hh⟩
  have hp : splitProfile h ![3, 2, 1] ![1, 3, 2] ∈ RationalProfiles (Fin 2) (Fin 3) :=
    fun i => natPref_rational _
  have hs := hh _ hp 0 1 (by simp [splitProfile, natPref_strict_iff])
  have key : ∑ i, bordaPoints (splitProfile h ![3, 2, 1] ![1, 3, 2] i) 0 = 4 ∧
      ∑ i, bordaPoints (splitProfile h ![3, 2, 1] ![1, 3, 2] i) 1 = 3 := by
    fin_cases h <;>
      simp only [splitProfile, Fin.sum_univ_two, Fin.zero_eta, Fin.isValue, Fin.mk_one,
        ↓reduceIte, show ((1 : Fin 2) = 0) = False by decide,
        show ((0 : Fin 2) = 1) = False by decide] <;>
      rw [bordaPoints_natPref, bordaPoints_natPref, bordaPoints_natPref, bordaPoints_natPref] <;>
      simp only [Finset.card_filter, Fin.sum_univ_three] <;> norm_num
  have := hs.1
  unfold bordaSWF at this
  rw [key.1, key.2] at this
  norm_num at this

/-- Total social indifference (Exercise 21.C.2(e)). -/
def totalIndifference : Profile ι X → X → X → Prop := fun _ _ _ => True

/-- **Exercise 21.C.2(e)** (MWG, p. 812). Total social indifference is a pairwise independent,
nondictatorial social welfare functional on `𝓡^I` that is not Paretian. -/
theorem exercise_21_C_2e [Nonempty ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    IsSWF (RationalProfiles ι X) totalIndifference ∧
      PairwiseIndependent (RationalProfiles ι X) totalIndifference ∧
      ¬Dictatorial (RationalProfiles ι X) totalIndifference ∧
      ¬Paretian (RationalProfiles ι X) totalIndifference := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hX
  refine ⟨fun _ _ => ⟨fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩,
    fun _ _ _ _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩, ?_, fun hP => ?_⟩
  · rintro ⟨h, hh⟩
    have := hh (fun _ => scorePref (rank3 a b c)) (fun _ => strictPrefs_subset (scorePref_mem _))
      a b (rank3_strict hab hac hbc).1
    exact this.2 trivial
  · have := hP (fun _ => scorePref (rank3 a b c)) (fun _ => strictPrefs_subset (scorePref_mem _))
      a b fun _ => (rank3_strict hab hac hbc).1
    exact this.2 trivial

/-- **Exercise 21.C.2(f)** (MWG, p. 812). A dictatorship satisfies (a)-(e): with three
alternatives and the universal domain it is a Paretian, pairwise independent social welfare
functional; only nondictatorship fails. -/
theorem exercise_21_C_2f :
    (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      IsSWF (RationalProfiles (Fin 2) (Fin 3)) (dictatorSWF 0) ∧
      Paretian (RationalProfiles (Fin 2) (Fin 3)) (dictatorSWF 0) ∧
      PairwiseIndependent (RationalProfiles (Fin 2) (Fin 3)) (dictatorSWF 0) ∧
      Dictatorial (RationalProfiles (Fin 2) (Fin 3)) (dictatorSWF 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := dictatorSWF_spec (Or.inl rfl : StandardDomain
    (RationalProfiles (Fin 2) (Fin 3))) (0 : Fin 2)
  exact ⟨⟨0, 1, 2, by decide, by decide, by decide⟩, h1, h2, h3, ⟨0, h4⟩⟩

/-- **Exercise 21.C.3** (MWG, p. 812). The lexical dictatorship with agents ordered
`0, 1, …, n - 1`: `x` is socially at least as good as `y` iff, for every `k`, if all agents
before `k` are indifferent between `x` and `y`, then `x ≿ₖ y`. -/
def lexRel {n : ℕ} (p : Profile (Fin n) X) (x y : X) : Prop :=
  ∀ k : Fin n, (∀ j < k, Indifferent (p j) x y) → p k x y

/-- **Exercise 21.C.3** (MWG, p. 812). The lexical dictatorship is a social welfare functional
on `𝓡^I`: the social relation is complete and transitive. -/
theorem exercise_21_C_3_rational {n : ℕ} : IsSWF (RationalProfiles (Fin n) X) lexRel := by
  intro p hp
  refine ⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    simp only [lexRel, not_forall] at h1
    obtain ⟨k, hk, hnk⟩ := h1
    refine h2 fun k' hk' => ?_
    rcases lt_trichotomy k' k with h | h | h
    · exact (hk k' h).2
    · subst h
      exact ((hp k').1 x y).resolve_left hnk
    · exact absurd (hk' k h).2 hnk
  · intro k hk
    have claim : ∀ m : ℕ, ∀ j : Fin n, j.val = m → j < k →
        Indifferent (p j) x y ∧ Indifferent (p j) y z := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro j hj hjk
        have prev : ∀ i < j, Indifferent (p i) x y ∧ Indifferent (p i) y z := fun i hi =>
          ih i.val (by rw [← hj]; exact hi) i rfl (lt_trans hi hjk)
        have hxyj : p j x y := hxy j fun i hi => (prev i hi).1
        have hyzj : p j y z := hyz j fun i hi => (prev i hi).2
        have hxz := hk j hjk
        have ht := (hp j).2
        exact ⟨⟨hxyj, ht y z x hyzj hxz.2⟩, ⟨hyzj, ht z x y hxz.2 hxyj⟩⟩
    have hxyk : p k x y := hxy k fun j hj => (claim j.val j rfl hj).1
    have hyzk : p k y z := hyz k fun j hj => (claim j.val j rfl hj).2
    exact (hp k).2 x y z hxyk hyzk

/-- **Exercise 21.C.3** (MWG, p. 812). The lexical dictatorship (with at least one agent) is
Paretian and pairwise independent on `𝓡^I`, and agent `0` is a dictator: all the hypotheses of
Arrow's theorem hold. -/
theorem exercise_21_C_3_arrow {n : ℕ} [NeZero n] :
    Paretian (RationalProfiles (Fin n) X) lexRel ∧
      PairwiseIndependent (RationalProfiles (Fin n) X) lexRel ∧
      IsDictator (RationalProfiles (Fin n) X) lexRel 0 := by
  refine ⟨fun p _ x y hall => ⟨fun k _ => (hall k).1, fun h => (hall 0).2 (h 0 fun j hj =>
    absurd hj (Fin.not_lt_zero j))⟩, fun p _ p' _ x y hag => ?_, fun p _ x y h0 => ?_⟩
  · have e : ∀ j, (Indifferent (p j) x y ↔ Indifferent (p' j) x y) ∧
        (Indifferent (p j) y x ↔ Indifferent (p' j) y x) := fun j => by
      refine ⟨?_, ?_⟩ <;> simp only [Indifferent, (hag j).1, (hag j).2]
    refine ⟨⟨fun h k hk => (hag k).1.1 (h k fun j hj => (e j).1.2 (hk j hj)),
      fun h k hk => (hag k).1.2 (h k fun j hj => (e j).1.1 (hk j hj))⟩,
      ⟨fun h k hk => (hag k).2.1 (h k fun j hj => (e j).2.2 (hk j hj)),
      fun h k hk => (hag k).2.2 (h k fun j hj => (e j).2.1 (hk j hj))⟩⟩
  · refine ⟨fun k hk => ?_, fun h => h0.2 (h 0 fun j hj => absurd hj (Fin.not_lt_zero j))⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact h0.1
    · exact absurd (hk 0 (Fin.pos_iff_ne_zero.2 hk0)).2 h0.2

/-- **Exercise 21.C.3** (MWG, p. 812). The social preference of the lexical dictatorship need
not be identical to the preference of any individual: with agent `0` having `0 ∼ 1 ≻ 2` and
agent `1` having `2 ≻ 1 ≻ 0`, the social preference is `1 ≻ 0 ≻ 2`. -/
theorem exercise_21_C_3_not_identical :
    let p : Profile (Fin 2) (Fin 3) := fun i => natPref (![![2, 2, 1], ![0, 1, 2]] i)
    ∀ h, lexRel p ≠ p h := by
  intro p h he
  have h10 : ¬lexRel p 0 1 := by
    intro hl
    have := hl 1 fun j hj => by
      have : j = 0 := by omega
      subst this
      simp [p, Indifferent, natPref]
    simp [p, natPref] at this
  have h02 : lexRel p 0 2 := by
    intro k _
    fin_cases k
    · simp [p, natPref]
    · simp [p, Indifferent, natPref] at *
  fin_cases h
  · exact h10 (by rw [he]; simp [p, natPref])
  · have := he ▸ h02
    simp [p, natPref] at this

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Social choice functions

MWG, Section 21.E, pp. 807-811: Definitions 21.E.1-21.E.6, Propositions 21.E.1 and 21.E.2 with
the seven-step proof, footnote 15, and Exercises 21.E.1-21.E.4 (pp. 815-816).

A social choice function on a domain `A` is a map `f : Profile ι X → X` (only its values on `A`
matter). We define weak Pareto optimality (21.E.2), maintaining one's position (21.E.3),
monotonicity (21.E.4), dictators (21.E.5) and taking a set to the top (21.E.6), and prove
Proposition 21.E.1 (with at least three alternatives, domain `𝓡^I` or `𝓟^I`, a weakly Paretian
monotonic social choice function is dictatorial) by the book's construction of a social welfare
functional `F` from `f` and Arrow's theorem, Steps 1-7. Profiles taking a set `X'` to the top are
built explicitly (`topProfile`), keeping the order outside `X'`. Proposition 21.E.2: a weakly
Paretian social choice function on `𝓟^I` with no incentive to misrepresent is monotonic, hence
dictatorial; the book's "without loss of generality" single-agent change is an induction over
the set of agents whose preferences change.

**Correction (Exercise 21.E.2).** On `𝓡^I` the "smallest label among agent 1's most preferred
alternatives" rule is dictatorial and weakly Paretian but *not* monotonic (with at least two
alternatives): `exercise_21_E_2_not_monotonic`. On `𝓟^I` it is monotonic, as is every
dictatorial social choice function (MWG, p. 808).
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- **Definition 21.E.2** (MWG, p. 808). `f` is weakly Paretian on `A`: if every agent strictly
prefers `x` to `y`, then `y` is not chosen. -/
def WeaklyParetian (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∀ p ∈ A, ∀ x y, (∀ i, Strict (p i) x y) → y ≠ f p

/-- **Definition 21.E.3** (MWG, p. 808). `x` maintains its position from `p` to `p'`:
`x ≿ᵢ y` implies `x ≿'ᵢ y` for every `i` and `y`. -/
def MaintainsPosition (x : X) (p p' : Profile ι X) : Prop := ∀ i y, p i x y → p' i x y

/-- **Footnote 15** (MWG, p. 808). The lower contour set `L(x, ≿) = {y : x ≿ y}`. -/
def lowerContour (r : X → X → Prop) (x : X) : Set X := {y | r x y}

/-- **Definition 21.E.3** (MWG, p. 808). `x` maintains its position iff every agent's lower
contour set at `x` weakly expands. -/
theorem maintainsPosition_iff (x : X) (p p' : Profile ι X) :
    MaintainsPosition x p p' ↔ ∀ i, lowerContour (p i) x ⊆ lowerContour (p' i) x :=
  ⟨fun h i _ hy => h i _ hy, fun h i _ hy => h i hy⟩

/-- **Definition 21.E.4** (MWG, p. 808). `f` is monotonic on `A`: if the chosen alternative
maintains its position from `p` to `p'` (both in `A`), it is still chosen at `p'`. -/
def Monotonic (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∀ p ∈ A, ∀ p' ∈ A, MaintainsPosition (f p) p p' → f p' = f p

/-- **Definition 21.E.5** (MWG, p. 808). `h` is a dictator for `f`: `f(p)` is a most preferred
alternative for `≿ₕ` at every profile of `A`. -/
def IsSCFDictator (A : Set (Profile ι X)) (f : Profile ι X → X) (h : ι) : Prop :=
  ∀ p ∈ A, ∀ y, p h (f p) y

/-- **Definition 21.E.5** (MWG, p. 808). `f` is dictatorial if it admits a dictator. -/
def DictatorialSCF (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∃ h, IsSCFDictator A f h

/-- **Section 21.E** (MWG, p. 807). With finitely many alternatives, every social welfare
functional `F` on `A` induces a social choice function choosing, at each profile of `A`, a most
preferred alternative for `F(p)`. -/
theorem induced_scf_exists [Finite X] [Nonempty X] {A : Set (Profile ι X)}
    {F : Profile ι X → X → X → Prop} (hF : IsSWF A F) :
    ∃ f : Profile ι X → X, ∀ p ∈ A, ∀ y, F p (f p) y := by
  classical
  have := Fintype.ofFinite X
  have hex : ∀ p, ∃ x, p ∈ A → ∀ y, F p x y := by
    intro p
    by_cases hp : p ∈ A
    · obtain ⟨x, -, hx⟩ := rational_acyclic (hF p hp) univ univ_nonempty
      exact ⟨x, fun _ y => hx y (mem_univ y)⟩
    · obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨x, fun h => absurd h hp⟩
  choose f hf using hex
  exact ⟨f, fun p hp => hf p hp⟩

/-- **Section 21.E** (MWG, p. 807). With an odd number of agents and the domain `𝓟_≥^I`, a
social choice function induced by pairwise majority voting chooses the Condorcet winner. -/
theorem induced_scf_condorcet [Fintype ι] [LinearOrder X] {f : Profile ι X → X}
    (hf : ∀ p ∈ StrictSinglePeakedProfiles ι X, ∀ y, majorityRel p (f p) y) :
    ∀ p ∈ StrictSinglePeakedProfiles ι X, IsCondorcetWinner p (f p) :=
  fun p hp => hf p hp

/-- **Definition 21.E.6** (MWG, p. 809). The profile `p'` takes `X'` to the top from `p`: every
alternative of `X'` is strictly preferred to every alternative outside `X'`, and the ranking
within `X'` is unchanged. -/
def TakesToTop (X' : Set X) (p p' : Profile ι X) : Prop :=
  ∀ i, (∀ x ∈ X', ∀ y ∉ X', Strict (p' i) x y) ∧ (∀ x ∈ X', ∀ y ∈ X', (p i x y ↔ p' i x y))

/-- The profile taking `X'` to the top from `p`, keeping each agent's ranking inside `X'` and
outside `X'`. -/
def topProfile (X' : Set X) (p : Profile ι X) : Profile ι X :=
  fun i a b => (a ∈ X' ∧ b ∈ X' ∧ p i a b) ∨ (a ∈ X' ∧ b ∉ X') ∨ (a ∉ X' ∧ b ∉ X' ∧ p i a b)

/-- `topProfile X' p` takes `X'` to the top from `p`, and stays in `𝓡` (resp. `𝓟`). -/
theorem topProfile_spec (X' : Set X) (p : Profile ι X) :
    TakesToTop X' p (topProfile X' p) ∧
      (∀ i, Rational (p i) → Rational (topProfile X' p i)) ∧
      (∀ i, p i ∈ StrictPrefs X → topProfile X' p i ∈ StrictPrefs X) := by
  have rat : ∀ i, Rational (p i) → Rational (topProfile X' p i) := by
    intro i hr
    refine ⟨fun a b => ?_, fun a b c hab hbc => ?_⟩
    · by_cases ha : a ∈ X' <;> by_cases hb : b ∈ X'
      · rcases hr.1 a b with h | h
        · exact Or.inl (Or.inl ⟨ha, hb, h⟩)
        · exact Or.inr (Or.inl ⟨hb, ha, h⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
      · rcases hr.1 a b with h | h
        · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, h⟩))
    · simp only [topProfile] at hab hbc ⊢
      rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
        rcases hbc with ⟨hb', hc, h2⟩ | ⟨hb', hc⟩ | ⟨hb', hc, h2⟩
      all_goals first
        | exact absurd hb' hb | exact absurd hb hb'
        | exact Or.inl ⟨ha, hc, hr.2 a b c h1 h2⟩
        | exact Or.inr (Or.inl ⟨ha, hc⟩)
        | exact Or.inr (Or.inr ⟨ha, hc, hr.2 a b c h1 h2⟩)
  refine ⟨fun i => ⟨fun x hx y hy => ⟨Or.inr (Or.inl ⟨hx, hy⟩), fun h => ?_⟩,
    fun x hx y hy => ?_⟩, rat, fun i hi => ⟨rat i hi.1, fun a b hab hba => ?_⟩⟩
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩
    · exact hy h1
    · exact hy h1
    · exact h1 hx
  · simp only [topProfile]
    constructor
    · exact fun h => Or.inl ⟨hx, hy, h⟩
    · rintro (⟨-, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd hy h
      · exact absurd hx h
  · simp only [topProfile] at hab hba
    rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
      rcases hba with ⟨hb', ha', h2⟩ | ⟨hb', ha'⟩ | ⟨hb', ha', h2⟩
    all_goals first
      | exact hi.2 a b h1 h2
      | (exfalso; tauto)

/-- **Section 21.E** (MWG, p. 809). If `p'` takes `X'` to the top from `p`, every `x ∈ X'`
maintains its position from `p` to `p'`. -/
theorem TakesToTop.maintains {X' : Set X} {p p' : Profile ι X} (h : TakesToTop X' p p') {x : X}
    (hx : x ∈ X') : MaintainsPosition x p p' := by
  intro i y hy
  by_cases hyX : y ∈ X'
  · exact ((h i).2 x hx y hyX).1 hy
  · exact ((h i).1 x hx y hyX).1

/-- Taking `Y` to the top and then `X' ⊆ Y` to the top takes `X'` to the top. -/
theorem TakesToTop.trans {X' Y : Set X} {p q r : Profile ι X} (hq : TakesToTop Y p q)
    (hr : TakesToTop X' q r) (hXY : X' ⊆ Y) : TakesToTop X' p r :=
  fun i => ⟨(hr i).1, fun x hx y hy => ((hq i).2 x (hXY hx) y (hXY hy)).trans ((hr i).2 x hx y hy)⟩

/-- **Section 21.E** (MWG, p. 809). The illustration of Definition 21.E.6: from
`x ≻ y ≻ z ≻ w`, the preference `y ≻' w ≻' z ≻' x` takes `{y, w}` to the top (alternatives
`x, y, z, w = 0, 1, 2, 3`, one agent). -/
theorem definition_21_E_6_example :
    TakesToTop ({1, 3} : Set (Fin 4)) (fun _ : Fin 1 => natPref ![4, 3, 2, 1])
      (fun _ => natPref ![1, 4, 2, 3]) := by
  intro _
  refine ⟨fun x hx y hy => (natPref_strict_iff _ _ _).2 ?_, fun x hx y hy => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    fin_cases x <;> fin_cases y <;> simp_all
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [natPref]

variable {A : Set (Profile ι X)} {f : Profile ι X → X}

/-- A weakly Paretian social choice function chooses inside `X'` at any profile of `A` that takes
the nonempty set `X'` to the top. -/
theorem WeaklyParetian.mem_top (hW : WeaklyParetian A f) {X' : Set X} (hne : X'.Nonempty)
    {p p' : Profile ι X} (hp' : p' ∈ A) (h : TakesToTop X' p p') : f p' ∈ X' := by
  by_contra hn
  obtain ⟨x, hx⟩ := hne
  exact hW p' hp' x (f p') (fun i => (h i).1 x hx _ hn) rfl

/-- **Step 1** of the proof of Proposition 21.E.1 (MWG, p. 809). If two profiles of `A` take
the nonempty set `X'` to the top from `p`, then `f` chooses the same alternative at both. -/
theorem scf_step_1 (hW : WeaklyParetian A f) (hM : Monotonic A f) {X' : Set X}
    (hne : X'.Nonempty) {p p' p'' : Profile ι X} (hp' : p' ∈ A) (hp'' : p'' ∈ A)
    (h' : TakesToTop X' p p') (h'' : TakesToTop X' p p'') : f p' = f p'' := by
  have hx := hW.mem_top hne hp' h'
  refine (hM p' hp' p'' hp'' fun i y hy => ?_).symm
  by_cases hyX : y ∈ X'
  · exact ((h'' i).2 _ hx y hyX).1 (((h' i).2 _ hx y hyX).2 hy)
  · exact ((h'' i).1 _ hx y hyX).1

/-- **Step 2** of the proof of Proposition 21.E.1 (MWG, p. 809). The social relation built
from `f`: `x` is socially at least as good as `y` iff `x = y` or `x` is chosen at the profile
taking `{x, y}` to the top. (By Step 1 any such profile may be used: `scf_step_2`.) -/
def scfRelation (f : Profile ι X → X) (p : Profile ι X) (x y : X) : Prop :=
  x = y ∨ x = f (topProfile {x, y} p)

/-- **Step 2** of the proof of Proposition 21.E.1 (MWG, p. 809). `scfRelation` is well defined:
any profile of `A` taking `{x, y}` to the top from `p` gives the same choice. -/
theorem scf_step_2 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p p' : Profile ι X} (hp : p ∈ A) (hp' : p' ∈ A) {x y : X}
    (h' : TakesToTop {x, y} p p') : f p' = f (topProfile {x, y} p) := by
  have htop := topProfile_spec ({x, y} : Set X) p
  have hmem : topProfile {x, y} p ∈ A := by
    rcases hA with rfl | rfl
    · exact fun i => htop.2.1 i (hp i)
    · exact fun i => htop.2.2 i (hp i)
  exact scf_step_1 hW hM ⟨x, Or.inl rfl⟩ hp' hmem h' htop.1

/-- Profiles taking a set to the top stay in a standard domain. -/
theorem StandardDomain.topProfile_mem (hA : StandardDomain A) {p : Profile ι X} (hp : p ∈ A)
    (X' : Set X) : topProfile X' p ∈ A := by
  have htop := topProfile_spec X' p
  rcases hA with rfl | rfl
  · exact fun i => htop.2.1 i (hp i)
  · exact fun i => htop.2.2 i (hp i)

/-- The alternative chosen at the profile taking `{x, y}` to the top is `x` or `y`. -/
theorem scf_choice_pair (hA : StandardDomain A) (hW : WeaklyParetian A f) {p : Profile ι X}
    (hp : p ∈ A) (x y : X) : f (topProfile {x, y} p) = x ∨ f (topProfile {x, y} p) = y :=
  hW.mem_top (X' := {x, y}) ⟨x, Or.inl rfl⟩ (hA.topProfile_mem hp _) (topProfile_spec _ p).1

/-- Part of **Step 3** of the proof of Proposition 21.E.1 (MWG, p. 810): if `x` is socially at
least as good as `y` and `x ≠ y`, then `y` is not chosen at a profile `p''` taking a superset
`Y ⊇ {x, y}` to the top. -/
theorem scf_not_chosen (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) {x y : X} (hxy : x ≠ y) (h : scfRelation f p x y)
    {Y : Set X} (hY : ({x, y} : Set X) ⊆ Y) {p'' : Profile ι X} (hp'' : p'' ∈ A)
    (h'' : TakesToTop Y p p'') : y ≠ f p'' := by
  intro hy
  have hfx : f (topProfile {x, y} p) = x := (h.resolve_left hxy).symm
  have htop := topProfile_spec ({x, y} : Set X) p''
  have hp' := hA.topProfile_mem hp'' ({x, y} : Set X)
  have h1 : f (topProfile {x, y} p'') = y := by
    rw [hM p'' hp'' _ hp' (hy ▸ htop.1.maintains (Or.inr rfl))]
    exact hy.symm
  have h2 : TakesToTop {x, y} p (topProfile {x, y} p'') := h''.trans htop.1 hY
  rw [scf_step_2 hA hW hM hp hp' h2, hfx] at h1
  exact hxy h1

/-- **Step 3** of the proof of Proposition 21.E.1 (MWG, pp. 809-810). For every profile of `A`,
the social relation is complete and transitive and no two distinct alternatives are socially
indifferent: it lies in `𝓟`. -/
theorem scf_step_3 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) : scfRelation f p ∈ StrictPrefs X := by
  have hnoind : NoIndifference (scfRelation f p) := by
    intro x y hxy hyx
    by_contra hne
    have h1 : f (topProfile {x, y} p) = x := (hxy.resolve_left hne).symm
    have h2 : f (topProfile {y, x} p) = y := (hyx.resolve_left (Ne.symm hne)).symm
    rw [Set.pair_comm, h1] at h2
    exact hne h2
  refine ⟨⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩, hnoind⟩
  · rcases scf_choice_pair hA hW hp x y with h | h
    · exact Or.inl (Or.inr h.symm)
    · refine Or.inr (Or.inr ?_)
      rw [Set.pair_comm]
      exact h.symm
  · by_cases e1 : x = y
    · subst e1
      exact hyz
    by_cases e2 : y = z
    · subst e2
      exact hxy
    by_cases e3 : x = z
    · exact Or.inl e3
    set p'' := topProfile ({x, y, z} : Set X) p with hp''
    have hp''A : p'' ∈ A := hA.topProfile_mem hp _
    have h'' : TakesToTop {x, y, z} p p'' := (topProfile_spec _ p).1
    have hmem : f p'' ∈ ({x, y, z} : Set X) := hW.mem_top ⟨x, Or.inl rfl⟩ hp''A h''
    have hny : y ≠ f p'' := scf_not_chosen hA hW hM hp e1 hxy
      (by intro a ha; rcases ha with rfl | rfl <;> simp) hp''A h''
    have hnz : z ≠ f p'' := scf_not_chosen hA hW hM hp e2 hyz
      (by intro a ha; rcases ha with rfl | rfl <;> simp) hp''A h''
    have hfx : f p'' = x := by
      rcases hmem with h | h | h
      · exact h
      · exact absurd h.symm hny
      · exact absurd (Set.mem_singleton_iff.1 h).symm hnz
    refine Or.inr ?_
    have htop := topProfile_spec ({x, z} : Set X) p''
    have hp' := hA.topProfile_mem hp''A ({x, z} : Set X)
    have hsub : ({x, z} : Set X) ⊆ {x, y, z} := by
      intro a ha
      rcases ha with rfl | rfl <;> simp
    have h1 : f (topProfile {x, z} p'') = x := by
      rw [hM p'' hp''A _ hp' (hfx ▸ htop.1.maintains (Or.inl rfl))]
      exact hfx
    have h2 := scf_step_2 hA hW hM hp hp' (h''.trans htop.1 hsub)
    rw [← h2, h1]

/-- **Exercise 21.E.3** (MWG, p. 816). The case of the pair `{y, z}` in Step 3: if
`y F(≿) z` with `y ≠ z`, then `z` is not chosen at the profile taking `{x, y, z}` to the top. -/
theorem exercise_21_E_3 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) {x y z : X} (hyz : y ≠ z) (h : scfRelation f p y z) :
    z ≠ f (topProfile {x, y, z} p) :=
  scf_not_chosen hA hW hM hp hyz h (by intro a ha; rcases ha with rfl | rfl <;> simp)
    (hA.topProfile_mem hp _) (topProfile_spec _ p).1

/-- **Step 4** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation
rationalizes `f`: `f(p)` is a most preferred alternative for it. -/
theorem scf_step_4 (hA : StandardDomain A) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) (y : X) : scfRelation f p (f p) y := by
  by_cases hy : f p = y
  · exact Or.inl hy
  refine Or.inr ?_
  have htop := topProfile_spec ({f p, y} : Set X) p
  exact (hM p hp _ (hA.topProfile_mem hp _) (htop.1.maintains (Or.inl rfl))).symm

/-- **Step 5** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation is
Paretian. -/
theorem scf_step_5 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    Paretian A (scfRelation f) := by
  intro p hp x y hall
  by_cases hxy : x = y
  · subst hxy
    have hι : IsEmpty ι := ⟨fun i => (hall i).2 (hall i).1⟩
    exact absurd rfl (hW p hp x (f p) fun i => hι.elim i)
  have htop := topProfile_spec ({x, y} : Set X) p
  have hmemA := hA.topProfile_mem hp ({x, y} : Set X)
  have hstrict : ∀ i, Strict (topProfile {x, y} p i) x y := fun i =>
    ⟨((htop.1 i).2 x (Or.inl rfl) y (Or.inr rfl)).1 (hall i).1,
      fun h => (hall i).2 (((htop.1 i).2 y (Or.inr rfl) x (Or.inl rfl)).2 h)⟩
  have hfx : f (topProfile {x, y} p) = x :=
    (scf_choice_pair hA hW hp x y).resolve_right fun h => hW _ hmemA x y hstrict h.symm
  have hrel : scfRelation f p x y := Or.inr hfx.symm
  exact ⟨hrel, fun h => hxy ((scf_step_3 hA hW hM hp).2 x y hrel h)⟩

/-- **Step 6** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation satisfies
the pairwise independence condition. -/
theorem scf_step_6 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    PairwiseIndependent A (scfRelation f) := by
  intro p hp p' hp' x y hag
  have hrefl : ∀ i a, p i a a ∧ p' i a a := fun i a =>
    ⟨complete_refl (hA.rational hp i).1 a, complete_refl (hA.rational hp' i).1 a⟩
  have htop := topProfile_spec ({x, y} : Set X) p
  have hT : TakesToTop {x, y} p' (topProfile {x, y} p) := by
    intro i
    refine ⟨(htop.1 i).1, fun a ha b hb => ?_⟩
    refine Iff.trans ?_ ((htop.1 i).2 a ha b hb)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact iff_of_true (hrefl i _).2 (hrefl i _).1
    · exact (hag i).1.symm
    · exact (hag i).2.symm
    · exact iff_of_true (hrefl i _).2 (hrefl i _).1
  have heq : f (topProfile {x, y} p) = f (topProfile {x, y} p') :=
    scf_step_2 hA hW hM hp' (hA.topProfile_mem hp _) hT
  have heq' : f (topProfile {y, x} p) = f (topProfile {y, x} p') := by
    rw [Set.pair_comm, heq]
  simp only [scfRelation, heq, heq', and_self]

/-- **Step 7** of the proof of Proposition 21.E.1 (MWG, pp. 810-811), and **Proposition 21.E.1**
(MWG, p. 809). With finitely many agents, at least three alternatives and domain `𝓡^I` or
`𝓟^I`, every weakly Paretian and monotonic social choice function is dictatorial. -/
theorem proposition_21_E_1 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    DictatorialSCF A f := by
  have hF : IsSWF A (scfRelation f) := fun p hp => (scf_step_3 hA hW hM hp).1
  obtain ⟨h, hh⟩ := proposition_21_C_1 hX hA hF (scf_step_5 hA hW hM) (scf_step_6 hA hW hM)
  refine ⟨h, fun p hp y => ?_⟩
  by_contra hn
  have hs : Strict (p h) y (f p) := ⟨((hA.rational hp h).1 _ _).resolve_left hn, hn⟩
  exact (hh p hp y (f p) hs).2 (scf_step_4 hA hM hp y)

/-- **Proposition 21.E.1**, non-vacuity (MWG, p. 809). On `𝓟^I` the dictatorial social choice
function "agent `h`'s most preferred alternative" is weakly Paretian and monotonic (MWG,
p. 808; Exercise 21.E.2, second part): the hypotheses have instances and the conclusion is
attained. -/
theorem dictatorial_strict_spec {f : Profile ι X → X} {h : ι}
    (hf : IsSCFDictator (StrictProfiles ι X) f h) :
    WeaklyParetian (StrictProfiles ι X) f ∧ Monotonic (StrictProfiles ι X) f := by
  refine ⟨fun p hp x y hall hy => (hall h).2 (hy ▸ hf p hp x), fun p hp p' hp' hmain => ?_⟩
  by_contra hne
  have h1 : p' h (f p) (f p') := hmain h _ (hf p hp _)
  exact hne ((hp' h).2 _ _ (hf p' hp' _) h1)

/-- The agent-`h` choice from a nonempty finite set of alternatives: the alternative with
smallest label among `h`'s most preferred ones (Exercise 21.E.2), with `0` as a default. -/
noncomputable def smallestTopLabel {N : ℕ} [NeZero N] (h : ι) (p : Profile ι (Fin N)) :
    Fin N :=
  by classical exact
    if hne : (univ.filter fun x => ∀ y, p h x y).Nonempty then
      (univ.filter fun x => ∀ y, p h x y).min' hne else 0

/-- The smallest-label rule chooses one of agent `h`'s most preferred alternatives. -/
theorem smallestTopLabel_spec {N : ℕ} [NeZero N] (h : ι) {p : Profile ι (Fin N)}
    (hp : Rational (p h)) :
    (∀ y, p h (smallestTopLabel h p) y) ∧
      ∀ x, (∀ y, p h x y) → smallestTopLabel h p ≤ x := by
  classical
  obtain ⟨m, -, hm⟩ := rational_acyclic hp univ univ_nonempty
  have hne : (univ.filter fun x => ∀ y, p h x y).Nonempty :=
    ⟨m, by simpa using fun y => hm y (mem_univ y)⟩
  have e : smallestTopLabel h p = (univ.filter fun x => ∀ y, p h x y).min' hne := by
    unfold smallestTopLabel
    simp only [hne, ↓reduceDIte]
  rw [e]
  refine ⟨fun y => ?_, fun x hx => min'_le _ _ (by simpa using hx)⟩
  have := min'_mem _ hne
  simp only [mem_filter, mem_univ, true_and] at this
  exact this y

/-- **Exercise 21.E.2** (MWG, p. 816), first part. On `𝓡^I`, the smallest-label rule of agent
`h` is dictatorial and weakly Paretian. -/
theorem exercise_21_E_2_dictatorial {N : ℕ} [NeZero N] (h : ι) :
    IsSCFDictator (RationalProfiles ι (Fin N)) (smallestTopLabel h) h ∧
      WeaklyParetian (RationalProfiles ι (Fin N)) (smallestTopLabel h) := by
  refine ⟨fun p hp y => (smallestTopLabel_spec h (hp h)).1 y, fun p hp x y hall hy => ?_⟩
  exact (hall h).2 (hy ▸ (smallestTopLabel_spec h (hp h)).1 x)

/-- **Exercise 21.E.2** (MWG, p. 816), correction. On `𝓡^I` the smallest-label rule is not
monotonic as soon as there are two alternatives: if agent `h` has `1 ≻ 0` the rule picks `1`;
if `h` becomes indifferent between `0` and `1` (so that `1` maintains its position), it picks
`0`. -/
theorem exercise_21_E_2_not_monotonic {N : ℕ} [NeZero N] (hN : 2 ≤ N) (h : ι) :
    ¬Monotonic (RationalProfiles ι (Fin N)) (smallestTopLabel h) := by
  classical
  intro hM
  let one : Fin N := ⟨1, by omega⟩
  let u : Fin N → ℕ := fun x => if x = one then 2 else if x = 0 then 1 else 0
  let u' : Fin N → ℕ := fun x => if x = one ∨ x = 0 then 2 else 0
  have h10 : one ≠ 0 := by
    intro e
    have := congrArg Fin.val e
    simp [one] at this
  let p : Profile ι (Fin N) := fun _ => natPref u
  let p' : Profile ι (Fin N) := fun _ => natPref u'
  have hp : p ∈ RationalProfiles ι (Fin N) := fun _ => natPref_rational _
  have hp' : p' ∈ RationalProfiles ι (Fin N) := fun _ => natPref_rational _
  have hfp : smallestTopLabel h p = one := by
    have hs := (smallestTopLabel_spec h (hp h)).1 one
    change u one ≤ u (smallestTopLabel h p) at hs
    have hu1 : u one = 2 := by simp [u]
    by_contra hne
    have : u (smallestTopLabel h p) ≤ 1 := by
      simp only [u]
      split_ifs <;> simp_all
    omega
  have hfp' : smallestTopLabel h p' = 0 := by
    have hs := smallestTopLabel_spec h (hp' h)
    have h0 : ∀ y, p' h 0 y := fun y => by
      simp only [p', natPref, u']
      split_ifs <;> simp_all
    exact le_antisymm (hs.2 0 h0) (Fin.zero_le _)
  have hmain : MaintainsPosition (smallestTopLabel h p) p p' := by
    rw [hfp]
    intro i y _
    simp only [p', natPref, u']
    split_ifs <;> simp_all
  have := hM p hp p' hp' hmain
  rw [hfp, hfp'] at this
  exact h10 this.symm

/-- **Exercise 21.E.2** (MWG, p. 816), the domain `𝓟^I`. There the smallest-label rule is
dictatorial, weakly Paretian and monotonic. -/
theorem exercise_21_E_2_strict {N : ℕ} [NeZero N] (h : ι) :
    IsSCFDictator (StrictProfiles ι (Fin N)) (smallestTopLabel h) h ∧
      WeaklyParetian (StrictProfiles ι (Fin N)) (smallestTopLabel h) ∧
      Monotonic (StrictProfiles ι (Fin N)) (smallestTopLabel h) := by
  have hd : IsSCFDictator (StrictProfiles ι (Fin N)) (smallestTopLabel h) h :=
    fun p hp y => (smallestTopLabel_spec h (hp h).1).1 y
  exact ⟨hd, dictatorial_strict_spec hd⟩

/-- **Proposition 21.E.2** (MWG, p. 811). The no-incentive-to-misrepresent condition on `𝓟^I`:
no agent `h` with true preference `≿ₕ` gains by reporting any `≿'ₕ ∈ 𝓟` instead. -/
def NoIncentiveToMisrepresent [DecidableEq ι] (f : Profile ι X → X) : Prop :=
  ∀ p ∈ StrictProfiles ι X, ∀ h, ∀ r ∈ StrictPrefs X, p h (f p) (f (Function.update p h r))

/-- The single-agent step of the proof of Proposition 21.E.2 (MWG, p. 811): if the chosen
alternative maintains its position when agent `a` alone changes preferences, the choice does
not change. -/
theorem no_incentive_step [DecidableEq ι] {f : Profile ι X → X}
    (hf : NoIncentiveToMisrepresent f) {q : Profile ι X} (hq : q ∈ StrictProfiles ι X) {a : ι}
    {r : X → X → Prop} (hr : r ∈ StrictPrefs X)
    (hmain : MaintainsPosition (f q) q (Function.update q a r)) :
    f (Function.update q a r) = f q := by
  have hq' : Function.update q a r ∈ StrictProfiles ι X := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa using hr
    · simpa [Function.update_of_ne hi] using hq i
  by_contra hne
  by_cases hyx : Strict (q a) (f (Function.update q a r)) (f q)
  · exact hyx.2 (hf q hq a r hr)
  · have hxy : q a (f q) (f (Function.update q a r)) := weak_of_not_strict (hq a).1.1 hyx
    have h1 : r (f q) (f (Function.update q a r)) := by
      simpa using hmain a _ hxy
    have h2 := hf _ hq' a (q a) (hq a)
    rw [Function.update_idem, Function.update_eq_self] at h2
    simp only [Function.update_self] at h2
    exact hne ((hr.2 _ _ h2 h1))

/-- **Proposition 21.E.2** (MWG, p. 811), main step. A social choice function on `𝓟^I` with no
incentive to misrepresent is monotonic (agents' preferences are changed one at a time). -/
theorem monotonic_of_noIncentive [Finite ι] [DecidableEq ι] {f : Profile ι X → X}
    (hf : NoIncentiveToMisrepresent f) : Monotonic (StrictProfiles ι X) f := by
  have := Fintype.ofFinite ι
  intro p hp p' hp' hmain
  let q : Finset ι → Profile ι X := fun S i => if i ∈ S then p' i else p i
  have hqmem : ∀ S, q S ∈ StrictProfiles ι X := fun S i => by
    by_cases hi : i ∈ S
    · simpa [q, hi] using hp' i
    · simpa [q, hi] using hp i
  have key : ∀ S, f (q S) = f p := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert a S haS ih =>
      have hupd : q (insert a S) = Function.update (q S) a (p' a) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [q]
        · simp [q, hi]
      rw [hupd]
      rw [← ih]
      refine no_incentive_step hf (hqmem S) (hp' a) fun i y hy => ?_
      rw [ih] at hy ⊢
      by_cases hi : i = a
      · subst hi
        simp only [Function.update_self]
        have : q S i = p i := by simp [q, haS]
        rw [this] at hy
        exact hmain i y hy
      · rwa [Function.update_of_ne hi]
  have huniv : q univ = p' := by
    funext i
    simp [q]
  rw [← huniv]
  exact key univ

/-- **Proposition 21.E.2** (MWG, p. 811). With finitely many agents and at least three
alternatives, a weakly Paretian social choice function on `𝓟^I` satisfying the
no-incentive-to-misrepresent condition is dictatorial. -/
theorem proposition_21_E_2 [Finite ι] [DecidableEq ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {f : Profile ι X → X} (hW : WeaklyParetian (StrictProfiles ι X) f)
    (hf : NoIncentiveToMisrepresent f) : DictatorialSCF (StrictProfiles ι X) f :=
  proposition_21_E_1 hX (Or.inr rfl) hW (monotonic_of_noIncentive hf)

/-- **Proposition 21.E.2**, non-vacuity (MWG, p. 811). The dictatorial smallest-label rule of
agent `h` is weakly Paretian on `𝓟^I` and gives no agent an incentive to misrepresent. -/
theorem smallestTopLabel_noIncentive [DecidableEq ι] {N : ℕ} [NeZero N] (h : ι) :
    WeaklyParetian (StrictProfiles ι (Fin N)) (smallestTopLabel h) ∧
      NoIncentiveToMisrepresent (X := Fin N) (smallestTopLabel h) := by
  refine ⟨(exercise_21_E_2_strict h).2.1, fun p hp k r _ => ?_⟩
  by_cases hk : k = h
  · subst hk
    exact (smallestTopLabel_spec k (hp k).1).1 _
  · have : smallestTopLabel h (Function.update p k r) = smallestTopLabel h p := by
      unfold smallestTopLabel
      rw [Function.update_of_ne (Ne.symm hk)]
    rw [this]
    exact complete_refl (hp k).1.1 _

/-- With an odd number of agents and preferences in `𝓟`, a Condorcet winner is unique. -/
theorem condorcetWinner_unique [Fintype ι] {p : Profile ι X} (hp : p ∈ StrictProfiles ι X)
    (hodd : Odd (Fintype.card ι)) {x y : X} (hx : IsCondorcetWinner p x)
    (hy : IsCondorcetWinner p y) : x = y := by
  classical
  by_contra hne
  have h1 := hx y
  have h2 := hy x
  rw [majorityRel_iff] at h1 h2
  exact strict_majority_odd hp hodd hne (by omega)

/-- The Condorcet-winner social choice function (Exercise 21.E.1): a Condorcet winner when one
exists. -/
noncomputable def condorcetSCF [Fintype ι] [Nonempty X] (p : Profile ι X) : X :=
  Classical.epsilon (IsCondorcetWinner p)

/-- **Exercise 21.E.1** (MWG, p. 815). With an odd number of agents and the domain `𝓟_≥^I`, the
social choice function assigning the Condorcet winner to every profile is weakly Paretian and
monotonic. (Finiteness of `X` is not needed.) -/
theorem exercise_21_E_1 [Fintype ι] [LinearOrder X] [Nonempty X]
    (hodd : Odd (Fintype.card ι)) :
    WeaklyParetian (StrictSinglePeakedProfiles ι X) condorcetSCF ∧
      Monotonic (StrictSinglePeakedProfiles ι X) condorcetSCF := by
  classical
  have hcw : ∀ p ∈ StrictSinglePeakedProfiles ι X, IsCondorcetWinner p (condorcetSCF p) :=
    fun p hp => Classical.epsilon_spec
      (proposition_21_D_1_exists (strictSinglePeaked_subset hp))
  refine ⟨fun p hp x y hall hy => ?_, fun p hp p' hp' hmain => ?_⟩
  · have h1 := hcw p hp x
    rw [← hy, majorityRel_iff] at h1
    have e1 : (univ.filter fun i => Strict (p i) x y) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact hall i
    have e2 : (univ.filter fun i => Strict (p i) y x) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact strict_asymm (hall i)
    rw [e1, e2, card_empty, card_univ] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  · set x := condorcetSCF p
    have hsp := strictSinglePeaked_subset_strict hp'
    have hcw' : IsCondorcetWinner p' x := by
      intro y
      by_cases hxy : x = y
      · subst hxy
        rw [majorityRel_iff]
      have h1 : majorityRel p x y := hcw p hp y
      rw [majorityRel_iff] at h1 ⊢
      have s1 : (univ.filter fun i => Strict (p i) x y) ⊆
          univ.filter fun i => Strict (p' i) x y := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨mem_univ i, hmain i y hi.2.1, fun h => hxy ((hsp i).2 x y (hmain i y hi.2.1) h)⟩
      have s2 : (univ.filter fun i => Strict (p' i) y x) ⊆
          univ.filter fun i => Strict (p i) y x := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨mem_univ i, ((hp i).1.1.1 y x).resolve_right fun h => hi.2.2 (hmain i y h),
          fun h => hi.2.2 (hmain i y h)⟩
      have := card_le_card s1
      have := card_le_card s2
      omega
    exact condorcetWinner_unique hsp hodd (hcw p' hp') hcw'

/-- The parity rule over two alternatives `0, 1` (Exercise 21.E.4): `0` is socially preferred
iff an odd number of agents prefer `0` to `1`. -/
noncomputable def parityRule [Fintype ι] (p : Profile ι (Fin 2)) (a b : Fin 2) : Prop :=
  by classical exact
    a = b ∨ (a = 0 ∧ b = 1 ∧ Odd (univ.filter fun i => Strict (p i) 0 1).card) ∨
      (a = 1 ∧ b = 0 ∧ ¬Odd (univ.filter fun i => Strict (p i) 0 1).card)

/-- **Exercise 21.E.4**, two alternatives (MWG, p. 816). With three agents and `𝓐 = 𝓟^I`, the
parity rule is a Paretian, pairwise independent social welfare functional `𝓐 → 𝓟`, and no
social choice function selecting its most preferred alternative is monotonic. -/
theorem exercise_21_E_4_two :
    (∀ p ∈ StrictProfiles (Fin 3) (Fin 2), parityRule p ∈ StrictPrefs (Fin 2)) ∧
      Paretian (StrictProfiles (Fin 3) (Fin 2)) parityRule ∧
      PairwiseIndependent (StrictProfiles (Fin 3) (Fin 2)) parityRule ∧
      ∀ f : Profile (Fin 3) (Fin 2) → Fin 2,
        (∀ p ∈ StrictProfiles (Fin 3) (Fin 2), ∀ y, parityRule p (f p) y) →
          ¬Monotonic (StrictProfiles (Fin 3) (Fin 2)) f := by
  classical
  have hP : ∀ p : Profile (Fin 3) (Fin 2), parityRule p ∈ StrictPrefs (Fin 2) := by
    intro p
    unfold parityRule
    by_cases ho : Odd (univ.filter fun i => Strict (p i) 0 1).card
    · refine ⟨⟨fun a b => ?_, fun a b c => ?_⟩, fun a b => ?_⟩ <;> simp only [ho] <;>
        fin_cases a <;> fin_cases b <;> (try fin_cases c) <;> simp
    · refine ⟨⟨fun a b => ?_, fun a b c => ?_⟩, fun a b => ?_⟩ <;> simp only [ho] <;>
        fin_cases a <;> fin_cases b <;> (try fin_cases c) <;> simp
  have hcount : ∀ p p' : Profile (Fin 3) (Fin 2),
      (univ.filter fun i => Strict (p i) 0 1) = (univ.filter fun i => Strict (p' i) 0 1) →
        parityRule p = parityRule p' := by
    intro p p' h
    unfold parityRule
    rw [h]
  refine ⟨fun p _ => hP p, fun p _ a b hall => ?_, fun p _ p' _ x y hag => ?_, fun f hf hM => ?_⟩
  · have hab : a ≠ b := fun e => (hall 0).2 (e ▸ (hall 0).1)
    have hP' := hP p
    have hrel : parityRule p a b := by
      unfold parityRule
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · have e : (univ.filter fun i => Strict (p i) 0 1) = univ := by
          ext i
          rw [mem_filter]
          simpa using hall i
        rw [e]
        right; left
        exact ⟨rfl, rfl, by decide⟩
      · have e : (univ.filter fun i => Strict (p i) 0 1) = ∅ := by
          ext i
          rw [mem_filter]
          simpa using strict_asymm (hall i)
        rw [e]
        right; right
        exact ⟨rfl, rfl, by decide⟩
      · exact absurd rfl hab
    exact ⟨hrel, fun h => hab (hP'.2 a b hrel h)⟩
  · by_cases hxy : x = y
    · subst hxy
      have h1 : parityRule p x x := by unfold parityRule; exact Or.inl rfl
      have h2 : parityRule p' x x := by unfold parityRule; exact Or.inl rfl
      exact ⟨iff_of_true h1 h2, iff_of_true h1 h2⟩
    have hxy' : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by omega
    have h01 : ∀ i, (p i 0 1 ↔ p' i 0 1) ∧ (p i 1 0 ↔ p' i 1 0) := by
      rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hag
      · exact fun i => ⟨(hag i).2, (hag i).1⟩
    have e : (univ.filter fun i => Strict (p i) 0 1) = univ.filter fun i => Strict (p' i) 0 1 := by
      ext i
      rw [mem_filter, mem_filter]
      simp only [Strict, (h01 i).1, (h01 i).2]
    rw [hcount p p' e]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · let u : Fin 2 → ℕ := ![1, 0]
    let v : Fin 2 → ℕ := ![0, 1]
    let p : Profile (Fin 3) (Fin 2) := fun i => natPref (if i = 0 then u else v)
    let p' : Profile (Fin 3) (Fin 2) := fun i => natPref (if i = 2 then v else u)
    have hp : p ∈ StrictProfiles (Fin 3) (Fin 2) := fun i => by
      by_cases hi : i = 0
      · simp only [p, hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
      · simp only [p, hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
    have hp' : p' ∈ StrictProfiles (Fin 3) (Fin 2) := fun i => by
      by_cases hi : i = 2
      · simp only [p', hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
      · simp only [p', hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
    have c1 : (univ.filter fun i => Strict (p i) 0 1) = {0} := by
      ext i
      rw [mem_filter]
      fin_cases i <;> simp [p, u, v, natPref_strict_iff]
    have c2 : (univ.filter fun i => Strict (p' i) 0 1) = {0, 1} := by
      ext i
      rw [mem_filter]
      fin_cases i <;> simp [p', u, v, natPref_strict_iff]
    have hfp : f p = 0 := by
      have h := hf p hp 0
      by_contra hne
      have h1 : f p = 1 := by omega
      rw [h1] at h
      unfold parityRule at h
      rw [c1] at h
      simp at h
    have hfp' : f p' = 1 := by
      have h := hf p' hp' 1
      by_contra hne
      have h0 : f p' = 0 := by omega
      rw [h0] at h
      unfold parityRule at h
      rw [c2] at h
      rcases h with h | ⟨-, -, h⟩ | ⟨h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hmain : MaintainsPosition (f p) p p' := by
      rw [hfp]
      intro i y hy
      fin_cases i <;> fin_cases y <;> simp_all [p, p', u, v, natPref]
    have := hM p hp p' hp' hmain
    rw [hfp, hfp'] at this
    exact absurd this (by decide)

/-- The domain `𝓐 = {pA, pB}` of Exercise 21.E.4 with three agents and alternatives
`x, y, z = 0, 1, 2`: `pA` has `y ≻ x ≻ z` (agents 1, 2) and `x ≻ y ≻ z` (agent 3); `pB` has
`y ≻ x ≻ z` (agent 1) and `x ≻ y ≻ z` (agents 2, 3). -/
def e214A : Fin 3 → Fin 3 → ℕ := ![![1, 2, 0], ![1, 2, 0], ![2, 1, 0]]

/-- See `e214A`. -/
def e214B : Fin 3 → Fin 3 → ℕ := ![![1, 2, 0], ![2, 1, 0], ![2, 1, 0]]

/-- The social welfare functional of Exercise 21.E.4 on `{pA, pB}`: `x ≻ y ≻ z` at `pA`,
`y ≻ x ≻ z` at `pB` (and `x ≻ y ≻ z` elsewhere). -/
noncomputable def e214F (p : Profile (Fin 3) (Fin 3)) : Fin 3 → Fin 3 → Prop :=
  by classical exact
    if p = (fun i => natPref (e214B i)) then natPref ![1, 2, 0] else natPref ![2, 1, 0]

/-- **Exercise 21.E.4**, more than two alternatives (MWG, p. 816). On the two-profile domain
`{pA, pB} ⊆ 𝓟^I`, `e214F` is a Paretian, pairwise independent social welfare functional with
values in `𝓟`, but the induced social choice function (choose the social top) is not
monotonic: it picks `x` at `pA`, `x` maintains its position from `pA` to `pB`, and `y` is
picked at `pB`. -/
theorem exercise_21_E_4_three :
    let A : Set (Profile (Fin 3) (Fin 3)) :=
      {fun i => natPref (e214A i), fun i => natPref (e214B i)}
    A ⊆ StrictProfiles (Fin 3) (Fin 3) ∧ (∀ p ∈ A, e214F p ∈ StrictPrefs (Fin 3)) ∧
      Paretian A e214F ∧ PairwiseIndependent A e214F ∧
      ∀ f : Profile (Fin 3) (Fin 3) → Fin 3, (∀ p ∈ A, ∀ y, e214F p (f p) y) →
        ¬Monotonic A f := by
  intro A
  classical
  have hne : (fun i => natPref (e214A i)) ≠ (fun i => natPref (e214B i)) := by
    intro h
    have := congrFun (congrFun (congrFun h 1) 0) 1
    simp [natPref, e214A, e214B] at this
  have FA : e214F (fun i => natPref (e214A i)) = natPref ![2, 1, 0] := by
    unfold e214F
    simp [hne]
  have FB : e214F (fun i => natPref (e214B i)) = natPref ![1, 2, 0] := by
    unfold e214F
    simp
  have hmemA : ∀ p ∈ A, p = (fun i => natPref (e214A i)) ∨ p = (fun i => natPref (e214B i)) :=
    fun p hp => hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp i
    rcases hmemA p hp with rfl | rfl <;> exact natPref_mem_strict (by fin_cases i <;> decide)
  · intro p hp
    rcases hmemA p hp with rfl | rfl
    · rw [FA]; exact natPref_mem_strict (by decide)
    · rw [FB]; exact natPref_mem_strict (by decide)
  · intro p hp x y hall
    rcases hmemA p hp with rfl | rfl
    · simp only [natPref_strict_iff] at hall
      rw [FA, natPref_strict_iff]
      revert hall
      revert x y
      decide
    · simp only [natPref_strict_iff] at hall
      rw [FB, natPref_strict_iff]
      revert hall
      revert x y
      decide
  · intro p hp p' hp' x y hag
    rcases hmemA p hp with rfl | rfl <;> rcases hmemA p' hp' with rfl | rfl
    · exact ⟨Iff.rfl, Iff.rfl⟩
    · rw [FA, FB]
      simp only [natPref] at hag ⊢
      revert hag
      revert x y
      decide
    · rw [FA, FB]
      simp only [natPref] at hag ⊢
      revert hag
      revert x y
      decide
    · exact ⟨Iff.rfl, Iff.rfl⟩
  · intro f hf hM
    have hA : (fun i => natPref (e214A i)) ∈ A := Or.inl rfl
    have hB : (fun i => natPref (e214B i)) ∈ A := Or.inr rfl
    have tA : f (fun i => natPref (e214A i)) = 0 := by
      have h := hf _ hA 0
      rw [FA] at h
      revert h
      generalize f (fun i => natPref (e214A i)) = a
      intro h
      fin_cases a <;> simp_all [natPref]
    have tB : f (fun i => natPref (e214B i)) = 1 := by
      have h := hf _ hB 1
      rw [FB] at h
      revert h
      generalize f (fun i => natPref (e214B i)) = a
      intro h
      fin_cases a <;> simp_all [natPref]
    have hmain : MaintainsPosition (f (fun i => natPref (e214A i)))
        (fun i => natPref (e214A i)) (fun i => natPref (e214B i)) := by
      rw [tA]
      intro i y
      simp only [natPref]
      revert i y
      decide
    have := hM _ hA _ hB hmain
    rw [tA, tB] at this
    exact absurd this (by decide)

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Single-peaked preferences on an interval

MWG, Section 21.D, p. 801 (Example 21.D.4) and Exercises 21.D.4 and 21.D.10, pp. 813-814.

On `X = [a, b] ⊆ ℝ` with its natural order, a continuous rational preference is single peaked
iff it is strictly convex: `αy + (1 - α)z ≻ w` whenever `y ≿ w`, `z ≿ w`, `y ≠ z` and
`α ∈ (0, 1)` (Example 21.D.4). Necessity (Exercise 21.D.4) needs neither continuity nor
compactness. Sufficiency uses a maximal element, which exists by continuity and compactness.

Exercise 21.D.10 (majority voting over a proportional tax rate `t ∈ [0, 1]`, odd number of
agents, positive wealths, increasing utilities of wealth).

**Corrections.**
1. Example 21.D.4 needs `X = [a, b]` nonempty (`a ≤ b`): for `a > b` every relation is
   strictly convex but none is single peaked.
2. Exercise 21.D.10(b): an agent whose wealth equals the mean `w̄` is indifferent between all
   tax rates, so her preference is not single peaked (`exercise_21_D_10b_mean_agent`); all other
   agents are single peaked. The Condorcet-winner claims hold as stated.
3. Exercise 21.D.10(d) is false: with the deadweight loss `(1 - t²)wᵢ`, every agent's
   preference over tax rates is still single peaked (`exercise_21_D_10d`), because ex post
   wealth `(1 - t²)((1 - t)wᵢ + t w̄)` is a product of positive affine functions, hence strictly
   log-concave on `[0, 1)`.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {a b : ℝ}

/-- The convex combination `αy + (1 - α)z` of two points of `[a, b]`, for `α ∈ [0, 1]`. -/
def iccComb (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (y z : Set.Icc a b) : Set.Icc a b :=
  ⟨α * y + (1 - α) * z, by
    have h := (convex_Icc a b) y.2 z.2 hα.1 (sub_nonneg.2 hα.2) (add_sub_cancel α 1)
    simpa [smul_eq_mul] using h⟩

/-- **Example 21.D.4** (MWG, p. 801). A preference on `[a, b]` is strictly convex:
`αy + (1 - α)z ≻ w` whenever `y ≿ w`, `z ≿ w`, `y ≠ z` and `α ∈ (0, 1)`. -/
def StrictlyConvexPref (r : Set.Icc a b → Set.Icc a b → Prop) : Prop :=
  ∀ w y z : Set.Icc a b, ∀ α (hα : α ∈ Set.Ioo (0 : ℝ) 1), r y w → r z w → y ≠ z →
    Strict r (iccComb α (Set.Ioo_subset_Icc_self hα) y z) w

/-- A preference on `[a, b]` is continuous: its graph is closed (MWG, Definition 3.C.1). -/
def ContinuousPref (r : Set.Icc a b → Set.Icc a b → Prop) : Prop :=
  IsClosed {q : Set.Icc a b × Set.Icc a b | r q.1 q.2}

/-- **Exercise 21.D.4** (MWG, p. 813). A single-peaked preference on `[a, b]` is strictly
convex. (Continuity is not needed.) -/
theorem exercise_21_D_4 {r : Set.Icc a b → Set.Icc a b → Prop} (hr : SinglePeaked r) :
    StrictlyConvexPref r := by
  obtain ⟨hrat, x, hx⟩ := hr
  intro w y z α hα hyw hzw hyz
  set m := iccComb α (Set.Ioo_subset_Icc_self hα) y z with hm
  have hm' : (m : ℝ) = α * y + (1 - α) * z := rfl
  have h1 := hα.1
  have h2 := hα.2
  have hyz' : (y : ℝ) ≠ z := fun e => hyz (Subtype.ext e)
  rcases lt_or_gt_of_ne hyz' with hlt | hgt
  · have hym : y < m := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    have hmz : m < z := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    by_cases hmx : m ≤ x
    · exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx y m).1 hmx hym) hyw
    · push Not at hmx
      exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx z m).2 hmx.le hmz) hzw
  · have hzm : z < m := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    have hmy : m < y := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    by_cases hmx : m ≤ x
    · exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx z m).1 hmx hzm) hzw
    · push Not at hmx
      exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx y m).2 hmx.le hmy) hyw

/-- A continuous rational preference on a nonempty compact interval has a maximal element. -/
theorem exists_max_of_continuousPref (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop}
    (hr : Rational r) (hc : ContinuousPref r) : ∃ x, ∀ y, r x y := by
  have hne : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have hclosed : ∀ y : Set.Icc a b, IsClosed {x | r x y} := fun y =>
    hc.preimage (Continuous.prodMk continuous_id continuous_const)
  obtain ⟨x, hx⟩ := isCompact_univ.inter_iInter_nonempty (fun y => {x | r x y}) hclosed
    fun u => by
      classical
      rcases u.eq_empty_or_nonempty with hu | hu
      · obtain ⟨x⟩ := hne
        exact ⟨x, by simp [hu]⟩
      · obtain ⟨m, -, hm⟩ := rational_acyclic hr u hu
        exact ⟨m, Set.mem_univ m, Set.mem_iInter₂.2 fun y hy => hm y hy⟩
  exact ⟨x, fun y => Set.mem_iInter.1 hx.2 y⟩

/-- **Example 21.D.4** (MWG, p. 801), sufficiency. A continuous, rational, strictly convex
preference on a nonempty interval `[a, b]` is single peaked, with peak its maximal element. -/
theorem example_21_D_4_sufficiency (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop}
    (hr : Rational r) (hc : ContinuousPref r) (hsc : StrictlyConvexPref r) : SinglePeaked r := by
  obtain ⟨x, hx⟩ := exists_max_of_continuousPref hab hr hc
  have best : ∀ y, y ≠ x → Strict r x y := by
    intro y hyx
    refine ⟨hx y, fun hyx' => ?_⟩
    have half : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    exact (hsc x y x (1 / 2) half hyx' (complete_refl hr.1 x) hyx).2 (hx _)
  have between : ∀ y z : Set.Icc a b, ((y : ℝ) < z ∧ (z : ℝ) < x) ∨ ((x : ℝ) < z ∧ (z : ℝ) < y) →
      Strict r z y := by
    intro y z hyzx
    have hxy : (x : ℝ) ≠ y := by rcases hyzx with h | h <;> intro e <;> linarith [e ▸ h.1]
    set α := ((z : ℝ) - y) / ((x : ℝ) - y) with hα
    have hαI : α ∈ Set.Ioo (0 : ℝ) 1 := by
      rcases hyzx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · constructor
        · exact div_pos (by linarith) (by linarith)
        · rw [div_lt_one (by linarith)]
          linarith
      · constructor
        · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        · rw [div_lt_one_of_neg (by linarith)]
          linarith
    have hcomb : iccComb α (Set.Ioo_subset_Icc_self hαI) x y = z := by
      apply Subtype.ext
      change α * x + (1 - α) * y = z
      rw [hα]
      field_simp [sub_ne_zero.2 hxy]
      ring
    have := hsc y x y α hαI (hx y) (complete_refl hr.1 y) (fun e => hxy (congrArg _ e))
    rwa [hcomb] at this
  refine ⟨hr, x, fun y z => ⟨fun hzx hyz => ?_, fun hxz hzy => ?_⟩⟩
  · rcases eq_or_lt_of_le hzx with e | e
    · rw [e]
      exact best y (ne_of_lt (e ▸ hyz))
    · exact between y z (Or.inl ⟨Subtype.coe_lt_coe.2 hyz, Subtype.coe_lt_coe.2 e⟩)
  · rcases eq_or_lt_of_le hxz with e | e
    · rw [← e]
      exact best y (ne_of_gt (e ▸ hzy))
    · exact between y z (Or.inr ⟨Subtype.coe_lt_coe.2 e, Subtype.coe_lt_coe.2 hzy⟩)

/-- **Example 21.D.4** (MWG, p. 801). On a nonempty interval `[a, b]`, a continuous rational
preference is single peaked iff it is strictly convex. -/
theorem example_21_D_4 (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop} (hr : Rational r)
    (hc : ContinuousPref r) : SinglePeaked r ↔ StrictlyConvexPref r :=
  ⟨exercise_21_D_4, example_21_D_4_sufficiency hab hr hc⟩

/-- **Example 21.D.4**, correction (MWG, p. 801). On an empty "interval" (`a > b`) every relation
is strictly convex, but none is single peaked. -/
theorem example_21_D_4_empty (hab : b < a) (r : Set.Icc a b → Set.Icc a b → Prop) :
    StrictlyConvexPref r ∧ ¬SinglePeaked r := by
  have hem : ∀ w : Set.Icc a b, False := fun w => by linarith [w.2.1, w.2.2]
  exact ⟨fun w => (hem w).elim, fun h => hem h.2.choose⟩

/-- **Example 21.D.4** (MWG, p. 801). Preferences generated by a strictly quasiconcave utility
are strictly convex. -/
theorem strictlyConvex_of_strictQuasiconcave {u : ℝ → ℝ}
    (hu : ∀ y z : ℝ, y ∈ Set.Icc a b → z ∈ Set.Icc a b → y ≠ z → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      min (u y) (u z) < u (α * y + (1 - α) * z)) :
    StrictlyConvexPref fun s t : Set.Icc a b => u t ≤ u s := by
  intro w y z α hα hyw hzw hyz
  have := hu y z y.2 z.2 (fun e => hyz (Subtype.ext e)) α hα
  have hmin : u w ≤ min (u y) (u z) := le_min hyw hzw
  exact ⟨by change u w ≤ u (α * y + (1 - α) * z); linarith,
    fun h => by change u (α * y + (1 - α) * z) ≤ u w at h; linarith⟩

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Majority voting over a redistributive tax rate

MWG, Exercise 21.D.10, p. 814.

An odd number of agents with wealths `wᵢ > 0` vote over a proportional tax rate
`t ∈ X = [0, 1]`; receipts are redistributed equally. Agent `i` ranks tax rates by ex post
wealth `fᵢ(t)` through a strictly increasing utility `Uᵢ`. The mean wealth `w̄` enters only as a
positive parameter (the results hold for every `w̄ > 0`, in particular for the mean). The
median wealth `w*` is the wealth of a median agent `h` (`IsMedianAgent w h`).

(a) is an interpretation, listed only. (b) `fᵢ(t) = (1 - t)wᵢ + t w̄`: an agent is single peaked
at `0` if `wᵢ > w̄` and at `1` if `wᵢ < w̄`, but **not** single peaked if `wᵢ = w̄`
(correction); `t = 0` (resp. `t = 1`) strictly defeats every other rate when `w* > w̄` (resp.
`w* < w̄`). (c) `fᵢ(t) = (1 - t)²wᵢ + t(1 - t)w̄`: all agents are single peaked with peak
`tᵢ = max(0, (w̄ - 2wᵢ)/(2(w̄ - wᵢ)))` (`tᵢ = 0` if `w̄ ≤ 2wᵢ`); the peak of the median agent is
the Condorcet winner `t_c`, `t_c ≤ 1/2`, `t_c = 0` if `w* ≥ w̄/2` and `t_c > 0` if `w* < w̄/2`.
(d) `fᵢ(t) = (1 - t²)((1 - t)wᵢ + t w̄)`: the claim that preferences need no longer be single
peaked is **false**; they are always single peaked (`exercise_21_D_10d`).
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι : Type*}

/-- The tax rates `X = [0, 1]`. -/
abbrev TaxRates := Set.Icc (0 : ℝ) 1

/-- The preference over tax rates induced by ex post wealth `f` and utility of wealth `U`. -/
def wealthPref (U f : ℝ → ℝ) : TaxRates → TaxRates → Prop := fun t t' => U (f t') ≤ U (f t)

/-- With a strictly increasing utility, the preference compares ex post wealth. -/
theorem wealthPref_iff {U : ℝ → ℝ} (hU : StrictMono U) (f : ℝ → ℝ) (t t' : TaxRates) :
    wealthPref U f t t' ↔ f t' ≤ f t := hU.le_iff_le

/-- Strict preference compares ex post wealth strictly. -/
theorem wealthPref_strict_iff {U : ℝ → ℝ} (hU : StrictMono U) (f : ℝ → ℝ) (t t' : TaxRates) :
    Strict (wealthPref U f) t t' ↔ f t' < f t := by
  simp only [Strict, wealthPref_iff hU, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- The preference induced by ex post wealth is rational. -/
theorem wealthPref_rational (U f : ℝ → ℝ) : Rational (wealthPref U f) :=
  ⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h2 h1⟩

/-- A strictly decreasing ex post wealth gives a preference single peaked at `0`. -/
theorem isPeak_zero {U : ℝ → ℝ} (hU : StrictMono U) {f : ℝ → ℝ}
    (hf : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → f t < f s) :
    IsPeak (wealthPref U f) (⟨0, le_rfl, zero_le_one⟩ : TaxRates) := by
  intro y z
  refine ⟨fun hz hyz => absurd (lt_of_lt_of_le hyz hz) (not_lt.2 ?_), fun _ hzy => ?_⟩
  · exact Subtype.coe_le_coe.1 y.2.1
  · rw [wealthPref_strict_iff hU]
    exact hf z y z.2.1 (Subtype.coe_lt_coe.2 hzy) y.2.2

/-- A strictly increasing ex post wealth gives a preference single peaked at `1`. -/
theorem isPeak_one {U : ℝ → ℝ} (hU : StrictMono U) {f : ℝ → ℝ}
    (hf : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → f s < f t) :
    IsPeak (wealthPref U f) (⟨1, zero_le_one, le_rfl⟩ : TaxRates) := by
  intro y z
  refine ⟨fun _ hyz => ?_, fun hz hzy => absurd (lt_of_le_of_lt hz hzy) (not_lt.2 ?_)⟩
  · rw [wealthPref_strict_iff hU]
    exact hf y z y.2.1 (Subtype.coe_lt_coe.2 hyz) z.2.2
  · exact Subtype.coe_le_coe.1 y.2.2

/-- Ex post wealth in Exercise 21.D.10(b): `(1 - t)wᵢ + t w̄`. -/
def wealthB (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t) * wi + t * wbar

/-- **Exercise 21.D.10(b)** (MWG, p. 814). An agent with `wᵢ > w̄` is single peaked at `0`, an
agent with `wᵢ < w̄` at `1`. -/
theorem exercise_21_D_10b_singlePeaked {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ} :
    (wbar < wi → IsPeak (wealthPref U (wealthB wi wbar)) ⟨0, le_rfl, zero_le_one⟩) ∧
      (wi < wbar → IsPeak (wealthPref U (wealthB wi wbar)) ⟨1, zero_le_one, le_rfl⟩) :=
  ⟨fun h => isPeak_zero hU fun s t _ hst _ => by unfold wealthB; nlinarith,
    fun h => isPeak_one hU fun s t _ hst _ => by unfold wealthB; nlinarith⟩

/-- **Exercise 21.D.10(b)**, correction (MWG, p. 814). An agent whose wealth equals the mean is
indifferent between all tax rates, so her preference is not single peaked. -/
theorem exercise_21_D_10b_mean_agent (U : ℝ → ℝ) (wbar : ℝ) :
    ¬SinglePeaked (wealthPref U (wealthB wbar wbar)) := by
  rintro ⟨-, x, hx⟩
  have hc : ∀ t, wealthB wbar wbar t = wbar := fun t => by unfold wealthB; ring
  obtain ⟨y, hyx⟩ : ∃ y : TaxRates, y ≠ x := by
    by_cases h : (x : ℝ) = 0
    · exact ⟨⟨1, zero_le_one, le_rfl⟩, fun e => by
        have := congrArg Subtype.val e
        simp only at this
        linarith⟩
    · exact ⟨⟨0, le_rfl, zero_le_one⟩, fun e => h (congrArg Subtype.val e).symm⟩
  have := (hx.strict_best hyx).2
  exact this (by simp only [wealthPref, hc, le_refl])

/-- **Exercise 21.D.10(b)** (MWG, p. 814). With an odd number of agents and median agent `h`:
if `w* = wₕ > w̄`, the tax rate `t = 0` is the Condorcet winner and strictly defeats every other
rate; if `w* < w̄`, so does `t = 1`. -/
theorem exercise_21_D_10b_condorcet [Fintype ι] (hodd : Odd (Fintype.card ι)) {U : ι → ℝ → ℝ}
    (hU : ∀ i, StrictMono (U i)) (w : ι → ℝ) (wbar : ℝ) {h : ι} (hh : IsMedianAgent w h) :
    let p : Profile ι TaxRates := fun i => wealthPref (U i) (wealthB (w i) wbar)
    (wbar < w h → IsCondorcetWinner p ⟨0, le_rfl, zero_le_one⟩ ∧
        ∀ t : TaxRates, t ≠ ⟨0, le_rfl, zero_le_one⟩ →
          ¬majorityRel p t ⟨0, le_rfl, zero_le_one⟩) ∧
      (w h < wbar → IsCondorcetWinner p ⟨1, zero_le_one, le_rfl⟩ ∧
        ∀ t : TaxRates, t ≠ ⟨1, zero_le_one, le_rfl⟩ →
          ¬majorityRel p t ⟨1, zero_le_one, le_rfl⟩) := by
  classical
  intro p
  constructor
  · intro hw
    have key : ∀ t : TaxRates, t ≠ ⟨0, le_rfl, zero_le_one⟩ →
        majorityRel p ⟨0, le_rfl, zero_le_one⟩ t ∧
          (univ.filter fun i => Strict (p i) t ⟨0, le_rfl, zero_le_one⟩).card <
            (univ.filter fun i => Strict (p i) ⟨0, le_rfl, zero_le_one⟩ t).card := by
      intro t ht
      have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun e => ht (Subtype.ext e.symm)
      obtain ⟨h1, h2⟩ := majority_of_supporters (m := ⟨0, le_rfl, zero_le_one⟩) (y := t) p
        (univ.filter fun i => w h ≤ w i) hh.1
        fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [wealthPref_strict_iff (hU i)]
          simp only [wealthB]
          nlinarith [t.2.2]
      exact ⟨h1, h2 hodd⟩
    refine ⟨fun t => ?_, fun t ht hmaj => ?_⟩
    · by_cases ht : t = ⟨0, le_rfl, zero_le_one⟩
      · rw [ht, majorityRel_iff]
      · exact (key t ht).1
    · have := (key t ht).2
      rw [majorityRel_iff] at hmaj
      omega
  · intro hw
    have key : ∀ t : TaxRates, t ≠ ⟨1, zero_le_one, le_rfl⟩ →
        majorityRel p ⟨1, zero_le_one, le_rfl⟩ t ∧
          (univ.filter fun i => Strict (p i) t ⟨1, zero_le_one, le_rfl⟩).card <
            (univ.filter fun i => Strict (p i) ⟨1, zero_le_one, le_rfl⟩ t).card := by
      intro t ht
      have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun e => ht (Subtype.ext e)
      obtain ⟨h1, h2⟩ := majority_of_supporters (m := ⟨1, zero_le_one, le_rfl⟩) (y := t) p
        (univ.filter fun i => w i ≤ w h) hh.2
        fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [wealthPref_strict_iff (hU i)]
          simp only [wealthB]
          nlinarith [t.2.1]
      exact ⟨h1, h2 hodd⟩
    refine ⟨fun t => ?_, fun t ht hmaj => ?_⟩
    · by_cases ht : t = ⟨1, zero_le_one, le_rfl⟩
      · rw [ht, majorityRel_iff]
      · exact (key t ht).1
    · have := (key t ht).2
      rw [majorityRel_iff] at hmaj
      omega

/-- Ex post wealth in Exercise 21.D.10(c): `(1 - t)²wᵢ + t(1 - t)w̄`. -/
def wealthC (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t) ^ 2 * wi + t * (1 - t) * wbar

/-- The peak of `wealthC`: `0` if `w̄ ≤ 2wᵢ`, otherwise `(w̄ - 2wᵢ)/(2(w̄ - wᵢ))`. -/
noncomputable def peakC (wi wbar : ℝ) : ℝ :=
  if wbar ≤ 2 * wi then 0 else (wbar - 2 * wi) / (2 * (wbar - wi))

/-- The peak of `wealthC` lies in `[0, 1/2]` (for `wᵢ > 0`). -/
theorem peakC_mem {wi wbar : ℝ} (hwi : 0 < wi) : 0 ≤ peakC wi wbar ∧ peakC wi wbar ≤ 1 / 2 := by
  unfold peakC
  split_ifs with h
  · norm_num
  · push Not at h
    have hd : 0 < 2 * (wbar - wi) := by linarith
    constructor
    · exact div_nonneg (by linarith) hd.le
    · rw [div_le_iff₀ hd]
      linarith

/-- The peak of `wealthC` as a tax rate. -/
noncomputable def peakCRate {wi : ℝ} (wbar : ℝ) (hwi : 0 < wi) : TaxRates :=
  ⟨peakC wi wbar, (peakC_mem (wbar := wbar) hwi).1, by linarith [(peakC_mem (wbar := wbar) hwi).2]⟩

/-- **Exercise 21.D.10(c)** (MWG, p. 814). Every agent's preference over tax rates is single
peaked, with peak `peakC wᵢ w̄`. -/
theorem exercise_21_D_10c_singlePeaked {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ}
    (hwi : 0 < wi) (hwbar : 0 < wbar) :
    IsPeak (wealthPref U (wealthC wi wbar)) (peakCRate wbar hwi) := by
  intro y z
  have hy0 := y.2.1
  have hy1 := y.2.2
  have hz0 := z.2.1
  have hz1 := z.2.2
  simp only [wealthPref_strict_iff hU]
  by_cases hge : wbar ≤ wi
  · have hpk : (peakCRate wbar hwi : ℝ) = 0 := by
      simp only [peakCRate, peakC, show wbar ≤ 2 * wi by linarith, ↓reduceIte]
    refine ⟨fun hz hyz => ?_, fun _ hzy => ?_⟩
    · have := Subtype.coe_le_coe.2 hz
      have := Subtype.coe_lt_coe.2 hyz
      rw [hpk] at *
      linarith
    · have hlt : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
      have hD : (wbar - 2 * wi) + ((y : ℝ) + z) * (wi - wbar) < 0 := by
        have : ((y : ℝ) + z) * (wi - wbar) ≤ 2 * (wi - wbar) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have e : wealthC wi wbar y - wealthC wi wbar z =
          ((y : ℝ) - z) * ((wbar - 2 * wi) + ((y : ℝ) + z) * (wi - wbar)) := by
        simp only [wealthC]
        ring
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hlt) hD]
  · push Not at hge
    set k := wbar - wi with hk
    have hkpos : 0 < k := by linarith
    set r := (wbar - 2 * wi) / (2 * k) with hr
    have hsq : ∀ t : ℝ, wealthC wi wbar t = wealthC wi wbar r - k * (t - r) ^ 2 := by
      intro t
      simp only [wealthC, hr]
      field_simp
      ring
    have hcmp : ∀ s t : ℝ, (s - r) ^ 2 < (t - r) ^ 2 → wealthC wi wbar t < wealthC wi wbar s :=
      fun s t h => by rw [hsq s, hsq t]; nlinarith
    by_cases hle : wbar ≤ 2 * wi
    · have hpk : (peakCRate wbar hwi : ℝ) = 0 := by
        simp only [peakCRate, peakC, hle, ↓reduceIte]
      have hr0 : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      refine ⟨fun hz hyz => ?_, fun _ hzy => ?_⟩
      · have := Subtype.coe_le_coe.2 hz
        have := Subtype.coe_lt_coe.2 hyz
        rw [hpk] at *
        linarith
      · have hlt : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
        exact hcmp z y (by nlinarith)
    · have hpk : (peakCRate wbar hwi : ℝ) = r := by
        simp only [peakCRate, peakC, hle, ↓reduceIte, hr, hk]
      refine ⟨fun hz hyz => ?_, fun hz hzy => ?_⟩
      · have h1 : (z : ℝ) ≤ r := hpk ▸ Subtype.coe_le_coe.2 hz
        have h2 : (y : ℝ) < z := Subtype.coe_lt_coe.2 hyz
        exact hcmp z y (by nlinarith)
      · have h1 : r ≤ (z : ℝ) := hpk ▸ Subtype.coe_le_coe.2 hz
        have h2 : (z : ℝ) < y := Subtype.coe_lt_coe.2 hzy
        exact hcmp z y (by nlinarith)

/-- The peak `peakC` is antitone in wealth. -/
theorem peakC_antitone {wi wj wbar : ℝ} (hwi : 0 < wi) (hij : wi ≤ wj) :
    peakC wj wbar ≤ peakC wi wbar := by
  have hj := peakC_mem (wbar := wbar) (lt_of_lt_of_le hwi hij)
  have hi := peakC_mem (wbar := wbar) hwi
  unfold peakC at hj hi ⊢
  by_cases h2 : wbar ≤ 2 * wj
  · simp only [h2, ↓reduceIte] at hj ⊢
    exact hi.1
  · have h1 : ¬wbar ≤ 2 * wi := by linarith
    simp only [h1, h2, ↓reduceIte]
    push Not at h1 h2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- **Exercise 21.D.10(c)** (MWG, p. 814). With an odd number of agents and `h` a median agent
for wealth, the median agent's peak `t_c` is the Condorcet winner (and strictly defeats every
other rate); `t_c ≤ 1/2`; `t_c = 0` if `w* ≥ w̄/2` and `t_c > 0` if `w* < w̄/2`. -/
theorem exercise_21_D_10c [Fintype ι] (hodd : Odd (Fintype.card ι)) {U : ι → ℝ → ℝ}
    (hU : ∀ i, StrictMono (U i)) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {wbar : ℝ} (hwbar : 0 < wbar)
    {h : ι} (hh : IsMedianAgent w h) :
    let p : Profile ι TaxRates := fun i => wealthPref (U i) (wealthC (w i) wbar)
    IsCondorcetWinner p (peakCRate wbar (hw h)) ∧
      (∀ t, t ≠ peakCRate wbar (hw h) → ¬IsCondorcetWinner p t) ∧
      (peakCRate wbar (hw h) : ℝ) ≤ 1 / 2 ∧
      (wbar / 2 ≤ w h → (peakCRate wbar (hw h) : ℝ) = 0) ∧
      (w h < wbar / 2 → 0 < (peakCRate wbar (hw h) : ℝ)) := by
  classical
  intro p
  let pk : ι → TaxRates := fun i => peakCRate wbar (hw i)
  have hpk : ∀ i, IsPeak (p i) (pk i) := fun i =>
    exercise_21_D_10c_singlePeaked (hU i) (hw i) hwbar
  have hmed : IsMedianAgent pk h := by
    constructor
    · refine le_trans hh.2 (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact Subtype.coe_le_coe.1 (peakC_antitone (hw i) hi)
    · refine le_trans hh.1 (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact Subtype.coe_le_coe.1 (peakC_antitone (hw h) hi)
  obtain ⟨hcw, hstrict⟩ := proposition_21_D_1 hpk hmed
  refine ⟨hcw, fun t ht hcwt => ?_, (peakC_mem (hw h)).2, fun hge => ?_, fun hlt => ?_⟩
  · have h1 := hstrict hodd t ht
    have h2 := hcwt (pk h)
    rw [majorityRel_iff] at h2
    omega
  · simp only [peakCRate, peakC, show wbar ≤ 2 * w h by linarith, ↓reduceIte]
  · simp only [peakCRate, peakC, show ¬wbar ≤ 2 * w h by linarith, ↓reduceIte]
    exact div_pos (by linarith) (by linarith)

/-- Ex post wealth in Exercise 21.D.10(d): `(1 - t²)((1 - t)wᵢ + t w̄)`. -/
def wealthD (wi wbar : ℝ) (t : ℝ) : ℝ := (1 - t ^ 2) * ((1 - t) * wi + t * wbar)

/-- `wealthD` is strictly quasiconcave on `[0, 1]`: it is a product of positive affine functions
on `[0, 1)`, hence strictly log-concave there, and it vanishes at `1`. -/
theorem wealthD_strictQuasiconcave {wi wbar : ℝ} (hwi : 0 < wi) (hwbar : 0 < wbar) :
    ∀ y z : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → z ∈ Set.Icc (0 : ℝ) 1 → y ≠ z →
      ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        min (wealthD wi wbar y) (wealthD wi wbar z) < wealthD wi wbar (α * y + (1 - α) * z) := by
  intro y z hy hz hyz α hα
  obtain ⟨hα0, hα1⟩ := hα
  set m := α * y + (1 - α) * z with hm
  have hm0 : 0 ≤ m := by nlinarith [hy.1, hz.1]
  have hm1 : m < 1 := by
    rcases lt_or_gt_of_ne hyz with h | h <;> nlinarith [hy.2, hz.2]
  have pos3 : ∀ t, 0 ≤ t → t ≤ 1 → 0 < (1 - t) * wi + t * wbar := fun t h0 h1 => by
    rcases eq_or_lt_of_le h1 with e | e
    · rw [e]; linarith
    · nlinarith
  have posD : ∀ t, 0 ≤ t → t < 1 → 0 < wealthD wi wbar t := fun t h0 h1 =>
    mul_pos (by nlinarith) (pos3 t h0 h1.le)
  have hDm := posD m hm0 hm1
  by_cases hy1 : y = 1
  · have : wealthD wi wbar y = 0 := by rw [hy1]; simp [wealthD]
    rw [this]
    exact lt_of_le_of_lt (min_le_left _ _) hDm
  by_cases hz1 : z = 1
  · have : wealthD wi wbar z = 0 := by rw [hz1]; simp [wealthD]
    rw [this]
    exact lt_of_le_of_lt (min_le_right _ _) hDm
  have hy1' : y < 1 := lt_of_le_of_ne hy.2 hy1
  have hz1' : z < 1 := lt_of_le_of_ne hz.2 hz1
  have hDy := posD y hy.1 hy1'
  have hDz := posD z hz.1 hz1'
  have hβ : (0 : ℝ) < 1 - α := by linarith
  have hsum : α + (1 - α) = 1 := by ring
  have logD : ∀ t, 0 ≤ t → t < 1 → Real.log (wealthD wi wbar t) =
      Real.log (1 - t) + Real.log (1 + t) + Real.log ((1 - t) * wi + t * wbar) := by
    intro t h0 h1
    have e : wealthD wi wbar t = (1 - t) * (1 + t) * ((1 - t) * wi + t * wbar) := by
      simp only [wealthD]
      ring
    rw [e, Real.log_mul (by nlinarith) (pos3 t h0 h1.le).ne', Real.log_mul (by linarith)
      (by linarith)]
  have c1 : α * Real.log (1 - y) + (1 - α) * Real.log (1 - z) < Real.log (1 - m) := by
    have := strictConcaveOn_log_Ioi.2 (show (1 - y) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith) (show (1 - z) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith) (fun e => hyz (by linarith)) hα0 hβ hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have c2 : α * Real.log (1 + y) + (1 - α) * Real.log (1 + z) ≤ Real.log (1 + m) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 + y) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith [hy.1]) (show (1 + z) ∈ Set.Ioi (0 : ℝ) by
      simp only [Set.mem_Ioi]; linarith [hz.1]) hα0.le hβ.le hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have c3 : α * Real.log ((1 - y) * wi + y * wbar) + (1 - α) * Real.log ((1 - z) * wi + z * wbar)
      ≤ Real.log ((1 - m) * wi + m * wbar) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (pos3 y hy.1 hy.2) (pos3 z hz.1 hz.2) hα0.le
      hβ.le hsum
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm]
    ring
  have hlog : α * Real.log (wealthD wi wbar y) + (1 - α) * Real.log (wealthD wi wbar z) <
      Real.log (wealthD wi wbar m) := by
    rw [logD y hy.1 hy1', logD z hz.1 hz1', logD m hm0 hm1]
    linarith
  have hmin : Real.log (min (wealthD wi wbar y) (wealthD wi wbar z)) <
      Real.log (wealthD wi wbar m) := by
    rcases min_choice (wealthD wi wbar y) (wealthD wi wbar z) with e | e
    · rw [e]
      have : Real.log (wealthD wi wbar y) ≤ Real.log (wealthD wi wbar z) :=
        Real.log_le_log hDy (e ▸ min_le_right _ _)
      nlinarith
    · rw [e]
      have : Real.log (wealthD wi wbar z) ≤ Real.log (wealthD wi wbar y) :=
        Real.log_le_log hDz (e ▸ min_le_left _ _)
      nlinarith
  exact (Real.log_lt_log_iff (lt_min hDy hDz) hDm).1 hmin

/-- **Exercise 21.D.10(d)** (MWG, p. 814), refuted. With the deadweight loss `(1 - t²)wᵢ`,
every agent's preference over tax rates is still single peaked (for any `wᵢ, w̄ > 0` and any
strictly increasing utility of wealth), contrary to the printed claim. -/
theorem exercise_21_D_10d {U : ℝ → ℝ} (hU : StrictMono U) {wi wbar : ℝ} (hwi : 0 < wi)
    (hwbar : 0 < wbar) : SinglePeaked (wealthPref U (wealthD wi wbar)) := by
  have hcont : Continuous (wealthD wi wbar) := by unfold wealthD; fun_prop
  have hc : ContinuousPref (wealthPref U (wealthD wi wbar)) := by
    have e : {q : TaxRates × TaxRates | wealthPref U (wealthD wi wbar) q.1 q.2} =
        {q | wealthD wi wbar q.2 ≤ wealthD wi wbar q.1} := by
      ext q
      exact wealthPref_iff hU _ q.1 q.2
    unfold ContinuousPref
    rw [e]
    exact isClosed_le (hcont.comp (continuous_subtype_val.comp continuous_snd))
      (hcont.comp (continuous_subtype_val.comp continuous_fst))
  have hsc : StrictlyConvexPref (wealthPref U (wealthD wi wbar)) := by
    have := strictlyConvex_of_strictQuasiconcave (a := 0) (b := 1)
      (wealthD_strictQuasiconcave hwi hwbar)
    intro w y z α hα hyw hzw hyz
    have h := this w y z α hα ((wealthPref_iff hU _ y w).1 hyw) ((wealthPref_iff hU _ z w).1 hzw)
      hyz
    exact (wealthPref_strict_iff hU _ _ _).2 (lt_of_le_of_ne h.1 fun e => h.2 e.ge)
  exact example_21_D_4_sufficiency zero_le_one (wealthPref_rational U _) hc hsc

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Single-peakedness cannot be weakened to weak monotonicity

MWG, Exercise 21.D.14, p. 815.

Five agents and five alternatives `x, y, z, v, w` (here `0, …, 4`) with the printed
preferences (indifferences allowed). (a) There is no Condorcet winner. (b) For the order
`x < y < z < v < w`, every agent's preference is weakly increasing as the agent's (unique) most
preferred alternative is approached. (c) Placing the alternatives at `0, 1/4, 1/2, 3/4, 1`,
the preferences are induced by quasiconcave utility functions on `[0, 1]`. (d) The same five
utility functions on the whole interval `[0, 1]` are quasiconcave, each has a single maximal
alternative, and there is no Condorcet winner in `[0, 1]`.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

/-- The utilities of Exercise 21.D.14 on `x, y, z, v, w = 0, …, 4`:
`x ≻₁ y ∼₁ z ∼₁ v ∼₁ w`, `y ≻₂ x ≻₂ z ≻₂ v ≻₂ w`, `z ≻₃ y ∼₃ v ∼₃ w ≻₃ x`,
`v ≻₄ w ≻₄ x ∼₄ y ∼₄ z`, `w ≻₅ x ∼₅ y ∼₅ z ∼₅ v`. -/
def e2114 : Fin 5 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![4, 5, 3, 2, 1], ![0, 1, 2, 1, 1], ![0, 0, 0, 2, 1], ![0, 0, 0, 0, 1]]

/-- **Exercise 21.D.14(a)** (MWG, p. 815). There is no Condorcet winner: every alternative is
defeated by majority voting by some other alternative. -/
theorem exercise_21_D_14a :
    ∀ m : Fin 5, ∃ y, Strict (majorityRel fun i => natPref (e2114 i)) y m := by
  simp only [Strict, majorityRel_natPref]
  decide

/-- Weak single-peakedness: `x` is a most preferred alternative and preference is weakly
increasing as `x` is approached from either side (Exercise 21.D.14). -/
def WeaklySinglePeaked {X : Type*} [LinearOrder X] (r : X → X → Prop) (x : X) : Prop :=
  (∀ y, r x y) ∧ ∀ y z, (z ≤ x → y < z → r z y) ∧ (x ≤ z → z < y → r z y)

/-- **Exercise 21.D.14(b)** (MWG, p. 815). For the order `x < y < z < v < w`, each agent's
preference is weakly increasing towards the agent's most preferred alternative, which is
unique. -/
theorem exercise_21_D_14b :
    ∀ i : Fin 5, WeaklySinglePeaked (natPref (e2114 i)) i ∧
      ∀ y, y ≠ i → Strict (natPref (e2114 i)) i y := by
  simp only [WeaklySinglePeaked, natPref, Strict]
  decide

/-- The five utility functions on `[0, 1]` of Exercise 21.D.14(c)-(d). -/
noncomputable def e2114u (i : Fin 5) (t : ℝ) : ℝ :=
  match i with
  | 0 => if t = 0 then 1 else 0
  | 1 => min (t - 1 / 4) (1 / 2 - 2 * t)
  | 2 => if t = 0 then 0 else if t = 1 / 2 then 2 else 1
  | 3 => if t ≤ 1 / 2 then 0 else if t = 3 / 4 then 2 else 1
  | 4 => if t = 1 then 1 else 0

/-- The location of alternative `j` in `[0, 1]`: `x, y, z, v, w ↦ 0, 1/4, 1/2, 3/4, 1`. -/
noncomputable def e2114pos (j : Fin 5) : ℝ := ![0, 1 / 4, 1 / 2, 3 / 4, 1] j

/-- A function on `[0, 1]` that is weakly increasing up to `p` and weakly decreasing after `p`
is quasiconcave. -/
theorem quasiconcaveOn_of_unimodal {u : ℝ → ℝ} {p : ℝ}
    (hup : ∀ s t, 0 ≤ s → s ≤ t → t ≤ p → u s ≤ u t)
    (hdown : ∀ s t, p ≤ s → s ≤ t → t ≤ 1 → u t ≤ u s) :
    QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) u := by
  intro γ
  rw [convex_iff_ordConnected]
  refine ⟨fun s hs t ht m hm => ⟨⟨le_trans hs.1.1 hm.1, le_trans hm.2 ht.1.2⟩, ?_⟩⟩
  by_cases hmp : m ≤ p
  · exact le_trans hs.2 (hup s m hs.1.1 hm.1 hmp)
  · push Not at hmp
    exact le_trans ht.2 (hdown m t hmp.le hm.2 ht.1.2)

/-- **Exercise 21.D.14(c)-(d)** (MWG, p. 815). Each of the five utility functions is
quasiconcave on `[0, 1]` and has a single maximal alternative there, at `0, 1/4, 1/2, 3/4, 1`
respectively. -/
theorem exercise_21_D_14_quasiconcave (i : Fin 5) :
    QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (e2114u i) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ e2114pos i → e2114u i t < e2114u i (e2114pos i) := by
  fin_cases i
  · refine ⟨quasiconcaveOn_of_unimodal (p := 0) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · have : s = t := by linarith
      rw [this]
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos] at hne ⊢
      norm_num at hne ⊢
      simp [e2114u, hne]
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1 / 4) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      rw [min_eq_left (by linarith), min_eq_left (by linarith)]
      linarith
    · simp only [e2114u]
      rw [min_eq_right (by linarith), min_eq_right (by linarith)]
      linarith
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      rcases lt_or_gt_of_ne hne with h | h
      · left
        linarith
      · right
        linarith
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1 / 2) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      split_ifs <;> norm_num
  · refine ⟨quasiconcaveOn_of_unimodal (p := 3 / 4) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      split_ifs <;> norm_num
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · have : s = t := by linarith
      rw [this]
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      simp [hne]

/-- **Exercise 21.D.14(c)** (MWG, p. 815). Restricted to the five points
`0, 1/4, 1/2, 3/4, 1`, the quasiconcave utilities induce exactly the preferences of the
exercise. -/
theorem exercise_21_D_14c (i j k : Fin 5) :
    e2114u i (e2114pos k) ≤ e2114u i (e2114pos j) ↔ e2114 i k ≤ e2114 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [e2114u, e2114pos, e2114]

/-- `s` defeats `t` by majority voting under the utilities `e2114u`. -/
def e2114Defeats (s t : ℝ) : Prop :=
  (univ.filter fun i : Fin 5 => e2114u i s < e2114u i t).card <
    (univ.filter fun i : Fin 5 => e2114u i t < e2114u i s).card

/-- **Exercise 21.D.14(d)** (MWG, p. 815). With five agents, alternatives `[0, 1]` and the
quasiconcave utilities `e2114u` (each with a single maximal alternative), there is no Condorcet
winner: every `t ∈ [0, 1]` is defeated by some `s ∈ [0, 1]`. -/
theorem exercise_21_D_14d : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1, e2114Defeats s t := by
  intro t ht
  have count : ∀ s (A B : Finset (Fin 5)),
      (univ.filter fun i : Fin 5 => e2114u i s < e2114u i t) = A →
      (univ.filter fun i : Fin 5 => e2114u i t < e2114u i s) = B → A.card < B.card →
      e2114Defeats s t := fun s A B hA hB hAB => by
    unfold e2114Defeats
    rw [hA, hB]
    exact hAB
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    refine ⟨1 / 4, by norm_num, count _ {0} {1, 2} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  have key : ∀ s, e2114Defeats s t ↔
      (∑ i : Fin 5, if e2114u i s < e2114u i t then 1 else 0) <
        ∑ i : Fin 5, if e2114u i t < e2114u i s then 1 else 0 := by
    intro s
    simp only [e2114Defeats, card_filter]
  by_cases hhalf : t < 1 / 2
  · have ht1 : t ≠ 1 := by linarith
    have a0 : e2114u 0 t = 0 := by simp only [e2114u, h0.ne', ↓reduceIte]
    have a0s : e2114u 0 1 = 0 := by norm_num [e2114u]
    have a1 : e2114u 1 1 < e2114u 1 t := by
      simp only [e2114u]
      rw [lt_min_iff]
      constructor <;> norm_num <;> linarith
    have a1' := not_lt.2 a1.le
    have a2 : e2114u 2 t = 1 := by simp only [e2114u, h0.ne', hhalf.ne, ↓reduceIte]
    have a2s : e2114u 2 1 = 1 := by norm_num [e2114u]
    have a3 : e2114u 3 t = 0 := by simp only [e2114u, hhalf.le, ↓reduceIte]
    have a3s : e2114u 3 1 = 1 := by norm_num [e2114u]
    have a4 : e2114u 4 t = 0 := by simp only [e2114u, ht1, ↓reduceIte]
    have a4s : e2114u 4 1 = 1 := by norm_num [e2114u]
    refine ⟨1, by norm_num, (key 1).2 ?_⟩
    simp only [Fin.sum_univ_five, a0, a0s, a1, a1', a2, a2s, a3, a3s, a4, a4s,
      lt_self_iff_false, ↓reduceIte]
    norm_num
  by_cases hh : t = 1 / 2
  · subst hh
    refine ⟨0, by norm_num, count _ {2} {0, 1} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  have hgt : 1 / 2 < t := lt_of_le_of_ne (not_lt.1 hhalf) (Ne.symm hh)
  by_cases h1 : t = 1
  · subst h1
    refine ⟨3 / 4, by norm_num, count _ {4} {1, 3} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  · have e0 : e2114u 0 t = 0 := by simp only [e2114u, h0.ne', ↓reduceIte]
    have e0s : e2114u 0 (1 / 2) = 0 := by norm_num [e2114u]
    have e1 : e2114u 1 t < e2114u 1 (1 / 2) := by
      simp only [e2114u]
      rw [min_lt_iff]
      right
      norm_num
      linarith
    have e1' := not_lt.2 e1.le
    have e2 : e2114u 2 t = 1 := by simp only [e2114u, h0.ne', hh, ↓reduceIte]
    have e2s : e2114u 2 (1 / 2) = 2 := by norm_num [e2114u]
    have e3 : e2114u 3 (1 / 2) < e2114u 3 t := by
      have : e2114u 3 (1 / 2) = 0 := by norm_num [e2114u]
      rw [this]
      simp only [e2114u, not_le.2 hgt, ↓reduceIte]
      split_ifs <;> norm_num
    have e3' := not_lt.2 e3.le
    have e4 : e2114u 4 t = 0 := by simp only [e2114u, h1, ↓reduceIte]
    have e4s : e2114u 4 (1 / 2) = 0 := by norm_num [e2114u]
    refine ⟨1 / 2, by norm_num, (key (1 / 2)).2 ?_⟩
    simp only [Fin.sum_univ_five, e0, e0s, e1, e1', e2, e2s, e3, e3', e4, e4s,
      lt_self_iff_false, ↓reduceIte]
    norm_num

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Majority voting with multidimensional alternatives

MWG, Section 21.D, p. 804 (Example 21.D.5 and footnote 10) and Exercise 21.D.12, p. 815.

Example 21.D.5: three agents with linear utilities on the unit square; every alternative is
beaten by majority voting (cases (i)-(iii)), each utility has a single maximal element, and the
cone spanned by the three gradients is all of `ℝ²`. Points of the square are pairs `(x₁, x₂)`.

Exercise 21.D.12: three agents share a cost `c > 0` by taxes `(t₁, t₂, t₃) ≥ 0`; each prefers a
lower own tax. (a) No strictly positive alternative is a Condorcet winner. (b) (Discussion,
made precise:) an alternative with exactly one zero tax is not a Condorcet winner, and one in
which a single agent pays everything is a (weak) Condorcet winner.
-/

namespace MWG.SocialChoice

open Finset

/-- The utilities of Example 21.D.5: `u₁ = -2x₁ - x₂`, `u₂ = x₁ + 2x₂`, `u₃ = x₁ - x₂`. -/
def ex21D5u (i : Fin 3) (x : ℝ × ℝ) : ℝ :=
  match i with
  | 0 => -2 * x.1 - x.2
  | 1 => x.1 + 2 * x.2
  | 2 => x.1 - x.2

/-- The unit square `[0, 1]²`. -/
def unitSquare : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1}

/-- **Example 21.D.5** (MWG, p. 804), case (i): if `x₁ = 0`, then `(1/2, x₂)` is preferred by
agents 2 and 3. -/
theorem example_21_D_5_i (x : ℝ × ℝ) (hx : x ∈ unitSquare) (h0 : x.1 = 0) :
    ((1 / 2, x.2) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 1 x < ex21D5u 1 (1 / 2, x.2) ∧
      ex21D5u 2 x < ex21D5u 2 (1 / 2, x.2) := by
  obtain ⟨-, -, h3, h4⟩ := hx
  refine ⟨⟨by norm_num, by norm_num, h3, h4⟩, ?_, ?_⟩ <;> simp only [ex21D5u, h0] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804), case (ii): if `x₂ = 1`, then `(x₁, 1/2)` is preferred by
agents 1 and 3. -/
theorem example_21_D_5_ii (x : ℝ × ℝ) (hx : x ∈ unitSquare) (h1 : x.2 = 1) :
    ((x.1, 1 / 2) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 0 x < ex21D5u 0 (x.1, 1 / 2) ∧
      ex21D5u 2 x < ex21D5u 2 (x.1, 1 / 2) := by
  obtain ⟨h1', h2, -, -⟩ := hx
  refine ⟨⟨h1', h2, by norm_num, by norm_num⟩, ?_, ?_⟩ <;> simp only [ex21D5u, h1] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804), case (iii): if `x₁ > 0` and `x₂ < 1`, then for
`0 < ε ≤ min(x₁, 1 - x₂)`, `(x₁ - ε, x₂ + ε)` lies in the square and is preferred by agents
1 and 2. -/
theorem example_21_D_5_iii (x : ℝ × ℝ) (hx : x ∈ unitSquare)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ x.1) (hε2 : ε ≤ 1 - x.2) :
    ((x.1 - ε, x.2 + ε) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 0 x < ex21D5u 0 (x.1 - ε, x.2 + ε) ∧
      ex21D5u 1 x < ex21D5u 1 (x.1 - ε, x.2 + ε) := by
  obtain ⟨-, h2, h3, -⟩ := hx
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ?_, ?_⟩ <;>
    simp only [ex21D5u] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804). For every `x` in the square there is `y` in the square
preferred to `x` by two of the three agents: there is no Condorcet winner. -/
theorem example_21_D_5 (x : ℝ × ℝ) (hx : x ∈ unitSquare) :
    ∃ y ∈ unitSquare, ∃ i j : Fin 3, i ≠ j ∧ ex21D5u i x < ex21D5u i y ∧
      ex21D5u j x < ex21D5u j y := by
  by_cases h0 : x.1 = 0
  · obtain ⟨hy, h1, h2⟩ := example_21_D_5_i x hx h0
    exact ⟨_, hy, 1, 2, by decide, h1, h2⟩
  by_cases h1 : x.2 = 1
  · obtain ⟨hy, h1', h2⟩ := example_21_D_5_ii x hx h1
    exact ⟨_, hy, 0, 2, by decide, h1', h2⟩
  have hpos : 0 < x.1 := lt_of_le_of_ne hx.1 (Ne.symm h0)
  have hlt : x.2 < 1 := lt_of_le_of_ne hx.2.2.2 h1
  obtain ⟨hy, h1', h2⟩ := example_21_D_5_iii x hx (ε := min x.1 (1 - x.2))
    (lt_min hpos (by linarith)) (min_le_left _ _) (min_le_right _ _)
  exact ⟨_, hy, 0, 1, by decide, h1', h2⟩

/-- **Example 21.D.5** (MWG, p. 804). Each utility has a single maximal element on the square,
at `(0, 0)`, `(1, 1)` and `(1, 0)` respectively. -/
theorem example_21_D_5_unique_max :
    (∀ y ∈ unitSquare, y ≠ (0, 0) → ex21D5u 0 y < ex21D5u 0 (0, 0)) ∧
      (∀ y ∈ unitSquare, y ≠ (1, 1) → ex21D5u 1 y < ex21D5u 1 (1, 1)) ∧
      (∀ y ∈ unitSquare, y ≠ (1, 0) → ex21D5u 2 y < ex21D5u 2 (1, 0)) := by
  refine ⟨fun y hy hne => ?_, fun y hy hne => ?_, fun y hy hne => ?_⟩ <;>
    obtain ⟨h1, h2, h3, h4⟩ := hy <;> simp only [ex21D5u] <;> by_contra hc <;> push Not at hc <;>
    apply hne <;> ext <;> simp <;> linarith

/-- **Example 21.D.5** (MWG, p. 805). The cone spanned by the gradients `(-2, -1)`, `(1, 2)`,
`(1, -1)` is all of `ℝ²`. -/
theorem example_21_D_5_cone (v : ℝ × ℝ) :
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧
      v = (μ 0 * -2 + μ 1 * 1 + μ 2 * 1, μ 0 * -1 + μ 1 * 2 + μ 2 * -1) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (-2 * v.1 + v.2) / 3 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (2 * v.2 - v.1) / 3 := ⟨_, rfl⟩
  refine ⟨![a + (|a| + |b|), b + (|a| + |b|), |a| + |b|], fun i => ?_, ?_⟩
  · fin_cases i <;> simp <;> linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b]
  · ext
    · change v.1 = (a + (|a| + |b|)) * -2 + (b + (|a| + |b|)) * 1 + (|a| + |b|) * 1
      rw [ha, hb]
      ring
    · change v.2 = (a + (|a| + |b|)) * -1 + (b + (|a| + |b|)) * 2 + (|a| + |b|) * -1
      rw [ha, hb]
      ring

/-- The alternatives of Exercise 21.D.12: tax shares `t ≥ 0` with `t₁ + t₂ + t₃ = c`. -/
def taxShares (c : ℝ) : Set (Fin 3 → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ t 0 + t 1 + t 2 = c}

/-- `s` defeats `t` by majority voting when each agent prefers a lower own tax: more agents
pay strictly less under `s` than under `t`. -/
def taxDefeats (s t : Fin 3 → ℝ) : Prop :=
  (univ.filter fun i => t i < s i).card < (univ.filter fun i => s i < t i).card

/-- Count a defeat through explicit sums. -/
theorem taxDefeats_iff (s t : Fin 3 → ℝ) :
    taxDefeats s t ↔ ((if t 0 < s 0 then 1 else 0) + (if t 1 < s 1 then 1 else 0) +
      (if t 2 < s 2 then 1 else 0) : ℕ) < (if s 0 < t 0 then 1 else 0) +
        (if s 1 < t 1 then 1 else 0) + (if s 2 < t 2 then 1 else 0) := by
  simp only [taxDefeats, card_filter, Fin.sum_univ_three]

/-- **Exercise 21.D.12(a)** (MWG, p. 815). No strictly positive alternative is a Condorcet
winner: lowering the taxes of agents 1 and 2 by `ε = min(t₁, t₂)` and raising agent 3's by
`2ε` gives an alternative that defeats it. -/
theorem exercise_21_D_12a {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (hpos : ∀ i, 0 < t i) :
    ∃ s ∈ taxShares c, taxDefeats s t := by
  set ε := min (t 0) (t 1) with hε
  have hε0 : 0 < ε := lt_min (hpos 0) (hpos 1)
  have h1 : ε ≤ t 0 := min_le_left _ _
  have h2 : ε ≤ t 1 := min_le_right _ _
  refine ⟨![t 0 - ε, t 1 - ε, t 2 + 2 * ε], ⟨fun i => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> simp <;> linarith [ht.1 2]
  · simp
    linarith [ht.2]
  · rw [taxDefeats_iff]
    have a0 : ¬t 0 < t 0 - ε := by linarith
    have a1 : ¬t 1 < t 1 - ε := by linarith
    have a2 : t 2 < t 2 + 2 * ε := by linarith
    have b0 : t 0 - ε < t 0 := by linarith
    have b1 : t 1 - ε < t 1 := by linarith
    have b2 : ¬t 2 + 2 * ε < t 2 := by linarith
    simp [a0, a1, a2, b0, b1, b2]

/-- **Exercise 21.D.12(b)** (MWG, p. 815). An alternative with exactly one zero tax is not a
Condorcet winner either: the two taxed agents can both pay less if the third pays more. -/
theorem exercise_21_D_12b_one_zero {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (k : Fin 3)
    (hk : t k = 0) (hpos : ∀ j, j ≠ k → 0 < t j) : ∃ s ∈ taxShares c, taxDefeats s t := by
  fin_cases k
  · set ε := min (t 1) (t 2)
    have hε0 : 0 < ε := lt_min (hpos 1 (by decide)) (hpos 2 (by decide))
    have h1 : ε ≤ t 1 := min_le_left _ _
    have h2 : ε ≤ t 2 := min_le_right _ _
    refine ⟨![t 0 + 2 * ε, t 1 - ε, t 2 - ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 0]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 1 < t 1 - ε ∧ ¬t 2 < t 2 - ε ∧ t 0 < t 0 + 2 * ε ∧ t 1 - ε < t 1 ∧
          t 2 - ε < t 2 ∧ ¬t 0 + 2 * ε < t 0 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]
  · set ε := min (t 0) (t 2)
    have hε0 : 0 < ε := lt_min (hpos 0 (by decide)) (hpos 2 (by decide))
    have h1 : ε ≤ t 0 := min_le_left _ _
    have h2 : ε ≤ t 2 := min_le_right _ _
    refine ⟨![t 0 - ε, t 1 + 2 * ε, t 2 - ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 1]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 0 < t 0 - ε ∧ ¬t 2 < t 2 - ε ∧ t 1 < t 1 + 2 * ε ∧ t 0 - ε < t 0 ∧
          t 2 - ε < t 2 ∧ ¬t 1 + 2 * ε < t 1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]
  · set ε := min (t 0) (t 1)
    have hε0 : 0 < ε := lt_min (hpos 0 (by decide)) (hpos 1 (by decide))
    have h1 : ε ≤ t 0 := min_le_left _ _
    have h2 : ε ≤ t 1 := min_le_right _ _
    refine ⟨![t 0 - ε, t 1 - ε, t 2 + 2 * ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 2]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 0 < t 0 - ε ∧ ¬t 1 < t 1 - ε ∧ t 2 < t 2 + 2 * ε ∧ t 0 - ε < t 0 ∧
          t 1 - ε < t 1 ∧ ¬t 2 + 2 * ε < t 2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]

/-- **Exercise 21.D.12(b)** (MWG, p. 815). An alternative in which one agent pays the whole
cost is a Condorcet winner: no alternative is preferred by more agents than prefer it. -/
theorem exercise_21_D_12b_one_payer {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (k : Fin 3)
    (hk : ∀ j, j ≠ k → t j = 0) : ∀ s ∈ taxShares c, ¬taxDefeats s t ∧
      (s ≠ t → (univ.filter fun i => t i < s i).Nonempty) := by
  intro s hs
  have hs0 := hs.1
  have hsum := ht.2
  refine ⟨fun hd => ?_, fun hne => ?_⟩
  · have hsub : (univ.filter fun i => s i < t i) ⊆ {k} := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      by_contra hik
      have := hk i (by simpa using hik)
      linarith [hs0 i]
    have c1 := card_le_card hsub
    rw [card_singleton] at c1
    have : (univ.filter fun i => t i < s i).card = 0 := by
      unfold taxDefeats at hd
      omega
    rw [card_eq_zero, filter_eq_empty_iff] at this
    have hle : ∀ i, s i ≤ t i := fun i => not_lt.1 (this (mem_univ i))
    have hsk : s k < t k := by
      have hc := card_pos.1 (by unfold taxDefeats at hd; omega :
        0 < (univ.filter fun i => s i < t i).card)
      obtain ⟨i, hi⟩ := hc
      have hik : i = k := mem_singleton.1 (hsub hi)
      subst hik
      simpa using hi
    have hsum' : s 0 + s 1 + s 2 < t 0 + t 1 + t 2 := by
      fin_cases k <;> simp at hsk <;> linarith [hle 0, hle 1, hle 2]
    linarith [hs.2]
  · by_contra hem
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hem
    have hle : ∀ i, s i ≤ t i := fun i => not_lt.1 (hem (mem_univ i))
    apply hne
    funext i
    have htot : s 0 + s 1 + s 2 = t 0 + t 1 + t 2 := by rw [hs.2, hsum]
    fin_cases i <;> simp <;> linarith [hle 0, hle 1, hle 2]

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Euclidean preferences, medians and Condorcet winners

MWG, Section 21.D, pp. 805-806: Example 21.D.6 (Euclidean preferences), Figures 21.D.6-21.D.8
and footnotes 11-12.

Alternatives and ideal points live in a real inner product space `E` (MWG: `ℝⁿ`). The agent
with peak `x` ranks alternatives by distance to `x`. The peaks preferring `y` to `z` form
`A(y, z) = {x : ‖x - y‖ < ‖x - z‖}`, an open half-space bounded by the perpendicular bisector
of `[y, z]`. A continuum of agents is a probability measure `μ` on peaks (MWG: a density `g`).
`x*` is a *median* if every open half-space bounded by a hyperplane through `x*` has mass at
most `1/2`; with null hyperplanes (e.g. a density) this is the book's "each half-space has mass
`1/2`" (`isMedianPoint_iff_book`). We prove, for every probability measure, that `x*` is a
Condorcet winner iff it is a median (MWG's two arguments, made precise with continuity of
measure). Figure 21.D.8(a): the centre of a rectangle is a median of the uniform distribution
(proved for every centrally symmetric measure).

**Departure.** The book's median ("each half-space has mass `1/2`") presupposes that hyperplanes
are null; our definition works for all probability measures and agrees with it then.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 805). The Euclidean preference with peak `x`:
`y ≿ z` iff `‖y - x‖ ≤ ‖z - x‖` (utility `-‖y - x‖`). -/
def euclidPref (x : E) : E → E → Prop := fun y z => ‖y - x‖ ≤ ‖z - x‖

omit [InnerProductSpace ℝ E] in
/-- Euclidean preferences are rational and have `x` as their unique best alternative. -/
theorem euclidPref_spec (x : E) :
    Rational (euclidPref x) ∧ ∀ y, y ≠ x → Strict (euclidPref x) x y := by
  refine ⟨⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h1 h2⟩, fun y hy => ?_⟩
  have : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  simp only [Strict, euclidPref, sub_self, norm_zero]
  exact ⟨this.le, not_le.2 this⟩

omit [InnerProductSpace ℝ E] in
/-- **Example 21.D.6** (MWG, p. 805). Each peak identifies a unique Euclidean preference:
different peaks give different preferences. -/
theorem euclidPref_injective {x x' : E} (h : euclidPref x = euclidPref x') : x = x' := by
  by_contra hne
  have h1 := (euclidPref_spec x').2 x hne
  rw [← h] at h1
  have h2 := (euclidPref_spec x).2 x' (Ne.symm hne)
  exact strict_asymm h2 h1

/-- **Example 21.D.6** (MWG, p. 805). `A(y, z)`: the peaks of the agents preferring `y` to `z`. -/
def prefRegion (y z : E) : Set E := {x | ‖x - y‖ < ‖x - z‖}

omit [InnerProductSpace ℝ E] in
/-- An agent with peak `x` prefers `y` to `z` iff `x ∈ A(y, z)`. -/
theorem strict_euclidPref_iff (x y z : E) : Strict (euclidPref x) y z ↔ x ∈ prefRegion y z := by
  simp only [Strict, euclidPref, prefRegion, Set.mem_ofPred_eq, not_le, norm_sub_rev x]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Distance comparison through the inner product:
`‖x - y‖ < ‖x - z‖ ↔ ‖y - z‖² < 2⟪x - z, y - z⟫`. -/
theorem mem_prefRegion_iff (x y z : E) :
    x ∈ prefRegion y z ↔ ‖y - z‖ ^ 2 < 2 * ⟪x - z, y - z⟫ := by
  have e : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 - 2 * ⟪x - z, y - z⟫ + ‖y - z‖ ^ 2 := by
    rw [← norm_sub_sq_real]
    congr 1
    abel
  simp only [prefRegion, Set.mem_ofPred_eq]
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Example 21.D.6** (MWG, p. 805, Figure 21.D.6). `A(y, z)` is the open half-space
`{x : ⟪x, z - y⟫ < (‖z‖² - ‖y‖²)/2}`. -/
theorem prefRegion_eq_halfspace (y z : E) :
    prefRegion y z = {x | ⟪x, z - y⟫ < (‖z‖ ^ 2 - ‖y‖ ^ 2) / 2} := by
  ext x
  simp only [prefRegion, Set.mem_ofPred_eq]
  have ey : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have ez : ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, z⟫ + ‖z‖ ^ 2 := norm_sub_sq_real x z
  have ei : ⟪x, z - y⟫ = ⟪x, z⟫ - ⟪x, y⟫ := inner_sub_right x z y
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Example 21.D.6** (MWG, p. 805). The boundary of `A(y, z)` is the hyperplane perpendicular
to `[y, z]` through its midpoint: `‖x - y‖ = ‖x - z‖ ↔ ⟪x - (y + z)/2, z - y⟫ = 0`. -/
theorem bisector_iff (x y z : E) :
    ‖x - y‖ = ‖x - z‖ ↔ ⟪x - (1 / 2 : ℝ) • (y + z), z - y⟫ = 0 := by
  have ey : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have ez : ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, z⟫ + ‖z‖ ^ 2 := norm_sub_sq_real x z
  have ei : ⟪x - (1 / 2 : ℝ) • (y + z), z - y⟫ = ⟪x, z⟫ - ⟪x, y⟫ - (‖z‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_add_left,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real, real_inner_comm y z]
    ring
  rw [ei]
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    have : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 := by rw [h]
    linarith
  · intro h
    have : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 := by linarith
    nlinarith [sq_nonneg (‖x - y‖ - ‖x - z‖), sq_nonneg (‖x - y‖ + ‖x - z‖)]

variable [MeasurableSpace E] [BorelSpace E]

/-- The open half-space `{z : ⟪z - x, q⟫ > 0}` bounded by the hyperplane through `x` with
normal `q`. -/
def openHalfSpace (x q : E) : Set E := {z | 0 < ⟪z - x, q⟫}

/-- Open half-spaces are measurable. -/
theorem measurableSet_openHalfSpace (x q : E) : MeasurableSet (openHalfSpace x q) :=
  (isOpen_lt continuous_const ((continuous_id.sub continuous_const).inner
    continuous_const)).measurableSet

/-- **Example 21.D.6** (MWG, p. 805). `x` is a median of the distribution `μ` of peaks: every
open half-space bounded by a hyperplane through `x` has at most half of the mass. -/
def IsMedianPoint (μ : Measure E) (x : E) : Prop :=
  ∀ q : E, q ≠ 0 → 2 * μ (openHalfSpace x q) ≤ μ Set.univ

/-- **Example 21.D.6** (MWG, p. 805). `x` is a Condorcet winner for the distribution `μ`: no
alternative is preferred to `x` by more agents than prefer `x` to it. -/
def IsCondorcetWinnerMeasure (μ : Measure E) (x : E) : Prop :=
  ∀ y, μ (prefRegion y x) ≤ μ (prefRegion x y)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The two open half-spaces bounded by a hyperplane through `x` are disjoint. -/
theorem disjoint_openHalfSpace (x q : E) :
    Disjoint (openHalfSpace x q) (openHalfSpace x (-q)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [openHalfSpace, inner_neg_right, Set.mem_ofPred_eq] at hz hz'
  linarith

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `A(y, z)` and `A(z, y)` are disjoint. -/
theorem disjoint_prefRegion (y z : E) : Disjoint (prefRegion y z) (prefRegion z y) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  simp only [prefRegion, Set.mem_ofPred_eq] at h1 h2
  linarith

omit [BorelSpace E] in
/-- **Example 21.D.6** (MWG, p. 805), the book's median: when hyperplanes are null, `x` is a
median iff every hyperplane through `x` splits the mass into two halves (`2μ(H) = 1`). -/
theorem isMedianPoint_iff_book (μ : Measure E) [IsProbabilityMeasure μ] (x : E)
    (hnull : ∀ q : E, μ {z | ⟪z - x, q⟫ = 0} = 0) :
    IsMedianPoint μ x ↔ ∀ q : E, q ≠ 0 → 2 * μ (openHalfSpace x q) = 1 := by
  constructor
  · intro h q hq
    have h1 := h q hq
    have h2 := h (-q) (neg_ne_zero.2 hq)
    rw [measure_univ] at h1 h2
    have hcover : Set.univ ⊆ (openHalfSpace x q ∪ openHalfSpace x (-q)) ∪
        {z | ⟪z - x, q⟫ = 0} := by
      intro z _
      simp only [openHalfSpace, inner_neg_right, Set.mem_union, Set.mem_ofPred_eq]
      rcases lt_trichotomy 0 ⟪z - x, q⟫ with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm
      · exact Or.inl (Or.inr (by linarith))
    have hge : 1 ≤ μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := by
      calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
        _ ≤ μ ((openHalfSpace x q ∪ openHalfSpace x (-q)) ∪ {z | ⟪z - x, q⟫ = 0}) :=
          measure_mono hcover
        _ ≤ μ (openHalfSpace x q ∪ openHalfSpace x (-q)) + μ {z | ⟪z - x, q⟫ = 0} :=
          measure_union_le _ _
        _ = μ (openHalfSpace x q ∪ openHalfSpace x (-q)) := by rw [hnull q, add_zero]
        _ ≤ μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := measure_union_le _ _
    refine le_antisymm h1 ?_
    have h3 : 1 + 1 ≤ 2 * μ (openHalfSpace x q) + 1 := by
      calc (1 : ENNReal) + 1 = 2 * 1 := by norm_num
        _ ≤ 2 * (μ (openHalfSpace x q) + μ (openHalfSpace x (-q))) := by gcongr
        _ = 2 * μ (openHalfSpace x q) + 2 * μ (openHalfSpace x (-q)) := mul_add _ _ _
        _ ≤ 2 * μ (openHalfSpace x q) + 1 := by gcongr
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h3
  · intro h q hq
    rw [h q hq, measure_univ]

/-- **Example 21.D.6** (MWG, pp. 805-806). For any probability distribution of peaks, `x*` is a
Condorcet winner iff it is a median. (If `y ≠ x*`, `A(y, x*)` lies in an open half-space
through `x*` and `A(x*, y)` contains the complementary closed one; if `x*` is not a median,
moving slightly from `x*` in the direction `q` of a heavy half-space defeats `x*`, by continuity
of the measure: Figure 21.D.7.) -/
theorem example_21_D_6 (μ : Measure E) [IsProbabilityMeasure μ] (x : E) :
    IsMedianPoint μ x ↔ IsCondorcetWinnerMeasure μ x := by
  constructor
  · intro h y
    by_cases hyx : y = x
    · subst hyx
      have : prefRegion y y = ∅ := by
        ext z
        simp [prefRegion]
      rw [this]
    set q := y - x with hq
    have hq0 : q ≠ 0 := sub_ne_zero.2 hyx
    set H := openHalfSpace x q
    have hH := measurableSet_openHalfSpace x q
    have s1 : prefRegion y x ⊆ H := by
      intro z hz
      rw [mem_prefRegion_iff] at hz
      simp only [H, openHalfSpace, Set.mem_ofPred_eq]
      nlinarith [sq_nonneg ‖y - x‖]
    have s2 : Hᶜ ⊆ prefRegion x y := by
      intro z hz
      simp only [H, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hz
      rw [mem_prefRegion_iff]
      have e : ⟪z - y, x - y⟫ = -⟪z - x, q⟫ + ‖x - y‖ ^ 2 := by
        have h1 : z - y = (z - x) - q := by rw [hq]; abel
        have h2 : x - y = -q := by rw [hq]; abel
        rw [h1, h2, inner_neg_right, inner_sub_left, norm_neg, ← real_inner_self_eq_norm_sq]
        ring
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
      rw [e]
      nlinarith
    have h1 := h q hq0
    rw [← measure_add_measure_compl hH, two_mul] at h1
    have h2 : μ H ≤ μ Hᶜ := (ENNReal.add_le_add_iff_left (measure_ne_top μ H)).1 h1
    exact (measure_mono s1).trans (h2.trans (measure_mono s2))
  · intro h
    by_contra hm
    simp only [IsMedianPoint, not_forall, not_le] at hm
    obtain ⟨q, hq0, hq⟩ := hm
    rw [measure_univ] at hq
    have hp : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    let A : ℕ → Set E := fun n => prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x
    have hAmem : ∀ n z, z ∈ A n ↔ (1 / ((n : ℝ) + 1)) * ‖q‖ ^ 2 < 2 * ⟪z - x, q⟫ := by
      intro n z
      simp only [A]
      rw [mem_prefRegion_iff, add_sub_cancel_left, norm_smul, inner_smul_right,
        Real.norm_eq_abs, abs_of_pos (hp n), mul_pow]
      have hpn := hp n
      constructor
      · intro h'
        by_contra hc
        push Not at hc
        nlinarith [mul_le_mul_of_nonneg_left hc hpn.le]
      · intro h'
        nlinarith [mul_lt_mul_of_pos_left h' hpn]
    have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hmono : Monotone A := by
      intro n m hnm z hz
      rw [hAmem] at hz ⊢
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      nlinarith [sq_nonneg ‖q‖]
    have hunion : (⋃ n, A n) = openHalfSpace x q := by
      ext z
      simp only [Set.mem_iUnion, openHalfSpace, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩
        rw [hAmem] at hn
        nlinarith [hp n, sq_nonneg ‖q‖, mul_pos (hp n) (pow_pos hqpos 2)]
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos (mul_pos two_pos hz) (pow_pos hqpos 2))
        refine ⟨n, (hAmem n z).2 ?_⟩
        rw [lt_div_iff₀ (pow_pos hqpos 2)] at hn
        linarith
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at ht
    have ht2 := ENNReal.Tendsto.const_mul ht (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    obtain ⟨n, hn⟩ := (ht2.eventually (lt_mem_nhds hq)).exists
    have hcw := h (x + (1 / ((n : ℝ) + 1)) • q)
    have hmeas : MeasurableSet (prefRegion x (x + (1 / ((n : ℝ) + 1)) • q)) :=
      (isOpen_lt (continuous_id.sub continuous_const).norm
        (continuous_id.sub continuous_const).norm).measurableSet
    have hsum := measure_union (μ := μ) (disjoint_prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x)
      hmeas
    have hle : μ (prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x ∪
        prefRegion x (x + (1 / ((n : ℝ) + 1)) • q)) ≤ 1 := prob_le_one
    rw [hsum] at hle
    have : 2 * μ (A n) ≤ 1 := by
      rw [two_mul]
      exact le_trans (add_le_add le_rfl hcw) hle
    exact absurd hn (not_lt.2 this)

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Medians of symmetric distributions; intermediate preferences

MWG, Figure 21.D.8(a), p. 806, and Exercise 21.D.9 (Grandmont), pp. 813-814.

A distribution of peaks that is symmetric about `x` has `x` as a median; in particular the
centre of a rectangle is a median of the uniform distribution on it (Figure 21.D.8(a)).

Exercise 21.D.9: (a) a positive combination of two utilities represents preferences
intermediate between them; (b) for utilities `u_β = ∑ βₙ hₙ` linear in the parameter, the set
`B(x, y)` of parameters preferring `x` to `y` is `ℝ^N_{++}` intersected with an open half-space;
(c) **correction**: with merely intermediate preferences along segments of parameters the set
`{β : y ≿_β x}` is convex, but `B(x, y)` itself need not be the intersection of the parameter
set with a half-space (it need not even be convex): `exercise_21_D_9c_counterexample`;
(d) a median agent exists for a symmetric density (the uniform density on a rectangle); the
nonexistence half (the triangle of Figure 21.D.8(b)) is in `TriangleMedian`; (e) a median agent
`β*` whose neighbourhoods carry positive mass (MWG: `g(β*) > 0`; for a density this needs
continuity at `β*`, which we assume in the form of positive mass on open sets approaching `β*`)
makes its
unique best alternative a strict majority winner; (f) Euclidean preferences are of this form,
with alternatives and agents kept separate.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 806). A measure invariant under the point reflection about `x`
has `x` as a median. -/
theorem isMedianPoint_of_symmetric (μ : Measure E) (x : E)
    (hsym : Measure.map (fun z => (x + x) - z) μ = μ) : IsMedianPoint μ x := by
  intro q _
  have hmeas : Measurable fun z : E => (x + x) - z :=
    (continuous_const.sub continuous_id).measurable
  have hpre : (fun z => (x + x) - z) ⁻¹' openHalfSpace x q = openHalfSpace x (-q) := by
    ext z
    simp only [openHalfSpace, Set.mem_preimage, Set.mem_ofPred_eq, inner_neg_right]
    have : x + x - z - x = -(z - x) := by abel
    rw [this, inner_neg_left]
  have h1 : μ (openHalfSpace x q) = μ (openHalfSpace x (-q)) := by
    conv_lhs => rw [← hsym]
    rw [Measure.map_apply hmeas (measurableSet_openHalfSpace x q), hpre]
  calc 2 * μ (openHalfSpace x q) = μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := by
        rw [two_mul, ← h1]
    _ = μ (openHalfSpace x q ∪ openHalfSpace x (-q)) :=
        (measure_union (disjoint_openHalfSpace x q) (measurableSet_openHalfSpace x (-q))).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

/-- Point reflection preserves Lebesgue measure on a finite-dimensional inner product space. -/
theorem measurePreserving_reflect [FiniteDimensional ℝ E] (c : E) :
    MeasurePreserving (fun z : E => c - z) volume volume := by
  have h1 := (LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving
  have h2 := measurePreserving_add_left (volume : Measure E) c
  convert h2.comp h1 using 1
  funext x
  simp [sub_eq_add_neg]

/-- The axis-parallel rectangle `[a₀, b₀] × [a₁, b₁]` in the plane. -/
def rectangle (a0 b0 a1 b1 : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | a0 ≤ z 0 ∧ z 0 ≤ b0 ∧ a1 ≤ z 1 ∧ z 1 ≤ b1}

/-- **Figure 21.D.8(a)** (MWG, p. 806). The centre of a rectangle is a median of the uniform
distribution on it (Lebesgue measure restricted to the rectangle). -/
theorem figure_21_D_8a (a0 b0 a1 b1 : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    (hc0 : c 0 = (a0 + b0) / 2) (hc1 : c 1 = (a1 + b1) / 2) :
    IsMedianPoint (volume.restrict (rectangle a0 b0 a1 b1)) c := by
  apply isMedianPoint_of_symmetric
  have hR : MeasurableSet (rectangle a0 b0 a1 b1) := by
    unfold rectangle
    measurability
  have hpre : (fun z => (c + c) - z) ⁻¹' rectangle a0 b0 a1 b1 = rectangle a0 b0 a1 b1 := by
    ext z
    simp only [rectangle, Set.mem_preimage, Set.mem_ofPred_eq, PiLp.sub_apply, PiLp.add_apply,
      hc0, hc1]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have := (measurePreserving_reflect (c + c)).restrict_preimage hR
  rw [hpre] at this
  exact this.map_eq

/-- **Figure 21.D.8(a)**, non-vacuity: the centre exists. -/
theorem figure_21_D_8a_center (a0 b0 a1 b1 : ℝ) :
    ∃ c : EuclideanSpace ℝ (Fin 2), c 0 = (a0 + b0) / 2 ∧ c 1 = (a1 + b1) / 2 :=
  ⟨EuclideanSpace.single 0 ((a0 + b0) / 2) + EuclideanSpace.single 1 ((a1 + b1) / 2),
    by simp, by simp⟩

/-- **Exercise 21.D.9** (MWG, p. 813). `≿''` is intermediate between `≿` and `≿'`: `x ≿ y` and
`x ≿' y` imply `x ≿'' y`. -/
def Intermediate {X : Type*} (r r' r'' : X → X → Prop) : Prop :=
  ∀ x y, r x y → r' x y → r'' x y

/-- **Exercise 21.D.9(a)** (MWG, p. 813). For `ψ, γ > 0`, `ψu + γu'` represents preferences
intermediate between those represented by `u` and `u'`. -/
theorem exercise_21_D_9a {X : Type*} (u u' : X → ℝ) {ψ γ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) :
    Intermediate (UtilityPref u) (UtilityPref u') (UtilityPref fun x => ψ * u x + γ * u' x) :=
  fun _ _ h1 h2 => by
    simp only [UtilityPref] at *
    nlinarith

/-- The utility `u_β(x) = ∑ βₙ hₙ(x)` (Exercise 21.D.9(b)). -/
def linParamUtil {X : Type*} {N : ℕ} (h : Fin N → X → ℝ) (β : Fin N → ℝ) (x : X) : ℝ :=
  ∑ n, β n * h n x

/-- **Exercise 21.D.9(b)** (MWG, p. 813). `B(x, y) = {β ∈ ℝ^N_{++} : u_β(x) > u_β(y)}` is the
intersection of `ℝ^N_{++}` with the open half-space `{β : ∑ βₙ (hₙ(x) - hₙ(y)) > 0}` (whose
boundary passes through the origin; empty if `h(x) = h(y)`). -/
theorem exercise_21_D_9b {X : Type*} {N : ℕ} (h : Fin N → X → ℝ) (x y : X) :
    {β : Fin N → ℝ | (∀ n, 0 < β n) ∧ linParamUtil h β y < linParamUtil h β x} =
      {β : Fin N → ℝ | ∀ n, 0 < β n} ∩ {β | 0 < ∑ n, β n * (h n x - h n y)} := by
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, linParamUtil, mul_sub,
    Finset.sum_sub_distrib, sub_pos]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(c)** (MWG, p. 814), what remains true. If the parameter set `P` is convex
and the preference of every convex combination of two parameters is intermediate between
theirs, then for all alternatives `x, y` the set `{β ∈ P : y ≿_β x}` (the complement of
`B(x, y)` in `P` for complete preferences) is convex. -/
theorem exercise_21_D_9c {X : Type*} {P : Set E} (hP : Convex ℝ P) (r : E → X → X → Prop)
    (hint : ∀ β ∈ P, ∀ β' ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      Intermediate (r β) (r β') (r (a • β + b • β'))) (x y : X) :
    Convex ℝ {β ∈ P | r β y x} := by
  intro β hβ β' hβ' a b ha hb hab
  exact ⟨hP hβ.1 hβ'.1 ha hb hab, hint β hβ.1 β' hβ'.1 a b ha hb hab y x hβ.2 hβ'.2⟩

/-- The family of Exercise 21.D.9(c)'s counterexample, on alternatives `true` (`x`) and
`false` (`y`) and parameters `β ∈ [0, 1]`: `x ≻ y` at `β = 0, 1`, and `x ∼ y` for
`0 < β < 1`. -/
def e219Family (β : ℝ) (a b : Bool) : Prop :=
  a = b ∨ (a = true ∧ b = false) ∨ β ∈ Set.Ioo (0 : ℝ) 1

/-- **Exercise 21.D.9(c)** (MWG, p. 814), correction. The family `e219Family` on the convex
parameter set `[0, 1]` has intermediate preferences along segments, yet
`B(x, y) = {β ∈ [0, 1] : x ≻_β y} = {0, 1}` is not convex, so it is not the intersection of
`[0, 1]` with any half-space: the conclusion of (b) does not carry over. -/
theorem exercise_21_D_9c_counterexample :
    (∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ β' ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → Intermediate (e219Family β) (e219Family β') (e219Family (a • β + b • β'))) ∧
      ¬Convex ℝ {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} ∧
      ¬∃ (s c : ℝ), {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} =
        Set.Icc (0 : ℝ) 1 ∩ {β | c < s * β} := by
  have key : {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} =
      Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Strict, e219Family]
    simp
  have hnc : ¬Convex ℝ {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} := by
    rw [key]
    intro hc
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by simp
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by simp
    have := hc h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    norm_num at this
  refine ⟨?_, hnc, ?_⟩
  · intro β hβ β' hβ' a b ha hb hab u v h1 h2
    simp only [e219Family] at h1 h2 ⊢
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    rcases h2 with h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ((convex_Ioo (0 : ℝ) 1) h1 h2 ha hb hab))
  · rintro ⟨s, c, he⟩
    apply hnc
    rw [he]
    refine (convex_Icc 0 1).inter ?_
    intro u hu v hv a b ha hb hab
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hu hv ⊢
    have e : s * (a * u + b * v) - c = a * (s * u - c) + b * (s * v - c) := by
      linear_combination c * hab
    have hpos : 0 < a * (s * u - c) + b * (s * v - c) := by
      rcases eq_or_lt_of_le ha with h | h
      · have hb1 : b = 1 := by linarith
        rw [← h, hb1]
        linarith
      · nlinarith [mul_pos h (sub_pos.2 hu), mul_nonneg hb (sub_pos.2 hv).le]
    linarith

/-- **Exercise 21.D.9(d)** (MWG, p. 814), existence half. For the uniform density on the square
`[1, 2]² ⊆ ℝ²_{++}` of parameters, the centre `(3/2, 3/2)` is a median agent. -/
theorem exercise_21_D_9d_exists :
    ∃ c : EuclideanSpace ℝ (Fin 2), (∀ i, 0 < c i) ∧ IsMedianPoint (volume.restrict
      (rectangle 1 2 1 2)) c ∧ rectangle 1 2 1 2 ⊆ {z | ∀ i, 0 < z i} := by
  obtain ⟨c, hc0, hc1⟩ := figure_21_D_8a_center 1 2 1 2
  refine ⟨c, fun i => ?_, figure_21_D_8a 1 2 1 2 c hc0 hc1, fun z hz i => ?_⟩
  · fin_cases i
    · simp only [Fin.zero_eta, hc0]
      norm_num
    · simp only [Fin.mk_one, hc1]
      norm_num
  · obtain ⟨h1, -, h3, -⟩ := hz
    fin_cases i
    · simp only [Fin.zero_eta]
      linarith
    · simp only [Fin.mk_one]
      linarith

/-- **Exercise 21.D.9(e)** (MWG, p. 814). Let utilities be linear in the parameter,
`u_β(x) = ⟪β, H x⟫`, let `β*` be a median agent of the distribution `μ`, with positive mass on
every open set approaching `β*` (MWG: `g(β*) > 0`), and let `x*` be the single most preferred
alternative of `β*`. Then `x*` defeats every other alternative in pairwise majority voting. -/
theorem exercise_21_D_9e {X : Type*} (μ : Measure E) [IsProbabilityMeasure μ] (H : X → E)
    (βs : E) (hmed : IsMedianPoint μ βs)
    (hpos : ∀ U : Set E, IsOpen U → βs ∈ closure U → 0 < μ U) (xs : X)
    (hbest : ∀ y, y ≠ xs → ⟪βs, H y⟫ < ⟪βs, H xs⟫) (y : X) (hy : y ≠ xs) :
    μ {β | ⟪β, H xs⟫ < ⟪β, H y⟫} < μ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := by
  set a := H xs - H y with ha
  set c := ⟪βs, a⟫ with hc
  have hcpos : 0 < c := by
    rw [hc, ha, inner_sub_right]
    linarith [hbest y hy]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [hc, h0, inner_zero_right] at hcpos
    exact lt_irrefl _ hcpos
  have hdecomp : ∀ β, ⟪β, a⟫ = ⟪β - βs, a⟫ + c := fun β => by
    rw [hc, inner_sub_left]
    ring
  set Cc := openHalfSpace βs (-a) with hCc
  have hCcm := measurableSet_openHalfSpace βs (-a)
  set S := {β : E | -c < ⟪β - βs, a⟫ ∧ ⟪β - βs, a⟫ < 0} with hS
  have hSopen : IsOpen S := by
    have hf : Continuous fun β : E => ⟪β - βs, a⟫ :=
      (continuous_id.sub continuous_const).inner continuous_const
    exact (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hSclos : βs ∈ closure S := by
    have hlim : Tendsto (fun t : ℝ => βs - t • a) (𝓝[>] 0) (𝓝 βs) := by
      have : Continuous fun t : ℝ => βs - t • a := continuous_const.sub (continuous_id.smul
        continuous_const)
      have h0 := this.tendsto 0
      simp only [zero_smul, sub_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hna : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 ha0) 2
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hcpos hna)] with t ht
    have e : ⟪βs - t • a - βs, a⟫ = -(t * ‖a‖ ^ 2) := by
      rw [show βs - t • a - βs = -(t • a) by abel, inner_neg_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    simp only [hS, Set.mem_ofPred_eq, e]
    obtain ⟨ht0, ht1⟩ := ht
    rw [lt_div_iff₀ hna] at ht1
    constructor
    · linarith
    · nlinarith
  have hSpos := hpos S hSopen hSclos
  have hsub1 : {β | ⟪β, H xs⟫ < ⟪β, H y⟫} ⊆ Cc := by
    intro β hβ
    simp only [Set.mem_ofPred_eq] at hβ
    simp only [hCc, openHalfSpace, Set.mem_ofPred_eq, inner_neg_right]
    have h1 := hdecomp β
    rw [ha, inner_sub_right] at h1
    linarith
  have hsub2 : Ccᶜ ∪ S ⊆ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := by
    intro β hβ
    have h1 := hdecomp β
    rw [ha, inner_sub_right] at h1
    simp only [Set.mem_ofPred_eq]
    rcases hβ with hβ | hβ
    · simp only [hCc, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, inner_neg_right,
        not_lt] at hβ
      linarith
    · simp only [hS, Set.mem_ofPred_eq] at hβ
      linarith [hβ.1]
  have hdisj : Disjoint Ccᶜ S := by
    rw [Set.disjoint_left]
    intro β h1 h2
    simp only [hCc, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, inner_neg_right,
      not_lt] at h1
    simp only [hS, Set.mem_ofPred_eq] at h2
    linarith [h2.2]
  have hmed' := hmed (-a) (neg_ne_zero.2 ha0)
  rw [← measure_add_measure_compl hCcm, two_mul] at hmed'
  have hle : μ Cc ≤ μ Ccᶜ := (ENNReal.add_le_add_iff_left (measure_ne_top μ Cc)).1 hmed'
  calc μ {β | ⟪β, H xs⟫ < ⟪β, H y⟫} ≤ μ Cc := measure_mono hsub1
    _ ≤ μ Ccᶜ := hle
    _ < μ Ccᶜ + μ S := ENNReal.lt_add_right (measure_ne_top μ _) (ne_of_gt hSpos)
    _ = μ (Ccᶜ ∪ S) := (measure_union hdisj hSopen.measurableSet).symm
    _ ≤ μ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := measure_mono hsub2

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(f)** (MWG, p. 814). Euclidean preferences fit the framework with agents
and alternatives kept apart: the agent with peak `x` ranks alternatives by
`v_x(y) = ⟪x, y⟫ - ‖y‖²/2`, which is affine in the parameter `x`. -/
theorem exercise_21_D_9f (x y z : E) :
    euclidPref x y z ↔ ⟪x, z⟫ - ‖z‖ ^ 2 / 2 ≤ ⟪x, y⟫ - ‖y‖ ^ 2 / 2 := by
  have ey : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have ez : ‖z - x‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪z, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real z x
  rw [real_inner_comm x y] at ey
  rw [real_inner_comm x z] at ez
  simp only [euclidPref]
  have h1 := norm_nonneg (y - x)
  have h2 := norm_nonneg (z - x)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(f)** (MWG, p. 814). The Euclidean preference with peak `ax + bx'`
(`a, b ≥ 0`, `a + b = 1`) is intermediate between those with peaks `x` and `x'`. -/
theorem exercise_21_D_9f_intermediate (x x' : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    Intermediate (euclidPref x) (euclidPref x') (euclidPref (a • x + b • x')) := by
  intro y z h1 h2
  rw [exercise_21_D_9f] at h1 h2 ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left]
  have e : ∀ t : ℝ, t = a * t + b * t := fun t => by linear_combination (-t) * hab
  rw [e (‖z‖ ^ 2 / 2), e (‖y‖ ^ 2 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Exercise 21.D.9(e)**, non-vacuity. On the parameter line `ℝ` with the uniform distribution
on `[0, 1]`, `β* = 1/2` is a median, open sets approaching `1/2` have positive mass, and with
`H(true) = 1`, `H(false) = -1` the alternative `true` is the single best one for `β*`. -/
theorem exercise_21_D_9e_instance :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      IsMedianPoint (volume.restrict (Set.Icc (0 : ℝ) 1)) (1 / 2) ∧
      (∀ U : Set ℝ, IsOpen U → (1 / 2 : ℝ) ∈ closure U →
        0 < volume.restrict (Set.Icc (0 : ℝ) 1) U) ∧
      ∀ y : Bool, y ≠ true → ⟪(1 / 2 : ℝ), (if y then (1 : ℝ) else -1)⟫ <
        ⟪(1 / 2 : ℝ), (if true then (1 : ℝ) else -1)⟫ := by
  refine ⟨⟨by simp⟩, ?_, fun U hU hcl => ?_, fun y hy => ?_⟩
  · intro q hq
    rw [Measure.restrict_apply_univ, Real.volume_Icc, Measure.restrict_apply
      (measurableSet_openHalfSpace _ _)]
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · have e : openHalfSpace (1 / 2 : ℝ) q ∩ Set.Icc 0 1 = Set.Ico 0 (1 / 2) := by
        ext z
        simp only [openHalfSpace, Set.mem_inter_iff, Set.mem_ofPred_eq, Real.inner_apply,
          Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, by nlinarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, h1, by linarith⟩
      rw [e, Real.volume_Ico]
      norm_num
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · have e : openHalfSpace (1 / 2 : ℝ) q ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
        ext z
        simp only [openHalfSpace, Set.mem_inter_iff, Set.mem_ofPred_eq, Real.inner_apply,
          Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨by nlinarith, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, by linarith, h2⟩
      rw [e, Real.volume_Ioc]
      norm_num
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
  · obtain ⟨z, hz, hzU⟩ := mem_closure_iff_nhds.1 hcl (Set.Ioo 0 1)
      (Ioo_mem_nhds (by norm_num) (by norm_num))
    rw [Measure.restrict_apply hU.measurableSet]
    have hpos : 0 < volume (U ∩ Set.Ioo 0 1) :=
      (hU.inter isOpen_Ioo).measure_pos volume ⟨z, hzU, hz⟩
    exact lt_of_lt_of_le hpos
      (measure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self))
  · have : y = false := by simpa using hy
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte, Real.inner_apply]
    norm_num

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Majority voting in the plane: finitely many types of Euclidean voters

MWG, Exercise 21.D.13, p. 815.

The plane `ℝ²` is modelled by `ℂ` with its real inner product (an isometric copy of the
Euclidean plane). A continuum of agents with Euclidean preferences falls into `J` types with
peaks `xⱼ` and masses `αⱼ ≥ 0`. `y` is a Condorcet winner if for every `z` the mass preferring
`z` to `y` is at most the mass preferring `y` to `z`.

The key lemma (`condorcet_halfplane`): if `y` is a Condorcet winner then for every direction
`w ≠ 0` the mass of types with `⟪xⱼ - y, w⟫ > 0` is at most the mass of the others (move from
`y` by a small step in direction `w`).

(a) With `J` odd and equal masses, a Condorcet winner is a peak (general position is not
needed); for `J` even this fails (`exercise_21_D_13a_even`). (b) (De Marzo) With a dominant type
and peaks in general position, the only possible Condorcet winner is the dominant type's peak.
-/

namespace MWG.SocialChoice

open Finset Filter Topology

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The mass of the types preferring `y` to `z` (`xⱼ` closer to `y` than to `z`). -/
noncomputable def typeMass {J : ℕ} (x : Fin J → ℂ) (α : Fin J → ℝ) (y z : ℂ) : ℝ :=
  ∑ j ∈ univ.filter (fun j => ‖x j - y‖ < ‖x j - z‖), α j

/-- **Exercise 21.D.13** (MWG, p. 815). `y` is a Condorcet winning alternative. -/
def IsTypeCondorcetWinner {J : ℕ} (x : Fin J → ℂ) (α : Fin J → ℝ) (y : ℂ) : Prop :=
  ∀ z, typeMass x α z y ≤ typeMass x α y z

/-- A small step from `y` in a direction `w ≠ 0` attracts exactly the types with
`⟪xⱼ - y, w⟫ > 0`. -/
theorem eventually_small_step {J : ℕ} (x : Fin J → ℂ) (y w : ℂ) (hw : w ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, (‖x j - (y + ε • w)‖ < ‖x j - y‖ ↔ 0 < ⟪x j - y, w⟫) ∧
      (‖x j - y‖ < ‖x j - (y + ε • w)‖ ↔ ⟪x j - y, w⟫ ≤ 0) := by
  rw [eventually_all]
  intro j
  set v := x j - y
  set c := ⟪v, w⟫
  have hw2 : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have key : ∀ ε : ℝ, ‖x j - (y + ε • w)‖ ^ 2 = ‖v‖ ^ 2 - 2 * ε * c + ε ^ 2 * ‖w‖ ^ 2 := by
    intro ε
    have : x j - (y + ε • w) = v - ε • w := by simp only [v]; abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have sqlt : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a < b ↔ a ^ 2 < b ^ 2) := fun a b ha hb =>
    ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  by_cases hc : 0 < c
  · filter_upwards [Ioo_mem_nhdsGT (div_pos (mul_pos two_pos hc) hw2)] with ε hε
    obtain ⟨h0, h1⟩ := hε
    rw [lt_div_iff₀ hw2] at h1
    rw [sqlt _ _ (norm_nonneg _) (norm_nonneg _), sqlt _ _ (norm_nonneg _) (norm_nonneg _),
      key]
    constructor
    · exact iff_of_true (by nlinarith) hc
    · exact iff_of_false (by nlinarith) (not_le.2 hc)
  · push Not at hc
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h0 : (0 : ℝ) < ε := hε
    rw [sqlt _ _ (norm_nonneg _) (norm_nonneg _), sqlt _ _ (norm_nonneg _) (norm_nonneg _),
      key]
    have hpos : 0 < ε ^ 2 * ‖w‖ ^ 2 := mul_pos (pow_pos h0 2) hw2
    have hnn : 0 ≤ ε * -c := mul_nonneg h0.le (neg_nonneg.2 hc)
    constructor
    · exact iff_of_false (by nlinarith) (not_lt.2 hc)
    · exact iff_of_true (by nlinarith) hc

/-- **Exercise 21.D.13**, key lemma. If `y` is a Condorcet winner, then for every direction
`w ≠ 0` the mass of types with `⟪xⱼ - y, w⟫ > 0` is at most the mass of the remaining types. -/
theorem condorcet_halfplane {J : ℕ} {x : Fin J → ℂ} {α : Fin J → ℝ} {y : ℂ}
    (hy : IsTypeCondorcetWinner x α y) (w : ℂ) (hw : w ≠ 0) :
    ∑ j ∈ univ.filter (fun j => 0 < ⟪x j - y, w⟫), α j ≤
      ∑ j ∈ univ.filter (fun j => ⟪x j - y, w⟫ ≤ 0), α j := by
  obtain ⟨ε, hε⟩ := (eventually_small_step x y w hw).exists
  have h := hy (y + ε • w)
  unfold typeMass at h
  have e1 : (univ.filter fun j => ‖x j - (y + ε • w)‖ < ‖x j - y‖) =
      univ.filter fun j => 0 < ⟪x j - y, w⟫ := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact (hε j).1
  have e2 : (univ.filter fun j => ‖x j - y‖ < ‖x j - (y + ε • w)‖) =
      univ.filter fun j => ⟪x j - y, w⟫ ≤ 0 := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact (hε j).2
  rwa [e1, e2] at h

/-- The real inner product on `ℂ` in coordinates. -/
theorem complex_inner_eq (v w : ℂ) : ⟪v, w⟫ = v.re * w.re + v.im * w.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Finitely many nonzero vectors of the plane admit a direction `w ≠ 0` orthogonal to none of
them (one of `1 + kI`, `k = 0, …, J`, works). -/
theorem exists_generic_direction {J : ℕ} (v : Fin J → ℂ) (hv : ∀ j, v j ≠ 0) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ j, ⟪v j, w⟫ ≠ 0 := by
  by_contra hc
  push Not at hc
  have hk : ∀ k : Fin (J + 1), ∃ j, ⟪v j, 1 + (k : ℝ) * Complex.I⟫ = 0 := by
    intro k
    refine hc _ fun h0 => ?_
    have := congrArg Complex.re h0
    simp at this
  choose f hf using hk
  obtain ⟨k, k', hne, hkk⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have h1 := hf k
  have h2 := hf k'
  rw [hkk, complex_inner_eq] at h1
  rw [complex_inner_eq] at h2
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.one_im, Complex.mul_im, zero_add] at h1 h2
  have hk' : ((k : ℕ) : ℝ) ≠ ((k' : ℕ) : ℝ) := by
    intro e
    exact hne (Fin.ext (by exact_mod_cast e))
  have him : (v (f k')).im = 0 := by
    have : ((k : ℕ) - (k' : ℕ) : ℝ) * (v (f k')).im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hk'
    · exact h
  have hre : (v (f k')).re = 0 := by rw [him] at h2; linarith
  exact hv (f k') (Complex.ext hre him)

/-- **Exercise 21.D.13(a)** (MWG, p. 815). With an odd number `J` of types of equal mass, a
Condorcet winning alternative must be the peak of some type. (General position is not used.) -/
theorem exercise_21_D_13a {J : ℕ} (hJ : Odd J) (x : Fin J → ℂ) {a : ℝ} (ha : 0 < a) {y : ℂ}
    (hy : IsTypeCondorcetWinner x (fun _ => a) y) : ∃ j, y = x j := by
  by_contra hc
  push Not at hc
  obtain ⟨w, hw0, hw⟩ := exists_generic_direction (fun j => x j - y)
    fun j h => hc j (sub_eq_zero.1 h).symm
  have h1 := condorcet_halfplane hy w hw0
  have h2 := condorcet_halfplane hy (-w) (neg_ne_zero.2 hw0)
  simp only [sum_const, nsmul_eq_mul, inner_neg_right, neg_pos, neg_nonpos] at h1 h2
  have e1 : (univ.filter fun j => ⟪x j - y, w⟫ ≤ 0) = univ.filter fun j => ⟪x j - y, w⟫ < 0 := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => lt_of_le_of_ne h (hw j), le_of_lt⟩
  have e2 : (univ.filter fun j => 0 ≤ ⟪x j - y, w⟫) = univ.filter fun j => 0 < ⟪x j - y, w⟫ := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hw j)), le_of_lt⟩
  rw [e1] at h1
  rw [e2] at h2
  have c1 := le_of_mul_le_mul_right h1 ha
  have c2 := le_of_mul_le_mul_right h2 ha
  have heq : (univ.filter fun j => 0 < ⟪x j - y, w⟫).card =
      (univ.filter fun j => ⟪x j - y, w⟫ < 0).card := by exact_mod_cast le_antisymm c1 c2
  have hsplit : (univ.filter fun j => 0 < ⟪x j - y, w⟫).card +
      (univ.filter fun j => ⟪x j - y, w⟫ < 0).card = J := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin J)))
      (fun j => 0 < ⟪x j - y, w⟫)
    have e : (univ.filter fun j => ¬0 < ⟪x j - y, w⟫) = univ.filter fun j => ⟪x j - y, w⟫ < 0 := by
      ext j
      simp only [mem_filter, mem_univ, true_and, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h (hw j), le_of_lt⟩
    rw [e, card_univ, Fintype.card_fin] at this
    exact this
  obtain ⟨m, hm⟩ := hJ
  omega

/-- **Exercise 21.D.13(a)**, even `J` (MWG, p. 815). The conclusion fails for an even number of
types: with two types of mass `1/2` at `0` and `1`, the midpoint `1/2` is a Condorcet winner but
not a peak. -/
theorem exercise_21_D_13a_even :
    IsTypeCondorcetWinner ![(0 : ℂ), 1] (fun _ => 1 / 2) (1 / 2) ∧
      ∀ j, (1 / 2 : ℂ) ≠ ![(0 : ℂ), 1] j := by
  refine ⟨fun z => ?_, fun j => ?_⟩
  · unfold typeMass
    simp only [sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : ‖(0 : ℂ) - 1 / 2‖ = 1 / 2 := by norm_num
    have h1 : ‖(1 : ℂ) - 1 / 2‖ = 1 / 2 := by norm_num
    have tri : ‖(0 : ℂ) - z‖ + ‖(1 : ℂ) - z‖ ≥ 1 := by
      have := norm_sub_le ((1 : ℂ) - z) ((0 : ℂ) - z)
      simp only [sub_sub_sub_cancel_right, sub_zero, norm_one] at this
      linarith
    by_cases hA : ‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 1 / 2‖ <;>
      by_cases hB : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 1 / 2‖ <;>
      by_cases hC : ‖(0 : ℂ) - 1 / 2‖ < ‖(0 : ℂ) - z‖ <;>
      by_cases hD : ‖(1 : ℂ) - 1 / 2‖ < ‖(1 : ℂ) - z‖ <;>
      simp only [hA, hB, hC, hD, ↓reduceIte] <;> linarith
  · fin_cases j
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this

/-- `⟪a, I b⟫ = Im(a b̄)`, the (signed) area spanned by `a` and `b`; zero iff `a, b` are
collinear with `0`. -/
theorem inner_I_mul (a b : ℂ) : ⟪a, Complex.I * b⟫ = a.im * b.re - a.re * b.im := by
  rw [complex_inner_eq]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    Complex.mul_im]
  ring

/-- Two vectors orthogonal to `I u` (i.e. on the line `ℝu`, `u ≠ 0`) are collinear. -/
theorem collinear_of_orth {u a b : ℂ} (hu : u ≠ 0) (ha : ⟪a, Complex.I * u⟫ = 0)
    (hb : ⟪b, Complex.I * u⟫ = 0) : ⟪a, Complex.I * b⟫ = 0 := by
  rw [inner_I_mul] at ha hb ⊢
  have h1 : (a.im * b.re - a.re * b.im) * u.re = 0 := by linear_combination b.re * ha - a.re * hb
  have h2 : (a.im * b.re - a.re * b.im) * u.im = 0 := by linear_combination b.im * ha - a.im * hb
  by_contra hne
  have hre : u.re = 0 := (mul_eq_zero.1 h1).resolve_left hne
  have him : u.im = 0 := (mul_eq_zero.1 h2).resolve_left hne
  exact hu (Complex.ext hre him)

/-- **Exercise 21.D.13(b)** (MWG, p. 815). Peaks are in general position: no three peaks of
distinct types lie on a line. -/
def GeneralPosition {J : ℕ} (x : Fin J → ℂ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⟪x j - x i, Complex.I * (x k - x i)⟫ ≠ 0

/-- **Exercise 21.D.13(b) (De Marzo)** (MWG, p. 815). With peaks in general position, masses
`αⱼ ≥ 0` summing to one and a dominant type `h` (`αₕ > αⱼ` for `j ≠ h`), a Condorcet winning
alternative can only be the dominant type's peak. -/
theorem exercise_21_D_13b {J : ℕ} {x : Fin J → ℂ} {α : Fin J → ℝ} (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j, α j = 1) (hgp : GeneralPosition x) {h : Fin J}
    (hdom : ∀ j, j ≠ h → α j < α h) {y : ℂ} (hy : IsTypeCondorcetWinner x α y) : y = x h := by
  classical
  by_contra hne
  set u := x h - y with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set n := Complex.I * u with hn
  have hun : ⟪u, n⟫ = 0 := by rw [hn, inner_I_mul]; ring
  have huu : 0 < ⟪u, u⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 hu0) 2
  have hαh : 0 < α h := by
    have : ∑ j, α j ≤ ∑ _j : Fin J, α h := sum_le_sum fun j _ => by
      by_cases hj : j = h
      · rw [hj]
      · exact (hdom j hj).le
    rw [hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    by_contra hc
    push Not at hc
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  set v : Fin J → ℂ := fun j => x j - y with hv
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, ⟪v j, n⟫ ≠ 0 →
      |δ * ⟪v j, u⟫| < |⟪v j, n⟫| := by
    rw [eventually_all]
    intro j
    by_cases hc : ⟪v j, n⟫ = 0
    · exact Eventually.of_forall fun _ h' => absurd hc h'
    · have hcpos : 0 < |⟪v j, n⟫| := abs_pos.2 hc
      filter_upwards [Ioo_mem_nhdsGT (div_pos hcpos (by positivity :
        (0 : ℝ) < |⟪v j, u⟫| + 1))] with δ hδ _
      obtain ⟨h0, h1⟩ := hδ
      rw [lt_div_iff₀ (by positivity)] at h1
      rw [abs_mul, abs_of_pos h0]
      nlinarith [abs_nonneg ⟪v j, u⟫]
  obtain ⟨δ, hδ, hδpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδpos
  set wp := n + δ • u
  set wm := -n + δ • u
  have hwp : wp ≠ 0 := by
    intro h0
    have : ⟪u, wp⟫ = 0 := by rw [h0, inner_zero_right]
    rw [inner_add_right, hun, inner_smul_right] at this
    nlinarith
  have hwm : wm ≠ 0 := by
    intro h0
    have : ⟪u, wm⟫ = 0 := by rw [h0, inner_zero_right]
    rw [inner_add_right, inner_neg_right, hun, inner_smul_right] at this
    nlinarith
  have c1 := condorcet_halfplane hy wp hwp
  have c2 := condorcet_halfplane hy wm hwm
  simp only [sum_filter] at c1 c2
  have hsum2 := add_le_add c1 c2
  rw [← sum_add_distrib, ← sum_add_distrib] at hsum2
  set Lp := univ.filter fun j => ⟪v j, n⟫ = 0 ∧ 0 < ⟪v j, u⟫
  set Lr := univ.filter fun j => ⟪v j, n⟫ = 0 ∧ ⟪v j, u⟫ ≤ 0
  have hpoint : ∀ j, ((if 0 < ⟪x j - y, wp⟫ then α j else 0) +
      (if 0 < ⟪x j - y, wm⟫ then α j else 0)) - ((if ⟪x j - y, wp⟫ ≤ 0 then α j else 0) +
      (if ⟪x j - y, wm⟫ ≤ 0 then α j else 0)) =
      2 * (if j ∈ Lp then α j else 0) - 2 * (if j ∈ Lr then α j else 0) := by
    intro j
    have ep : ⟪x j - y, wp⟫ = ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by
      simp only [wp, inner_add_right, inner_smul_right, v]
    have em : ⟪x j - y, wm⟫ = -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by
      simp only [wm, inner_add_right, inner_neg_right, inner_smul_right, v]
    rw [ep, em]
    simp only [Lp, Lr, mem_filter, mem_univ, true_and]
    by_cases hc : ⟪v j, n⟫ = 0
    · rw [hc]
      by_cases hd : 0 < ⟪v j, u⟫
      · have : 0 < δ * ⟪v j, u⟫ := mul_pos hδ0 hd
        simp only [zero_add, neg_zero, true_and, hd, this, not_le.2 this, not_le.2 hd,
          ↓reduceIte]
        ring
      · push Not at hd
        have : δ * ⟪v j, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ0.le hd
        simp only [zero_add, neg_zero, true_and, not_lt.2 hd, not_lt.2 this, this, hd,
          ↓reduceIte]
        ring
    · have hb := hδ j hc
      rw [abs_lt] at hb
      simp only [hc, false_and, ↓reduceIte, mul_zero, sub_zero]
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [abs_of_neg hlt] at hb
        have a1 : ¬0 < ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        have a2 : 0 < -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        simp only [a1, a2, not_lt.1 a1, not_le.2 a2, ↓reduceIte]
        ring
      · rw [abs_of_pos hgt] at hb
        have a1 : 0 < ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        have a2 : ¬0 < -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        simp only [a1, a2, not_lt.1 a2, not_le.2 a1, ↓reduceIte]
        ring
  have hLpLr : ∑ j ∈ Lp, α j ≤ ∑ j ∈ Lr, α j := by
    have hdiff : ∑ j, (((if 0 < ⟪x j - y, wp⟫ then α j else 0) +
        (if 0 < ⟪x j - y, wm⟫ then α j else 0)) - ((if ⟪x j - y, wp⟫ ≤ 0 then α j else 0) +
        (if ⟪x j - y, wm⟫ ≤ 0 then α j else 0))) ≤ 0 := by
      rw [sum_sub_distrib]
      linarith
    simp only [hpoint] at hdiff
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_ite_mem, sum_ite_mem, univ_inter,
      univ_inter] at hdiff
    linarith
  have hhLp : h ∈ Lp := by
    simp only [Lp, mem_filter, mem_univ, true_and]
    exact ⟨hun, huu⟩
  have hLp_ge : α h ≤ ∑ j ∈ Lp, α j := single_le_sum (fun j _ => hα j) hhLp
  have hLr_sub : ∀ j ∈ Lr, ∀ k ∈ Lr, j = k := by
    intro j hj k hk
    simp only [Lr, mem_filter, mem_univ, true_and] at hj hk
    by_contra hjk
    have hjh : j ≠ h := fun e => by rw [e] at hj; linarith [hj.2]
    have hkh : k ≠ h := fun e => by rw [e] at hk; linarith [hk.2]
    apply hgp h j k (Ne.symm hjh) (Ne.symm hkh) hjk
    have hj' : ⟪x j - x h, n⟫ = 0 := by
      have : x j - x h = v j - u := by simp only [v, hu]; abel
      rw [this, inner_sub_left, hj.1, hun, sub_zero]
    have hk' : ⟪x k - x h, n⟫ = 0 := by
      have : x k - x h = v k - u := by simp only [v, hu]; abel
      rw [this, inner_sub_left, hk.1, hun, sub_zero]
    exact collinear_of_orth hu0 hj' hk'
  rcases Lr.eq_empty_or_nonempty with he | ⟨k, hk⟩
  · rw [he, sum_empty] at hLpLr
    linarith
  · have hsub : Lr ⊆ {k} := fun j hj => mem_singleton.2 (hLr_sub j hj k hk)
    have hkh : k ≠ h := by
      intro e
      simp only [Lr, mem_filter, mem_univ, true_and] at hk
      rw [e] at hk
      linarith [hk.2]
    have := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hα j
    rw [sum_singleton] at this
    linarith [hdom k hkh]

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Condorcet cycles near a point where the gradients span the plane

MWG, Exercises 21.D.7 and 21.D.8, p. 813.

Three agents have utilities `uᵢ` on a set `X ⊆ ℝ²` (modelled by `ℂ`) containing a neighbourhood
of the origin, differentiable at the origin with gradients `gᵢ` (MWG assumes `X` convex and
the `uᵢ` continuously differentiable; we only use differentiability at `0`). If the cone spanned
by the gradients is the whole plane then (a) there is a Condorcet cycle `x, y, z ∈ X`, and (b)
for every `x ≠ 0` there is `y ∈ X` with `‖x - y‖ < ‖x‖` preferred to the origin by two agents
(without the hint's linearity assumption).

The construction: the cone condition gives `λ ≫ 0` with `∑ λᵢ gᵢ = 0`, so the signed areas
`D(g₀, g₁)`, `D(g₁, g₂)`, `D(g₂, g₀)` are nonzero with a common sign `σ`; the directions
`d₀ = σ I (g₂ - g₁)`, `d₁ = σ I (g₀ - g₂)`, `d₂ = σ I (g₁ - g₀)` sum to zero and each makes
exactly the two agents other than `k` better off to first order.

**Correction.** In (b) the point `x` must be nonzero: for `x = 0` no `y` satisfies
`‖x - y‖ < ‖x‖`.

Exercise 21.D.8: we prove part (c) for linear utilities (a directional median agent, which for
linear utilities is the same at every point, rules out Condorcet cycles). Parts (a) (existence
of a directional median for a pointed gradient cone) and (b) (an example with a changing median
and a Condorcet cycle), and (c) for the literal notion, are in `DirectionalMedian`.
-/

namespace MWG.SocialChoice

open Finset Filter Topology

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Two of the three agents strictly prefer `a` to `b`: a strict majority. -/
def TwoAgentsPrefer (u : Fin 3 → ℂ → ℝ) (a b : ℂ) : Prop :=
  ∃ i j, i ≠ j ∧ u i b < u i a ∧ u j b < u j a

/-- First-order comparison: if `u` has gradient `g` at `0` and `⟪g, a - b⟫ > 0`, then
`u(ta) > u(tb)` for all small `t > 0`. -/
theorem eventually_gradient_lt {f : ℂ → ℝ} {g : ℂ} (hf : HasGradientAt f g 0) {a b : ℂ}
    (hab : 0 < ⟪g, a - b⟫) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f ((t : ℝ) • b) < f ((t : ℝ) • a) := by
  have hF := hf.hasFDerivAt
  have hpath : ∀ c : ℂ, HasDerivAt (fun t : ℝ => f (t • c)) ⟪g, c⟫ 0 := by
    intro c
    have hγ : HasDerivAt (fun t : ℝ => t • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const c
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hF hγ (zero_smul ℝ c).symm
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
  have hφ : HasDerivAt (fun t : ℝ => f (t • a) - f (t • b)) ⟪g, a - b⟫ 0 := by
    rw [inner_sub_right]
    exact (hpath a).sub (hpath b)
  have hslope := hasDerivAt_iff_tendsto_slope.1 hφ
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope (fun t : ℝ => f (t • a) - f (t • b)) 0 t :=
    hslope.eventually (lt_mem_nhds hab)
  have hpos' := (hpos.filter_mono (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).and
    self_mem_nhdsWithin
  filter_upwards [hpos'] with t ht
  obtain ⟨h1, h2⟩ := ht
  have h2' : (0 : ℝ) < t := h2
  rw [slope_def_field] at h1
  simp only [zero_smul, sub_self, sub_zero] at h1
  have := (div_pos_iff_of_pos_right h2').1 h1
  linarith

/-- The signed area `D(a, b) = ⟪a, I b⟫`. -/
theorem area_antisymm (a b : ℂ) : ⟪a, Complex.I * b⟫ = -⟪b, Complex.I * a⟫ := by
  rw [inner_I_mul, inner_I_mul]
  ring

/-- `D(a, a) = 0`. -/
theorem area_self (a : ℂ) : ⟪a, Complex.I * a⟫ = 0 := by
  rw [inner_I_mul]
  ring

/-- The structure of three gradients whose cone is the plane: three directions summing to
zero, each improving (to first order) exactly the two agents other than its index, and such that
every nonzero vector makes a positive inner product with one of them. -/
theorem cone_directions {g : Fin 3 → ℂ}
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) :
    ∃ d0 d1 d2 : ℂ, d0 + d1 + d2 = 0 ∧ 0 < ⟪g 1, d0⟫ ∧ 0 < ⟪g 2, d0⟫ ∧ 0 < ⟪g 0, d1⟫ ∧
      0 < ⟪g 2, d1⟫ ∧ 0 < ⟪g 0, d2⟫ ∧ 0 < ⟪g 1, d2⟫ ∧
      ∀ x : ℂ, x ≠ 0 → 0 < ⟪x, d0⟫ ∨ 0 < ⟪x, d1⟫ ∨ 0 < ⟪x, d2⟫ := by
  obtain ⟨μ, hμ, hv⟩ := hcone (-(g 0 + g 1 + g 2))
  simp only [Fin.sum_univ_three] at hv
  set l : Fin 3 → ℝ := fun i => μ i + 1
  have hl : ∀ i, 0 < l i := fun i => by simp only [l]; linarith [hμ i]
  have hsum : l 0 • g 0 + l 1 • g 1 + l 2 • g 2 = 0 := by
    simp only [l, add_smul, one_smul]
    rw [show μ 0 • g 0 + g 0 + (μ 1 • g 1 + g 1) + (μ 2 • g 2 + g 2) =
      (μ 0 • g 0 + μ 1 • g 1 + μ 2 • g 2) + (g 0 + g 1 + g 2) by abel, ← hv]
    abel
  set D : ℂ → ℂ → ℝ := fun a b => ⟪a, Complex.I * b⟫ with hD
  have Dlin : ∀ c, l 0 * D (g 0) c + l 1 * D (g 1) c + l 2 * D (g 2) c = 0 := by
    intro c
    have : D (l 0 • g 0 + l 1 • g 1 + l 2 • g 2) c = 0 := by
      rw [hsum]
      simp only [hD, inner_zero_left]
    simpa only [hD, inner_add_left, real_inner_smul_left] using this
  have Danti : ∀ a b, D a b = -D b a := area_antisymm
  have Dself : ∀ a, D a a = 0 := area_self
  set σ := D (g 0) (g 1) with hσdef
  have e0 := Dlin (g 0)
  have e1 := Dlin (g 1)
  rw [Dself, Danti (g 1) (g 0)] at e0
  rw [Dself] at e1
  have hD20 : D (g 2) (g 0) = l 1 * σ / l 2 := by
    field_simp [(hl 2).ne']
    linarith
  have hD21 : D (g 2) (g 1) = -(l 0 * σ / l 2) := by
    field_simp [(hl 2).ne']
    linarith
  have hD02 : D (g 0) (g 2) = -(l 1 * σ / l 2) := by rw [Danti, hD20]
  have hD12 : D (g 1) (g 2) = l 0 * σ / l 2 := by rw [Danti, hD21, neg_neg]
  have hD10 : D (g 1) (g 0) = -σ := by rw [Danti]
  have hσ : σ ≠ 0 := by
    intro hσ0
    have z : ∀ k i, D (g k) (g i) = 0 := by
      intro k i
      fin_cases k <;> fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Dself, hD20, hD21,
          hD02, hD12, hD10, ← hσdef, hσ0, mul_zero, zero_div, neg_zero]
    by_cases hall : ∀ k, g k = 0
    · obtain ⟨μ', -, hv'⟩ := hcone 1
      simp only [hall, smul_zero, sum_const_zero] at hv'
      exact one_ne_zero hv'
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      obtain ⟨μ', -, hv'⟩ := hcone (Complex.I * g k)
      have h1 : D (g k) (Complex.I * g k) = 0 := by
        rw [hv']
        have e : ∀ i, ⟪g k, Complex.I * (μ' i • g i)⟫ = μ' i * D (g k) (g i) := fun i => by
          rw [mul_smul_comm, inner_smul_right]
        have z' : ∀ i, ⟪g k, Complex.I * g i⟫ = 0 := fun i => z k i
        simp only [hD, Fin.sum_univ_three, mul_add, inner_add_right, e]
        rw [z' 0, z' 1, z' 2]
        ring
      have h2 : D (g k) (Complex.I * g k) = -‖g k‖ ^ 2 := by
        simp only [hD, ← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right,
          real_inner_self_eq_norm_sq]
      rw [h2] at h1
      have : ‖g k‖ = 0 := by nlinarith [norm_nonneg (g k)]
      exact hk (norm_eq_zero.1 this)
  have key : ∀ i c c' : ℂ, ⟪i, σ • (Complex.I * (c - c'))⟫ = σ * (D i c - D i c') := by
    intro i c c'
    simp only [hD, inner_smul_right, mul_sub, inner_sub_right]
  have p1 : 0 < σ * σ := mul_self_pos.2 hσ
  have pa : 0 < σ * (l 1 * σ / l 2) := by
    have : σ * (l 1 * σ / l 2) = l 1 * (σ * σ) / l 2 := by ring
    rw [this]
    exact div_pos (mul_pos (hl 1) p1) (hl 2)
  have pb : 0 < σ * (l 0 * σ / l 2) := by
    have : σ * (l 0 * σ / l 2) = l 0 * (σ * σ) / l 2 := by ring
    rw [this]
    exact div_pos (mul_pos (hl 0) p1) (hl 2)
  refine ⟨σ • (Complex.I * (g 2 - g 1)), σ • (Complex.I * (g 0 - g 2)),
    σ • (Complex.I * (g 1 - g 0)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add, ← smul_add, ← mul_add, ← mul_add]
    simp
  · rw [key, hD12, Dself]; linarith
  · rw [key, Dself, hD21]; linarith
  · rw [key, Dself, hD02]; linarith
  · rw [key, hD20, Dself]; linarith
  · rw [key, ← hσdef, Dself]; linarith
  · rw [key, Dself, hD10]; linarith
  · intro x hx
    by_contra hc
    push Not at hc
    obtain ⟨c0, c1, c2⟩ := hc
    have hsum0 : ⟪x, σ • (Complex.I * (g 2 - g 1))⟫ + ⟪x, σ • (Complex.I * (g 0 - g 2))⟫ +
        ⟪x, σ • (Complex.I * (g 1 - g 0))⟫ = 0 := by
      rw [← inner_add_right, ← inner_add_right, ← smul_add, ← smul_add, ← mul_add, ← mul_add]
      simp
    have z0 : ⟪x, σ • (Complex.I * (g 2 - g 1))⟫ = 0 := by linarith
    have z1 : ⟪x, σ • (Complex.I * (g 0 - g 2))⟫ = 0 := by linarith
    have hIx : Complex.I * x ≠ 0 := mul_ne_zero Complex.I_ne_zero hx
    have o0 : ⟪σ • (Complex.I * (g 2 - g 1)), Complex.I * (Complex.I * x)⟫ = 0 := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right, real_inner_comm, z0,
        neg_zero]
    have o1 : ⟪σ • (Complex.I * (g 0 - g 2)), Complex.I * (Complex.I * x)⟫ = 0 := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right, real_inner_comm, z1,
        neg_zero]
    have hc := collinear_of_orth hIx o0 o1
    have hval : ⟪σ • (Complex.I * (g 2 - g 1)), Complex.I * (σ • (Complex.I * (g 0 - g 2)))⟫ =
        σ * σ * (D (g 2) (g 0) - D (g 2) (g 2) - D (g 1) (g 0) + D (g 1) (g 2)) := by
      simp only [hD, inner_I_mul, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
        Complex.sub_im]
      ring
    rw [hval, hD20, Dself, hD10, hD12] at hc
    have : 0 < σ * σ * (l 1 * σ / l 2 - 0 - -σ + l 0 * σ / l 2) * σ := by
      have : σ * σ * (l 1 * σ / l 2 - 0 - -σ + l 0 * σ / l 2) * σ =
          (σ * σ) * ((l 1 * (σ * σ) / l 2) + σ * σ + (l 0 * (σ * σ) / l 2)) := by ring
      rw [this]
      exact mul_pos p1 (add_pos (add_pos (div_pos (mul_pos (hl 1) p1) (hl 2)) p1)
        (div_pos (mul_pos (hl 0) p1) (hl 2)))
    rw [hc, zero_mul] at this
    exact lt_irrefl _ this

/-- **Exercise 21.D.7(a)** (MWG, p. 813). If three utilities are differentiable at the origin,
an interior point of `X`, with gradients whose cone is `ℝ²`, then there are `x, y, z ∈ X` forming
a Condorcet cycle: a strict majority prefers `x` to `y`, `y` to `z`, and `z` to `x`. -/
theorem exercise_21_D_7a {X : Set ℂ} (hX : X ∈ 𝓝 (0 : ℂ)) {u : Fin 3 → ℂ → ℝ} {g : Fin 3 → ℂ}
    (hu : ∀ i, HasGradientAt (u i) (g i) 0)
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ z ∈ X, TwoAgentsPrefer u x y ∧ TwoAgentsPrefer u y z ∧
      TwoAgentsPrefer u z x := by
  obtain ⟨d0, d1, d2, hs, a10, a20, a01, a21, a02, a12, -⟩ := cone_directions hcone
  have hy : (-d0) = d1 + d2 := by linear_combination (-1 : ℂ) * hs
  have tend : ∀ c : ℂ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (t : ℝ) • c ∈ X := fun c => by
    have : Tendsto (fun t : ℝ => t • c) (𝓝[>] 0) (𝓝 0) := by
      exact ((continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds
    exact this hX
  have i1 : 0 < ⟪g 1, (0 : ℂ) - -d0⟫ := by simpa using a10
  have i2 : 0 < ⟪g 2, (0 : ℂ) - -d0⟫ := by simpa using a20
  have j0 : 0 < ⟪g 0, -d0 - d2⟫ := by rw [hy]; simpa using a01
  have j2 : 0 < ⟪g 2, -d0 - d2⟫ := by rw [hy]; simpa using a21
  have k0 : 0 < ⟪g 0, d2 - 0⟫ := by simpa using a02
  have k1 : 0 < ⟪g 1, d2 - 0⟫ := by simpa using a12
  obtain ⟨t, ht⟩ := ((eventually_gradient_lt (hu 1) i1).and ((eventually_gradient_lt (hu 2) i2).and
    ((eventually_gradient_lt (hu 0) j0).and ((eventually_gradient_lt (hu 2) j2).and
    ((eventually_gradient_lt (hu 0) k0).and ((eventually_gradient_lt (hu 1) k1).and
    ((tend 0).and ((tend (-d0)).and (tend d2))))))))).exists
  obtain ⟨b1, b2, b3, b4, b5, b6, m1, m2, m3⟩ := ht
  refine ⟨t • 0, m1, t • (-d0), m2, t • d2, m3, ⟨1, 2, by decide, b1, b2⟩,
    ⟨0, 2, by decide, b3, b4⟩, ⟨0, 1, by decide, b5, b6⟩⟩

/-- **Exercise 21.D.7(b)** (MWG, p. 813), for `x ≠ 0` (correction: for `x = 0` no `y` has
`‖x - y‖ < ‖x‖`). Under the hypotheses of (a), for every `x ≠ 0` there is `y ∈ X` with
`‖x - y‖ < ‖x‖` that two agents prefer to the origin (the status quo). No linearity is
assumed. -/
theorem exercise_21_D_7b {X : Set ℂ} (hX : X ∈ 𝓝 (0 : ℂ)) {u : Fin 3 → ℂ → ℝ} {g : Fin 3 → ℂ}
    (hu : ∀ i, HasGradientAt (u i) (g i) 0)
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) {x : ℂ}
    (hx : x ≠ 0) : ∃ y ∈ X, ‖x - y‖ < ‖x‖ ∧ TwoAgentsPrefer u y 0 := by
  obtain ⟨d0, d1, d2, -, a10, a20, a01, a21, a02, a12, hpos⟩ := cone_directions hcone
  have tend : ∀ c : ℂ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (t : ℝ) • c ∈ X := fun c => by
    have : Tendsto (fun t : ℝ => t • c) (𝓝[>] 0) (𝓝 0) := by
      exact ((continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds
    exact this hX
  have closer : ∀ d : ℂ, 0 < ⟪x, d⟫ → ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖x - (t : ℝ) • d‖ < ‖x‖ := by
    intro d hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have hn : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hd0) 2
    filter_upwards [Ioo_mem_nhdsGT (div_pos (mul_pos two_pos hd) hn)] with t ht
    obtain ⟨h0, h1⟩ := ht
    rw [lt_div_iff₀ hn] at h1
    have e : ‖x - t • d‖ ^ 2 = ‖x‖ ^ 2 - 2 * t * ⟪x, d⟫ + t ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have : ‖x - t • d‖ ^ 2 < ‖x‖ ^ 2 := by rw [e]; nlinarith
    nlinarith [norm_nonneg (x - t • d), norm_nonneg x]
  have zero_smul' : ∀ t : ℝ, (t • (0 : ℂ)) = 0 := fun t => smul_zero t
  rcases hpos x hx with h | h | h
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d0 h).and ((eventually_gradient_lt (hu 1)
      (b := 0) (by simpa using a10)).and ((eventually_gradient_lt (hu 2) (b := 0)
      (by simpa using a20)).and (tend d0)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d0, h4, h1, 1, 2, by decide, h2, h3⟩
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d1 h).and ((eventually_gradient_lt (hu 0)
      (b := 0) (by simpa using a01)).and ((eventually_gradient_lt (hu 2) (b := 0)
      (by simpa using a21)).and (tend d1)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d1, h4, h1, 0, 2, by decide, h2, h3⟩
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d2 h).and ((eventually_gradient_lt (hu 0)
      (b := 0) (by simpa using a02)).and ((eventually_gradient_lt (hu 1) (b := 0)
      (by simpa using a12)).and (tend d2)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d2, h4, h1, 0, 1, by decide, h2, h3⟩

/-- **Exercise 21.D.7(b)**, correction. For `x = 0` the requirement `‖x - y‖ < ‖x‖` is
impossible. -/
theorem exercise_21_D_7b_zero (y : ℂ) : ¬‖(0 : ℂ) - y‖ < ‖(0 : ℂ)‖ := by
  simp only [norm_zero, not_lt]
  exact norm_nonneg _

/-- **Exercise 21.D.8(a)** (MWG, p. 813), the property, for linear utilities `uᵢ(v) = ⟪gᵢ, v⟫`:
agent `h` is a directional median: every move having a strict majority makes `h` strictly
better off. -/
def IsDirectionalMedian (g : Fin 3 → ℂ) (h : Fin 3) : Prop :=
  ∀ d : ℂ, (∃ i j, i ≠ j ∧ 0 < ⟪g i, d⟫ ∧ 0 < ⟪g j, d⟫) → 0 < ⟪g h, d⟫

/-- **Exercise 21.D.8(c)** (MWG, p. 813), linear case. If, with linear utilities, some agent is
a directional median (necessarily the same at every point), there is no Condorcet cycle. -/
theorem exercise_21_D_8c {g : Fin 3 → ℂ} {h : Fin 3} (hh : IsDirectionalMedian g h)
    (x y z : ℂ) :
    ¬(TwoAgentsPrefer (fun i v => ⟪g i, v⟫) x y ∧ TwoAgentsPrefer (fun i v => ⟪g i, v⟫) y z ∧
      TwoAgentsPrefer (fun i v => ⟪g i, v⟫) z x) := by
  rintro ⟨⟨i1, j1, h1, a1, b1⟩, ⟨i2, j2, h2, a2, b2⟩, ⟨i3, j3, h3, a3, b3⟩⟩
  have c1 := hh (x - y) ⟨i1, j1, h1, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  have c2 := hh (y - z) ⟨i2, j2, h2, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  have c3 := hh (z - x) ⟨i3, j3, h3, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  rw [inner_sub_right] at c1 c2 c3
  linarith

/-- **Exercise 21.D.8(c)**, instance. With gradients `1, 1, I` (a pointed cone), agent `0` is a
directional median. -/
theorem exercise_21_D_8c_instance : IsDirectionalMedian ![1, 1, Complex.I] 0 := by
  rintro d ⟨i, j, hij, hi, hj⟩
  fin_cases i <;> fin_cases j <;> simp_all

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Instances of the hypotheses of the chapter's theorems

Concrete instances showing that the hypothesis sets of Proposition 21.D.1, Example 21.D.6,
Exercise 21.D.7 and Exercise 21.D.13 are satisfiable (the other results carry their instances
next to them: `proposition_21_C_1_nonvacuous`, `dictatorial_strict_spec`,
`smallestTopLabel_noIncentive`, `exercise_21_C_2b`, `exercise_21_D_9e_instance`, the
Exercise 21.D.10 applications of Example 21.D.4 and Proposition 21.D.1, and so on).
-/

namespace MWG.SocialChoice

open Finset MeasureTheory

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Proposition 21.D.1**, instance. Three agents on `{0, 1, 2}` with peaks `0, 2, 2`; agent 1
(peak `2`) is a median agent, so `2` is the Condorcet winner. -/
theorem proposition_21_D_1_instance :
    let p : Profile (Fin 3) (Fin 3) := fun i => natPref (![![2, 1, 0], ![0, 1, 2], ![0, 1, 2]] i)
    (∀ i, IsPeak (p i) (![0, 2, 2] i)) ∧ IsMedianAgent (![0, 2, 2] : Fin 3 → Fin 3) 1 ∧
      IsCondorcetWinner p 2 := by
  intro p
  have hpk : ∀ i, IsPeak (p i) (![0, 2, 2] i) := by
    intro i
    simp only [IsPeak, p, natPref_strict_iff]
    fin_cases i <;> decide
  have hmed : IsMedianAgent (![0, 2, 2] : Fin 3 → Fin 3) 1 := by
    unfold IsMedianAgent
    decide
  exact ⟨hpk, hmed, (proposition_21_D_1 hpk hmed).1⟩

/-- **Example 21.D.6**, instance. The point mass at `x` has `x` as a median, hence as a Condorcet
winner. -/
theorem example_21_D_6_instance (x : ℂ) :
    IsMedianPoint (Measure.dirac x) x ∧ IsCondorcetWinnerMeasure (Measure.dirac x) x := by
  have hmed : IsMedianPoint (Measure.dirac x) x := by
    intro q _
    rw [Measure.dirac_apply' _ (measurableSet_openHalfSpace x q)]
    simp [openHalfSpace]
  exact ⟨hmed, (example_21_D_6 _ x).1 hmed⟩

/-- The linear utility `v ↦ ⟪g, v⟫` has gradient `g` at `0`. -/
theorem hasGradientAt_inner_const (g : ℂ) : HasGradientAt (fun v : ℂ => ⟪g, v⟫) g 0 := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (InnerProductSpace.toDual ℝ ℂ g : ℂ →L[ℝ] ℝ).hasFDerivAt (x := 0)
  convert h using 1
  funext v
  simp [InnerProductSpace.toDual_apply_apply]

/-- **Exercise 21.D.7**, instance. The linear utilities with gradients `1`, `I`, `-1 - I` on
`X = ℂ`: the cone of the gradients is the whole plane. -/
theorem exercise_21_D_7_instance :
    (∀ i, HasGradientAt (fun v : ℂ => ⟪![1, Complex.I, -1 - Complex.I] i, v⟫)
      (![1, Complex.I, -1 - Complex.I] i) 0) ∧
      ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧
        v = ∑ i, μ i • (![1, Complex.I, -1 - Complex.I] : Fin 3 → ℂ) i := by
  refine ⟨fun i => hasGradientAt_inner_const _, fun v => ?_⟩
  set M := |v.re| + |v.im|
  refine ⟨![v.re + M, v.im + M, M], fun i => ?_, ?_⟩
  · fin_cases i <;> simp [M] <;> linarith [neg_abs_le v.re, neg_abs_le v.im, abs_nonneg v.re,
      abs_nonneg v.im]
  · apply Complex.ext <;> simp [Fin.sum_univ_three, M] <;> ring

/-- **Exercise 21.D.13(a)**, instance. Three types of equal mass with collinear peaks `-1, 0, 1`:
the middle peak `0` is a Condorcet winner. -/
theorem exercise_21_D_13a_instance :
    IsTypeCondorcetWinner ![(-1 : ℂ), 0, 1] (fun _ => 1) 0 := by
  intro z
  unfold typeMass
  simp only [sum_filter, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have tri : ‖(-1 : ℂ) - z‖ + ‖(1 : ℂ) - z‖ ≥ 2 := by
    have := norm_sub_le ((1 : ℂ) - z) ((-1 : ℂ) - z)
    have e : (1 : ℂ) - z - (-1 - z) = 2 := by ring
    rw [e] at this
    simp only [Complex.norm_ofNat] at this
    linarith [norm_sub_rev ((-1 : ℂ) - z) 0]
  have h1 : ‖(-1 : ℂ) - 0‖ = 1 := by simp
  have h2 : ‖(1 : ℂ) - 0‖ = 1 := by simp
  have h0 : ‖(0 : ℂ) - 0‖ = 0 := by simp
  have hz := norm_nonneg ((0 : ℂ) - z)
  by_cases hA : ‖(-1 : ℂ) - z‖ < ‖(-1 : ℂ) - 0‖ <;>
    by_cases hB : ‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 0‖ <;>
    by_cases hC : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 0‖ <;>
    by_cases hA' : ‖(-1 : ℂ) - 0‖ < ‖(-1 : ℂ) - z‖ <;>
    by_cases hB' : ‖(0 : ℂ) - 0‖ < ‖(0 : ℂ) - z‖ <;>
    by_cases hC' : ‖(1 : ℂ) - 0‖ < ‖(1 : ℂ) - z‖ <;>
    simp only [hA, hB, hC, hA', hB', hC', ↓reduceIte] <;> linarith

/-- **Exercise 21.D.13(b)**, instance. Peaks `0, 1, I` (in general position), masses
`1/2, 1/4, 1/4`; the dominant type's peak `0` is a Condorcet winner. -/
theorem exercise_21_D_13b_instance :
    GeneralPosition ![(0 : ℂ), 1, Complex.I] ∧
      IsTypeCondorcetWinner ![(0 : ℂ), 1, Complex.I] ![1 / 2, 1 / 4, 1 / 4] 0 := by
  refine ⟨fun i j k hij hik hjk => ?_, fun z => ?_⟩
  · rw [inner_I_mul]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  · unfold typeMass
    simp only [sum_filter, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases hz : z = 0
    · subst hz
      simp
    · have hpos : 0 < ‖(0 : ℂ) - z‖ := by simpa using hz
      have hn : ¬‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 0‖ := by simp
      have hy : ‖(0 : ℂ) - 0‖ < ‖(0 : ℂ) - z‖ := by simpa using hpos
      simp only [hn, hy, ↓reduceIte]
      by_cases hA : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 0‖ <;>
        by_cases hB : ‖Complex.I - z‖ < ‖Complex.I - 0‖ <;>
        by_cases hA' : ‖(1 : ℂ) - 0‖ < ‖(1 : ℂ) - z‖ <;>
        by_cases hB' : ‖Complex.I - 0‖ < ‖Complex.I - z‖ <;>
        simp only [hA, hB, hA', hB', ↓reduceIte] <;> norm_num

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The uniform distribution on a triangle has no median

MWG, Example 21.D.6 and Figure 21.D.8(b), p. 806, and the nonexistence half of
Exercise 21.D.9(d), p. 814.

The median property is invariant under affine bijections: if `v + L x` is a median of the
uniform distribution on `v + L(S)`, then `x` is a median of the uniform distribution on `S`
(`isMedianPoint_of_affine_image`; the hyperplane with normal `q` through `x` is carried to the
one with normal `(L⁻¹)* q`, and Lebesgue measure is multiplied by `|det L|`). Every triangle
with nonempty interior is the image of the standard triangle
`{z : 0 < z₀, 0 < z₁, z₀ + z₁ < 1}` under such a map.

For the standard triangle, the line `z₀ = c` through a median must cut the triangle into two
pieces of area `1/4`: integrating, `(1 - c)² / 2 = 1/4` (`stdTriangle_median_coord`). The
coordinate swap and `z ↦ (1 - z₀ - z₁, z₁)` map the triangle onto itself, so the same holds for
the lines through the median parallel to the other two sides:
`(1 - x₀)² = (1 - x₁)² = (x₀ + x₁)² = 1/2` with all three bases positive, which forces
`1 - x₀ = x₀ + x₁ = 2(1 - x₀)`, impossible. Hence no point is a median
(`figure_21_D_8b`, for every triangle: `figure_21_D_8b_affine`), and a parameter density on
`ℝ²_{++}` need not have a median agent (`exercise_21_D_9d_not_exists`).

The triangle is taken open; the uniform distribution does not depend on the boundary (a null
set). Measures are not normalised; the median property is invariant under scaling.
-/

namespace MWG.SocialChoice

open MeasureTheory

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 806), affine invariance of medians. If `v + L x` is a median of
a Haar measure restricted to `v + L(S)`, then `x` is a median of its restriction to `S`. -/
theorem isMedianPoint_of_affine_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : E ≃ₗ[ℝ] E) (v : E) (S : Set E) (x : E)
    (h : IsMedianPoint (μ.restrict ((fun z => v + L z) '' S)) (v + L x)) :
    IsMedianPoint (μ.restrict S) x := by
  intro q hq
  set A : E →ₗ[ℝ] E := (L.symm : E →ₗ[ℝ] E) with hA
  set q' := LinearMap.adjoint A q with hq'def
  have hq' : q' ≠ 0 := by
    intro h0
    have e := LinearMap.adjoint_inner_right A (L q) q
    rw [← hq'def, h0, inner_zero_right] at e
    have e2 : ⟪q, q⟫ = 0 := by simpa [hA] using e.symm
    exact hq (inner_self_eq_zero.1 e2)
  have key := h q' hq'
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at key
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hpre : (fun z => v + L z) ⁻¹' openHalfSpace (v + L x) q' = openHalfSpace x q := by
    ext z
    simp only [openHalfSpace, Set.mem_preimage, Set.mem_ofPred_eq]
    have e : v + L z - (v + L x) = L (z - x) := by rw [map_sub]; abel
    rw [e, hq'def, LinearMap.adjoint_inner_right]
    simp [hA]
  have himg : openHalfSpace (v + L x) q' ∩ (fun z => v + L z) '' S =
      (fun z => v + L z) '' (openHalfSpace x q ∩ S) := by
    rw [Set.inter_comm, ← Set.image_inter_preimage, hpre, Set.inter_comm]
  have hmeas : ∀ T : Set E, μ ((fun z => v + L z) '' T) =
      ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * μ T := by
    intro T
    have e : (fun z => v + L z) '' T = (fun z => v + z) '' ((L : E →ₗ[ℝ] E) '' T) := by
      rw [Set.image_image]
      rfl
    rw [e, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap]
  rw [himg, hmeas, hmeas] at key
  have hd0 : ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (IsUnit.ne_zero L.isUnit_det')
  rw [mul_left_comm] at key
  exact (ENNReal.mul_le_mul_iff_right hd0 ENNReal.ofReal_ne_top).1 key

/-- The standard (open) triangle `{z : 0 < z₀, 0 < z₁, z₀ + z₁ < 1}` in the plane. -/
def stdTriangle : Set (EuclideanSpace ℝ (Fin 2)) := {z | 0 < z 0 ∧ 0 < z 1 ∧ z 0 + z 1 < 1}

/-- The coordinate map `z ↦ (z₀, z₁)` from the Euclidean plane to `ℝ × ℝ` preserves Lebesgue
measure. -/
theorem triangle_coords_measurePreserving :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- Area under the line `b = 1 - a` over `u < a < w`. -/
theorem triangle_strip_volume {u w : ℝ} (huw : u ≤ w) (hw : w ≤ 1) :
    volume (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) =
      ENNReal.ofReal ((w - u) - (w ^ 2 - u ^ 2) / 2) := by
  have hc : Continuous fun a : ℝ => 1 - a := continuous_const.sub continuous_id
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (continuous_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
    (hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo
    (fun a ha => by linarith [ha.2])]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huw]
  simp only [Pi.sub_apply, sub_zero]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- The standard triangle in coordinates: the region under `b = 1 - a` over `0 < a < 1`. -/
theorem stdTriangle_eq_preimage : stdTriangle = (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
    regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo 0 1) := by
  ext z
  simp only [stdTriangle, Set.mem_ofPred_eq, Set.mem_preimage, regionBetween, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  · rintro ⟨⟨h1, -⟩, h2, h3⟩
    exact ⟨h1, h2, by linarith⟩

/-- Through a median `x` of the uniform distribution on the standard triangle, the line
`z₀ = x₀` cuts the triangle into two pieces of equal area `1/4`: `0 < x₀ < 1` and
`(1 - x₀)² = 1/2`. -/
theorem stdTriangle_median_coord (x : EuclideanSpace ℝ (Fin 2))
    (h : IsMedianPoint (volume.restrict stdTriangle) x) :
    0 < x 0 ∧ x 0 < 1 ∧ (1 - x 0) ^ 2 = 1 / 2 := by
  set c := x 0 with hcdef
  set m := max 0 (min c 1) with hm
  have hm0 : 0 ≤ m := le_max_left _ _
  have hm1 : m ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hP := triangle_coords_measurePreserving
  have hR : ∀ u w : ℝ, MeasurableSet
      (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) := fun u w =>
    measurableSet_regionBetween measurable_const (measurable_const.sub measurable_id)
      measurableSet_Ioo
  have hup : openHalfSpace x (EuclideanSpace.single 0 1) ∩ stdTriangle =
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
        regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo m 1) := by
    ext z
    simp only [openHalfSpace, stdTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, regionBetween, Set.mem_Ioo, EuclideanSpace.inner_single_right,
      PiLp.sub_apply, one_mul, hm, max_lt_iff, min_lt_iff, RCLike.conj_to_real]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨h2, Or.inl (by linarith)⟩, by linarith⟩, h3, by linarith⟩
    · rintro ⟨⟨⟨h2, h5⟩, h6⟩, h3, h4⟩
      rcases h5 with h5 | h5
      · exact ⟨by linarith, h2, h3, by linarith⟩
      · exact absurd h6 (by linarith)
  have hlow : openHalfSpace x (-EuclideanSpace.single 0 1) ∩ stdTriangle =
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
        regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo 0 m) := by
    ext z
    simp only [openHalfSpace, stdTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, regionBetween, Set.mem_Ioo, inner_neg_right,
      EuclideanSpace.inner_single_right, PiLp.sub_apply, one_mul, hm, lt_max_iff, lt_min_iff,
      RCLike.conj_to_real]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h2, Or.inr ⟨by linarith, by linarith⟩⟩, h3, by linarith⟩
    · rintro ⟨⟨h2, h5⟩, h3, h4⟩
      rcases h5 with h5 | h5
      · exact absurd h2 (by linarith)
      · exact ⟨by linarith [h5.1], h2, h3, by linarith⟩
  have vol : ∀ u w : ℝ, volume ((fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) ⁻¹'
      regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) =
      volume (regionBetween (fun _ => (0 : ℝ)) (fun a => 1 - a) (Set.Ioo u w)) :=
    fun u w => hP.measure_preimage (hR u w).nullMeasurableSet
  have hq : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h0
    simp at this
  have h1 := h _ hq
  have h2 := h _ (neg_ne_zero.2 hq)
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hup, stdTriangle_eq_preimage,
    vol, vol, triangle_strip_volume hm1 le_rfl, triangle_strip_volume zero_le_one le_rfl,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
  rw [Measure.restrict_apply (measurableSet_openHalfSpace _ _),
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hlow, stdTriangle_eq_preimage,
    vol, vol, triangle_strip_volume hm0 hm1, triangle_strip_volume zero_le_one le_rfl,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  have hsq : (1 - m) ^ 2 = 1 / 2 := by nlinarith
  have hmpos : 0 < m := by
    rcases eq_or_lt_of_le hm0 with e | e
    · rw [← e] at hsq
      norm_num at hsq
    · exact e
  have hmlt : m < 1 := by
    rcases eq_or_lt_of_le hm1 with e | e
    · rw [e] at hsq
      norm_num at hsq
    · exact e
  have hmc : m = c := by
    rcases le_total c 0 with hc | hc
    · have : m = 0 := by rw [hm]; exact max_eq_left (le_trans (min_le_left _ _) hc)
      linarith
    · rcases le_total c 1 with hc1 | hc1
      · rw [hm, min_eq_left hc1, max_eq_right hc]
      · have : m = 1 := by rw [hm, min_eq_right hc1, max_eq_right zero_le_one]
        linarith
  rw [← hmc]
  exact ⟨hmpos, hmlt, hsq⟩

/-- The coordinate swap of the plane, as a linear map. -/
def triSwapLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun z := WithLp.toLp 2 ![z 1, z 0]
  map_add' a b := by
    ext i
    fin_cases i <;> simp
  map_smul' r a := by
    ext i
    fin_cases i <;> simp

/-- The linear part `z ↦ (-z₀ - z₁, z₁)` of the reflection `z ↦ (1 - z₀ - z₁, z₁)` of the
standard triangle. -/
def triShearLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun z := WithLp.toLp 2 ![-z 0 - z 1, z 1]
  map_add' a b := by
    ext i
    fin_cases i
    all_goals simp
    all_goals ring
  map_smul' r a := by
    ext i
    fin_cases i
    all_goals simp
    all_goals ring

/-- The swap is an involution. -/
theorem triSwapLin_involutive : Function.Involutive triSwapLin := by
  intro z
  ext i
  fin_cases i <;> simp [triSwapLin]

/-- The shear is an involution. -/
theorem triShearLin_involutive : Function.Involutive triShearLin := by
  intro z
  ext i
  fin_cases i <;> simp [triShearLin]

/-- Through a median `x` of the uniform distribution on the standard triangle, each of the three
lines through `x` parallel to a side bisects the area. -/
theorem stdTriangle_median_three (x : EuclideanSpace ℝ (Fin 2))
    (h : IsMedianPoint (volume.restrict stdTriangle) x) :
    (0 < x 0 ∧ x 0 < 1 ∧ (1 - x 0) ^ 2 = 1 / 2) ∧ (0 < x 1 ∧ x 1 < 1 ∧ (1 - x 1) ^ 2 = 1 / 2) ∧
      (0 < 1 - x 0 - x 1 ∧ 1 - x 0 - x 1 < 1 ∧ (x 0 + x 1) ^ 2 = 1 / 2) := by
  refine ⟨stdTriangle_median_coord x h, ?_, ?_⟩
  · set L := LinearEquiv.ofInvolutive triSwapLin triSwapLin_involutive
    have hL : ∀ z, L z = triSwapLin z := fun z => rfl
    have himg : (fun z => 0 + L z) '' stdTriangle = stdTriangle := by
      ext z
      simp only [zero_add, hL, Set.mem_image]
      constructor
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp [triSwapLin] <;> linarith
      · rintro ⟨h1, h2, h3⟩
        refine ⟨triSwapLin z, ⟨?_, ?_, ?_⟩, triSwapLin_involutive z⟩ <;>
          simp [triSwapLin] <;> linarith
    have hx : 0 + L (triSwapLin x) = x := by rw [zero_add, hL, triSwapLin_involutive x]
    have hmed := isMedianPoint_of_affine_image volume L 0 stdTriangle (triSwapLin x)
      (by rw [himg, hx]; exact h)
    simpa [triSwapLin] using stdTriangle_median_coord _ hmed
  · set L := LinearEquiv.ofInvolutive triShearLin triShearLin_involutive
    have hL : ∀ z, L z = triShearLin z := fun z => rfl
    set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    have hv0 : v 0 = 1 := by simp [v]
    have hv1 : v 1 = 0 := by simp [v]
    have himg : (fun z => v + L z) '' stdTriangle = stdTriangle := by
      ext z
      simp only [hL, Set.mem_image]
      constructor
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp [triShearLin, hv0, hv1] <;> linarith
      · rintro ⟨h1, h2, h3⟩
        refine ⟨v + triShearLin z, ⟨?_, ?_, ?_⟩, ?_⟩
        · simp [triShearLin, hv0]
          linarith
        · simp [triShearLin, hv1]
          linarith
        · simp [triShearLin, hv0, hv1]
          linarith
        · ext i
          fin_cases i
          · simp [triShearLin, hv0, hv1]
            ring
          · simp [triShearLin, hv1]
    have hx : v + L (v + triShearLin x) = x := by
      rw [hL]
      ext i
      fin_cases i
      · simp [triShearLin, hv0, hv1]
        ring
      · simp [triShearLin, hv1]
    have hmed := isMedianPoint_of_affine_image volume L v stdTriangle (v + triShearLin x)
      (by rw [himg, hx]; exact h)
    have := stdTriangle_median_coord _ hmed
    simp only [PiLp.add_apply, hv0, triShearLin, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero] at this
    obtain ⟨a, b, e⟩ := this
    refine ⟨by linarith, by linarith, ?_⟩
    rw [← e]
    ring

/-- **Figure 21.D.8(b)** (MWG, p. 806). The uniform distribution on a triangle has no median:
"through any point of a triangle we can draw a line that divides it into two regions of unequal
area". Standard triangle. -/
theorem figure_21_D_8b (x : EuclideanSpace ℝ (Fin 2)) :
    ¬IsMedianPoint (volume.restrict stdTriangle) x := by
  intro h
  obtain ⟨⟨-, a1, e0⟩, ⟨b0, b1, e1⟩, ⟨c0, -, e2⟩⟩ := stdTriangle_median_three x h
  have hr : 1 - x 0 = 1 - x 1 := by
    have : (1 - x 0 - (1 - x 1)) * (1 - x 0 + (1 - x 1)) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hs : x 0 + x 1 = 1 - x 0 := by
    have : (x 0 + x 1 - (1 - x 0)) * (x 0 + x 1 + (1 - x 0)) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have : x 0 = 1 / 3 := by linarith
  rw [this] at e0
  norm_num at e0

/-- **Figure 21.D.8(b)** (MWG, p. 806), every triangle. The image of the standard triangle under
any affine bijection `z ↦ v + L z` (every triangle with nonempty interior is such an image)
carries a uniform distribution with no median. -/
theorem figure_21_D_8b_affine (L : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (v y : EuclideanSpace ℝ (Fin 2)) :
    ¬IsMedianPoint (volume.restrict ((fun z => v + L z) '' stdTriangle)) y := by
  intro h
  have hy : v + L (L.symm (y - v)) = y := by simp
  rw [← hy] at h
  exact figure_21_D_8b _ (isMedianPoint_of_affine_image volume L v stdTriangle _ h)

/-- **Exercise 21.D.9(d)** (MWG, p. 814), nonexistence half. For the uniform density of
parameters on the triangle with vertices `(1, 1)`, `(2, 1)`, `(1, 2)` inside `ℝ²_{++}`, no
`β*` is a median agent. -/
theorem exercise_21_D_9d_not_exists :
    (fun z => EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 + z) '' stdTriangle ⊆
        {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 < z i} ∧
      ∀ β : EuclideanSpace ℝ (Fin 2), ¬IsMedianPoint (volume.restrict
        ((fun z => EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 + z) '' stdTriangle))
        β := by
  refine ⟨?_, fun β => ?_⟩
  · rintro _ ⟨w, ⟨h1, h2, -⟩, rfl⟩ i
    fin_cases i
    · simp
      linarith
    · simp
      linarith
  · have := figure_21_D_8b_affine (LinearEquiv.refl ℝ _)
      (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) β
    simpa using this

end MWG.SocialChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Directional median agents

MWG, Exercise 21.D.8, p. 813.

Three agents have utilities on `X ⊆ ℝ²` (modelled by `ℂ`) with gradients `g₀, g₁, g₂` at a
point. Agent `h` is a (first-order) *directional median* if every direction that strictly
improves two agents strictly improves `h` (`IsDirectionalMedian`, in `GradientCycles`).

(a) A directional median exists whenever the cone spanned by the gradients is pointed in MWG's
sense (contains no half-space): `exercise_21_D_8a`. In fact we prove the full dichotomy: a
directional median exists iff the cone is not the whole plane (`exercise_21_D_8a_iff`; the
spanning case is that of Exercise 21.D.7). The case analysis runs on the signs of the signed
areas `c₀ = D(g₁, g₂)`, `c₁ = D(g₂, g₀)`, `c₂ = D(g₀, g₁)`, which satisfy
`c₀ g₀ + c₁ g₁ + c₂ g₂ = 0`: if no agent is a directional median, the Binet-Cauchy identity
rules out `cᵢ = 0` and the relation rules out mixed signs, so the `cᵢ` have a common strict sign
and the gradients span the plane positively.

**Correction (reading of (a)).** Read literally ("any alternative having a strict majority
against the origin must make this agent strictly better off", a global statement about
utility levels), (a) is false even for concave utilities with a pointed gradient cone:
`exercise_21_D_8a_global_counterexample`. The statement holds for the first-order notion.

(b) Euclidean utilities `uᵢ(z) = -‖z - pᵢ‖²` with peaks `(0, 8)`, `(8, 8)`, `(4, 12)` on the
open half-plane `X = {z : z₁ < 8}` (which contains the origin): the gradient cone is pointed
at every point of `X`, the directional median is agent 2 at the origin but agent 0 at
`(-12, 7)`, and there is a Condorcet cycle in `X` (`exercise_21_D_8b`).

(c) For the literal (global) reading the conclusion holds for arbitrary utilities on any set
(`exercise_21_D_8c_global`); for the first-order notion it holds for linear utilities
(`exercise_21_D_8c`, in `GradientCycles`) but **fails** for nonlinear concave utilities:
`exercise_21_D_8c_counterexample` (`Im z - (Re z)²`, `Im z`, `Im z - (max (Re z) 0)²` on the
plane; agent 2 is a first-order directional median everywhere, the cone is pointed everywhere,
and there is a Condorcet cycle).
-/

namespace MWG.SocialChoice

open Finset

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Exercise 21.D.8** (MWG, p. 813). The cone spanned by `g₀, g₁, g₂` contains a closed
half-space `{v : ⟪v, q⟫ ≥ 0}`, `q ≠ 0`. MWG calls the cone *pointed* when this fails. -/
def ConeContainsHalfSpace (g : Fin 3 → ℂ) : Prop :=
  ∃ q : ℂ, q ≠ 0 ∧ ∀ v : ℂ, 0 ≤ ⟪v, q⟫ →
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i

/-- The relation `D(b, c) a + D(c, a) b + D(a, b) c = 0` among three plane vectors, paired
with any `d`. -/
theorem dm_three_term (a b c d : ℂ) :
    ⟪b, Complex.I * c⟫ * ⟪a, d⟫ + ⟪c, Complex.I * a⟫ * ⟪b, d⟫ + ⟪a, Complex.I * b⟫ * ⟪c, d⟫ =
      0 := by
  simp only [inner_I_mul]
  simp only [complex_inner_eq]
  ring

/-- The Binet-Cauchy identity in the plane. -/
theorem dm_binet_cauchy (a b d d' : ℂ) :
    ⟪a, d⟫ * ⟪b, d'⟫ - ⟪a, d'⟫ * ⟪b, d⟫ = ⟪a, Complex.I * b⟫ * ⟪d, Complex.I * d'⟫ := by
  simp only [inner_I_mul]
  simp only [complex_inner_eq]
  ring

/-- If `h` is not a directional median, some direction strictly improves both other agents and
does not improve `h`. -/
theorem dm_not_median {g : Fin 3 → ℂ} {h : Fin 3} (hn : ¬IsDirectionalMedian g h) :
    ∃ d : ℂ, ⟪g h, d⟫ ≤ 0 ∧ ∀ k, k ≠ h → 0 < ⟪g k, d⟫ := by
  unfold IsDirectionalMedian at hn
  push Not at hn
  obtain ⟨d, ⟨i, j, hij, hi, hj⟩, hh⟩ := hn
  refine ⟨d, hh, fun k hk => ?_⟩
  have hih : i ≠ h := by
    rintro rfl
    linarith
  have hjh : j ≠ h := by
    rintro rfl
    linarith
  have key : ∀ h i j k : Fin 3, i ≠ h → j ≠ h → i ≠ j → k ≠ h → k = i ∨ k = j := by decide
  rcases key h i j k hih hjh hij hk with rfl | rfl
  · exact hi
  · exact hj

/-- Gradients with a strictly positive linear relation `∑ lᵢ gᵢ = 0` and `D(g₀, g₁) ≠ 0` span
the plane positively. -/
theorem dm_spans_of_relation {g : Fin 3 → ℂ} {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i)
    (hsum : ∀ d : ℂ, l 0 * ⟪g 0, d⟫ + l 1 * ⟪g 1, d⟫ + l 2 * ⟪g 2, d⟫ = 0)
    (h01 : ⟪g 0, Complex.I * g 1⟫ ≠ 0) (v : ℂ) :
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  have hre : l 0 * (g 0).re + l 1 * (g 1).re + l 2 * (g 2).re = 0 := by
    have := hsum 1
    simp only [complex_inner_eq, Complex.one_re, Complex.one_im, mul_one, mul_zero,
      add_zero] at this
    exact this
  have him : l 0 * (g 0).im + l 1 * (g 1).im + l 2 * (g 2).im = 0 := by
    have := hsum Complex.I
    simp only [complex_inner_eq, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      zero_add] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c, c = ⟪g 0, Complex.I * g 1⟫ := ⟨_, rfl⟩
  rw [← hc] at h01
  obtain ⟨α, hα⟩ : ∃ α, α = ⟪v, Complex.I * g 1⟫ / c := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ⟪g 0, Complex.I * v⟫ / c := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = |α| / l 0 + |β| / l 1 := ⟨_, rfl⟩
  have e1 : α * (g 0).re + β * (g 1).re = v.re := by
    rw [hα, hβ]
    field_simp
    rw [hc]
    simp only [inner_I_mul]
    ring
  have e2 : α * (g 0).im + β * (g 1).im = v.im := by
    rw [hα, hβ]
    field_simp
    rw [hc]
    simp only [inner_I_mul]
    ring
  have t0 : |α| ≤ t * l 0 := by
    have : t * l 0 = |α| + |β| / l 1 * l 0 := by
      rw [ht]
      field_simp [(hl 0).ne']
    rw [this]
    have := div_nonneg (abs_nonneg β) (hl 1).le
    nlinarith [hl 0]
  have t1 : |β| ≤ t * l 1 := by
    have : t * l 1 = |α| / l 0 * l 1 + |β| := by
      rw [ht]
      field_simp [(hl 1).ne']
    rw [this]
    have := div_nonneg (abs_nonneg α) (hl 0).le
    nlinarith [hl 1]
  have tnn : 0 ≤ t := by
    rw [ht]
    exact add_nonneg (div_nonneg (abs_nonneg _) (hl 0).le) (div_nonneg (abs_nonneg _) (hl 1).le)
  refine ⟨![α + t * l 0, β + t * l 1, t * l 2], fun i => ?_, ?_⟩
  · fin_cases i
    · change 0 ≤ α + t * l 0
      linarith [neg_abs_le α]
    · change 0 ≤ β + t * l 1
      linarith [neg_abs_le β]
    · change 0 ≤ t * l 2
      exact mul_nonneg tnn (hl 2).le
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      linear_combination -e1 - t * hre
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      linear_combination -e2 - t * him

/-- **Exercise 21.D.8(a)** (MWG, p. 813), the case analysis on the cone. Either some agent is a
directional median, or the gradients span the whole plane positively. -/
theorem dm_median_or_spans (g : Fin 3 → ℂ) :
    (∃ h, IsDirectionalMedian g h) ∨
      ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  by_cases hm : ∃ h, IsDirectionalMedian g h
  · exact Or.inl hm
  right
  push Not at hm
  obtain ⟨d0, a00, ha0⟩ := dm_not_median (hm 0)
  obtain ⟨d1, a11, ha1⟩ := dm_not_median (hm 1)
  obtain ⟨d2, a22, ha2⟩ := dm_not_median (hm 2)
  have a10 := ha0 1 (by decide)
  have a20 := ha0 2 (by decide)
  have a01 := ha1 0 (by decide)
  have a21 := ha1 2 (by decide)
  have a02 := ha2 0 (by decide)
  have a12 := ha2 1 (by decide)
  have R0 := dm_three_term (g 0) (g 1) (g 2) d0
  have R1 := dm_three_term (g 0) (g 1) (g 2) d1
  have R2 := dm_three_term (g 0) (g 1) (g 2) d2
  have B2 := dm_binet_cauchy (g 0) (g 1) d0 d2
  have B0 := dm_binet_cauchy (g 1) (g 2) d1 d0
  have B1 := dm_binet_cauchy (g 2) (g 0) d2 d1
  have hc2 : ⟪g 0, Complex.I * g 1⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B2
    nlinarith [mul_pos a02 a10, mul_nonneg (neg_nonneg.2 a00) a12.le]
  have hc0 : ⟪g 1, Complex.I * g 2⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B0
    nlinarith [mul_pos a10 a21, mul_nonneg (neg_nonneg.2 a11) a20.le]
  have hc1 : ⟪g 2, Complex.I * g 0⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B1
    nlinarith [mul_pos a21 a02, mul_nonneg (neg_nonneg.2 a22) a01.le]
  have hsign : (0 < ⟪g 1, Complex.I * g 2⟫ ∧ 0 < ⟪g 2, Complex.I * g 0⟫ ∧
      0 < ⟪g 0, Complex.I * g 1⟫) ∨ (⟪g 1, Complex.I * g 2⟫ < 0 ∧
      ⟪g 2, Complex.I * g 0⟫ < 0 ∧ ⟪g 0, Complex.I * g 1⟫ < 0) := by
    rcases hc0.lt_or_gt with h0 | h0 <;> rcases hc1.lt_or_gt with h1 | h1 <;>
      rcases hc2.lt_or_gt with h2 | h2
    · exact Or.inr ⟨h0, h1, h2⟩
    · linarith [mul_neg_of_neg_of_pos h0 a02, mul_neg_of_neg_of_pos h1 a12,
        mul_nonpos_of_nonneg_of_nonpos h2.le a22]
    · linarith [mul_neg_of_neg_of_pos h0 a01, mul_nonpos_of_nonneg_of_nonpos h1.le a11,
        mul_neg_of_neg_of_pos h2 a21]
    · linarith [mul_nonneg_of_nonpos_of_nonpos h0.le a00, mul_pos h1 a10, mul_pos h2 a20]
    · linarith [mul_nonpos_of_nonneg_of_nonpos h0.le a00, mul_neg_of_neg_of_pos h1 a10,
        mul_neg_of_neg_of_pos h2 a20]
    · linarith [mul_pos h0 a01, mul_nonneg_of_nonpos_of_nonpos h1.le a11, mul_pos h2 a21]
    · linarith [mul_pos h0 a02, mul_pos h1 a12, mul_nonneg_of_nonpos_of_nonpos h2.le a22]
    · exact Or.inl ⟨h0, h1, h2⟩
  rcases hsign with ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩
  · refine dm_spans_of_relation (l := ![⟪g 1, Complex.I * g 2⟫, ⟪g 2, Complex.I * g 0⟫,
      ⟪g 0, Complex.I * g 1⟫]) (fun i => ?_) (fun d => ?_) hc2
    · fin_cases i
      · exact p0
      · exact p1
      · exact p2
    · simpa using dm_three_term (g 0) (g 1) (g 2) d
  · refine dm_spans_of_relation (l := ![-⟪g 1, Complex.I * g 2⟫, -⟪g 2, Complex.I * g 0⟫,
      -⟪g 0, Complex.I * g 1⟫]) (fun i => ?_) (fun d => ?_) hc2
    · fin_cases i
      · exact neg_pos.2 p0
      · exact neg_pos.2 p1
      · exact neg_pos.2 p2
    · have := dm_three_term (g 0) (g 1) (g 2) d
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      linarith

/-- If the gradients span the plane positively, no agent is a directional median. -/
theorem dm_spans_no_median {g : Fin 3 → ℂ}
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) (h : Fin 3) :
    ¬IsDirectionalMedian g h := by
  obtain ⟨d0, d1, d2, -, a10, a20, a01, a21, a02, a12, -⟩ := cone_directions hcone
  obtain ⟨μ, hμ, hv⟩ := hcone (-(g 0 + g 1 + g 2))
  have rel : ∀ d : ℂ, (μ 0 + 1) * ⟪g 0, d⟫ + (μ 1 + 1) * ⟪g 1, d⟫ + (μ 2 + 1) * ⟪g 2, d⟫ =
      0 := by
    intro d
    have := congrArg (fun w => ⟪w, d⟫) hv
    simp only [Fin.sum_univ_three, inner_add_left, inner_neg_left, real_inner_smul_left] at this
    linarith
  have m0 := hμ 0
  have m1 := hμ 1
  have m2 := hμ 2
  intro hmed
  fin_cases h
  · have := hmed d0 ⟨1, 2, by decide, a10, a20⟩
    change 0 < ⟪g 0, d0⟫ at this
    nlinarith [rel d0, mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) a10,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) a20,
      mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) this]
  · have := hmed d1 ⟨0, 2, by decide, a01, a21⟩
    change 0 < ⟪g 1, d1⟫ at this
    nlinarith [rel d1, mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) a01,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) a21,
      mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) this]
  · have := hmed d2 ⟨0, 1, by decide, a02, a12⟩
    change 0 < ⟪g 2, d2⟫ at this
    nlinarith [rel d2, mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) a02,
      mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) a12,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) this]

/-- **Exercise 21.D.8(a)** (MWG, p. 813), sharp form. Some agent is a directional median iff the
cone spanned by the gradients is not the whole plane. -/
theorem exercise_21_D_8a_iff (g : Fin 3 → ℂ) :
    (∃ h, IsDirectionalMedian g h) ↔
      ¬∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  constructor
  · rintro ⟨h, hh⟩ hc
    exact dm_spans_no_median hc h hh
  · intro hn
    exact (dm_median_or_spans g).resolve_right hn

/-- **Exercise 21.D.8(a)** (MWG, p. 813). If the cone spanned by the gradients is pointed
(contains no half-space), some agent is a directional median: every direction that strictly
improves a majority strictly improves that agent. -/
theorem exercise_21_D_8a (g : Fin 3 → ℂ) (hpt : ¬ConeContainsHalfSpace g) :
    ∃ h, IsDirectionalMedian g h :=
  (dm_median_or_spans g).resolve_right fun hc => hpt ⟨1, one_ne_zero, fun v _ => hc v⟩

/-- A cone of vectors all strictly on one side of a line through the origin is pointed. -/
theorem not_coneContainsHalfSpace_of_pos (g : Fin 3 → ℂ) (p : ℂ) (hp : ∀ i, 0 < ⟪g i, p⟫) :
    ¬ConeContainsHalfSpace g := by
  rintro ⟨q, hq, hH⟩
  have hIq : ⟪Complex.I * q, q⟫ = 0 := by
    simp only [complex_inner_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hIq0 : Complex.I * q ≠ 0 := mul_ne_zero Complex.I_ne_zero hq
  have key : ∀ w : ℂ, w ≠ 0 → ⟪w, q⟫ = 0 → ⟪w, p⟫ ≤ 0 → False := by
    intro w hw hwq hwp
    obtain ⟨μ, hμ, hv⟩ := hH w hwq.ge
    have hnn : ∀ j, 0 ≤ μ j * ⟪g j, p⟫ := fun j => mul_nonneg (hμ j) (hp j).le
    have e : ⟪w, p⟫ = ∑ j, μ j * ⟪g j, p⟫ := by
      rw [hv, sum_inner]
      simp only [real_inner_smul_left]
    have hsum0 : ∑ j, μ j * ⟪g j, p⟫ = 0 :=
      le_antisymm (e ▸ hwp) (sum_nonneg fun j _ => hnn j)
    have hz : ∀ i, μ i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 hsum0 i (mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hp i).ne'
    apply hw
    rw [hv]
    simp [hz]
  rcases le_total ⟪Complex.I * q, p⟫ 0 with h | h
  · exact key _ hIq0 hIq h
  · exact key (-(Complex.I * q)) (neg_ne_zero.2 hIq0) (by rw [inner_neg_left, hIq, neg_zero])
      (by rw [inner_neg_left]; linarith)

/-- **Exercise 21.D.8(a)**, instance. The gradients `1, 1, I` span a pointed cone, and agent `0`
is a directional median. -/
theorem exercise_21_D_8a_instance :
    ¬ConeContainsHalfSpace ![1, 1, Complex.I] ∧ IsDirectionalMedian ![1, 1, Complex.I] 0 :=
  ⟨not_coneContainsHalfSpace_of_pos _ (1 + Complex.I) (by
    intro i
    fin_cases i <;> simp), exercise_21_D_8c_instance⟩

/-- **Exercise 21.D.8(a)** (MWG, p. 813), literal reading: agent `h` is a directional median at
`x` if every alternative of `X` that a strict majority prefers to `x` makes `h` strictly better
off. -/
def IsGlobalDirectionalMedian (X : Set ℂ) (u : Fin 3 → ℂ → ℝ) (x : ℂ) (h : Fin 3) : Prop :=
  ∀ y ∈ X, TwoAgentsPrefer u y x → u h x < u h y

/-- The concave utilities `Re z`, `Im z`, `Re z + Im z - 2 (Re z - Im z)²` of the counterexample
to the literal reading of Exercise 21.D.8(a). -/
def e218aUtil : Fin 3 → ℂ → ℝ :=
  ![fun z => z.re, fun z => z.im, fun z => z.re + z.im - 2 * (z.re - z.im) ^ 2]

/-- **Exercise 21.D.8(a)**, correction: the literal reading is false. The utilities `e218aUtil`
are concave, with gradients `1, I, 1 + I` at the origin spanning a pointed cone (agent 2 is a
first-order directional median), yet for every agent `h` some alternative is preferred to the
origin by a strict majority while `h` is not better off. -/
theorem exercise_21_D_8a_global_counterexample :
    (∀ i, ConcaveOn ℝ Set.univ (e218aUtil i)) ∧
      (∀ i, HasGradientAt (e218aUtil i) (![1, Complex.I, 1 + Complex.I] i) 0) ∧
      ¬ConeContainsHalfSpace ![1, Complex.I, 1 + Complex.I] ∧
      IsDirectionalMedian ![1, Complex.I, 1 + Complex.I] 2 ∧
      ∀ h, ¬IsGlobalDirectionalMedian Set.univ e218aUtil 0 h := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, fun h => ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    fin_cases i
    · simp [e218aUtil]
    · simp [e218aUtil]
    · simp only [e218aUtil, Fin.reduceFinMk, Matrix.cons_val, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg ((x.re - x.im) - (y.re - y.im)))]
  · fin_cases i
    · convert hasGradientAt_inner_const 1 using 1
      · funext z
        simp [e218aUtil]
      · rfl
    · convert hasGradientAt_inner_const Complex.I using 1
      · funext z
        simp [e218aUtil]
      · rfl
    · rw [hasGradientAt_iff_hasFDerivAt]
      have hA := (InnerProductSpace.toDual ℝ ℂ (1 + Complex.I) : ℂ →L[ℝ] ℝ).hasFDerivAt
        (x := 0)
      have hB := (InnerProductSpace.toDual ℝ ℂ (1 - Complex.I) : ℂ →L[ℝ] ℝ).hasFDerivAt
        (x := 0)
      have hC := hA.sub ((hB.mul hB).const_mul 2)
      convert hC using 1
      · funext z
        simp [e218aUtil, InnerProductSpace.toDual_apply_apply]
        ring
      · simp
  · exact not_coneContainsHalfSpace_of_pos _ (1 + Complex.I) (by
      intro i
      fin_cases i <;> rw [complex_inner_eq] <;> simp)
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  · intro hh
    fin_cases h
    · have := hh ⟨-1 / 100, 1 / 50⟩ trivial ⟨1, 2, by decide, by simp [e218aUtil],
        by simp [e218aUtil]; norm_num⟩
      simp [e218aUtil] at this
      norm_num at this
    · have := hh ⟨1 / 50, -1 / 100⟩ trivial ⟨0, 2, by decide, by simp [e218aUtil],
        by simp [e218aUtil]; norm_num⟩
      simp [e218aUtil] at this
      norm_num at this
    · have := hh ⟨1, 1 / 100⟩ trivial ⟨0, 1, by decide, by simp [e218aUtil],
        by simp [e218aUtil]⟩
      simp [e218aUtil] at this
      norm_num at this

/-- The peaks `(0, 8)`, `(8, 8)`, `(4, 12)` of the Euclidean example for Exercise 21.D.8(b). -/
def e218bPeak : Fin 3 → ℂ := ![⟨0, 8⟩, ⟨8, 8⟩, ⟨4, 12⟩]

/-- The Euclidean utilities `uᵢ(z) = -‖z - pᵢ‖²` of the example for Exercise 21.D.8(b), in
coordinates. -/
def e218bUtil (i : Fin 3) (z : ℂ) : ℝ :=
  -((z.re - (e218bPeak i).re) ^ 2 + (z.im - (e218bPeak i).im) ^ 2)

/-- Their gradients `2 (pᵢ - x)` at `x`. -/
noncomputable def e218bGrad (x : ℂ) (i : Fin 3) : ℂ := (2 : ℝ) • (e218bPeak i - x)

/-- The utilities `e218bUtil` are Euclidean: `uᵢ(z) = -‖z - pᵢ‖²`. -/
theorem e218bUtil_eq (i : Fin 3) (z : ℂ) : e218bUtil i z = -‖z - e218bPeak i‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, e218bUtil, Complex.sub_re, Complex.sub_im]
  ring

/-- The utilities `e218bUtil` are concave on the plane. -/
theorem e218bUtil_concave (i : Fin 3) : ConcaveOn ℝ Set.univ (e218bUtil i) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [e218bUtil, smul_eq_mul, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg (x.re - y.re))
    (sq_nonneg (x.im - y.im)))]

/-- `e218bUtil i` has gradient `2 (pᵢ - x)` at every `x`. -/
theorem e218bUtil_hasGradientAt (i : Fin 3) (x : ℂ) :
    HasGradientAt (e218bUtil i) (e218bGrad x i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hre := (Complex.reCLM.hasFDerivAt (x := x)).sub_const (e218bPeak i).re
  have him := (Complex.imCLM.hasFDerivAt (x := x)).sub_const (e218bPeak i).im
  have h := ((hre.mul hre).add (him.mul him)).neg
  convert h using 1
  · funext z
    simp only [e218bUtil, Pi.neg_apply, Pi.add_apply, Pi.mul_apply, Complex.reCLM_apply,
      Complex.imCLM_apply]
    ring
  · ext v
    simp [e218bGrad, InnerProductSpace.toDual_apply_apply]
    ring

/-- **Exercise 21.D.8(b)** (MWG, p. 813). Euclidean utilities with peaks `(0, 8)`, `(8, 8)`,
`(4, 12)` on the convex open half-plane `X = {z : z₁ < 8}`, which contains the origin. The
utilities are concave and differentiable; at every point of `X` the gradient cone is pointed,
so (by (a)) there is a directional median; the directional median is agent 2 (not agent 0) at
the origin and agent 0 (not agent 2) at `(-12, 7)`; and `(-7, 6)`, `0`, `(-4, 2)` form a
Condorcet cycle in `X`. -/
theorem exercise_21_D_8b :
    Convex ℝ {z : ℂ | z.im < 8} ∧ (0 : ℂ) ∈ interior {z : ℂ | z.im < 8} ∧
      (∀ i, ConcaveOn ℝ Set.univ (e218bUtil i)) ∧
      (∀ x i, HasGradientAt (e218bUtil i) (e218bGrad x i) x) ∧
      (∀ x : ℂ, x.im < 8 → ¬ConeContainsHalfSpace (e218bGrad x)) ∧
      (∀ x : ℂ, x.im < 8 → ∃ h, IsDirectionalMedian (e218bGrad x) h) ∧
      IsDirectionalMedian (e218bGrad 0) 2 ∧ ¬IsDirectionalMedian (e218bGrad 0) 0 ∧
      IsDirectionalMedian (e218bGrad ⟨-12, 7⟩) 0 ∧
      ¬IsDirectionalMedian (e218bGrad ⟨-12, 7⟩) 2 ∧
      ∃ x ∈ {z : ℂ | z.im < 8}, ∃ y ∈ {z : ℂ | z.im < 8}, ∃ z ∈ {z : ℂ | z.im < 8},
        TwoAgentsPrefer e218bUtil x y ∧ TwoAgentsPrefer e218bUtil y z ∧
          TwoAgentsPrefer e218bUtil z x := by
  have hpt : ∀ x : ℂ, x.im < 8 → ¬ConeContainsHalfSpace (e218bGrad x) := by
    intro x hx
    apply not_coneContainsHalfSpace_of_pos _ Complex.I
    intro i
    fin_cases i <;> simp [e218bGrad, e218bPeak] <;> linarith
  refine ⟨?_, ?_, e218bUtil_concave, fun x i => e218bUtil_hasGradientAt i x, hpt,
    fun x hx => exercise_21_D_8a _ (hpt x hx), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢
      rw [zero_add] at hab
      rw [hab]
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx h, mul_le_mul_of_nonneg_left hy.le hb]
  · rw [(isOpen_lt Complex.continuous_im continuous_const).interior_eq]
    simp
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all [e218bGrad, e218bPeak] <;> linarith
  · intro h
    have := h 1 ⟨1, 2, by decide, by simp [e218bGrad, e218bPeak], by
      simp [e218bGrad, e218bPeak]⟩
    simp [e218bGrad, e218bPeak] at this
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all [e218bGrad, e218bPeak] <;> linarith
  · intro h
    have := h ⟨1, -4⟩ ⟨0, 1, by decide, by simp [e218bGrad, e218bPeak]; norm_num, by
      simp [e218bGrad, e218bPeak]; norm_num⟩
    simp [e218bGrad, e218bPeak] at this
    norm_num at this
  · refine ⟨⟨-7, 6⟩, by simp; norm_num, 0, by simp, ⟨-4, 2⟩, by simp; norm_num,
      ⟨0, 2, by decide, ?_, ?_⟩, ⟨1, 2, by decide, ?_, ?_⟩, ⟨0, 1, by decide, ?_, ?_⟩⟩ <;>
      simp [e218bUtil, e218bPeak] <;> norm_num

/-- **Exercise 21.D.8(c)** (MWG, p. 813), literal reading, arbitrary utilities. If the same
agent `h` is a directional median (in the literal sense of (a)) at every point of `X`, there is
no Condorcet cycle in `X`. -/
theorem exercise_21_D_8c_global {X : Set ℂ} {u : Fin 3 → ℂ → ℝ} {h : Fin 3}
    (hmed : ∀ x ∈ X, IsGlobalDirectionalMedian X u x h) {x y z : ℂ} (hx : x ∈ X) (hy : y ∈ X)
    (hz : z ∈ X) :
    ¬(TwoAgentsPrefer u x y ∧ TwoAgentsPrefer u y z ∧ TwoAgentsPrefer u z x) := by
  rintro ⟨h1, h2, h3⟩
  have a := hmed y hy x hx h1
  have b := hmed z hz y hy h2
  have c := hmed x hx z hz h3
  linarith

/-- **Exercise 21.D.8(c)**, instance. For the linear utilities with gradients `1, 1, I`, agent
`0` is a directional median in the literal sense at every point of the plane. -/
theorem exercise_21_D_8c_global_instance (x : ℂ) :
    IsGlobalDirectionalMedian Set.univ (fun i v => ⟪![1, 1, Complex.I] i, v⟫) x 0 := by
  rintro y - ⟨i, j, hij, hi, hj⟩
  have := exercise_21_D_8c_instance (y - x) ⟨i, j, hij, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  rw [inner_sub_right] at this
  linarith

/-- `t ↦ (max t 0)²` has derivative `2 max t 0` everywhere. -/
theorem e218c_hasDerivAt_sqPos (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have e : (fun s : ℝ => max s 0 ^ 2) =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [max_eq_right (le_of_lt (Set.mem_Iio.1 hs))]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq e
  · rw [hasDerivAt_iff_isLittleO]
    simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      mul_zero, smul_zero]
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun s => ?_)).trans_isLittleO
      (Asymptotics.isLittleO_pow_id one_lt_two)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _), one_mul]
    rcases le_total s 0 with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg s]
    · rw [max_eq_left h]
  · have e : (fun s : ℝ => max s 0 ^ 2) =ᶠ[nhds t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt (Set.mem_Ioi.1 hs))]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq e

/-- The concave utilities `Im z - (Re z)²`, `Im z`, `Im z - (max (Re z) 0)²` of the
counterexample to the first-order reading of Exercise 21.D.8(c). -/
def e218cUtil : Fin 3 → ℂ → ℝ :=
  ![fun z => z.im - z.re ^ 2, fun z => z.im, fun z => z.im - max z.re 0 ^ 2]

/-- Their gradients `(-2 Re x, 1)`, `(0, 1)`, `(-2 max (Re x) 0, 1)` at `x`. -/
noncomputable def e218cGrad (x : ℂ) : Fin 3 → ℂ :=
  ![⟨-2 * x.re, 1⟩, ⟨0, 1⟩, ⟨-2 * max x.re 0, 1⟩]

/-- **Exercise 21.D.8(c)** (MWG, p. 813), correction: false for nonlinear utilities under the
first-order notion of directional median. On `X = ℝ²` the utilities `e218cUtil` are concave and
differentiable with gradients `e218cGrad`; at every point the gradient cone is pointed and agent
2 is a directional median (its gradient equals agent 1's where `Re x ≤ 0` and agent 0's where
`Re x ≥ 0`); yet `(0, -1/4)`, `(1, 1/2)`, `(-1, 0)` form a Condorcet cycle. What survives is
the literal reading (`exercise_21_D_8c_global`) and the linear case (`exercise_21_D_8c`). -/
theorem exercise_21_D_8c_counterexample :
    (∀ i, ConcaveOn ℝ Set.univ (e218cUtil i)) ∧
      (∀ x i, HasGradientAt (e218cUtil i) (e218cGrad x i) x) ∧
      (∀ x, ¬ConeContainsHalfSpace (e218cGrad x)) ∧
      (∀ x, IsDirectionalMedian (e218cGrad x) 2) ∧
      TwoAgentsPrefer e218cUtil ⟨0, -1 / 4⟩ ⟨1, 1 / 2⟩ ∧
      TwoAgentsPrefer e218cUtil ⟨1, 1 / 2⟩ ⟨-1, 0⟩ ∧
      TwoAgentsPrefer e218cUtil ⟨-1, 0⟩ ⟨0, -1 / 4⟩ := by
  refine ⟨fun i => ?_, fun x i => ?_, fun x => ?_, fun x => ?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    fin_cases i
    · simp only [e218cUtil, Fin.zero_eta, Matrix.cons_val_zero, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      obtain rfl : b = 1 - a := by linarith
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.re - y.re))]
    · simp [e218cUtil]
    · simp only [e218cUtil, Fin.reduceFinMk, Matrix.cons_val, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      have h1 : max (a * x.re + b * y.re) 0 ≤ a * max x.re 0 + b * max y.re 0 :=
        max_le (by nlinarith [le_max_left x.re 0, le_max_left y.re 0])
          (by nlinarith [le_max_right x.re 0, le_max_right y.re 0])
      have h0 := le_max_right (a * x.re + b * y.re) 0
      obtain rfl : b = 1 - a := by linarith
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (max x.re 0 - max y.re 0)),
        mul_le_mul h1 h1 h0 (le_trans h0 h1)]
  · rw [hasGradientAt_iff_hasFDerivAt]
    fin_cases i
    · have h := (Complex.imCLM.hasFDerivAt (x := x)).sub
        ((Complex.reCLM.hasFDerivAt (x := x)).mul (Complex.reCLM.hasFDerivAt (x := x)))
      convert h using 1
      · funext z
        simp [e218cUtil]
        ring
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
        ring
    · convert Complex.imCLM.hasFDerivAt (x := x) using 1
      · funext v
        simp [e218cUtil]
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
    · have hq := e218c_hasDerivAt_sqPos (Complex.reCLM x)
      have h := (Complex.imCLM.hasFDerivAt (x := x)).sub
        (hq.comp_hasFDerivAt x (Complex.reCLM.hasFDerivAt (x := x)))
      convert h using 1
      · funext z
        simp [e218cUtil]
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
        ring
  · apply not_coneContainsHalfSpace_of_pos _ Complex.I
    intro i
    fin_cases i <;> simp [e218cGrad]
  · rintro d ⟨i, j, hij, hi, hj⟩
    rcases le_total x.re 0 with hr | hr
    · have hm : max x.re 0 = 0 := max_eq_right hr
      fin_cases i <;> fin_cases j <;> simp_all [e218cGrad]
    · have hm : max x.re 0 = x.re := max_eq_left hr
      fin_cases i <;> fin_cases j <;> simp_all [e218cGrad]
  · exact ⟨0, 2, by decide, by simp [e218cUtil]; norm_num, by simp [e218cUtil]; norm_num⟩
  · exact ⟨0, 1, by decide, by simp [e218cUtil], by simp [e218cUtil]⟩
  · exact ⟨1, 2, by decide, by simp [e218cUtil]; norm_num, by simp [e218cUtil]; norm_num⟩

end MWG.SocialChoice

set_option linter.style.longLine false
#print axioms MWG.SocialChoice.Profile
#print axioms MWG.SocialChoice.NoIndifference
#print axioms MWG.SocialChoice.RationalPrefs
#print axioms MWG.SocialChoice.StrictPrefs
#print axioms MWG.SocialChoice.RationalProfiles
#print axioms MWG.SocialChoice.StrictProfiles
#print axioms MWG.SocialChoice.strictPrefs_subset
#print axioms MWG.SocialChoice.strictProfiles_subset
#print axioms MWG.SocialChoice.footnote_21_4
#print axioms MWG.SocialChoice.footnote_21_3_strict
#print axioms MWG.SocialChoice.footnote_21_3_indifferent
#print axioms MWG.SocialChoice.strict_trans
#print axioms MWG.SocialChoice.strict_of_weak_strict
#print axioms MWG.SocialChoice.weak_of_not_strict
#print axioms MWG.SocialChoice.strict_asymm
#print axioms MWG.SocialChoice.IsSWF
#print axioms MWG.SocialChoice.Paretian
#print axioms MWG.SocialChoice.PairwiseIndependent
#print axioms MWG.SocialChoice.IsDictator
#print axioms MWG.SocialChoice.Dictatorial
#print axioms MWG.SocialChoice.restrictPair
#print axioms MWG.SocialChoice.restrictPair_eq_iff
#print axioms MWG.SocialChoice.footnote_21_7
#print axioms MWG.SocialChoice.agree_of_same_ranking
#print axioms MWG.SocialChoice.PairwiseIndependent.strict_transfer
#print axioms MWG.SocialChoice.majorityRel
#print axioms MWG.SocialChoice.majorityRel_iff
#print axioms MWG.SocialChoice.majorityRel_complete
#print axioms MWG.SocialChoice.scorePref
#print axioms MWG.SocialChoice.scorePref_mem
#print axioms MWG.SocialChoice.scorePref_strict_of_lt
#print axioms MWG.SocialChoice.natPref
#print axioms MWG.SocialChoice.natPref_rational
#print axioms MWG.SocialChoice.natPref_mem_strict
#print axioms MWG.SocialChoice.natPref_strict_iff
#print axioms MWG.SocialChoice.natPref_indifferent_iff
#print axioms MWG.SocialChoice.rank3
#print axioms MWG.SocialChoice.rank3_strict
#print axioms MWG.SocialChoice.exists_third
#print axioms MWG.SocialChoice.TwoAltProfiles
#print axioms MWG.SocialChoice.IsTwoAltSWF
#print axioms MWG.SocialChoice.TwoAltParetian
#print axioms MWG.SocialChoice.weightedVoting
#print axioms MWG.SocialChoice.majorityVoting
#print axioms MWG.SocialChoice.signType_cast_cases
#print axioms MWG.SocialChoice.weightedVoting_isSWF
#print axioms MWG.SocialChoice.example_21_B_1
#print axioms MWG.SocialChoice.majorityVoting_eq_weighted
#print axioms MWG.SocialChoice.int_sign_cases
#print axioms MWG.SocialChoice.majorityVoting_isSWF
#print axioms MWG.SocialChoice.nPlus
#print axioms MWG.SocialChoice.nMinus
#print axioms MWG.SocialChoice.sum_eq_nPlus_sub_nMinus
#print axioms MWG.SocialChoice.majorityVoting_spec
#print axioms MWG.SocialChoice.IsTwoAltDictator
#print axioms MWG.SocialChoice.example_21_B_2_paretian
#print axioms MWG.SocialChoice.example_21_B_2
#print axioms MWG.SocialChoice.SymmetricAmongAgents
#print axioms MWG.SocialChoice.NeutralBetweenAlternatives
#print axioms MWG.SocialChoice.PositivelyResponsive
#print axioms MWG.SocialChoice.neg_mem_twoAltProfiles
#print axioms MWG.SocialChoice.exercise_21_B_1_symmetric
#print axioms MWG.SocialChoice.exercise_21_B_1_neutral
#print axioms MWG.SocialChoice.exercise_21_B_1_responsive
#print axioms MWG.SocialChoice.may_tie
#print axioms MWG.SocialChoice.may_plus
#print axioms MWG.SocialChoice.proposition_21_B_1
#print axioms MWG.SocialChoice.exercise_21_B_1
#print axioms MWG.SocialChoice.tiltedVoting
#print axioms MWG.SocialChoice.exercise_21_B_2_symmetry
#print axioms MWG.SocialChoice.xBiasedVoting
#print axioms MWG.SocialChoice.exercise_21_B_2_neutrality
#print axioms MWG.SocialChoice.exercise_21_B_2_responsiveness
#print axioms MWG.SocialChoice.ParetoOptimalNoTransfers
#print axioms MWG.SocialChoice.MajorityDecision
#print axioms MWG.SocialChoice.exercise_21_B_3_pareto_no_transfers
#print axioms MWG.SocialChoice.FeasibleWithTransfers
#print axioms MWG.SocialChoice.ParetoOptimalWithTransfers
#print axioms MWG.SocialChoice.exercise_21_B_3_mean
#print axioms MWG.SocialChoice.exercise_21_B_3_not_pareto_with_transfers
#print axioms MWG.SocialChoice.bordaPoints
#print axioms MWG.SocialChoice.bordaSWF
#print axioms MWG.SocialChoice.example_21_C_1_rational
#print axioms MWG.SocialChoice.bordaPoints_lt
#print axioms MWG.SocialChoice.example_21_C_1_paretian
#print axioms MWG.SocialChoice.bordaPoints_natPref
#print axioms MWG.SocialChoice.example_21_C_1_rank
#print axioms MWG.SocialChoice.footnote_21_6
#print axioms MWG.SocialChoice.bordaSWF_two
#print axioms MWG.SocialChoice.bordaSWF_three
#print axioms MWG.SocialChoice.bordaProfileA
#print axioms MWG.SocialChoice.bordaProfileB
#print axioms MWG.SocialChoice.example_21_C_1_two_agents
#print axioms MWG.SocialChoice.bordaProfileC
#print axioms MWG.SocialChoice.bordaProfileD
#print axioms MWG.SocialChoice.bordaProfileE
#print axioms MWG.SocialChoice.example_21_C_1_three_agents
#print axioms MWG.SocialChoice.majorityRel_natPref
#print axioms MWG.SocialChoice.condorcetProfile
#print axioms MWG.SocialChoice.condorcetProfile_mem
#print axioms MWG.SocialChoice.condorcet_majority
#print axioms MWG.SocialChoice.example_21_C_2
#print axioms MWG.SocialChoice.pairWinner
#print axioms MWG.SocialChoice.agendaWinner
#print axioms MWG.SocialChoice.condorcet_agenda
#print axioms MWG.SocialChoice.StandardDomain
#print axioms MWG.SocialChoice.StandardDomain.score_mem
#print axioms MWG.SocialChoice.StandardDomain.rational
#print axioms MWG.SocialChoice.DecisiveFor
#print axioms MWG.SocialChoice.Decisive
#print axioms MWG.SocialChoice.CompletelyDecisiveFor
#print axioms MWG.SocialChoice.arrow_step_1
#print axioms MWG.SocialChoice.exercise_21_C_1
#print axioms MWG.SocialChoice.arrow_step_2
#print axioms MWG.SocialChoice.arrow_step_3
#print axioms MWG.SocialChoice.arrow_step_4
#print axioms MWG.SocialChoice.arrow_step_5
#print axioms MWG.SocialChoice.arrow_empty_not_decisive
#print axioms MWG.SocialChoice.arrow_step_6
#print axioms MWG.SocialChoice.arrow_step_7
#print axioms MWG.SocialChoice.arrow_step_8
#print axioms MWG.SocialChoice.pairTop
#print axioms MWG.SocialChoice.arrow_step_9
#print axioms MWG.SocialChoice.arrow_step_10
#print axioms MWG.SocialChoice.proposition_21_C_1
#print axioms MWG.SocialChoice.dictatorSWF
#print axioms MWG.SocialChoice.dictatorSWF_spec
#print axioms MWG.SocialChoice.proposition_21_C_1_nonvacuous
#print axioms MWG.SocialChoice.Quasitransitive
#print axioms MWG.SocialChoice.Acyclic
#print axioms MWG.SocialChoice.AcyclicAsPrinted
#print axioms MWG.SocialChoice.acyclic_as_printed_false
#print axioms MWG.SocialChoice.footnote_21_9_acyclic
#print axioms MWG.SocialChoice.rational_quasitransitive
#print axioms MWG.SocialChoice.rational_acyclic
#print axioms MWG.SocialChoice.oligarchyRel
#print axioms MWG.SocialChoice.example_21_D_1_strict
#print axioms MWG.SocialChoice.exercise_21_D_2_quasitransitive
#print axioms MWG.SocialChoice.example_21_D_1_paretian_independent
#print axioms MWG.SocialChoice.example_21_D_1_extremes
#print axioms MWG.SocialChoice.example_21_D_1_not_dictatorial
#print axioms MWG.SocialChoice.exercise_21_D_2_not_transitive
#print axioms MWG.SocialChoice.vetoRel
#print axioms MWG.SocialChoice.vetoRel_strict
#print axioms MWG.SocialChoice.exercise_21_D_3_acyclic
#print axioms MWG.SocialChoice.exercise_21_D_3_not_quasitransitive
#print axioms MWG.SocialChoice.condorcet_not_acyclic
#print axioms MWG.SocialChoice.cyclicRel
#print axioms MWG.SocialChoice.exercise_21_D_1
#print axioms MWG.SocialChoice.IsLinearOrderRel
#print axioms MWG.SocialChoice.linearOrderRel_of_linearOrder
#print axioms MWG.SocialChoice.linearOrderRel_dual
#print axioms MWG.SocialChoice.example_21_D_3
#print axioms MWG.SocialChoice.linearOrderOfRel
#print axioms MWG.SocialChoice.IsPeak
#print axioms MWG.SocialChoice.SinglePeaked
#print axioms MWG.SocialChoice.IsPeak.strict_best
#print axioms MWG.SocialChoice.IsPeak.unique
#print axioms MWG.SocialChoice.SinglePeakedPrefs
#print axioms MWG.SocialChoice.StrictSinglePeakedPrefs
#print axioms MWG.SocialChoice.SinglePeakedProfiles
#print axioms MWG.SocialChoice.StrictSinglePeakedProfiles
#print axioms MWG.SocialChoice.strictSinglePeaked_subset
#print axioms MWG.SocialChoice.strictSinglePeaked_subset_strict
#print axioms MWG.SocialChoice.IsCondorcetWinner
#print axioms MWG.SocialChoice.IsMedianAgent
#print axioms MWG.SocialChoice.median_exists
#print axioms MWG.SocialChoice.median_odd_unique
#print axioms MWG.SocialChoice.majority_of_supporters
#print axioms MWG.SocialChoice.proposition_21_D_1
#print axioms MWG.SocialChoice.proposition_21_D_1_exists
#print axioms MWG.SocialChoice.IsPeak.restrict
#print axioms MWG.SocialChoice.strict_singlePeaked_condorcet_finset
#print axioms MWG.SocialChoice.tieBreak
#print axioms MWG.SocialChoice.tieBreak_spec
#print axioms MWG.SocialChoice.doubleProfile
#print axioms MWG.SocialChoice.doubleProfile_card
#print axioms MWG.SocialChoice.majorityRel_doubleProfile
#print axioms MWG.SocialChoice.doubleProfile_mem
#print axioms MWG.SocialChoice.majorityRel_acyclic
#print axioms MWG.SocialChoice.strict_majority_odd
#print axioms MWG.SocialChoice.proposition_21_D_2
#print axioms MWG.SocialChoice.three_middle
#print axioms MWG.SocialChoice.IsPeak.middle_not_worst
#print axioms MWG.SocialChoice.exercise_21_D_5
#print axioms MWG.SocialChoice.natPref_singlePeaked_of_isPeak
#print axioms MWG.SocialChoice.exercise21D6Profile
#print axioms MWG.SocialChoice.exercise_21_D_6
#print axioms MWG.SocialChoice.oligarchyMajority
#print axioms MWG.SocialChoice.exercise_21_D_11_oligarchy
#print axioms MWG.SocialChoice.phantomUtil
#print axioms MWG.SocialChoice.withPhantoms
#print axioms MWG.SocialChoice.phantomMajority
#print axioms MWG.SocialChoice.phantom_mem
#print axioms MWG.SocialChoice.phantomTestA
#print axioms MWG.SocialChoice.phantomTestB
#print axioms MWG.SocialChoice.exercise_21_D_11
#print axioms MWG.SocialChoice.majorityRel_paretian
#print axioms MWG.SocialChoice.majorityRel_independent
#print axioms MWG.SocialChoice.majorityRel_not_dictatorial
#print axioms MWG.SocialChoice.splitProfile
#print axioms MWG.SocialChoice.exercise_21_C_2a
#print axioms MWG.SocialChoice.exercise_21_C_2b
#print axioms MWG.SocialChoice.exercise_21_C_2c
#print axioms MWG.SocialChoice.exercise_21_C_2d
#print axioms MWG.SocialChoice.totalIndifference
#print axioms MWG.SocialChoice.exercise_21_C_2e
#print axioms MWG.SocialChoice.exercise_21_C_2f
#print axioms MWG.SocialChoice.lexRel
#print axioms MWG.SocialChoice.exercise_21_C_3_rational
#print axioms MWG.SocialChoice.exercise_21_C_3_arrow
#print axioms MWG.SocialChoice.exercise_21_C_3_not_identical
#print axioms MWG.SocialChoice.WeaklyParetian
#print axioms MWG.SocialChoice.MaintainsPosition
#print axioms MWG.SocialChoice.lowerContour
#print axioms MWG.SocialChoice.maintainsPosition_iff
#print axioms MWG.SocialChoice.Monotonic
#print axioms MWG.SocialChoice.IsSCFDictator
#print axioms MWG.SocialChoice.DictatorialSCF
#print axioms MWG.SocialChoice.induced_scf_exists
#print axioms MWG.SocialChoice.induced_scf_condorcet
#print axioms MWG.SocialChoice.TakesToTop
#print axioms MWG.SocialChoice.topProfile
#print axioms MWG.SocialChoice.topProfile_spec
#print axioms MWG.SocialChoice.TakesToTop.maintains
#print axioms MWG.SocialChoice.TakesToTop.trans
#print axioms MWG.SocialChoice.definition_21_E_6_example
#print axioms MWG.SocialChoice.WeaklyParetian.mem_top
#print axioms MWG.SocialChoice.scf_step_1
#print axioms MWG.SocialChoice.scfRelation
#print axioms MWG.SocialChoice.scf_step_2
#print axioms MWG.SocialChoice.StandardDomain.topProfile_mem
#print axioms MWG.SocialChoice.scf_choice_pair
#print axioms MWG.SocialChoice.scf_not_chosen
#print axioms MWG.SocialChoice.scf_step_3
#print axioms MWG.SocialChoice.exercise_21_E_3
#print axioms MWG.SocialChoice.scf_step_4
#print axioms MWG.SocialChoice.scf_step_5
#print axioms MWG.SocialChoice.scf_step_6
#print axioms MWG.SocialChoice.proposition_21_E_1
#print axioms MWG.SocialChoice.dictatorial_strict_spec
#print axioms MWG.SocialChoice.smallestTopLabel
#print axioms MWG.SocialChoice.smallestTopLabel_spec
#print axioms MWG.SocialChoice.exercise_21_E_2_dictatorial
#print axioms MWG.SocialChoice.exercise_21_E_2_not_monotonic
#print axioms MWG.SocialChoice.exercise_21_E_2_strict
#print axioms MWG.SocialChoice.NoIncentiveToMisrepresent
#print axioms MWG.SocialChoice.no_incentive_step
#print axioms MWG.SocialChoice.monotonic_of_noIncentive
#print axioms MWG.SocialChoice.proposition_21_E_2
#print axioms MWG.SocialChoice.smallestTopLabel_noIncentive
#print axioms MWG.SocialChoice.condorcetWinner_unique
#print axioms MWG.SocialChoice.condorcetSCF
#print axioms MWG.SocialChoice.exercise_21_E_1
#print axioms MWG.SocialChoice.parityRule
#print axioms MWG.SocialChoice.exercise_21_E_4_two
#print axioms MWG.SocialChoice.e214A
#print axioms MWG.SocialChoice.e214B
#print axioms MWG.SocialChoice.e214F
#print axioms MWG.SocialChoice.exercise_21_E_4_three
#print axioms MWG.SocialChoice.iccComb
#print axioms MWG.SocialChoice.StrictlyConvexPref
#print axioms MWG.SocialChoice.ContinuousPref
#print axioms MWG.SocialChoice.exercise_21_D_4
#print axioms MWG.SocialChoice.exists_max_of_continuousPref
#print axioms MWG.SocialChoice.example_21_D_4_sufficiency
#print axioms MWG.SocialChoice.example_21_D_4
#print axioms MWG.SocialChoice.example_21_D_4_empty
#print axioms MWG.SocialChoice.strictlyConvex_of_strictQuasiconcave
#print axioms MWG.SocialChoice.TaxRates
#print axioms MWG.SocialChoice.wealthPref
#print axioms MWG.SocialChoice.wealthPref_iff
#print axioms MWG.SocialChoice.wealthPref_strict_iff
#print axioms MWG.SocialChoice.wealthPref_rational
#print axioms MWG.SocialChoice.isPeak_zero
#print axioms MWG.SocialChoice.isPeak_one
#print axioms MWG.SocialChoice.wealthB
#print axioms MWG.SocialChoice.exercise_21_D_10b_singlePeaked
#print axioms MWG.SocialChoice.exercise_21_D_10b_mean_agent
#print axioms MWG.SocialChoice.exercise_21_D_10b_condorcet
#print axioms MWG.SocialChoice.wealthC
#print axioms MWG.SocialChoice.peakC
#print axioms MWG.SocialChoice.peakC_mem
#print axioms MWG.SocialChoice.peakCRate
#print axioms MWG.SocialChoice.exercise_21_D_10c_singlePeaked
#print axioms MWG.SocialChoice.peakC_antitone
#print axioms MWG.SocialChoice.exercise_21_D_10c
#print axioms MWG.SocialChoice.wealthD
#print axioms MWG.SocialChoice.wealthD_strictQuasiconcave
#print axioms MWG.SocialChoice.exercise_21_D_10d
#print axioms MWG.SocialChoice.e2114
#print axioms MWG.SocialChoice.exercise_21_D_14a
#print axioms MWG.SocialChoice.WeaklySinglePeaked
#print axioms MWG.SocialChoice.exercise_21_D_14b
#print axioms MWG.SocialChoice.e2114u
#print axioms MWG.SocialChoice.e2114pos
#print axioms MWG.SocialChoice.quasiconcaveOn_of_unimodal
#print axioms MWG.SocialChoice.exercise_21_D_14_quasiconcave
#print axioms MWG.SocialChoice.exercise_21_D_14c
#print axioms MWG.SocialChoice.e2114Defeats
#print axioms MWG.SocialChoice.exercise_21_D_14d
#print axioms MWG.SocialChoice.ex21D5u
#print axioms MWG.SocialChoice.unitSquare
#print axioms MWG.SocialChoice.example_21_D_5_i
#print axioms MWG.SocialChoice.example_21_D_5_ii
#print axioms MWG.SocialChoice.example_21_D_5_iii
#print axioms MWG.SocialChoice.example_21_D_5
#print axioms MWG.SocialChoice.example_21_D_5_unique_max
#print axioms MWG.SocialChoice.example_21_D_5_cone
#print axioms MWG.SocialChoice.taxShares
#print axioms MWG.SocialChoice.taxDefeats
#print axioms MWG.SocialChoice.taxDefeats_iff
#print axioms MWG.SocialChoice.exercise_21_D_12a
#print axioms MWG.SocialChoice.exercise_21_D_12b_one_zero
#print axioms MWG.SocialChoice.exercise_21_D_12b_one_payer
#print axioms MWG.SocialChoice.euclidPref
#print axioms MWG.SocialChoice.euclidPref_spec
#print axioms MWG.SocialChoice.euclidPref_injective
#print axioms MWG.SocialChoice.prefRegion
#print axioms MWG.SocialChoice.strict_euclidPref_iff
#print axioms MWG.SocialChoice.mem_prefRegion_iff
#print axioms MWG.SocialChoice.prefRegion_eq_halfspace
#print axioms MWG.SocialChoice.bisector_iff
#print axioms MWG.SocialChoice.openHalfSpace
#print axioms MWG.SocialChoice.measurableSet_openHalfSpace
#print axioms MWG.SocialChoice.IsMedianPoint
#print axioms MWG.SocialChoice.IsCondorcetWinnerMeasure
#print axioms MWG.SocialChoice.disjoint_openHalfSpace
#print axioms MWG.SocialChoice.disjoint_prefRegion
#print axioms MWG.SocialChoice.isMedianPoint_iff_book
#print axioms MWG.SocialChoice.example_21_D_6
#print axioms MWG.SocialChoice.isMedianPoint_of_symmetric
#print axioms MWG.SocialChoice.measurePreserving_reflect
#print axioms MWG.SocialChoice.rectangle
#print axioms MWG.SocialChoice.figure_21_D_8a
#print axioms MWG.SocialChoice.figure_21_D_8a_center
#print axioms MWG.SocialChoice.Intermediate
#print axioms MWG.SocialChoice.exercise_21_D_9a
#print axioms MWG.SocialChoice.linParamUtil
#print axioms MWG.SocialChoice.exercise_21_D_9b
#print axioms MWG.SocialChoice.exercise_21_D_9c
#print axioms MWG.SocialChoice.e219Family
#print axioms MWG.SocialChoice.exercise_21_D_9c_counterexample
#print axioms MWG.SocialChoice.exercise_21_D_9d_exists
#print axioms MWG.SocialChoice.exercise_21_D_9e
#print axioms MWG.SocialChoice.exercise_21_D_9f
#print axioms MWG.SocialChoice.exercise_21_D_9f_intermediate
#print axioms MWG.SocialChoice.exercise_21_D_9e_instance
#print axioms MWG.SocialChoice.typeMass
#print axioms MWG.SocialChoice.IsTypeCondorcetWinner
#print axioms MWG.SocialChoice.eventually_small_step
#print axioms MWG.SocialChoice.condorcet_halfplane
#print axioms MWG.SocialChoice.complex_inner_eq
#print axioms MWG.SocialChoice.exists_generic_direction
#print axioms MWG.SocialChoice.exercise_21_D_13a
#print axioms MWG.SocialChoice.exercise_21_D_13a_even
#print axioms MWG.SocialChoice.inner_I_mul
#print axioms MWG.SocialChoice.collinear_of_orth
#print axioms MWG.SocialChoice.GeneralPosition
#print axioms MWG.SocialChoice.exercise_21_D_13b
#print axioms MWG.SocialChoice.TwoAgentsPrefer
#print axioms MWG.SocialChoice.eventually_gradient_lt
#print axioms MWG.SocialChoice.area_antisymm
#print axioms MWG.SocialChoice.area_self
#print axioms MWG.SocialChoice.cone_directions
#print axioms MWG.SocialChoice.exercise_21_D_7a
#print axioms MWG.SocialChoice.exercise_21_D_7b
#print axioms MWG.SocialChoice.exercise_21_D_7b_zero
#print axioms MWG.SocialChoice.IsDirectionalMedian
#print axioms MWG.SocialChoice.exercise_21_D_8c
#print axioms MWG.SocialChoice.exercise_21_D_8c_instance
#print axioms MWG.SocialChoice.proposition_21_D_1_instance
#print axioms MWG.SocialChoice.example_21_D_6_instance
#print axioms MWG.SocialChoice.hasGradientAt_inner_const
#print axioms MWG.SocialChoice.exercise_21_D_7_instance
#print axioms MWG.SocialChoice.exercise_21_D_13a_instance
#print axioms MWG.SocialChoice.exercise_21_D_13b_instance
#print axioms MWG.SocialChoice.isMedianPoint_of_affine_image
#print axioms MWG.SocialChoice.stdTriangle
#print axioms MWG.SocialChoice.triangle_coords_measurePreserving
#print axioms MWG.SocialChoice.triangle_strip_volume
#print axioms MWG.SocialChoice.stdTriangle_eq_preimage
#print axioms MWG.SocialChoice.stdTriangle_median_coord
#print axioms MWG.SocialChoice.triSwapLin
#print axioms MWG.SocialChoice.triShearLin
#print axioms MWG.SocialChoice.triSwapLin_involutive
#print axioms MWG.SocialChoice.triShearLin_involutive
#print axioms MWG.SocialChoice.stdTriangle_median_three
#print axioms MWG.SocialChoice.figure_21_D_8b
#print axioms MWG.SocialChoice.figure_21_D_8b_affine
#print axioms MWG.SocialChoice.exercise_21_D_9d_not_exists
#print axioms MWG.SocialChoice.ConeContainsHalfSpace
#print axioms MWG.SocialChoice.dm_three_term
#print axioms MWG.SocialChoice.dm_binet_cauchy
#print axioms MWG.SocialChoice.dm_not_median
#print axioms MWG.SocialChoice.dm_spans_of_relation
#print axioms MWG.SocialChoice.dm_median_or_spans
#print axioms MWG.SocialChoice.dm_spans_no_median
#print axioms MWG.SocialChoice.exercise_21_D_8a_iff
#print axioms MWG.SocialChoice.exercise_21_D_8a
#print axioms MWG.SocialChoice.not_coneContainsHalfSpace_of_pos
#print axioms MWG.SocialChoice.exercise_21_D_8a_instance
#print axioms MWG.SocialChoice.IsGlobalDirectionalMedian
#print axioms MWG.SocialChoice.e218aUtil
#print axioms MWG.SocialChoice.exercise_21_D_8a_global_counterexample
#print axioms MWG.SocialChoice.e218bPeak
#print axioms MWG.SocialChoice.e218bUtil
#print axioms MWG.SocialChoice.e218bGrad
#print axioms MWG.SocialChoice.e218bUtil_eq
#print axioms MWG.SocialChoice.e218bUtil_concave
#print axioms MWG.SocialChoice.e218bUtil_hasGradientAt
#print axioms MWG.SocialChoice.exercise_21_D_8b
#print axioms MWG.SocialChoice.exercise_21_D_8c_global
#print axioms MWG.SocialChoice.exercise_21_D_8c_global_instance
#print axioms MWG.SocialChoice.e218c_hasDerivAt_sqPos
#print axioms MWG.SocialChoice.e218cUtil
#print axioms MWG.SocialChoice.e218cGrad
#print axioms MWG.SocialChoice.exercise_21_D_8c_counterexample
