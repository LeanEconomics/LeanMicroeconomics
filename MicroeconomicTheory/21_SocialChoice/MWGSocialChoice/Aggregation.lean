/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPreferenceChoice.PreferenceRelations
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Fintype.Card

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
