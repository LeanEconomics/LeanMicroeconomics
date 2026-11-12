import ChoicePreferenceUtility.FiniteUtility
import ChoicePreferenceUtility.UtilityEquivalence
import ChoicePreferenceUtility.Lexicographic
import ChoicePreferenceUtility.Basic
import ChoicePreferenceUtility.Rationalization
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preference relations and utility functions

MWG, Section 1.B, pp. 6-9, and Exercises 1.B.1-1.B.5, p. 15.

A preference relation on `X` is a binary relation `r : X → X → Prop`, read `r x y` as
"`x` is at least as good as `y`". The strict preference and indifference relations, and the
notions *complete*, *transitive*, *rational* and *utility representation*, are exactly those
of Kreps Chapter 1 (`Kreps.ChoicePreferenceUtility`), whose orientation agrees with MWG's;
`definition_1_B_1` and `definition_1_B_2` record that they are MWG's Definitions 1.B.1 and
1.B.2. The section proves Proposition 1.B.1 (i)-(iii), footnote 2 (completeness implies
reflexivity), Proposition 1.B.2, the transitivity failures in the small-type discussion
(just perceptible differences, framing, the Condorcet paradox, change of tastes), the
ordinal/cardinal remark (utility differences are not ordinal), the remark that not every
rational relation has a utility representation (via Kreps Problem 1.10), and Exercises
1.B.1-1.B.5. No departures from the book.
-/

namespace MWG.PreferenceChoice

open Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- **Definition 1.B.1** (MWG, p. 6). A preference relation is *rational* if it is complete
(`∀ x y, x ≿ y ∨ y ≿ x`) and transitive. Kreps's `Rational` is this notion. -/
theorem definition_1_B_1 (r : X → X → Prop) :
    Rational r ↔ (∀ x y, r x y ∨ r y x) ∧ (∀ x y z, r x y → r y z → r x z) :=
  Iff.rfl

/-- **Section 1.B** (MWG, p. 6). The strict preference `x ≻ y` holds iff `x ≿ y` but not
`y ≿ x`; this is Kreps's `Strict`. -/
theorem strict_iff (r : X → X → Prop) (x y : X) : Strict r x y ↔ r x y ∧ ¬r y x :=
  Iff.rfl

/-- **Section 1.B** (MWG, p. 6). Indifference `x ∼ y` holds iff `x ≿ y` and `y ≿ x`; this is
Kreps's `Indifferent`. -/
theorem indifferent_iff (r : X → X → Prop) (x y : X) :
    Indifferent r x y ↔ r x y ∧ r y x :=
  Iff.rfl

/-- **Footnote 2** (MWG, p. 6). Reflexivity is implied by completeness. -/
theorem footnote_1_2 {r : X → X → Prop} (hc : Complete r) (x : X) : r x x :=
  complete_refl hc x

/-- **Proposition 1.B.1(i)** (MWG, p. 7). For rational `≿`, strict preference is irreflexive
and transitive. -/
theorem proposition_1_B_1_i {r : X → X → Prop} (hr : Rational r) :
    (∀ x, ¬Strict r x x) ∧ (∀ x y z, Strict r x y → Strict r y z → Strict r x z) := by
  refine ⟨fun x h => h.2 h.1, fun x y z hxy hyz => ⟨hr.2 x y z hxy.1 hyz.1, fun hzx => ?_⟩⟩
  exact hyz.2 (hr.2 z x y hzx hxy.1)

/-- **Proposition 1.B.1(ii)** (MWG, p. 7). For rational `≿`, indifference is reflexive,
transitive and symmetric. -/
theorem proposition_1_B_1_ii {r : X → X → Prop} (hr : Rational r) :
    (∀ x, Indifferent r x x) ∧
      (∀ x y z, Indifferent r x y → Indifferent r y z → Indifferent r x z) ∧
      (∀ x y, Indifferent r x y → Indifferent r y x) := by
  refine ⟨fun x => ⟨complete_refl hr.1 x, complete_refl hr.1 x⟩, ?_, ?_⟩
  · exact fun x y z hxy hyz => ⟨hr.2 x y z hxy.1 hyz.1, hr.2 z y x hyz.2 hxy.2⟩
  · exact fun x y h => ⟨h.2, h.1⟩

/-- **Proposition 1.B.1(iii)** (MWG, p. 7). For rational `≿`, `x ≻ y ≿ z` implies `x ≻ z`. -/
theorem proposition_1_B_1_iii {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨hr.2 x y z hxy.1 hyz, fun hzx => hxy.2 (hr.2 y z x hyz hzx)⟩

/-- **Exercise 1.B.1** (MWG, p. 15). Property (iii) of Proposition 1.B.1. -/
theorem exercise_1_B_1 {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  proposition_1_B_1_iii hr hxy hyz

/-- **Exercise 1.B.2** (MWG, p. 15). Properties (i) and (ii) of Proposition 1.B.1. -/
theorem exercise_1_B_2 {r : X → X → Prop} (hr : Rational r) :
    ((∀ x, ¬Strict r x x) ∧ (∀ x y z, Strict r x y → Strict r y z → Strict r x z)) ∧
      ((∀ x, Indifferent r x x) ∧
        (∀ x y z, Indifferent r x y → Indifferent r y z → Indifferent r x z) ∧
        (∀ x y, Indifferent r x y → Indifferent r y x)) :=
  ⟨proposition_1_B_1_i hr, proposition_1_B_1_ii hr⟩

/-- **Section 1.B** (MWG, pp. 7-8). A rational relation has no strict cycle
`x ≻ y ≻ z ≻ x`; this is the common form of the intransitivities discussed in small type. -/
theorem prefRel_no_strict_cycle {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : Strict r x y) (hyz : Strict r y z) : ¬Strict r z x := fun hzx =>
  (proposition_1_B_1_i hr).1 x ((proposition_1_B_1_i hr).2 x z x
    ((proposition_1_B_1_i hr).2 x y z hxy hyz) hzx)

/-- **Section 1.B, just perceptible differences** (MWG, p. 7). Shades are real numbers and a
shade is at least as good as another unless it is darker by more than the perception
threshold `δ > 0`. Shades `0` and `δ`, and `δ` and `2δ`, are indifferent, but `2δ` is
strictly preferred to `0`, so the relation is not transitive. -/
theorem prefRel_just_perceptible {δ : ℝ} (hδ : 0 < δ) :
    let r : ℝ → ℝ → Prop := fun a b => b - a ≤ δ
    Indifferent r 0 δ ∧ Indifferent r δ (2 * δ) ∧ Strict r (2 * δ) 0 ∧ ¬TransitivePref r := by
  intro r
  have h1 : Indifferent r 0 δ := ⟨by simp [r], by simp [r]; linarith⟩
  have h2 : Indifferent r δ (2 * δ) := ⟨by simp [r]; linarith, by simp [r]; linarith⟩
  have h3 : Strict r (2 * δ) 0 := ⟨by simp [r]; linarith, by simp [r]; linarith⟩
  exact ⟨h1, h2, h3, fun ht => h3.2 (ht 0 δ (2 * δ) h1.1 h2.1)⟩

/-- **Section 1.B, framing** (MWG, p. 8). The answers `x ≻ z`, `z ≻ y` and `x ∼ y` are not
consistent with any rational (indeed any transitive) preference relation. -/
theorem prefRel_framing {r : X → X → Prop} (ht : TransitivePref r) {x y z : X}
    (hxz : Strict r x z) (hzy : Strict r z y) : ¬Indifferent r x y := fun hxy =>
  hzy.2 (ht y x z hxy.2 hxz.1)

/-- The three rational member preferences of the Condorcet example (MWG, p. 8), on the
alternatives opera `0`, rock concert `1`, ice show `2`, as rank utilities (higher is better):
Mom `O ≻ R ≻ I`, Dad `I ≻ O ≻ R`, Child `R ≻ I ≻ O`. -/
def condorcetRank (i a : Fin 3) : ℕ :=
  ![![2, 1, 0], ![1, 0, 2], ![0, 2, 1]] i a

/-- Household majority preference: `a` beats `b` when at least two members strictly prefer
`a` to `b`. -/
def condorcetMajority (a b : Fin 3) : Prop :=
  2 ≤ (Finset.univ.filter fun i => condorcetRank i b < condorcetRank i a).card

/-- **Section 1.B, Condorcet paradox** (MWG, p. 8). Each member's preference is rational, but
majority voting gives `O ≻ R`, `R ≻ I` and `I ≻ O`, so no rational household preference
`≿` can have these as its strict preferences. -/
theorem prefRel_condorcet :
    (∀ i, Rational (UtilityPref fun a => (condorcetRank i a : ℝ))) ∧
      condorcetMajority 0 1 ∧ condorcetMajority 1 2 ∧ condorcetMajority 2 0 ∧
      ∀ r : Fin 3 → Fin 3 → Prop, Rational r →
        ¬(Strict r 0 1 ∧ Strict r 1 2 ∧ Strict r 2 0) := by
  refine ⟨fun i => Kreps.ChoicePreferenceUtility.proposition_1_3a _, ?_, ?_, ?_, ?_⟩
  · unfold condorcetMajority condorcetRank; decide
  · unfold condorcetMajority condorcetRank; decide
  · unfold condorcetMajority condorcetRank; decide
  · rintro r hr ⟨h01, h12, h20⟩
    exact prefRel_no_strict_cycle hr h01 h12 h20

/-- **Section 1.B, change of tastes** (MWG, p. 8). Initially `x ≻ y ≻ z`; after choosing `x`
the tastes become `z ≻ x ≻ y`. The observed pairwise strict rankings `x ≻ y`, `y ≻ z` (old
tastes) and `z ≻ x` (new tastes) cannot all be strict preferences of one rational relation. -/
theorem prefRel_change_of_tastes {r : X → X → Prop} (hr : Rational r) {x y z : X}
    (hxy : Strict r x y) (hyz : Strict r y z) : ¬Strict r z x :=
  prefRel_no_strict_cycle hr hxy hyz

/-- **Definition 1.B.2** (MWG, p. 9). `u : X → ℝ` represents `≿` if `x ≿ y ↔ u x ≥ u y` for
all `x, y`; this is Kreps's `Represents`. -/
theorem definition_1_B_2 (u : X → ℝ) (r : X → X → Prop) :
    Represents u r ↔ ∀ x y, r x y ↔ u x ≥ u y :=
  Iff.rfl

/-- **Exercise 1.B.3** (MWG, p. 15; claim on p. 9). If `f : ℝ → ℝ` is strictly increasing and
`u` represents `≿`, then `v = f ∘ u` represents `≿`. -/
theorem exercise_1_B_3 {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r) {f : ℝ → ℝ}
    (hf : StrictMono f) : Represents (fun x => f (u x)) r :=
  proposition_1_20 hu hf

/-- **Section 1.B** (MWG, p. 9). Utility differences are cardinal, not ordinal: with
`u = id` on `ℝ` and the strictly increasing `f t = t ^ 3`, the alternatives `0, 2, 3` have
`u 2 - u 0 > u 3 - u 2` but `f (u 2) - f (u 0) < f (u 3) - f (u 2)`. -/
theorem prefRel_differences_not_ordinal :
    StrictMono (fun t : ℝ => t ^ 3) ∧ ((2 : ℝ) - 0 > 3 - 2) ∧
      ((2 : ℝ) ^ 3 - 0 ^ 3 < 3 ^ 3 - 2 ^ 3) :=
  ⟨Odd.strictMono_pow (by decide), by norm_num, by norm_num⟩

/-- **Proposition 1.B.2** (MWG, p. 9). A preference relation that can be represented by a
utility function is rational. -/
theorem proposition_1_B_2 {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r) :
    Rational r := by
  refine ⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩
  · rcases le_total (u y) (u x) with h | h
    · exact Or.inl ((hu x y).mpr h)
    · exact Or.inr ((hu y x).mpr h)
  · exact (hu x z).mpr (le_trans ((hu y z).mp hyz) ((hu x y).mp hxy))

/-- **Section 1.B** (MWG, p. 9; example in Section 3.G). Not every rational preference
relation has a utility representation: the lexicographic order on `[0,1] × [0,1]`
(Kreps, Problem 1.10). -/
theorem prefRel_rational_not_representable :
    ∃ (Y : Type) (r : Y → Y → Prop), Rational r ∧ ¬∃ u : Y → ℝ, Represents u r :=
  ⟨_, _, problem_1_10⟩

/-- **Exercise 1.B.4** (MWG, p. 15). If `u x = u y` implies `x ∼ y`, and `u x > u y` implies
`x ≻ y`, then `u` represents `≿`. The book assumes `≿` rational; the proof does not use it
(rationality then follows from Proposition 1.B.2). -/
theorem exercise_1_B_4 {r : X → X → Prop} {u : X → ℝ}
    (heq : ∀ x y, u x = u y → Indifferent r x y) (hgt : ∀ x y, u x > u y → Strict r x y) :
    Represents u r := by
  intro x y
  constructor
  · intro hxy
    by_contra h
    exact (hgt y x (lt_of_not_ge h)).2 hxy
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (hgt x y h).1
    · exact (heq x y h.symm).1

/-- **Exercise 1.B.5** (MWG, p. 15; claim on p. 9). If `X` is finite and `≿` is rational, then
some `u : X → ℝ` represents `≿` (Kreps, Proposition 1.8: `u x` is the number of alternatives
`x` is at least as good as). -/
theorem exercise_1_B_5 [Finite X] {r : X → X → Prop} (hr : Rational r) :
    ∃ u : X → ℝ, Represents u r :=
  ⟨FiniteUtility r, proposition_1_8 hr⟩

end MWG.PreferenceChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Choice rules and the weak axiom

MWG, Section 1.C, pp. 9-11, and Exercises 1.C.1-1.C.3, p. 15.

A choice structure `(𝓑, C(·))` is MWG's own notion: a family `𝓑` of nonempty budget sets
(which need not contain every subset of `X`) and a choice rule assigning to each `B ∈ 𝓑` a
nonempty `C(B) ⊆ B`. The values of `C` off `𝓑` play no role. We define the weak axiom of
revealed preference (Definition 1.C.1), the revealed preference relation `≿*`
(Definition 1.C.2) and "revealed preferred", prove the restatement of the weak axiom,
Examples 1.C.1-1.C.2, footnote 5, that `≿*` need be neither complete nor transitive, and
Exercises 1.C.1-1.C.3. The bridge `weakAxiom_iff_coherentOn` shows that the weak axiom is
Kreps's choice coherence on the budget family. No departures from the book.
-/

namespace MWG.PreferenceChoice

open Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- **Section 1.C** (MWG, pp. 9-10). A choice structure `(𝓑, C(·))`: a family `budgets` of
nonempty subsets of `X` and a choice rule `C` with `∅ ≠ C(B) ⊆ B` for every `B ∈ 𝓑`. -/
structure ChoiceStructure (X : Type*) where
  /-- The family `𝓑` of budget sets. -/
  budgets : Set (Set X)
  /-- The choice rule `C(·)`. -/
  C : Set X → Set X
  /-- Every budget set is nonempty. -/
  budget_nonempty : ∀ B ∈ budgets, B.Nonempty
  /-- Chosen elements are feasible. -/
  choice_subset : ∀ B ∈ budgets, C B ⊆ B
  /-- Something is chosen from every budget set. -/
  choice_nonempty : ∀ B ∈ budgets, (C B).Nonempty

/-- **Definition 1.C.1** (MWG, p. 10). The weak axiom of revealed preference: if `x, y ∈ B`,
`x ∈ C(B)`, and `x, y ∈ B'`, `y ∈ C(B')`, for `B, B' ∈ 𝓑`, then `x ∈ C(B')`. -/
def WeakAxiom (S : ChoiceStructure X) : Prop :=
  ∀ B ∈ S.budgets, ∀ B' ∈ S.budgets, ∀ x y, x ∈ B → y ∈ B → x ∈ S.C B →
    x ∈ B' → y ∈ B' → y ∈ S.C B' → x ∈ S.C B'

/-- **Definition 1.C.2** (MWG, p. 11). The revealed preference relation `x ≿* y`: some
`B ∈ 𝓑` has `x, y ∈ B` and `x ∈ C(B)`. -/
def RevealedPref (S : ChoiceStructure X) (x y : X) : Prop :=
  ∃ B ∈ S.budgets, x ∈ B ∧ y ∈ B ∧ x ∈ S.C B

/-- **Section 1.C** (MWG, p. 11). `x` is revealed preferred to `y` (`x ≻* y`, Exercise 1.C.3):
some `B ∈ 𝓑` has `x, y ∈ B`, `x ∈ C(B)` and `y ∉ C(B)`. -/
def RevealedStrict (S : ChoiceStructure X) (x y : X) : Prop :=
  ∃ B ∈ S.budgets, x ∈ B ∧ y ∈ B ∧ x ∈ S.C B ∧ y ∉ S.C B

/-- **Exercise 1.C.3** (MWG, p. 15). The second candidate `x ≻** y`: `x ≿* y` but not
`y ≿* x`. -/
def RevealedStrict' (S : ChoiceStructure X) (x y : X) : Prop :=
  RevealedPref S x y ∧ ¬RevealedPref S y x

/-- **Section 1.C** (MWG, p. 11). Restatement of the weak axiom: if `x` is revealed at least as
good as `y`, then `y` cannot be revealed preferred to `x`. -/
theorem weakAxiom_iff_revealed (S : ChoiceStructure X) :
    WeakAxiom S ↔ ∀ x y, RevealedPref S x y → ¬RevealedStrict S y x := by
  constructor
  · rintro h x y ⟨B, hB, hx, hy, hxC⟩ ⟨B', hB', hy', hx', hyC, hxC'⟩
    exact hxC' (h B hB B' hB' x y hx hy hxC hx' hy' hyC)
  · intro h B hB B' hB' x y hx hy hxC hx' hy' hyC
    by_contra hxC'
    exact h x y ⟨B, hB, hx, hy, hxC⟩ ⟨B', hB', hy', hx', hyC, hxC'⟩

/-- Bridge to Kreps (Definition 1.1b): the weak axiom is Kreps's coherence of `C` on the
budget family `𝓑`. -/
theorem weakAxiom_iff_coherentOn (S : ChoiceStructure X) :
    WeakAxiom S ↔ CoherentOn S.budgets S.C := by
  constructor
  · intro h A hA B hB x hx y hy hxA hyA hyB
    exact hyA (h B hB A hA y x hy.2 hx.2 hyB hy.1 hx.1 hxA)
  · intro h B hB B' hB' x y hx hy hxC hx' hy' hyC
    by_contra hxC'
    exact h B' hB' B hB y ⟨hy', hy⟩ x ⟨hx', hx⟩ hyC hxC' hxC

/-- The choice structure `(𝓑, C(·))` with `X = {x, y, z} = Fin 3` (`x = 0`, `y = 1`, `z = 2`),
`𝓑 = {{x, y}, {x, y, z}}` and the given values on the two budgets. -/
def threeChoice (Cxy Cxyz : Set (Fin 3)) (hxy : Cxy ⊆ {0, 1}) (hxy' : Cxy.Nonempty)
    (hxyz : Cxyz ⊆ {0, 1, 2}) (hxyz' : Cxyz.Nonempty) : ChoiceStructure (Fin 3) where
  budgets := {{0, 1}, {0, 1, 2}}
  C B := if B = {0, 1} then Cxy else Cxyz
  budget_nonempty B hB := by
    rcases hB with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
  choice_subset B hB := by
    rcases hB with rfl | hB
    · simpa using hxy
    · rw [Set.mem_singleton_iff] at hB
      subst hB
      have hne : ({0, 1, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
        have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
        simp at this
      simpa [hne] using hxyz
  choice_nonempty B hB := by
    by_cases h : B = {0, 1}
    · simpa [h] using hxy'
    · simpa [h] using hxyz'

/-- The two budgets of Example 1.C.1 are different. -/
theorem threeChoice_ne : ({0, 1, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
  have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
  simp at this

/-- The choice from `{x, y}` in `threeChoice`. -/
theorem threeChoice_C_xy {Cxy Cxyz : Set (Fin 3)} (a b c d) :
    (threeChoice Cxy Cxyz a b c d).C {0, 1} = Cxy := by
  simp [threeChoice]

/-- The choice from `{x, y, z}` in `threeChoice`. -/
theorem threeChoice_C_xyz {Cxy Cxyz : Set (Fin 3)} (a b c d) :
    (threeChoice Cxy Cxyz a b c d).C {0, 1, 2} = Cxyz := by
  simp [threeChoice, threeChoice_ne]

/-- **Example 1.C.1** (MWG, p. 10). The structure `(𝓑, C₁(·))` with `C₁({x,y}) = {x}` and
`C₁({x,y,z}) = {x}`. -/
def example_1_C_1_C₁ : ChoiceStructure (Fin 3) :=
  threeChoice {0} {0} (by simp) ⟨0, rfl⟩ (by simp) ⟨0, rfl⟩

/-- **Example 1.C.1** (MWG, p. 10). The structure `(𝓑, C₂(·))` with `C₂({x,y}) = {x}` and
`C₂({x,y,z}) = {x, y}`. -/
def example_1_C_1_C₂ : ChoiceStructure (Fin 3) :=
  threeChoice {0} {0, 1} (by simp) ⟨0, rfl⟩ (by
    intro a ha
    rcases ha with rfl | ha
    · simp
    · rw [Set.mem_singleton_iff] at ha
      simp [ha]) ⟨0, by simp⟩

/-- Membership in a budget of the Example 1.C.1 family. -/
theorem threeChoice_budgets {Cxy Cxyz : Set (Fin 3)} (a b c d) (B : Set (Fin 3)) :
    B ∈ (threeChoice Cxy Cxyz a b c d).budgets ↔ B = {0, 1} ∨ B = {0, 1, 2} :=
  Iff.rfl

/-- **Example 1.C.2** (MWG, p. 11), first structure: under `C₁`, `x ≿* y` and `x ≿* z`, there is
no revealed relation between `y` and `z`, and the weak axiom holds. -/
theorem example_1_C_2_C₁ :
    RevealedPref example_1_C_1_C₁ 0 1 ∧ RevealedPref example_1_C_1_C₁ 0 2 ∧
      ¬RevealedPref example_1_C_1_C₁ 1 2 ∧ ¬RevealedPref example_1_C_1_C₁ 2 1 ∧
      WeakAxiom example_1_C_1_C₁ := by
  have hC : ∀ B ∈ example_1_C_1_C₁.budgets, example_1_C_1_C₁.C B = {0} := by
    intro B hB
    rcases hB with rfl | hB
    · exact threeChoice_C_xy _ _ _ _
    · rw [Set.mem_singleton_iff] at hB
      subst hB
      exact threeChoice_C_xyz _ _ _ _
  refine ⟨⟨{0, 1}, Or.inl rfl, by simp, by simp, by rw [hC _ (Or.inl rfl)]; rfl⟩,
    ⟨{0, 1, 2}, Or.inr rfl, by simp, by simp, by rw [hC _ (Or.inr rfl)]; rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨B, hB, -, -, h⟩
    rw [hC B hB] at h
    simp at h
  · rintro ⟨B, hB, -, -, h⟩
    rw [hC B hB] at h
    simp at h
  · intro B hB B' hB' x y _ _ hxC _ _ hyC
    rw [hC B hB] at hxC
    rw [hC B' hB'] at hyC ⊢
    rw [Set.mem_singleton_iff] at hxC hyC ⊢
    exact hxC

/-- **Example 1.C.2** (MWG, p. 11), second structure: under `C₂`, `y ≿* x`, `x ≿* y`, `x ≿* z`
and `y ≿* z`; `x` is revealed preferred to `y`; so the weak axiom fails. -/
theorem example_1_C_2_C₂ :
    RevealedPref example_1_C_1_C₂ 1 0 ∧ RevealedPref example_1_C_1_C₂ 0 1 ∧
      RevealedPref example_1_C_1_C₂ 0 2 ∧ RevealedPref example_1_C_1_C₂ 1 2 ∧
      RevealedStrict example_1_C_1_C₂ 0 1 ∧ ¬WeakAxiom example_1_C_1_C₂ := by
  have h1 : example_1_C_1_C₂.C {0, 1} = {0} := threeChoice_C_xy _ _ _ _
  have h2 : example_1_C_1_C₂.C {0, 1, 2} = {0, 1} := threeChoice_C_xyz _ _ _ _
  have hs : RevealedStrict example_1_C_1_C₂ 0 1 :=
    ⟨{0, 1}, Or.inl rfl, by simp, by simp, by rw [h1]; rfl, by rw [h1]; simp⟩
  have hyx : RevealedPref example_1_C_1_C₂ 1 0 :=
    ⟨{0, 1, 2}, Or.inr rfl, by simp, by simp, by rw [h2]; simp⟩
  refine ⟨hyx, ⟨{0, 1, 2}, Or.inr rfl, by simp, by simp, by rw [h2]; simp⟩,
    ⟨{0, 1, 2}, Or.inr rfl, by simp, by simp, by rw [h2]; simp⟩,
    ⟨{0, 1, 2}, Or.inr rfl, by simp, by simp, by rw [h2]; simp⟩, hs, fun h => ?_⟩
  exact (weakAxiom_iff_revealed _).mp h 1 0 hyx hs

/-- **Footnote 5 and Exercise 1.C.1** (MWG, pp. 11, 15). If `{x, y}` and `{x, y, z}` are budget
sets, `C({x, y}) = {x}` and the weak axiom holds, then `C({x, y, z})` is `{x}`, `{z}` or
`{x, z}`. Proved for any choice structure containing these two budgets (in Exercise 1.C.1
they are all of `𝓑`); `x, y, z` need not be distinct. -/
theorem exercise_1_C_1 (S : ChoiceStructure X) (hwa : WeakAxiom S) {x y z : X}
    (hB : {x, y} ∈ S.budgets) (hB' : {x, y, z} ∈ S.budgets) (hC : S.C {x, y} = {x}) :
    S.C {x, y, z} = {x} ∨ S.C {x, y, z} = {z} ∨ S.C {x, y, z} = {x, z} := by
  have hsub := S.choice_subset _ hB'
  have hne := S.choice_nonempty _ hB'
  have hy : y ∈ S.C {x, y, z} → y = x := by
    intro hyC
    have : y ∈ S.C {x, y} := hwa {x, y, z} hB' {x, y} hB y x (by simp) (by simp) hyC
      (by simp) (by simp) (by rw [hC]; rfl)
    rw [hC] at this
    exact this
  have hsub' : S.C {x, y, z} ⊆ {x, z} := by
    intro w hw
    rcases hsub hw with h | h | h
    · exact Or.inl h
    · subst h
      exact Or.inl (hy hw)
    · exact Or.inr h
  by_cases hx : x ∈ S.C {x, y, z} <;> by_cases hz : z ∈ S.C {x, y, z}
  · right; right
    exact Set.Subset.antisymm hsub' (by
      intro w hw
      rcases hw with rfl | hw
      · exact hx
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact hz)
  · left
    refine Set.Subset.antisymm (fun w hw => ?_) (by simpa using hx)
    rcases hsub' hw with h | h
    · exact h
    · rw [Set.mem_singleton_iff] at h; subst h; exact absurd hw hz
  · right; left
    refine Set.Subset.antisymm (fun w hw => ?_) (by simpa using hz)
    rcases hsub' hw with h | h
    · subst h; exact absurd hw hx
    · exact h
  · exfalso
    obtain ⟨w, hw⟩ := hne
    rcases hsub' hw with h | h
    · subst h; exact hx hw
    · rw [Set.mem_singleton_iff] at h; subst h; exact hz hw

/-- **Exercise 1.C.2** (MWG, p. 15). The weak axiom is equivalent to: whenever `B, B' ∈ 𝓑`,
`x, y ∈ B`, `x, y ∈ B'`, `x ∈ C(B)` and `y ∈ C(B')`, we have `{x, y} ⊆ C(B)` and
`{x, y} ⊆ C(B')`. -/
theorem exercise_1_C_2 (S : ChoiceStructure X) :
    WeakAxiom S ↔ ∀ B ∈ S.budgets, ∀ B' ∈ S.budgets, ∀ x y, x ∈ B → y ∈ B → x ∈ B' →
      y ∈ B' → x ∈ S.C B → y ∈ S.C B' → {x, y} ⊆ S.C B ∧ {x, y} ⊆ S.C B' := by
  constructor
  · intro h B hB B' hB' x y hx hy hx' hy' hxC hyC
    have h1 : x ∈ S.C B' := h B hB B' hB' x y hx hy hxC hx' hy' hyC
    have h2 : y ∈ S.C B := h B' hB' B hB y x hy' hx' hyC hy hx hxC
    refine ⟨Set.insert_subset hxC (Set.singleton_subset_iff.mpr h2),
      Set.insert_subset h1 (Set.singleton_subset_iff.mpr hyC)⟩
  · intro h B hB B' hB' x y hx hy hxC hx' hy' hyC
    exact (h B hB B' hB' x y hx hy hx' hy' hxC hyC).2 (by simp)

/-- **Exercise 1.C.3(a)** (MWG, p. 15). Under the weak axiom, `x ≻* y ↔ x ≻** y`. -/
theorem exercise_1_C_3a (S : ChoiceStructure X) (hwa : WeakAxiom S) (x y : X) :
    RevealedStrict S x y ↔ RevealedStrict' S x y := by
  constructor
  · rintro ⟨B, hB, hx, hy, hxC, hyC⟩
    exact ⟨⟨B, hB, hx, hy, hxC⟩, fun hyx =>
      (weakAxiom_iff_revealed S).mp hwa y x hyx ⟨B, hB, hx, hy, hxC, hyC⟩⟩
  · rintro ⟨⟨B, hB, hx, hy, hxC⟩, hyx⟩
    exact ⟨B, hB, hx, hy, hxC, fun hyC => hyx ⟨B, hB, hy, hx, hyC⟩⟩

/-- **Exercise 1.C.3(a)**, second part (MWG, p. 15). Without the weak axiom the two relations
can differ: in Example 1.C.1's `C₂`, `x ≻* y` but not `x ≻** y`. -/
theorem exercise_1_C_3a_without_weakAxiom :
    RevealedStrict example_1_C_1_C₂ 0 1 ∧ ¬RevealedStrict' example_1_C_1_C₂ 0 1 := by
  obtain ⟨hyx, -, -, -, hs, -⟩ := example_1_C_2_C₂
  exact ⟨hs, fun h => h.2 hyx⟩

/-- `x ≻** y` always implies `x ≻* y`, with or without the weak axiom. -/
theorem revealedStrict_of_revealedStrict' (S : ChoiceStructure X) {x y : X}
    (h : RevealedStrict' S x y) : RevealedStrict S x y := by
  obtain ⟨⟨B, hB, hx, hy, hxC⟩, hyx⟩ := h
  exact ⟨B, hB, hx, hy, hxC, fun hyC => hyx ⟨B, hB, hy, hx, hyC⟩⟩

/-- The choice structure of Example 1.D.1 (MWG, p. 13) on `X = Fin 3`:
`𝓑 = {{x,y}, {y,z}, {x,z}}`, `C({x,y}) = {x}`, `C({y,z}) = {y}`, `C({x,z}) = {z}`. -/
def cyclicPairs : ChoiceStructure (Fin 3) where
  budgets := {{0, 1}, {1, 2}, {0, 2}}
  C B := if B = {0, 1} then {0} else if B = {1, 2} then {1} else if B = {0, 2} then {2} else ∅
  budget_nonempty B hB := by
    rcases hB with rfl | rfl | rfl <;> exact ⟨_, Set.mem_insert _ _⟩
  choice_subset B hB := by
    rcases hB with rfl | rfl | hB
    · simp
    · have : ({1, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
        have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
        simp at this
      simp [this]
    · rw [Set.mem_singleton_iff] at hB
      subst hB
      have h1 : ({0, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
        have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
        simp at this
      have h2 : ({0, 2} : Set (Fin 3)) ≠ {1, 2} := fun h => by
        have : (0 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := h ▸ by simp
        simp at this
      simp [h1, h2]
  choice_nonempty B hB := by
    rcases hB with rfl | rfl | hB
    · simp
    · have : ({1, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
        have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
        simp at this
      simp [this]
    · rw [Set.mem_singleton_iff] at hB
      subst hB
      have h1 : ({0, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
        have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
        simp at this
      have h2 : ({0, 2} : Set (Fin 3)) ≠ {1, 2} := fun h => by
        have : (0 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := h ▸ by simp
        simp at this
      simp [h1, h2]

/-- The three values of the Example 1.D.1 choice rule, and the budget family. -/
theorem cyclicPairs_values :
    cyclicPairs.C {0, 1} = {0} ∧ cyclicPairs.C {1, 2} = {1} ∧ cyclicPairs.C {0, 2} = {2} := by
  have h12 : ({1, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
    have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
    simp at this
  have h1 : ({0, 2} : Set (Fin 3)) ≠ {0, 1} := fun h => by
    have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ by simp
    simp at this
  have h2 : ({0, 2} : Set (Fin 3)) ≠ {1, 2} := fun h => by
    have : (0 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := h ▸ by simp
    simp at this
  refine ⟨by simp [cyclicPairs], by simp [cyclicPairs, h12], by simp [cyclicPairs, h1, h2]⟩

/-- Each budget of `cyclicPairs` is one of the three pairs, with its singleton choice. -/
theorem cyclicPairs_budget_cases {B : Set (Fin 3)} (hB : B ∈ cyclicPairs.budgets) :
    (B = {0, 1} ∧ cyclicPairs.C B = {0}) ∨ (B = {1, 2} ∧ cyclicPairs.C B = {1}) ∨
      (B = {0, 2} ∧ cyclicPairs.C B = {2}) := by
  obtain ⟨h1, h2, h3⟩ := cyclicPairs_values
  rcases hB with rfl | rfl | hB
  · exact Or.inl ⟨rfl, h1⟩
  · exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · rw [Set.mem_singleton_iff] at hB
    subst hB
    exact Or.inr (Or.inr ⟨rfl, h3⟩)

/-- **Example 1.D.1** (MWG, p. 13; "you should verify this"). The structure `cyclicPairs`
satisfies the weak axiom: each budget has two elements and a single chosen one, and no two
budgets share two elements. -/
theorem cyclicPairs_weakAxiom : WeakAxiom cyclicPairs := by
  intro B hB B' hB' x y hx hy hxC hx' hy' hyC
  rcases cyclicPairs_budget_cases hB with ⟨rfl, hC⟩ | ⟨rfl, hC⟩ | ⟨rfl, hC⟩ <;>
  rcases cyclicPairs_budget_cases hB' with ⟨rfl, hC'⟩ | ⟨rfl, hC'⟩ | ⟨rfl, hC'⟩ <;>
  rw [hC] at hxC <;> rw [hC'] at hyC ⊢ <;>
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hxC hyC hx hy hx' hy' ⊢ <;>
  subst hxC <;> subst hyC <;> omega

/-- **Section 1.C** (MWG, p. 11). `≿*` need not be complete: under `C₁` of Example 1.C.1,
neither `y ≿* z` nor `z ≿* y`. -/
theorem revealedPref_not_complete :
    ¬∀ a b, RevealedPref example_1_C_1_C₁ a b ∨ RevealedPref example_1_C_1_C₁ b a := by
  intro h
  obtain ⟨-, -, h12, h21, -⟩ := example_1_C_2_C₁
  exact (h 1 2).elim h12 h21

/-- **Section 1.C** (MWG, p. 11). `≿*` need not be transitive, even under the weak axiom: in
Example 1.D.1, `x ≿* y` and `y ≿* z` but not `x ≿* z`. -/
theorem revealedPref_not_transitive :
    WeakAxiom cyclicPairs ∧ RevealedPref cyclicPairs 0 1 ∧ RevealedPref cyclicPairs 1 2 ∧
      ¬RevealedPref cyclicPairs 0 2 := by
  obtain ⟨h1, h2, -⟩ := cyclicPairs_values
  refine ⟨cyclicPairs_weakAxiom, ⟨{0, 1}, Or.inl rfl, by simp, by simp, by rw [h1]; rfl⟩,
    ⟨{1, 2}, Or.inr (Or.inl rfl), by simp, by simp, by rw [h2]; rfl⟩, ?_⟩
  rintro ⟨B, hB, hx, hz, hC⟩
  rcases cyclicPairs_budget_cases hB with ⟨rfl, hC'⟩ | ⟨rfl, hC'⟩ | ⟨rfl, hC'⟩ <;>
    rw [hC'] at hC <;> simp at hC hx hz

/-- **Exercise 1.C.3(b)** (MWG, p. 15). `≻*` need not be transitive, even under the weak
axiom: in Example 1.D.1, `x ≻* y` and `y ≻* z` but not `x ≻* z`. -/
theorem exercise_1_C_3b :
    WeakAxiom cyclicPairs ∧ RevealedStrict cyclicPairs 0 1 ∧ RevealedStrict cyclicPairs 1 2 ∧
      ¬RevealedStrict cyclicPairs 0 2 := by
  obtain ⟨h1, h2, -⟩ := cyclicPairs_values
  obtain ⟨hwa, -, -, hn⟩ := revealedPref_not_transitive
  refine ⟨hwa, ⟨{0, 1}, Or.inl rfl, by simp, by simp, by rw [h1]; rfl, by rw [h1]; simp⟩,
    ⟨{1, 2}, Or.inr (Or.inl rfl), by simp, by simp, by rw [h2]; rfl, by rw [h2]; simp⟩, ?_⟩
  rintro ⟨B, hB, hx, hz, hC, -⟩
  exact hn ⟨B, hB, hx, hz, hC⟩

/-- **Exercise 1.C.3(c)** (MWG, p. 15). Under the weak axiom, if `𝓑` contains every
three-element subset of `X`, then `≻*` is transitive. -/
theorem exercise_1_C_3c (S : ChoiceStructure X) (hwa : WeakAxiom S)
    (h3 : ∀ a b c : X, a ≠ b → b ≠ c → a ≠ c → {a, b, c} ∈ S.budgets) {x y z : X}
    (hxy : RevealedStrict S x y) (hyz : RevealedStrict S y z) : RevealedStrict S x z := by
  rw [exercise_1_C_3a S hwa] at hxy hyz ⊢
  have hne : ∀ {a b : X}, RevealedStrict' S a b → a ≠ b := by
    rintro a b ⟨hab, hba⟩ rfl
    exact hba hab
  have hxz : x ≠ z := by
    rintro rfl
    exact hxy.2 hyz.1
  have hT := h3 x y z (hne hxy) (hne hyz) hxz
  have hyC : y ∉ S.C {x, y, z} := fun h => hxy.2 ⟨_, hT, by simp, by simp, h⟩
  have hzC : z ∉ S.C {x, y, z} := fun h => hyz.2 ⟨_, hT, by simp, by simp, h⟩
  have hxC : x ∈ S.C {x, y, z} := by
    obtain ⟨w, hw⟩ := S.choice_nonempty _ hT
    rcases S.choice_subset _ hT hw with rfl | rfl | rfl
    · exact hw
    · exact absurd hw hyC
    · exact absurd hw hzC
  have hxz' : RevealedStrict S x z := ⟨_, hT, by simp, by simp, hxC, hzC⟩
  exact (exercise_1_C_3a S hwa x z).mp hxz'

end MWG.PreferenceChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preference relations and choice rules

MWG, Section 1.D, pp. 11-14, and Exercises 1.D.1-1.D.4, pp. 15-16.

The preference-maximizing set `C*(B, ≿) = {x ∈ B | x ≿ y for all y ∈ B}` is Kreps's
`PrefChoice r B`. We prove that it may be empty (p. 12), that rational preferences generate
choice structures satisfying the weak axiom (Proposition 1.D.1), define rationalization
(Definition 1.D.1), show that Example 1.D.1 satisfies the weak axiom but is not
rationalizable, and prove Proposition 1.D.2 at the book's generality: `X` is arbitrary and
`𝓑` is any family containing all (nonempty) subsets with at most three elements; the
revealed preference relation `≿*` is then rational, rationalizes `C(·)`, and is the only
relation (rational or not) that does. Also proved: the equivalence of the weak axiom and
rationalizability on such families (p. 14), the weaker notion `C(B) ⊆ C*(B, ≿)` and its
triviality (p. 14), and Exercises 1.D.1-1.D.4. No departures from the book.
-/

namespace MWG.PreferenceChoice

open Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- **Section 1.D** (MWG, p. 12). `x ∈ C*(B, ≿)` iff `x ∈ B` and `x ≿ y` for every `y ∈ B`;
`C*(B, ≿)` is Kreps's `PrefChoice r B`. -/
theorem mem_prefChoice_iff (r : X → X → Prop) (B : Set X) (x : X) :
    x ∈ PrefChoice r B ↔ x ∈ B ∧ ∀ y ∈ B, r x y :=
  Iff.rfl

/-- **Section 1.D** (MWG, p. 12). `C*(B, ≿)` can be empty: for the rational relation `≥` on
`ℕ` and `B = ℕ`, nothing is at least as good as everything. -/
theorem prefChoice_can_be_empty :
    Rational (fun a b : ℕ => b ≤ a) ∧ PrefChoice (fun a b : ℕ => b ≤ a) Set.univ = ∅ := by
  refine ⟨⟨fun a b => le_total b a, fun _ _ _ hab hbc => le_trans hbc hab⟩, ?_⟩
  ext a
  refine ⟨fun h => absurd (h.2 (a + 1) trivial) (by omega), fun h => absurd h id⟩

/-- **Section 1.D** (MWG, p. 12). When `C*(B, ≿)` is nonempty for every `B ∈ 𝓑`, the
preference relation `≿` generates the choice structure `(𝓑, C*(·, ≿))`. -/
def generatedStructure (budgets : Set (Set X)) (hB : ∀ B ∈ budgets, B.Nonempty)
    (r : X → X → Prop) (hne : ∀ B ∈ budgets, (PrefChoice r B).Nonempty) :
    ChoiceStructure X where
  budgets := budgets
  C := PrefChoice r
  budget_nonempty := hB
  choice_subset _ _ := prefChoice_feasible r _
  choice_nonempty := hne

/-- **Proposition 1.D.1** (MWG, p. 12). If `≿` is rational, the choice structure
`(𝓑, C*(·, ≿))` it generates satisfies the weak axiom. -/
theorem proposition_1_D_1 {r : X → X → Prop} (hr : Rational r) (budgets : Set (Set X))
    (hB : ∀ B ∈ budgets, B.Nonempty) (hne : ∀ B ∈ budgets, (PrefChoice r B).Nonempty) :
    WeakAxiom (generatedStructure budgets hB r hne) := by
  intro B _ B' _ x y _ hy hxC hx' _ hyC
  exact ⟨hx', fun z hz => hr.2 x y z (hxC.2 y hy) (hyC.2 z hz)⟩

/-- **Definition 1.D.1** (MWG, p. 12). The rational preference relation `≿` rationalizes
`C(·)` relative to `𝓑` if `C(B) = C*(B, ≿)` for all `B ∈ 𝓑`. -/
def Rationalizes (r : X → X → Prop) (S : ChoiceStructure X) : Prop :=
  Rational r ∧ ∀ B ∈ S.budgets, S.C B = PrefChoice r B

/-- A choice structure is rationalizable if some rational preference relation rationalizes
it. -/
def Rationalizable (S : ChoiceStructure X) : Prop :=
  ∃ r : X → X → Prop, Rationalizes r S

/-- **Section 1.D** (MWG, p. 13). Proposition 1.D.1 implies that only a choice rule satisfying
the weak axiom can be rationalized. -/
theorem weakAxiom_of_rationalizes {r : X → X → Prop} {S : ChoiceStructure X}
    (h : Rationalizes r S) : WeakAxiom S := by
  intro B hB B' hB' x y hx hy hxC hx' hy' hyC
  rw [h.2 B hB] at hxC
  rw [h.2 B' hB'] at hyC ⊢
  have hne : ∀ D ∈ S.budgets, (PrefChoice r D).Nonempty := fun D hD =>
    h.2 D hD ▸ S.choice_nonempty D hD
  exact proposition_1_D_1 h.1 S.budgets S.budget_nonempty hne B hB B' hB' x y hx hy hxC hx'
    hy' hyC

/-- **Example 1.D.1** (MWG, p. 13). The structure with `𝓑 = {{x,y}, {y,z}, {x,z}}`,
`C({x,y}) = {x}`, `C({y,z}) = {y}`, `C({x,z}) = {z}` satisfies the weak axiom but has no
rationalizing preference relation. -/
theorem example_1_D_1 : WeakAxiom cyclicPairs ∧ ¬Rationalizable cyclicPairs := by
  refine ⟨cyclicPairs_weakAxiom, ?_⟩
  rintro ⟨r, hr, hC⟩
  obtain ⟨h1, h2, h3⟩ := cyclicPairs_values
  have s01 : Strict r 0 1 := by
    have h0 : (0 : Fin 3) ∈ PrefChoice r {0, 1} := by rw [← hC _ (Or.inl rfl), h1]; rfl
    have h1' : (1 : Fin 3) ∉ PrefChoice r {0, 1} := by rw [← hC _ (Or.inl rfl), h1]; simp
    exact ⟨h0.2 1 (by simp), fun h => h1' ⟨by simp, fun w hw => by
      rcases hw with rfl | hw
      · exact h
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact complete_refl hr.1 _⟩⟩
  have s12 : Strict r 1 2 := by
    have hm : (1 : Fin 3) ∈ PrefChoice r {1, 2} := by
      rw [← hC _ (Or.inr (Or.inl rfl)), h2]; rfl
    have hn : (2 : Fin 3) ∉ PrefChoice r {1, 2} := by
      rw [← hC _ (Or.inr (Or.inl rfl)), h2]; simp
    exact ⟨hm.2 2 (by simp), fun h => hn ⟨by simp, fun w hw => by
      rcases hw with rfl | hw
      · exact h
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact complete_refl hr.1 _⟩⟩
  have s20 : Strict r 2 0 := by
    have hm : (2 : Fin 3) ∈ PrefChoice r {0, 2} := by
      rw [← hC _ (Or.inr (Or.inr rfl)), h3]; rfl
    have hn : (0 : Fin 3) ∉ PrefChoice r {0, 2} := by
      rw [← hC _ (Or.inr (Or.inr rfl)), h3]; simp
    exact ⟨hm.2 0 (by simp), fun h => hn ⟨by simp, fun w hw => by
      rcases hw with rfl | hw
      · exact complete_refl hr.1 _
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact h⟩⟩
  exact prefRel_no_strict_cycle hr s01 s12 s20

/-- Hypothesis (ii) of Proposition 1.D.2 (MWG, p. 13): `𝓑` contains every (nonempty) subset of
`X` with at most three elements. -/
def ContainsSmallSubsets (budgets : Set (Set X)) : Prop :=
  ∀ B : Set X, B.Nonempty → B.encard ≤ 3 → B ∈ budgets

/-- Under `ContainsSmallSubsets`, every `{x, y}` is a budget set. -/
theorem containsSmallSubsets_pair {budgets : Set (Set X)} (h : ContainsSmallSubsets budgets)
    (x y : X) : ({x, y} : Set X) ∈ budgets := by
  refine h _ ⟨x, by simp⟩ ?_
  calc ({x, y} : Set X).encard ≤ ({y} : Set X).encard + 1 := Set.encard_insert_le _ _
    _ ≤ 3 := by rw [Set.encard_singleton]; norm_num

/-- Under `ContainsSmallSubsets`, every `{x, y, z}` is a budget set. -/
theorem containsSmallSubsets_triple {budgets : Set (Set X)} (h : ContainsSmallSubsets budgets)
    (x y z : X) : ({x, y, z} : Set X) ∈ budgets := by
  refine h _ ⟨x, by simp⟩ ?_
  calc ({x, y, z} : Set X).encard ≤ ({y, z} : Set X).encard + 1 := Set.encard_insert_le _ _
    _ ≤ (({z} : Set X).encard + 1) + 1 := by gcongr; exact Set.encard_insert_le _ _
    _ = 3 := by rw [Set.encard_singleton]; norm_num

/-- Under the weak axiom with all pairs in `𝓑`, `x ≿* y` iff `x ∈ C({x, y})`. -/
theorem revealedPref_iff_mem_pair {S : ChoiceStructure X} (hwa : WeakAxiom S)
    (hpair : ∀ x y : X, ({x, y} : Set X) ∈ S.budgets) (x y : X) :
    RevealedPref S x y ↔ x ∈ S.C {x, y} := by
  constructor
  · rintro ⟨B, hB, hx, hy, hxC⟩
    obtain ⟨w, hw⟩ := S.choice_nonempty _ (hpair x y)
    rcases S.choice_subset _ (hpair x y) hw with rfl | h
    · exact hw
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact hwa B hB _ (hpair x w) x w hx hy hxC (by simp) (by simp) hw
  · intro h
    exact ⟨_, hpair x y, by simp, by simp, h⟩

/-- **Proposition 1.D.2(i)** (MWG, p. 13). Under the weak axiom, if `𝓑` contains all pairs and
triples, the revealed preference relation `≿*` is rational. -/
theorem proposition_1_D_2_rational {S : ChoiceStructure X} (hwa : WeakAxiom S)
    (hpair : ∀ x y : X, ({x, y} : Set X) ∈ S.budgets)
    (htriple : ∀ x y z : X, ({x, y, z} : Set X) ∈ S.budgets) : Rational (RevealedPref S) := by
  refine ⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩
  · obtain ⟨w, hw⟩ := S.choice_nonempty _ (hpair x y)
    rcases S.choice_subset _ (hpair x y) hw with rfl | h
    · exact Or.inl ⟨_, hpair w y, by simp, by simp, hw⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Or.inr ⟨_, hpair x w, by simp, by simp, hw⟩
  · have hT := htriple x y z
    suffices hxC : x ∈ S.C {x, y, z} from ⟨_, hT, by simp, by simp, hxC⟩
    obtain ⟨B₁, hB₁, hx₁, hy₁, hxC₁⟩ := hxy
    obtain ⟨B₂, hB₂, hy₂, hz₂, hyC₂⟩ := hyz
    have hy : y ∈ S.C {x, y, z} → x ∈ S.C {x, y, z} := fun h =>
      hwa B₁ hB₁ _ hT x y hx₁ hy₁ hxC₁ (by simp) (by simp) h
    obtain ⟨w, hw⟩ := S.choice_nonempty _ hT
    rcases S.choice_subset _ hT hw with rfl | rfl | h
    · exact hw
    · exact hy hw
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact hy (hwa B₂ hB₂ _ hT y w hy₂ hz₂ hyC₂ (by simp) (by simp) hw)

/-- **Proposition 1.D.2(ii)** (MWG, pp. 13-14). Under the weak axiom, `C(B) = C*(B, ≿*)` for
all `B ∈ 𝓑` (no further hypothesis on `𝓑` is needed for this step). -/
theorem proposition_1_D_2_generates {S : ChoiceStructure X} (hwa : WeakAxiom S) :
    ∀ B ∈ S.budgets, S.C B = PrefChoice (RevealedPref S) B := by
  intro B hB
  ext x
  constructor
  · intro hx
    exact ⟨S.choice_subset B hB hx, fun y hy =>
      ⟨B, hB, S.choice_subset B hB hx, hy, hx⟩⟩
  · rintro ⟨hxB, hall⟩
    obtain ⟨w, hw⟩ := S.choice_nonempty B hB
    obtain ⟨Bw, hBw, hx, hwBw, hxC⟩ := hall w (S.choice_subset B hB hw)
    exact hwa Bw hBw B hB x w hx hwBw hxC hxB (S.choice_subset B hB hw) hw

/-- **Proposition 1.D.2(iii)** (MWG, p. 14). If `𝓑` contains all subsets of at most three
elements, any relation `≿` (rational or not) with `C(B) = C*(B, ≿)` for all `B ∈ 𝓑` is the
revealed preference relation `≿*`. -/
theorem proposition_1_D_2_unique {S : ChoiceStructure X} (hwa : WeakAxiom S)
    (hsmall : ContainsSmallSubsets S.budgets) {r : X → X → Prop}
    (hr : ∀ B ∈ S.budgets, S.C B = PrefChoice r B) : r = RevealedPref S := by
  have hpair := containsSmallSubsets_pair hsmall
  have hrefl : ∀ x, r x x := by
    intro x
    have h1 : ({x} : Set X) ∈ S.budgets := by
      simpa using hpair x x
    obtain ⟨w, hw⟩ := S.choice_nonempty _ h1
    rw [hr _ h1] at hw
    have : w = x := hw.1
    subst this
    exact hw.2 w rfl
  funext x y
  apply propext
  rw [revealedPref_iff_mem_pair hwa hpair, hr _ (hpair x y)]
  constructor
  · intro h
    refine ⟨by simp, fun w hw => ?_⟩
    rcases hw with rfl | hw
    · exact hrefl w
    · rw [Set.mem_singleton_iff] at hw; subst hw; exact h
  · intro h
    exact h.2 y (by simp)

/-- **Proposition 1.D.2** (MWG, p. 13; Arrow 1959). If `(𝓑, C(·))` satisfies the weak axiom and
`𝓑` contains all subsets of `X` with up to three elements, then the revealed preference
relation `≿*` is a rational preference relation rationalizing `C(·)` relative to `𝓑`, and it
is the only preference relation that does so. -/
theorem proposition_1_D_2 {S : ChoiceStructure X} (hwa : WeakAxiom S)
    (hsmall : ContainsSmallSubsets S.budgets) :
    Rationalizes (RevealedPref S) S ∧
      ∀ r : X → X → Prop, (∀ B ∈ S.budgets, S.C B = PrefChoice r B) → r = RevealedPref S :=
  ⟨⟨proposition_1_D_2_rational hwa (containsSmallSubsets_pair hsmall)
      (containsSmallSubsets_triple hsmall), proposition_1_D_2_generates hwa⟩,
    fun _ hr => proposition_1_D_2_unique hwa hsmall hr⟩

/-- **Section 1.D** (MWG, p. 14). When `𝓑` contains all subsets with up to three elements,
the weak axiom is equivalent to rationalizability by a rational preference relation. -/
theorem weakAxiom_iff_rationalizable {S : ChoiceStructure X}
    (hsmall : ContainsSmallSubsets S.budgets) : WeakAxiom S ↔ Rationalizable S :=
  ⟨fun hwa => ⟨_, (proposition_1_D_2 hwa hsmall).1⟩, fun ⟨_, h⟩ => weakAxiom_of_rationalizes h⟩

/-- **Section 1.D, small type** (MWG, p. 14). The alternative notion: `≿` rationalizes `C(·)` in
the weak sense if `C(B) ⊆ C*(B, ≿)` for all `B ∈ 𝓑`. -/
def WeaklyRationalizes (r : X → X → Prop) (S : ChoiceStructure X) : Prop :=
  Rational r ∧ ∀ B ∈ S.budgets, S.C B ⊆ PrefChoice r B

/-- **Section 1.D, small type** (MWG, p. 14). The alternative notion is weaker. -/
theorem weaklyRationalizes_of_rationalizes {r : X → X → Prop} {S : ChoiceStructure X}
    (h : Rationalizes r S) : WeaklyRationalizes r S :=
  ⟨h.1, fun B hB => (h.2 B hB).le⟩

/-- **Section 1.D, small type** (MWG, p. 14). The alternative notion is trivial: total
indifference rationalizes every choice structure in this weak sense. -/
theorem weaklyRationalizes_indifference (S : ChoiceStructure X) :
    WeaklyRationalizes (fun _ _ => True) S :=
  ⟨⟨fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩,
    fun B hB _ hx => ⟨S.choice_subset B hB hx, fun _ _ => trivial⟩⟩

/-- The structure of Exercise 1.D.1: `X = Fin 3`, `𝓑 = {X}`, `C(X) = {x}` (`x = 0`). -/
def exercise_1_D_1_structure : ChoiceStructure (Fin 3) where
  budgets := {Set.univ}
  C _ := {0}
  budget_nonempty _ hB := by rw [Set.mem_singleton_iff] at hB; subst hB; exact ⟨0, trivial⟩
  choice_subset _ hB := by rw [Set.mem_singleton_iff] at hB; subst hB; exact Set.subset_univ _
  choice_nonempty _ _ := ⟨0, rfl⟩

/-- **Exercise 1.D.1** (MWG, p. 15), first part. A choice structure rationalized by two different
rational preference relations: `x ≻ y ≻ z` and `x ≻ z ≻ y` both rationalize choosing `x`
from `{x, y, z}`. -/
theorem exercise_1_D_1a :
    ∃ r₁ r₂ : Fin 3 → Fin 3 → Prop, r₁ ≠ r₂ ∧ Rationalizes r₁ exercise_1_D_1_structure ∧
      Rationalizes r₂ exercise_1_D_1_structure := by
  let u₁ : Fin 3 → ℝ := ![2, 1, 0]
  let u₂ : Fin 3 → ℝ := ![2, 0, 1]
  have key : ∀ u : Fin 3 → ℝ, (∀ a, a ≠ 0 → u a < u 0) →
      Rationalizes (UtilityPref u) exercise_1_D_1_structure := by
    intro u hu
    refine ⟨proposition_1_3a u, fun B hB => ?_⟩
    have hB' : B = Set.univ := hB
    subst hB'
    ext a
    simp only [exercise_1_D_1_structure, Set.mem_singleton_iff, PrefChoice, UtilityPref,
      Set.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · rintro rfl b _
      by_cases hb : b = 0
      · rw [hb]
      · exact (hu b hb).le
    · intro h
      by_contra ha
      exact absurd (h 0 trivial) (not_le.mpr (hu a ha))
  refine ⟨UtilityPref u₁, UtilityPref u₂, fun h => ?_, key u₁ ?_, key u₂ ?_⟩
  · have h' : UtilityPref u₁ 1 2 = UtilityPref u₂ 1 2 := by rw [h]
    simp [UtilityPref, u₁, u₂] at h'
    norm_num at h'
  · intro a ha
    fin_cases a <;> simp [u₁] at ha ⊢
  · intro a ha
    fin_cases a <;> simp [u₂] at ha ⊢

/-- **Exercise 1.D.1** (MWG, p. 15), second part. If `𝓑` contains all two-element subsets of `X`,
there is at most one rationalizing preference relation. -/
theorem exercise_1_D_1b {S : ChoiceStructure X}
    (hpair : ∀ x y : X, x ≠ y → ({x, y} : Set X) ∈ S.budgets) {r₁ r₂ : X → X → Prop}
    (h₁ : Rationalizes r₁ S) (h₂ : Rationalizes r₂ S) : r₁ = r₂ := by
  have key : ∀ r : X → X → Prop, Rationalizes r S → ∀ x y, x ≠ y →
      (r x y ↔ x ∈ S.C {x, y}) := by
    intro r hr x y hxy
    rw [hr.2 _ (hpair x y hxy)]
    constructor
    · intro h
      refine ⟨by simp, fun w hw => ?_⟩
      rcases hw with rfl | hw
      · exact complete_refl hr.1.1 w
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact h
    · intro h
      exact h.2 y (by simp)
  funext x y
  apply propext
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun _ => complete_refl h₂.1.1 x, fun _ => complete_refl h₁.1.1 x⟩
  · rw [key r₁ h₁ x y hxy, key r₂ h₂ x y hxy]

/-- **Exercise 1.D.2** (MWG, p. 16; footnote 6, p. 12). If `X` is finite, a rational preference
relation generates a nonempty choice rule: `C*(B, ≿) ≠ ∅` for every nonempty `B ⊆ X`. -/
theorem exercise_1_D_2 [Finite X] {r : X → X → Prop} (hr : Rational r) {B : Set X}
    (hB : B.Nonempty) : (PrefChoice r B).Nonempty :=
  prefChoice_finiteNonempty hr B (Set.toFinite B) hB

/-- **Exercise 1.D.3** (MWG, p. 16). With `X = {x, y, z}`, `𝓑` all of `{x,y}`, `{y,z}`, `{x,z}`,
`{x,y,z}`, and `C({x,y}) = {x}`, `C({y,z}) = {y}`, `C({x,z}) = {z}`, the weak axiom fails,
whatever `C({x, y, z})` is. -/
theorem exercise_1_D_3 (S : ChoiceStructure (Fin 3))
    (hB : S.budgets = {{0, 1}, {1, 2}, {0, 2}, {0, 1, 2}}) (h01 : S.C {0, 1} = {0})
    (h12 : S.C {1, 2} = {1}) (h02 : S.C {0, 2} = {2}) : ¬WeakAxiom S := by
  intro hwa
  have hT : ({0, 1, 2} : Set (Fin 3)) ∈ S.budgets := by rw [hB]; simp
  have b01 : ({0, 1} : Set (Fin 3)) ∈ S.budgets := by rw [hB]; simp
  have b12 : ({1, 2} : Set (Fin 3)) ∈ S.budgets := by rw [hB]; simp
  have b02 : ({0, 2} : Set (Fin 3)) ∈ S.budgets := by rw [hB]; simp
  obtain ⟨w, hw⟩ := S.choice_nonempty _ hT
  rcases S.choice_subset _ hT hw with rfl | rfl | h
  · have := hwa _ hT _ b02 0 2 (by simp) (by simp) hw (by simp) (by simp) (by rw [h02]; rfl)
    rw [h02] at this
    simp at this
  · have := hwa _ hT _ b01 1 0 (by simp) (by simp) hw (by simp) (by simp) (by rw [h01]; rfl)
    rw [h01] at this
    simp at this
  · rw [Set.mem_singleton_iff] at h
    subst h
    have := hwa _ hT _ b12 2 1 (by simp) (by simp) hw (by simp) (by simp) (by rw [h12]; rfl)
    rw [h12] at this
    simp at this

/-- **Exercise 1.D.4** (MWG, p. 16). If a rationalizing preference relation exists, then `C(·)`
is path-invariant: for `B₁, B₂ ∈ 𝓑` with `B₁ ∪ B₂ ∈ 𝓑` and `C(B₁) ∪ C(B₂) ∈ 𝓑`,
`C(B₁ ∪ B₂) = C(C(B₁) ∪ C(B₂))`. -/
theorem exercise_1_D_4 {S : ChoiceStructure X} (hS : Rationalizable S) {B₁ B₂ : Set X}
    (h₁ : B₁ ∈ S.budgets) (h₂ : B₂ ∈ S.budgets) (hu : B₁ ∪ B₂ ∈ S.budgets)
    (hc : S.C B₁ ∪ S.C B₂ ∈ S.budgets) : S.C (B₁ ∪ B₂) = S.C (S.C B₁ ∪ S.C B₂) := by
  obtain ⟨r, hr, hC⟩ := hS
  have hsub : S.C B₁ ∪ S.C B₂ ⊆ B₁ ∪ B₂ :=
    Set.union_subset_union (S.choice_subset _ h₁) (S.choice_subset _ h₂)
  rw [hC _ hu, hC _ hc]
  ext x
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨?_, fun y hy => hall y (hsub hy)⟩
    rcases hx with hx | hx
    · left; rw [hC _ h₁]; exact ⟨hx, fun y hy => hall y (Or.inl hy)⟩
    · right; rw [hC _ h₂]; exact ⟨hx, fun y hy => hall y (Or.inr hy)⟩
  · rintro ⟨hx, hall⟩
    refine ⟨hsub hx, fun y hy => ?_⟩
    rcases hy with hy | hy
    · obtain ⟨w, hw⟩ := S.choice_nonempty _ h₁
      have hw' := hw
      rw [hC _ h₁] at hw'
      exact hr.2 x w y (hall w (Or.inl hw)) (hw'.2 y hy)
    · obtain ⟨w, hw⟩ := S.choice_nonempty _ h₂
      have hw' := hw
      rw [hC _ h₂] at hw'
      exact hr.2 x w y (hall w (Or.inr hw)) (hw'.2 y hy)

end MWG.PreferenceChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Stochastic choice rationalized by random preferences

MWG, Exercise 1.D.5, p. 16.

`X = {x, y, z}` is `Fin 3` (`x = 0`, `y = 1`, `z = 2`) and `𝓑 = {{x,y}, {y,z}, {z,x}}`. The six
strict preference relations on `X` are encoded by the permutations `σ` of `Fin 3`, read as
rank assignments: `a ≻_σ b` iff `σ a < σ b`. Each such relation is irreflexive, transitive and
total on distinct alternatives (`rankPrefers_strictTotal`), and distinct permutations give
distinct relations (`rankPrefers_injective`). A stochastic choice function on the pairs is
`c a b = C_a({a, b})`. It is rationalized by preferences if a probability distribution `Pr` on
the six relations gives `c a b = Pr{≻ : a ≻ b}` for every pair of distinct alternatives.

For the cyclic function `C({x,y}) = C({y,z}) = C({z,x}) = (α, 1 - α)` we prove: it is
rationalizable iff `1/3 ≤ α ≤ 2/3` (`cyclicChoice_rationalizable_iff`). Hence (a) `α = 1/2` is
rationalizable, (b) `α = 1/4` is not, and (c) on `0 < α < 1` the function switches between
rationalizable and nonrationalizable exactly at `α = 1/3` and `α = 2/3`. The key fact is that
every strict ordering ranks exactly one or two of the three cyclic pairs `x ≻ y`, `y ≻ z`,
`z ≻ x` the "cyclic" way, so `3α = E[count] ∈ [1, 2]`.
-/

namespace MWG.PreferenceChoice

/-- The strict preference relation encoded by a ranking `σ`: `a ≻ b` iff `a` has the smaller
rank. -/
abbrev rankPrefers (σ : Equiv.Perm (Fin 3)) (a b : Fin 3) : Prop := σ a < σ b

/-- Each ranking gives a strict preference relation: irreflexive, transitive, and total on
distinct alternatives. -/
theorem rankPrefers_strictTotal (σ : Equiv.Perm (Fin 3)) :
    (∀ a, ¬rankPrefers σ a a) ∧
      (∀ a b c, rankPrefers σ a b → rankPrefers σ b c → rankPrefers σ a c) ∧
      (∀ a b, a ≠ b → rankPrefers σ a b ∨ rankPrefers σ b a) := by
  refine ⟨fun a => lt_irrefl _, fun a b c => lt_trans, fun a b hab => ?_⟩
  exact lt_or_gt_of_ne (fun h => hab (σ.injective h))

/-- Distinct rankings give distinct strict preference relations, so the six permutations are
the six strict preference relations of the exercise. -/
theorem rankPrefers_injective : Function.Injective rankPrefers := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3), (∀ a b, σ a < σ b ↔ τ a < τ b) → σ = τ := by decide
  intro σ τ h
  exact key σ τ fun a b => by
    have := congrFun (congrFun h a) b
    exact Iff.of_eq this

/-- A stochastic choice function `c a b = C_a({a, b})` on the three pairs is rationalized by
preferences if some probability distribution on the six strict relations gives
`c a b = Pr{≻ : a ≻ b}` for all distinct `a, b`. -/
def StochasticRationalizable (c : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∃ Pr : Equiv.Perm (Fin 3) → ℝ, (∀ σ, 0 ≤ Pr σ) ∧ ∑ σ, Pr σ = 1 ∧
    ∀ a b, a ≠ b → c a b = ∑ σ ∈ Finset.univ.filter (fun σ => rankPrefers σ a b), Pr σ

/-- The cyclic stochastic choice function `C({x,y}) = C({y,z}) = C({z,x}) = (α, 1 - α)`:
`C_a({a, a + 1}) = α` and `C_{a+1}({a, a + 1}) = 1 - α` (indices mod 3). -/
def cyclicChoice (α : ℝ) (a b : Fin 3) : ℝ := if b = a + 1 then α else 1 - α

/-- The cyclic function is a stochastic choice function on `𝓑` when `0 ≤ α ≤ 1`: frequencies
are nonnegative and sum to one on each pair. -/
theorem cyclicChoice_valid {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (a b : Fin 3) (hab : a ≠ b) :
    0 ≤ cyclicChoice α a b ∧ cyclicChoice α a b + cyclicChoice α b a = 1 := by
  have key : ∀ a b : Fin 3, a ≠ b → (b = a + 1 ∧ ¬a = b + 1) ∨ (¬b = a + 1 ∧ a = b + 1) := by
    decide
  rcases key a b hab with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · simp only [cyclicChoice, eq_true h1', eq_false h2', ite_true, ite_false]
    constructor <;> linarith
  · simp only [cyclicChoice, eq_true h2', eq_false h1', ite_true, ite_false]
    constructor <;> linarith

/-- How many of the cyclic pairs `x ≻ y`, `y ≻ z`, `z ≻ x` the ranking `σ` has. -/
def cyclicCount (σ : Equiv.Perm (Fin 3)) : ℕ :=
  (if σ 0 < σ 1 then 1 else 0) + (if σ 1 < σ 2 then 1 else 0) + (if σ 2 < σ 0 then 1 else 0)

/-- Every strict ordering of `{x, y, z}` has one or two of the cyclic pairs. -/
theorem cyclicCount_bounds (σ : Equiv.Perm (Fin 3)) : 1 ≤ cyclicCount σ ∧ cyclicCount σ ≤ 2 := by
  revert σ
  unfold cyclicCount
  decide

/-- **Exercise 1.D.5** (MWG, p. 16), necessity. If the cyclic function is rationalizable then
`1/3 ≤ α ≤ 2/3`. -/
theorem cyclicChoice_bounds_of_rationalizable {α : ℝ}
    (h : StochasticRationalizable (cyclicChoice α)) : 1 / 3 ≤ α ∧ α ≤ 2 / 3 := by
  obtain ⟨Pr, hnn, hsum, hc⟩ := h
  have h01 := hc 0 1 (by decide)
  have h12 := hc 1 2 (by decide)
  have h20 := hc 2 0 (by decide)
  have c : ∀ a b : Fin 3, b = a + 1 → cyclicChoice α a b = α := fun a b h => by
    simp only [cyclicChoice, eq_true h, ite_true]
  rw [c 0 1 (by decide)] at h01
  rw [c 1 2 (by decide)] at h12
  rw [c 2 0 (by decide)] at h20
  rw [Finset.sum_filter] at h01 h12 h20
  have h3 : 3 * α = ∑ σ, Pr σ * (cyclicCount σ : ℝ) := by
    have e : ∀ σ : Equiv.Perm (Fin 3), Pr σ * (cyclicCount σ : ℝ) =
        (if rankPrefers σ 0 1 then Pr σ else 0) + (if rankPrefers σ 1 2 then Pr σ else 0) +
          (if rankPrefers σ 2 0 then Pr σ else 0) := by
      intro σ
      simp only [cyclicCount, rankPrefers]
      push_cast
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib]
    rw [← h01, ← h12, ← h20]
    ring
  have hlo : ∑ σ, Pr σ * 1 ≤ ∑ σ, Pr σ * (cyclicCount σ : ℝ) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast (cyclicCount_bounds σ).1) (hnn σ)
  have hhi : ∑ σ, Pr σ * (cyclicCount σ : ℝ) ≤ ∑ σ, Pr σ * 2 :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast (cyclicCount_bounds σ).2) (hnn σ)
  rw [← Finset.sum_mul, hsum] at hlo hhi
  constructor <;> linarith

/-- The number of rankings with `a ≻ b` is three for distinct `a, b`. -/
theorem rankPrefers_card (a b : Fin 3) (hab : a ≠ b) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => rankPrefers σ a b).card = 3 := by
  revert a b
  unfold rankPrefers
  decide

/-- The total cyclic count over the rankings with `a ≻ b`: five for a cyclic pair `b = a + 1`,
four otherwise. -/
theorem rankPrefers_cyclicCount_sum (a b : Fin 3) (hab : a ≠ b) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => rankPrefers σ a b), cyclicCount σ =
      if b = a + 1 then 5 else 4 := by
  revert a b
  unfold rankPrefers cyclicCount
  decide

/-- The explicit distribution used for sufficiency: probability `1/6 + (α - 1/2)` on the three
rankings with two cyclic pairs and `1/6 - (α - 1/2)` on the other three. -/
noncomputable def cyclicDistribution (α : ℝ) (σ : Equiv.Perm (Fin 3)) : ℝ :=
  1 / 6 + (α - 1 / 2) * (2 * (cyclicCount σ : ℝ) - 3)

/-- **Exercise 1.D.5** (MWG, p. 16), sufficiency. If `1/3 ≤ α ≤ 2/3`, the cyclic function is
rationalized by `cyclicDistribution α`. -/
theorem cyclicChoice_rationalizable_of_bounds {α : ℝ} (h1 : 1 / 3 ≤ α) (h2 : α ≤ 2 / 3) :
    StochasticRationalizable (cyclicChoice α) := by
  have hsumFilter : ∀ s : Finset (Equiv.Perm (Fin 3)), ∑ σ ∈ s, cyclicDistribution α σ =
      s.card / 6 + (α - 1 / 2) * (2 * ((∑ σ ∈ s, cyclicCount σ : ℕ) : ℝ) - 3 * s.card) := by
    intro s
    simp only [cyclicDistribution, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Nat.cast_sum]
    ring
  refine ⟨cyclicDistribution α, fun σ => ?_, ?_, fun a b hab => ?_⟩
  · unfold cyclicDistribution
    rcases cyclicCount_bounds σ with ⟨hl, hu⟩
    have : cyclicCount σ = 1 ∨ cyclicCount σ = 2 := by omega
    rcases this with h | h <;> rw [h] <;> push_cast <;> linarith
  · rw [hsumFilter]
    have hc : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by decide
    have hs : ∑ σ : Equiv.Perm (Fin 3), cyclicCount σ = 9 := by
      unfold cyclicCount
      decide
    rw [hc, hs]
    push_cast
    ring
  · rw [hsumFilter, rankPrefers_card a b hab, rankPrefers_cyclicCount_sum a b hab]
    unfold cyclicChoice
    split_ifs <;> push_cast <;> ring

/-- **Exercise 1.D.5** (MWG, p. 16). The cyclic stochastic choice function is rationalizable by
preferences iff `1/3 ≤ α ≤ 2/3`. -/
theorem cyclicChoice_rationalizable_iff (α : ℝ) :
    StochasticRationalizable (cyclicChoice α) ↔ 1 / 3 ≤ α ∧ α ≤ 2 / 3 :=
  ⟨cyclicChoice_bounds_of_rationalizable, fun h => cyclicChoice_rationalizable_of_bounds h.1 h.2⟩

/-- **Exercise 1.D.5(a)** (MWG, p. 16). `C({x,y}) = C({y,z}) = C({z,x}) = (1/2, 1/2)` can be
rationalized by preferences. -/
theorem exercise_1_D_5a : StochasticRationalizable (cyclicChoice (1 / 2)) :=
  (cyclicChoice_rationalizable_iff _).mpr ⟨by norm_num, by norm_num⟩

/-- **Exercise 1.D.5(b)** (MWG, p. 16). `C({x,y}) = C({y,z}) = C({z,x}) = (1/4, 3/4)` is not
rationalizable by preferences. -/
theorem exercise_1_D_5b : ¬StochasticRationalizable (cyclicChoice (1 / 4)) := fun h => by
  have := ((cyclicChoice_rationalizable_iff _).mp h).1
  norm_num at this

/-- **Exercise 1.D.5(c)** (MWG, p. 16). For `0 < α < 1`, the cyclic function is rationalizable
exactly on `[1/3, 2/3]`: it switches from rationalizable to nonrationalizable at `α = 1/3`
(below) and at `α = 2/3` (above). -/
theorem exercise_1_D_5c :
    (∀ α : ℝ, 0 < α → α < 1 → (StochasticRationalizable (cyclicChoice α) ↔
      α ∈ Set.Icc (1 / 3 : ℝ) (2 / 3))) ∧
      (∀ α : ℝ, 0 < α → α < 1 / 3 → ¬StochasticRationalizable (cyclicChoice α)) ∧
      (∀ α : ℝ, 2 / 3 < α → α < 1 → ¬StochasticRationalizable (cyclicChoice α)) := by
  refine ⟨fun α _ _ => cyclicChoice_rationalizable_iff α, fun α _ h h' => ?_,
    fun α h _ h' => ?_⟩
  · have := ((cyclicChoice_rationalizable_iff α).mp h').1
    linarith
  · have := ((cyclicChoice_rationalizable_iff α).mp h').2
    linarith

end MWG.PreferenceChoice

set_option linter.style.longLine false
#print axioms MWG.PreferenceChoice.definition_1_B_1
#print axioms MWG.PreferenceChoice.strict_iff
#print axioms MWG.PreferenceChoice.indifferent_iff
#print axioms MWG.PreferenceChoice.footnote_1_2
#print axioms MWG.PreferenceChoice.proposition_1_B_1_i
#print axioms MWG.PreferenceChoice.proposition_1_B_1_ii
#print axioms MWG.PreferenceChoice.proposition_1_B_1_iii
#print axioms MWG.PreferenceChoice.exercise_1_B_1
#print axioms MWG.PreferenceChoice.exercise_1_B_2
#print axioms MWG.PreferenceChoice.prefRel_no_strict_cycle
#print axioms MWG.PreferenceChoice.prefRel_just_perceptible
#print axioms MWG.PreferenceChoice.prefRel_framing
#print axioms MWG.PreferenceChoice.condorcetRank
#print axioms MWG.PreferenceChoice.condorcetMajority
#print axioms MWG.PreferenceChoice.prefRel_condorcet
#print axioms MWG.PreferenceChoice.prefRel_change_of_tastes
#print axioms MWG.PreferenceChoice.definition_1_B_2
#print axioms MWG.PreferenceChoice.exercise_1_B_3
#print axioms MWG.PreferenceChoice.prefRel_differences_not_ordinal
#print axioms MWG.PreferenceChoice.proposition_1_B_2
#print axioms MWG.PreferenceChoice.prefRel_rational_not_representable
#print axioms MWG.PreferenceChoice.exercise_1_B_4
#print axioms MWG.PreferenceChoice.exercise_1_B_5
#print axioms MWG.PreferenceChoice.ChoiceStructure
#print axioms MWG.PreferenceChoice.ChoiceStructure.mk
#print axioms MWG.PreferenceChoice.ChoiceStructure.budgets
#print axioms MWG.PreferenceChoice.ChoiceStructure.C
#print axioms MWG.PreferenceChoice.ChoiceStructure.budget_nonempty
#print axioms MWG.PreferenceChoice.ChoiceStructure.choice_subset
#print axioms MWG.PreferenceChoice.ChoiceStructure.choice_nonempty
#print axioms MWG.PreferenceChoice.WeakAxiom
#print axioms MWG.PreferenceChoice.RevealedPref
#print axioms MWG.PreferenceChoice.RevealedStrict
#print axioms MWG.PreferenceChoice.RevealedStrict'
#print axioms MWG.PreferenceChoice.weakAxiom_iff_revealed
#print axioms MWG.PreferenceChoice.weakAxiom_iff_coherentOn
#print axioms MWG.PreferenceChoice.threeChoice
#print axioms MWG.PreferenceChoice.threeChoice_ne
#print axioms MWG.PreferenceChoice.threeChoice_C_xy
#print axioms MWG.PreferenceChoice.threeChoice_C_xyz
#print axioms MWG.PreferenceChoice.example_1_C_1_C₁
#print axioms MWG.PreferenceChoice.example_1_C_1_C₂
#print axioms MWG.PreferenceChoice.threeChoice_budgets
#print axioms MWG.PreferenceChoice.example_1_C_2_C₁
#print axioms MWG.PreferenceChoice.example_1_C_2_C₂
#print axioms MWG.PreferenceChoice.exercise_1_C_1
#print axioms MWG.PreferenceChoice.exercise_1_C_2
#print axioms MWG.PreferenceChoice.exercise_1_C_3a
#print axioms MWG.PreferenceChoice.exercise_1_C_3a_without_weakAxiom
#print axioms MWG.PreferenceChoice.revealedStrict_of_revealedStrict'
#print axioms MWG.PreferenceChoice.cyclicPairs
#print axioms MWG.PreferenceChoice.cyclicPairs_values
#print axioms MWG.PreferenceChoice.cyclicPairs_budget_cases
#print axioms MWG.PreferenceChoice.cyclicPairs_weakAxiom
#print axioms MWG.PreferenceChoice.revealedPref_not_complete
#print axioms MWG.PreferenceChoice.revealedPref_not_transitive
#print axioms MWG.PreferenceChoice.exercise_1_C_3b
#print axioms MWG.PreferenceChoice.exercise_1_C_3c
#print axioms MWG.PreferenceChoice.mem_prefChoice_iff
#print axioms MWG.PreferenceChoice.prefChoice_can_be_empty
#print axioms MWG.PreferenceChoice.generatedStructure
#print axioms MWG.PreferenceChoice.proposition_1_D_1
#print axioms MWG.PreferenceChoice.Rationalizes
#print axioms MWG.PreferenceChoice.Rationalizable
#print axioms MWG.PreferenceChoice.weakAxiom_of_rationalizes
#print axioms MWG.PreferenceChoice.example_1_D_1
#print axioms MWG.PreferenceChoice.ContainsSmallSubsets
#print axioms MWG.PreferenceChoice.containsSmallSubsets_pair
#print axioms MWG.PreferenceChoice.containsSmallSubsets_triple
#print axioms MWG.PreferenceChoice.revealedPref_iff_mem_pair
#print axioms MWG.PreferenceChoice.proposition_1_D_2_rational
#print axioms MWG.PreferenceChoice.proposition_1_D_2_generates
#print axioms MWG.PreferenceChoice.proposition_1_D_2_unique
#print axioms MWG.PreferenceChoice.proposition_1_D_2
#print axioms MWG.PreferenceChoice.weakAxiom_iff_rationalizable
#print axioms MWG.PreferenceChoice.WeaklyRationalizes
#print axioms MWG.PreferenceChoice.weaklyRationalizes_of_rationalizes
#print axioms MWG.PreferenceChoice.weaklyRationalizes_indifference
#print axioms MWG.PreferenceChoice.exercise_1_D_1_structure
#print axioms MWG.PreferenceChoice.exercise_1_D_1a
#print axioms MWG.PreferenceChoice.exercise_1_D_1b
#print axioms MWG.PreferenceChoice.exercise_1_D_2
#print axioms MWG.PreferenceChoice.exercise_1_D_3
#print axioms MWG.PreferenceChoice.exercise_1_D_4
#print axioms MWG.PreferenceChoice.rankPrefers
#print axioms MWG.PreferenceChoice.rankPrefers_strictTotal
#print axioms MWG.PreferenceChoice.rankPrefers_injective
#print axioms MWG.PreferenceChoice.StochasticRationalizable
#print axioms MWG.PreferenceChoice.cyclicChoice
#print axioms MWG.PreferenceChoice.cyclicChoice_valid
#print axioms MWG.PreferenceChoice.cyclicCount
#print axioms MWG.PreferenceChoice.cyclicCount_bounds
#print axioms MWG.PreferenceChoice.cyclicChoice_bounds_of_rationalizable
#print axioms MWG.PreferenceChoice.rankPrefers_card
#print axioms MWG.PreferenceChoice.rankPrefers_cyclicCount_sum
#print axioms MWG.PreferenceChoice.cyclicDistribution
#print axioms MWG.PreferenceChoice.cyclicChoice_rationalizable_of_bounds
#print axioms MWG.PreferenceChoice.cyclicChoice_rationalizable_iff
#print axioms MWG.PreferenceChoice.exercise_1_D_5a
#print axioms MWG.PreferenceChoice.exercise_1_D_5b
#print axioms MWG.PreferenceChoice.exercise_1_D_5c
