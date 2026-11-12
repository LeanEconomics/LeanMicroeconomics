/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.FiniteUtility
import ChoicePreferenceUtility.UtilityEquivalence
import ChoicePreferenceUtility.Lexicographic

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
