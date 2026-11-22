/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.SinglePeaked
import Mathlib.Tactic.Order

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
