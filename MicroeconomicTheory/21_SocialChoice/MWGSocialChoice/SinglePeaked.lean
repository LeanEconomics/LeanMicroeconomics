/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.WeakRationality
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

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
