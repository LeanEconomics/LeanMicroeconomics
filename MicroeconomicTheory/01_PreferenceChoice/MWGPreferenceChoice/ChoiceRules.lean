/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Basic

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
