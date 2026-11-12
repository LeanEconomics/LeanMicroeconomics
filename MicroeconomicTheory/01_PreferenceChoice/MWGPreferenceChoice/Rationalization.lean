/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPreferenceChoice.PreferenceRelations
import MWGPreferenceChoice.ChoiceRules
import ChoicePreferenceUtility.Rationalization

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
