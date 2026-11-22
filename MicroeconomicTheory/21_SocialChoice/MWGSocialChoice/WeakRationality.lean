/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Borda

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
