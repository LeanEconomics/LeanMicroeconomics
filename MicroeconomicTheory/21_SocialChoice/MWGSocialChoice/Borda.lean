/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Aggregation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

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
