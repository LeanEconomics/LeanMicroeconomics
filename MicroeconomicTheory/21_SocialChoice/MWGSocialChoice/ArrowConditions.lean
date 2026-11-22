/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.SinglePeakedExercises
import MWGSocialChoice.Arrow

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
