/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Aggregation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

/-!
# Arrow's impossibility theorem

MWG, Section 21.C, pp. 796-799: Definition 21.C.4, Proposition 21.C.1 and Exercise 21.C.1.

We follow the book's decisive-set proof, Steps 1-10, for a fixed social welfare functional `F`
that is Paretian and pairwise independent on a domain `A` that is either `𝓡^I` or `𝓟^I`, with
finitely many agents and at least three alternatives (the set of alternatives may be
infinite). Profiles needed in the steps are built with `scorePref`, which lies in `𝓟` and hence
in both domains.

**Departure (proof repair).** In Step 9 the book takes, for the agents of `T ⊆ I \ S` who
regard `x` as at least as good as `y`, a profile with `x ≻ᵢ y ≻ᵢ z`. On `𝓡^I` an agent of `T`
may be indifferent between `x` and `y`, and then pairwise independence does not relate the two
profiles. We use `x ∼ᵢ y ≻ᵢ z` for such agents (a profile in `𝓡^I`; on `𝓟^I` the case does
not arise); the rest of the argument is unchanged.

Non-vacuity: `dictatorSWF h` (`F(≿) = ≿ₕ`) is a Paretian, pairwise independent social welfare
functional on both domains, so the hypotheses of Proposition 21.C.1 have instances (e.g. two
agents and three alternatives), and its conclusion is attained.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility

variable {ι X : Type*}

/-- The two domains of Proposition 21.C.1: `A = 𝓡^I` or `A = 𝓟^I`. -/
def StandardDomain (A : Set (Profile ι X)) : Prop :=
  A = RationalProfiles ι X ∨ A = StrictProfiles ι X

/-- Profiles of score orders lie in both standard domains. -/
theorem StandardDomain.score_mem {A : Set (Profile ι X)} (hA : StandardDomain A)
    (s : ι → X → ℕ) : (fun i => scorePref (s i)) ∈ A := by
  rcases hA with rfl | rfl
  · exact fun i => strictPrefs_subset (scorePref_mem (s i))
  · exact fun i => scorePref_mem (s i)

/-- Standard domains consist of rational profiles. -/
theorem StandardDomain.rational {A : Set (Profile ι X)} (hA : StandardDomain A)
    {p : Profile ι X} (hp : p ∈ A) (i : ι) : Rational (p i) := by
  rcases hA with rfl | rfl
  · exact hp i
  · exact (hp i).1

/-- **Definition 21.C.4(i)** (MWG, p. 797). `S` is decisive for `x` over `y`: whenever every
agent in `S` prefers `x` to `y` and every agent outside `S` prefers `y` to `x`, `x` is socially
preferred to `y`. -/
def DecisiveFor (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι)
    (x y : X) : Prop :=
  ∀ p ∈ A, (∀ i ∈ S, Strict (p i) x y) → (∀ i ∉ S, Strict (p i) y x) → Strict (F p) x y

/-- **Definition 21.C.4(ii)** (MWG, p. 797). `S` is decisive: decisive for `x` over `y` for
every pair of (distinct) alternatives. -/
def Decisive (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι) : Prop :=
  ∀ x y, x ≠ y → DecisiveFor A F S x y

/-- **Definition 21.C.4(iii)** (MWG, p. 797). `S` is completely decisive for `x` over `y`:
whenever every agent in `S` prefers `x` to `y`, `x` is socially preferred to `y`. -/
def CompletelyDecisiveFor (A : Set (Profile ι X)) (F : Profile ι X → X → X → Prop) (S : Set ι)
    (x y : X) : Prop :=
  ∀ p ∈ A, (∀ i ∈ S, Strict (p i) x y) → Strict (F p) x y

variable {A : Set (Profile ι X)} {F : Profile ι X → X → X → Prop}

/-- **Step 1** of the proof of Proposition 21.C.1 (MWG, p. 797). If `S` is decisive for `x`
over `y`, then it is decisive for `x` over any `z ≠ x`. -/
theorem arrow_step_1 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzx : z ≠ x) : DecisiveFor A F S x z := by
  classical
  by_cases hzy : z = y
  · subst hzy
    exact h
  intro p hp hS hN
  let q : Profile ι X := fun i =>
    scorePref (if i ∈ S then rank3 x y z else rank3 y z x)
  have hq : q ∈ A := hA.score_mem _
  have r1 := rank3_strict hxy (Ne.symm hzx) (Ne.symm hzy)
  have r2 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have h1 : Strict (F q) x y := h q hq (fun i hi => by simpa only [q, hi, ↓reduceIte] using r1.1)
    (fun i hi => by simpa only [q, hi, ↓reduceIte] using r2.2.2)
  have h2 : Strict (F q) y z := hP q hq y z fun i => by
    by_cases hi : i ∈ S
    · simpa only [q, hi, ↓reduceIte] using r1.2.1
    · simpa only [q, hi, ↓reduceIte] using r2.1
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) h1 h2)
  by_cases hi : i ∈ S
  · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using r1.2.2⟩
  · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using r2.2.1⟩)

/-- **Exercise 21.C.1** (MWG, p. 812), the second half of Step 1 (MWG, p. 797). If `S` is
decisive for `x` over `y`, then it is decisive for any `z ≠ y` over `y`. -/
theorem exercise_21_C_1 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzy : z ≠ y) : DecisiveFor A F S z y := by
  classical
  by_cases hzx : z = x
  · subst hzx
    exact h
  intro p hp hS hN
  let q : Profile ι X := fun i =>
    scorePref (if i ∈ S then rank3 z x y else rank3 y z x)
  have hq : q ∈ A := hA.score_mem _
  have rs := rank3_strict hzx hzy hxy
  have rn := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have h1 : Strict (F q) z x := hP q hq z x fun i => by
    by_cases hi : i ∈ S
    · simpa only [q, hi, ↓reduceIte] using rs.1
    · simpa only [q, hi, ↓reduceIte] using rn.2.1
  have h2 : Strict (F q) x y := h q hq (fun i hi => by simpa only [q, hi, ↓reduceIte] using rs.2.1)
    (fun i hi => by simpa only [q, hi, ↓reduceIte] using rn.2.2)
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) h1 h2)
  by_cases hi : i ∈ S
  · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using rs.2.2⟩
  · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using rn.1⟩)

/-- **Step 2** of the proof of Proposition 21.C.1 (MWG, p. 797). If `S` is decisive for `x`
over `y` and `z` is a third alternative, then `S` is decisive for `z` over `w` and for `w`
over `z`, for every `w ≠ z`. -/
theorem arrow_step_2 (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) {S : Set ι} {x y z w : X} (hxy : x ≠ y)
    (h : DecisiveFor A F S x y) (hzx : z ≠ x) (hzy : z ≠ y) (hwz : w ≠ z) :
    DecisiveFor A F S z w ∧ DecisiveFor A F S w z := by
  have hxz : DecisiveFor A F S x z := arrow_step_1 hA hF hP hI hxy h hzx
  have hzy' : DecisiveFor A F S z y := exercise_21_C_1 hA hF hP hI hxy h hzy
  exact ⟨arrow_step_1 hA hF hP hI hzy hzy' hwz,
    exercise_21_C_1 hA hF hP hI (Ne.symm hzx) hxz hwz⟩

/-- **Step 3** of the proof of Proposition 21.C.1 (MWG, p. 797). With at least three
alternatives, a set decisive for some `x` over some `y ≠ x` is decisive. -/
theorem arrow_step_3 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S : Set ι}
    {x y : X} (hxy : x ≠ y) (h : DecisiveFor A F S x y) : Decisive A F S := by
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  intro v w hvw
  by_cases hv : v = z
  · subst hv
    exact (arrow_step_2 hA hF hP hI hxy h hzx hzy (Ne.symm hvw)).1
  by_cases hw : w = z
  · subst hw
    exact (arrow_step_2 hA hF hP hI hxy h hzx hzy hvw).2
  have hzw : DecisiveFor A F S z w := (arrow_step_2 hA hF hP hI hxy h hzx hzy hw).1
  exact exercise_21_C_1 hA hF hP hI (Ne.symm hw) hzw hvw

/-- **Step 4** of the proof of Proposition 21.C.1 (MWG, p. 798). The intersection of two
decisive sets is decisive. -/
theorem arrow_step_4 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S T : Set ι}
    (hS : Decisive A F S) (hT : Decisive A F T) : Decisive A F (S ∩ T) := by
  classical
  obtain ⟨x, y, -, hxy, -, -⟩ := id hX
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  refine arrow_step_3 hX hA hF hP hI hxy fun p hp hST hN => ?_
  let q : Profile ι X := fun i => scorePref
    (if i ∈ S then (if i ∈ T then rank3 x z y else rank3 z y x)
      else (if i ∈ T then rank3 y x z else rank3 y z x))
  have hq : q ∈ A := hA.score_mem _
  have a1 := rank3_strict (Ne.symm hzx) hxy hzy
  have a2 := rank3_strict hzy hzx (Ne.symm hxy)
  have a3 := rank3_strict (Ne.symm hxy) (Ne.symm hzy) (Ne.symm hzx)
  have a4 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have hzy' : Strict (F q) z y := hS z y hzy q hq (fun i hi => by
      by_cases hiT : i ∈ T
      · simpa only [q, hi, hiT, ↓reduceIte] using a1.2.1
      · simpa only [q, hi, hiT, ↓reduceIte] using a2.1) (fun i hi => by
      by_cases hiT : i ∈ T
      · simpa only [q, hi, hiT, ↓reduceIte] using a3.2.2
      · simpa only [q, hi, hiT, ↓reduceIte] using a4.1)
  have hxz : Strict (F q) x z := hT x z (Ne.symm hzx) q hq (fun i hi => by
      by_cases hiS : i ∈ S
      · simpa only [q, hi, hiS, ↓reduceIte] using a1.1
      · simpa only [q, hi, hiS, ↓reduceIte] using a3.2.1) (fun i hi => by
      by_cases hiS : i ∈ S
      · simpa only [q, hi, hiS, ↓reduceIte] using a2.2.2
      · simpa only [q, hi, hiS, ↓reduceIte] using a4.2.1)
  refine hI.strict_transfer hp hq (fun i => ?_) (strict_trans (hF q hq) hxz hzy')
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact Or.inl ⟨hST i ⟨hiS, hiT⟩, by simpa only [q, hiS, hiT, ↓reduceIte] using a1.2.2⟩
  · refine Or.inr (Or.inl ⟨hN i fun h => hiT h.2, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a2.2.1
  · refine Or.inr (Or.inl ⟨hN i fun h => hiS h.1, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a3.1
  · refine Or.inr (Or.inl ⟨hN i fun h => hiS h.1, ?_⟩)
    simpa only [q, hiS, hiT, ↓reduceIte] using a4.2.2

/-- **Step 5** of the proof of Proposition 21.C.1 (MWG, p. 798). For any `S`, either `S` or
its complement is decisive. -/
theorem arrow_step_5 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) (S : Set ι) :
    Decisive A F S ∨ Decisive A F Sᶜ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hX
  let q : Profile ι X := fun i => scorePref (if i ∈ S then rank3 x z y else rank3 y x z)
  have hq : q ∈ A := hA.score_mem _
  have a1 := rank3_strict hxz hxy (Ne.symm hyz)
  have a2 := rank3_strict (Ne.symm hxy) hyz hxz
  by_cases hF1 : Strict (F q) x y
  · left
    refine arrow_step_3 ⟨x, y, z, hxy, hxz, hyz⟩ hA hF hP hI hxy fun p hp hS hN => ?_
    refine hI.strict_transfer hp hq (fun i => ?_) hF1
    by_cases hi : i ∈ S
    · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using a1.2.2⟩
    · exact Or.inr (Or.inl ⟨hN i hi, by simpa only [q, hi, ↓reduceIte] using a2.1⟩)
  · right
    have hyx : F q y x := weak_of_not_strict (hF q hq).1 hF1
    have hxz' : Strict (F q) x z := hP q hq x z fun i => by
      by_cases hi : i ∈ S
      · simpa only [q, hi, ↓reduceIte] using a1.1
      · simpa only [q, hi, ↓reduceIte] using a2.2.1
    have hyz' : Strict (F q) y z := strict_of_weak_strict (hF q hq) hyx hxz'
    refine arrow_step_3 ⟨x, y, z, hxy, hxz, hyz⟩ hA hF hP hI hyz fun p hp hS hN => ?_
    refine hI.strict_transfer hp hq (fun i => ?_) hyz'
    by_cases hi : i ∈ S
    · refine Or.inr (Or.inl ⟨hN i (by simpa using hi), ?_⟩)
      simpa only [q, hi, ↓reduceIte] using a1.2.1
    · exact Or.inl ⟨hS i hi, by simpa only [q, hi, ↓reduceIte] using a2.2.2⟩

/-- **Step 6** of the proof of Proposition 21.C.1 (MWG, p. 798), first remark: by the Pareto
property the empty set of agents is not decisive. -/
theorem arrow_empty_not_decisive (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hP : Paretian A F) : ¬Decisive A F ∅ := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hX
  intro hD
  let q : Profile ι X := fun _ => scorePref (rank3 y x z)
  have hq : q ∈ A := hA.score_mem _
  have a := rank3_strict (Ne.symm hxy) hyz hxz
  have h1 : Strict (F q) x y := hD x y hxy q hq (fun _ hi => absurd hi (Set.notMem_empty _))
    (fun _ _ => a.1)
  exact strict_asymm h1 (hP q hq y x fun _ => a.1)

/-- **Step 6** of the proof of Proposition 21.C.1 (MWG, p. 798). A superset of a decisive set
is decisive. -/
theorem arrow_step_6 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S T : Set ι}
    (hS : Decisive A F S) (hST : S ⊆ T) : Decisive A F T := by
  rcases arrow_step_5 hX hA hF hP hI T with h | h
  · exact h
  · exfalso
    have h' := arrow_step_4 hX hA hF hP hI hS h
    have he : S ∩ Tᶜ = ∅ := by
      ext i
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      exact fun hi => hST hi
    rw [he] at h'
    exact arrow_empty_not_decisive hX hA hP h'

/-- **Step 7** of the proof of Proposition 21.C.1 (MWG, p. 798). A decisive set with more than
one agent has a decisive strict subset. -/
theorem arrow_step_7 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) (S : Finset ι) (hS : Decisive A F ↑S)
    (hcard : 1 < S.card) : ∃ S' ⊂ S, Decisive A F ↑S' := by
  classical
  obtain ⟨h, hh⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  by_cases hD : Decisive A F ↑(S.erase h)
  · exact ⟨S.erase h, Finset.erase_ssubset hh, hD⟩
  · rcases arrow_step_5 hX hA hF hP hI ↑(S.erase h) with h1 | h1
    · exact absurd h1 hD
    · have h2 := arrow_step_4 hX hA hF hP hI hS h1
      have he : (↑S ∩ (↑(S.erase h) : Set ι)ᶜ : Set ι) = ↑({h} : Finset ι) := by
        ext i
        simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_compl_iff, Finset.mem_erase,
          not_and, Finset.coe_singleton, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hi, hi'⟩
          by_contra hne
          exact hi' hne hi
        · rintro rfl
          exact ⟨hh, fun h' => absurd rfl h'⟩
      rw [he] at h2
      refine ⟨{h}, ?_, h2⟩
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.singleton_subset_iff.2 hh, fun he' => ?_⟩
      rw [← he', Finset.card_singleton] at hcard
      exact lt_irrefl _ hcard

/-- **Step 8** of the proof of Proposition 21.C.1 (MWG, p. 798). Some single agent forms a
decisive set (the set of all agents is decisive by the Pareto property, and Step 7 is
iterated; we take a decisive set of minimal cardinality). -/
theorem arrow_step_8 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) : ∃ h, Decisive A F {h} := by
  classical
  have := Fintype.ofFinite ι
  have huniv : Decisive A F ↑(Finset.univ : Finset ι) :=
    fun x y _ p hp hS _ => hP p hp x y fun i => hS i (by simp)
  let D := (Finset.univ : Finset (Finset ι)).filter fun T : Finset ι => Decisive A F (↑T : Set ι)
  have hmem : (Finset.univ : Finset ι) ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huniv
  have hne : D.Nonempty := ⟨Finset.univ, hmem⟩
  obtain ⟨T, hT, hmin⟩ := D.exists_min_image Finset.card hne
  have hTd : Decisive A F ↑T := (Finset.mem_filter.1 hT).2
  rcases Nat.lt_or_ge 1 T.card with h2 | h1
  · obtain ⟨S', hS'T, hS'⟩ := arrow_step_7 hX hA hF hP hI T hTd h2
    have h3 := hmin S' (by simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
                           exact hS')
    have h4 := Finset.card_lt_card hS'T
    omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1'
    · rw [Finset.card_eq_zero] at h0
      subst h0
      exact absurd (by simpa using hTd) (arrow_empty_not_decisive hX hA hP)
    · obtain ⟨h, rfl⟩ := Finset.card_eq_one.1 h1'
      exact ⟨h, by simpa using hTd⟩

/-- Scores putting `x` and `y` jointly on top (score 2), `z` next (score 1). -/
noncomputable def pairTop (x y z : X) : X → ℕ :=
  by classical exact fun w => if w = x ∨ w = y then 2 else if w = z then 1 else 0

/-- **Step 9** of the proof of Proposition 21.C.1 (MWG, pp. 798-799). A decisive set is
completely decisive for every `x` over every `y`. (For agents outside `S` indifferent between
`x` and `y` we use `x ∼ y ≻ z`; see the module docstring.) -/
theorem arrow_step_9 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {S : Set ι}
    (hS : Decisive A F S) {x y : X} (hxy : x ≠ y) : CompletelyDecisiveFor A F S x y := by
  classical
  obtain ⟨z, hzx, hzy⟩ := exists_third (x := x) (y := y) hX
  intro p hp hSp
  let q : Profile ι X := fun i =>
    if i ∈ S then scorePref (rank3 x z y)
    else if Strict (p i) y x then scorePref (rank3 y z x)
    else if Strict (p i) x y then scorePref (rank3 x y z)
    else natPref (pairTop x y z)
  have ptx : pairTop x y z x = 2 := by simp [pairTop]
  have pty : pairTop x y z y = 2 := by simp [pairTop]
  have ptz : pairTop x y z z = 1 := by simp [pairTop, hzx, hzy]
  have a1 := rank3_strict (Ne.symm hzx) hxy hzy
  have a2 := rank3_strict (Ne.symm hzy) (Ne.symm hxy) hzx
  have a3 := rank3_strict hxy (Ne.symm hzx) (Ne.symm hzy)
  have nxz : Strict (natPref (pairTop x y z)) x z := (natPref_strict_iff _ _ _).2 (by omega)
  have nyz : Strict (natPref (pairTop x y z)) y z := (natPref_strict_iff _ _ _).2 (by omega)
  have nxy : Indifferent (natPref (pairTop x y z)) x y :=
    (natPref_indifferent_iff _ _ _).2 (by omega)
  have hq : q ∈ A := by
    rcases hA with rfl | rfl
    · intro i
      simp only [q]
      split_ifs
      · exact strictPrefs_subset (scorePref_mem _)
      · exact strictPrefs_subset (scorePref_mem _)
      · exact strictPrefs_subset (scorePref_mem _)
      · exact natPref_rational _
    · intro i
      simp only [q]
      split_ifs with h1 h2 h3
      · exact scorePref_mem _
      · exact scorePref_mem _
      · exact scorePref_mem _
      · exfalso
        have hc := (hp i).1.1
        exact hxy ((hp i).2 x y (weak_of_not_strict hc h2) (weak_of_not_strict hc h3))
  let U : Set ι := S ∪ {i | ¬Strict (p i) y x}
  have hU : Decisive A F U := arrow_step_6 hX hA hF hP hI hS Set.subset_union_left
  have hxz : Strict (F q) x z := hU x z (Ne.symm hzx) q hq (fun i hi => by
      by_cases h1 : i ∈ S
      · simpa only [q, h1, ↓reduceIte] using a1.1
      · have h2 : ¬Strict (p i) y x := by
          rcases hi with hi | hi
          · exact absurd hi h1
          · exact hi
        by_cases h3 : Strict (p i) x y
        · simpa only [q, h1, h2, h3, ↓reduceIte] using a3.2.2
        · simpa only [q, h1, h2, h3, ↓reduceIte] using nxz) (fun i hi => by
      have h1 : i ∉ S := fun h => hi (Or.inl h)
      have h2 : Strict (p i) y x := by
        by_contra h
        exact hi (Or.inr h)
      simpa only [q, h1, h2, ↓reduceIte] using a2.2.1)
  have hzy' : Strict (F q) z y := hS z y hzy q hq (fun i hi => by
      simpa only [q, hi, ↓reduceIte] using a1.2.1) (fun i hi => by
      by_cases h2 : Strict (p i) y x
      · simpa only [q, hi, h2, ↓reduceIte] using a2.1
      · by_cases h3 : Strict (p i) x y
        · simpa only [q, hi, h2, h3, ↓reduceIte] using a3.2.1
        · simpa only [q, hi, h2, h3, ↓reduceIte] using nyz)
  have hagree : ∀ i, (p i x y ↔ q i x y) ∧ (p i y x ↔ q i y x) := by
    intro i
    apply agree_of_same_ranking
    by_cases h1 : i ∈ S
    · exact Or.inl ⟨hSp i h1, by simpa only [q, h1, ↓reduceIte] using a1.2.2⟩
    · by_cases h2 : Strict (p i) y x
      · exact Or.inr (Or.inl ⟨h2, by simpa only [q, h1, h2, ↓reduceIte] using a2.2.2⟩)
      · by_cases h3 : Strict (p i) x y
        · exact Or.inl ⟨h3, by simpa only [q, h1, h2, h3, ↓reduceIte] using a3.1⟩
        · have hc := (hA.rational hp i).1
          refine Or.inr (Or.inr ⟨⟨weak_of_not_strict hc h2, weak_of_not_strict hc h3⟩, ?_⟩)
          simpa only [q, h1, h2, h3, ↓reduceIte] using nxy
  have hfin := strict_trans (hF q hq) hxz hzy'
  have := hI p hp q hq x y hagree
  exact ⟨this.1.2 hfin.1, fun h' => hfin.2 (this.2.1 h')⟩

/-- **Step 10** of the proof of Proposition 21.C.1 (MWG, p. 799). If `{h}` is decisive, then
`h` is a dictator. -/
theorem arrow_step_10 (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) (hA : StandardDomain A)
    (hF : IsSWF A F) (hP : Paretian A F) (hI : PairwiseIndependent A F) {h : ι}
    (hh : Decisive A F {h}) : IsDictator A F h := by
  intro p hp x y hxy
  have hne : x ≠ y := by
    rintro rfl
    exact hxy.2 hxy.1
  exact arrow_step_9 hX hA hF hP hI hh hne p hp fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    exact hi ▸ hxy

/-- **Proposition 21.C.1 (Arrow's impossibility theorem)** (MWG, p. 796). With at least three
alternatives, finitely many agents and domain `𝓡^I` or `𝓟^I`, every Paretian social welfare
functional satisfying the pairwise independence condition is dictatorial. -/
theorem proposition_21_C_1 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hF : IsSWF A F) (hP : Paretian A F)
    (hI : PairwiseIndependent A F) : Dictatorial A F := by
  obtain ⟨h, hh⟩ := arrow_step_8 hX hA hF hP hI
  exact ⟨h, arrow_step_10 hX hA hF hP hI hh⟩

/-- The dictatorial social welfare functional `F(≿) = ≿ₕ`. -/
def dictatorSWF (h : ι) : Profile ι X → X → X → Prop := fun p => p h

/-- The dictatorial functional is a Paretian, pairwise independent social welfare functional
with dictator `h`, on any standard domain. -/
theorem dictatorSWF_spec {A : Set (Profile ι X)} (hA : StandardDomain A) (h : ι) :
    IsSWF A (dictatorSWF h) ∧ Paretian A (dictatorSWF h) ∧
      PairwiseIndependent A (dictatorSWF h) ∧ IsDictator A (dictatorSWF h) h :=
  ⟨fun _ hp => hA.rational hp h, fun _ _ _ _ hall => hall h,
    fun _ _ _ _ _ _ hagree => hagree h, fun _ _ _ _ hxy => hxy⟩

/-- **Proposition 21.C.1**, non-vacuity (MWG, p. 796). Its hypotheses are jointly satisfiable
(two agents, three alternatives, both domains), and the dictatorship it asserts occurs. -/
theorem proposition_21_C_1_nonvacuous :
    (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      (∀ A : Set (Profile (Fin 2) (Fin 3)), StandardDomain A →
        IsSWF A (dictatorSWF 0) ∧ Paretian A (dictatorSWF 0) ∧
          PairwiseIndependent A (dictatorSWF 0) ∧ Dictatorial A (dictatorSWF 0)) ∧
      StandardDomain (RationalProfiles (Fin 2) (Fin 3)) ∧
      StandardDomain (StrictProfiles (Fin 2) (Fin 3)) := by
  refine ⟨⟨0, 1, 2, by decide, by decide, by decide⟩, fun A hA => ?_, Or.inl rfl, Or.inr rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := dictatorSWF_spec hA (0 : Fin 2)
  exact ⟨h1, h2, h3, ⟨0, h4⟩⟩

end MWG.SocialChoice
