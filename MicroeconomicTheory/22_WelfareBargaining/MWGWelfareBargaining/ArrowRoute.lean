/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.FunctionalExercises

/-!
# Arrow's theorem through invariance (Exercise 22.D.5) and non-vacuity of Section 22.D

MWG, p. 837 (last paragraph of Section 22.D) and Exercise 22.D.5, p. 852.

From a Chapter 21 social welfare functional `F` on `𝓡^I` (Chapter 21's `IsSWF`, `Paretian`,
`PairwiseIndependent`, imported from `MWGSocialChoice`) we build `F'(ũ) = F(≿(ũ₁), …, ≿(ũ_I))`,
where `≿(ũᵢ)` is the preference induced by `ũᵢ` (`inducedFunctional`). We verify the three
claims of Exercise 22.D.5: `F'` inherits pairwise independence and the Pareto property, it does
not allow interpersonal comparisons, and a dictator of `F'` is a dictator of `F`.

**Correction.** Definition 21.C.2 (Pareto) only asks unanimous strict preference to be
respected, while Definition 22.D.2 also asks unanimous weak preference to be respected. `F'`
inherits the strict half but not the weak half: the "tie-broken dictatorship"
`tieBreakDict` (agent `0`'s strict preference, ties broken by a fixed order) is a Paretian,
pairwise independent social welfare functional on `𝓡^I` whose `F'` ranks two alternatives
strictly although everybody is indifferent (`exercise_22_D_5_weak_not_inherited`). With the
extra hypothesis that unanimous weak preference is respected, the route of p. 837 (Proposition
22.D.1, Exercise 22.D.3 and the extended Proposition 22.D.3) proves Arrow's theorem
(`exercise_22_D_5`). Arrow's theorem itself holds without the extra hypothesis (MWG
Proposition 21.C.1, `MWG.SocialChoice.proposition_21_C_1`).

The section closes with instances showing that the hypotheses of Propositions 22.D.1-22.D.3 are
satisfiable.
-/

namespace MWG.WelfareBargaining

open Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {ι X : Type*}

/-- **Section 22.D** (MWG, p. 837). The functional on utility profiles induced by a functional on
preference profiles: `F'(ũ₁, …, ũ_I) = F(≿₁, …, ≿_I)` with `≿ᵢ` induced by `ũᵢ`. -/
def inducedFunctional (F : Profile ι X → X → X → Prop) : UProfile ι X → X → X → Prop :=
  fun ũ => F (fun i => UtilityPref (ũ i))

theorem induced_mem (ũ : UProfile ι X) :
    (fun i => UtilityPref (ũ i)) ∈ RationalProfiles ι X :=
  fun i => proposition_1_3a (ũ i)

/-- **Exercise 22.D.5** (MWG, p. 852). `F'` is a social welfare functional. -/
theorem exercise_22_D_5_isUSWF {F : Profile ι X → X → X → Prop}
    (hF : IsSWF (RationalProfiles ι X) F) : IsUSWF (inducedFunctional F) :=
  fun ũ => hF _ (induced_mem ũ)

/-- **Exercise 22.D.5** (MWG, p. 852). `F'` inherits the strict half of the Pareto property. -/
theorem exercise_22_D_5_strict {F : Profile ι X → X → X → Prop}
    (hP : Paretian (RationalProfiles ι X) F) (ũ : UProfile ι X) (x y : X)
    (h : ∀ i, ũ i y < ũ i x) : Strict (inducedFunctional F ũ) x y :=
  hP _ (induced_mem ũ) x y fun i => ⟨(h i).le, not_le.2 (h i)⟩

/-- **Exercise 22.D.5** (MWG, p. 852). `F'` inherits pairwise independence. -/
theorem exercise_22_D_5_pairwise {F : Profile ι X → X → X → Prop}
    (hI : PairwiseIndependent (RationalProfiles ι X) F) :
    UPairwiseIndependent (inducedFunctional F) := by
  intro ũ ũ' x y hx hy
  refine (hI _ (induced_mem ũ) _ (induced_mem ũ') x y fun i => ⟨?_, ?_⟩).1
  · simp only [UtilityPref, hx, hy]
  · simp only [UtilityPref, hx, hy]

/-- **Exercise 22.D.5** (MWG, p. 852). `F'` does not allow interpersonal comparisons of utility
(Definition 22.D.5). -/
theorem exercise_22_D_5_noInterpersonal (F : Profile ι X → X → X → Prop) :
    NoInterpersonalComparisons (inducedFunctional F) := by
  intro β α hβ ũ
  unfold inducedFunctional
  congr 1
  funext i a b
  simp only [UtilityPref, add_le_add_iff_right]
  exact propext (mul_le_mul_iff_of_pos_left (hβ i))

/-- **Exercise 22.D.5** (MWG, p. 852). A dictator for `F'` is a dictator for `F` (on `𝓡^I`). -/
theorem exercise_22_D_5_dictator {F : Profile ι X → X → X → Prop}
    (hI : PairwiseIndependent (RationalProfiles ι X) F) {h : ι}
    (hh : ∀ (ũ : UProfile ι X) (x y : X), ũ h y < ũ h x → Strict (inducedFunctional F ũ) x y) :
    IsDictator (RationalProfiles ι X) F h := by
  classical
  intro p hp x y hxy
  have hne : x ≠ y := by rintro rfl; exact hxy.2 hxy.1
  let ũ : UProfile ι X := fun i z => if z = x then (if p i y x then 0 else 1)
    else (if p i x y then 0 else 1)
  have ex : ∀ i, ũ i x = if p i y x then 0 else 1 := fun i => by simp [ũ]
  have ey : ∀ i, ũ i y = if p i x y then 0 else 1 := fun i => by simp [ũ, Ne.symm hne]
  have hagree : ∀ i, (p i x y ↔ UtilityPref (ũ i) x y) ∧ (p i y x ↔ UtilityPref (ũ i) y x) := by
    intro i
    simp only [UtilityPref, ex, ey]
    have hc := (hp i).1 x y
    by_cases h1 : p i x y <;> by_cases h2 : p i y x <;> simp_all
  have hpi := hI p hp _ (induced_mem ũ) x y hagree
  have hs := hh ũ x y (by rw [ex, ey]; simp [hxy.1, hxy.2])
  exact ⟨hpi.1.2 hs.1, fun h' => hs.2 (hpi.2.1 h')⟩

/-- **Exercise 22.D.5, counterexample** (MWG, p. 852). The tie-broken dictatorship: agent `0`'s
strict preference prevails, and among alternatives she is indifferent between the smaller
label wins. -/
def tieBreakDict : Profile (Fin 1) (Fin 3) → Fin 3 → Fin 3 → Prop :=
  fun p a b => Strict (p 0) a b ∨ (Indifferent (p 0) a b ∧ a ≤ b)

/-- **Exercise 22.D.5, correction** (MWG, p. 852). The tie-broken dictatorship is a Paretian
(Definition 21.C.2), pairwise independent social welfare functional on `𝓡^I`, but the induced
functional `F'` violates the weak half of Definition 22.D.2: with everybody indifferent between
`1` and `0`, `F'` does not rank `1` weakly above `0`. -/
theorem exercise_22_D_5_weak_not_inherited :
    IsSWF (RationalProfiles (Fin 1) (Fin 3)) tieBreakDict ∧
      Paretian (RationalProfiles (Fin 1) (Fin 3)) tieBreakDict ∧
      PairwiseIndependent (RationalProfiles (Fin 1) (Fin 3)) tieBreakDict ∧
      ¬∀ (ũ : UProfile (Fin 1) (Fin 3)) (x y : Fin 3), (∀ i, ũ i y ≤ ũ i x) →
        inducedFunctional tieBreakDict ũ x y := by
  refine ⟨fun p hp => ?_, fun p hp a b hab => ?_, fun p hp p' hp' a b hagr => ?_, fun h => ?_⟩
  · have hr : Rational (p 0) := hp 0
    refine ⟨fun a b => ?_, fun a b c h1 h2 => ?_⟩
    · by_cases hab : p 0 a b <;> by_cases hba : p 0 b a
      · rcases le_total a b with h | h
        · exact Or.inl (Or.inr ⟨⟨hab, hba⟩, h⟩)
        · exact Or.inr (Or.inr ⟨⟨hba, hab⟩, h⟩)
      · exact Or.inl (Or.inl ⟨hab, hba⟩)
      · exact Or.inr (Or.inl ⟨hba, hab⟩)
      · exact absurd ((hr.1 a b).resolve_left hab) hba
    · rcases h1 with h1 | ⟨i1, l1⟩ <;> rcases h2 with h2 | ⟨i2, l2⟩
      · exact Or.inl (strict_trans hr h1 h2)
      · exact Or.inl (strict_of_strict_weak hr.2 h1 i2.1)
      · exact Or.inl (strict_of_weak_strict hr i1.1 h2)
      · exact Or.inr ⟨⟨hr.2 _ _ _ i1.1 i2.1, hr.2 _ _ _ i2.2 i1.2⟩, l1.trans l2⟩
  · have h0 := hab 0
    refine ⟨Or.inl h0, fun h' => ?_⟩
    rcases h' with h' | ⟨i', -⟩
    · exact h0.2 h'.1
    · exact h0.2 i'.1
  · have e := hagr 0
    simp [tieBreakDict, Strict, Indifferent, e.1, e.2]
  · have := h 0 1 0 fun _ => le_rfl
    simp only [inducedFunctional, tieBreakDict, Strict, Indifferent, UtilityPref,
      Pi.zero_apply, le_refl, not_true, and_false, true_and, false_or] at this
    exact absurd this (by decide)

/-- **Exercise 22.D.5** (MWG, pp. 837, 852), corrected. Arrow's impossibility theorem along the
lines of p. 837: if `F` is a Paretian, pairwise independent social welfare functional on `𝓡^I`
(finitely many agents, at least three alternatives) that also respects unanimous weak
preference, then `F` is dictatorial. The proof is Proposition 22.D.1 applied to `F'`, Exercise
22.D.3, the extended Proposition 22.D.3 and the dictator transfer. -/
theorem exercise_22_D_5 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {F : Profile ι X → X → X → Prop} (hF : IsSWF (RationalProfiles ι X) F)
    (hP : Paretian (RationalProfiles ι X) F) (hI : PairwiseIndependent (RationalProfiles ι X) F)
    (hW : ∀ p ∈ RationalProfiles ι X, ∀ x y, (∀ i, p i x y) → F p x y) :
    Dictatorial (RationalProfiles ι X) F := by
  have hP' : UParetian (inducedFunctional F) :=
    fun ũ x y => ⟨fun h => hW _ (induced_mem ũ) x y h, exercise_22_D_5_strict hP ũ x y⟩
  have hI' := exercise_22_D_5_pairwise hI
  obtain ⟨R, hR, hgen⟩ := proposition_22_D_1 hX (exercise_22_D_5_isUSWF hF) hP' hI'
  obtain ⟨hO, hU⟩ := (noInterpersonalComparisons_iff _).1 (exercise_22_D_5_noInterpersonal F)
  obtain ⟨a, b, -, hab, -⟩ := hX
  obtain ⟨h, hh⟩ := proposition_22_D_3_relation ⟨a, b, hab⟩ hP' hR hgen hO hU
  exact ⟨h, exercise_22_D_5_dictator hI hh⟩

/-! ### Non-vacuity of Propositions 22.D.1-22.D.3 -/

/-- The purely utilitarian social welfare function is continuous and increasing. -/
theorem sum_isIncreasingSWF [Fintype ι] [Nonempty ι] :
    IsIncreasingSWF (fun u : ι → ℝ => ∑ i, u i) :=
  ⟨fun _ _ h => Finset.sum_le_sum fun i _ => h i,
    fun _ _ h => Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h i⟩

/-- **Proposition 22.D.1**, non-vacuity (MWG, p. 833). The utilitarian functional on three
alternatives satisfies all hypotheses. -/
theorem proposition_22_D_1_instance :
    IsUSWF (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) ∧
      UParetian (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) ∧
      UPairwiseIndependent (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) := by
  refine ⟨swfFunctional_isUSWF _, fun ũ x y => ⟨fun h => ?_, fun h => ?_⟩,
    generatedBy_pairwiseIndependent (swfFunctional_generatedBy _)⟩
  · exact sum_isIncreasingSWF.1 _ _ h
  · exact ⟨(sum_isIncreasingSWF.2 _ _ h).le, not_le.2 (sum_isIncreasingSWF.2 _ _ h)⟩

/-- **Propositions 22.D.2-22.D.3**, non-vacuity (MWG, pp. 835-837). The utilitarian functional
is generated by a continuous increasing social welfare function and is invariant to independent
(hence also common) changes of origins. -/
theorem proposition_22_D_3_instance :
    Continuous (fun u : Fin 2 → ℝ => ∑ i, u i) ∧
      IsIncreasingSWF (fun u : Fin 2 → ℝ => ∑ i, u i) ∧
      InvIndepOrigins (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) ∧
      InvCommonOrigins (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) := by
  have hO : InvIndepOrigins (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => ∑ i, u i)) := by
    intro α ũ
    refine invariance_of_relation (swfFunctional_generatedBy _) (fun v i => v i + α i)
      (fun u u' => ?_) ũ
    simp only [Finset.sum_add_distrib, add_le_add_iff_right]
  refine ⟨continuous_finsetSum _ fun i _ => continuous_apply i, sum_isIncreasingSWF, hO,
    fun α ũ => hO (fun _ => α) ũ⟩

/-- **Proposition 22.D.3**, non-vacuity of the dictatorship part (MWG, p. 837). The functional
generated by `W(u) = u₀` is generated by a continuous increasing social welfare function and
allows no interpersonal comparisons. -/
theorem proposition_22_D_3_dictatorial_instance :
    IsIncreasingSWF (fun u : Fin 2 → ℝ => u 0) ∧
      NoInterpersonalComparisons (swfFunctional (X := Fin 3) (fun u : Fin 2 → ℝ => u 0)) := by
  refine ⟨⟨fun _ _ h => h 0, fun _ _ h => h 0⟩, fun β α hβ ũ => ?_⟩
  refine invariance_of_relation (swfFunctional_generatedBy _) (fun v i => β i * v i + α i)
    (fun u u' => ?_) ũ
  simp only [add_le_add_iff_right]
  exact mul_le_mul_iff_of_pos_left (hβ 0)

end MWG.WelfareBargaining
