/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Uniform

/-!
# Exercise 13.C.1: a costless test with a continuum of types

MWG, Exercise 13.C.1, p. 474. Nature draws the worker's type from a continuous distribution on
`[θ̲, θ̄]`; the worker chooses whether to take a costless test that reveals her type; two
firms then bid for her (`r = 0`, as in Section 13.C).

As in Section 13.C (`bertrand_wage`) the competing firms pay the expected productivity under
their beliefs, so an equilibrium is described in reduced form (`IsTestEq`, the pattern of
`IsPBEC4`) by the test strategy `τ(θ)` and the wage `w_N` offered to a worker who did not take
the test: a tested worker is paid her type `θ`; `w_N ∈ [θ̲, θ̄]` (the mean of some belief); each
type's choice is optimal; and if the non-testers have positive probability, `w_N` is their
conditional mean.

* `exercise_13_C_1`: in every equilibrium `w_N = θ̲` (so firms offer no more than `θ̲` to a
  worker not taking the test) and every type `θ > θ̲` takes the test (strictly prefers to).
* `exercise_13_C_1_instance`: with types uniform on `[1, 2]`, both "everybody tests" and
  "everybody but `θ̲` tests" are equilibria: `θ̲` is indifferent, so "all worker types submit"
  holds for all types but `θ̲`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.C.1** (MWG, p. 474). The types in `[θ̲, θ̄]` that do not take the test. -/
def testNonTakers (θl θh : ℝ) (τ : ℝ → Bool) : Set ℝ := {θ | θ ∈ Set.Icc θl θh ∧ τ θ = false}

/-- **Exercise 13.C.1** (MWG, p. 474). The reduced form of an SPNE of the testing game: the test
strategy `τ` (`true` = take the test) and the wage `w_N` paid after no test. -/
def IsTestEq (μ : Measure ℝ) (θl θh : ℝ) (τ : ℝ → Bool) (wN : ℝ) : Prop :=
  (θl ≤ wN ∧ wN ≤ θh) ∧ (∀ θ ∈ Set.Icc θl θh, τ θ = true → wN ≤ θ) ∧
    (∀ θ ∈ Set.Icc θl θh, τ θ = false → θ ≤ wN) ∧
    (0 < μ (testNonTakers θl θh τ) → wN = condMean μ θl θh (testNonTakers θl θh τ))

/-- **Exercise 13.C.1** (MWG, p. 474). In any equilibrium of the testing game firms pay `θ̲` to a
worker who does not take the test, and every type above `θ̲` takes it. -/
theorem exercise_13_C_1 {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (hden : HasPosDensity μ θl θh) {τ : ℝ → Bool} {wN : ℝ} (h : IsTestEq μ θl θh τ wN) :
    wN = θl ∧ ∀ θ, θl < θ → θ ≤ θh → τ θ = true ∧ wN < θ := by
  have := hd.prob
  obtain ⟨⟨hw1, hw2⟩, htest, hno, hbayes⟩ := h
  set A := testNonTakers θl θh τ with hAdef
  have hsub : Set.Ico θl wN ⊆ A := fun θ hθ => by
    refine ⟨⟨hθ.1, hθ.2.le.trans hw2⟩, ?_⟩
    cases hτ : τ θ
    · rfl
    · exact absurd (htest θ ⟨hθ.1, hθ.2.le.trans hw2⟩ hτ) (not_le.2 hθ.2)
  have hAeq : A = Set.Ico θl wN ∪ (A ∩ {wN}) := by
    ext θ
    constructor
    · intro hθ
      rcases eq_or_lt_of_le (hno θ hθ.1 hθ.2) with he | hlt
      · exact Or.inr ⟨hθ, he⟩
      · exact Or.inl ⟨hθ.1.1, hlt⟩
    · rintro (hθ | hθ)
      · exact hsub hθ
      · exact hθ.1
  have hAm : MeasurableSet A := by
    rw [hAeq]
    exact measurableSet_Ico.union
      (Set.subsingleton_singleton.anti Set.inter_subset_right).measurableSet
  have hA0 : μ A = 0 := by
    by_contra hne
    have hpos : 0 < μ A := pos_iff_ne_zero.2 hne
    have hw := hbayes hpos
    have hae : ∀ᵐ θ ∂μ, θ ≠ wN := by
      rw [ae_iff]; simpa using hden.noAtom wN
    have hlt : 0 < ∫ θ in A, (wN - θ) ∂μ :=
      setIntegral_pos_of_ae_pos hAm hpos
        (hae.mono fun θ hθ hθA => sub_pos.2 (lt_of_le_of_ne (hno θ hθA.1 hθA.2) hθ))
        ((integrable_const wN).sub hd.integrable_id).integrableOn
    rw [integral_sub (integrable_const wN).integrableOn hd.integrable_id.integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    have ha : 0 < (μ A).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    simp only [condMean, hpos, ↓reduceIte] at hw
    rw [eq_div_iff ha.ne'] at hw
    nlinarith
  have hwl : wN ≤ θl := by
    by_contra hlt
    rw [not_le] at hlt
    have hp := hden.pos θl ((θl + wN) / 2) le_rfl (by linarith) (by linarith)
    have h0 : μ (Set.Icc θl ((θl + wN) / 2)) = 0 :=
      measure_mono_null (fun θ hθ => hsub ⟨hθ.1, by linarith [hθ.2]⟩) hA0
    rw [h0] at hp
    exact lt_irrefl _ hp
  have heq : wN = θl := le_antisymm hwl hw1
  refine ⟨heq, fun θ h1 h2 => ⟨?_, by linarith⟩⟩
  cases hτ : τ θ
  · have := hno θ ⟨h1.le, h2⟩ hτ
    linarith
  · rfl

/-- **Exercise 13.C.1**, instance (MWG, p. 474). With types uniform on `[1, 2]` and `w_N = 1`,
"every type takes the test" and "every type but `θ̲ = 1` takes the test" are both equilibria. -/
theorem exercise_13_C_1_instance :
    IsTestEq (unifMeas 1 2) 1 2 (fun _ => true) 1 ∧
      IsTestEq (unifMeas 1 2) 1 2 (fun θ => decide (1 < θ)) 1 := by
  refine ⟨⟨⟨le_rfl, by norm_num⟩, fun θ hθ _ => hθ.1, fun θ _ h => absurd h (by simp),
    fun h => ?_⟩, ⟨⟨le_rfl, by norm_num⟩, fun θ hθ _ => hθ.1, fun θ _ h => ?_, fun h => ?_⟩⟩
  · have : testNonTakers 1 2 (fun _ => true) = ∅ := by
      ext θ; simp [testNonTakers]
    rw [this, measure_empty] at h
    exact absurd h (lt_irrefl _)
  · simpa using h
  · have hsub : testNonTakers 1 2 (fun θ => decide (1 < θ)) ⊆ {1} := by
      intro θ hθ
      simp only [testNonTakers, Set.mem_ofPred_eq, decide_eq_false_iff_not, not_lt] at hθ
      exact le_antisymm hθ.2 hθ.1.1
    have h0 := measure_mono_null hsub ((unifMeas_density one_lt_two).noAtom 1)
    rw [h0] at h
    exact absurd h (lt_irrefl _)

end MWG.AdverseSelection
