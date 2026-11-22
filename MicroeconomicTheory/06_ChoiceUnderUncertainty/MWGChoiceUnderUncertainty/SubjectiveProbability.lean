/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.StateDependent

/-!
# Subjective probability theory

MWG, Section 6.F, pp. 204-206, and Exercises 6.F.1-6.F.2, pp. 214-215: state preferences,
Definition 6.F.1 (state uniformity), the affine relation `u_s = π_s u + β_s`, Proposition 6.F.1
(the subjective expected utility theorem, in the Anscombe-Aumann setting with state-contingent
lotteries), its uniqueness part (Exercise 6.F.1), the Ellsberg variation (Example 6.F.1) and the
Gilboa-Schmeidler multiple-priors explanation (Exercise 6.F.2).

Correction: the probabilities are unique only when the utility on money is nonconstant (not all
lotteries indifferent); otherwise every probability vector represents the preference
(`exercise_6_F_1_probabilities_not_unique`).
-/

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- **p. 206**. The state-`s` preference on money lotteries derived from the state utility
`u_s`: `F ≿_s F'` iff `∫ u_s dF ≥ ∫ u_s dF'`. -/
def statePref (U : S → X → ℝ) (s : S) (F F' : SimpleLottery X) : Prop :=
  ExpectedUtility (U s) F' ≤ ExpectedUtility (U s) F

/-- **Definition 6.F.1** (MWG, p. 206). The state preferences are state uniform if
`≿_s = ≿_{s'}` for all `s, s'`. -/
def StateUniform (U : S → X → ℝ) : Prop := ∀ s s', statePref U s = statePref U s'

omit [Fintype S] in
/-- **p. 206**. With state uniformity, `u_s = α_s u + β_s` with `α_s > 0` for a common `u`
(here `u = u_{s₀}`). -/
theorem stateUniform_affine {U : S → X → ℝ} (h : StateUniform U) (s₀ s : S) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, U s x = A * U s₀ x + B := by
  have h0 : Represents (ExpectedUtility (U s₀)) (statePref U s₀) := fun _ _ => Iff.rfl
  have h1 : Represents (ExpectedUtility (U s)) (statePref U s₀) := by
    rw [h s₀ s]; exact fun _ _ => Iff.rfl
  exact proposition_5_3_unique h0 h1

/-- **Proposition 6.F.1** (MWG, p. 206), the subjective expected utility theorem: if the
preference on state-contingent lotteries is rational, continuous, satisfies the extended
independence axiom, and the derived state preferences are state uniform, there are
probabilities `π_s > 0` summing to one and a utility `u` with
`L ≿ L'` iff `∑ π_s ∫ u dF_s ≥ ∑ π_s ∫ u dF'_s`. -/
theorem proposition_6_F_1 [Nonempty S] {r : HorseLottery S X → HorseLottery S X → Prop}
    (hr : Rational r) (hc : MixContinuous r) (hi : ExtendedIndependence r)
    (huni : ∀ U : S → X → ℝ, Represents (HorseValue U) r → StateUniform U) :
    ∃ (π : S → ℝ) (u : X → ℝ), (∀ s, 0 < π s) ∧ ∑ s, π s = 1 ∧
      Represents (SubjectiveHorseValue π u) r := by
  classical
  obtain ⟨U, hU⟩ := proposition_6_E_1 hr hc hi
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hu := huni U hU
  choose A hA B hB using stateUniform_affine hu s₀
  set T := ∑ s, A s
  have hT : 0 < T := Finset.sum_pos (fun s _ => hA s) Finset.univ_nonempty
  refine ⟨fun s => A s / T, U s₀, fun s => div_pos (hA s) hT, ?_, fun L L' => ?_⟩
  · rw [← Finset.sum_div, div_self hT.ne']
  · have hval (M : HorseLottery S X) : HorseValue U M =
        T * SubjectiveHorseValue (fun s => A s / T) (U s₀) M + ∑ s, B s := by
      simp only [HorseValue, StateAdditiveValue, SubjectiveHorseValue, SubjectiveActValue]
      have he (s : S) : ExpectedUtility (U s) (M s) =
          A s * ExpectedUtility (U s₀) (M s) + B s := by
        rw [show U s = fun x => A s * U s₀ x + B s from funext (hB s),
          expectedUtility_affine_transform]
      simp only [he, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by field_simp
    rw [hU, hval, hval]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

/-- **Proposition 6.F.1** (MWG, p. 206) for sure money payoffs `(x₁, …, x_S)`:
`x ≿ x'` iff `∑ π_s u(x_s) ≥ ∑ π_s u(x'_s)`. -/
theorem proposition_6_F_1_sure [Nonempty S] {r : HorseLottery S X → HorseLottery S X → Prop}
    (hr : Rational r) (hc : MixContinuous r) (hi : ExtendedIndependence r)
    (huni : ∀ U : S → X → ℝ, Represents (HorseValue U) r → StateUniform U) :
    ∃ (π : S → ℝ) (u : X → ℝ), (∀ s, 0 < π s) ∧ ∑ s, π s = 1 ∧ ∀ x x' : S → X,
      r (fun s => PureLottery (x s)) (fun s => PureLottery (x' s)) ↔
        ∑ s, π s * u (x' s) ≤ ∑ s, π s * u (x s) := by
  obtain ⟨π, u, hπ, h1, hrep⟩ := proposition_6_F_1 hr hc hi huni
  refine ⟨π, u, hπ, h1, fun x x' => ?_⟩
  rw [hrep]
  simp only [SubjectiveHorseValue, SubjectiveActValue, expectedUtility_pure]

/-- **Exercise 6.F.1** (MWG, p. 214), utility. In the subjective expected utility theorem the
utility on money is unique up to origin and scale. -/
theorem exercise_6_F_1_utility {π π' : S → ℝ} (hπ : ∑ s, π s = 1) (hπ' : ∑ s, π' s = 1)
    {u u' : X → ℝ} {r : HorseLottery S X → HorseLottery S X → Prop}
    (h : Represents (SubjectiveHorseValue π u) r) (h' : Represents (SubjectiveHorseValue π' u') r) :
    ∃ β > 0, ∃ γ : ℝ, ∀ x, u' x = β * u x + γ :=
  subjective_prize_utility_unique π π' hπ hπ' u u' h h'

/-- **Exercise 6.F.1** (MWG, p. 214), probabilities. When the utility on money is nonconstant,
the subjective probabilities are uniquely determined. -/
theorem exercise_6_F_1_probabilities {π π' : S → ℝ} (hπ : ∑ s, π s = 1)
    (hπ' : ∑ s, π' s = 1) {u u' : X → ℝ} {r : HorseLottery S X → HorseLottery S X → Prop}
    (h : Represents (SubjectiveHorseValue π u) r) (h' : Represents (SubjectiveHorseValue π' u') r)
    {x y : X} (hne : u x ≠ u y) : π' = π :=
  subjective_probabilities_unique π π' hπ hπ' u u' h h' hne

/-- **Exercise 6.F.1**: correction. Without a nonconstant utility the probabilities are not
unique: for the total-indifference preference, `u = 0` with `π = (1/2, 1/2)` and with
`π = (1/3, 2/3)` both represent it. -/
theorem exercise_6_F_1_probabilities_not_unique :
    let r : HorseLottery (Fin 2) Bool → HorseLottery (Fin 2) Bool → Prop := fun _ _ => True
    Represents (SubjectiveHorseValue ![1 / 2, 1 / 2] (fun _ => 0)) r ∧
      Represents (SubjectiveHorseValue ![1 / 3, 2 / 3] (fun _ => 0)) r ∧
      (![1 / 2, 1 / 2] : Fin 2 → ℝ) ≠ ![1 / 3, 2 / 3] := by
  intro r
  have h0 (p : Fin 2 → ℝ) (M : HorseLottery (Fin 2) Bool) :
      SubjectiveHorseValue p (fun _ => (0 : ℝ)) M = 0 := by
    simp [SubjectiveHorseValue, SubjectiveActValue, ExpectedUtility]
  refine ⟨fun L L' => ?_, fun L L' => ?_, fun h => ?_⟩
  · simp [r, h0]
  · simp [r, h0]
  · have := congrFun h 0
    norm_num at this

/-- **Example 6.F.1** (MWG, p. 206), a variation of the Ellsberg paradox. Urn `R` has `49` white
and `51` black balls; urn `H` an unknown mixture. With any subjective probability `q` that the
`H`-ball is white, strictly preferring the `R`-ball when black wins (`0.51 > 1 - q`) forces
strictly preferring the `H`-ball when white wins (`q > 0.49`): choosing `R` in both situations
is inconsistent with subjective expected utility. -/
theorem example_6_F_1 (q : ℝ) :
    (51 / 100 : ℝ) > 1 - q → q > 49 / 100 := by intro h; linarith

/-- **Exercise 6.F.2** (MWG, pp. 214-215). Gilboa-Schmeidler utilities with a set of beliefs `P`
on the `H`-ball being white, `u(0) = 0`, `u(1000) = 1`. -/
noncomputable def gsUtilityW (P : Set ℝ) : ℝ := sInf P

/-- The worst-case probability of black. -/
noncomputable def gsUtilityB (P : Set ℝ) : ℝ := sInf ((fun q => 1 - q) '' P)

/-- **Exercise 6.F.2(a)** (MWG, p. 215). With a single belief `P = {q}`, the utilities are
expected utilities (`U_W(H) = q`, `U_B(H) = 1 - q`), and `U_W(R) > U_W(H)` iff
`U_B(R) < U_B(H)`. -/
theorem exercise_6_F_2a (q : ℝ) :
    gsUtilityW {q} = q ∧ gsUtilityB {q} = 1 - q ∧
      ((49 / 100 : ℝ) > gsUtilityW {q} ↔ (51 / 100 : ℝ) < gsUtilityB {q}) := by
  have h1 : gsUtilityW {q} = q := csInf_singleton q
  have h2 : gsUtilityB {q} = 1 - q := by
    simp [gsUtilityB, Set.image_singleton, csInf_singleton]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  constructor <;> intro h <;> linarith

/-- **Exercise 6.F.2(b)** (MWG, p. 215). With `P = [0.4, 0.6]` the decision maker strictly
prefers the `R`-ball in both choice situations: `U_W(R) = 0.49 > 0.4 = U_W(H)` and
`U_B(R) = 0.51 > 0.4 = U_B(H)`. -/
theorem exercise_6_F_2b :
    gsUtilityW (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 ∧ gsUtilityB (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 ∧
      (49 / 100 : ℝ) > gsUtilityW (Set.Icc (2 / 5) (3 / 5)) ∧
      (51 / 100 : ℝ) > gsUtilityB (Set.Icc (2 / 5) (3 / 5)) := by
  have h1 : gsUtilityW (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 := csInf_Icc (by norm_num)
  have himg : (fun q : ℝ => 1 - q) '' Set.Icc (2 / 5) (3 / 5) = Set.Icc (2 / 5) (3 / 5) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
    · intro hy; exact ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by ring⟩
  have h2 : gsUtilityB (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 := by
    rw [gsUtilityB, himg]; exact csInf_Icc (by norm_num)
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num

end MWG.ChoiceUnderUncertainty
