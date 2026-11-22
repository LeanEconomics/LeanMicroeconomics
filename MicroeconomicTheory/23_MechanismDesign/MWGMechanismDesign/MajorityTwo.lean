/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.DSExercises
import MWGMechanismDesign.GibbardSatterthwaite

/-!
# Majority voting with two alternatives

MWG, Section 23.C, p. 875: "the conclusion of Proposition 23.C.3 does not follow if `X` contains
two elements. For example, in this case, a majority voting social choice function (see Section
21.E) is both nondictatorial and truthfully implementable in dominant strategies (Exercise
23.C.2)."

Types are rich: every agent can strictly prefer either alternative (`MtRich`).

* `majority_nondictatorial`: with at least three agents every majority voting social choice
  function on `X = Bool` is nondictatorial.
* `majority_tieTrue_nondictatorial`, `majority_tieTrue_strategyProof`: with at least two agents
  the majority rule with ties going to `x₁ = true` is nondictatorial and strategy-proof
  (by `exercise_23_C_2`); `remark_23_C_majority` collects the claim of p. 875.
* **Correction of scope** (`majority_two_agents_dictatorial`): with exactly two agents a majority
  voting function may be dictatorial: breaking ties by agent `0`'s preference makes agent `0` a
  dictator. So "a majority voting social choice function is nondictatorial" needs `I ≥ 3`, or,
  with `I = 2`, a tie rule that does not follow one agent.
-/

namespace MWG.MechanismDesign

open Function

variable {ι : Type*} {Θ : ι → Type*}

/-- Every agent has types strictly preferring each alternative of `X = Bool` (as when `𝓡ᵢ`
contains all strict preferences). -/
def MtRich (u : (i : ι) → Bool → Θ i → ℝ) : Prop :=
  ∀ i x, ∃ a : Θ i, u i (!x) a < u i x a

/-- At a profile where agent `h` strictly prefers `false` and everybody else strictly prefers
`true`, `#{i : true ≻ᵢ false} = I - 1` and `#{i : false ≻ᵢ true} = 1`. -/
theorem mt_counts [Fintype ι] (u : (i : ι) → Bool → Θ i → ℝ)
    (θ : (i : ι) → Θ i) (h : ι) (hh : u h true (θ h) < u h false (θ h))
    (ho : ∀ j ≠ h, u j false (θ j) < u j true (θ j)) :
    numPref u θ true = Fintype.card ι - 1 ∧ numPref u θ false = 1 := by
  classical
  constructor
  · have e : (Finset.univ.filter fun i => u i (!true) (θ i) < u i true (θ i)) =
        Finset.univ.erase h := by
      ext i
      simp only [Bool.not_true, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, ne_eq, and_true]
      constructor
      · rintro hi rfl; exact lt_asymm hi hh
      · exact ho i
    unfold numPref
    convert congrArg Finset.card e using 2
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ]
  · have e : (Finset.univ.filter fun i => u i (!false) (θ i) < u i false (θ i)) = {h} := by
      ext i
      simp only [Bool.not_false, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hi
        by_contra hne
        exact lt_asymm hi (ho i hne)
      · rintro rfl; exact hh
    unfold numPref
    convert congrArg Finset.card e using 2
    rw [Finset.card_singleton]

/-- With rich types, for every agent `h` there is a profile where `h` strictly prefers `false`
and everybody else strictly prefers `true`. -/
theorem mt_profile {u : (i : ι) → Bool → Θ i → ℝ} (hr : MtRich u) (h : ι) :
    ∃ θ : (i : ι) → Θ i, u h true (θ h) < u h false (θ h) ∧
      ∀ j ≠ h, u j false (θ j) < u j true (θ j) := by
  classical
  choose a ha using hr
  refine ⟨update (fun j => a j true) h (a h false), ?_, fun j hj => ?_⟩
  · rw [update_self]; simpa using ha h false
  · rw [update_of_ne hj]; simpa using ha j true

/-- **Section 23.C** (MWG, p. 875). With at least three agents and rich types, every majority
voting social choice function on two alternatives is nondictatorial. -/
theorem majority_nondictatorial [Fintype ι] {u : (i : ι) → Bool → Θ i → ℝ}
    (hr : MtRich u) (hI : 3 ≤ Fintype.card ι) {f : ((i : ι) → Θ i) → Bool}
    (hM : IsMajorityVoting u f) : ¬Dictatorial u f := by
  rintro ⟨h, hd⟩
  obtain ⟨θ, hh, ho⟩ := mt_profile hr h
  obtain ⟨c1, c0⟩ := mt_counts u θ h hh ho
  have hf : f θ = true := hM θ true (by simp only [Bool.not_true, c0, c1]; omega)
  have := hd θ false
  rw [hf] at this
  linarith

/-- The majority rule with ties going to `x₁ = true`. -/
noncomputable def majorityTieTrue [Fintype ι] (u : (i : ι) → Bool → Θ i → ℝ) :
    ((i : ι) → Θ i) → Bool :=
  fun θ => decide (numPref u θ false ≤ numPref u θ true)

/-- **Section 23.C** (MWG, p. 875). With at least two agents and rich types, majority voting
with ties going to `x₁` is nondictatorial. -/
theorem majority_tieTrue_nondictatorial [Fintype ι]
    {u : (i : ι) → Bool → Θ i → ℝ} (hr : MtRich u) (hI : 2 ≤ Fintype.card ι) :
    ¬Dictatorial u (majorityTieTrue u) := by
  rintro ⟨h, hd⟩
  obtain ⟨θ, hh, ho⟩ := mt_profile hr h
  obtain ⟨c1, c0⟩ := mt_counts u θ h hh ho
  have hf : majorityTieTrue u θ = true := by
    simp only [majorityTieTrue, c0, c1, decide_eq_true_eq]; omega
  have := hd θ false
  rw [hf] at this
  linarith

/-- **Section 23.C** (MWG, p. 875) and Exercise 23.C.2: majority voting with ties going to `x₁`
is strategy-proof (truthfully implementable in dominant strategies), for any number of agents. -/
theorem majority_tieTrue_strategyProof [Fintype ι] [DecidableEq ι]
    (u : (i : ι) → Bool → Θ i → ℝ) : StrategyProof u (majorityTieTrue u) :=
  exercise_23_C_2 (exercise_23_C_2_instance u).1 (exercise_23_C_2_instance u).2

/-- **Section 23.C** (MWG, p. 875), the remark after Proposition 23.C.3: with two alternatives
the Gibbard-Satterthwaite conclusion fails. For at least two agents with rich types, majority
voting (ties to `x₁`) is onto, nondictatorial and truthfully implementable in dominant
strategies. -/
theorem remark_23_C_majority [Fintype ι] [DecidableEq ι] {u : (i : ι) → Bool → Θ i → ℝ}
    (hr : MtRich u) (hI : 2 ≤ Fintype.card ι) :
    Function.Surjective (majorityTieTrue u) ∧ ¬Dictatorial u (majorityTieTrue u) ∧
      StrategyProof u (majorityTieTrue u) := by
  classical
  refine ⟨fun x => ?_, majority_tieTrue_nondictatorial hr hI,
    majority_tieTrue_strategyProof u⟩
  choose a ha using hr
  refine ⟨fun j => a j x, ?_⟩
  have hall : ∀ j, u j (!x) (a j x) < u j x (a j x) := fun j => ha j x
  have hc : numPref u (fun j => a j x) (!x) = 0 ∧
      numPref u (fun j => a j x) x = Fintype.card ι := by
    unfold numPref
    constructor
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      simp only [Bool.not_not]
      exact (hall j).le.not_gt
    · rw [Finset.filter_true_of_mem fun j _ => hall j, Finset.card_univ]
  have hpos : 0 < Fintype.card ι := by omega
  cases x
  · simp only [Bool.not_false] at hc
    simp only [majorityTieTrue, hc.1, hc.2, decide_eq_false_iff_not, not_le]
    exact hpos
  · simp only [Bool.not_true] at hc
    simp only [majorityTieTrue, hc.1, hc.2, decide_eq_true_eq]
    exact Nat.zero_le _

/-- Two agents with `uᵢ(x₁, θᵢ) = θᵢ`, `uᵢ(x₂, θᵢ) = 0` (`x₁ = true`): majority voting with ties
broken by agent `0`'s preference (and by agent `1`'s when agent `0` is indifferent). -/
noncomputable def majorityTieZero (θ : Fin 2 → ℝ) : Bool :=
  if θ 0 = 0 then (if 0 < θ 1 then true else false) else (if 0 < θ 0 then true else false)

/-- **Section 23.C** (MWG, p. 875), correction of scope: with two agents a majority voting social
choice function can be dictatorial. `majorityTieZero` (ties broken by agent `0`) is a majority
voting function, on rich types, and agent `0` is a dictator. -/
theorem majority_two_agents_dictatorial :
    MtRich (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0) ∧
      IsMajorityVoting (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0)
        majorityTieZero ∧
      Dictatorial (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0)
        majorityTieZero := by
  classical
  have hcount : ∀ (θ : Fin 2 → ℝ) (x : Bool),
      numPref (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0) θ x =
        (if (if !x then θ 0 else 0) < (if x then θ 0 else 0) then 1 else 0) +
          (if (if !x then θ 1 else 0) < (if x then θ 1 else 0) then 1 else 0) := by
    intro θ x
    unfold numPref
    rw [Finset.card_filter, Fin.sum_univ_two]
  refine ⟨fun i x => ?_, fun θ x h => ?_, ⟨0, fun θ y => ?_⟩⟩
  · cases x
    · exact ⟨-1, by norm_num⟩
    · exact ⟨1, by norm_num⟩
  · rw [hcount, hcount] at h
    simp only [majorityTieZero]
    cases x <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h <;>
      split_ifs at h ⊢ <;>
      first
        | rfl
        | contradiction
        | (exfalso; linarith)
        | (exfalso; rcases lt_or_gt_of_ne ‹¬θ 0 = 0› with h' | h' <;> linarith)
  · simp only [majorityTieZero]
    cases y <;> split_ifs <;>
      first
        | exact le_rfl
        | contradiction
        | linarith

end MWG.MechanismDesign
