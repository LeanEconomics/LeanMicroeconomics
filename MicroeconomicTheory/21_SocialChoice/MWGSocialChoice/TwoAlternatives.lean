/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Basic.Sign.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Social preferences over two alternatives and May's theorem

MWG, Section 21.B, pp. 790-792, and Exercises 21.B.1-21.B.3, p. 812.

With two alternatives `x` and `y`, a profile is a vector `α : ι → ℤ` with entries in
`{-1, 0, 1}` (agent `i` prefers `x`, is indifferent, prefers `y`), and a social welfare
functional is a map `F : (ι → ℤ) → ℤ` with values in `{-1, 0, 1}` on such profiles
(Definition 21.B.1). We prove the Pareto property of the weighted rules `sign ∑ βᵢ αᵢ`
(Example 21.B.1), the dictatorship remarks of Example 21.B.2, and May's theorem (Proposition
21.B.1): `F` is majority voting iff it is symmetric among agents, neutral between alternatives
and positively responsive. Our proof of sufficiency follows the book; instead of the book's
"without loss of generality" reordering of agents (which itself appeals to symmetry) it lowers
the excess `x`-supporters to indifference directly. May's characterization is proved for
every `F : (ι → ℤ) → ℤ`: the range condition of Definition 21.B.1 is not needed.

Exercise 21.B.2 gives, for each of the three properties, a rule satisfying the other two and
differing from majority voting. Exercise 21.B.3 shows that majority voting over a public
project is Pareto optimal among the two levels without transfers, characterizes Pareto
optimality with transfers by the sign of `∑ vᵢ` (the "mean"), and gives a majority decision
that transfers Pareto-dominate.

The Part Five introduction (MWG, p. 787) contains no precise mathematical claim.
-/

namespace MWG.SocialChoice

open Finset

variable {ι : Type*} [Fintype ι]

/-- The profiles over two alternatives: vectors with entries in `{-1, 0, 1}` (MWG, p. 790). -/
def TwoAltProfiles (ι : Type*) : Set (ι → ℤ) := {α | ∀ i, α i = -1 ∨ α i = 0 ∨ α i = 1}

/-- **Definition 21.B.1** (MWG, p. 790). A social welfare functional for two alternatives
assigns a social preference in `{-1, 0, 1}` to every profile. -/
def IsTwoAltSWF (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, F α = -1 ∨ F α = 0 ∨ F α = 1

/-- **Definition 21.B.2** (MWG, p. 790). `F` is Paretian: `F(1, …, 1) = 1` and
`F(-1, …, -1) = -1`. -/
def TwoAltParetian (F : (ι → ℤ) → ℤ) : Prop := F (fun _ => 1) = 1 ∧ F (fun _ => -1) = -1

/-- **Example 21.B.1** (MWG, p. 791). The weighted rule `F(α) = sign ∑ βᵢ αᵢ`. -/
noncomputable def weightedVoting (β : ι → ℝ) (α : ι → ℤ) : ℤ :=
  ((SignType.sign (∑ i, β i * (α i : ℝ)) : SignType) : ℤ)

/-- **Example 21.B.1** (MWG, p. 791). Majority voting: `F(α) = sign ∑ αᵢ`. -/
def majorityVoting (α : ι → ℤ) : ℤ := Int.sign (∑ i, α i)

/-- The sign of a real number, cast to `ℤ`, lies in `{-1, 0, 1}`. -/
theorem signType_cast_cases (a : ℝ) :
    ((SignType.sign a : SignType) : ℤ) = -1 ∨ ((SignType.sign a : SignType) : ℤ) = 0 ∨
      ((SignType.sign a : SignType) : ℤ) = 1 := by
  rcases lt_trichotomy a 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- **Example 21.B.1** (MWG, p. 791). Every weighted rule is a social welfare functional. -/
theorem weightedVoting_isSWF (β : ι → ℝ) : IsTwoAltSWF (weightedVoting β) :=
  fun _ _ => signType_cast_cases _

/-- **Example 21.B.1** (MWG, pp. 790-791). With nonnegative weights, not all zero, the
weighted rule is Paretian. -/
theorem example_21_B_1 (β : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) (hne : ∃ i, β i ≠ 0) :
    TwoAltParetian (weightedVoting β) := by
  obtain ⟨j, hj⟩ := hne
  have hpos : 0 < ∑ i, β i := by
    have hj' : 0 < β j := lt_of_le_of_ne (hβ j) (Ne.symm hj)
    calc (0 : ℝ) < β j := hj'
      _ ≤ ∑ i, β i := single_le_sum (fun i _ => hβ i) (mem_univ j)
  constructor
  · simp [weightedVoting, sign_pos hpos]
  · have hneg : ∑ i, β i * ((-1 : ℤ) : ℝ) < 0 := by
      simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, sum_neg_distrib]
      linarith
    simp only [weightedVoting, sign_neg hneg]
    rfl

/-- Majority voting is the weighted rule with all weights equal to one (MWG, p. 791). -/
theorem majorityVoting_eq_weighted (α : ι → ℤ) :
    majorityVoting α = weightedVoting (fun _ => 1) α := by
  unfold majorityVoting weightedVoting
  have hs : ∑ i, (1 : ℝ) * (α i : ℝ) = ((∑ i, α i : ℤ) : ℝ) := by simp
  rw [hs]
  rcases lt_trichotomy (∑ i, α i) 0 with h | h | h
  · have h' : ((∑ i, α i : ℤ) : ℝ) < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h, sign_neg h']
    rfl
  · rw [h]
    simp
  · have h' : (0 : ℝ) < ((∑ i, α i : ℤ) : ℝ) := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h, sign_pos h']
    rfl

/-- The integer sign lies in `{-1, 0, 1}`. -/
theorem int_sign_cases (n : ℤ) : n.sign = -1 ∨ n.sign = 0 ∨ n.sign = 1 := by
  rcases lt_trichotomy n 0 with h | h | h
  · exact Or.inl (Int.sign_eq_neg_one_of_neg h)
  · exact Or.inr (Or.inl (by simp [h]))
  · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos h))

/-- Majority voting is a social welfare functional. -/
theorem majorityVoting_isSWF : IsTwoAltSWF (ι := ι) majorityVoting :=
  fun _ _ => int_sign_cases _

/-- Number of agents preferring `x` (`n⁺`, MWG, p. 792). -/
def nPlus (α : ι → ℤ) : ℕ := (univ.filter fun i => α i = 1).card

/-- Number of agents preferring `y` (`n⁻`, MWG, p. 792). -/
def nMinus (α : ι → ℤ) : ℕ := (univ.filter fun i => α i = -1).card

/-- For a profile, `∑ αᵢ = n⁺ - n⁻`. -/
theorem sum_eq_nPlus_sub_nMinus {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    ∑ i, α i = (nPlus α : ℤ) - nMinus α := by
  have h : ∀ i, α i = (if α i = 1 then 1 else 0) - (if α i = -1 then 1 else 0) := by
    intro i
    rcases hα i with h | h | h <;> simp [h]
  rw [sum_congr rfl fun i _ => h i, sum_sub_distrib, sum_boole, sum_boole]
  rfl

/-- **Example 21.B.1** (MWG, p. 791). Majority voting gives `1` iff more agents prefer `x`
than `y`, `-1` iff more prefer `y`, and `0` in case of equality. -/
theorem majorityVoting_spec {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    (majorityVoting α = 1 ↔ nMinus α < nPlus α) ∧
      (majorityVoting α = -1 ↔ nPlus α < nMinus α) ∧
      (majorityVoting α = 0 ↔ nPlus α = nMinus α) := by
  unfold majorityVoting
  rw [sum_eq_nPlus_sub_nMinus hα]
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.sign_eq_one_iff_pos]
    omega
  · rw [Int.sign_eq_neg_one_iff_neg]
    omega
  · rw [Int.sign_eq_zero_iff_zero]
    omega

/-- **Example 21.B.2** (MWG, p. 791). Agent `h` is a dictator: `αₕ = 1` forces `F(α) = 1` and
`αₕ = -1` forces `F(α) = -1`. -/
def IsTwoAltDictator (F : (ι → ℤ) → ℤ) (h : ι) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, (α h = 1 → F α = 1) ∧ (α h = -1 → F α = -1)

omit [Fintype ι] in
/-- **Example 21.B.2** (MWG, p. 791). A dictatorial social welfare functional is Paretian. -/
theorem example_21_B_2_paretian {F : (ι → ℤ) → ℤ} {h : ι} (hF : IsTwoAltDictator F h) :
    TwoAltParetian F :=
  ⟨(hF _ (fun _ => Or.inr (Or.inr rfl))).1 rfl, (hF _ (fun _ => Or.inl rfl)).2 rfl⟩

/-- **Example 21.B.2** (MWG, p. 791). For the weighted rule with `βₕ > 0` and `βᵢ = 0` for
`i ≠ h`, `F(α) = αₕ`; in particular `h` is a dictator. -/
theorem example_21_B_2 (β : ι → ℝ) (h : ι) (hh : 0 < β h)
    (h0 : ∀ i, i ≠ h → β i = 0) :
    (∀ α ∈ TwoAltProfiles ι, weightedVoting β α = α h) ∧
      IsTwoAltDictator (weightedVoting β) h := by
  classical
  have key : ∀ α ∈ TwoAltProfiles ι, weightedVoting β α = α h := by
    intro α hα
    have hs : ∑ i, β i * (α i : ℝ) = β h * (α h : ℝ) :=
      sum_eq_single h (fun i _ hi => by rw [h0 i hi, zero_mul]) (fun hn => absurd (mem_univ h) hn)
    unfold weightedVoting
    rw [hs]
    rcases hα h with ha | ha | ha
    · have : β h * (α h : ℝ) < 0 := by rw [ha]; simp; linarith
      rw [sign_neg this, ha]
      rfl
    · simp [ha]
    · have : 0 < β h * (α h : ℝ) := by rw [ha]; simp; linarith
      rw [sign_pos this, ha]
      rfl
  exact ⟨key, fun α hα => ⟨fun h1 => (key α hα).trans h1, fun h1 => (key α hα).trans h1⟩⟩

/-- **Definition 21.B.3** (MWG, p. 791). `F` is symmetric among agents (anonymous): permuting
the agents' preferences by any onto map `π` does not change the social preference. -/
def SymmetricAmongAgents (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ π : ι → ι, Function.Surjective π → ∀ α ∈ TwoAltProfiles ι, F α = F (α ∘ π)

/-- **Definition 21.B.4** (MWG, p. 791). `F` is neutral between alternatives:
`F(α) = -F(-α)`. -/
def NeutralBetweenAlternatives (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, F α = -F (-α)

/-- **Definition 21.B.5** (MWG, p. 791). `F` is positively responsive: `α ≥ α'`, `α ≠ α'` and
`F(α') ≥ 0` imply `F(α) = 1`. -/
def PositivelyResponsive (F : (ι → ℤ) → ℤ) : Prop :=
  ∀ α ∈ TwoAltProfiles ι, ∀ α' ∈ TwoAltProfiles ι, (∀ i, α' i ≤ α i) → α ≠ α' →
    0 ≤ F α' → F α = 1

omit [Fintype ι] in
/-- Negating a profile gives a profile. -/
theorem neg_mem_twoAltProfiles {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι) :
    -α ∈ TwoAltProfiles ι := by
  intro i
  rcases hα i with h | h | h <;> simp [h]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is symmetric among agents. -/
theorem exercise_21_B_1_symmetric : SymmetricAmongAgents (ι := ι) majorityVoting := by
  intro π hπ α _
  have hinj : Function.Injective π := Finite.injective_iff_surjective.mpr hπ
  unfold majorityVoting
  congr 1
  exact (Equiv.sum_comp (Equiv.ofBijective π ⟨hinj, hπ⟩) α).symm

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is neutral between alternatives. -/
theorem exercise_21_B_1_neutral : NeutralBetweenAlternatives (ι := ι) majorityVoting := by
  intro α _
  simp [majorityVoting, sum_neg_distrib, Int.sign_neg]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting is positively responsive. -/
theorem exercise_21_B_1_responsive : PositivelyResponsive (ι := ι) majorityVoting := by
  intro α _ α' _ hle hne h0
  have hlt : ∑ i, α' i < ∑ i, α i := by
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    exact sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, lt_of_le_of_ne (hle j) (Ne.symm hj)⟩
  have h0' : 0 ≤ ∑ i, α' i := by
    unfold majorityVoting at h0
    rcases lt_or_ge (∑ i, α' i) 0 with h | h
    · rw [Int.sign_eq_neg_one_of_neg h] at h0
      omega
    · exact h
  exact Int.sign_eq_one_of_pos (by omega)

/-- Under symmetry and neutrality, a tie `n⁺ = n⁻` forces social indifference (first step of
the proof of Proposition 21.B.1, MWG, p. 792). -/
theorem may_tie {F : (ι → ℤ) → ℤ} (hS : SymmetricAmongAgents F)
    (hN : NeutralBetweenAlternatives F) {α : ι → ℤ} (hα : α ∈ TwoAltProfiles ι)
    (h : nPlus α = nMinus α) : F α = 0 := by
  classical
  set P := univ.filter fun i => α i = 1 with hP
  set N := univ.filter fun i => α i = -1 with hN'
  have hcard : Fintype.card P = Fintype.card N := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h
  let e : P ≃ N := Fintype.equivOfCardEq hcard
  have memP : ∀ i, i ∈ P ↔ α i = 1 := fun i => by simp [hP]
  have memN : ∀ i, i ∈ N ↔ α i = -1 := fun i => by simp [hN']
  have hPN : ∀ i, i ∈ N → i ∉ P := fun i hi hi' => by
    have h1 := (memP i).1 hi'
    rw [(memN i).1 hi] at h1
    exact absurd h1 (by decide)
  let π : ι → ι := fun i =>
    if h1 : i ∈ P then (e ⟨i, h1⟩ : ι) else if h2 : i ∈ N then (e.symm ⟨i, h2⟩ : ι) else i
  have hπα : ∀ i, α (π i) = -α i := by
    intro i
    by_cases h1 : i ∈ P
    · have : π i = (e ⟨i, h1⟩ : ι) := by simp only [π, h1, ↓reduceDIte]
      rw [this, (memN _).1 (e ⟨i, h1⟩).2, (memP i).1 h1]
    · by_cases h2 : i ∈ N
      · have : π i = (e.symm ⟨i, h2⟩ : ι) := by simp only [π, h1, h2, ↓reduceDIte]
        rw [this, (memP _).1 (e.symm ⟨i, h2⟩).2, (memN i).1 h2]
        rfl
      · have : π i = i := by simp only [π, h1, h2, ↓reduceDIte]
        rw [this]
        rcases hα i with h3 | h3 | h3
        · exact absurd ((memN i).2 h3) h2
        · rw [h3]; rfl
        · exact absurd ((memP i).2 h3) h1
  have hsurj : Function.Surjective π := by
    intro j
    by_cases h1 : j ∈ P
    · refine ⟨(e ⟨j, h1⟩ : ι), ?_⟩
      have hk1 : (e ⟨j, h1⟩ : ι) ∈ N := (e ⟨j, h1⟩).2
      have hk2 : (e ⟨j, h1⟩ : ι) ∉ P := hPN _ hk1
      simp only [π, hk2, hk1, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
    · by_cases h2 : j ∈ N
      · refine ⟨(e.symm ⟨j, h2⟩ : ι), ?_⟩
        have hk1 : (e.symm ⟨j, h2⟩ : ι) ∈ P := (e.symm ⟨j, h2⟩).2
        simp only [π, hk1, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]
      · exact ⟨j, by simp only [π, h1, h2, ↓reduceDIte]⟩
  have hcomp : α ∘ π = -α := funext fun i => hπα i
  have h1 := hS π hsurj α hα
  rw [hcomp] at h1
  have h2 := hN α hα
  omega

/-- Under symmetry, neutrality and positive responsiveness, `n⁺ > n⁻` forces `F(α) = 1`
(second step of the proof of Proposition 21.B.1, MWG, p. 792). -/
theorem may_plus {F : (ι → ℤ) → ℤ} (hS : SymmetricAmongAgents F)
    (hN : NeutralBetweenAlternatives F) (hR : PositivelyResponsive F) {α : ι → ℤ}
    (hα : α ∈ TwoAltProfiles ι) (h : nMinus α < nPlus α) : F α = 1 := by
  classical
  set P := univ.filter fun i => α i = 1 with hP
  obtain ⟨Q, hQP, hQcard⟩ := exists_subset_card_eq (s := P) (n := nPlus α - nMinus α)
    (by simp [nPlus, hP])
  let α' : ι → ℤ := fun i => if i ∈ Q then 0 else α i
  have hαQ : ∀ i ∈ Q, α i = 1 := fun i hi => by
    have := hQP hi
    simpa [hP] using this
  have hα' : α' ∈ TwoAltProfiles ι := by
    intro i
    by_cases hi : i ∈ Q
    · simp [α', hi]
    · simpa [α', hi] using hα i
  have hplus : nPlus α' = nMinus α := by
    have hfilter : (univ.filter fun i => α' i = 1) = P \ Q := by
      ext i
      by_cases hi : i ∈ Q <;> simp [α', hi, hP]
    have hsd : (P \ Q).card = P.card - Q.card := card_sdiff_of_subset hQP
    change (univ.filter fun i => α' i = 1).card = nMinus α
    rw [hfilter, hsd, hQcard]
    have hPc : P.card = nPlus α := rfl
    omega
  have hminus : nMinus α' = nMinus α := by
    unfold nMinus
    congr 1
    ext i
    by_cases hi : i ∈ Q
    · simp [α', hi, hαQ i hi]
    · simp [α', hi]
  have h0 : F α' = 0 := may_tie hS hN hα' (hplus.trans hminus.symm)
  have hQne : Q.Nonempty := by
    rw [← card_pos, hQcard]
    omega
  obtain ⟨j, hj⟩ := hQne
  refine hR α hα α' hα' (fun i => ?_) (fun heq => ?_) h0.ge
  · by_cases hi : i ∈ Q
    · simp [α', hi, hαQ i hi]
    · simp [α', hi]
  · have := congrFun heq j
    simp [α', hj, hαQ j hj] at this

/-- **Proposition 21.B.1 (May's theorem)** (MWG, p. 792). A social welfare functional over two
alternatives is majority voting iff it is symmetric among agents, neutral between
alternatives and positively responsive. (Proved for every `F : (ι → ℤ) → ℤ`.) -/
theorem proposition_21_B_1 (F : (ι → ℤ) → ℤ) :
    (∀ α ∈ TwoAltProfiles ι, F α = majorityVoting α) ↔
      SymmetricAmongAgents F ∧ NeutralBetweenAlternatives F ∧ PositivelyResponsive F := by
  constructor
  · intro h
    refine ⟨fun π hπ α hα => ?_, fun α hα => ?_, fun α hα α' hα' hle hne h0 => ?_⟩
    · have hα' : α ∘ π ∈ TwoAltProfiles ι := fun i => hα (π i)
      rw [h α hα, h _ hα']
      exact exercise_21_B_1_symmetric π hπ α hα
    · rw [h α hα, h _ (neg_mem_twoAltProfiles hα)]
      exact exercise_21_B_1_neutral α hα
    · rw [h α hα]
      rw [h α' hα'] at h0
      exact exercise_21_B_1_responsive α hα α' hα' hle hne h0
  · rintro ⟨hS, hN, hR⟩ α hα
    rcases lt_trichotomy (nMinus α) (nPlus α) with hlt | heq | hgt
    · rw [may_plus hS hN hR hα hlt, ((majorityVoting_spec hα).1).2 hlt]
    · rw [may_tie hS hN hα heq.symm, ((majorityVoting_spec hα).2.2).2 heq.symm]
    · have hα' := neg_mem_twoAltProfiles hα
      have hc1 : nPlus (-α) = nMinus α := by
        unfold nPlus nMinus
        congr 1
        ext i
        simp [neg_eq_iff_eq_neg]
      have hc2 : nMinus (-α) = nPlus α := by
        unfold nPlus nMinus
        congr 1
        ext i
        simp [neg_eq_iff_eq_neg]
      have h1 : F (-α) = 1 := may_plus hS hN hR hα' (by omega)
      rw [hN α hα, h1, ((majorityVoting_spec hα).2.1).2 hgt]

/-- **Exercise 21.B.1** (MWG, p. 812). Majority voting satisfies the three properties. -/
theorem exercise_21_B_1 :
    SymmetricAmongAgents (ι := ι) majorityVoting ∧
      NeutralBetweenAlternatives (ι := ι) majorityVoting ∧
      PositivelyResponsive (ι := ι) majorityVoting :=
  ⟨exercise_21_B_1_symmetric, exercise_21_B_1_neutral, exercise_21_B_1_responsive⟩

/-- Weighted integer voting `sign ∑ wᵢ αᵢ` with weight `2` for agent `i₀` and `1` otherwise
(Exercise 21.B.2). -/
def tiltedVoting [DecidableEq ι] (i₀ : ι) (α : ι → ℤ) : ℤ :=
  Int.sign (∑ i, (if i = i₀ then 2 else 1) * α i)

/-- **Exercise 21.B.2**, symmetry dropped (MWG, p. 812). With two distinct agents, the tilted
rule is neutral and positively responsive but not symmetric, hence not majority voting. -/
theorem exercise_21_B_2_symmetry [DecidableEq ι] {i₀ i₁ : ι} (h01 : i₀ ≠ i₁) :
    NeutralBetweenAlternatives (tiltedVoting i₀) ∧ PositivelyResponsive (tiltedVoting i₀) ∧
      ¬SymmetricAmongAgents (tiltedVoting i₀) ∧
      ¬∀ α ∈ TwoAltProfiles ι, tiltedVoting i₀ α = majorityVoting α := by
  have hN : NeutralBetweenAlternatives (tiltedVoting i₀) := by
    intro α _
    simp [tiltedVoting, mul_neg, sum_neg_distrib, Int.sign_neg]
  have hR : PositivelyResponsive (tiltedVoting i₀) := by
    intro α _ α' _ hle hne h0
    have hlt : ∑ i, (if i = i₀ then 2 else 1) * α' i < ∑ i, (if i = i₀ then 2 else 1) * α i := by
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
        by_contra hc
        push Not at hc
        exact hne (funext hc)
      refine sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
      · split_ifs <;> linarith [hle i]
      · have := lt_of_le_of_ne (hle j) (Ne.symm hj)
        split_ifs <;> linarith
    have h0' : 0 ≤ ∑ i, (if i = i₀ then 2 else 1) * α' i := by
      unfold tiltedVoting at h0
      rcases lt_or_ge (∑ i, (if i = i₀ then 2 else 1) * α' i) 0 with h | h
      · rw [Int.sign_eq_neg_one_of_neg h] at h0
        omega
      · exact h
    exact Int.sign_eq_one_of_pos (by omega)
  let α : ι → ℤ := fun i => if i = i₀ then 1 else if i = i₁ then -1 else 0
  have hα : α ∈ TwoAltProfiles ι := by
    intro i
    by_cases h0 : i = i₀ <;> by_cases h1 : i = i₁ <;> simp [α, h0, h1, Ne.symm h01]
  have hsum : ∑ i, (if i = i₀ then 2 else 1) * α i = 1 := by
    rw [Fintype.sum_eq_add i₀ i₁ h01 (fun i hi => by simp [α, hi.1, hi.2])]
    simp [α, Ne.symm h01]
  let π : ι → ι := Equiv.swap i₀ i₁
  have hsum' : ∑ i, (if i = i₀ then 2 else 1) * (α ∘ π) i = -1 := by
    rw [Fintype.sum_eq_add i₀ i₁ h01 (fun i hi => by
      simp [α, π, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, hi.1, hi.2])]
    simp [α, π, Ne.symm h01]
  have hnotS : ¬SymmetricAmongAgents (tiltedVoting i₀) := by
    intro hS
    have := hS π (Equiv.surjective _) α hα
    simp only [tiltedVoting, hsum, hsum'] at this
    norm_num at this
  refine ⟨hN, hR, hnotS, fun h => hnotS ?_⟩
  intro π' hπ' β hβ
  have hβ' : β ∘ π' ∈ TwoAltProfiles ι := fun i => hβ (π' i)
  rw [h β hβ, h _ hβ']
  exact exercise_21_B_1_symmetric π' hπ' β hβ

/-- The rule `F(α) = 1` if `n⁺ ≥ n⁻` and `-1` otherwise (Exercise 21.B.2). -/
def xBiasedVoting (α : ι → ℤ) : ℤ := if 0 ≤ ∑ i, α i then 1 else -1

/-- **Exercise 21.B.2**, neutrality dropped (MWG, p. 812). The `x`-biased rule is symmetric
and positively responsive but not neutral, hence not majority voting. -/
theorem exercise_21_B_2_neutrality :
    SymmetricAmongAgents (ι := ι) xBiasedVoting ∧ PositivelyResponsive (ι := ι) xBiasedVoting ∧
      ¬NeutralBetweenAlternatives (ι := ι) xBiasedVoting ∧
      ¬∀ α ∈ TwoAltProfiles ι, xBiasedVoting α = majorityVoting α := by
  have hS : SymmetricAmongAgents (ι := ι) xBiasedVoting := by
    intro π hπ α _
    have hinj : Function.Injective π := Finite.injective_iff_surjective.mpr hπ
    unfold xBiasedVoting
    rw [show ∑ i, (α ∘ π) i = ∑ i, α i from
      Equiv.sum_comp (Equiv.ofBijective π ⟨hinj, hπ⟩) α]
  have hR : PositivelyResponsive (ι := ι) xBiasedVoting := by
    intro α _ α' _ hle hne h0
    have hlt : ∑ i, α' i < ∑ i, α i := by
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ α' j := by
        by_contra hc
        push Not at hc
        exact hne (funext hc)
      exact sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, lt_of_le_of_ne (hle j) (Ne.symm hj)⟩
    have h0' : 0 ≤ ∑ i, α' i := by
      unfold xBiasedVoting at h0
      split_ifs at h0 with h
      · exact h
      · omega
    unfold xBiasedVoting
    simp [show (0 : ℤ) ≤ ∑ i, α i by omega]
  have hnot : ¬NeutralBetweenAlternatives (ι := ι) xBiasedVoting := by
    intro hN
    have := hN 0 (fun _ => Or.inr (Or.inl rfl))
    simp [xBiasedVoting] at this
  refine ⟨hS, hR, hnot, fun h => hnot ?_⟩
  intro β hβ
  rw [h β hβ, h _ (neg_mem_twoAltProfiles hβ)]
  exact exercise_21_B_1_neutral β hβ

/-- **Exercise 21.B.2**, positive responsiveness dropped (MWG, p. 812). With at least one
agent, the constant rule `F ≡ 0` is symmetric and neutral but not positively responsive, hence
not majority voting. -/
theorem exercise_21_B_2_responsiveness (i₀ : ι) :
    SymmetricAmongAgents (fun _ : ι → ℤ => (0 : ℤ)) ∧
      NeutralBetweenAlternatives (fun _ : ι → ℤ => (0 : ℤ)) ∧
      ¬PositivelyResponsive (fun _ : ι → ℤ => (0 : ℤ)) ∧
      ¬∀ α ∈ TwoAltProfiles ι, (0 : ℤ) = majorityVoting α := by
  classical
  have hnot : ¬PositivelyResponsive (fun _ : ι → ℤ => (0 : ℤ)) := by
    intro hR
    have h1 : (fun i => if i = i₀ then (1 : ℤ) else 0) ∈ TwoAltProfiles ι := by
      intro i
      by_cases h : i = i₀ <;> simp [h]
    have := hR _ h1 0 (fun _ => Or.inr (Or.inl rfl)) (fun i => by split_ifs <;> simp)
      (fun h => by simpa using congrFun h i₀) le_rfl
    simp at this
  refine ⟨fun _ _ _ _ => rfl, fun _ _ => by simp, hnot, fun h => hnot ?_⟩
  intro β hβ β' hβ' hle hne _
  have e1 := h β hβ
  have e2 := h β' hβ'
  have := exercise_21_B_1_responsive β hβ β' hβ' hle hne (by rw [← e2])
  change (0 : ℤ) = 1
  omega

/-- The level `k ∈ {0, 1}` is Pareto optimal among the two levels with no transfers, when
agent `i` gains `vᵢ k` from level `k` (Exercise 21.B.3). -/
def ParetoOptimalNoTransfers (v : ι → ℝ) (k : ℕ) : Prop :=
  ¬∃ k' ∈ ({0, 1} : Set ℕ), (∀ i, v i * k ≤ v i * k') ∧ ∃ i, v i * k < v i * k'

/-- The level `k ∈ {0, 1}` is a majority decision: `k = 1` only if at least as many agents
strictly gain from the project as strictly lose, and `k = 0` only if at least as many lose as
gain (Exercise 21.B.3). -/
def MajorityDecision (v : ι → ℝ) (k : ℕ) : Prop :=
  (k = 0 ∨ k = 1) ∧
    (k = 1 → (univ.filter fun i => v i < 0).card ≤ (univ.filter fun i => 0 < v i).card) ∧
    (k = 0 → (univ.filter fun i => 0 < v i).card ≤ (univ.filter fun i => v i < 0).card)

/-- **Exercise 21.B.3**, first claim (MWG, p. 812). A majority decision over the two levels of
the public project is Pareto optimal among the two levels when no transfers take place. -/
theorem exercise_21_B_3_pareto_no_transfers {v : ι → ℝ} {k : ℕ} (hk : MajorityDecision v k) :
    ParetoOptimalNoTransfers v k := by
  rintro ⟨k', hk', hall, j, hj⟩
  rcases hk.1 with rfl | rfl <;> rcases hk' with rfl | rfl
  · simp at hj
  · have hpos : (univ.filter fun i => v i < 0) = ∅ := by
      ext i
      have := hall i
      simp only [Nat.cast_zero, mul_zero, Nat.cast_one, mul_one] at this
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
      exact this
    have hj' : 0 < v j := by simpa using hj
    have := hk.2.2 rfl
    rw [hpos, card_empty] at this
    have hmem : j ∈ univ.filter fun i => 0 < v i := by simp [hj']
    have := card_pos.mpr ⟨j, hmem⟩
    omega
  · have hneg : (univ.filter fun i => 0 < v i) = ∅ := by
      ext i
      have := hall i
      simp only [Nat.cast_one, mul_one, Nat.cast_zero, mul_zero] at this
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
      exact this
    have hj' : v j < 0 := by simpa using hj
    have := hk.2.1 rfl
    rw [hneg, card_empty] at this
    have hmem : j ∈ univ.filter fun i => v i < 0 := by simp [hj']
    have := card_pos.mpr ⟨j, hmem⟩
    omega
  · simp at hj

/-- A policy with transfers: a level `k ∈ {0, 1}` and transfers `t` with `∑ tᵢ = 0`; agent `i`
gets `vᵢ k + tᵢ` (Exercise 21.B.3). -/
def FeasibleWithTransfers (k : ℕ) (t : ι → ℝ) : Prop := (k = 0 ∨ k = 1) ∧ ∑ i, t i = 0

/-- Pareto optimality among policies with transfers (Exercise 21.B.3). -/
def ParetoOptimalWithTransfers (v : ι → ℝ) (k : ℕ) (t : ι → ℝ) : Prop :=
  ¬∃ k' t', FeasibleWithTransfers k' t' ∧ (∀ i, v i * k + t i ≤ v i * k' + t' i) ∧
    ∃ i, v i * k + t i < v i * k' + t' i

/-- **Exercise 21.B.3**, the "mean" rule (MWG, p. 812). With at least one agent, a feasible
policy with transfers is Pareto optimal iff its level maximizes total willingness to pay
`∑ vᵢ k`, i.e. `k = 1` needs `∑ vᵢ ≥ 0` and `k = 0` needs `∑ vᵢ ≤ 0`. -/
theorem exercise_21_B_3_mean [Nonempty ι] (v : ι → ℝ) {k : ℕ} {t : ι → ℝ}
    (hf : FeasibleWithTransfers k t) :
    ParetoOptimalWithTransfers v k t ↔ ∀ k' ∈ ({0, 1} : Set ℕ),
      ∑ i, v i * k' ≤ ∑ i, v i * k := by
  constructor
  · intro hpo k' hk'
    by_contra hlt
    push Not at hlt
    set δ := (∑ i, v i * k' - ∑ i, v i * k) / Fintype.card ι with hδ
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hδpos : 0 < δ := div_pos (by linarith) hcard
    refine hpo ⟨k', fun i => v i * k + t i - v i * k' + δ, ⟨hk', ?_⟩, fun i => ?_, ?_⟩
    · rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, hf.2, sum_const, card_univ,
        nsmul_eq_mul, hδ]
      rw [mul_div_cancel₀ _ hcard.ne']
      ring
    · linarith
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, by linarith⟩
  · rintro hmax ⟨k', t', hf', hle, j, hj⟩
    have h1 : ∑ i, (v i * k + t i) < ∑ i, (v i * k' + t' i) :=
      sum_lt_sum (fun i _ => hle i) ⟨j, mem_univ j, hj⟩
    rw [sum_add_distrib, sum_add_distrib, hf.2, hf'.2] at h1
    have := hmax k' hf'.1
    linarith

/-- **Exercise 21.B.3**, majority versus Pareto with transfers (MWG, p. 812). With
willingness to pay `v = (1, 1, -10)`, building the project (`k = 1`) is a majority decision
but is Pareto dominated, once transfers are allowed, by not building and transferring
`(1, 1, -2)`. -/
theorem exercise_21_B_3_not_pareto_with_transfers :
    MajorityDecision (![1, 1, -10] : Fin 3 → ℝ) 1 ∧
      ¬ParetoOptimalWithTransfers (![1, 1, -10] : Fin 3 → ℝ) 1 (fun _ => 0) := by
  constructor
  · refine ⟨Or.inr rfl, fun _ => ?_, fun h => absurd h (by norm_num)⟩
    have h1 : (univ.filter fun i : Fin 3 => (![1, 1, -10] : Fin 3 → ℝ) i < 0) = {2} := by
      ext i
      fin_cases i <;> simp
    have h2 : (univ.filter fun i : Fin 3 => 0 < (![1, 1, -10] : Fin 3 → ℝ) i) = {0, 1} := by
      ext i
      fin_cases i <;> simp
    rw [h1, h2]
    decide
  · intro h
    refine h ⟨0, ![1, 1, -2], ⟨Or.inl rfl, ?_⟩, fun i => ?_, ⟨2, ?_⟩⟩
    · simp [Fin.sum_univ_succ]
      norm_num
    · fin_cases i <;> norm_num
    · simp
      norm_num

end MWG.SocialChoice
