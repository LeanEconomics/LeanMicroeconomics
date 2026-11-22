/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.NashImplementation
import MWGSocialChoice.SinglePeaked

/-!
# Exercises on dominant strategy implementation

MWG, Exercises 23.C.2 and 23.C.5-23.C.8 (pp. 918-920), with the remark on p. 875.

* **Exercise 23.C.2** (and p. 875): with two alternatives (`X = Bool`), a majority voting social
  choice function (the alternative preferred by more agents is chosen; either one on a tie) is
  strategy-proof for any number of agents (`exercise_23_C_2`), provided it depends only on the
  agents' ordinal preferences (`OrdinalSCF`), as in Section 21.E where types are ordinal
  preferences. **Correction of scope**: with cardinal types and a tie-breaking rule depending on
  preference intensities, a majority voting function can fail to be strategy-proof
  (`exercise_23_C_2_cardinal`: two agents, `f(θ) = x₁` iff `θ₁ + θ₂ ≥ 0`).
* **Exercise 23.C.5**: with single-peaked preferences without indifference and an odd number of
  agents, the Condorcet-winner social choice function is strategy-proof (`exercise_23_C_5`;
  non-vacuity `exercise_23_C_5_instance`). The proof uses Chapter 21's median voter result.
* **Exercise 23.C.6** (IPM = the property (23.C.6) of Proposition 23.C.2): (a) IPM does not imply
  monotonicity (the social choice function of Exercise 23.C.8, which has indifferences);
  (b) monotonicity does not imply IPM (one agent, four alternatives, strict preferences);
  (c) IPM and `𝓡ᵢ ⊆ 𝒫` imply monotonicity (Step 1 of the Gibbard-Satterthwaite proof);
  (d) monotonicity and `𝓡ᵢ = 𝒫` imply IPM.
* **Exercise 23.C.7**: a social choice function selecting the unique maximal element of a
  nonnegatively responsive social welfare functional (whose social preferences are transitive)
  is strategy-proof.
* **Exercise 23.C.8**: the social choice function `f = b` at `(θ₁', θ₂')`, `a` otherwise, is ex
  post efficient and satisfies (23.C.6), but announcing `θᵢ''` is also weakly dominant for type
  `θᵢ'`; if an agent uses that untruthful dominant strategy, `f` is not implemented.

Departures: Exercise 23.C.5's social choice function is any selection of a Condorcet winner
(it is unique, by the median voter theorem); Exercise 23.C.7 assumes transitivity of the social
preferences at the profiles that arise (MWG's social welfare functionals are rational).
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {ι : Type*} {Θ : ι → Type*}

/-! ### Exercise 23.C.2: two alternatives -/

/-- The number of agents who strictly prefer the alternative `x ∈ Bool` to the other one. -/
noncomputable def numPref [Fintype ι] (u : (i : ι) → Bool → Θ i → ℝ) (θ : (i : ι) → Θ i)
    (x : Bool) : ℕ := by
  classical exact (Finset.univ.filter fun i => u i (!x) (θ i) < u i x (θ i)).card

/-- **Exercise 23.C.2** (MWG, pp. 918-919). `f` is a majority voting social choice function on
`X = Bool`: it chooses the alternative that more agents strictly prefer (either one on a tie). -/
def IsMajorityVoting [Fintype ι] (u : (i : ι) → Bool → Θ i → ℝ) (f : ((i : ι) → Θ i) → Bool) :
    Prop :=
  ∀ θ x, numPref u θ (!x) < numPref u θ x → f θ = x

/-- `f` depends on the types only through the agents' ordinal preferences (MWG's Section 21.E
setting, where a type is an ordinal preference). -/
def OrdinalSCF (u : (i : ι) → Bool → Θ i → ℝ) (f : ((i : ι) → Θ i) → Bool) : Prop :=
  ∀ θ θ', (∀ i, inducedPref u i (θ i) = inducedPref u i (θ' i)) → f θ = f θ'

/-- Changing agent `i`'s type changes the count only through agent `i`. -/
theorem numPref_update [Fintype ι] [DecidableEq ι] (u : (i : ι) → Bool → Θ i → ℝ)
    (θ : (i : ι) → Θ i) (i : ι) (a : Θ i) (x : Bool) :
    numPref u (update θ i a) x + (if u i (!x) (θ i) < u i x (θ i) then 1 else 0) =
      numPref u θ x + (if u i (!x) a < u i x a then 1 else 0) := by
  classical
  unfold numPref
  rw [Finset.card_filter, Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), update_self,
    Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]]
  ring

/-- Two types that both strictly prefer `x` induce the same preference on `Bool`. -/
theorem inducedPref_bool_eq {u : (i : ι) → Bool → Θ i → ℝ} {i : ι} {a a' : Θ i} {x : Bool}
    (ha : u i (!x) a < u i x a) (ha' : u i (!x) a' < u i x a') :
    inducedPref u i a = inducedPref u i a' := by
  have hb : ∀ b : Bool, b = x ∨ b = !x := by intro b; cases b <;> cases x <;> simp
  funext y z
  apply propext
  simp only [inducedPref]
  rcases hb y with rfl | rfl <;> rcases hb z with rfl | rfl
  · exact Iff.rfl.trans ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · exact ⟨fun _ => ha'.le, fun _ => ha.le⟩
  · exact ⟨fun h => absurd h (not_le.2 ha), fun h => absurd h (not_le.2 ha')⟩
  · exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-- **Exercise 23.C.2** (MWG, pp. 875, 918-919). With two alternatives, every majority voting
social choice function that depends only on ordinal preferences is truthfully implementable in
dominant strategies, for any number of agents and any tie-breaking rule. -/
theorem exercise_23_C_2 [Fintype ι] [DecidableEq ι] {u : (i : ι) → Bool → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → Bool} (hM : IsMajorityVoting u f) (hO : OrdinalSCF u f) :
    StrategyProof u f := by
  intro i θ θh
  have key : ∀ x : Bool, u i (!x) (θ i) < u i x (θ i) →
      u i (f (update θ i θh)) (θ i) ≤ u i (f θ) (θ i) := by
    intro x hx
    have hcases : ∀ b : Bool, b = x ∨ b = !x := by intro b; cases b <;> cases x <;> simp
    rcases hcases (f θ) with hf | hf
    · rw [hf]
      rcases hcases (f (update θ i θh)) with h' | h'
      · rw [h']
      · rw [h']; exact hx.le
    · by_cases hθh : u i (!x) θh < u i x θh
      · rw [hO θ (update θ i θh) fun j => by
          by_cases hj : j = i
          · subst hj; rw [update_self]; exact inducedPref_bool_eq hx hθh
          · rw [update_of_ne hj]]
      · have hnot : ¬numPref u θ (!x) < numPref u θ x := fun h => by
          have := hM θ x h; rw [hf] at this; cases x <;> simp at this
        have h1 := numPref_update u θ i θh x
        have h2 := numPref_update u θ i θh (!x)
        simp only [hx, hθh, ↓reduceIte, Bool.not_not, not_lt.2 hx.le] at h1 h2
        have hlt : numPref u (update θ i θh) (!!x) < numPref u (update θ i θh) (!x) := by
          rw [Bool.not_not]; split_ifs at h2 <;> omega
        rw [hM _ (!x) hlt, hf]
  rcases lt_trichotomy (u i false (θ i)) (u i true (θ i)) with h | h | h
  · exact key true h
  · have hall : ∀ b : Bool, u i b (θ i) = u i true (θ i) := by
      intro b; cases b
      · exact h
      · rfl
    rw [hall (f (update θ i θh)), hall (f θ)]
  · exact key false h

/-- **Exercise 23.C.2**, non-vacuity: majority voting with ties going to `x₁ = true`,
`f(θ) = x₁` iff `#{i : x₂ ≻ᵢ x₁} ≤ #{i : x₁ ≻ᵢ x₂}`, is a majority voting social choice function
depending only on ordinal preferences (for any utilities). -/
theorem exercise_23_C_2_instance [Fintype ι] (u : (i : ι) → Bool → Θ i → ℝ) :
    IsMajorityVoting u (fun θ => decide (numPref u θ false ≤ numPref u θ true)) ∧
      OrdinalSCF u (fun θ => decide (numPref u θ false ≤ numPref u θ true)) := by
  classical
  refine ⟨fun θ x h => ?_, fun θ θ' h => ?_⟩
  · cases x
    · exact decide_eq_false (not_le.2 h)
    · exact decide_eq_true h.le
  · have hn : ∀ x, numPref u θ x = numPref u θ' x := by
      intro x
      unfold numPref
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      have := congrFun (congrFun (h i) (!x)) x
      simp only [inducedPref] at this
      rw [← not_le, ← not_le, this]
    simp only [hn]

/-- **Exercise 23.C.2**, correction of scope (MWG, pp. 918-919). With cardinal types the claim
needs the tie-breaking rule to ignore preference intensities. Two agents with
`uᵢ(x₁, θᵢ) = θᵢ`, `uᵢ(x₂, θᵢ) = 0` (`x₁ = true`) and `f(θ) = x₁` iff `θ₁ + θ₂ ≥ 0`: `f` is a
majority voting social choice function (it breaks ties by intensity), but agent 1 of type `1`
facing type `-2` gets `x₂`, and gets `x₁` by announcing `3`. -/
theorem exercise_23_C_2_cardinal :
    IsMajorityVoting (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0)
        (fun θ => decide (0 ≤ θ 0 + θ 1)) ∧
      ¬StrategyProof (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0)
        (fun θ => decide (0 ≤ θ 0 + θ 1)) ∧
      ¬OrdinalSCF (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0)
        (fun θ => decide (0 ≤ θ 0 + θ 1)) := by
  classical
  have hcount : ∀ (θ : Fin 2 → ℝ) (x : Bool),
      numPref (Θ := fun _ : Fin 2 => ℝ) (fun _ x θi => if x then θi else 0) θ x =
        (if (if !x then θ 0 else 0) < (if x then θ 0 else 0) then 1 else 0) +
          (if (if !x then θ 1 else 0) < (if x then θ 1 else 0) then 1 else 0) := by
    intro θ x
    unfold numPref
    rw [Finset.card_filter, Fin.sum_univ_two]
  refine ⟨fun θ x h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hcount, hcount] at h
    cases x <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      <;> split_ifs at h with h0 h1 h2 h3 <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not,
        not_le] <;> first | omega | linarith
  · have := h 0 ![1, -2] 3
    norm_num at this
  · have := h ![1, -2] ![3, -2] fun i => by
      fin_cases i
      · exact inducedPref_bool_eq (x := true) (by norm_num) (by norm_num)
      · rfl
    norm_num at this

/-! ### Exercise 23.C.5: single-peaked preferences -/

/-- The profile of ordinal preferences induced by a type profile. -/
def typeProfile {X : Type*} (u : (i : ι) → X → Θ i → ℝ) (θ : (i : ι) → Θ i) : Profile ι X :=
  fun i => inducedPref u i (θ i)

/-- Strict preference under the induced preference. -/
theorem strict_inducedPref_iff {X : Type*} {u : (i : ι) → X → Θ i → ℝ} {i : ι} {θi : Θ i}
    {a b : X} : Strict (inducedPref u i θi) a b ↔ u i b θi < u i a θi := by
  simp only [Strict, inducedPref, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- **Exercise 23.C.5** (MWG, p. 919). Suppose every type's preference is single peaked with
respect to a linear order on `X` and has no indifference, and the number of agents is odd. Then
the social choice function selecting a Condorcet winner (Section 21.D) is truthfully
implementable in dominant strategies. -/
theorem exercise_23_C_5 [Fintype ι] [DecidableEq ι] {X : Type*} [LinearOrder X]
    {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hSP : ∀ i θi, inducedPref u i θi ∈ StrictSinglePeakedPrefs X)
    (hodd : Odd (Fintype.card ι)) (hf : ∀ θ, IsCondorcetWinner (typeProfile u θ) (f θ)) :
    StrategyProof u f := by
  classical
  intro i θ θh
  by_contra hlt
  rw [not_le] at hlt
  set θ' := update θ i θh with hθ'
  set c := f θ
  set c' := f θ'
  have hcc : c ≠ c' := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  -- the Condorcet winner at `θ` strictly defeats `c'`
  have hne : Nonempty ι := ⟨i⟩
  choose pk hpk using fun j => (hSP j (θ j)).1.2
  obtain ⟨h, hh⟩ := median_exists pk
  obtain ⟨-, hstrict⟩ := proposition_21_D_1 (p := typeProfile u θ) hpk hh
  have hc : c = pk h := by
    by_contra hne'
    have h1 := hstrict hodd c hne'
    have h2 : majorityRel (typeProfile u θ) c (pk h) := hf θ (pk h)
    rw [majorityRel_iff] at h2
    omega
  have hA := hstrict hodd c' (fun e => hcc (hc.trans e.symm))
  rw [← hc] at hA
  -- `c'` is a Condorcet winner at `θ'`
  have hB : majorityRel (typeProfile u θ') c' c := hf θ' c
  rw [majorityRel_iff] at hB
  have s1 : (Finset.univ.filter fun j => Strict (typeProfile u θ j) c c') ⊆
      Finset.univ.filter fun j => Strict (typeProfile u θ' j) c c' := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hji : j = i
    · subst hji
      exact absurd (strict_inducedPref_iff.1 hj) (not_lt.2 hlt.le)
    · simpa [typeProfile, hθ', update_of_ne hji] using hj
  have s2 : (Finset.univ.filter fun j => Strict (typeProfile u θ' j) c' c) ⊆
      Finset.univ.filter fun j => Strict (typeProfile u θ j) c' c := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hji : j = i
    · subst hji
      exact strict_inducedPref_iff.2 hlt
    · simpa [typeProfile, hθ', update_of_ne hji] using hj
  have c1 := Finset.card_le_card s1
  have c2 := Finset.card_le_card s2
  omega

/-- A single-peaked strict preference on `Fin 3`: `2 ≻ 1 ≻ 0` (peak `2`). -/
theorem singlePeaked_fin3 :
    natPref (fun x : Fin 3 => x.val) ∈ StrictSinglePeakedPrefs (Fin 3) := by
  have hs := natPref_mem_strict (X := Fin 3) Fin.val_injective
  refine ⟨⟨hs.1, 2, fun y z => ⟨fun _ hyz => ?_, fun h2 hzy => ?_⟩⟩, hs.2⟩
  · exact (natPref_strict_iff _ _ _).2 hyz
  · exact absurd (lt_of_le_of_lt h2 hzy) (not_lt.2 (Fin.le_last y))

/-- **Exercise 23.C.5**, non-vacuity (MWG, p. 919). Three agents, `X = Fin 3`, types = all strict
single-peaked preferences (nonempty), rank utilities: a Condorcet winner selection exists, and
it is strategy-proof. -/
theorem exercise_23_C_5_instance :
    Nonempty {r // r ∈ StrictSinglePeakedPrefs (Fin 3)} ∧
    ∃ f : (Fin 3 → {r // r ∈ StrictSinglePeakedPrefs (Fin 3)}) → Fin 3,
      (∀ θ, IsCondorcetWinner (typeProfile (fun _ x θi => rankUtil θi.1 x) θ) (f θ)) ∧
      StrategyProof (Θ := fun _ : Fin 3 => {r // r ∈ StrictSinglePeakedPrefs (Fin 3)})
        (fun _ x θi => rankUtil θi.1 x) f := by
  have hind : ∀ (i : Fin 3) (θi : {r // r ∈ StrictSinglePeakedPrefs (Fin 3)}),
      inducedPref (Θ := fun _ : Fin 3 => {r // r ∈ StrictSinglePeakedPrefs (Fin 3)})
        (fun _ x θi => rankUtil θi.1 x) i θi = θi.1 := by
    intro i θi
    funext x y
    exact propext (rankUtil_le_iff θi.2.1.1 x y)
  have hprof : ∀ θ : Fin 3 → {r // r ∈ StrictSinglePeakedPrefs (Fin 3)},
      typeProfile (fun _ x θi => rankUtil θi.1 x) θ ∈ SinglePeakedProfiles (Fin 3) (Fin 3) := by
    intro θ j
    simp only [typeProfile, hind]
    exact (θ j).2.1
  choose f hf using fun θ => proposition_21_D_1_exists (hprof θ)
  refine ⟨⟨⟨_, singlePeaked_fin3⟩⟩, f, hf, exercise_23_C_5 (fun i θi => ?_) (by decide) hf⟩
  rw [hind]
  exact θi.2

/-! ### Exercise 23.C.6: independent person-by-person monotonicity -/

/-- **Exercise 23.C.6** (MWG, p. 919). Independent person-by-person monotonicity (IPM): the
property (23.C.6) of Proposition 23.C.2, `f(θᵢ'', θ₋ᵢ) ∈ Lᵢ(f(θᵢ', θ₋ᵢ), θᵢ')` and
`f(θᵢ', θ₋ᵢ) ∈ Lᵢ(f(θᵢ'', θ₋ᵢ), θᵢ'')`. -/
def IPM [DecidableEq ι] {X : Type*} (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    Prop :=
  ∀ i (θ : (j : ι) → Θ j) (θ' θ'' : Θ i),
    f (update θ i θ'') ∈ lowerContour u i (f (update θ i θ')) θ' ∧
      f (update θ i θ') ∈ lowerContour u i (f (update θ i θ'')) θ''

/-- IPM is strategy-proofness (Proposition 23.C.2). -/
theorem ipm_iff [DecidableEq ι] {X : Type*} (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) : IPM u f ↔ StrategyProof u f :=
  (proposition_23_C_2 u f).symm

/-- **Exercise 23.C.6(a)** (MWG, p. 919). IPM does not imply monotonicity: the social choice
function of Exercise 23.C.8 (where `a ~ b` for type `θᵢ'`) satisfies IPM but is not monotonic. -/
theorem exercise_23_C_6a :
    IPM (Θ := fun _ : Fin 2 => Bool) c8U c8F ∧ ¬MonotonicSCF (Θ := fun _ : Fin 2 => Bool) c8U c8F :=
  ⟨(ipm_iff _ _).2 exercise_23_BB_2b_strategyProof, exercise_23_BB_2b_not_monotonic⟩

/-- **Exercise 23.C.6(b)**. One agent, `X = {a, b, c, d}` (`0, …, 3`), type `θ'` (`true`):
`a ≻ b ≻ c ≻ d`; type `θ''` (`false`): `b ≻ d ≻ c ≻ a`. -/
def c6U : Unit → Fin 4 → Bool → ℝ := fun _ x t => if t then ![3, 2, 1, 0] x else ![0, 3, 1, 2] x

/-- **Exercise 23.C.6(b)**. `f(θ') = c`, `f(θ'') = b`. -/
def c6F (θ : Unit → Bool) : Fin 4 := if θ () then 2 else 1

/-- **Exercise 23.C.6(b)** (MWG, p. 919). Monotonicity does not imply IPM, even with strict
preferences: `c6F` is monotonic (no type change keeps the chosen alternative's lower contour
sets from shrinking), but type `θ'` prefers `b = f(θ'')` to `c = f(θ')`. -/
theorem exercise_23_C_6b :
    MonotonicSCF (Θ := fun _ : Unit => Bool) c6U c6F ∧
      ¬IPM (Θ := fun _ : Unit => Bool) c6U c6F ∧
      ∀ i, prefSet (Θ := fun _ : Unit => Bool) c6U i ⊆ StrictPrefs (Fin 4) := by
  refine ⟨fun θ θ' hL => ?_, fun h => ?_, fun i r hr => ?_⟩
  · cases h0 : θ () <;> cases h1 : θ' ()
    · have : θ = θ' := funext fun _ => by rw [h0, h1]
      rw [this]
    · have := hL () (show (0 : Fin 4) ∈ lowerContour c6U () (c6F θ) (θ ()) by
        simp [lowerContour, c6U, c6F, h0])
      norm_num [lowerContour, c6U, c6F, h0, h1] at this
    · have := hL () (show (3 : Fin 4) ∈ lowerContour c6U () (c6F θ) (θ ()) by
        simp [lowerContour, c6U, c6F, h0])
      norm_num [lowerContour, c6U, c6F, h0, h1] at this
    · have : θ = θ' := funext fun _ => by rw [h0, h1]
      rw [this]
  · have := ((ipm_iff _ _).1 h) () (fun _ => true) false
    norm_num [c6U, c6F] at this
  · obtain ⟨t, rfl⟩ := hr
    refine ⟨inducedPref_rational _ _ _, fun x y h1 h2 => ?_⟩
    simp only [inducedPref] at h1 h2
    have := le_antisymm h2 h1
    revert this
    cases t <;> fin_cases x <;> fin_cases y <;> norm_num [c6U]

/-- **Exercise 23.C.6(c)** (MWG, p. 919). If `f` satisfies IPM and `𝓡ᵢ ⊆ 𝒫` for all `i` (finitely
many agents), then `f` is monotonic. -/
theorem exercise_23_C_6c [Finite ι] [DecidableEq ι] {X : Type*} {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i ⊆ StrictPrefs X) (h : IPM u f) :
    MonotonicSCF u f :=
  gs_step_1 hR ((ipm_iff u f).1 h)

/-- **Exercise 23.C.6(d)** (MWG, p. 919). If `f` is monotonic and `𝓡ᵢ = 𝒫` for all `i`, then `f`
satisfies IPM. If agent `i` of type `θᵢ` preferred `y = f(θ̂ᵢ, θ₋ᵢ)` to `x = f(θ)`, a type ranking
`y` first and `x` second would get both `y` (monotonicity from `(θ̂ᵢ, θ₋ᵢ)`) and `x`
(monotonicity from `θ`). -/
theorem exercise_23_C_6d [DecidableEq ι] {X : Type*} {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i = StrictPrefs X) (hM : MonotonicSCF u f) :
    IPM u f := by
  rw [ipm_iff]
  intro i θ θh
  by_contra hlt
  rw [not_le] at hlt
  set x := f θ with hx
  set y := f (update θ i θh) with hy
  have hxy : x ≠ y := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hr : inducedPref u i (θ i) ∈ StrictPrefs X := by rw [← hR i]; exact ⟨θ i, rfl⟩
  obtain ⟨θ2, hθ2⟩ := exists_type_of_pref (hR i) (topTwo_mem (y := y) (x := x) hr)
  have hcontour : ∀ (θ0 : (j : ι) → Θ j) (z : X) (hsub : lowerContour u i z (θ0 i) ⊆
      lowerContour u i z θ2) (j : ι),
      lowerContour u j z (θ0 j) ⊆ lowerContour u j z (update θ0 i θ2 j) := by
    intro θ0 z hsub j
    by_cases hj : j = i
    · subst hj; rw [update_self]; exact hsub
    · rw [update_of_ne hj]
  have e1 : f (update θ i θ2) = y := by
    have := hM (update θ i θh) (update θ i θ2) (by
      have := hcontour (update θ i θh) y (fun z _ => by
        change u i z θ2 ≤ u i y θ2
        exact (hθ2 y z).2 (topTwo_first hr z))
      simpa [update_idem] using this)
    rw [← hy] at this
    exact this
  have e2 : f (update θ i θ2) = x := by
    refine hM θ (update θ i θ2) (hcontour θ x fun z hz => ?_)
    have hz' : u i z (θ i) ≤ u i x (θ i) := hz
    have hzy : z ≠ y := fun h => by rw [h] at hz'; exact absurd hlt (not_lt.2 hz')
    change u i z θ2 ≤ u i x θ2
    exact (hθ2 x z).2 (topTwo_second hr hxy hzy)
  exact hxy (e2.symm.trans e1)

/-- **Exercise 23.C.6(c)-(d)**, non-vacuity: with two agents, three alternatives and all strict
preferences as types (`𝓡ᵢ = 𝒫`), the rule "agent 0's best alternative" is monotonic and
satisfies IPM. -/
theorem exercise_23_C_6_instance :
    (∀ i, prefSet (rankU (X := Fin 3) (Fin 2)) i = StrictPrefs (Fin 3)) ∧
      MonotonicSCF (rankU (Fin 2)) (dictatorRule (X := Fin 3) (0 : Fin 2)) ∧
      IPM (rankU (Fin 2)) (dictatorRule (X := Fin 3) (0 : Fin 2)) := by
  obtain ⟨hR, -, hSP, -⟩ := proposition_23_C_3_instance
  exact ⟨hR, gs_step_1 (fun i => (hR i).le) hSP, (ipm_iff _ _).2 hSP⟩

/-! ### Exercise 23.C.7: nonnegative responsiveness -/

/-- **Exercise 23.C.7** (MWG, p. 919). The social welfare functional `F` is nonnegatively
responsive: if, going from `p` to `p'`, every agent's ranking of `x` against `y` weakly improves
(`x ≿ᵢ y ⇒ x ≿ᵢ' y` and `x ≻ᵢ y ⇒ x ≻ᵢ' y`), then the social ranking of `x` against `y` does too. -/
def NonnegResponsive {X : Type*} (F : Profile ι X → X → X → Prop) : Prop :=
  ∀ (x y : X) (p p' : Profile ι X), (∀ i, (p i x y → p' i x y) ∧
    (Strict (p i) x y → Strict (p' i) x y)) →
    (F p x y → F p' x y) ∧ (Strict (F p) x y → Strict (F p') x y)

/-- **Exercise 23.C.7** (MWG, p. 919). If `F` is nonnegatively responsive, its social preferences
at the relevant profiles are transitive, and `f(θ)` is the unique `F`-maximal alternative,
`f(θ) = {x : x F(≿₁(θ₁), …, ≿_I(θ_I)) y for all y}`, then `f` is truthfully implementable in
dominant strategies. -/
theorem exercise_23_C_7 [DecidableEq ι] {X : Type*} {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (F : Profile ι X → X → X → Prop) (hNR : NonnegResponsive F)
    (htrans : ∀ θ a b c, F (typeProfile u θ) a b → F (typeProfile u θ) b c →
      F (typeProfile u θ) a c)
    (hmax : ∀ θ, {x | ∀ y, F (typeProfile u θ) x y} = {f θ}) : StrategyProof u f := by
  intro i θ θh
  by_contra hlt
  rw [not_le] at hlt
  have hy : ∀ z, F (typeProfile u (update θ i θh)) (f (update θ i θh)) z := by
    have : f (update θ i θh) ∈ {x | ∀ y, F (typeProfile u (update θ i θh)) x y} := by
      rw [hmax]; rfl
    exact this
  have hx : ∀ z, F (typeProfile u θ) (f θ) z := by
    have : f θ ∈ {x | ∀ y, F (typeProfile u θ) x y} := by rw [hmax]; rfl
    exact this
  have hmove := (hNR (f (update θ i θh)) (f θ) (typeProfile u (update θ i θh)) (typeProfile u θ)
    fun j => by
      by_cases hj : j = i
      · subst hj
        exact ⟨fun _ => hlt.le, fun _ => strict_inducedPref_iff.2 hlt⟩
      · simp only [typeProfile, update_of_ne hj]
        exact ⟨id, id⟩).1 (hy (f θ))
  have hmem : f (update θ i θh) ∈ {x | ∀ y, F (typeProfile u θ) x y} :=
    fun z => htrans θ _ _ _ hmove (hx z)
  rw [hmax] at hmem
  rw [Set.mem_singleton_iff.1 hmem] at hlt
  exact lt_irrefl _ hlt

/-- **Exercise 23.C.7**, non-vacuity: the dictatorial social welfare functional `F(p) = p₀` is
nonnegatively responsive, and with strict-preference types its maximal element is unique and
equals agent 0's best alternative. -/
theorem exercise_23_C_7_instance :
    NonnegResponsive (ι := Fin 2) (X := Fin 3) (fun p => p 0) ∧
      (∀ θ a b c, typeProfile (rankU (X := Fin 3) (Fin 2)) θ 0 a b →
        typeProfile (rankU (Fin 2)) θ 0 b c → typeProfile (rankU (Fin 2)) θ 0 a c) ∧
      ∀ θ, {x | ∀ y, typeProfile (rankU (X := Fin 3) (Fin 2)) θ 0 x y} =
        {dictatorRule (X := Fin 3) (0 : Fin 2) θ} := by
  refine ⟨fun x y p p' h => ⟨(h 0).1, (h 0).2⟩, fun θ a b c h1 h2 => le_trans h2 h1,
    fun θ => ?_⟩
  have hp : typeProfile (rankU (X := Fin 3) (Fin 2)) θ 0 = (θ 0).1 := by
    funext x y
    exact propext (rankUtil_le_iff (θ 0).2.1 x y)
  rw [hp]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, dictatorRule]
  have htop : ∀ y, (θ 0).1 (topOf (θ 0).1) y := fun y =>
    (rankUtil_le_iff (θ 0).2.1 _ _).1 (topOf_spec _ y)
  exact ⟨fun h => (θ 0).2.2 _ _ (h _) (htop x), fun h => h ▸ htop⟩

/-! ### Exercise 23.C.8 -/

/-- **Exercise 23.C.8(a)** (MWG, p. 920). `f` (`b` at `(θ₁', θ₂')`, `a` otherwise) is ex post
efficient: `f(θ)` is a best alternative for both agents at every profile. -/
theorem exercise_23_C_8a : ExPostEfficient (Θ := fun _ : Fin 2 => Bool) c8U c8F := by
  rw [exPostEfficient_iff]
  intro θ x _ i
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  all_goals cases h0 : θ 0 <;> cases h1 : θ 1 <;> fin_cases x <;> norm_num [c8U, c8F, h0, h1]

/-- **Exercise 23.C.8(b)** (MWG, p. 920). `f` satisfies the property (23.C.6) of
Proposition 23.C.2. -/
theorem exercise_23_C_8b : IPM (Θ := fun _ : Fin 2 => Bool) c8U c8F :=
  (ipm_iff _ _).2 exercise_23_BB_2b_strategyProof

/-- The action `a` is weakly dominant for agent `i` of type `θᵢ` in `Γ`: against every profile of
the others' actions it does at least as well as any other action. -/
def WeaklyDominantAction [DecidableEq ι] {X : Type*} {S : ι → Type*}
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (i : ι) (θi : Θ i) (a : S i) : Prop :=
  ∀ (σ : (j : ι) → S j) (a' : S i),
    u i (Γ.outcome (update σ i a')) θi ≤ u i (Γ.outcome (update σ i a)) θi

/-- In the direct mechanism of Exercise 23.C.8 agent 0 announces `θ₀''` whatever his type; agent
1 tells the truth. -/
def c8Untruthful : (i : Fin 2) → Bool → Bool := fun i b => if i = 0 then false else b

/-- **Exercise 23.C.8(c)** (MWG, p. 920). In the direct revelation mechanism for `f`, truth
telling is not each agent's unique weakly dominant strategy: for type `θᵢ'` (`true`) both
announcements are weakly dominant (for type `θᵢ''` only the truth is). If agent 0 uses his
untruthful dominant strategy (always announce `θ₀''`), the strategies are still a dominant
strategy equilibrium, but at `(θ₁', θ₂')` the outcome is `a ≠ b = f(θ₁', θ₂')`: `f` is not
implemented. -/
theorem exercise_23_C_8c :
    (∀ i (a : Bool), WeaklyDominantAction (Θ := fun _ : Fin 2 => Bool) c8U
      (directMechanism c8F) i true a) ∧
    (∀ i (a : Bool), WeaklyDominantAction (Θ := fun _ : Fin 2 => Bool) c8U
      (directMechanism c8F) i false a → a = false) ∧
    IsDominantStrategyEquilibrium (Θ := fun _ : Fin 2 => Bool) c8U (directMechanism c8F)
      c8Untruthful ∧
    (directMechanism c8F).outcome (play (Θ := fun _ : Fin 2 => Bool) c8Untruthful
      fun _ => true) ≠ c8F fun _ => true := by
  refine ⟨fun i a σ a' => ?_, fun i a h => ?_, fun i θi a σ => ?_, by decide⟩
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases a <;> cases a' <;>
      norm_num [c8U, c8F, h0, h1, update_apply, directMechanism]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · by_contra ha
      have := h (fun _ => true) false
      simp only [Bool.not_eq_false] at ha
      subst ha
      norm_num [c8U, c8F, update_apply, directMechanism] at this
    · by_contra ha
      have := h (fun _ => true) false
      simp only [Bool.not_eq_false] at ha
      subst ha
      norm_num [c8U, c8F, update_apply, directMechanism] at this
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases a <;> cases θi <;>
      norm_num [c8U, c8F, h0, h1, update_apply, directMechanism, c8Untruthful]

end MWG.MechanismDesign
