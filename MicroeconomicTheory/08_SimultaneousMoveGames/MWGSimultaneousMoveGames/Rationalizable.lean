/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Existence

/-!
# Rationalizable strategies

MWG, Section 8.C, pp. 242-245, and the remarks on rationalizability in Section 8.D (p. 247).

Strategy sets are sets `T_i ⊆ Δ(S_i)` of mixed strategies. A strategy survives one round if it
is a best response (Definition 8.C.1, over all of `Δ(S_i)`) to some profile of the rivals'
remaining strategies.

* `ratStep`, `ratIter`: removing every strategy that is never a best response, once and `n`
  times; **Definition 8.C.2**: `Rationalizable N i τ` holds when `τ` survives every round.
* `NBRStep`: one step of a deletion process that removes *some* strategies that are never a
  best response to the remaining strategies; `NBRTerminal`: nothing remaining can be removed.
* **Exercise 8.C.2** (`exercise_8_C_2`): every complete deletion process ends at the set of
  rationalizable strategies (`nbrTerminal_eq_rationalizable`), so the order of removal does not
  matter (no finiteness is needed).
* **Section 8.C** (p. 243): the rationalizable strategies are no more than the strategies that
  survive iterated strict dominance: they put no weight on a pure strategy deleted by any
  process of iterated deletion of (pure) strategies that are strictly dominated by mixed
  strategies of the remaining ones (`rationalizable_support_subset`; `MSDStep` generalizes the
  pure process `SDStep` of Section 8.B, `sdStep_msdStep`).
* **Section 8.D** (p. 247): every strategy in a Nash equilibrium is rationalizable
  (`rationalizable_of_isMixedNash`); with Proposition 8.D.2, every player has a rationalizable
  strategy (footnote 3, `footnote_8_3`).
* **Exercise 8.C.1** (`exercise_8_C_1`): if iterated strict dominance leaves a unique profile,
  that profile (played with certainty) is exactly what survives the removal of strategies that
  are never a best response.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- `τ` is a best response to some profile of the rivals' strategies remaining in `T`. -/
def BRToSome (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) (i : I) (τ : S i → ℝ) :
    Prop :=
  ∃ σ : (j : I) → S j → ℝ, IsMixedProfile σ ∧ (∀ j, j ≠ i → σ j ∈ T j) ∧ IsBestResponse N i τ σ

/-- One round of removal of the strategies that are never a best response to the remaining
strategies. -/
def ratStep (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) : (i : I) → Set (S i → ℝ) :=
  fun i => {τ | τ ∈ T i ∧ BRToSome N T i τ}

/-- The strategies surviving `n` rounds, starting from `Δ(S_i)`. -/
def ratIter (N : NormalForm I S) : ℕ → (i : I) → Set (S i → ℝ)
  | 0 => fun i => mixedExtension (S i)
  | n + 1 => ratStep N (ratIter N n)

/-- **Definition 8.C.2** (MWG, p. 243). The rationalizable strategies of player `i` are the
strategies in `Δ(S_i)` that survive the iterated removal of strategies that are never a best
response. -/
def Rationalizable (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ n, τ ∈ ratIter N n i

omit [∀ i, DecidableEq (S i)] in
theorem BRToSome.mono {N : NormalForm I S} {T T' : (i : I) → Set (S i → ℝ)}
    (hTT' : ∀ j, T j ⊆ T' j) {i : I} {τ : S i → ℝ} (h : BRToSome N T i τ) :
    BRToSome N T' i τ := by
  obtain ⟨σ, hσ, hT, hbr⟩ := h
  exact ⟨σ, hσ, fun j hj => hTT' j (hT j hj), hbr⟩

omit [∀ i, DecidableEq (S i)] in
/-- A set of strategies each of which is a best response to the remaining strategies is never
reduced: it lies in every round, hence consists of rationalizable strategies. -/
theorem subset_ratIter_of_bestResponseSet {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (hTΔ : ∀ i, T i ⊆ mixedExtension (S i)) (hT : ∀ i, ∀ τ ∈ T i, BRToSome N T i τ) :
    ∀ n i, T i ⊆ ratIter N n i := by
  intro n
  induction n with
  | zero => exact hTΔ
  | succ n ih => exact fun i τ hτ => ⟨ih i hτ, (hT i τ hτ).mono ih⟩

omit [∀ i, DecidableEq (S i)] in
/-- Strategies in a best-response set are rationalizable. -/
theorem rationalizable_of_bestResponseSet {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (hTΔ : ∀ i, T i ⊆ mixedExtension (S i)) (hT : ∀ i, ∀ τ ∈ T i, BRToSome N T i τ) {i : I}
    {τ : S i → ℝ} (hτ : τ ∈ T i) : Rationalizable N i τ :=
  fun n => subset_ratIter_of_bestResponseSet hTΔ hT n i hτ

omit [∀ i, DecidableEq (S i)] in
/-- Rationalizable strategies are mixed strategies. -/
theorem Rationalizable.isMixedStrategy {N : NormalForm I S} {i : I} {τ : S i → ℝ}
    (h : Rationalizable N i τ) : IsMixedStrategy τ :=
  h 0

/-- A deletion step: `T'` keeps part of each `T_i`, and every removed strategy is never a best
response to the strategies remaining in `T`. -/
def NBRStep (N : NormalForm I S) (T T' : (i : I) → Set (S i → ℝ)) : Prop :=
  (∀ i, T' i ⊆ T i) ∧ ∀ i, ∀ τ ∈ T i, τ ∉ T' i → ¬ BRToSome N T i τ

/-- A deletion process is complete when every remaining strategy is a best response to some
remaining strategies. -/
def NBRTerminal (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) : Prop :=
  ∀ i, ∀ τ ∈ T i, BRToSome N T i τ

omit [∀ i, DecidableEq (S i)] in
/-- Along any deletion process from `Δ`, some round of the maximal process lies inside the
current sets. -/
theorem exists_ratIter_subset_of_chain {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T) :
    ∃ n, ∀ i, ratIter N n i ⊆ T i := by
  induction h with
  | refl => exact ⟨0, fun _ => le_rfl⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ => ?_⟩
    by_contra hτQ
    exact hstep.2 i τ (hn i hτ.1) hτQ (hτ.2.mono hn)

omit [∀ i, DecidableEq (S i)] in
/-- Deletion processes stay inside `Δ`. -/
theorem nbrChain_subset {N : NormalForm I S} {P T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) P T) (i : I) : T i ⊆ P i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (hstep.1 i).trans ih

omit [∀ i, DecidableEq (S i)] in
/-- Every complete deletion process of strategies that are never a best response ends at the set
of rationalizable strategies. -/
theorem nbrTerminal_eq_rationalizable {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T)
    (ht : NBRTerminal N T) (i : I) : T i = {τ | Rationalizable N i τ} := by
  ext τ
  constructor
  · exact fun hτ => rationalizable_of_bestResponseSet (nbrChain_subset h) ht hτ
  · intro hτ
    obtain ⟨n, hn⟩ := exists_ratIter_subset_of_chain h
    exact hn i (hτ n)

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.C.2** (MWG, p. 262). The order of removal does not matter for the set of
strategies that survives a process of iterated deletion of strategies that are never a best
response. -/
theorem exercise_8_C_2 {N : NormalForm I S} {T₁ T₂ : (i : I) → Set (S i → ℝ)}
    (h₁ : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T₁)
    (ht₁ : NBRTerminal N T₁)
    (h₂ : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T₂)
    (ht₂ : NBRTerminal N T₂) : T₁ = T₂ :=
  funext fun i => (nbrTerminal_eq_rationalizable h₁ ht₁ i).trans
    (nbrTerminal_eq_rationalizable h₂ ht₂ i).symm

omit [∀ i, DecidableEq (S i)] in
/-- The maximal process (removing every strategy that is never a best response at each round)
is a deletion process. -/
theorem nbrStep_ratStep (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) :
    NBRStep N T (ratStep N T) :=
  ⟨fun _ _ hτ => hτ.1, fun _ _ hτ hτ' hbr => hτ' ⟨hτ, hbr⟩⟩

/-! ### Rationalizability and iterated strict dominance -/

/-- One step of iterated deletion of strictly dominated pure strategies when randomization is
allowed (Section 8.B, p. 242: the test of Proposition 8.B.1 "applied at each stage using the
remaining set of pure strategies"): every removed pure strategy `a ∈ P_i` is strictly worse,
against every remaining rival profile, than some mixed strategy over `P_i`. -/
def MSDStep (N : NormalForm I S) (P Q : (i : I) → Set (S i)) : Prop :=
  (∀ i, Q i ⊆ P i) ∧ ∀ i, ∀ a ∈ P i, a ∉ Q i → ∃ τ' : S i → ℝ, IsMixedStrategy τ' ∧
    (∀ b, 0 < τ' b → b ∈ P i) ∧ ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ P j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i

/-- A step of the pure process of Section 8.B is a step of the mixed one. -/
theorem sdStep_msdStep {N : NormalForm I S} {P Q : (i : I) → Set (S i)}
    (h : SDStep N P Q) : MSDStep N P Q := by
  refine ⟨h.1, fun i a ha haQ => ?_⟩
  obtain ⟨a', ha', hdom⟩ := h.2 i a ha haQ
  refine ⟨pureMixed a', isMixedStrategy_pureMixed a', fun b hb => ?_, fun r hr => ?_⟩
  · have : b = a' := by
      by_contra hne
      simp [pureMixed, hne] at hb
    rwa [this]
  · rw [mixedPayoff_pureProfile_update]
    exact hdom r hr

/-- Against a mixed profile whose rivals only play remaining pure strategies, a pure strategy
deleted in an `MSDStep` does strictly worse than its dominator. -/
theorem msd_dominated_lt {N : NormalForm I S} {P : (i : I) → Set (S i)} {i : I} {a : S i}
    {τ' : S i → ℝ}
    (hdom : ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ P j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i)
    {σ : (j : I) → S j → ℝ} (hσ : IsMixedProfile σ)
    (hsupp : ∀ j, j ≠ i → ∀ b, 0 < σ j b → b ∈ P j) :
    N.mixedPayoff (update σ i (pureMixed a)) i < N.mixedPayoff (update σ i τ') i := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  have hw : ∀ s : (i : I) → S i, 0 ≤ ∏ j, σ j (s j) :=
    prod_mixed_nonneg fun j a => (hσ j).1 a
  have hsum := sum_prod_mixed_eq_one (fun j => (hσ j).2)
  obtain ⟨s₀, -, hs₀⟩ : ∃ s ∈ (univ : Finset ((i : I) → S i)), 0 < ∏ j, σ j (s j) := by
    by_contra hno
    push Not at hno
    have : ∑ s : (i : I) → S i, ∏ j, σ j (s j) ≤ 0 := Finset.sum_nonpos hno
    linarith
  have hlt : ∀ s, 0 < ∏ j, σ j (s j) →
      N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
    intro s hs
    rw [mixedPayoff_pureProfile_update]
    refine hdom s fun j hj => hsupp j hj (s j) ?_
    have hne : ∏ j, σ j (s j) ≠ 0 := hs.ne'
    rw [Finset.prod_ne_zero_iff] at hne
    exact ((hσ j).1 _).lt_of_ne (hne j (mem_univ j)).symm
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left
    (hlt s₀ hs₀) hs₀⟩
  rcases (hw s).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hlt s hpos).le (hw s)

/-- **Section 8.C** (MWG, p. 243). The set of rationalizable strategies is no larger than the set
surviving iterated removal of strictly dominated strategies: along any deletion process of
strictly dominated pure strategies (dominated by mixtures of remaining ones), some round of the
removal of never-best responses only keeps strategies supported on the remaining pure
strategies. -/
theorem exists_ratIter_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) :
    ∃ n, ∀ i, ∀ τ ∈ ratIter N n i, ∀ a, 0 < τ a → a ∈ Q i := by
  induction h with
  | refl => exact ⟨0, fun _ _ _ _ _ => Set.mem_univ _⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ a ha => ?_⟩
    have haP : a ∈ P i := hn i τ hτ.1 a ha
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 i a haP haQ
    obtain ⟨σ, hσ, hσT, hbr⟩ := hτ.2
    have hlt := msd_dominated_lt hdom hσ fun j hj b hb => hn j (σ j) (hσT j hj) b hb
    have hsupp := (isBestResponse_iff_support N i hbr.1 σ).1 hbr a ha
    have h1 := mixedPayoff_le_of_pure_le N σ i hτ' i hsupp
    linarith

/-- **Section 8.C** (MWG, p. 243). A rationalizable strategy puts no weight on any pure strategy
removed by iterated strict dominance. -/
theorem rationalizable_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) {i : I} {τ : S i → ℝ}
    (hτ : Rationalizable N i τ) {a : S i} (ha : 0 < τ a) : a ∈ Q i := by
  obtain ⟨n, hn⟩ := exists_ratIter_support_subset h
  exact hn i τ (hτ n) a ha

/-- A process of the pure deletion of Section 8.B is a process of the mixed one. -/
theorem msdChain_of_sdChain {N : NormalForm I S} {P Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (SDStep N) P Q) : Relation.ReflTransGen (MSDStep N) P Q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (sdStep_msdStep hs)

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.D** (MWG, p. 247). Every strategy that is part of a Nash equilibrium profile is
rationalizable. -/
theorem rationalizable_of_isMixedNash {N : NormalForm I S} {σ : (i : I) → S i → ℝ}
    (h : IsMixedNash N σ) (i : I) : Rationalizable N i (σ i) := by
  have hbr := (isMixedNash_iff_bestResponse N σ).1 h
  refine rationalizable_of_bestResponseSet (T := fun j => {σ j})
    (fun j τ hτ => by rw [Set.mem_singleton_iff.1 hτ]; exact h.1 j)
    (fun j τ hτ => ?_) (Set.mem_singleton _)
  rw [Set.mem_singleton_iff.1 hτ]
  exact ⟨σ, h.1, fun k _ => Set.mem_singleton _, hbr.2 j⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 3** (MWG, p. 245). A player always has a rationalizable strategy when a Nash
equilibrium exists, in particular in every finite game (Proposition 8.D.2). -/
theorem footnote_8_3 [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I) :
    ∃ τ, Rationalizable N i τ := by
  obtain ⟨σ, hσ⟩ := proposition_8_D_2 N
  exact ⟨σ i, rationalizable_of_isMixedNash hσ i⟩

/-- **Exercise 8.C.1** (MWG, p. 262). If iterated elimination of strictly dominated strategies
yields a unique prediction `s`, the same prediction results from eliminating strategies that are
never a best response: the rationalizable strategies of player `i` are exactly `s_i` played with
certainty. -/
theorem exercise_8_C_1 [∀ i, Nonempty (S i)] {N : NormalForm I S}
    {T : (i : I) → Set (S i)} (hT : Relation.ReflTransGen (SDStep N) (fullSets S) T)
    {s : (i : I) → S i} (hs : ∀ i, T i = {s i}) (i : I) (τ : S i → ℝ) :
    Rationalizable N i τ ↔ τ = pureMixed (s i) := by
  constructor
  · intro hτ
    have hsupp : ∀ a, 0 < τ a → a = s i := fun a ha => by
      have := rationalizable_support_subset (msdChain_of_sdChain hT) hτ ha
      rwa [hs i, Set.mem_singleton_iff] at this
    have hmix := hτ.isMixedStrategy
    have hzero : ∀ a, a ≠ s i → τ a = 0 := fun a ha =>
      le_antisymm (not_lt.1 fun h => ha (hsupp a h)) (hmix.1 a)
    have hone : τ (s i) = 1 := by
      rw [← hmix.2, Finset.sum_eq_single (s i) (fun b _ hb => hzero b hb)
        (fun h => absurd (mem_univ _) h)]
    funext a
    by_cases ha : a = s i
    · subst ha; simp [pureMixed, hone]
    · simp [pureMixed, ha, hzero a ha]
  · rintro rfl
    have hne : IsNashEquilibrium N s := exercise_8_D_2 hT hs
    exact rationalizable_of_isMixedNash ((corollary_8_D_1 N s).1 hne) i

end MWG.SimultaneousMoveGames
