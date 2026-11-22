/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.DSExercises

/-!
# Strong implementation (Appendix A)

MWG, Appendix A, pp. 910-912, and Exercises 23.AA.1-23.AA.2 (pp. 924-925).

* **Definition 23.AA.1**: `Γ` strongly implements `f` if every equilibrium yields `f`.
  **Correction**: as printed the definition has no existence requirement, so it does not imply
  implementation (Definition 23.B.4), contrary to the remark on p. 912 that `f` "can be strongly
  implemented only if it can be implemented in the weaker sense": with no equilibrium at all,
  every `f` is "strongly implemented" (`definition_23_AA_1_literal_counterexample`). We define
  `StronglyImplements` as implementation plus the printed condition, so strong implementation
  implies implementation (`StronglyImplements.implements`) and the necessary conditions for
  dominant strategy implementation remain necessary (`stronglyImplements_strategyProof`).
  Strong implementation of a social choice correspondence (p. 912): `StronglyImplementsSCC`.
* p. 911: if every agent's dominant strategy is strictly dominant, implementation in dominant
  strategies is strong (`strong_of_strictlyDominant`); two weakly dominant strategies give the
  same payoff against all strategies of the others (`weaklyDominant_indifferent`).
  **Correction**: MWG say strict dominance "is always the case ... in any environment in which
  agents' preferences never involve indifference". That is false (two messages with the same
  outcome: `noIndifference_not_strictlyDominant`). What is true: without indifference all
  dominant strategy equilibria yield the same outcomes (`dse_outcome_eq`), so implementation in
  dominant strategies is strong (`strong_of_noIndifference`).
* **Exercise 23.AA.1**: a mechanism with three messages per agent (`θᵢ'`, `θᵢ''` and an extra one)
  implements the social choice function of Exercise 23.C.8 in dominant strategies with unique
  weakly dominant strategies, hence strongly (`exercise_23_AA_1`); its direct mechanism does not
  (`exercise_23_AA_1_direct_not_strong`).
* **Exercise 23.AA.2**: with all valuation functions possible (types are the valuations
  `θᵢ : K → ℝ`), in a Groves mechanism announcing `θᵢ + c` is weakly dominant for every constant
  `c`, so truth telling is not the unique weakly dominant strategy (`exercise_23_AA_2a`); in the
  normalized Groves mechanism (announcements with `vᵢ(k₀) = 0`) the normalized truth is the
  unique weakly dominant strategy when `I ≥ 2` (`exercise_23_AA_2b`).
-/

namespace MWG.MechanismDesign

open Function Finset

variable {ι : Type*} {Θ : ι → Type*} {X : Type*} {S : ι → Type*}

/-! ### Definition 23.AA.1 -/

/-- **Definition 23.AA.1** (MWG, pp. 910-911), as printed: every equilibrium strategy profile `s*`
(in the set `E`) has `g(s*(θ)) = f(θ)` for all `θ`. -/
def EveryEquilibriumYields (E : Set ((i : ι) → Θ i → S i)) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ s ∈ E, ∀ θ, Γ.outcome (play s θ) = f θ

/-- **Definition 23.AA.1** (MWG, p. 910), with the existence clause implicit in MWG's p. 912
remark: `Γ` implements `f` (Definition 23.B.4) and every equilibrium yields `f`. -/
def StronglyImplements (E : Set ((i : ι) → Θ i → S i)) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  Implements E Γ f ∧ EveryEquilibriumYields E Γ f

/-- **Appendix A** (MWG, p. 912). Strong implementation implies implementation. -/
theorem StronglyImplements.implements {E : Set ((i : ι) → Θ i → S i)} {Γ : Mechanism S X}
    {f : ((i : ι) → Θ i) → X} (h : StronglyImplements E Γ f) : Implements E Γ f :=
  h.1

/-- **Appendix A** (MWG, p. 912). The necessary conditions for implementation stay necessary for
strong implementation: a social choice function strongly implementable in dominant strategies is
strategy-proof (so the Gibbard-Satterthwaite theorem applies). -/
theorem stronglyImplements_strategyProof [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X}
    (h : StronglyImplements {s | IsDominantStrategyEquilibrium u Γ s} Γ f) : StrategyProof u f :=
  proposition_23_C_1 h.1

/-- **Definition 23.AA.1** (MWG, pp. 910-912), as printed, does not imply implementation. One agent
with one type, `X = ℕ`, `u(x) = x`, and the mechanism "announce `n`, get `n`": there is no
dominant strategy equilibrium, so every equilibrium "yields" `f ≡ 0`, but no equilibrium
implements it. -/
theorem definition_23_AA_1_literal_counterexample :
    EveryEquilibriumYields {s | IsDominantStrategyEquilibrium (Θ := fun _ : Unit => Unit)
        (fun _ (x : ℕ) _ => (x : ℝ)) (⟨fun σ => σ ()⟩ : Mechanism (fun _ : Unit => ℕ) ℕ) s}
        ⟨fun σ => σ ()⟩ (fun _ => 0) ∧
      ¬Implements {s | IsDominantStrategyEquilibrium (Θ := fun _ : Unit => Unit)
        (fun _ (x : ℕ) _ => (x : ℝ)) (⟨fun σ => σ ()⟩ : Mechanism (fun _ : Unit => ℕ) ℕ) s}
        ⟨fun σ => σ ()⟩ (fun _ => 0) := by
  have none : ∀ s, ¬IsDominantStrategyEquilibrium (Θ := fun _ : Unit => Unit)
      (fun _ (x : ℕ) _ => (x : ℝ)) (⟨fun σ => σ ()⟩ : Mechanism (fun _ : Unit => ℕ) ℕ) s := by
    intro s hs
    have := hs () () (s () () + 1) fun _ => 0
    simp only [update_self, Nat.cast_add, Nat.cast_one] at this
    linarith
  exact ⟨fun s hs => absurd hs (none s), fun ⟨s, hs, _⟩ => none s hs⟩

/-- **Appendix A** (MWG, p. 912). `Γ` strongly implements the social choice correspondence `F`:
every equilibrium `s*` has `g(s*(θ)) ∈ F(θ)` for all `θ`. -/
def StronglyImplementsSCC (E : Set ((i : ι) → Θ i → S i)) (Γ : Mechanism S X)
    (F : ((i : ι) → Θ i) → Set X) : Prop :=
  ∀ s ∈ E, ∀ θ, Γ.outcome (play s θ) ∈ F θ

/-- **Appendix A** (MWG, p. 912). For a single-valued correspondence `F(θ) = {f(θ)}` this is the
printed condition of Definition 23.AA.1. -/
theorem stronglyImplementsSCC_singleton (E : Set ((i : ι) → Θ i → S i)) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) :
    StronglyImplementsSCC E Γ (fun θ => {f θ}) ↔ EveryEquilibriumYields E Γ f :=
  Iff.rfl

/-! ### Dominant strategies (p. 911) -/

/-- The action `a` is strictly dominant for agent `i` of type `θᵢ`: every other action does
strictly worse against every profile of the others' actions. -/
def StrictlyDominantAction [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (i : ι) (θi : Θ i) (a : S i) : Prop :=
  ∀ (σ : (j : ι) → S j) (a' : S i), a' ≠ a →
    u i (Γ.outcome (update σ i a')) θi < u i (Γ.outcome (update σ i a)) θi

/-- In a dominant strategy equilibrium every agent's action is weakly dominant. -/
theorem weaklyDominantAction_of_dse [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {s : (i : ι) → Θ i → S i} (hs : IsDominantStrategyEquilibrium u Γ s)
    (i : ι) (θi : Θ i) : WeaklyDominantAction u Γ i θi (s i θi) :=
  fun σ a' => hs i θi a' σ

/-- **Appendix A** (MWG, p. 911). If `s*` yields `f` and each agent's `sᵢ*(θᵢ)` is strictly
dominant, then `Γ` strongly implements `f` in dominant strategies. -/
theorem strong_of_strictlyDominant [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X} {s : (i : ι) → Θ i → S i}
    (hf : ∀ θ, Γ.outcome (play s θ) = f θ)
    (hstrict : ∀ i θi, StrictlyDominantAction u Γ i θi (s i θi)) :
    StronglyImplements {s | IsDominantStrategyEquilibrium u Γ s} Γ f := by
  have hs : IsDominantStrategyEquilibrium u Γ s := by
    intro i θi a σ
    by_cases ha : a = s i θi
    · rw [ha]
    · exact (hstrict i θi σ a ha).le
  refine ⟨⟨s, hs, hf⟩, fun s' hs' θ => ?_⟩
  have : play s' θ = play s θ := by
    funext i
    by_contra hne
    have h1 := hstrict i (θ i) (play s θ) (s' i (θ i)) hne
    have h2 := hs' i (θ i) (s i (θ i)) (play s θ)
    exact absurd h2 (not_le.2 h1)
  rw [this, hf]

/-- Non-vacuity of `strong_of_strictlyDominant`: one agent, `X = Bool` with `true ≻ false`, and
the mechanism "announce the outcome": announcing `true` is strictly dominant, so `Γ` strongly
implements `f ≡ true`. -/
theorem strong_of_strictlyDominant_instance :
    StronglyImplements {s | IsDominantStrategyEquilibrium (Θ := fun _ : Unit => Unit)
      (fun _ (x : Bool) _ => if x then (1 : ℝ) else 0)
      (⟨fun σ => σ ()⟩ : Mechanism (fun _ : Unit => Bool) Bool) s}
      (⟨fun σ => σ ()⟩ : Mechanism (fun _ : Unit => Bool) Bool) fun _ => true := by
  refine strong_of_strictlyDominant (s := fun _ _ => true) (fun _ => rfl) fun i θi σ a' ha => ?_
  have : a' = false := by simpa using ha
  subst this
  simp

/-- **Appendix A** (MWG, p. 911). Two weakly dominant actions of an agent give him the same
payoff against every profile of the others' actions. -/
theorem weaklyDominant_indifferent [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {i : ι} {θi : Θ i} {a b : S i} (ha : WeaklyDominantAction u Γ i θi a)
    (hb : WeaklyDominantAction u Γ i θi b) (σ : (j : ι) → S j) :
    u i (Γ.outcome (update σ i a)) θi = u i (Γ.outcome (update σ i b)) θi :=
  le_antisymm (hb σ a) (ha σ b)

/-- **Appendix A** (MWG, p. 911), what holds without indifference: if no agent is ever
indifferent between two alternatives, any two dominant strategy equilibria yield the same
outcomes (change the agents' actions one at a time). -/
theorem dse_outcome_eq [Finite ι] [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} (hinj : ∀ i (θi : Θ i), Injective fun x => u i x θi)
    {s s' : (i : ι) → Θ i → S i} (hs : IsDominantStrategyEquilibrium u Γ s)
    (hs' : IsDominantStrategyEquilibrium u Γ s') (θ : (i : ι) → Θ i) :
    Γ.outcome (play s' θ) = Γ.outcome (play s θ) := by
  have := Fintype.ofFinite ι
  have key : ∀ T : Finset ι,
      Γ.outcome (fun j => if j ∈ T then s' j (θ j) else s j (θ j)) = Γ.outcome (play s θ) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rfl
    | insert a T haT ih =>
      set τ : (j : ι) → S j := fun j => if j ∈ T then s' j (θ j) else s j (θ j) with hτ
      have h1 : (fun j => if j ∈ insert a T then s' j (θ j) else s j (θ j)) =
          update τ a (s' a (θ a)) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp
        · simp [hτ, hj]
      have h2 : update τ a (s a (θ a)) = τ := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [hτ, haT]
        · simp [hj]
      rw [h1, ← ih, ← h2, update_idem]
      exact hinj a (θ a) (weaklyDominant_indifferent (weaklyDominantAction_of_dse hs' a (θ a))
        (weaklyDominantAction_of_dse hs a (θ a)) τ)
  have e : (fun j => if j ∈ Finset.univ then s' j (θ j) else s j (θ j)) = play s' θ := by
    funext j; simp [play]
  have := key Finset.univ
  rwa [e] at this

/-- **Appendix A** (MWG, p. 911). Without indifference, implementation in dominant strategies is
strong implementation in dominant strategies. -/
theorem strong_of_noIndifference [Finite ι] [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X}
    (hinj : ∀ i (θi : Θ i), Injective fun x => u i x θi)
    (h : ImplementsInDominantStrategies u Γ f) :
    StronglyImplements {s | IsDominantStrategyEquilibrium u Γ s} Γ f := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨⟨s, hs, hf⟩, fun s' hs' θ => (dse_outcome_eq hinj hs hs' θ).trans (hf θ)⟩

/-- **Appendix A** (MWG, p. 911), correction: preferences without indifference do not make
dominant strategies strictly dominant. One agent with one type, `X = Bool` with `true ≻ false`,
and three messages, `0` and `1` giving `true` and `2` giving `false`: announcing `0` is a dominant
strategy but not strictly dominant (`1` does as well). -/
theorem noIndifference_not_strictlyDominant :
    Injective (fun x : Bool => if x then (1 : ℝ) else 0) ∧
      IsDominantStrategyEquilibrium (Θ := fun _ : Unit => Unit)
        (fun _ (x : Bool) _ => if x then (1 : ℝ) else 0)
        (⟨fun σ => decide (σ () ≠ 2)⟩ : Mechanism (fun _ : Unit => Fin 3) Bool)
        (fun _ _ => 0) ∧
      ¬StrictlyDominantAction (Θ := fun _ : Unit => Unit)
        (fun _ (x : Bool) _ => if x then (1 : ℝ) else 0)
        (⟨fun σ => decide (σ () ≠ 2)⟩ : Mechanism (fun _ : Unit => Fin 3) Bool) () () 0 := by
  refine ⟨fun x y h => ?_, fun i θi a σ => ?_, fun h => ?_⟩
  · revert h
    cases x <;> cases y <;> norm_num
  · fin_cases a <;> simp
  · have := h (fun _ => 0) 1 (by decide)
    simp at this

/-! ### Exercise 23.AA.1 -/

/-- **Exercise 23.AA.1** (MWG, p. 924). The outcome function: messages `0` (`θᵢ'`), `1` (`θᵢ''`)
and `2` (extra). If both report types, the outcome is `f` of Exercise 23.C.8; if exactly one
sends the extra message, the outcome is `c` if the other reported `θⱼ'` and `d` if `θⱼ''`;
if both send it, `e`. -/
def aa1G (m : Fin 2 → Fin 3) : Fin 5 := ![![1, 0, 2], ![0, 0, 3], ![2, 3, 4]] (m 0) (m 1)

/-- **Exercise 23.AA.1** (MWG, p. 924). The mechanism `Γ = (S₁, S₂, g)` with `Sᵢ = {0, 1, 2}`. -/
def aa1Mech : Mechanism (fun _ : Fin 2 => Fin 3) (Fin 5) := ⟨aa1G⟩

/-- **Exercise 23.AA.1**. Truth telling in `aa1Mech`: type `θᵢ'` sends `0`, type `θᵢ''`
sends `1`. -/
def aa1S : (i : Fin 2) → Bool → Fin 3 := fun _ b => if b then 0 else 1

/-- **Exercise 23.AA.1** (MWG, p. 924). `aa1Mech` is not a direct revelation mechanism (its
strategy sets are not the type sets), truth telling is a dominant strategy equilibrium yielding
`f` of Exercise 23.C.8, every agent's weakly dominant strategy is unique, and so `aa1Mech`
strongly implements `f` in dominant strategies. -/
theorem exercise_23_AA_1 :
    IsEmpty (Fin 3 ≃ Bool) ∧
      IsDominantStrategyEquilibrium (Θ := fun _ : Fin 2 => Bool) c8U aa1Mech aa1S ∧
      (∀ θ, aa1Mech.outcome (play (Θ := fun _ : Fin 2 => Bool) aa1S θ) = c8F θ) ∧
      (∀ i θi a, WeaklyDominantAction (Θ := fun _ : Fin 2 => Bool) c8U aa1Mech i θi a →
        a = aa1S i θi) ∧
      StronglyImplements {s | IsDominantStrategyEquilibrium (Θ := fun _ : Fin 2 => Bool) c8U
        aa1Mech s} aa1Mech c8F := by
  have hdse : IsDominantStrategyEquilibrium (Θ := fun _ : Fin 2 => Bool) c8U aa1Mech aa1S := by
    intro i θi a σ
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [aa1Mech, aa1G, update_self, update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      generalize σ 1 = m
      fin_cases a <;> fin_cases m <;> cases θi <;> norm_num [c8U, aa1S]
    · simp only [aa1Mech, aa1G, update_self, update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      generalize σ 0 = m
      fin_cases a <;> fin_cases m <;> cases θi <;> norm_num [c8U, aa1S]
  have hout : ∀ θ, aa1Mech.outcome (play (Θ := fun _ : Fin 2 => Bool) aa1S θ) = c8F θ := by
    intro θ
    simp only [aa1Mech, aa1G, play, aa1S, c8F]
    cases θ 0 <;> cases θ 1 <;> rfl
  have huniq : ∀ i θi a, WeaklyDominantAction (Θ := fun _ : Fin 2 => Bool) c8U aa1Mech i θi a →
      a = aa1S i θi := by
    intro i θi a h
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals
      have h0 := h (fun _ => 0) (if θi then 0 else 1)
      have h2 := h (fun _ => 2) (if θi then 0 else 1)
      revert h0 h2
      fin_cases a <;> cases θi <;> norm_num [aa1Mech, aa1G, aa1S, c8U, update_apply]
  refine ⟨⟨fun e => absurd (Fintype.card_congr e) (by decide)⟩, hdse, hout, huniq,
    ⟨aa1S, hdse, hout⟩, fun s hs θ => ?_⟩
  have : play s θ = play aa1S θ := by
    funext i
    exact huniq i (θ i) _ (weaklyDominantAction_of_dse hs i (θ i))
  rw [this, hout]

/-- **Appendix A** (MWG, p. 912) and **Exercise 23.C.8**: the direct revelation mechanism of
Exercise 23.C.8's `f` does not strongly implement it in dominant strategies (a strong
implementation cannot in general be found among direct mechanisms). -/
theorem exercise_23_AA_1_direct_not_strong :
    ¬StronglyImplements {s | IsDominantStrategyEquilibrium (Θ := fun _ : Fin 2 => Bool) c8U
      (directMechanism c8F) s} (directMechanism c8F) c8F := by
  rintro ⟨-, h⟩
  obtain ⟨-, -, hdse, hne⟩ := exercise_23_C_8c
  exact hne (h _ hdse _)

/-! ### Exercise 23.AA.2: Groves mechanisms with all valuations possible -/

variable {K : Type*}

/-- `∑ⱼ (update w i v)ⱼ(k) = v(k) + ∑_{j≠i} wⱼ(k)`. -/
theorem gr_sum_update [Fintype ι] [DecidableEq ι] (w : ι → K → ℝ) (i : ι) (v : K → ℝ) (k : K) :
    ∑ j, update w i v j k = v k + ∑ j ∈ univ.erase i, w j k := by
  rw [← add_sum_erase _ _ (mem_univ i), update_self]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Exercise 23.AA.2** (MWG, pp. 924-925). The Groves mechanism with announced valuations
`wᵢ : K → ℝ`: the project `k*(w)` and transfers `tᵢ(w) = ∑_{j≠i} wⱼ(k*(w)) + hᵢ(w)`. -/
def grovesMech [Fintype ι] [DecidableEq ι] (kstar : (ι → K → ℝ) → K) (h : ι → (ι → K → ℝ) → ℝ) :
    Mechanism (fun _ : ι => K → ℝ) (K × (ι → ℝ)) :=
  ⟨fun w => (kstar w, fun i => ∑ j ∈ univ.erase i, w j (kstar w) + h i w)⟩

/-- Quasilinear utility with the type equal to the valuation function: `uᵢ((k, t), θᵢ) =
θᵢ(k) + tᵢ` (MWG's `𝒱` rich: every valuation `K → ℝ` is some type). -/
def valU : (i : ι) → K × (ι → ℝ) → (K → ℝ) → ℝ := fun i x θi => θi x.1 + x.2 i

/-- Agent `i`'s payoff in a Groves mechanism, with `hᵢ` independent of `wᵢ`. -/
theorem groves_payoff [Fintype ι] [DecidableEq ι] {kstar : (ι → K → ℝ) → K}
    {h : ι → (ι → K → ℝ) → ℝ} (hh : ∀ i w a, h i (update w i a) = h i w) (i : ι)
    (θi v : K → ℝ) (σ : ι → K → ℝ) :
    valU i ((grovesMech kstar h).outcome (update σ i v)) θi =
      θi (kstar (update σ i v)) + ∑ j ∈ univ.erase i, σ j (kstar (update σ i v)) + h i σ := by
  simp only [valU, grovesMech, hh]
  rw [sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]]
  ring

/-- **Exercise 23.AA.2(a)** (MWG, pp. 924-925). In a Groves mechanism (project rule efficient for
the announcements, `hᵢ` independent of `wᵢ`), announcing `θᵢ + c` is a weakly dominant strategy
for every constant `c` (`c = 0`: truth telling). So truth telling is not the unique weakly
dominant strategy: for `c ≠ 0` the announcement differs from `θᵢ`. -/
theorem exercise_23_AA_2a [Fintype ι] [DecidableEq ι] [Nonempty K] {kstar : (ι → K → ℝ) → K}
    (hk : ∀ (w : ι → K → ℝ) k, ∑ j, w j k ≤ ∑ j, w j (kstar w)) {h : ι → (ι → K → ℝ) → ℝ}
    (hh : ∀ i w a, h i (update w i a) = h i w) (i : ι) (θi : K → ℝ) (c : ℝ) :
    WeaklyDominantAction (Θ := fun _ : ι => K → ℝ) valU (grovesMech kstar h) i θi
        (fun k => θi k + c) ∧
      (c ≠ 0 → (fun k => θi k + c) ≠ θi) := by
  refine ⟨fun σ a => ?_, fun hc he => ?_⟩
  · rw [groves_payoff hh, groves_payoff hh]
    have := hk (update σ i fun k => θi k + c) (kstar (update σ i a))
    rw [gr_sum_update, gr_sum_update] at this
    linarith
  · obtain ⟨k⟩ := ‹Nonempty K›
    have := congrFun he k
    exact hc (by linarith)

/-- An efficient project rule for announced valuations: a maximizer of `∑ⱼ wⱼ(k)`. -/
noncomputable def effChoice [Fintype ι] [Fintype K] [Nonempty K] (w : ι → K → ℝ) : K :=
  (exists_max_image univ (fun k => ∑ j, w j k) univ_nonempty).choose

/-- `effChoice` is efficient. -/
theorem effChoice_spec [Fintype ι] [Fintype K] [Nonempty K] (w : ι → K → ℝ) (k : K) :
    ∑ j, w j k ≤ ∑ j, w j (effChoice w) :=
  (exists_max_image univ (fun k => ∑ j, w j k) univ_nonempty).choose_spec.2 k (mem_univ k)

/-- **Exercise 23.AA.2**, non-vacuity: `effChoice` with `h = 0` is a Groves mechanism. -/
theorem exercise_23_AA_2_instance [Fintype ι] [DecidableEq ι] [Fintype K] [Nonempty K] :
    (∀ (w : ι → K → ℝ) k, ∑ j, w j k ≤ ∑ j, w j (effChoice w)) ∧
      ∀ i (w : ι → K → ℝ) (a : K → ℝ),
        (fun (_ : ι) (_ : ι → K → ℝ) => (0 : ℝ)) i (update w i a) = (fun _ _ => (0 : ℝ)) i w :=
  ⟨fun w k => effChoice_spec w k, fun _ _ _ => rfl⟩

/-- The normalized valuations `{w : K → ℝ | w(k₀) = 0}`. -/
abbrev NormVal (K : Type*) (k0 : K) := {w : K → ℝ // w k0 = 0}

/-- **Exercise 23.AA.2(b)** (MWG, p. 925). The normalized Groves mechanism: each agent announces a
normalized valuation, and `k*` and the Groves transfers are computed from the announcements. -/
def normGrovesMech [Fintype ι] [DecidableEq ι] (k0 : K) (kstar : (ι → K → ℝ) → K)
    (h : ι → (ι → K → ℝ) → ℝ) : Mechanism (fun _ : ι => NormVal K k0) (K × (ι → ℝ)) :=
  ⟨fun w => (grovesMech kstar h).outcome fun j => (w j).1⟩

/-- Truth telling in the normalized Groves mechanism: announce `θᵢ - θᵢ(k₀)`. -/
def normalize (k0 : K) (θi : K → ℝ) : NormVal K k0 := ⟨fun k => θi k - θi k0, sub_self _⟩

/-- The coordinates of an updated profile of normalized announcements. -/
theorem norm_update_coe [DecidableEq ι] {k0 : K} (σ : ι → NormVal K k0) (i : ι)
    (a : NormVal K k0) : (fun j => (update σ i a j).1) = update (fun j => (σ j).1) i a.1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update_of_ne hj]

/-- An efficient project rule picks the strict maximizer. -/
theorem eff_eq_of_strict_max [Fintype ι] {kstar : (ι → K → ℝ) → K}
    (hk : ∀ (w : ι → K → ℝ) k, ∑ j, w j k ≤ ∑ j, w j (kstar w)) (w : ι → K → ℝ) {k1 : K}
    (h1 : ∀ k, k ≠ k1 → ∑ j, w j k < ∑ j, w j k1) : kstar w = k1 := by
  by_contra hne
  exact absurd (hk w k1) (not_le.2 (h1 _ hne))

/-- **Exercise 23.AA.2(b)** (MWG, p. 925). In the normalized Groves mechanism with at least two
agents (and every valuation a possible type), announcing the normalized true valuation is a
weakly dominant strategy and it is the unique one: against a suitable announcement of another
agent, any other normalized announcement gives a strictly lower payoff. -/
theorem exercise_23_AA_2b [Fintype ι] [DecidableEq ι] [Nontrivial ι] (k0 : K)
    {kstar : (ι → K → ℝ) → K} (hk : ∀ (w : ι → K → ℝ) k, ∑ j, w j k ≤ ∑ j, w j (kstar w))
    {h : ι → (ι → K → ℝ) → ℝ} (hh : ∀ i w a, h i (update w i a) = h i w) (i : ι)
    (θi : K → ℝ) :
    WeaklyDominantAction (Θ := fun _ : ι => K → ℝ) valU (normGrovesMech k0 kstar h) i θi
        (normalize k0 θi) ∧
      ∀ a, WeaklyDominantAction (Θ := fun _ : ι => K → ℝ) valU (normGrovesMech k0 kstar h) i θi
        a → a = normalize k0 θi := by
  classical
  have hpay : ∀ (σ : ι → NormVal K k0) (a : NormVal K k0),
      valU i ((normGrovesMech k0 kstar h).outcome (update σ i a)) θi =
        θi (kstar (update (fun j => (σ j).1) i a.1)) +
          ∑ j ∈ univ.erase i, (σ j).1 (kstar (update (fun j => (σ j).1) i a.1)) +
            h i fun j => (σ j).1 := by
    intro σ a
    simp only [normGrovesMech]
    rw [norm_update_coe, groves_payoff hh]
  have hdom : WeaklyDominantAction (Θ := fun _ : ι => K → ℝ) valU (normGrovesMech k0 kstar h) i
      θi (normalize k0 θi) := by
    intro σ a
    rw [hpay, hpay]
    have := hk (update (fun j => (σ j).1) i (normalize k0 θi).1)
      (kstar (update (fun j => (σ j).1) i a.1))
    rw [gr_sum_update, gr_sum_update] at this
    simp only [normalize] at this ⊢
    linarith
  refine ⟨hdom, fun a ha => ?_⟩
  by_contra hne
  obtain ⟨k1, hk1⟩ : ∃ k1, a.1 k1 ≠ (normalize k0 θi).1 k1 := by
    by_contra hall
    push Not at hall
    exact hne (Subtype.ext (funext hall))
  have hk10 : k1 ≠ k0 := fun e => by
    subst e; exact hk1 (by rw [a.2, (normalize k1 θi).2])
  set ν := (normalize k0 θi).1 with hν
  set D := a.1 k1 - ν k1 with hD
  have hDne : D ≠ 0 := sub_ne_zero.2 hk1
  -- the other agent `j`'s announcement
  obtain ⟨j, hji⟩ := exists_ne i
  let W : K → ℝ := fun k => if k = k0 then 0 else if k = k1 then -(ν k1 + a.1 k1) / 2 else
    -(|a.1 k| + |ν k| + 1)
  have hW0 : W k0 = 0 := by simp [W]
  have hW1 : W k1 = -(ν k1 + a.1 k1) / 2 := by simp [W, hk10]
  have hWo : ∀ k, k ≠ k0 → k ≠ k1 → W k = -(|a.1 k| + |ν k| + 1) := by
    intro k h0 h1; simp [W, h0, h1]
  let σ : ι → NormVal K k0 := fun l => if l = j then ⟨W, hW0⟩ else ⟨0, rfl⟩
  have hσ : ∀ k, ∑ l ∈ univ.erase i, (σ l).1 k = W k := by
    intro k
    rw [sum_eq_single j]
    · simp [σ]
    · intro l _ hl; simp [σ, hl]
    · intro hj; exact absurd (mem_erase.2 ⟨hji, mem_univ j⟩) hj
  have htot : ∀ (v : K → ℝ) k, ∑ l, update (fun l => (σ l).1) i v l k = v k + W k := by
    intro v k; rw [gr_sum_update, hσ]
  have hν0 : ν k0 = 0 := (normalize k0 θi).2
  have hθ : ∀ k, θi k = ν k + θi k0 := fun k => by simp [hν, normalize]
  have hle := ha σ (normalize k0 θi)
  rw [hpay, hpay, hσ, hσ] at hle
  rcases lt_or_gt_of_ne hDne with hneg | hpos
  · -- `D < 0`: announcing `a` gives `k₀`, truth gives `k₁`
    have e1 : kstar (update (fun l => (σ l).1) i a.1) = k0 := by
      refine eff_eq_of_strict_max hk _ fun k hk0 => ?_
      rw [htot, htot, a.2, hW0]
      by_cases hk1' : k = k1
      · subst hk1'; rw [hW1]; linarith
      · rw [hWo k hk0 hk1']; linarith [le_abs_self (a.1 k), abs_nonneg (ν k)]
    have e2 : kstar (update (fun l => (σ l).1) i ν) = k1 := by
      refine eff_eq_of_strict_max hk _ fun k hk1' => ?_
      rw [htot, htot, hW1]
      by_cases hk0 : k = k0
      · subst hk0; rw [hν0, hW0]; linarith
      · rw [hWo k hk0 hk1']; linarith [le_abs_self (ν k), abs_nonneg (a.1 k)]
    rw [e1, e2, hθ k1, hW1, hW0] at hle
    linarith
  · -- `D > 0`: announcing `a` gives `k₁`, truth gives `k₀`
    have e1 : kstar (update (fun l => (σ l).1) i a.1) = k1 := by
      refine eff_eq_of_strict_max hk _ fun k hk1' => ?_
      rw [htot, htot, hW1]
      by_cases hk0 : k = k0
      · subst hk0; rw [a.2, hW0]; linarith
      · rw [hWo k hk0 hk1']; linarith [le_abs_self (a.1 k), abs_nonneg (ν k)]
    have e2 : kstar (update (fun l => (σ l).1) i ν) = k0 := by
      refine eff_eq_of_strict_max hk _ fun k hk0 => ?_
      rw [htot, htot, hν0, hW0]
      by_cases hk1' : k = k1
      · subst hk1'; rw [hW1]; linarith
      · rw [hWo k hk0 hk1']; linarith [le_abs_self (ν k), abs_nonneg (a.1 k)]
    rw [e1, e2, hθ k1, hW1, hW0] at hle
    linarith

end MWG.MechanismDesign
