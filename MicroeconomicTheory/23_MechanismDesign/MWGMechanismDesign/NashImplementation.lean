/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.GSCorollaries
import MWGMechanismDesign.Quasilinear

/-!
# Implementation in Nash equilibrium (complete information)

MWG, Appendix B of Chapter 23, pp. 912-915, with Exercises 23.BB.2 and 23.BB.3 (p. 925).

With complete information every agent observes the whole profile `θ`, and the game induced by a
mechanism `Γ` at `θ` is a game of complete information. We formalize:

* Nash equilibrium of the game induced by `Γ` at `θ` (`IsNashAt`) and Definition 23.BB.1
  (`ImplementsInNash`, `StronglyImplementsInNash`).
* p. 913 and footnote 59: a dominant strategy equilibrium gives a Nash equilibrium at every
  profile, so dominant strategy implementation implies Nash implementation
  (`dominant_implementsInNash`, which is also Exercise 23.BB.2, first question).
* pp. 913-914: with `I ≥ 3` every social choice function is implemented in Nash equilibrium by
  the mechanism "announce a profile; if at least `I - 1` agents agree on `θ̂`, choose `f(θ̂)`,
  else `x₀`" (`agreementMech`, `nash_any_implementable`), and every `x ∈ f(Θ)` is a Nash
  equilibrium outcome at every profile (`nash_agreement_every_value`).
* Proposition 23.BB.1 (Maskin): strong Nash implementation implies monotonicity.
* Proposition 23.BB.2: under `𝓡ᵢ = 𝒫` with at least three alternatives and `f` onto, strong
  Nash implementability is equivalent to dictatorship.
* No veto power and Proposition 23.BB.3 (Maskin; MWG omit the proof): with `I ≥ 3`, monotonicity
  and no veto power imply strong Nash implementation. We prove the stronger statement for social
  choice correspondences (full implementation, p. 915) with Maskin's integer mechanism
  (`maskinMech`, `maskin_fullyImplements`), and deduce Proposition 23.BB.3.
* p. 915: no veto power holds when no two agents share a best alternative, in particular with a
  transferable private good; there monotonicity is necessary and sufficient. Monotonic social
  choice correspondences; full implementation; the Pareto correspondence.
* Exercise 23.BB.2 (second question) and Exercise 23.BB.3.

## Departures and corrections

1. **Definition 23.BB.1, strong implementation.** As printed, "`Γ` strongly implements `f` if
   for each `θ` every Nash equilibrium results in `f(θ)`" does not require that a Nash
   equilibrium exists. Read literally, Proposition 23.BB.1 is false: a mechanism with no Nash
   equilibrium "strongly implements" every `f`, including non-monotonic ones
   (`definition_23_BB_1_literal_counterexample`). The proof of Proposition 23.BB.1 uses the
   existence of an equilibrium with outcome `f(θ)` (strong implementation includes
   implementation, as in Appendix A); `StronglyImplementsInNash` includes it.
2. **Proposition 23.BB.2** assumes `X` finite; this is not needed (as for Proposition 23.C.3).
3. **p. 915, Pareto correspondence.** "If `f(θ)` is the Pareto set for all `θ`, then `f` is
   monotonic" is false in general (`paretoSet_not_monotonic`: two agents, one becomes
   indifferent). It holds for the weak Pareto set (`weakParetoSet_monotonic`) and, with a
   transferable good (quasilinear utilities), for the Pareto set
   (`paretoSet_ql_monotonic`), which is the setting of MWG's conclusion
   (`nash_ql_pareto_fullyImplements`).
4. **Exercise 23.BB.2.** Dominant strategy implementability implies Nash implementability, but
   not strong Nash implementability: the social choice function of Exercise 23.C.8 is
   strategy-proof but not monotonic (`exercise_23_BB_2b_not_monotonic`).
5. **Exercise 23.BB.3.** With `I ≥ 3` every social choice function is Nash implementable, so
   neither Groves property is necessary (`exercise_23_BB_3_weak_not_I`,
   `exercise_23_BB_3_weak_not_II`). For strong implementation, monotonicity forces the whole
   outcome to be constant on `{k = 1}` and on `{k = 0}`, so property (i) must hold
   (`exercise_23_BB_3_strong_I`) and property (ii) can never hold
   (`exercise_23_BB_3_strong_not_II`); strongly implementable functions with an efficient
   project choice exist (`exercise_23_BB_3_strong_exists`).
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {ι : Type*} {Θ : ι → Type*} {X : Type*} {S : ι → Type*}

/-! ### Nash equilibrium and Definition 23.BB.1 -/

/-- **Appendix B** (MWG, p. 913). With complete information, `σ` is a Nash equilibrium of the game
induced by `Γ` when the profile is `θ`: no agent `i` gains by a unilateral deviation `a ∈ Sᵢ`,
`uᵢ(g(a, σ₋ᵢ), θᵢ) ≤ uᵢ(g(σ), θᵢ)`. -/
def IsNashAt [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (θ : (i : ι) → Θ i) (σ : (i : ι) → S i) : Prop :=
  ∀ i (a : S i), u i (Γ.outcome (update σ i a)) (θ i) ≤ u i (Γ.outcome σ) (θ i)

/-- **Definition 23.BB.1** (MWG, p. 913). `Γ` implements `f` in Nash equilibrium: for each `θ`
there is a Nash equilibrium of the game induced by `Γ` at `θ` with outcome `f(θ)`. -/
def ImplementsInNash [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ θ, ∃ σ, IsNashAt u Γ θ σ ∧ Γ.outcome σ = f θ

/-- **Definition 23.BB.1** (MWG, p. 913), in MWG's form: there is a strategy profile
`s*(θ) = (s₁*(θ), …, s_I*(θ))` that is a Nash equilibrium at every `θ`, with `g(s*(θ)) = f(θ)`. -/
theorem implementsInNash_iff [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) :
    ImplementsInNash u Γ f ↔
      ∃ s : ((i : ι) → Θ i) → (i : ι) → S i, ∀ θ, IsNashAt u Γ θ (s θ) ∧ Γ.outcome (s θ) = f θ :=
  ⟨fun h => ⟨fun θ => (h θ).choose, fun θ => (h θ).choose_spec⟩,
    fun ⟨s, hs⟩ θ => ⟨s θ, hs θ⟩⟩

/-- **Definition 23.BB.1** (MWG, p. 913). `Γ` strongly implements `f` in Nash equilibrium: for
each `θ` a Nash equilibrium exists and every Nash equilibrium results in `f(θ)`. (The existence
clause is implicit in MWG; see `definition_23_BB_1_literal_counterexample`.) -/
def StronglyImplementsInNash [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ θ, (∃ σ, IsNashAt u Γ θ σ) ∧ ∀ σ, IsNashAt u Γ θ σ → Γ.outcome σ = f θ

/-- **Definition 23.BB.1** (MWG, p. 913), as printed: every Nash equilibrium at `θ` results in
`f(θ)` (no existence requirement). -/
def EveryNashYields [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ θ σ, IsNashAt u Γ θ σ → Γ.outcome σ = f θ

/-- **Definition 23.BB.1** (MWG, p. 913). Strong implementation is implementation together with
the printed condition "every Nash equilibrium results in `f(θ)`". -/
theorem stronglyImplementsInNash_iff [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (f : ((i : ι) → Θ i) → X) :
    StronglyImplementsInNash u Γ f ↔ ImplementsInNash u Γ f ∧ EveryNashYields u Γ f := by
  constructor
  · intro h
    exact ⟨fun θ => let ⟨σ, hσ⟩ := (h θ).1; ⟨σ, hσ, (h θ).2 σ hσ⟩, fun θ => (h θ).2⟩
  · rintro ⟨h1, h2⟩ θ
    obtain ⟨σ, hσ, -⟩ := h1 θ
    exact ⟨⟨σ, hσ⟩, h2 θ⟩

/-- **Definition 23.BB.1** (MWG, p. 913), as printed, is too weak for Proposition 23.BB.1. One
agent with two types and utility `u(x, θ) = x` on `X = ℕ`, and the mechanism "announce a number
`n`, get `n`": no Nash equilibrium exists, so every Nash equilibrium "results in" the
non-monotonic `f(true) = 0`, `f(false) = 1`. -/
theorem definition_23_BB_1_literal_counterexample :
    EveryNashYields (S := fun _ : Unit => ℕ) (fun _ (x : ℕ) (_ : Bool) => (x : ℝ))
        ⟨fun σ => σ ()⟩ (fun θ => if θ () then 0 else 1) ∧
      ¬MonotonicSCF (Θ := fun _ : Unit => Bool) (fun _ (x : ℕ) (_ : Bool) => (x : ℝ))
        (fun θ => if θ () then 0 else 1) := by
  refine ⟨fun θ σ hσ => ?_, fun hM => ?_⟩
  · exfalso
    have h := hσ () (σ () + 1)
    simp only [update_self] at h
    push_cast at h
    linarith
  · have h := hM (fun _ => true) (fun _ => false) (fun _ _ hz => hz)
    simp at h

/-! ### Dominant strategies and complete information (p. 913, footnote 59) -/

/-- **Appendix B** (MWG, p. 913, footnote 59) and **Exercise 23.BB.2** (MWG, p. 925, first
question). A dominant strategy equilibrium `s*(·)` gives, at every profile `θ`, the Nash
equilibrium `s*(θ) = (s₁*(θ₁), …, s_I*(θ_I))`; so if `Γ` implements `f` in dominant strategies,
it implements `f` in Nash equilibrium. -/
theorem dominant_implementsInNash [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X} (h : ImplementsInDominantStrategies u Γ f) :
    ImplementsInNash u Γ f := by
  obtain ⟨s, hs, hf⟩ := h
  intro θ
  refine ⟨play s θ, fun i a => ?_, hf θ⟩
  have h1 := hs i (θ i) a (play s θ)
  have e : update (play s θ) i (s i (θ i)) = play s θ := update_eq_self i (play s θ)
  rwa [e] at h1

/-! ### Any social choice function is Nash implementable when `I ≥ 3` (pp. 913-914) -/

/-- **Appendix B** (MWG, p. 913). With at least three agents, any two agents leave a third. -/
theorem nash_exists_third [Fintype ι] (h3 : 3 ≤ Fintype.card ι) (a b : ι) :
    ∃ k, k ≠ a ∧ k ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset ι) ⊆ {a, b} := by
    intro k _
    by_cases hk : k = a
    · simp [hk]
    · simp [h k hk]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le a ({b} : Finset ι)
  rw [Finset.card_univ] at h1
  rw [Finset.card_singleton] at h2
  omega

/-- **Appendix B** (MWG, pp. 913, 915). "At least `I - 1` agents satisfy `P`" is "all agents
except possibly one agent `j` satisfy `P`". -/
theorem nash_allBut_iff_card [Fintype ι] [Nonempty ι] (P : ι → Prop) [DecidablePred P] :
    (∃ j, ∀ i, i ≠ j → P i) ↔ Fintype.card ι - 1 ≤ (Finset.univ.filter P).card := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [Finset.card_univ] at hsum
  constructor
  · rintro ⟨j, hj⟩
    have hsub : Finset.univ.filter (fun i => ¬P i) ⊆ {j} := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_singleton]
      by_contra hij
      exact hi (hj i hij)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h1
    omega
  · intro h
    have hle : (Finset.univ.filter (fun i => ¬P i)).card ≤ 1 := by omega
    rw [Finset.card_le_one] at hle
    by_cases hne : ∃ j, ¬P j
    · obtain ⟨j, hj⟩ := hne
      refine ⟨j, fun i hij => ?_⟩
      by_contra hi
      exact hij (hle i (by simp [hi]) j (by simp [hj]))
    · push Not at hne
      obtain ⟨j⟩ := ‹Nonempty ι›
      exact ⟨j, fun i _ => hne i⟩

open Classical in
/-- **Appendix B** (MWG, pp. 913-914). The mechanism in which every agent announces a profile of
types; if at least `I - 1` agents announce the same profile `θ̂` (all except possibly one agent
`j`), the outcome is `f(θ̂)`, otherwise it is a fixed `x₀`. -/
noncomputable def agreementMech (f : ((i : ι) → Θ i) → X) (x0 : X) :
    Mechanism (fun _ : ι => (i : ι) → Θ i) X :=
  ⟨fun σ => if h : ∃ θh : (i : ι) → Θ i, ∃ j, ∀ i, i ≠ j → σ i = θh then f h.choose else x0⟩

/-- **Appendix B** (MWG, p. 913). With `I ≥ 3` the agreement mechanism is well defined: the
profile announced by at least `I - 1` agents is unique, and the outcome is `f` of it. -/
theorem agreementMech_outcome [Fintype ι] (h3 : 3 ≤ Fintype.card ι) (f : ((i : ι) → Θ i) → X)
    (x0 : X) {σ : ι → (i : ι) → Θ i} {θh : (i : ι) → Θ i} {j : ι}
    (h : ∀ i, i ≠ j → σ i = θh) : (agreementMech f x0).outcome σ = f θh := by
  simp only [agreementMech]
  split_ifs with h'
  · obtain ⟨j', hj'⟩ := h'.choose_spec
    obtain ⟨k, hk1, hk2⟩ := nash_exists_third h3 j j'
    rw [← h k hk1, hj' k hk2]
  · exact absurd ⟨θh, j, h⟩ h'

/-- **Appendix B** (MWG, p. 914). With `I ≥ 3`, at any profile `θ` all agents announcing the same
profile `θ'` is a Nash equilibrium of the agreement mechanism, with outcome `f(θ')`: no agent can
change the outcome by deviating unilaterally. -/
theorem nash_agreement_isNash [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) (x0 : X) (θ θ' : (i : ι) → Θ i) :
    IsNashAt u (agreementMech f x0) θ (fun _ => θ') ∧
      (agreementMech f x0).outcome (fun _ => θ') = f θ' := by
  obtain ⟨j⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  refine ⟨fun i a => ?_, agreementMech_outcome h3 f x0 (j := j) fun _ _ => rfl⟩
  rw [agreementMech_outcome h3 f x0 (θh := θ') (j := i) fun k hk => by simp [hk],
    agreementMech_outcome h3 f x0 (θh := θ') (j := i) fun _ _ => rfl]

/-- **Appendix B** (MWG, pp. 913-914). With `I ≥ 3` any social choice function is implemented in
Nash equilibrium (by the agreement mechanism; at `θ` everyone announces `θ`). -/
theorem nash_any_implementable [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) (x0 : X) :
    ImplementsInNash u (agreementMech f x0) f :=
  fun θ => ⟨fun _ => θ, nash_agreement_isNash h3 u f x0 θ θ⟩

/-- **Appendix B** (MWG, p. 914). With the agreement mechanism, at every profile `θ` and for every
`x ∈ f(Θ)` there is a Nash equilibrium resulting in `x`. -/
theorem nash_agreement_every_value [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) (x0 : X) (θ : (i : ι) → Θ i)
    {x : X} (hx : x ∈ Set.range f) :
    ∃ σ, IsNashAt u (agreementMech f x0) θ σ ∧ (agreementMech f x0).outcome σ = x := by
  obtain ⟨θ', rfl⟩ := hx
  exact ⟨fun _ => θ', nash_agreement_isNash h3 u f x0 θ θ'⟩

/-! ### Propositions 23.BB.1 and 23.BB.2 -/

/-- **Proposition 23.BB.1** (Maskin; MWG, p. 914). If `f` can be strongly implemented in Nash
equilibrium, then `f` is monotonic: a Nash equilibrium `σ` at `θ` with outcome `f(θ)` remains a
Nash equilibrium at `θ'` when every `Lᵢ(f(θ), θᵢ) ⊆ Lᵢ(f(θ), θᵢ')`. -/
theorem proposition_23_BB_1 [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X}
    {f : ((i : ι) → Θ i) → X} (h : StronglyImplementsInNash u Γ f) : MonotonicSCF u f := by
  intro θ θ' hL
  obtain ⟨⟨σ, hσ⟩, hall⟩ := h θ
  have hfθ : Γ.outcome σ = f θ := hall σ hσ
  have hσ' : IsNashAt u Γ θ' σ := by
    intro i a
    have h1 : Γ.outcome (update σ i a) ∈ lowerContour u i (f θ) (θ i) := by
      have h2 := hσ i a
      rw [hfθ] at h2
      exact h2
    have h2 := hL i h1
    rw [hfθ]
    exact h2
  exact ((h θ').2 σ hσ').symm.trans hfθ

/-- **Proposition 23.BB.2** (MWG, p. 914), the mechanism of the proof: the dictator `h` chooses an
alternative from `X` (every agent's strategy set is `X`; only `h`'s choice matters). -/
def dictatorMech (h : ι) : Mechanism (fun _ : ι => X) X := ⟨fun σ => σ h⟩

/-- **Proposition 23.BB.2** (MWG, p. 914), sufficiency. If `f(θ)` is always a best alternative for
agent `h` and `𝓡ᵢ ⊆ 𝒫`, letting `h` choose from `X` strongly implements `f` in Nash
equilibrium: in every Nash equilibrium `h` chooses his unique best alternative. -/
theorem dictatorMech_strongly [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i ⊆ StrictPrefs X) {h : ι}
    (hh : ∀ θ y, u h y (θ h) ≤ u h (f θ) (θ h)) :
    StronglyImplementsInNash u (dictatorMech h) f := by
  intro θ
  refine ⟨⟨fun _ => f θ, fun i a => ?_⟩, fun σ hσ => ?_⟩
  · by_cases hi : i = h
    · subst hi
      simp only [dictatorMech, update_self]
      exact hh θ a
    · simp [dictatorMech, update_of_ne (Ne.symm hi)]
  · have h1 := hσ h (f θ)
    simp only [dictatorMech, update_self] at h1
    exact eq_of_utility_eq (hR h) (θ h) (le_antisymm (hh θ _) h1)

/-- **Proposition 23.BB.2** (MWG, p. 914), necessity, for any mechanism. With finitely many
agents, at least three alternatives, `𝓡ᵢ = 𝒫` and `f(Θ) = X`, a strongly Nash implementable
`f` is dictatorial (Proposition 23.BB.1 and Steps 2-3 of the proof of Proposition 23.C.3). -/
theorem proposition_23_BB_2_necessity [Finite ι] [Nonempty ι] [DecidableEq ι]
    (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i = StrictPrefs X) (hon : Surjective f)
    {Γ : Mechanism S X} (h : StronglyImplementsInNash u Γ f) : Dictatorial u f := by
  have hM := proposition_23_BB_1 h
  exact gs_step_3 hX hR hM (gs_step_2 hR hM hon)

/-- **Proposition 23.BB.2** (MWG, p. 914). Suppose there are finitely many agents, `X` has at
least three elements, `𝓡ᵢ = 𝒫` for all `i` and `f(Θ) = X`. Then `f` is strongly implementable
in Nash equilibrium iff it is dictatorial. (MWG also assume `X` finite; that is not needed.) -/
theorem proposition_23_BB_2 [Finite ι] [Nonempty ι] [DecidableEq ι]
    (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i = StrictPrefs X) (hon : Surjective f) :
    (∃ Γ : Mechanism (fun _ : ι => X) X, StronglyImplementsInNash u Γ f) ↔ Dictatorial u f := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    exact proposition_23_BB_2_necessity hX hR hon hΓ
  · rintro ⟨h, hh⟩
    exact ⟨dictatorMech h, dictatorMech_strongly (fun i => (hR i).le) hh⟩

/-- **Proposition 23.BB.2**, non-vacuity (MWG, p. 914). Three alternatives, two agents whose types
are all strict preferences (`𝓡ᵢ = 𝒫`): the onto rule "agent 0's best alternative" is strongly
implemented in Nash equilibrium by letting agent 0 choose. -/
theorem proposition_23_BB_2_instance :
    (∀ i, prefSet (rankU (X := Fin 3) (Fin 2)) i = StrictPrefs (Fin 3)) ∧
      Surjective (dictatorRule (X := Fin 3) (0 : Fin 2)) ∧
      StronglyImplementsInNash (rankU (Fin 2)) (dictatorMech (0 : Fin 2))
        (dictatorRule (X := Fin 3) (0 : Fin 2)) := by
  obtain ⟨hR, hon, -, -⟩ := proposition_23_C_3_instance
  exact ⟨hR, hon, dictatorMech_strongly (fun i => (hR i).le) fun θ y => topOf_spec (θ 0).1 y⟩

/-! ### No veto power, correspondences and Proposition 23.BB.3 -/

/-- **Appendix B** (MWG, p. 915). `f` satisfies no veto power: if `I - 1` agents (all agents except
possibly one agent `j`) rank `x` as a best alternative at `θ`, then `x = f(θ)`. -/
def NoVetoPower (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ θ x (j : ι), (∀ i, i ≠ j → ∀ y, u i y (θ i) ≤ u i x (θ i)) → f θ = x

open Classical in
/-- **Appendix B** (MWG, p. 915). No veto power in MWG's wording: whenever at least `I - 1` agents
rank `x` as a best alternative, `x = f(θ)`. -/
theorem noVetoPower_iff_card [Fintype ι] [Nonempty ι] (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) :
    NoVetoPower u f ↔ ∀ θ x, Fintype.card ι - 1 ≤
      (Finset.univ.filter fun i => ∀ y, u i y (θ i) ≤ u i x (θ i)).card → f θ = x := by
  constructor
  · intro h θ x hc
    obtain ⟨j, hj⟩ := (nash_allBut_iff_card _).2 hc
    exact h θ x j hj
  · intro h θ x j hj
    exact h θ x ((nash_allBut_iff_card _).1 ⟨j, hj⟩)

/-- **Appendix B** (MWG, p. 915). If no two agents ever have a common best alternative, no veto
power is trivially satisfied when `I ≥ 3` (then `I - 1 ≥ 2` agents cannot agree on a best
alternative). -/
theorem noVetoPower_of_noCommonTop [Fintype ι] (h3 : 3 ≤ Fintype.card ι)
    {u : (i : ι) → X → Θ i → ℝ} (f : ((i : ι) → Θ i) → X)
    (hT : ∀ (θ : (i : ι) → Θ i) x (i j : ι), i ≠ j → (∀ y, u i y (θ i) ≤ u i x (θ i)) →
      (∀ y, u j y (θ j) ≤ u j x (θ j)) → False) : NoVetoPower u f := by
  intro θ x j hx
  obtain ⟨k, hkj, -⟩ := nash_exists_third h3 j j
  obtain ⟨k', hk'j, hk'k⟩ := nash_exists_third h3 j k
  exact (hT θ x k k' (Ne.symm hk'k) (hx k hkj) (hx k' hk'j)).elim

/-- **Appendix B** (MWG, p. 915). A social choice correspondence `F` is monotonic if whenever
`x ∈ F(θ)` and `Lᵢ(x, θᵢ) ⊆ Lᵢ(x, θᵢ')` for all `i`, then `x ∈ F(θ')`. -/
def MonotonicSCC (u : (i : ι) → X → Θ i → ℝ) (F : ((i : ι) → Θ i) → Set X) : Prop :=
  ∀ θ θ' x, x ∈ F θ → (∀ i, lowerContour u i x (θ i) ⊆ lowerContour u i x (θ' i)) → x ∈ F θ'

/-- **Appendix B** (MWG, p. 915). No veto power for a correspondence: if all agents except
possibly `j` rank `x` as a best alternative at `θ`, then `x ∈ F(θ)`. -/
def NoVetoPowerSCC (u : (i : ι) → X → Θ i → ℝ) (F : ((i : ι) → Θ i) → Set X) : Prop :=
  ∀ θ x (j : ι), (∀ i, i ≠ j → ∀ y, u i y (θ i) ≤ u i x (θ i)) → x ∈ F θ

/-- **Appendix A** (MWG, p. 912) and **Appendix B** (MWG, p. 915). `Γ` strongly implements the
correspondence `F` in Nash equilibrium: at each `θ` a Nash equilibrium exists and every Nash
equilibrium outcome `g(s*(θ))` lies in `F(θ)`. -/
def StronglyImplementsSCCInNash [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (F : ((i : ι) → Θ i) → Set X) : Prop :=
  ∀ θ, (∃ σ, IsNashAt u Γ θ σ) ∧ ∀ σ, IsNashAt u Γ θ σ → Γ.outcome σ ∈ F θ

/-- **Appendix B** (MWG, p. 915). Full implementation of `F`: at each `θ` the set of Nash
equilibrium outcomes is exactly `F(θ)`. -/
def FullyImplementsInNash [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (F : ((i : ι) → Θ i) → Set X) : Prop :=
  ∀ θ, {x | ∃ σ, IsNashAt u Γ θ σ ∧ Γ.outcome σ = x} = F θ

/-- **Appendix B** (MWG, p. 915). Full implementation of a correspondence with nonempty values is
strong implementation. -/
theorem FullyImplementsInNash.stronglyImplementsSCC [DecidableEq ι]
    {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X} {F : ((i : ι) → Θ i) → Set X}
    (h : FullyImplementsInNash u Γ F) (hne : ∀ θ, (F θ).Nonempty) :
    StronglyImplementsSCCInNash u Γ F := by
  intro θ
  refine ⟨?_, fun σ hσ => ?_⟩
  · obtain ⟨x, hx⟩ := hne θ
    rw [← h θ] at hx
    obtain ⟨σ, hσ, -⟩ := hx
    exact ⟨σ, hσ⟩
  · rw [← h θ]
    exact ⟨σ, hσ, rfl⟩

/-- **Definition 23.BB.1** (MWG, p. 913). Strong implementation of `f` is full implementation of
the singleton correspondence `θ ↦ {f(θ)}`. -/
theorem stronglyImplementsInNash_iff_full [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (f : ((i : ι) → Θ i) → X) :
    StronglyImplementsInNash u Γ f ↔ FullyImplementsInNash u Γ (fun θ => {f θ}) := by
  constructor
  · intro h θ
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (h θ).2 σ hσ
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨σ, hσ⟩ := (h θ).1
      exact ⟨σ, hσ, (h θ).2 σ hσ⟩
  · intro h θ
    refine ⟨?_, fun σ hσ => ?_⟩
    · have hx : f θ ∈ {x | ∃ σ, IsNashAt u Γ θ σ ∧ Γ.outcome σ = x} := by
        rw [h θ]
        rfl
      obtain ⟨σ, hσ, -⟩ := hx
      exact ⟨σ, hσ⟩
    · have hx : Γ.outcome σ ∈ {x | ∃ σ, IsNashAt u Γ θ σ ∧ Γ.outcome σ = x} := ⟨σ, hσ, rfl⟩
      rw [h θ] at hx
      exact hx

/-- **Proposition 23.BB.1 for correspondences** (MWG, p. 915: "the necessary and sufficient
conditions … carry over to the multivalued case"). If `Γ` fully implements `F` in Nash
equilibrium, then `F` is monotonic. -/
theorem proposition_23_BB_1_correspondence [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {F : ((i : ι) → Θ i) → Set X} (h : FullyImplementsInNash u Γ F) :
    MonotonicSCC u F := by
  intro θ θ' x hx hL
  rw [← h θ] at hx
  rw [← h θ']
  obtain ⟨σ, hσ, rfl⟩ := hx
  refine ⟨σ, fun i a => hL i (hσ i a), rfl⟩

/-- **Appendix B** (MWG, p. 915). A monotonic social choice function is a monotonic singleton
correspondence. -/
theorem monotonicSCC_singleton {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hM : MonotonicSCF u f) : MonotonicSCC u (fun θ => {f θ}) := by
  intro θ θ' x hx hL
  rw [Set.mem_singleton_iff] at hx ⊢
  subst hx
  exact (hM θ θ' hL).symm

/-- **Appendix B** (MWG, p. 915). No veto power of a social choice function is no veto power of its
singleton correspondence. -/
theorem noVetoPowerSCC_singleton {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hV : NoVetoPower u f) : NoVetoPowerSCC u (fun θ => {f θ}) :=
  fun θ x j hx => Set.mem_singleton_iff.2 (hV θ x j hx).symm

/-- **Proposition 23.BB.3** (Maskin's mechanism). A message: a type profile, an alternative and a
nonnegative integer. -/
abbrev MaskinMsg (Θ : ι → Type*) (X : Type*) : Type _ := ((i : ι) → Θ i) × X × ℕ

open Classical in
/-- **Proposition 23.BB.3** (Maskin, 1977; the proof MWG omit, p. 915). The outcome function of
Maskin's mechanism for a correspondence `F`, messages `mᵢ = (θ̂ⁱ, xⁱ, nⁱ)`.
Rule 1: if all agents announce `(θ̂, x, 0)` with `x ∈ F(θ̂)`, the outcome is `x`.
Rule 2: if all agents but `j` announce `(θ̂, x, 0)` with `x ∈ F(θ̂)`, the outcome is `xʲ` if
`uⱼ(x, θ̂ⱼ) ≥ uⱼ(xʲ, θ̂ⱼ)` and `x` otherwise.
Rule 3: otherwise, the outcome is `xⁱ` for an agent `i` announcing the largest integer. -/
noncomputable def maskinOutcome [Fintype ι] [Nonempty ι] (u : (i : ι) → X → Θ i → ℝ)
    (F : ((i : ι) → Θ i) → Set X) (m : ι → MaskinMsg Θ X) : X :=
  if h1 : ∃ p : ((i : ι) → Θ i) × X, p.2 ∈ F p.1 ∧ ∀ k, m k = (p.1, p.2, 0) then h1.choose.2
  else if h2 : ∃ p : ((i : ι) → Θ i) × X × ι, p.2.1 ∈ F p.1 ∧
      ∀ k, k ≠ p.2.2 → m k = (p.1, p.2.1, 0) then
    if u h2.choose.2.2 (m h2.choose.2.2).2.1 (h2.choose.1 h2.choose.2.2) ≤
        u h2.choose.2.2 h2.choose.2.1 (h2.choose.1 h2.choose.2.2)
    then (m h2.choose.2.2).2.1 else h2.choose.2.1
  else (m (Finset.univ.exists_max_image (fun k => (m k).2.2) Finset.univ_nonempty).choose).2.1

/-- **Proposition 23.BB.3** (MWG, p. 915). Maskin's mechanism: each agent's strategy set is the
set of messages `Θ × X × ℕ`. -/
noncomputable def maskinMech [Fintype ι] [Nonempty ι] (u : (i : ι) → X → Θ i → ℝ)
    (F : ((i : ι) → Θ i) → Set X) : Mechanism (fun _ : ι => MaskinMsg Θ X) X :=
  ⟨maskinOutcome u F⟩

/-- **Proposition 23.BB.3** (MWG, p. 915). Maskin's mechanism, rule 1. -/
theorem maskin_rule1 [Fintype ι] [Nonempty ι] (u : (i : ι) → X → Θ i → ℝ)
    (F : ((i : ι) → Θ i) → Set X) {m : ι → MaskinMsg Θ X} {θh : (i : ι) → Θ i} {x : X}
    (hx : x ∈ F θh) (h : ∀ k, m k = (θh, x, 0)) : maskinOutcome u F m = x := by
  have h1 : ∃ p : ((i : ι) → Θ i) × X, p.2 ∈ F p.1 ∧ ∀ k, m k = (p.1, p.2, 0) :=
    ⟨(θh, x), hx, h⟩
  unfold maskinOutcome
  rw [dite_eq_left h1]
  obtain ⟨-, hc⟩ := h1.choose_spec
  obtain ⟨k⟩ := ‹Nonempty ι›
  have e := (h k).symm.trans (hc k)
  simp only [Prod.mk.injEq] at e
  exact e.2.1.symm

/-- **Proposition 23.BB.3** (MWG, p. 915). Maskin's mechanism, rule 2 (with `I ≥ 3` the profile, the
alternative and the odd agent out are determined by the messages). -/
theorem maskin_rule2 [Fintype ι] [Nonempty ι] (h3 : 3 ≤ Fintype.card ι)
    (u : (i : ι) → X → Θ i → ℝ) (F : ((i : ι) → Θ i) → Set X) {m : ι → MaskinMsg Θ X}
    {θh : (i : ι) → Θ i} {x : X} {j : ι} (hx : x ∈ F θh) (h : ∀ k, k ≠ j → m k = (θh, x, 0))
    (hj : m j ≠ (θh, x, 0)) :
    maskinOutcome u F m = if u j (m j).2.1 (θh j) ≤ u j x (θh j) then (m j).2.1 else x := by
  have hn1 : ¬∃ p : ((i : ι) → Θ i) × X, p.2 ∈ F p.1 ∧ ∀ k, m k = (p.1, p.2, 0) := by
    rintro ⟨p, -, hp⟩
    obtain ⟨k, hk, -⟩ := nash_exists_third h3 j j
    have e := (h k hk).symm.trans (hp k)
    simp only [Prod.mk.injEq] at e
    apply hj
    rw [hp j, ← e.1, ← e.2.1]
  have h2 : ∃ p : ((i : ι) → Θ i) × X × ι, p.2.1 ∈ F p.1 ∧
      ∀ k, k ≠ p.2.2 → m k = (p.1, p.2.1, 0) := ⟨(θh, x, j), hx, h⟩
  unfold maskinOutcome
  rw [dite_eq_right hn1, dite_eq_left h2]
  obtain ⟨-, hp⟩ := h2.choose_spec
  generalize h2.choose = p at hp ⊢
  obtain ⟨a, b, c⟩ := p
  obtain ⟨k, hk1, hk2⟩ := nash_exists_third h3 j c
  have e := (h k hk1).symm.trans (hp k hk2)
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, -⟩ := e
  have hc : c = j := by
    by_contra hc
    exact hj (hp j (Ne.symm hc))
  subst hc
  rfl

/-- **Proposition 23.BB.3** (MWG, p. 915). Maskin's mechanism, rule 3: when rules 1 and 2 do not
apply, an agent announcing a strictly largest integer gets the alternative he announces. -/
theorem maskin_rule3 [Fintype ι] [Nonempty ι] (u : (i : ι) → X → Θ i → ℝ)
    (F : ((i : ι) → Θ i) → Set X) {m : ι → MaskinMsg Θ X} {i : ι}
    (hno : ¬∃ p : ((i : ι) → Θ i) × X × ι, p.2.1 ∈ F p.1 ∧
      ∀ k, k ≠ p.2.2 → m k = (p.1, p.2.1, 0))
    (hwin : ∀ k, k ≠ i → (m k).2.2 < (m i).2.2) : maskinOutcome u F m = (m i).2.1 := by
  have hn1 : ¬∃ p : ((i : ι) → Θ i) × X, p.2 ∈ F p.1 ∧ ∀ k, m k = (p.1, p.2, 0) := by
    rintro ⟨p, hp1, hp⟩
    exact hno ⟨(p.1, p.2, i), hp1, fun k _ => hp k⟩
  unfold maskinOutcome
  rw [dite_eq_right hn1, dite_eq_right hno]
  have hw := (Finset.univ.exists_max_image (fun k => (m k).2.2) Finset.univ_nonempty).choose_spec
  generalize (Finset.univ.exists_max_image (fun k => (m k).2.2) Finset.univ_nonempty).choose
    = w at hw ⊢
  by_cases hwi : w = i
  · rw [hwi]
  · exact absurd (hw.2 i (Finset.mem_univ i)) (not_le.2 (hwin w hwi))

/-- **Proposition 23.BB.3** (MWG, p. 915). Maskin's mechanism: an agent `i` such that the other
agents do not all announce a common `(θ̂, x, 0)` with `x ∈ F(θ̂)` can obtain any alternative `z` by
announcing `z` together with an integer larger than everybody else's (rule 3). -/
theorem maskin_win [Fintype ι] [Nonempty ι] [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (F : ((i : ι) → Θ i) → Set X) {σ : ι → MaskinMsg Θ X} {i : ι}
    (hno : ¬∃ q : ((i : ι) → Θ i) × X, q.2 ∈ F q.1 ∧ ∀ k, k ≠ i → σ k = (q.1, q.2, 0))
    (θ0 : (i : ι) → Θ i) (z : X) :
    maskinOutcome u F (update σ i (θ0, z, ∑ k, (σ k).2.2 + 1)) = z := by
  have h := maskin_rule3 (i := i) u F (m := update σ i (θ0, z, ∑ k, (σ k).2.2 + 1)) ?_ ?_
  · rw [h, update_self]
  · rintro ⟨⟨a, b, c⟩, hb, hp⟩
    by_cases hci : c = i
    · subst hci
      exact hno ⟨(a, b), hb, fun k hk => by have h' := hp k hk; rwa [update_of_ne hk] at h'⟩
    · have h' := hp i (Ne.symm hci)
      rw [update_self] at h'
      simp only [Prod.mk.injEq] at h'
      exact absurd h'.2.2 (Nat.succ_ne_zero _)
  · intro k hk
    rw [update_of_ne hk, update_self]
    have h' := Finset.single_le_sum (f := fun k => (σ k).2.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    simp only at h' ⊢
    omega

/-- **Proposition 23.BB.3 for correspondences** (Maskin; MWG, p. 915: Maskin's result establishes
full implementation). If `I ≥ 3` and `F` is monotonic and satisfies no veto power, Maskin's
mechanism fully implements `F` in Nash equilibrium: at each `θ` its Nash equilibrium outcomes
are exactly `F(θ)`. -/
theorem maskin_fullyImplements [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (h3 : 3 ≤ Fintype.card ι) {u : (i : ι) → X → Θ i → ℝ} {F : ((i : ι) → Θ i) → Set X}
    (hM : MonotonicSCC u F) (hV : NoVetoPowerSCC u F) :
    FullyImplementsInNash u (maskinMech u F) F := by
  intro θ
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change maskinOutcome u F σ ∈ F θ
    by_cases A : ∃ p : ((i : ι) → Θ i) × X, p.2 ∈ F p.1 ∧ ∀ k, σ k = (p.1, p.2, 0)
    · obtain ⟨⟨θh, x⟩, hx, hA⟩ := A
      simp only at hx hA
      rw [maskin_rule1 u F hx hA]
      refine hM θh θ x hx fun j z hz => ?_
      have hdev := hσ j (θh, z, 1)
      have hout : maskinOutcome u F (update σ j (θh, z, 1)) = z := by
        rw [maskin_rule2 h3 u F hx (j := j) (fun k hk => by rw [update_of_ne hk]; exact hA k)
          (by rw [update_self]; simp)]
        simp only [update_self]
        exact ite_eq_left hz
      change u j (maskinOutcome u F _) (θ j) ≤ u j (maskinOutcome u F σ) (θ j) at hdev
      rw [hout, maskin_rule1 u F hx hA] at hdev
      exact hdev
    · have key : ∀ i, (¬∃ q : ((i : ι) → Θ i) × X, q.2 ∈ F q.1 ∧
          ∀ k, k ≠ i → σ k = (q.1, q.2, 0)) →
          ∀ z, u i z (θ i) ≤ u i (maskinOutcome u F σ) (θ i) := by
        intro i hno z
        have h' := hσ i (θ, z, ∑ k, (σ k).2.2 + 1)
        change u i (maskinOutcome u F _) (θ i) ≤ _ at h'
        rwa [maskin_win u F hno θ z] at h'
      by_cases B : ∃ p : ((i : ι) → Θ i) × X × ι, p.2.1 ∈ F p.1 ∧
          ∀ k, k ≠ p.2.2 → σ k = (p.1, p.2.1, 0)
      · obtain ⟨⟨θh, x, j⟩, hx, hB⟩ := B
        simp only at hx hB
        refine hV θ _ j fun i hij => key i ?_
        rintro ⟨⟨a, b⟩, -, hq⟩
        simp only at hq
        obtain ⟨k, hki, hkj⟩ := nash_exists_third h3 i j
        have e := (hB k hkj).symm.trans (hq k hki)
        simp only [Prod.mk.injEq] at e
        apply A
        refine ⟨(θh, x), hx, fun k' => ?_⟩
        by_cases hk' : k' = j
        · rw [hk', hq j (Ne.symm hij), ← e.1, ← e.2.1]
        · exact hB k' hk'
      · obtain ⟨j⟩ := ‹Nonempty ι›
        refine hV θ _ j fun i _ => key i ?_
        rintro ⟨⟨a, b⟩, hb, hq⟩
        exact B ⟨(a, b, i), hb, hq⟩
  · intro hy
    refine ⟨fun _ => (θ, y, 0), fun i a => ?_, maskin_rule1 u F hy fun _ => rfl⟩
    change u i (maskinOutcome u F _) (θ i) ≤ u i (maskinOutcome u F _) (θ i)
    rw [maskin_rule1 u F hy (m := fun _ => (θ, y, 0)) fun _ => rfl]
    by_cases ha : a = (θ, y, 0)
    · have e : update (fun _ : ι => ((θ, y, 0) : MaskinMsg Θ X)) i (θ, y, 0) =
          fun _ => (θ, y, 0) := update_eq_self i _
      rw [ha, e, maskin_rule1 u F hy (m := fun _ => (θ, y, 0)) fun _ => rfl]
    · rw [maskin_rule2 h3 u F hy (j := i) (fun k hk => by simp [update_of_ne hk])
        (by rw [update_self]; exact ha)]
      rw [update_self]
      split_ifs with hc
      · exact hc
      · exact le_rfl

/-- **Proposition 23.BB.3** (Maskin; MWG, p. 915, proof omitted there). If `I ≥ 3`, `f` is
monotonic and `f` satisfies no veto power, then `f` is strongly implementable in Nash
equilibrium (by Maskin's mechanism). -/
theorem proposition_23_BB_3 [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X} (hM : MonotonicSCF u f)
    (hV : NoVetoPower u f) :
    ∃ Γ : Mechanism (fun _ : ι => MaskinMsg Θ X) X, StronglyImplementsInNash u Γ f := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  exact ⟨maskinMech u (fun θ => {f θ}), (stronglyImplementsInNash_iff_full u _ f).2
    (maskin_fullyImplements h3 (monotonicSCC_singleton hM) (noVetoPowerSCC_singleton hV))⟩

/-- **Proposition 23.BB.3** (MWG, p. 915). Three agents and three alternatives; agent `i` values
only alternative `i`. -/
def nvpU : Fin 3 → Fin 3 → Bool → ℝ := fun i x _ => if x = i then 1 else 0

/-- **Proposition 23.BB.3**, non-vacuity (MWG, p. 915). Three agents and three alternatives; agent
`i` likes only alternative `i` (so no two agents share a best alternative and no veto power
holds); the constant social choice function is monotonic and hence strongly implementable. -/
theorem proposition_23_BB_3_instance :
    MonotonicSCF (Θ := fun _ : Fin 3 => Bool) nvpU (fun _ => 0) ∧
      NoVetoPower (Θ := fun _ : Fin 3 => Bool) nvpU (fun _ => 0) ∧
      ∃ Γ : Mechanism (fun _ : Fin 3 => MaskinMsg (fun _ : Fin 3 => Bool) (Fin 3)) (Fin 3),
        StronglyImplementsInNash (Θ := fun _ : Fin 3 => Bool) nvpU Γ (fun _ => 0) := by
  have hM : MonotonicSCF (Θ := fun _ : Fin 3 => Bool) nvpU (fun _ => 0) := fun _ _ _ => rfl
  have hV : NoVetoPower (Θ := fun _ : Fin 3 => Bool) nvpU (fun _ => 0) := by
    refine noVetoPower_of_noCommonTop (by simp) _ fun θ x i j hij hi hj => ?_
    have h1 := hi i
    have h2 := hj j
    simp only [nvpU, ite_true] at h1 h2
    by_cases hxi : x = i
    · by_cases hxj : x = j
      · exact hij (hxi.symm.trans hxj)
      · simp only [hxj, ite_false] at h2
        norm_num at h2
    · simp only [hxi, ite_false] at h1
      norm_num at h1
  exact ⟨hM, hV, proposition_23_BB_3 (by simp) hM hV⟩

/-! ### Pareto correspondences and transferable goods (p. 915) -/

/-- **Appendix B** (MWG, p. 915). The Pareto set at `θ`: the ex post efficient alternatives
(Definition 23.B.2): no `x'` makes every agent weakly and some agent strictly better off. -/
def ParetoSet (u : (i : ι) → X → Θ i → ℝ) (θ : (i : ι) → Θ i) : Set X :=
  {x | ¬∃ x', (∀ i, u i x (θ i) ≤ u i x' (θ i)) ∧ ∃ i, u i x (θ i) < u i x' (θ i)}

/-- The weak Pareto set at `θ`: no `x'` makes every agent strictly better off. -/
def WeakParetoSet (u : (i : ι) → X → Θ i → ℝ) (θ : (i : ι) → Θ i) : Set X :=
  {x | ¬∃ x', ∀ i, u i x (θ i) < u i x' (θ i)}

/-- **Appendix B** (MWG, p. 915), corrected. The weak Pareto correspondence is monotonic. -/
theorem weakParetoSet_monotonic (u : (i : ι) → X → Θ i → ℝ) :
    MonotonicSCC u (WeakParetoSet u) := by
  intro θ θ' x hx hL hcon
  obtain ⟨x', hx'⟩ := hcon
  exact hx ⟨x', fun i => lt_of_not_ge fun h => absurd (hL i h) (not_le.2 (hx' i))⟩

/-- **Appendix B** (MWG, p. 915). The utilities of the counterexample `paretoSet_not_monotonic`:
alternatives `false` (`x`) and `true` (`y`); agent 0 prefers `y`; agent 1 of type `true` prefers
`x`, of type `false` is indifferent. -/
def nashParetoCxU : Fin 2 → Bool → Bool → ℝ :=
  fun i x b => if i = 0 then (if x then 1 else 0) else (if b then (if x then 0 else 1) else 0)

/-- **Appendix B** (MWG, p. 915), correction. "If `f(θ)` is the Pareto set for all `θ`, then `f`
is monotonic" is false in general: `x` is Pareto optimal when agent 1 strictly prefers it, the
lower contour sets of `x` do not shrink when agent 1 becomes indifferent, but then `y` Pareto
dominates `x`. -/
theorem paretoSet_not_monotonic :
    ¬MonotonicSCC (Θ := fun _ : Fin 2 => Bool) nashParetoCxU (ParetoSet nashParetoCxU) := by
  intro hM
  have hx : false ∈ ParetoSet (Θ := fun _ : Fin 2 => Bool) nashParetoCxU (fun _ => true) := by
    rintro ⟨x', h1, i, h2⟩
    cases x'
    · exact lt_irrefl _ h2
    · have h := h1 1
      norm_num [nashParetoCxU] at h
  have hinc : ∀ i, lowerContour (Θ := fun _ : Fin 2 => Bool) nashParetoCxU i false true ⊆
      lowerContour (Θ := fun _ : Fin 2 => Bool) nashParetoCxU i false (![true, false] i) := by
    intro i z hz
    fin_cases i
    · exact hz
    · change nashParetoCxU 1 z false ≤ nashParetoCxU 1 false false
      norm_num [nashParetoCxU]
  apply hM (fun _ => true) ![true, false] false hx hinc
  refine ⟨true, fun i => ?_, 0, by norm_num [nashParetoCxU]⟩
  fin_cases i <;> norm_num [nashParetoCxU]

variable {K : Type*}

/-- **Appendix B** (MWG, p. 915). Quasilinear utilities `uᵢ((k, t), θᵢ) = vᵢ(k, θᵢ) + m̄ᵢ + tᵢ` on
the feasible alternatives `X = {(k, t) : ∑ᵢ tᵢ ≤ 0}` (a transferable private good). -/
def nashQLU [Fintype ι] (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) :
    (i : ι) → QLAlt ι K → Θ i → ℝ :=
  fun i x θi => qlU v m i x.1 θi

/-- **Appendix B** (MWG, p. 915). With a transferable private good and at least two agents, no
agent has a best alternative: moving one unit of the good from `j` to `i` makes `i` better off. -/
theorem nash_ql_no_best [Fintype ι] (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ)
    {i j : ι} (hij : i ≠ j) (θi : Θ i) (x : QLAlt ι K) :
    ∃ y : QLAlt ι K, nashQLU v m i x θi < nashQLU v m i y θi := by
  classical
  let t : ι → ℝ := fun k => x.1.2 k + (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have ht : ∑ k, t k ≤ 0 := by
    have e : ∑ k, t k = ∑ k, x.1.2 k := by
      simp only [t, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      ring
    rw [e]
    exact x.2
  refine ⟨⟨(x.1.1, t), ht⟩, ?_⟩
  simp only [nashQLU, qlU, t, ite_true, hij, ite_false]
  linarith

/-- **Appendix B** (MWG, p. 915). With a transferable private good and `I ≥ 2`, no veto power is
trivially satisfied. -/
theorem noVetoPower_ql [Fintype ι] (h2 : 2 ≤ Fintype.card ι)
    (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    NoVetoPower (nashQLU v m) f := by
  intro θ x j hx
  obtain ⟨i, hij⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
  obtain ⟨y, hy⟩ := nash_ql_no_best v m hij (θ i) x
  exact absurd (hx i hij y) (not_le.2 hy)

/-- **Appendix B** (MWG, p. 915). No veto power for correspondences, with a transferable good. -/
theorem noVetoPowerSCC_ql [Fintype ι] (h2 : 2 ≤ Fintype.card ι)
    (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) (F : ((i : ι) → Θ i) → Set (QLAlt ι K)) :
    NoVetoPowerSCC (nashQLU v m) F := by
  intro θ x j hx
  obtain ⟨i, hij⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
  obtain ⟨y, hy⟩ := nash_ql_no_best v m hij (θ i) x
  exact absurd (hx i hij y) (not_le.2 hy)

/-- **Appendix B** (MWG, p. 915). In environments with a transferable private good and `I ≥ 3`,
monotonicity of `f` is necessary and sufficient for strong implementability in Nash
equilibrium. -/
theorem nash_ql_strong_iff_monotonic [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    (∃ Γ : Mechanism (fun _ : ι => MaskinMsg Θ (QLAlt ι K)) (QLAlt ι K),
        StronglyImplementsInNash (nashQLU v m) Γ f) ↔ MonotonicSCF (nashQLU v m) f :=
  ⟨fun ⟨_, h⟩ => proposition_23_BB_1 h,
    fun hM => proposition_23_BB_3 h3 hM (noVetoPower_ql (by omega) v m f)⟩

/-- **Appendix B** (MWG, p. 915), corrected. With a transferable good (quasilinear utilities) the
Pareto correspondence is monotonic: if `x'` Pareto dominates `x` at `θ'`, redistributing the
gain gives an alternative every agent strictly prefers to `x` at `θ'`, hence (lower contour
sets having expanded) also at `θ`. -/
theorem paretoSet_ql_monotonic [Fintype ι] [Nonempty ι]
    (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) :
    MonotonicSCC (nashQLU v m) (ParetoSet (nashQLU v m)) := by
  classical
  intro θ θ' x hx hL hcon
  obtain ⟨x', h1, j, hj⟩ := hcon
  apply hx
  set δ := nashQLU v m j x' (θ' j) - nashQLU v m j x (θ' j) with hδdef
  have hδ : 0 < δ := sub_pos.2 hj
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let t'' : ι → ℝ := fun i => x'.1.2 i + δ / Fintype.card ι - (if i = j then δ else 0)
  have hfeas : ∑ i, t'' i ≤ 0 := by
    have e : ∑ i, t'' i = ∑ i, x'.1.2 i := by
      simp only [t'', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      field_simp
      ring
    rw [e]
    exact x'.2
  let x'' : QLAlt ι K := ⟨(x'.1.1, t''), hfeas⟩
  have hd : 0 < δ / Fintype.card ι := div_pos hδ hn
  have hstrict : ∀ i, nashQLU v m i x (θ' i) < nashQLU v m i x'' (θ' i) := by
    intro i
    have h1i := h1 i
    by_cases hij : i = j
    · subst hij
      simp only [nashQLU, qlU, x'', t'', ite_true] at hδdef ⊢
      linarith
    · simp only [nashQLU, qlU, x'', t'', hij, ite_false] at h1i ⊢
      linarith
  have hθ : ∀ i, nashQLU v m i x (θ i) < nashQLU v m i x'' (θ i) :=
    fun i => lt_of_not_ge fun h => absurd (hL i h) (not_le.2 (hstrict i))
  obtain ⟨i0⟩ := ‹Nonempty ι›
  exact ⟨x'', fun i => (hθ i).le, i0, hθ i0⟩

/-- **Appendix B** (MWG, p. 915). With a transferable good and `I ≥ 3`, the Pareto set social
choice correspondence is (fully, hence strongly) implementable in Nash equilibrium. -/
theorem nash_ql_pareto_fullyImplements [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (h3 : 3 ≤ Fintype.card ι) (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) :
    FullyImplementsInNash (nashQLU v m) (maskinMech (nashQLU v m) (ParetoSet (nashQLU v m)))
      (ParetoSet (nashQLU v m)) :=
  maskin_fullyImplements h3 (paretoSet_ql_monotonic v m) (noVetoPowerSCC_ql (by omega) v m _)

/-! ### Exercise 23.BB.2 -/

/-- **Exercise 23.C.8** (MWG, pp. 919-920), used in Exercise 23.BB.2. Alternatives
`a, b, c, d, e = 0, …, 4`; type `true` (`θᵢ'`): `a ~ b ≻ c ≻ d ≻ e`; type `false` (`θᵢ''`):
`a ≻ b ≻ d ≻ c ≻ e`; the same for both agents. -/
def c8U : Fin 2 → Fin 5 → Bool → ℝ :=
  fun _ x b => if b then ![4, 4, 2, 1, 0] x else ![4, 3, 1, 2, 0] x

/-- **Exercise 23.C.8** (MWG, p. 920). `f(θ) = b` if `θ = (θ₁', θ₂')` and `a` otherwise. -/
def c8F (θ : Fin 2 → Bool) : Fin 5 := if θ 0 && θ 1 then 1 else 0

/-- **Exercise 23.BB.2** (MWG, p. 925). The social choice function of Exercise 23.C.8 is
strategy-proof. -/
theorem exercise_23_BB_2b_strategyProof : StrategyProof (Θ := fun _ : Fin 2 => Bool) c8U c8F := by
  intro i θ θh
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  all_goals cases h0 : θ 0 <;> cases h1 : θ 1 <;> cases θh <;>
    norm_num [c8U, c8F, h0, h1, update_apply]

/-- **Exercise 23.BB.2** (MWG, p. 925). The social choice function of Exercise 23.C.8 is
implemented in dominant strategies (by its direct mechanism), hence in Nash equilibrium. -/
theorem exercise_23_BB_2b_implementable :
    ImplementsInDominantStrategies (Θ := fun _ : Fin 2 => Bool) c8U (directMechanism c8F) c8F ∧
      ImplementsInNash (Θ := fun _ : Fin 2 => Bool) c8U (directMechanism c8F) c8F :=
  ⟨strategyProof_implements exercise_23_BB_2b_strategyProof,
    dominant_implementsInNash (strategyProof_implements exercise_23_BB_2b_strategyProof)⟩

/-- **Exercise 23.BB.2** (MWG, p. 925). The social choice function of Exercise 23.C.8 is not
monotonic: `a = f(θ₁'', θ₂')` is a best alternative for both agents at `(θ₁', θ₂')` too, so its
lower contour sets do not shrink, yet `f(θ₁', θ₂') = b`. -/
theorem exercise_23_BB_2b_not_monotonic : ¬MonotonicSCF (Θ := fun _ : Fin 2 => Bool) c8U c8F := by
  intro hM
  have h := hM ![false, true] (fun _ => true) fun i z _ => by
    change c8U i z true ≤ c8U i (c8F ![false, true]) true
    fin_cases z <;> norm_num [c8U, c8F]
  norm_num [c8F] at h

/-- **Exercise 23.BB.2** (MWG, p. 925), second question. A social choice function implementable in
dominant strategies need not be strongly implementable in Nash equilibrium: no mechanism
strongly implements the function of Exercise 23.C.8 (Proposition 23.BB.1). -/
theorem exercise_23_BB_2b_not_strongly {S : Fin 2 → Type*} (Γ : Mechanism S (Fin 5)) :
    ¬StronglyImplementsInNash (Θ := fun _ : Fin 2 => Bool) c8U Γ c8F :=
  fun h => exercise_23_BB_2b_not_monotonic (proposition_23_BB_1 h)

/-! ### Exercise 23.BB.3 -/

/-- **Exercise 23.BB.3** (MWG, p. 925). Public project choice with `K = {0, 1}` (`false`, `true`)
and `Θᵢ = ℝ`: agent `i`'s benefit is `vᵢ(k, θᵢ) = θᵢ k`. -/
def bbV : ι → Bool → ℝ → ℝ := fun _ k θi => if k then θi else 0

/-- **Exercise 23.BB.3** (MWG, p. 925). Utilities `uᵢ((k, t), θᵢ) = θᵢ k + tᵢ` on
`X = {(k, t) : ∑ᵢ tᵢ ≤ 0}`. -/
def bbU [Fintype ι] : (i : ι) → QLAlt ι Bool → ℝ → ℝ := nashQLU (Θ := fun _ => ℝ) bbV 0

/-- **Exercise 23.BB.3** (MWG, p. 925), property (i) of Groves transfers: if
`k(θᵢ, θ₋ᵢ) = k(θᵢ', θ₋ᵢ)` then `tᵢ(θᵢ, θ₋ᵢ) = tᵢ(θᵢ', θ₋ᵢ)`. -/
def GrovesPropertyI [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → QLAlt ι Bool) : Prop :=
  ∀ i (θ : ι → ℝ) (a : ℝ), (f (update θ i a)).1.1 = (f θ).1.1 →
    (f (update θ i a)).1.2 i = (f θ).1.2 i

/-- **Exercise 23.BB.3** (MWG, p. 925), property (ii) of Groves transfers: if `k(θᵢ, θ₋ᵢ) = 1` and
`k(θᵢ', θ₋ᵢ) = 0` then `tᵢ(θᵢ, θ₋ᵢ) - tᵢ(θᵢ', θ₋ᵢ) = ∑_{j≠i} θⱼ`. -/
def GrovesPropertyII [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → QLAlt ι Bool) : Prop :=
  ∀ i (θ : ι → ℝ) (a : ℝ), (f θ).1.1 = true → (f (update θ i a)).1.1 = false →
    (f θ).1.2 i - (f (update θ i a)).1.2 i = ∑ j ∈ Finset.univ.erase i, θ j

/-- **Exercise 23.BB.3** (MWG, p. 925). The ex post efficient project choice `k*(θ) = 1` iff `∑ᵢ θᵢ
≥ 0`. -/
noncomputable def bbK [Fintype ι] (θ : ι → ℝ) : Bool := decide (0 ≤ ∑ i, θ i)

/-- **Exercise 23.BB.3** (MWG, p. 925). The sum of the benefits `∑ᵢ vᵢ(k, θᵢ)`. -/
theorem bbV_sum [Fintype ι] (k : Bool) (θ : ι → ℝ) :
    ∑ i, bbV i k (θ i) = if k then ∑ i, θ i else 0 := by
  cases k <;> simp [bbV]

/-- **Exercise 23.BB.3** (MWG, p. 925). `k*` is ex post efficient (condition (23.C.7)). -/
theorem bbK_efficient [Fintype ι] : EfficientProject (Θ := fun _ : ι => ℝ) bbV bbK := by
  intro θ k'
  simp only [bbV_sum, bbK]
  by_cases h : 0 ≤ ∑ i, θ i
  · cases k' <;> simp [h]
  · cases k' <;> simp [h]
    linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). With an efficient project choice, `k = 1` when `∑ᵢ θᵢ > 0`.
-/
theorem bb_eff_true [Fintype ι] {k : (ι → ℝ) → Bool}
    (hE : EfficientProject (Θ := fun _ : ι => ℝ) bbV k) {θ : ι → ℝ} (h : 0 < ∑ i, θ i) :
    k θ = true := by
  by_contra hk
  have h1 := hE θ true
  rw [bbV_sum, bbV_sum, Bool.eq_false_iff.2 hk] at h1
  simp at h1
  linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). With an efficient project choice, `k = 0` when `∑ᵢ θᵢ < 0`.
-/
theorem bb_eff_false [Fintype ι] {k : (ι → ℝ) → Bool}
    (hE : EfficientProject (Θ := fun _ : ι => ℝ) bbV k) {θ : ι → ℝ} (h : ∑ i, θ i < 0) :
    k θ = false := by
  by_contra hk
  have h1 := hE θ false
  rw [bbV_sum, bbV_sum, Bool.not_eq_false _ |>.mp hk] at h1
  simp only [ite_true] at h1
  simp at h1
  linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). `∑ⱼ (θᵢ', θ₋ᵢ)ⱼ = θᵢ' + ∑_{j≠i} θⱼ`. -/
theorem bb_sum_update [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (i : ι) (a : ℝ) :
    ∑ j, update θ i a j = a + ∑ j ∈ Finset.univ.erase i, θ j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), update_self]
  congr 1
  exact Finset.sum_congr rfl fun _ hj => update_of_ne (Finset.ne_of_mem_erase hj) _ _

/-- **Exercise 23.BB.3** (MWG, p. 925). `∑_{j≠i} (θᵢ', θ₋ᵢ)ⱼ = ∑_{j≠i} θⱼ`. -/
theorem bb_erase_update [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (i : ι) (a : ℝ) :
    ∑ j ∈ Finset.univ.erase i, update θ i a j = ∑ j ∈ Finset.univ.erase i, θ j :=
  Finset.sum_congr rfl fun _ hj => update_of_ne (Finset.ne_of_mem_erase hj) _ _

/-- **Exercise 23.BB.3** (MWG, p. 925). `∑_{k≠i} (c 1_{j})ₖ = c` for `j ≠ i`. -/
theorem bb_sum_erase_single [Fintype ι] [DecidableEq ι] {i j : ι} (hji : j ≠ i) (c : ℝ) :
    ∑ k ∈ Finset.univ.erase i, update (0 : ι → ℝ) j c k = c := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩), update_self,
    Finset.sum_eq_zero fun k hk => ?_, add_zero]
  rw [update_of_ne (Finset.ne_of_mem_erase hk)]
  rfl

/-- **Exercise 23.BB.3** (MWG, p. 925). The constant-transfer rule: `k*` with `t = 0`. -/
noncomputable def bbF0 [Fintype ι] (θ : ι → ℝ) : QLAlt ι Bool :=
  ⟨(bbK θ, 0), by simp⟩

/-- **Exercise 23.BB.3** (MWG, p. 925). A rule with `k*` and transfers `tᵢ = -1` if `θᵢ > 0`, `0`
otherwise (feasible). -/
noncomputable def bbF1 [Fintype ι] (θ : ι → ℝ) : QLAlt ι Bool :=
  ⟨(bbK θ, fun i => if 0 < θ i then -1 else 0),
    Finset.sum_nonpos fun i _ => by simp only; split_ifs <;> norm_num⟩

/-- **Exercise 23.BB.3** (MWG, p. 925), Nash implementation. With `I ≥ 3` every social choice
function, in particular every one with an ex post efficient project choice, is implemented in
Nash equilibrium (pp. 913-914). -/
theorem exercise_23_BB_3_weak [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι)
    (f : (ι → ℝ) → QLAlt ι Bool) (x0 : QLAlt ι Bool) :
    ImplementsInNash bbU (agreementMech (Θ := fun _ : ι => ℝ) f x0) f :=
  nash_any_implementable h3 _ f x0

/-- **Exercise 23.BB.3** (MWG, p. 925). Property (ii) is not necessary for Nash implementation:
`(k*, t = 0)` has an efficient project choice, is Nash implementable (`I ≥ 3`) and violates
(ii). -/
theorem exercise_23_BB_3_weak_not_II [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι) :
    EfficientProject (Θ := fun _ : ι => ℝ) bbV (fun θ => (bbF0 θ).1.1) ∧
      ImplementsInNash bbU (agreementMech (Θ := fun _ : ι => ℝ) bbF0 (bbF0 0)) bbF0 ∧
      ¬GrovesPropertyII (ι := ι) bbF0 := by
  refine ⟨bbK_efficient, nash_any_implementable h3 _ _ _, fun hII => ?_⟩
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hsum : (1 : ℝ) + ∑ j ∈ Finset.univ.erase i, (1 : ℝ) = Fintype.card ι := by
    rw [Finset.add_sum_erase _ (fun _ => (1 : ℝ)) (Finset.mem_univ i)]
    simp
  have hc : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h3
  have h := hII i (fun _ => 1) (-(Fintype.card ι : ℝ)) ?_ ?_
  · simp only [bbF0, sub_self, Pi.zero_apply] at h
    linarith
  · simp only [bbF0, bbK, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [decide_eq_true_eq]
    positivity
  · simp only [bbF0, bbK, bb_sum_update, decide_eq_false_iff_not, not_le]
    linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). Property (i) is not necessary for Nash implementation:
`(k*, tᵢ = -1 if θᵢ > 0)` has an efficient project choice, is Nash implementable (`I ≥ 3`) and
violates (i). -/
theorem exercise_23_BB_3_weak_not_I [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι) :
    EfficientProject (Θ := fun _ : ι => ℝ) bbV (fun θ => (bbF1 θ).1.1) ∧
      ImplementsInNash bbU (agreementMech (Θ := fun _ : ι => ℝ) bbF1 (bbF1 0)) bbF1 ∧
      ¬GrovesPropertyI (ι := ι) bbF1 := by
  refine ⟨bbK_efficient, nash_any_implementable h3 _ _ _, fun hI => ?_⟩
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hsum : (1 : ℝ) + ∑ j ∈ Finset.univ.erase i, (1 : ℝ) = Fintype.card ι := by
    rw [Finset.add_sum_erase _ (fun _ => (1 : ℝ)) (Finset.mem_univ i)]
    simp
  have hc : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h3
  have h := hI i (fun _ => 1) 0 ?_
  · simp only [bbF1, update_self, lt_self_iff_false, ite_false, zero_lt_one, ite_true] at h
    norm_num at h
  · have a1 : (0 : ℝ) ≤ ∑ j, update (fun _ => (1 : ℝ)) i 0 j := by
      rw [bb_sum_update]
      exact add_nonneg le_rfl (Finset.sum_nonneg fun _ _ => zero_le_one)
    have a2 : (0 : ℝ) ≤ ∑ j : ι, (fun _ => (1 : ℝ)) j := Finset.sum_nonneg fun _ _ => zero_le_one
    simp only [bbF1, bbK]
    rw [decide_eq_true a1, decide_eq_true a2]

/-- **Exercise 23.BB.3** (MWG, p. 925). Under `k = 1`, raising every type weakly expands the lower
contour sets of `(k, t)`. -/
theorem bb_lower_up [Fintype ι] {x : QLAlt ι Bool} (hk : x.1.1 = true) {θi θi' : ℝ}
    (h : θi ≤ θi') (i : ι) : lowerContour bbU i x θi ⊆ lowerContour bbU i x θi' := by
  intro z hz
  have hz' : bbU i z θi ≤ bbU i x θi := hz
  change bbU i z θi' ≤ bbU i x θi'
  simp only [bbU, nashQLU, qlU, bbV, hk, ite_true, Pi.zero_apply] at hz' ⊢
  cases hzk : z.1.1 <;> simp only [hzk, ite_true] at hz' ⊢ <;> simp at hz' ⊢ <;> linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). Under `k = 0`, lowering every type weakly expands the lower
contour sets of `(k, t)`. -/
theorem bb_lower_down [Fintype ι] {x : QLAlt ι Bool} (hk : x.1.1 = false) {θi θi' : ℝ}
    (h : θi' ≤ θi) (i : ι) : lowerContour bbU i x θi ⊆ lowerContour bbU i x θi' := by
  intro z hz
  have hz' : bbU i z θi ≤ bbU i x θi := hz
  change bbU i z θi' ≤ bbU i x θi'
  simp only [bbU, nashQLU, qlU, bbV, hk, Pi.zero_apply] at hz' ⊢
  cases hzk : z.1.1 <;> simp only [hzk, ite_true] at hz' ⊢ <;> simp at hz' ⊢ <;> linarith

/-- **Exercise 23.BB.3** (MWG, p. 925), strong implementation. A monotonic `f = (k, t)` (necessary
for strong Nash implementation, Proposition 23.BB.1) is constant on `{k = 1}` and on `{k = 0}`:
two profiles with `k = 1` are both below their componentwise maximum, two with `k = 0` above
their minimum. -/
theorem exercise_23_BB_3_constant [Fintype ι] {f : (ι → ℝ) → QLAlt ι Bool}
    (hM : MonotonicSCF (Θ := fun _ : ι => ℝ) bbU f) {θ θ' : ι → ℝ}
    (hk : (f θ).1.1 = (f θ').1.1) : f θ = f θ' := by
  cases hb : (f θ).1.1
  · have hb' : (f θ').1.1 = false := hk ▸ hb
    have e1 := hM θ (fun i => min (θ i) (θ' i)) fun i => bb_lower_down hb (min_le_left _ _) i
    have e2 := hM θ' (fun i => min (θ i) (θ' i)) fun i => bb_lower_down hb' (min_le_right _ _) i
    exact e1.symm.trans e2
  · have hb' : (f θ').1.1 = true := hk ▸ hb
    have e1 := hM θ (fun i => max (θ i) (θ' i)) fun i => bb_lower_up hb (le_max_left _ _) i
    have e2 := hM θ' (fun i => max (θ i) (θ' i)) fun i => bb_lower_up hb' (le_max_right _ _) i
    exact e1.symm.trans e2

/-- **Exercise 23.BB.3** (MWG, p. 925). Property (i) must hold for every strongly Nash
implementable social choice function (indeed the whole outcome is unchanged). -/
theorem exercise_23_BB_3_strong_I [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {f : (ι → ℝ) → QLAlt ι Bool} {Γ : Mechanism S (QLAlt ι Bool)}
    (h : StronglyImplementsInNash (Θ := fun _ : ι => ℝ) bbU Γ f) : GrovesPropertyI f :=
  fun _ _ _ hk => by rw [exercise_23_BB_3_constant (proposition_23_BB_1 h) hk]

/-- **Exercise 23.BB.3** (MWG, p. 925). Property (ii) holds for no strongly Nash implementable
social choice function with an ex post efficient project choice (`I ≥ 2`): by
`exercise_23_BB_3_constant` the difference `tᵢ(θ) - tᵢ(θᵢ', θ₋ᵢ)` cannot depend on `θ₋ᵢ`. -/
theorem exercise_23_BB_3_strong_not_II [Fintype ι] [DecidableEq ι] (h2 : 2 ≤ Fintype.card ι)
    {S : ι → Type*} {f : (ι → ℝ) → QLAlt ι Bool} {Γ : Mechanism S (QLAlt ι Bool)}
    (h : StronglyImplementsInNash (Θ := fun _ : ι => ℝ) bbU Γ f)
    (hE : EfficientProject (Θ := fun _ : ι => ℝ) bbV (fun θ => (f θ).1.1)) :
    ¬GrovesPropertyII f := by
  intro hII
  have hM := proposition_23_BB_1 h
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have hz : ∑ k ∈ Finset.univ.erase i, (0 : ι → ℝ) k = 0 := by simp
  -- `θ¹ = (1, 0, …)`, `θ² = (1, 1, 0, …)` (agent `i` first), lowered to `-1` and `-3`
  set θ1 : ι → ℝ := update 0 i 1
  set θ2 : ι → ℝ := update (update 0 j 1) i 1
  have s1 : ∑ k, θ1 k = 1 := by simp only [θ1, bb_sum_update, hz, add_zero]
  have s1' : ∑ k, update θ1 i (-1) k = -1 := by
    simp only [θ1, update_idem, bb_sum_update, hz, add_zero]
  have s2 : ∑ k, θ2 k = 2 := by
    simp only [θ2, bb_sum_update, bb_sum_erase_single hji]
    norm_num
  have s2' : ∑ k, update θ2 i (-3) k = -2 := by
    simp only [θ2, update_idem, bb_sum_update, bb_sum_erase_single hji]
    norm_num
  have e1 : ∑ k ∈ Finset.univ.erase i, θ1 k = 0 := by
    simp only [θ1, bb_erase_update, hz]
  have e2 : ∑ k ∈ Finset.univ.erase i, θ2 k = 1 := by
    simp only [θ2, bb_erase_update, bb_sum_erase_single hji]
  have k1 := bb_eff_true hE (θ := θ1) (by rw [s1]; norm_num)
  have k2 := bb_eff_true hE (θ := θ2) (by rw [s2]; norm_num)
  have k1' := bb_eff_false hE (θ := update θ1 i (-1)) (by rw [s1']; norm_num)
  have k2' := bb_eff_false hE (θ := update θ2 i (-3)) (by rw [s2']; norm_num)
  have d1 := hII i θ1 (-1) k1 k1'
  have d2 := hII i θ2 (-3) k2 k2'
  rw [exercise_23_BB_3_constant hM (k1.trans k2.symm),
    exercise_23_BB_3_constant hM (k1'.trans k2'.symm), e1] at d1
  rw [e2] at d2
  linarith

/-- **Exercise 23.BB.3** (MWG, p. 925). With `I ≥ 3` some social choice function with an ex post
efficient project choice is strongly implementable in Nash equilibrium: `(k*, t = 0)` is
monotonic, and no veto power holds trivially. It satisfies (i) but not (ii). -/
theorem exercise_23_BB_3_strong_exists [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι) :
    EfficientProject (Θ := fun _ : ι => ℝ) bbV (fun θ => (bbF0 θ).1.1) ∧
      MonotonicSCF (Θ := fun _ : ι => ℝ) bbU bbF0 ∧
      ∃ Γ : Mechanism (fun _ : ι => MaskinMsg (fun _ : ι => ℝ) (QLAlt ι Bool)) (QLAlt ι Bool),
        StronglyImplementsInNash (Θ := fun _ : ι => ℝ) bbU Γ bbF0 := by
  have hM : MonotonicSCF (Θ := fun _ : ι => ℝ) bbU bbF0 := by
    intro θ θ' hL
    -- the test alternatives: `i` gets `c` from `j`, with the other project choice
    have test : ∀ i, ∃ j, j ≠ i := fun i =>
      Fintype.exists_ne_of_one_lt_card (show 1 < Fintype.card ι by omega) i
    have hfeas : ∀ (i j : ι), j ≠ i → ∀ c : ℝ, ∑ k, update (update (0 : ι → ℝ) j (-c)) i c k ≤ 0 :=
      fun i j hji c => by rw [bb_sum_update, bb_sum_erase_single hji]; simp
    have hkk : bbK θ' = bbK θ := by
      cases hb : bbK θ
      · -- `∑ θ < 0`; lower contour sets of `(0, 0)` expand only if `θ' ≤ θ`
        have hle : ∀ i, θ' i ≤ θ i := by
          intro i
          obtain ⟨j, hji⟩ := test i
          let z : QLAlt ι Bool := ⟨(true, update (update 0 j (-(-θ i))) i (-θ i)),
            hfeas i j hji (-θ i)⟩
          have hz := hL i (show bbU i z (θ i) ≤ bbU i (bbF0 θ) (θ i) by
            simp only [z, bbU, nashQLU, qlU, bbV, bbF0, hb, update_self, ite_true]
            simp)
          have hz' : bbU i z (θ' i) ≤ bbU i (bbF0 θ) (θ' i) := hz
          simp only [z, bbU, nashQLU, qlU, bbV, bbF0, hb, update_self, ite_true] at hz'
          simp at hz'
          linarith
        have hs : ¬(0 ≤ ∑ i, θ i) := by simpa [bbK] using hb
        simp only [bbK, decide_eq_false_iff_not]
        intro h0
        exact hs (h0.trans (Finset.sum_le_sum fun i _ => hle i))
      · have hle : ∀ i, θ i ≤ θ' i := by
          intro i
          obtain ⟨j, hji⟩ := test i
          let z : QLAlt ι Bool := ⟨(false, update (update 0 j (-θ i)) i (θ i)),
            hfeas i j hji (θ i)⟩
          have hz := hL i (show bbU i z (θ i) ≤ bbU i (bbF0 θ) (θ i) by
            simp only [z, bbU, nashQLU, qlU, bbV, bbF0, hb, update_self, ite_true]
            simp)
          have hz' : bbU i z (θ' i) ≤ bbU i (bbF0 θ) (θ' i) := hz
          simp only [z, bbU, nashQLU, qlU, bbV, bbF0, hb, update_self, ite_true] at hz'
          simp at hz'
          linarith
        have hs : 0 ≤ ∑ i, θ i := by simpa [bbK] using hb
        simp only [bbK, decide_eq_true_eq]
        exact hs.trans (Finset.sum_le_sum fun i _ => hle i)
    exact Subtype.ext (by simp only [bbF0, hkk])
  exact ⟨bbK_efficient, hM, proposition_23_BB_3 h3 hM (noVetoPower_ql (by omega) _ _ _)⟩

end MWG.MechanismDesign
