/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Mechanisms
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Bayesian implementation

MWG, Section 23.C (p. 869, (23.C.1), footnote 16) and Section 23.D (pp. 883-885).

Agent `i`'s beliefs about the others' types, conditional on his own type `θᵢ`, are a measure
`B i θᵢ` on type profiles; only the coordinates `θ₋ᵢ` matter, since agent `i`'s own coordinate
is always replaced (by `update · i ·`). With a common prior `φ` this is the conditional
distribution of `θ₋ᵢ` given `θᵢ`; with independent types it is the prior itself
(`Independent.lean`). Conditional expectations `E_{θ₋ᵢ}[· | θᵢ]` are Bochner integrals against
`B i θᵢ`.

* `interimUtility`: `E_{θ₋ᵢ}[uᵢ(g(sᵢ, s₋ᵢ(θ₋ᵢ)), θᵢ) | θᵢ]`.
* **Definitions 23.D.1-23.D.3**: Bayesian Nash equilibrium of a mechanism, implementation in
  Bayesian Nash equilibrium, Bayesian incentive compatibility (23.D.1).
* **Proposition 23.D.1**: the revelation principle for Bayesian Nash equilibrium.
* p. 884: a dominant strategy equilibrium is a Bayesian Nash equilibrium, so dominant
  strategy implementation implies Bayesian implementation (with the expectations defined).
* (23.C.1) and **footnote 16**: weak dominance against all strategies `s₋ᵢ(·)` in expectation is
  equivalent to the ex post condition (23.C.2).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory

variable {ι : Type*} {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)] {X : Type*}
  {S : ι → Type*}

/-- Agent `i`'s interim expected utility, `E_{θ₋ᵢ}[uᵢ(g(a, s₋ᵢ(θ₋ᵢ)), θᵢ) | θᵢ]`, from playing
`a ∈ Sᵢ` when his type is `θᵢ` and the others play `s₋ᵢ(·)`. -/
noncomputable def interimUtility [DecidableEq ι]
    (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)) (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (s : (i : ι) → Θ i → S i) (i : ι) (θi : Θ i) (a : S i) : ℝ :=
  ∫ θ, u i (Γ.outcome (update (play s θ) i a)) θi ∂(B i θi)

/-- **Definition 23.D.1** (MWG, p. 883). `s*(·)` is a Bayesian Nash equilibrium of `Γ`: for all
`i` and `θᵢ`, `E_{θ₋ᵢ}[uᵢ(g(sᵢ*(θᵢ), s₋ᵢ*(θ₋ᵢ)), θᵢ) | θᵢ] ≥ E_{θ₋ᵢ}[uᵢ(g(ŝᵢ, s₋ᵢ*(θ₋ᵢ)), θᵢ) | θᵢ]`
for all `ŝᵢ ∈ Sᵢ`. -/
def IsBayesianNash [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (s : (i : ι) → Θ i → S i) : Prop :=
  ∀ i (θi : Θ i) (a : S i), interimUtility B u Γ s i θi a ≤ interimUtility B u Γ s i θi (s i θi)

/-- **Definition 23.D.2** (MWG, p. 883). `Γ` implements `f` in Bayesian Nash equilibrium. -/
def ImplementsInBNE [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (f : ((i : ι) → Θ i) → X) : Prop :=
  Implements {s | IsBayesianNash B u Γ s} Γ f

/-- **Definition 23.D.3** (MWG, p. 883). `f` is Bayesian incentive compatible (truthfully
implementable in Bayesian Nash equilibrium): condition (23.D.1),
`E_{θ₋ᵢ}[uᵢ(f(θᵢ, θ₋ᵢ), θᵢ) | θᵢ] ≥ E_{θ₋ᵢ}[uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ) | θᵢ]` for all `i`, `θᵢ`, `θ̂ᵢ`. -/
def BayesianIC [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ i (θi θh : Θ i), ∫ θ, u i (f (update θ i θh)) θi ∂(B i θi) ≤
    ∫ θ, u i (f (update θ i θi)) θi ∂(B i θi)

/-- **Definition 23.D.3** (MWG, p. 883). Bayesian incentive compatibility is truth telling being
a Bayesian Nash equilibrium of the direct revelation mechanism. -/
theorem bayesianIC_iff [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    BayesianIC B u f ↔ TruthfullyImplementable {s | IsBayesianNash B u (directMechanism f) s} :=
  Iff.rfl

/-- **Proposition 23.D.1** (The Revelation Principle for Bayesian Nash Equilibrium; MWG,
p. 884). If some mechanism implements `f` in Bayesian Nash equilibrium, then `f` is Bayesian
incentive compatible. -/
theorem proposition_23_D_1 [DecidableEq ι] {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)}
    {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X}
    (h : ImplementsInBNE B u Γ f) : BayesianIC B u f := by
  obtain ⟨s, hs, hf⟩ := h
  intro i θi θh
  -- (23.D.3): deviate to `sᵢ*(θ̂ᵢ)`; then use `g(s*(θ)) = f(θ)` (23.D.4)
  have h3 := hs i θi (s i θh)
  unfold interimUtility at h3
  have e : ∀ (a : Θ i) (θ : (j : ι) → Θ j),
      update (play s θ) i (s i a) = play s (update θ i a) := by
    intro a θ
    funext j
    by_cases hj : j = i
    · subst hj; simp [play]
    · simp [play, update_of_ne hj]
  simp only [e, hf] at h3
  exact h3

/-- **Section 23.D** (MWG, p. 884). Every dominant strategy equilibrium is a Bayesian Nash
equilibrium (when the conditional expectations are defined: the payoffs are integrable for the
beliefs). -/
theorem isBayesianNash_of_dominant [DecidableEq ι] {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)}
    {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X} {s : (i : ι) → Θ i → S i}
    (hs : IsDominantStrategyEquilibrium u Γ s)
    (hint : ∀ i (θi : Θ i) (a : S i),
      Integrable (fun θ => u i (Γ.outcome (update (play s θ) i a)) θi) (B i θi)) :
    IsBayesianNash B u Γ s :=
  fun i θi a => integral_mono (hint i θi a) (hint i θi (s i θi)) fun θ => hs i θi a (play s θ)

/-- **Section 23.D** (MWG, p. 884). A social choice function implementable in dominant strategies
is implementable in Bayesian Nash equilibrium (with integrable payoffs). -/
theorem implementsInBNE_of_dominant [DecidableEq ι]
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {f : ((i : ι) → Θ i) → X}
    (hint : ∀ (s : (i : ι) → Θ i → S i) i (θi : Θ i) (a : S i),
      Integrable (fun θ => u i (Γ.outcome (update (play s θ) i a)) θi) (B i θi))
    (h : ImplementsInDominantStrategies u Γ f) : ImplementsInBNE B u Γ f := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨s, isBayesianNash_of_dominant hs (hint s), hf⟩

/-- **Section 23.D** (MWG, p. 884). A strategy-proof social choice function is Bayesian incentive
compatible (with integrable payoffs). -/
theorem bayesianIC_of_strategyProof [DecidableEq ι]
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hf : StrategyProof u f)
    (hint : ∀ i (θi θh : Θ i), Integrable (fun θ => u i (f (update θ i θh)) θi) (B i θi)) :
    BayesianIC B u f := by
  intro i θi θh
  refine integral_mono (hint i θi θh) (hint i θi θi) fun θ => ?_
  have := hf i (update θ i θi) θh
  simpa using this

/-- **(23.C.1)** (MWG, p. 869). The strategy `sᵢ(·)` is weakly dominant for agent `i` in the
Bayesian sense: for every `θᵢ`, every profile `σ(·)` of the others' strategies (its `i`-th
component is ignored) and every `ŝᵢ`, `E_{θ₋ᵢ}[uᵢ(g(sᵢ(θᵢ), σ₋ᵢ(θ₋ᵢ)), θᵢ) | θᵢ] ≥
E_{θ₋ᵢ}[uᵢ(g(ŝᵢ, σ₋ᵢ(θ₋ᵢ)), θᵢ) | θᵢ]`. -/
def WeaklyDominantInExpectation [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (i : ι) (si : Θ i → S i) : Prop :=
  ∀ (θi : Θ i) (σ : (j : ι) → Θ j → S j) (a : S i),
    ∫ θ, u i (Γ.outcome (update (play σ θ) i a)) θi ∂(B i θi) ≤
      ∫ θ, u i (Γ.outcome (update (play σ θ) i (si θi))) θi ∂(B i θi)

/-- **(23.C.2)** (MWG, p. 870). The ex post form of weak dominance: `uᵢ(g(sᵢ(θᵢ), s₋ᵢ), θᵢ) ≥
uᵢ(g(ŝᵢ, s₋ᵢ), θᵢ)` for every `θᵢ`, `ŝᵢ` and `s₋ᵢ`. -/
def WeaklyDominantExPost [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X)
    (i : ι) (si : Θ i → S i) : Prop :=
  ∀ (θi : Θ i) (σ : (j : ι) → S j) (a : S i),
    u i (Γ.outcome (update σ i a)) θi ≤ u i (Γ.outcome (update σ i (si θi))) θi

/-- **Footnote 16** (MWG, p. 870), first half. Taking constant strategies `s₋ᵢ(θ₋ᵢ) = s₋ᵢ`,
condition (23.C.1) for all `s₋ᵢ(·)` implies (23.C.2) (beliefs are probability measures). -/
theorem footnote_23_16_expost [DecidableEq ι] {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)}
    [∀ i θi, IsProbabilityMeasure (B i θi)] {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X}
    {i : ι} {si : Θ i → S i} (h : WeaklyDominantInExpectation B u Γ i si) :
    WeaklyDominantExPost u Γ i si := by
  intro θi σ a
  have := h θi (fun j _ => σ j) a
  have hc : play (fun j (_ : Θ j) => σ j) = fun (_ : (j : ι) → Θ j) => σ := by
    funext θ j; rfl
  simpa [hc, integral_const] using this

/-- **Footnote 16** (MWG, p. 870), second half. (23.C.2) implies (23.C.1) whenever the
conditional expectations are defined (MWG write them as finite sums when `S₋ᵢ` is finite;
here integrability of the payoffs suffices). -/
theorem footnote_23_16_expectation [DecidableEq ι]
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {Γ : Mechanism S X} {i : ι} {si : Θ i → S i}
    (hint : ∀ (θi : Θ i) (σ : (j : ι) → Θ j → S j) (a : S i),
      Integrable (fun θ => u i (Γ.outcome (update (play σ θ) i a)) θi) (B i θi))
    (h : WeaklyDominantExPost u Γ i si) : WeaklyDominantInExpectation B u Γ i si :=
  fun θi σ a => integral_mono (hint θi σ a) (hint θi σ (si θi)) fun θ => h θi (play σ θ) a

/-- **Footnote 16** (MWG, p. 870), the finite case. With finitely many type profiles (discrete
measurable structure) and finite beliefs, (23.C.1) for all `s₋ᵢ(·)` is equivalent to
(23.C.2). -/
theorem footnote_23_16 [DecidableEq ι] [Finite ((j : ι) → Θ j)]
    [MeasurableSingletonClass ((j : ι) → Θ j)] {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)}
    [∀ i θi, IsProbabilityMeasure (B i θi)] {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X}
    {i : ι} {si : Θ i → S i} :
    WeaklyDominantInExpectation B u Γ i si ↔ WeaklyDominantExPost u Γ i si :=
  ⟨footnote_23_16_expost, footnote_23_16_expectation fun _ _ _ => Integrable.of_finite⟩

end MWG.MechanismDesign
