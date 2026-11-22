import MWGSocialChoice.SocialChoiceFunctions
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import MWGSocialChoice.SinglePeaked
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.MinMax
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The mechanism design problem and dominant strategy implementation

MWG, Section 23.B (pp. 858-869) and the first part of Section 23.C (pp. 869-873).

Agent `i` has a type `θᵢ ∈ Θᵢ` and a Bernoulli utility `uᵢ(x, θᵢ)` over alternatives `x ∈ X`.
We formalize:

* Definitions 23.B.1-23.B.2: social choice functions and ex post efficiency;
  the preference `≿ᵢ(θᵢ)` induced by `uᵢ(·, θᵢ)` and the set `𝓡ᵢ` of such preferences.
* Definitions 23.B.3-23.B.6: mechanisms `Γ = (S₁, …, S_I, g)`, implementation relative to an
  (unspecified) set of equilibria, direct revelation mechanisms and truthful implementation.
* Definitions 23.C.1-23.C.3: dominant strategy equilibria (23.C.2), implementation in dominant
  strategies, strategy-proofness (23.C.3); the revelation principle for dominant strategies
  (Proposition 23.C.1); the weak preference reversal property and its lower-contour-set form
  (Proposition 23.C.2, Exercise 23.C.1).

The `i`-th coordinate of a profile passed to `Function.update _ i _` is ignored, so
`update σ i sᵢ` is MWG's `(sᵢ, s₋ᵢ)`.
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility

variable {ι : Type*} {Θ : ι → Type*} {X : Type*}

/-- **Definition 23.B.1** (MWG, p. 859). A social choice function assigns an alternative
`f(θ₁, …, θ_I) ∈ X` to every profile of types. -/
abbrev SocialChoiceFunction (Θ : ι → Type*) (X : Type*) := ((i : ι) → Θ i) → X

/-- **Definition 23.B.2** (MWG, p. 859). `f` is ex post efficient (Paretian): there is no
profile `θ` and alternative `x` with `uᵢ(x, θᵢ) ≥ uᵢ(f(θ), θᵢ)` for every `i` and `>` for some
`i`. -/
def ExPostEfficient (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ¬∃ θ x, (∀ i, u i (f θ) (θ i) ≤ u i x (θ i)) ∧ ∃ i, u i (f θ) (θ i) < u i x (θ i)

/-- **Section 23.B** (MWG, p. 858). The ordinal preference `≿ᵢ(θᵢ)` induced by `uᵢ(·, θᵢ)`:
`x ≿ᵢ(θᵢ) y` iff `uᵢ(x, θᵢ) ≥ uᵢ(y, θᵢ)`. -/
def inducedPref (u : (i : ι) → X → Θ i → ℝ) (i : ι) (θi : Θ i) : X → X → Prop :=
  fun x y => u i y θi ≤ u i x θi

/-- **Section 23.B** (MWG, p. 858). Agent `i`'s set of possible preference relations,
`𝓡ᵢ = {≿ᵢ : ≿ᵢ = ≿ᵢ(θᵢ) for some θᵢ ∈ Θᵢ}`. -/
def prefSet (u : (i : ι) → X → Θ i → ℝ) (i : ι) : Set (X → X → Prop) :=
  Set.range (inducedPref u i)

/-- **Section 23.B** (MWG, p. 858). Preferences induced by utility functions are rational. -/
theorem inducedPref_rational (u : (i : ι) → X → Θ i → ℝ) (i : ι) (θi : Θ i) :
    Rational (inducedPref u i θi) :=
  ⟨fun x y => le_total (u i y θi) (u i x θi), fun _ _ _ h1 h2 => le_trans h2 h1⟩

/-- **Definition 23.B.2** (MWG, p. 859), unfolded: `f(θ)` is Pareto optimal for the utility
functions `u₁(·, θ₁), …, u_I(·, θ_I)` at every profile. -/
theorem exPostEfficient_iff (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    ExPostEfficient u f ↔ ∀ θ x, (∀ i, u i (f θ) (θ i) ≤ u i x (θ i)) →
      ∀ i, u i x (θ i) ≤ u i (f θ) (θ i) := by
  unfold ExPostEfficient
  constructor
  · intro h θ x hx i
    by_contra hlt
    exact h ⟨θ, x, hx, i, lt_of_not_ge hlt⟩
  · rintro h ⟨θ, x, hx, i, hi⟩
    exact absurd (h θ x hx i) (not_le.2 hi)

variable {S : ι → Type*}

/-- The strategies played at the type profile `θ` under the strategy profile `s(·)`:
`(s₁(θ₁), …, s_I(θ_I))`. -/
def play (s : (i : ι) → Θ i → S i) (θ : (i : ι) → Θ i) : (i : ι) → S i := fun i => s i (θ i)

/-- **Definition 23.B.3** (MWG, p. 866). A mechanism `Γ = (S₁, …, S_I, g(·))`: strategy sets
`Sᵢ` and an outcome function `g : S₁ × ⋯ × S_I → X`. -/
structure Mechanism (S : ι → Type*) (X : Type*) where
  /-- The outcome function `g`. -/
  outcome : ((i : ι) → S i) → X

/-- **Definition 23.B.4** (MWG, p. 867). The mechanism `Γ` implements `f` if some equilibrium
strategy profile `s*(·)` of the game induced by `Γ` (an element of the set `E` of equilibria,
whose solution concept MWG leave unspecified) satisfies `g(s*(θ)) = f(θ)` for all `θ`. -/
def Implements (E : Set ((i : ι) → Θ i → S i)) (Γ : Mechanism S X)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∃ s ∈ E, ∀ θ, Γ.outcome (play s θ) = f θ

/-- **Definition 23.B.5** (MWG, p. 868). The direct revelation mechanism `(Θ₁, …, Θ_I, f(·))`. -/
def directMechanism (f : ((i : ι) → Θ i) → X) : Mechanism Θ X := ⟨f⟩

/-- Truth telling: `sᵢ*(θᵢ) = θᵢ` for all `θᵢ` and `i`. -/
def truthful : (i : ι) → Θ i → Θ i := fun _ => id

/-- Truth telling plays the type profile itself. -/
@[simp] theorem play_truthful (θ : (i : ι) → Θ i) : play truthful θ = θ := rfl

/-- **Definition 23.B.6** (MWG, p. 868). `f` is truthfully implementable when truth telling is an
equilibrium (an element of the set `E` of equilibria) of the direct revelation mechanism. -/
def TruthfullyImplementable (E : Set ((i : ι) → Θ i → Θ i)) : Prop := truthful ∈ E

/-- **Definition 23.B.6** (MWG, p. 868). A truthfully implementable `f` is implemented by its
direct revelation mechanism. -/
theorem implements_of_truthfullyImplementable {E : Set ((i : ι) → Θ i → Θ i)}
    (f : ((i : ι) → Θ i) → X) (h : TruthfullyImplementable E) :
    Implements E (directMechanism f) f :=
  ⟨truthful, h, fun _ => rfl⟩

/-- **Definition 23.C.1** (MWG, p. 870). `s*(·)` is a dominant strategy equilibrium of `Γ`: for
all `i` and `θᵢ`, `uᵢ(g(sᵢ*(θᵢ), s₋ᵢ), θᵢ) ≥ uᵢ(g(sᵢ', s₋ᵢ), θᵢ)` for all `sᵢ'` and `s₋ᵢ`
(condition (23.C.2)). -/
def IsDominantStrategyEquilibrium [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (s : (i : ι) → Θ i → S i) : Prop :=
  ∀ i (θi : Θ i) (s' : S i) (σ : (j : ι) → S j),
    u i (Γ.outcome (update σ i s')) θi ≤ u i (Γ.outcome (update σ i (s i θi))) θi

/-- **Definition 23.C.2** (MWG, p. 870). `Γ` implements `f` in dominant strategies. -/
def ImplementsInDominantStrategies [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (Γ : Mechanism S X) (f : ((i : ι) → Θ i) → X) : Prop :=
  Implements {s | IsDominantStrategyEquilibrium u Γ s} Γ f

/-- **Definition 23.C.3** (MWG, p. 871). `f` is truthfully implementable in dominant strategies
(dominant strategy incentive compatible, strategy-proof): condition (23.C.3),
`uᵢ(f(θᵢ, θ₋ᵢ), θᵢ) ≥ uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ)` for all `i`, `θᵢ`, `θ̂ᵢ` and `θ₋ᵢ`. -/
def StrategyProof [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    Prop :=
  ∀ i (θ : (j : ι) → Θ j) (θh : Θ i), u i (f (update θ i θh)) (θ i) ≤ u i (f θ) (θ i)

/-- **Definition 23.C.3** (MWG, p. 871). Strategy-proofness is exactly truthful implementation
(Definition 23.B.6) with dominant strategy equilibrium as the solution concept: truth telling
is a dominant strategy equilibrium of the direct revelation mechanism. -/
theorem strategyProof_iff_truthfullyImplementable [DecidableEq ι]
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    StrategyProof u f ↔
      TruthfullyImplementable {s | IsDominantStrategyEquilibrium u (directMechanism f) s} := by
  constructor
  · intro h i θi s' σ
    have := h i (update σ i θi) s'
    simpa [directMechanism, truthful] using this
  · intro h i θ θh
    have := h i (θ i) θh θ
    simpa [directMechanism, truthful] using this

/-- **Proposition 23.C.1** (The Revelation Principle for Dominant Strategies; MWG, p. 871). If
some mechanism implements `f` in dominant strategies, then `f` is truthfully implementable in
dominant strategies. -/
theorem proposition_23_C_1 [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ} {Γ : Mechanism S X}
    {f : ((i : ι) → Θ i) → X} (h : ImplementsInDominantStrategies u Γ f) :
    StrategyProof u f := by
  obtain ⟨s, hs, hf⟩ := h
  intro i θ θh
  -- (23.C.5): the strategies `s₋ᵢ*(θ₋ᵢ)` and the deviation `sᵢ*(θ̂ᵢ)`
  have h5 := hs i (θ i) (s i θh) (play s θ)
  have e1 : update (play s θ) i (s i θh) = play s (update θ i θh) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [play]
    · simp [play, update_of_ne hj]
  have e2 : update (play s θ) i (s i (θ i)) = play s θ := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [play]
    · simp [update_of_ne hj]
  rw [e1, e2, hf, hf] at h5
  exact h5

/-- **Section 23.C** (MWG, p. 872). The lower contour set `Lᵢ(x, θᵢ) = {z ∈ X : uᵢ(x, θᵢ) ≥
uᵢ(z, θᵢ)}`. -/
def lowerContour (u : (i : ι) → X → Θ i → ℝ) (i : ι) (x : X) (θi : Θ i) : Set X :=
  {z | u i z θi ≤ u i x θi}

/-- **Section 23.C** (MWG, p. 872). The weak preference reversal property of agent `i`: for all
`θ₋ᵢ` and types `θᵢ', θᵢ''`, `uᵢ(f(θᵢ', θ₋ᵢ), θᵢ') ≥ uᵢ(f(θᵢ'', θ₋ᵢ), θᵢ')`. (Applied to both
orders of the two types it is the reversal of the two outcomes' ranking.) -/
def WeakPreferenceReversal [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ i (θ : (j : ι) → Θ j) (θ' θ'' : Θ i),
    u i (f (update θ i θ'')) θ' ≤ u i (f (update θ i θ')) θ' ∧
      u i (f (update θ i θ')) θ'' ≤ u i (f (update θ i θ'')) θ''

/-- **Exercise 23.C.1** (MWG, p. 918). If the weak preference reversal property holds for all
`i`, all `θᵢ', θᵢ''` and all `θ₋ᵢ`, then `f` is truthfully implementable in dominant
strategies; the converse is the necessity half of the argument on p. 872. -/
theorem exercise_23_C_1 [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) : WeakPreferenceReversal u f ↔ StrategyProof u f := by
  constructor
  · intro h i θ θh
    have := (h i θ (θ i) θh).1
    simpa using this
  · intro h i θ θ' θ''
    refine ⟨?_, ?_⟩
    · have := h i (update θ i θ') θ''
      simpa using this
    · have := h i (update θ i θ'') θ'
      simpa using this

/-- **Proposition 23.C.2** (MWG, p. 872). `f` is truthfully implementable in dominant strategies
iff for all `i`, `θ₋ᵢ` and types `θᵢ', θᵢ''`, condition (23.C.6) holds:
`f(θᵢ'', θ₋ᵢ) ∈ Lᵢ(f(θᵢ', θ₋ᵢ), θᵢ')` and `f(θᵢ', θ₋ᵢ) ∈ Lᵢ(f(θᵢ'', θ₋ᵢ), θᵢ'')`. -/
theorem proposition_23_C_2 [DecidableEq ι] (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) :
    StrategyProof u f ↔ ∀ i (θ : (j : ι) → Θ j) (θ' θ'' : Θ i),
      f (update θ i θ'') ∈ lowerContour u i (f (update θ i θ')) θ' ∧
        f (update θ i θ') ∈ lowerContour u i (f (update θ i θ'')) θ'' :=
  (exercise_23_C_1 u f).symm

/-- A dominant strategy equilibrium of the direct revelation mechanism other than truth telling
need not exist; but strategy-proofness of `f` gives one (truth telling). -/
theorem strategyProof_implements [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (h : StrategyProof u f) :
    ImplementsInDominantStrategies u (directMechanism f) f :=
  implements_of_truthfullyImplementable f
    ((strategyProof_iff_truthfullyImplementable u f).1 h)

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Gibbard-Satterthwaite theorem

MWG, Section 23.C, pp. 873-876: Definitions 23.C.4-23.C.5 (dictatorial and monotonic social
choice functions), Proposition 23.C.3 (the Gibbard-Satterthwaite theorem) by the book's three
steps, and footnote 19.

Types are primitive: agent `i` of type `θᵢ` has utility `uᵢ(·, θᵢ)` and induced preference
`≿ᵢ(θᵢ)`; MWG's hypothesis `𝓡ᵢ = 𝒫` is `prefSet u i = StrictPrefs X`. Step 3 reduces to
Proposition 21.E.1 (imported from Chapter 21): from `f` we build a social choice function on
preference profiles (choosing for each strict preference a type inducing it), show it is weakly
Paretian and monotonic, and transfer the dictator back.

* `gs_step_1`: with `𝓡ᵢ ⊆ 𝒫` (so in particular `𝓡ᵢ = 𝒫`) and finitely many agents, a
  strategy-proof `f` is monotonic (agents' types are changed one at a time).
* `gs_step_2`: with `𝓡ᵢ = 𝒫`, a monotonic onto `f` is ex post efficient.
* `gs_step_3`: with `𝓡ᵢ = 𝒫` and at least three alternatives, a monotonic, ex post efficient
  `f` is dictatorial (Proposition 21.E.1).
* `proposition_23_C_3`: finitely many agents, at least three alternatives, `𝓡ᵢ = 𝒫`,
  `f(Θ) = X`: `f` is strategy-proof iff it is dictatorial.
* `footnote_23_19`: finiteness of `X` is not used: `proposition_23_C_3` holds for any `X`.
  (For uncountable `X` the hypothesis `𝓡ᵢ = 𝒫` has no instance, as the footnote notes via the
  lexicographic order; the Barberà-Peleg continuous-preference version is not formalized.)
* `proposition_23_C_3_instance`: non-vacuity, with `X` finite, the types being the strict
  preferences themselves (represented by rank utilities), and a dictatorial onto rule.
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {ι : Type*} {Θ : ι → Type*} {X : Type*}

/-- **Definition 23.C.4** (MWG, p. 873). `f` is dictatorial: there is an agent `h` with
`f(θ) ∈ {x ∈ X : u_h(x, θ_h) ≥ u_h(y, θ_h) for all y ∈ X}` for all `θ`. -/
def Dictatorial (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∃ h, ∀ θ y, u h y (θ h) ≤ u h (f θ) (θ h)

/-- **Definition 23.C.5** (MWG, p. 873). `f` is monotonic: if `Lᵢ(f(θ), θᵢ) ⊆ Lᵢ(f(θ), θᵢ')`
for all `i`, then `f(θ') = f(θ)`. -/
def MonotonicSCF (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ θ θ', (∀ i, lowerContour u i (f θ) (θ i) ⊆ lowerContour u i (f θ) (θ' i)) → f θ' = f θ

/-- Under `𝓡ᵢ ⊆ 𝒫` no two alternatives are indifferent for any type. -/
theorem eq_of_utility_eq {u : (i : ι) → X → Θ i → ℝ} {i : ι}
    (hR : prefSet u i ⊆ StrictPrefs X) (θi : Θ i) {x y : X} (h : u i x θi = u i y θi) :
    x = y :=
  (hR ⟨θi, rfl⟩).2 x y (show u i y θi ≤ u i x θi from h.ge) (show u i x θi ≤ u i y θi from h.le)

/-- Under `𝓡ᵢ ⊆ 𝒫`, weak preference between distinct alternatives is strict. -/
theorem lt_of_le_of_ne' {u : (i : ι) → X → Θ i → ℝ} {i : ι}
    (hR : prefSet u i ⊆ StrictPrefs X) (θi : Θ i) {x y : X} (h : u i x θi ≤ u i y θi)
    (hne : x ≠ y) : u i x θi < u i y θi :=
  lt_of_le_of_ne h fun he => hne (eq_of_utility_eq hR θi he)

/-- One agent's type change: if `f` is strategy-proof, `≿ᵢ(θᵢ') ∈ 𝒫`, and
`Lᵢ(f(θ), θᵢ) ⊆ Lᵢ(f(θ), θᵢ')`, then `f(θᵢ', θ₋ᵢ) = f(θ)` (Step 1 of the proof of
Proposition 23.C.3, via Proposition 23.C.2). -/
theorem gs_single_change [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hf : StrategyProof u f) {i : ι}
    (θ : (j : ι) → Θ j) (θ' : Θ i) (hθ' : inducedPref u i θ' ∈ StrictPrefs X)
    (hL : lowerContour u i (f θ) (θ i) ⊆ lowerContour u i (f θ) θ') :
    f (update θ i θ') = f θ := by
  have h1 : u i (f (update θ i θ')) θ' ≤ u i (f θ) θ' := hL (hf i θ θ')
  have h2 := hf i (update θ i θ') (θ i)
  rw [update_idem, update_eq_self, update_self] at h2
  exact hθ'.2 _ _ h2 h1

/-- Step 1 of the proof of Proposition 23.C.3 (MWG, p. 874), iterated over a set `T` of agents:
changing the types of the agents in `T` to types `θᵢ'` with `≿ᵢ(θᵢ') ∈ 𝒫` and
`Lᵢ(f(θ), θᵢ) ⊆ Lᵢ(f(θ), θᵢ')` does not change the outcome of a strategy-proof `f`. -/
theorem gs_change_on [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hf : StrategyProof u f) (θ θ' : (j : ι) → Θ j) (T : Finset ι)
    (hstrict : ∀ i ∈ T, inducedPref u i (θ' i) ∈ StrictPrefs X)
    (hL : ∀ i ∈ T, lowerContour u i (f θ) (θ i) ⊆ lowerContour u i (f θ) (θ' i)) :
    f (fun i => if i ∈ T then θ' i else θ i) = f θ := by
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a T haT ih =>
    have ih' := ih (fun i hi => hstrict i (Finset.mem_insert_of_mem hi))
      (fun i hi => hL i (Finset.mem_insert_of_mem hi))
    have hupd : (fun i => if i ∈ insert a T then θ' i else θ i) =
        update (fun i => if i ∈ T then θ' i else θ i) a (θ' a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp
      · simp [hj]
    rw [hupd, ← ih']
    refine gs_single_change hf _ (θ' a) (hstrict a (Finset.mem_insert_self a T)) ?_
    rw [ih']
    simpa [haT] using hL a (Finset.mem_insert_self a T)

/-- **Step 1** of the proof of Proposition 23.C.3 (MWG, p. 874). With finitely many agents and
`𝓡ᵢ ⊆ 𝒫` for all `i`, a strategy-proof `f` is monotonic. -/
theorem gs_step_1 [Finite ι] [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i ⊆ StrictPrefs X)
    (hf : StrategyProof u f) : MonotonicSCF u f := by
  have := Fintype.ofFinite ι
  intro θ θ' hL
  have := gs_change_on hf θ θ' Finset.univ (fun i _ => hR i ⟨θ' i, rfl⟩) (fun i _ => hL i)
  simpa using this

/-- The preference obtained from `r` by taking the set `X'` to the top, keeping the ranking
inside `X'` and outside `X'` (Chapter 21's `topProfile`, for one agent). -/
def topPref (X' : Set X) (r : X → X → Prop) : X → X → Prop :=
  topProfile (ι := Unit) X' (fun _ => r) ()

/-- Taking a set to the top preserves `𝒫`. -/
theorem topPref_mem {X' : Set X} {r : X → X → Prop} (hr : r ∈ StrictPrefs X) :
    topPref X' r ∈ StrictPrefs X :=
  (topProfile_spec (ι := Unit) X' (fun _ => r)).2.2 () hr

/-- An alternative of `X'` is weakly preferred to everything after taking `X'` to the top, if
it is a best alternative of `X'` under `r`. -/
theorem topPref_top {X' : Set X} {r : X → X → Prop} {x : X} (hx : x ∈ X')
    (hbest : ∀ y ∈ X', r x y) (y : X) : topPref X' r x y := by
  by_cases hy : y ∈ X'
  · exact Or.inl ⟨hx, hy, hbest y hy⟩
  · exact Or.inr (Or.inl ⟨hx, hy⟩)

/-- Outside `X'`, the order is unchanged by taking `X'` to the top. -/
theorem topPref_outside {X' : Set X} {r : X → X → Prop} {x y : X} (hx : x ∉ X') (hy : y ∉ X') :
    topPref X' r x y ↔ r x y := by
  unfold topPref topProfile
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩)
    · exact absurd h hx
    · exact absurd h hx
    · exact h
  · exact fun h => Or.inr (Or.inr ⟨hx, hy, h⟩)

/-- The strict preference with `y` first and `x` second, the rest ranked as in `r`. -/
def topTwo (y x : X) (r : X → X → Prop) : X → X → Prop := topPref {y} (topPref {x, y} r)

/-- `topTwo y x r ∈ 𝒫` when `r ∈ 𝒫`. -/
theorem topTwo_mem {y x : X} {r : X → X → Prop} (hr : r ∈ StrictPrefs X) :
    topTwo y x r ∈ StrictPrefs X :=
  topPref_mem (topPref_mem hr)

/-- Under `topTwo y x r`, `y` is ranked above everything. -/
theorem topTwo_first {y x : X} {r : X → X → Prop} (hr : r ∈ StrictPrefs X) (z : X) :
    topTwo y x r y z :=
  topPref_top (X' := {y}) (Set.mem_singleton y) (fun w hw => by
    rw [Set.mem_singleton_iff.1 hw]
    exact (topPref_mem hr).1.1 _ _ |>.elim id id) z

/-- Under `topTwo y x r` with `x ≠ y`, `x` is ranked above everything but `y`. -/
theorem topTwo_second {y x : X} {r : X → X → Prop} (hr : r ∈ StrictPrefs X) (hxy : x ≠ y)
    {z : X} (hz : z ≠ y) : topTwo y x r x z := by
  unfold topTwo
  rw [topPref_outside (by simpa using hxy) (by simpa using hz)]
  by_cases hzX : z ∈ ({x, y} : Set X)
  · have hzx : z = x := by
      rcases hzX with h | h
      · exact h
      · exact absurd h hz
    subst hzx
    exact (topPref_mem hr).1.1 _ _ |>.elim id id
  · exact Or.inr (Or.inl ⟨Or.inl rfl, hzX⟩)

/-- Under `𝓡ᵢ = 𝒫`, a type inducing a given strict preference. -/
theorem exists_type_of_pref {u : (i : ι) → X → Θ i → ℝ} {i : ι}
    (hR : prefSet u i = StrictPrefs X) {r : X → X → Prop} (hr : r ∈ StrictPrefs X) :
    ∃ θi, ∀ x y, u i y θi ≤ u i x θi ↔ r x y := by
  rw [← hR] at hr
  obtain ⟨θi, hθ⟩ := hr
  exact ⟨θi, fun x y => by rw [← hθ]; rfl⟩

/-- **Step 2** of the proof of Proposition 23.C.3 (MWG, pp. 874-875). With `𝓡ᵢ = 𝒫` for all `i`,
a monotonic `f` with `f(Θ) = X` is ex post efficient. -/
theorem gs_step_2 {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hR : ∀ i, prefSet u i = StrictPrefs X) (hM : MonotonicSCF u f)
    (hon : Surjective f) : ExPostEfficient u f := by
  rintro ⟨θ, y, hy, j, hj⟩
  have hyx : y ≠ f θ := fun h => by rw [h] at hj; exact lt_irrefl _ hj
  -- every agent strictly prefers `y` to `f θ` (no indifference)
  have hstrict : ∀ i, u i (f θ) (θ i) < u i y (θ i) :=
    fun i => lt_of_le_of_ne' (hR i).le (θ i) (hy i) hyx.symm
  obtain ⟨θ', hθ'⟩ := hon y
  -- types ranking `y` first and `f θ` second
  have hex : ∀ i, ∃ θi, ∀ x z, u i z θi ≤ u i x θi ↔
      topTwo y (f θ) (inducedPref u i (θ i)) x z := fun i =>
    exists_type_of_pref (hR i) (topTwo_mem (by rw [← hR i]; exact ⟨θ i, rfl⟩))
  choose θ'' hθ'' using hex
  have h1 : f θ'' = y := by
    rw [← hθ']
    refine hM θ' θ'' fun i z _ => ?_
    rw [hθ']
    exact (hθ'' i y z).2 (topTwo_first (by rw [← hR i]; exact ⟨θ i, rfl⟩) z)
  have h2 : f θ'' = f θ := by
    refine hM θ θ'' fun i z hz => ?_
    have hzy : z ≠ y := fun h => by
      rw [h] at hz
      exact absurd hz (not_le.2 (hstrict i))
    exact (hθ'' i (f θ) z).2
      (topTwo_second (by rw [← hR i]; exact ⟨θ i, rfl⟩) hyx.symm hzy)
  exact hyx (h1.symm.trans h2)

/-- **Step 3** of the proof of Proposition 23.C.3 (MWG, p. 875). With finitely many agents, at
least three alternatives and `𝓡ᵢ = 𝒫`, a monotonic and ex post efficient `f` is dictatorial;
this is Proposition 21.E.1, applied to the social choice function on preference profiles
induced by `f`. -/
theorem gs_step_3 [Finite ι] [Nonempty ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hR : ∀ i, prefSet u i = StrictPrefs X) (hM : MonotonicSCF u f)
    (hE : ExPostEfficient u f) : Dictatorial u f := by
  classical
  -- a type for each strict preference
  have hex : ∀ i (r : {r : X → X → Prop // r ∈ StrictPrefs X}),
      ∃ θi, ∀ x y, u i y θi ≤ u i x θi ↔ r.1 x y :=
    fun i r => exists_type_of_pref (hR i) r.2
  choose τ hτ using hex
  obtain ⟨x₀, -⟩ := id hX
  let typesOf : (p : Profile ι X) → p ∈ StrictProfiles ι X → (i : ι) → Θ i :=
    fun p hp i => τ i ⟨p i, hp i⟩
  let F : Profile ι X → X :=
    fun p => if hp : p ∈ StrictProfiles ι X then f (typesOf p hp) else x₀
  have hF : ∀ p (hp : p ∈ StrictProfiles ι X), F p = f (typesOf p hp) := by
    intro p hp
    simp [F, hp]
  have hpref : ∀ p (hp : p ∈ StrictProfiles ι X) i x y,
      u i y (typesOf p hp i) ≤ u i x (typesOf p hp i) ↔ p i x y :=
    fun p hp i x y => hτ i ⟨p i, hp i⟩ x y
  have hW : WeaklyParetian (StrictProfiles ι X) F := by
    intro p hp x y hxy hyF
    rw [hF p hp] at hyF
    rw [exPostEfficient_iff] at hE
    have hall : ∀ i, u i (f (typesOf p hp)) (typesOf p hp i) ≤ u i x (typesOf p hp i) := by
      intro i
      rw [← hyF, hpref p hp i x y]
      exact (hxy i).1
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hE (typesOf p hp) x hall i
    rw [← hyF, hpref p hp i y x] at this
    exact (hxy i).2 this
  have hMF : MWG.SocialChoice.Monotonic (StrictProfiles ι X) F := by
    intro p hp p' hp' hmain
    rw [hF p hp, hF p' hp']
    refine hM _ _ fun i z hz => ?_
    have h1 : p i (F p) z := by rw [hF p hp]; exact (hpref p hp i _ z).1 hz
    have h2 := hmain i z h1
    rw [hF p hp] at h2
    exact (hpref p' hp' i _ z).2 h2
  obtain ⟨h, hh⟩ := proposition_21_E_1 hX (Or.inr rfl) hW hMF
  refine ⟨h, fun θ y => ?_⟩
  let p : Profile ι X := fun i => inducedPref u i (θ i)
  have hp : p ∈ StrictProfiles ι X := fun i => by rw [← hR i]; exact ⟨θ i, rfl⟩
  have hfp : f (typesOf p hp) = f θ := by
    symm
    refine hM _ _ fun i z hz => ?_
    exact (hpref p hp i _ z).1 hz
  have := hh p hp y
  rw [hF p hp, hfp] at this
  exact this

/-- Under `𝓡ᵢ ⊆ 𝒫`, a dictatorial social choice function is strategy-proof: the dictator's
choice is his unique best alternative, so it depends on his type only. ("It is immediate",
MWG, p. 874.) -/
theorem strategyProof_of_dictatorial [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i ⊆ StrictPrefs X)
    (hD : Dictatorial u f) : StrategyProof u f := by
  obtain ⟨h, hh⟩ := hD
  -- the dictator's choice depends only on his own type
  have hdep : ∀ θ θ' : (i : ι) → Θ i, θ h = θ' h → f θ = f θ' := by
    intro θ θ' he
    have h1 := hh θ (f θ')
    have h2 := hh θ' (f θ)
    rw [← he] at h2
    exact eq_of_utility_eq (hR h) (θ h) (le_antisymm h2 h1)
  intro i θ θh
  by_cases hi : i = h
  · subst hi
    exact hh θ _
  · rw [hdep (update θ i θh) θ (by rw [update_of_ne (Ne.symm hi)])]

/-- **Proposition 23.C.3** (The Gibbard-Satterthwaite Theorem; MWG, p. 874). Suppose there are
finitely many agents, `X` contains at least three elements, `𝓡ᵢ = 𝒫` for all `i`, and
`f(Θ) = X`. Then `f` is truthfully implementable in dominant strategies iff it is dictatorial.
(MWG also assume `X` finite; that is not needed, see `footnote_23_19`.) -/
theorem proposition_23_C_3 [Finite ι] [Nonempty ι] [DecidableEq ι]
    (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i = StrictPrefs X) (hon : Surjective f) :
    StrategyProof u f ↔ Dictatorial u f := by
  constructor
  · intro hf
    have hM := gs_step_1 (fun i => (hR i).le) hf
    exact gs_step_3 hX hR hM (gs_step_2 hR hM hon)
  · exact strategyProof_of_dictatorial fun i => (hR i).le

/-- **Footnote 19** (MWG, p. 874). Finiteness of `X` is not required: Proposition 23.C.3 holds
for an arbitrary set of alternatives (this is `proposition_23_C_3`, which has no finiteness
assumption on `X`). -/
theorem footnote_23_19 [Finite ι] [Nonempty ι] [DecidableEq ι]
    (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i = StrictPrefs X) (hon : Surjective f) :
    StrategyProof u f ↔ Dictatorial u f :=
  proposition_23_C_3 hX hR hon

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Rank utilities and the non-vacuity of the Gibbard-Satterthwaite theorem

MWG, Section 23.C, pp. 873-875, and Exercises 23.C.3-23.C.4 (p. 919).

On a finite set of alternatives every rational preference is represented by its rank utility
`u(x) = #{y : x ≿ y}`. Taking the types of each agent to be the strict preferences themselves
gives `𝓡ᵢ = 𝒫`, the hypothesis of Proposition 23.C.3; a dictator's top choice is then a
strategy-proof, dictatorial and onto social choice function (`proposition_23_C_3_instance`).

* **Exercise 23.C.3**: with `𝓡ᵢ = 𝒫`, an ex post efficient `f` is onto.
* **Exercise 23.C.4**: strategy-proofness survives restricting the type sets.
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {X : Type*}

/-- The rank utility of a preference on a finite set: the number of alternatives weakly below. -/
noncomputable def rankUtil [Fintype X] (r : X → X → Prop) (x : X) : ℝ := by
  classical exact ((Finset.univ.filter fun y => r x y).card : ℝ)

/-- The rank utility represents a rational preference on a finite set. -/
theorem rankUtil_le_iff [Fintype X] {r : X → X → Prop} (hr : Rational r) (x y : X) :
    rankUtil r y ≤ rankUtil r x ↔ r x y := by
  classical
  unfold rankUtil
  constructor
  · intro h
    by_contra hxy
    have hyx : r y x := (hr.1 x y).resolve_left hxy
    have hsub : Finset.univ.filter (fun z => r x z) ⊂ Finset.univ.filter (fun z => r y z) := by
      refine Finset.ssubset_iff_of_subset (fun z hz => ?_) |>.2 ⟨y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hr.2 _ _ _ hyx hz
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hr.1 y y).elim id id
      · simpa using hxy
    have := Finset.card_lt_card hsub
    have h' : ((Finset.univ.filter fun z => r x z).card : ℝ) <
        ((Finset.univ.filter fun z => r y z).card : ℝ) := by exact_mod_cast this
    linarith
  · intro h
    have hsub : Finset.univ.filter (fun z => r y z) ⊆ Finset.univ.filter (fun z => r x z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hr.2 _ _ _ h hz
    exact_mod_cast Finset.card_le_card hsub

/-- The type set "all strict preferences". -/
abbrev StrictType (X : Type*) := {r : X → X → Prop // r ∈ StrictPrefs X}

/-- The type set "all rational preferences". -/
abbrev RationalType (X : Type*) := {r : X → X → Prop // r ∈ RationalPrefs X}

/-- Rank utilities with strict-preference types. -/
noncomputable def rankU [Fintype X] (ι : Type*) : (i : ι) → X → StrictType X → ℝ :=
  fun _ x θ => rankUtil θ.1 x

/-- With strict-preference types and rank utilities, `𝓡ᵢ = 𝒫`. -/
theorem prefSet_rankU [Fintype X] (ι : Type*) (i : ι) :
    prefSet (rankU (X := X) ι) i = StrictPrefs X := by
  ext r
  constructor
  · rintro ⟨θ, rfl⟩
    have : inducedPref (rankU ι) i θ = θ.1 := by
      funext x y
      exact propext (rankUtil_le_iff θ.2.1 x y)
    rw [this]
    exact θ.2
  · intro hr
    refine ⟨⟨r, hr⟩, ?_⟩
    funext x y
    exact propext (rankUtil_le_iff hr.1 x y)

/-- A best alternative under a preference on a finite nonempty set (maximal rank utility). -/
noncomputable def topOf [Fintype X] [Nonempty X] (r : X → X → Prop) : X :=
  (Finset.exists_max_image Finset.univ (rankUtil r) Finset.univ_nonempty).choose

/-- `topOf r` maximizes the rank utility. -/
theorem topOf_spec [Fintype X] [Nonempty X] (r : X → X → Prop) (y : X) :
    rankUtil r y ≤ rankUtil r (topOf r) :=
  (Finset.exists_max_image Finset.univ (rankUtil r) Finset.univ_nonempty).choose_spec.2 y
    (Finset.mem_univ y)

/-- Taking `{x}` to the top puts `x` above everything. -/
theorem topPref_singleton_top {r : X → X → Prop} (hr : Rational r) (x y : X) :
    topPref {x} r x y :=
  topPref_top (X' := {x}) rfl (fun w hw => by
    rw [Set.mem_singleton_iff.1 hw]
    exact (hr.1 x x).elim id id) y

/-- A strict preference with `x` on top exists (take `x` to the top of any strict preference). -/
theorem exists_strict_top (x : X) : ∃ r ∈ StrictPrefs X, ∀ y, r x y :=
  ⟨topPref {x} (scorePref fun _ => 0), topPref_mem (scorePref_mem _),
    topPref_singleton_top (scorePref_mem _).1 x⟩

/-- The dictatorial rule "agent `h`'s best alternative" with strict-preference types. -/
noncomputable def dictatorRule [Fintype X] [Nonempty X] {ι : Type*} (h : ι)
    (θ : ι → StrictType X) : X :=
  topOf (θ h).1

/-- **Proposition 23.C.3**, non-vacuity (MWG, p. 874). With three alternatives, two agents whose
types are all strict preferences (`𝓡ᵢ = 𝒫`), the rule "agent 0's best alternative" is onto,
strategy-proof and dictatorial. -/
theorem proposition_23_C_3_instance :
    (∀ i, prefSet (rankU (X := Fin 3) (Fin 2)) i = StrictPrefs (Fin 3)) ∧
      Surjective (dictatorRule (X := Fin 3) (0 : Fin 2)) ∧
      StrategyProof (rankU (Fin 2)) (dictatorRule (X := Fin 3) (0 : Fin 2)) ∧
      Dictatorial (rankU (Fin 2)) (dictatorRule (X := Fin 3) (0 : Fin 2)) := by
  have hR := prefSet_rankU (X := Fin 3) (Fin 2)
  have hD : Dictatorial (rankU (Fin 2)) (dictatorRule (X := Fin 3) (0 : Fin 2)) :=
    ⟨0, fun θ y => topOf_spec (θ 0).1 y⟩
  refine ⟨hR, fun x => ?_, strategyProof_of_dictatorial (fun i => (hR i).le) hD, hD⟩
  obtain ⟨r, hr, htop⟩ := exists_strict_top x
  refine ⟨fun _ => ⟨r, hr⟩, ?_⟩
  have h1 := topOf_spec r x
  have h2 : rankUtil r (topOf r) ≤ rankUtil r x := (rankUtil_le_iff hr.1 x _).2 (htop _)
  exact hr.2 _ _ ((rankUtil_le_iff hr.1 _ _).1 h1) ((rankUtil_le_iff hr.1 _ _).1 h2)

variable {ι : Type*} {Θ : ι → Type*}

/-- **Exercise 23.C.3** (MWG, p. 919). With `𝓡ᵢ = 𝒫` for all `i` (and at least one agent), any
ex post efficient social choice function has `f(Θ) = X`. -/
theorem exercise_23_C_3 [Nonempty ι] {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hR : ∀ i, prefSet u i = StrictPrefs X) (hE : ExPostEfficient u f) : Surjective f := by
  intro x
  have hex : ∀ i, ∃ θi, ∀ a b, u i b θi ≤ u i a θi ↔ topPref {x} (scorePref fun _ => 0) a b :=
    fun i => exists_type_of_pref (hR i) (topPref_mem (scorePref_mem _))
  choose θ hθ using hex
  refine ⟨θ, ?_⟩
  by_contra hne
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hx : ∀ i, u i (f θ) (θ i) ≤ u i x (θ i) := fun i => (hθ i x (f θ)).2
    (topPref_singleton_top (scorePref_mem _).1 x (f θ))
  exact hE ⟨θ, x, hx, i₀, lt_of_le_of_ne' (hR i₀).le (θ i₀) (hx i₀) hne⟩

/-- **Exercise 23.C.4** (MWG, p. 919). If `f` is strategy-proof on `Θ₁ × ⋯ × Θ_I`, its
restriction to `Θ̂₁ × ⋯ × Θ̂_I` (`Θ̂ᵢ ⊆ Θᵢ`) is strategy-proof. -/
theorem exercise_23_C_4 [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hf : StrategyProof u f) (Θh : (i : ι) → Set (Θ i)) :
    StrategyProof (fun i x (θi : Θh i) => u i x θi.1)
      (fun θ : (i : ι) → Θh i => f fun i => (θ i).1) := by
  intro i θ θh
  have := hf i (fun j => (θ j).1) θh.1
  have e : (fun j => (update θ i θh j).1) = update (fun j => (θ j).1) i θh.1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simpa [e] using this

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extensions of the Gibbard-Satterthwaite theorem

MWG, Section 23.C, pp. 875-876 (small type): Corollaries 23.C.1-23.C.2 and Definition 23.C.6.

* **Corollary 23.C.1** (`corollary_23_C_1`): with `X` finite with at least three elements,
  `𝒫 ⊆ 𝓡ᵢ` for all `i` and `f(Θ) = X`, a strategy-proof `f` is dictatorial. The proof follows
  the book: restrict to the types with strict preferences (Exercise 23.C.4), where the
  restriction is still onto (one agent at a time, Step 1), apply Proposition 23.C.3, and extend
  the dictatorship to all types with the profile `θ''`.
* **Correction.** The converse ("it is again immediate that a dictatorial social choice function
  is truthfully implementable") is false once indifference is allowed: the dictator's
  indifference can be broken by the others' reports (`corollary_23_C_1_converse_false`). It
  holds when `𝓡ᵢ ⊆ 𝒫` (`strategyProof_of_dictatorial`).
* **Definition 23.C.6** and **Corollary 23.C.2** (`corollary_23_C_2`): with `X` finite,
  `|f(Θ)| ≥ 3` and `𝒫 ⊆ 𝓡ᵢ`, a strategy-proof `f` is dictatorial on `f(Θ)`. The converse is
  false in the same way (`corollary_23_C_2_converse_false`) and true under `𝓡ᵢ ⊆ 𝒫`
  (`strategyProof_of_dictatorialOn`).
-/

namespace MWG.MechanismDesign

open Function Kreps.ChoicePreferenceUtility MWG.SocialChoice

variable {ι : Type*} {Θ : ι → Type*} {X : Type*}

/-- **Corollary 23.C.1** (MWG, p. 875). Suppose there are finitely many agents, `X` is finite
with at least three elements, `𝒫 ⊆ 𝓡ᵢ` for all `i`, and `f(Θ) = X`. If `f` is truthfully
implementable in dominant strategies, it is dictatorial. -/
theorem corollary_23_C_1 [Finite ι] [Nonempty ι] [DecidableEq ι] [Finite X]
    (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c) {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, StrictPrefs X ⊆ prefSet u i) (hon : Surjective f)
    (hf : StrategyProof u f) : Dictatorial u f := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite X
  -- the types with strict preferences (Exercise 23.C.4)
  let Θh : (i : ι) → Set (Θ i) := fun i => {θi | inducedPref u i θi ∈ StrictPrefs X}
  let uh : (i : ι) → X → Θh i → ℝ := fun i x θi => u i x θi.1
  let fh : ((i : ι) → Θh i) → X := fun θ => f fun i => (θ i).1
  have hRh : ∀ i, prefSet uh i = StrictPrefs X := by
    intro i
    ext r
    constructor
    · rintro ⟨θi, rfl⟩
      exact θi.2
    · intro hr
      obtain ⟨θi, hθi⟩ := hR i hr
      exact ⟨⟨θi, show inducedPref u i θi ∈ StrictPrefs X by rw [hθi]; exact hr⟩, hθi⟩
  have hfh : StrategyProof uh fh := exercise_23_C_4 hf Θh
  -- strict types putting a given alternative on top
  have htop : ∀ (i : ι) (x : X), ∃ θi : Θ i,
      inducedPref u i θi = topPref {x} (scorePref fun _ => 0) :=
    fun i x => hR i (topPref_mem (scorePref_mem _))
  choose τ hτ using htop
  have hτs : ∀ i x, inducedPref u i (τ i x) ∈ StrictPrefs X := fun i x => by
    rw [hτ i x]; exact topPref_mem (scorePref_mem _)
  have hτtop : ∀ i x z, u i z (τ i x) ≤ u i x (τ i x) := fun i x z => by
    have : inducedPref u i (τ i x) x z := by
      rw [hτ i x]; exact topPref_singleton_top (scorePref_mem _).1 x z
    exact this
  -- the restriction is onto
  have honh : Surjective fh := by
    intro x
    obtain ⟨θ, hθ⟩ := hon x
    refine ⟨fun i => ⟨τ i x, hτs i x⟩, ?_⟩
    have := gs_change_on hf θ (fun i => τ i x) Finset.univ (fun i _ => hτs i x)
      (fun i _ z _ => by
        change u i z (τ i x) ≤ u i (f θ) (τ i x)
        rw [hθ]; exact hτtop i x z)
    simpa [fh, hθ] using this
  obtain ⟨h, hh⟩ := (proposition_23_C_3 hX hRh honh).1 hfh
  refine ⟨h, fun θ y => ?_⟩
  by_contra hcon'
  have hcon := lt_of_not_ge hcon'
  obtain ⟨z, -, hz⟩ := Finset.exists_max_image Finset.univ (fun w => u h w (θ h))
    ⟨y, Finset.mem_univ y⟩
  -- the profile `θ''`: agents `i ≠ h` put `f θ` on top, agent `h` puts `z` on top
  let θ'' : (i : ι) → Θ i := fun i => if i = h then τ i z else τ i (f θ)
  have hs : ∀ i, inducedPref u i (θ'' i) ∈ StrictPrefs X := fun i => by
    by_cases hi : i = h
    · subst hi; simpa [θ''] using hτs i z
    · simpa [θ'', hi] using hτs i (f θ)
  let θ3 : (i : ι) → Θ i := fun i => if i ∈ Finset.univ.erase h then θ'' i else θ i
  have h1 : f θ3 = f θ := gs_change_on hf θ θ'' (Finset.univ.erase h) (fun i _ => hs i)
    (fun i hi w _ => by
      have hih : i ≠ h := Finset.ne_of_mem_erase hi
      change u i w (θ'' i) ≤ u i (f θ) (θ'' i)
      simpa [θ'', hih] using hτtop i (f θ) w)
  have h2 : f θ'' = z := by
    have hd := hh (fun i => ⟨θ'' i, hs i⟩) z
    have hzt : u h (f θ'') (θ'' h) ≤ u h z (θ'' h) := by
      simpa [θ''] using hτtop h z (f θ'')
    exact (hs h).2 _ _ hd hzt
  have h3 := hf h θ3 (θ'' h)
  have e1 : update θ3 h (θ'' h) = θ'' := by
    funext j
    by_cases hj : j = h
    · subst hj; simp
    · simp [θ3, hj]
  have e2 : θ3 h = θ h := by simp [θ3]
  rw [e1, h2, h1, e2] at h3
  exact absurd (lt_of_lt_of_le hcon (hz y (Finset.mem_univ y))) (not_lt.2 h3)

/-- The worst alternative under a preference on a finite nonempty set (minimal rank utility). -/
noncomputable def botOf [Fintype X] [Nonempty X] (r : X → X → Prop) : X :=
  (Finset.exists_min_image Finset.univ (rankUtil r) Finset.univ_nonempty).choose

/-- `botOf r` minimizes the rank utility. -/
theorem botOf_spec [Fintype X] [Nonempty X] (r : X → X → Prop) (y : X) :
    rankUtil r (botOf r) ≤ rankUtil r y :=
  (Finset.exists_min_image Finset.univ (rankUtil r) Finset.univ_nonempty).choose_spec.2 y
    (Finset.mem_univ y)

/-- Types for the counterexample: a strict preference, or total indifference (`none`). -/
noncomputable def optU : (i : Fin 2) → Fin 3 → Option (StrictType (Fin 3)) → ℝ :=
  fun _ x θ => θ.elim 0 fun r => rankUtil r.1 x

/-- The counterexample rule: agent 0's best alternative if he has a strict preference; if agent
0 is indifferent among all alternatives, agent 1's *worst* alternative. -/
noncomputable def tieBreakRule (θ : Fin 2 → Option (StrictType (Fin 3))) : Fin 3 :=
  (θ 0).elim ((θ 1).elim 0 fun r => botOf r.1) fun r => topOf r.1

/-- A strict preference with `0` at the bottom. -/
def zeroBottom : StrictType (Fin 3) :=
  ⟨natPref Fin.val, natPref_mem_strict Fin.val_injective⟩

/-- A strict preference with `0` at the top. -/
def zeroTop : StrictType (Fin 3) :=
  ⟨topPref {0} (scorePref fun _ => 0), topPref_mem (scorePref_mem _)⟩

/-- **Corollary 23.C.1**, correction (MWG, p. 875). The converse fails when indifference is
allowed: with `𝒫 ⊆ 𝓡ᵢ` (strict preferences and total indifference), `f(Θ) = X`, three
alternatives and two agents, `tieBreakRule` is dictatorial (agent 0) but not strategy-proof:
when agent 0 is indifferent, agent 1 gains by reporting a preference with his best alternative at
the bottom. -/
theorem corollary_23_C_1_converse_false :
    (∀ i, StrictPrefs (Fin 3) ⊆ prefSet optU i) ∧ Surjective tieBreakRule ∧
      Dictatorial optU tieBreakRule ∧ ¬StrategyProof optU tieBreakRule := by
  have hsome : ∀ (i : Fin 2) (r : StrictType (Fin 3)), inducedPref optU i (some r) = r.1 := by
    intro i r
    funext x y
    exact propext (rankUtil_le_iff r.2.1 x y)
  refine ⟨fun i r hr => ⟨some ⟨r, hr⟩, hsome i ⟨r, hr⟩⟩, fun x => ?_, ⟨0, fun θ y => ?_⟩, ?_⟩
  · obtain ⟨r, hr, htop⟩ := exists_strict_top x
    refine ⟨fun _ => some ⟨r, hr⟩, ?_⟩
    change topOf r = x
    exact hr.2 _ _ ((rankUtil_le_iff hr.1 _ _).1 (topOf_spec r x))
      ((rankUtil_le_iff hr.1 _ _).1 ((rankUtil_le_iff hr.1 x _).2 (htop _)))
  · cases h0 : θ 0 with
    | none => simp [optU]
    | some r => simp only [optU, h0, tieBreakRule, Option.elim]; exact topOf_spec r.1 y
  · intro hSP
    let θ : Fin 2 → Option (StrictType (Fin 3)) := ![none, some zeroTop]
    have h := hSP 1 θ (some zeroBottom)
    have hb : tieBreakRule (update θ 1 (some zeroBottom)) = 0 := by
      change botOf zeroBottom.1 = 0
      have h1 := botOf_spec zeroBottom.1 0
      have h2 : rankUtil zeroBottom.1 0 ≤ rankUtil zeroBottom.1 (botOf zeroBottom.1) :=
        (rankUtil_le_iff zeroBottom.2.1 _ _).2 (Nat.zero_le _)
      exact zeroBottom.2.2 _ _ ((rankUtil_le_iff zeroBottom.2.1 _ _).1 h2)
        ((rankUtil_le_iff zeroBottom.2.1 _ _).1 h1)
    have htop0 : ∀ y, rankUtil zeroTop.1 y ≤ rankUtil zeroTop.1 0 := fun y =>
      (rankUtil_le_iff zeroTop.2.1 _ _).2 (topPref_singleton_top (scorePref_mem _).1 0 y)
    have hbot : tieBreakRule θ = botOf zeroTop.1 := rfl
    have hne : botOf zeroTop.1 ≠ 0 := by
      intro he
      have h1 := botOf_spec zeroTop.1 1
      rw [he] at h1
      have := zeroTop.2.2 0 1 ((rankUtil_le_iff zeroTop.2.1 _ _).1 (htop0 1))
        ((rankUtil_le_iff zeroTop.2.1 _ _).1 h1)
      exact absurd this (by decide)
    rw [hb, hbot] at h
    have hθ1 : θ 1 = some zeroTop := rfl
    simp only [optU, hθ1, Option.elim] at h
    have hlt : rankUtil zeroTop.1 (botOf zeroTop.1) < rankUtil zeroTop.1 0 :=
      lt_of_le_of_ne (htop0 _) fun he => hne (zeroTop.2.2 _ _
        ((rankUtil_le_iff zeroTop.2.1 _ _).1 he.ge) ((rankUtil_le_iff zeroTop.2.1 _ _).1 he.le))
    exact absurd h (not_le.2 hlt)

/-- A strict preference on `X` extending a strict preference `r` on `Y ⊆ X`: `Y` is ranked above
its complement, `r` inside `Y` and `s` outside. -/
def extendPref (Y : Set X) (r : Y → Y → Prop) (s : X → X → Prop) : X → X → Prop :=
  fun a b => (∃ ha : a ∈ Y, ∃ hb : b ∈ Y, r ⟨a, ha⟩ ⟨b, hb⟩) ∨ (a ∈ Y ∧ b ∉ Y) ∨
    (a ∉ Y ∧ b ∉ Y ∧ s a b)

/-- `extendPref Y r s ∈ 𝒫` when `r ∈ 𝒫(Y)` and `s ∈ 𝒫(X)`. -/
theorem extendPref_mem {Y : Set X} {r : Y → Y → Prop} {s : X → X → Prop}
    (hr : r ∈ StrictPrefs Y) (hs : s ∈ StrictPrefs X) : extendPref Y r s ∈ StrictPrefs X := by
  refine ⟨⟨fun a b => ?_, fun a b c hab hbc => ?_⟩, fun a b hab hba => ?_⟩
  · by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y
    · rcases hr.1.1 ⟨a, ha⟩ ⟨b, hb⟩ with h | h
      · exact Or.inl (Or.inl ⟨ha, hb, h⟩)
      · exact Or.inr (Or.inl ⟨hb, ha, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
    · rcases hs.1.1 a b with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, h⟩))
  · rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
      rcases hbc with ⟨hb', hc, h2⟩ | ⟨hb', hc⟩ | ⟨hb', hc, h2⟩
    all_goals first
      | exact absurd hb' hb | exact absurd hb hb'
      | exact Or.inl ⟨ha, hc, hr.1.2 _ _ _ h1 h2⟩
      | exact Or.inr (Or.inl ⟨ha, hc⟩)
      | exact Or.inr (Or.inr ⟨ha, hc, hs.1.2 a b c h1 h2⟩)
  · rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
      rcases hba with ⟨hb', ha', h2⟩ | ⟨hb', ha'⟩ | ⟨hb', ha', h2⟩
    all_goals first
      | exact congrArg Subtype.val (hr.2 _ _ h1 h2)
      | exact hs.2 a b h1 h2
      | (exfalso; tauto)

/-- `extendPref Y r s` restricts to `r` on `Y`. -/
theorem extendPref_restrict {Y : Set X} {r : Y → Y → Prop} {s : X → X → Prop} (a b : Y) :
    extendPref Y r s a.1 b.1 ↔ r a b := by
  constructor
  · rintro (⟨ha, hb, h⟩ | ⟨-, hb⟩ | ⟨ha, -⟩)
    · exact h
    · exact absurd b.2 hb
    · exact absurd a.2 ha
  · exact fun h => Or.inl ⟨a.2, b.2, h⟩

/-- **Definition 23.C.6** (MWG, p. 876). `f` is dictatorial on `X̂ ⊆ X`: some agent `h` has
`f(θ) ∈ {x ∈ X̂ : u_h(x, θ_h) ≥ u_h(y, θ_h) for all y ∈ X̂}` for all `θ`. -/
def DictatorialOn (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) (Xh : Set X) :
    Prop :=
  ∃ h, ∀ θ, f θ ∈ Xh ∧ ∀ y ∈ Xh, u h y (θ h) ≤ u h (f θ) (θ h)

/-- **Corollary 23.C.2** (MWG, p. 876). Suppose there are finitely many agents, `X` is finite,
`f(Θ)` has at least three elements and `𝒫 ⊆ 𝓡ᵢ` for all `i`. If `f` is truthfully
implementable in dominant strategies, it is dictatorial on `f(Θ)`. (Proof: Corollary 23.C.1
applied to `f̂ : Θ → f(Θ)`.) -/
theorem corollary_23_C_2 [Finite ι] [Nonempty ι] [DecidableEq ι] [Finite X]
    {u : (i : ι) → X → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hX : ∃ a ∈ Set.range f, ∃ b ∈ Set.range f, ∃ c ∈ Set.range f, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hR : ∀ i, StrictPrefs X ⊆ prefSet u i) (hf : StrategyProof u f) :
    DictatorialOn u f (Set.range f) := by
  let Y := Set.range f
  let uY : (i : ι) → Y → Θ i → ℝ := fun i y θi => u i y.1 θi
  let fY : ((i : ι) → Θ i) → Y := fun θ => ⟨f θ, θ, rfl⟩
  have hRY : ∀ i, StrictPrefs Y ⊆ prefSet uY i := by
    intro i r hr
    obtain ⟨θi, hθi⟩ := hR i (extendPref_mem hr (scorePref_mem (fun _ => 0)))
    refine ⟨θi, ?_⟩
    funext a b
    have := congrFun (congrFun hθi a.1) b.1
    exact this.trans (propext (extendPref_restrict a b))
  have hXY : ∃ a b c : Y, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hX
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, fun h => hab (congrArg Subtype.val h),
      fun h => hac (congrArg Subtype.val h), fun h => hbc (congrArg Subtype.val h)⟩
  have honY : Surjective fY := by
    rintro ⟨x, θ, rfl⟩
    exact ⟨θ, rfl⟩
  have hfY : StrategyProof uY fY := fun i θ θh => hf i θ θh
  obtain ⟨h, hh⟩ := corollary_23_C_1 hXY hRY honY hfY
  exact ⟨h, fun θ => ⟨⟨θ, rfl⟩, fun y hy => hh θ ⟨y, hy⟩⟩⟩

/-- **Corollary 23.C.2**, the converse under `𝓡ᵢ ⊆ 𝒫` (MWG, p. 876): a social choice function
dictatorial on `f(Θ)` is strategy-proof when no type has indifferences. -/
theorem strategyProof_of_dictatorialOn [DecidableEq ι] {u : (i : ι) → X → Θ i → ℝ}
    {f : ((i : ι) → Θ i) → X} (hR : ∀ i, prefSet u i ⊆ StrictPrefs X)
    (hD : DictatorialOn u f (Set.range f)) : StrategyProof u f := by
  obtain ⟨h, hh⟩ := hD
  have hdep : ∀ θ θ' : (i : ι) → Θ i, θ h = θ' h → f θ = f θ' := by
    intro θ θ' he
    have h1 := (hh θ).2 (f θ') ⟨θ', rfl⟩
    have h2 := (hh θ').2 (f θ) ⟨θ, rfl⟩
    rw [← he] at h2
    exact eq_of_utility_eq (hR h) (θ h) (le_antisymm h2 h1)
  intro i θ θh
  by_cases hi : i = h
  · subst hi
    exact (hh θ).2 _ ⟨_, rfl⟩
  · rw [hdep (update θ i θh) θ (by rw [update_of_ne (Ne.symm hi)])]

/-- **Corollary 23.C.2**, correction (MWG, p. 876). With indifference allowed the converse fails:
`tieBreakRule` is dictatorial on `f(Θ) = X` but not strategy-proof. -/
theorem corollary_23_C_2_converse_false :
    DictatorialOn optU tieBreakRule (Set.range tieBreakRule) ∧
      ¬StrategyProof optU tieBreakRule := by
  obtain ⟨-, -, ⟨h, hh⟩, hn⟩ := corollary_23_C_1_converse_false
  exact ⟨⟨h, fun θ => ⟨⟨θ, rfl⟩, fun y _ => hh θ y⟩⟩, hn⟩

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quasilinear environments: Groves-Clarke mechanisms

MWG, Section 23.C, pp. 876-881.

An alternative is `x = (k, t₁, …, t_I)` with a project `k ∈ K` and transfers `tᵢ ∈ ℝ`; agent
`i` of type `θᵢ` has utility `uᵢ(x, θᵢ) = vᵢ(k, θᵢ) + (m̄ᵢ + tᵢ)`; the feasible alternatives have
`∑ᵢ tᵢ ≤ 0`. A social choice function is `f(θ) = (k(θ), t₁(θ), …, t_I(θ))`.

* `exPostEfficient_ql_iff`: `f` is ex post efficient (within the feasible alternatives) iff its
  project rule satisfies (23.C.7) and it is budget balanced (23.C.12) (with at least one
  agent); in particular (23.C.7) is necessary (p. 877).
* **Proposition 23.C.4** (Groves): a project rule satisfying (23.C.7) with transfers (23.C.8)
  is strategy-proof.
* The Clarke (pivotal) mechanism and its properties (p. 878): transfers are `0` when agent `i`
  is not pivotal and `≤ 0` always. **Correction**: MWG say the transfer "is negative" when the
  announcement changes the project decision; with ties it can be `0`
  (`clarke_pivotal_zero_tax`). Footnote 23: `hᵢ(θ₋ᵢ) ≤ -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)` is sufficient
  but not necessary for `∑ᵢ tᵢ(θ) ≤ 0`.
* The single-good case: the Clarke transfer is minus the highest other valuation for the winner
  and `0` for the others (the second-price auction, p. 879).
* **Proposition 23.C.5** (Green-Laffont): if every valuation function `K → ℝ` arises for some
  type, every strategy-proof `f` with an efficient project rule is a Groves mechanism. MWG's
  type `θᵢ'` in (23.C.10) has valuation `-∞` off two projects, which is not a real-valued
  function (not in `𝒱`); we use `-∑_{j≠i} vⱼ(k, θⱼ) - 1` there instead (correction).
* Footnote 20: with at least two agents no social choice function is dictatorial, since no
  agent has a best feasible alternative.
* Exercise 23.C.11: Proposition 23.C.4 survives a strictly increasing transformation
  `uᵢ(vᵢ(k, θᵢ) + m̄ᵢ + tᵢ)`.
-/

namespace MWG.MechanismDesign

open Function Finset

variable {ι : Type*} {Θ : ι → Type*} {K : Type*}

/-- **Section 23.C** (MWG, p. 876). Quasilinear utility `uᵢ(x, θᵢ) = vᵢ(k, θᵢ) + (m̄ᵢ + tᵢ)` of
the alternative `x = (k, t)`. -/
def qlU (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) : (i : ι) → K × (ι → ℝ) → Θ i → ℝ :=
  fun i x θi => v i x.1 θi + (m i + x.2 i)

/-- **Section 23.C** (MWG, p. 877). The feasible alternatives `X = {(k, t) : ∑ᵢ tᵢ ≤ 0}`. -/
def QLAlt (ι : Type*) [Fintype ι] (K : Type*) : Type _ :=
  {x : K × (ι → ℝ) // ∑ i, x.2 i ≤ 0}

/-- **(23.C.7)** (MWG, p. 877). The project rule `k(·)` is efficient:
`∑ᵢ vᵢ(k(θ), θᵢ) ≥ ∑ᵢ vᵢ(k, θᵢ)` for all `k ∈ K` and `θ`. -/
def EfficientProject [Fintype ι] (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) :
    Prop :=
  ∀ θ k', ∑ i, v i k' (θ i) ≤ ∑ i, v i (k θ) (θ i)

/-- **(23.C.12)** (MWG, p. 880). Budget balance: `∑ᵢ tᵢ(θ) = 0` for all `θ`. -/
def BudgetBalanced [Fintype ι] (t : ((i : ι) → Θ i) → ι → ℝ) : Prop :=
  ∀ θ, ∑ i, t θ i = 0

/-- **Section 23.C** (MWG, pp. 877, 880). A feasible quasilinear social choice function is ex post
efficient (Definition 23.B.2, among the feasible alternatives) iff its project rule satisfies
(23.C.7) and it is budget balanced (23.C.12). -/
theorem exPostEfficient_ql_iff [Fintype ι] [Nonempty ι] (v : (i : ι) → K → Θ i → ℝ)
    (m : ι → ℝ) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    ExPostEfficient (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) f ↔
      EfficientProject v (fun θ => (f θ).1.1) ∧ BudgetBalanced (fun θ => (f θ).1.2) := by
  classical
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · intro hE
    refine ⟨fun θ k' => ?_, fun θ => ?_⟩
    · by_contra hlt
      rw [not_le] at hlt
      set δ := ∑ i, v i k' (θ i) - ∑ i, v i (f θ).1.1 (θ i) with hδ
      have hδpos : 0 < δ := by linarith
      let t' : ι → ℝ := fun i => (f θ).1.2 i + v i (f θ).1.1 (θ i) - v i k' (θ i) +
        δ / Fintype.card ι
      have hfeas : ∑ i, t' i ≤ 0 := by
        have : ∑ i, t' i = ∑ i, (f θ).1.2 i := by
          simp only [t', sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
          field_simp
          ring
        rw [this]; exact (f θ).2
      apply hE
      refine ⟨θ, ⟨(k', t'), hfeas⟩, fun i => ?_, Classical.arbitrary ι, ?_⟩
      · simp only [qlU, t']
        have := div_pos hδpos hI
        linarith
      · simp only [qlU, t']
        have := div_pos hδpos hI
        linarith
    · by_contra hne
      have hlt : ∑ i, (f θ).1.2 i < 0 := lt_of_le_of_ne (f θ).2 hne
      set δ := -∑ i, (f θ).1.2 i
      let t' : ι → ℝ := fun i => (f θ).1.2 i + δ / Fintype.card ι
      have hfeas : ∑ i, t' i ≤ 0 := by
        have : ∑ i, t' i = 0 := by
          simp only [t', sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, δ]
          field_simp
          ring
        rw [this]
      apply hE
      have hd : 0 < δ / Fintype.card ι := div_pos (by simp only [δ]; linarith) hI
      refine ⟨θ, ⟨((f θ).1.1, t'), hfeas⟩, fun i => ?_, Classical.arbitrary ι, ?_⟩
      · simp only [qlU, t']; linarith
      · simp only [qlU, t']; linarith
  · rintro ⟨hk, hb⟩ ⟨θ, x, hx, j, hj⟩
    have hsum : ∑ i, qlU v m i (f θ).1 (θ i) < ∑ i, qlU v m i x.1 (θ i) :=
      sum_lt_sum (fun i _ => hx i) ⟨j, mem_univ j, hj⟩
    simp only [qlU, sum_add_distrib] at hsum
    have h1 := hk θ x.1.1
    have h2 := hb θ
    have h3 := x.2
    simp only at h1 h2
    linarith

/-- The transfer function of a Groves mechanism, (23.C.8):
`tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)`. -/
def grovesTransfer [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) :
    ((i : ι) → Θ i) → ι → ℝ :=
  fun θ i => ∑ j ∈ univ.erase i, v j (k θ) (θ j) + h i θ

/-- `hᵢ` depends only on `θ₋ᵢ`: changing `θᵢ` does not change `hᵢ(θ)`. -/
def IndepOwn [DecidableEq ι] {Y : Type*} (h : (i : ι) → ((j : ι) → Θ j) → Y) : Prop :=
  ∀ i θ (a : Θ i), h i (update θ i a) = h i θ

/-- **Proposition 23.C.4** (MWG, p. 877). If `k*(·)` satisfies (23.C.7) and the transfers have the
form (23.C.8) with `hᵢ` a function of `θ₋ᵢ` only, then `f = (k*, t)` is truthfully implementable
in dominant strategies. -/
theorem proposition_23_C_4 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) :
    StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k h θ)) := by
  intro i θ θh
  simp only [qlU, grovesTransfer, hh i θ θh]
  have e : ∀ θ' : (j : ι) → Θ j, (∀ j ≠ i, θ' j = θ j) →
      v i (k θ') (θ i) + ∑ j ∈ univ.erase i, v j (k θ') (θ' j) = ∑ j, v j (k θ') (θ j) := by
    intro θ' hθ'
    rw [← add_sum_erase _ _ (mem_univ i)]
    congr 1
    exact sum_congr rfl fun j hj => by rw [hθ' j (ne_of_mem_erase hj)]
  have e1 := e (update θ i θh) fun j hj => update_of_ne hj _ _
  have e2 := e θ fun _ _ => rfl
  have := hk θ (k (update θ i θh))
  linarith

/-- The Clarke (pivotal) transfer: `hᵢ(θ₋ᵢ) = -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)`, where `k₋ᵢ*(θ₋ᵢ)` is
efficient for the agents `j ≠ i` alone (MWG, p. 878). -/
def clarkeH [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (kminus : ι → ((j : ι) → Θ j) → K) : (i : ι) → ((j : ι) → Θ j) → ℝ :=
  fun i θ => -∑ j ∈ univ.erase i, v j (kminus i θ) (θ j)

/-- `k₋ᵢ*(θ₋ᵢ)` is efficient for the agents other than `i` (MWG, p. 878). -/
def EfficientForOthers [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (kminus : ι → ((j : ι) → Θ j) → K) : Prop :=
  IndepOwn kminus ∧ ∀ i θ k', ∑ j ∈ univ.erase i, v j k' (θ j) ≤
    ∑ j ∈ univ.erase i, v j (kminus i θ) (θ j)

/-- **Clarke mechanism** (MWG, p. 878). The Clarke `hᵢ` depends only on `θ₋ᵢ`, so the Clarke
mechanism is a Groves mechanism and is strategy-proof. -/
theorem clarke_strategyProof [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {kminus : ι → ((j : ι) → Θ j) → K} (hkm : EfficientForOthers v kminus) :
    StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k (clarkeH v kminus) θ)) := by
  refine proposition_23_C_4 m hk fun i θ a => ?_
  simp only [clarkeH, hkm.1 i θ a]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Clarke mechanism** (MWG, p. 878). Agent `i`'s Clarke transfer is `0` if his announcement does
not change the project decision relative to `k₋ᵢ*(θ₋ᵢ)`, and is never positive. -/
theorem clarke_transfer_props [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    {k : ((i : ι) → Θ i) → K} {kminus : ι → ((j : ι) → Θ j) → K}
    (hkm : EfficientForOthers v kminus) (θ : (i : ι) → Θ i) (i : ι) :
    (k θ = kminus i θ → grovesTransfer v k (clarkeH v kminus) θ i = 0) ∧
      grovesTransfer v k (clarkeH v kminus) θ i ≤ 0 := by
  refine ⟨fun he => ?_, ?_⟩
  · simp [grovesTransfer, clarkeH, he]
  · have := hkm.2 i θ (k θ)
    simp only [grovesTransfer, clarkeH]
    linarith

/-- **Footnote 23** (MWG, p. 878). The Clarke mechanism is feasible: `∑ᵢ tᵢ(θ) ≤ 0`; more
generally `hᵢ(θ₋ᵢ) ≤ -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)` for all `i` is sufficient for a Groves scheme to
be feasible. -/
theorem footnote_23_23 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    {k : ((i : ι) → Θ i) → K} {kminus : ι → ((j : ι) → Θ j) → K}
    (hkm : EfficientForOthers v kminus) {h : (i : ι) → ((j : ι) → Θ j) → ℝ}
    (hle : ∀ i θ, h i θ ≤ clarkeH v kminus i θ) (θ : (i : ι) → Θ i) :
    ∑ i, grovesTransfer v k h θ i ≤ 0 := by
  refine sum_nonpos fun i _ => ?_
  have h1 := hkm.2 i θ (k θ)
  have h2 := hle i θ
  simp only [grovesTransfer, clarkeH] at h2 ⊢
  linarith

/-- **Footnote 23** (MWG, p. 878), "sufficient (but not necessary)": a feasible Groves scheme with
`h₁ > -∑_{j≠1} vⱼ(k₋₁*, θⱼ)` (one project, `h = (1, -1)`). -/
theorem footnote_23_23_not_necessary :
    let v : Fin 2 → Unit → Unit → ℝ := fun _ _ _ => 0
    let h : Fin 2 → (Fin 2 → Unit) → ℝ := fun i _ => if i = 0 then 1 else -1
    (∑ i, grovesTransfer (Θ := fun _ => Unit) v (fun _ => ()) h (fun _ => ()) i ≤ 0) ∧
      clarkeH (Θ := fun _ => Unit) v (fun _ _ => ()) 0 (fun _ => ()) < h 0 (fun _ => ()) := by
  intro v h
  simp [v, h, grovesTransfer, clarkeH, Fin.sum_univ_two]

/-- **Correction** (MWG, p. 878). A pivotal agent's Clarke tax can be `0`: with two agents,
projects `Bool`, agent 0 valuing `true` at `1`, agent 1 indifferent, and `k₋₀* = false`, the
efficient decision is `true ≠ k₋₀*` but agent 0's transfer is `0`, not negative. -/
theorem clarke_pivotal_zero_tax :
    let v : Fin 2 → Bool → Unit → ℝ := fun i k _ => if i = 0 ∧ k = true then 1 else 0
    (fun (_ : Fin 2 → Unit) => true) ≠ (fun _ => false) ∧
      grovesTransfer v (fun _ => true) (clarkeH v fun _ _ => false) (fun _ => ()) 0 = 0 := by
  refine ⟨fun h => absurd (congrFun h fun _ => ()) (by decide), ?_⟩
  simp [grovesTransfer, clarkeH]

/-- **Single indivisible good** (MWG, pp. 877, 879). The project is the winner `k ∈ ι`, and
`vᵢ(k, θᵢ) = θᵢ` if `k = i`, `0` otherwise. -/
def goodV [DecidableEq ι] : ι → ι → ℝ → ℝ := fun i k θi => if k = i then θi else 0

/-- **Single indivisible good** (MWG, p. 879): with an efficient allocation (the good goes to a
highest valuation) and `k₋ᵢ*(θ₋ᵢ)` a highest valuation among the others, the Clarke transfer of
the winner is minus the highest other valuation (the second-highest valuation) and every other
agent's transfer is `0`: the Clarke mechanism is the second-price sealed-bid auction. -/
theorem clarke_single_good [Fintype ι] [DecidableEq ι] {k : (ι → ℝ) → ι}
    (hk : ∀ (θ : ι → ℝ) j, θ j ≤ θ (k θ)) {kminus : ι → (ι → ℝ) → ι}
    (hkm1 : ∀ i (θ : ι → ℝ), kminus i θ ≠ i)
    (hkm2 : ∀ i (θ : ι → ℝ) j, j ≠ i → θ j ≤ θ (kminus i θ)) (θ : ι → ℝ) (i : ι) :
    grovesTransfer (Θ := fun _ => ℝ) goodV k (clarkeH (Θ := fun _ => ℝ) goodV kminus) θ i =
      if k θ = i then -θ (kminus i θ) else 0 := by
  have hsum : ∀ w : ι, ∑ j ∈ univ.erase i, goodV j w (θ j) = if w = i then 0 else θ w := by
    intro w
    by_cases hw : w = i
    · subst hw
      refine (sum_eq_zero fun j hj => ?_).trans (by simp)
      simp [goodV, Ne.symm (ne_of_mem_erase hj)]
    · rw [sum_eq_single w]
      · simp [goodV, hw]
      · intro j _ hj; simp [goodV, Ne.symm hj]
      · intro h; exact absurd (mem_erase.2 ⟨hw, mem_univ w⟩) h
  simp only [grovesTransfer, clarkeH, hsum, hkm1 i θ, ite_false]
  by_cases hw : k θ = i
  · simp [hw]
  · simp only [hw, ite_false]
    have h1 := hk θ (kminus i θ)
    have h2 := hkm2 i θ (k θ) hw
    linarith

/-- **Proposition 23.C.5** (Green and Laffont; MWG, p. 879). Suppose every valuation function
`K → ℝ` arises for some type of each agent (`{vᵢ(·, θᵢ) : θᵢ ∈ Θᵢ} = 𝒱`). If `f = (k*, t)` with
`k*` satisfying (23.C.7) is truthfully implementable in dominant strategies, then the transfers
have the Groves form (23.C.8): `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)`. -/
theorem proposition_23_C_5 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) :
    ∃ h : (i : ι) → ((j : ι) → Θ j) → ℝ, IndepOwn h ∧ ∀ θ, t θ = grovesTransfer v k h θ := by
  classical
  -- (23.C.9)
  let h : (i : ι) → ((j : ι) → Θ j) → ℝ := fun i θ => t θ i - ∑ j ∈ univ.erase i, v j (k θ) (θ j)
  refine ⟨h, ?_, fun θ => funext fun i => by simp [grovesTransfer, h]⟩
  -- the others' total valuation of a project, at the others' types in `θ`
  let W : ι → ((j : ι) → Θ j) → K → ℝ := fun i θ k' => ∑ j ∈ univ.erase i, v j k' (θ j)
  have hW : ∀ i θ (a : Θ i) k', W i (update θ i a) k' = W i θ k' := fun i θ a k' =>
    sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  have hsplit : ∀ i θ k', ∑ j, v j k' (θ j) = v i k' (θ i) + W i θ k' := fun i θ k' =>
    (add_sum_erase _ _ (mem_univ i)).symm
  -- SP, rewritten: type `a` of agent `i` reporting `b`, with the others at `θ`
  have hsp : ∀ i θ (a b : Θ i), v i (k (update θ i b)) a + t (update θ i b) i ≤
      v i (k (update θ i a)) a + t (update θ i a) i := by
    intro i θ a b
    have := hSP i (update θ i a) b
    simp only [qlU, update_idem, update_self] at this
    linarith
  -- (i): equal projects give equal transfers
  have case_i : ∀ i θ (a b : Θ i), k (update θ i a) = k (update θ i b) →
      t (update θ i a) i = t (update θ i b) i := by
    intro i θ a b he
    have h1 := hsp i θ a b
    have h2 := hsp i θ b a
    rw [he] at h1 h2
    linarith
  -- the key inequality: `hᵢ(a, θ₋ᵢ) ≤ hᵢ(b, θ₋ᵢ)` for all `a`, `b`
  have key : ∀ i θ (a b : Θ i), h i (update θ i a) ≤ h i (update θ i b) := by
    intro i θ a b
    by_cases he : k (update θ i a) = k (update θ i b)
    · have e1 := hW i θ a (k (update θ i b))
      have e2 := hW i θ b (k (update θ i b))
      simp only [h, W] at e1 e2 ⊢
      rw [case_i i θ a b he, he, e1, e2]
    · -- (23.C.10) with `-∞` replaced by `-W - 1`
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨k1, hk1⟩ : ∃ k1, k (update θ i a) = k1 := ⟨_, rfl⟩
      obtain ⟨k2, hk2'⟩ : ∃ k2, k (update θ i b) = k2 := ⟨_, rfl⟩
      rw [hk1, hk2'] at he
      obtain ⟨c, hc⟩ := hrich i fun k' =>
        if k' = k1 then -W i θ k1 else if k' = k2 then -W i θ k2 + ε else -W i θ k' - 1
      have hv1 : v i k1 c = -W i θ k1 := by rw [hc]; simp
      have hv2 : v i k2 c = -W i θ k2 + ε := by rw [hc]; simp [Ne.symm he]
      have hvo : ∀ k', k' ≠ k1 → k' ≠ k2 → v i k' c = -W i θ k' - 1 := by
        intro k' h1 h2; rw [hc]; simp [h1, h2]
      -- the efficient project at type `c` is `k2`
      have hk2 : k (update θ i c) = k2 := by
        by_contra hne
        have hmax := hk (update θ i c) k2
        rw [hsplit i _ k2, hsplit i _ (k (update θ i c)), hW, hW] at hmax
        simp only [update_self] at hmax
        rw [hv2] at hmax
        by_cases h1 : k (update θ i c) = k1
        · rw [h1, hv1] at hmax; linarith
        · rw [hvo _ h1 hne] at hmax; linarith
      have hti := case_i i θ c b (by rw [hk2, hk2'])
      have hsp' := hsp i θ c a
      rw [hk2, hk1, hv1, hv2, hti] at hsp'
      have e1 := hW i θ a k1
      have e2 := hW i θ b k2
      simp only [h, W] at hsp' e1 e2 ⊢
      rw [hk1, hk2', e1, e2]
      linarith
  intro i θ a
  have h1 := key i θ a (θ i)
  have h2 := key i θ (θ i) a
  rw [update_eq_self] at h1 h2
  exact le_antisymm h1 h2

/-- **Footnote 20** (MWG, p. 877). The quasilinear set of alternatives is not compact; with at
least two agents no social choice function is dictatorial, since every feasible alternative can
be improved for any agent by a transfer from another agent. -/
theorem footnote_23_20 [Fintype ι] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (h2 : ∀ i : ι, ∃ j, j ≠ i) (θ0 : (i : ι) → Θ i) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    ¬Dictatorial (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) f := by
  classical
  rintro ⟨h, hh⟩
  obtain ⟨j, hj⟩ := h2 h
  let x := f θ0
  let t' : ι → ℝ := fun i => x.1.2 i + (if i = h then 1 else 0) - (if i = j then 1 else 0)
  have hfeas : ∑ i, t' i ≤ 0 := by
    have : ∑ i, t' i = ∑ i, x.1.2 i := by
      simp only [t', sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
      ring
    rw [this]; exact x.2
  have := hh θ0 ⟨(x.1.1, t'), hfeas⟩
  simp only [qlU, t', ite_true, Ne.symm hj, ite_false] at this
  linarith

/-- **Exercise 23.C.11** (MWG, p. 920). With utilities `uᵢ(vᵢ(k, θᵢ) + m̄ᵢ + tᵢ)` for strictly
increasing `uᵢ` (arbitrary risk preferences over money), Proposition 23.C.4 is unaffected:
Groves schemes remain strategy-proof. -/
theorem exercise_23_C_11 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) (U : ι → ℝ → ℝ)
    (hU : ∀ i, StrictMono (U i)) :
    StrategyProof (fun i x θi => U i (qlU v m i x θi))
      (fun θ => (k θ, grovesTransfer v k h θ)) :=
  fun i θ θh => (hU i).monotone (proposition_23_C_4 m hk hh i θ θh)

/-- **Outside agent** (MWG, p. 881). With an agent 0 who has no private information and utility
`m̄₀ + t₀`, a Groves scheme for agents `1, …, I` with `t₀(θ) = -∑_{i≠0} tᵢ(θ)` is budget balanced
for all `I + 1` agents, keeps (23.C.7) (agent 0 values all projects at `0`), and remains
strategy-proof for the agents with private types. -/
theorem outside_agent [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) (θ : (i : ι) → Θ i) :
    (-∑ i, grovesTransfer v k h θ i) + ∑ i, grovesTransfer v k h θ i = 0 ∧
      (∀ k', (0 : ℝ) + ∑ i, v i k' (θ i) ≤ 0 + ∑ i, v i (k θ) (θ i)) ∧
      StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k h θ)) :=
  ⟨by ring, fun k' => by linarith [hk θ k'], proposition_23_C_4 m hk hh⟩

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Groves mechanisms and budget balance

MWG, Section 23.C, pp. 880-881, Proposition 23.C.6 (Green and Laffont; proof omitted in MWG),
and Exercise 23.C.10(a)-(b) (Holmstrom, p. 920).

`V*(θ) = ∑ᵢ vᵢ(k*(θ), θᵢ)` is the maximal total valuation.

* **Exercise 23.C.10(a)**: if `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`, the Groves scheme with
  `hᵢ = -(I - 1)Vᵢ` is efficient, budget balanced and strategy-proof (`exercise_23_C_10a_if`).
  Conversely, under the richness hypothesis of Proposition 23.C.5 and with at least two agents,
  an efficient, budget balanced, strategy-proof `f` forces such a decomposition
  (`exercise_23_C_10a_only_if`). The "only if" needs `I ≥ 2`: with one agent `t = 0` works
  for every `V*` (`exercise_23_C_10a_only_if_false_one_agent`).
* `mixedDifference_eq_zero`: a sum of functions each independent of one coordinate has zero
  `I`-fold mixed difference.
* **Proposition 23.C.6**: with every valuation function possible, at least two agents and at
  least two projects, no strategy-proof social choice function satisfies (23.C.7) and (23.C.12)
  (`proposition_23_C_6`); the proof exhibits types whose maximal total valuation has nonzero
  mixed difference. **Correction**: MWG state it without `I ≥ 2` and `|K| ≥ 2`; with one
  project or one agent, `t = 0` is an efficient, budget balanced, strategy-proof rule
  (`proposition_23_C_6_false_one_project`, `proposition_23_C_6_false_one_agent`).
* **Exercise 23.C.10(b)**: with `I ≥ 3`, `K = ℝ` and `vᵢ(k, θᵢ) = θᵢk - k²/2`, an efficient,
  budget balanced, strategy-proof rule exists (for real types, hence for `Θᵢ = ℝ₊`).
-/

namespace MWG.MechanismDesign

open Function Finset

variable {ι : Type*} {Θ : ι → Type*} {K : Type*}

/-- `∑ᵢ ∑_{j≠i} gⱼ = (I - 1) ∑ⱼ gⱼ`. -/
theorem sum_sum_erase [Fintype ι] [DecidableEq ι] (g : ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, g j = (Fintype.card ι - 1) * ∑ j, g j := by
  simp only [sum_erase_eq_sub (mem_univ _), sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The total transfer of a Groves scheme: `∑ᵢ tᵢ(θ) = (I - 1)V*(θ) + ∑ᵢ hᵢ(θ)`. -/
theorem sum_grovesTransfer [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) (θ : (i : ι) → Θ i) :
    ∑ i, grovesTransfer v k h θ i =
      (Fintype.card ι - 1) * ∑ j, v j (k θ) (θ j) + ∑ i, h i θ := by
  simp only [grovesTransfer, sum_add_distrib]
  rw [sum_sum_erase (fun j => v j (k θ) (θ j))]

/-- **Exercise 23.C.10(a)** (MWG, p. 920), "if". If `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`, there is an ex post
efficient (efficient project and budget balanced) social choice function truthfully
implementable in dominant strategies: the Groves scheme with `hᵢ = -(I - 1)Vᵢ`. -/
theorem exercise_23_C_10a_if [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    (V : (i : ι) → ((j : ι) → Θ j) → ℝ) (hV : IndepOwn V)
    (hdec : ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ) :
    ∃ t : ((i : ι) → Θ i) → ι → ℝ,
      StrategyProof (qlU v m) (fun θ => (k θ, t θ)) ∧ BudgetBalanced t := by
  refine ⟨grovesTransfer v k fun i θ => -((Fintype.card ι : ℝ) - 1) * V i θ,
    proposition_23_C_4 m hk fun i θ a => by simp only [hV i θ a], fun θ => ?_⟩
  rw [sum_grovesTransfer, hdec θ, ← mul_sum]
  ring

/-- **Exercise 23.C.10(a)** (MWG, p. 920), "only if", under the richness hypothesis of
Proposition 23.C.5 and with at least two agents: if an efficient project rule is part of a
budget balanced, strategy-proof social choice function, then `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`. -/
theorem exercise_23_C_10a_only_if [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) (hBB : BudgetBalanced t) :
    ∃ V : (i : ι) → ((j : ι) → Θ j) → ℝ, IndepOwn V ∧
      ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ := by
  obtain ⟨h, hh, ht⟩ := proposition_23_C_5 m hrich hk hSP
  have hI' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hI
  refine ⟨fun i θ => -h i θ / ((Fintype.card ι : ℝ) - 1), fun i θ a => by simp [hh i θ a],
    fun θ => ?_⟩
  have h0 := hBB θ
  rw [ht θ, sum_grovesTransfer] at h0
  have hne : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by linarith
  rw [← sum_div, sum_neg_distrib, eq_div_iff hne]
  linarith

/-- **Exercise 23.C.10(a)**, correction: the "only if" fails with one agent. With one agent,
projects `Bool`, every valuation possible, and the efficient rule, `t = 0` is strategy-proof and
budget balanced, while `V*` is not a function of `θ₋₁` (which is trivial). -/
theorem exercise_23_C_10a_only_if_false_one_agent :
    let v : Unit → Bool → (Bool → ℝ) → ℝ := fun _ k θ => θ k
    let k : (Unit → Bool → ℝ) → Bool := fun θ => decide (θ () false ≤ θ () true)
    EfficientProject (ι := Unit) (Θ := fun _ => Bool → ℝ) v k ∧
      StrategyProof (qlU (ι := Unit) (Θ := fun _ => Bool → ℝ) v 0) (fun θ => (k θ, fun _ => 0)) ∧
      BudgetBalanced (ι := Unit) (Θ := fun _ => Bool → ℝ) (fun _ _ => (0 : ℝ)) ∧
      ¬∃ V : Unit → (Unit → Bool → ℝ) → ℝ, IndepOwn (ι := Unit) (Θ := fun _ => Bool → ℝ) V ∧
        ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ := by
  intro v k
  have hk : ∀ (θ : Unit → Bool → ℝ) (b : Bool), θ () b ≤ θ () (k θ) := by
    intro θ b
    by_cases h : θ () false ≤ θ () true
    · cases b <;> simp [k, h]
    · cases b <;> simp [k, h]
      all_goals linarith
  refine ⟨fun θ b => by simpa [v] using hk θ b, fun i θ θh => ?_, fun _ => by simp, ?_⟩
  · simp only [qlU, v, Pi.zero_apply, add_zero]
    exact hk θ _
  · rintro ⟨V, hV, hdec⟩
    have e0 := hdec fun _ _ => 0
    have e1 := hdec fun _ b => if b then 1 else 0
    have hc : V () (fun _ b => if b then 1 else 0) = V () fun _ _ => 0 := by
      have := hV () (fun _ _ => 0) (fun b => if b then 1 else 0)
      rw [show update (fun _ _ => (0 : ℝ)) () (fun b : Bool => if b then (1 : ℝ) else 0) =
        fun _ b => if b then 1 else 0 from funext fun _ => rfl] at this
      exact this
    simp only [v, k, Finset.univ_unique, sum_singleton] at e0 e1
    norm_num at e0 e1
    linarith

/-- The profile using `θ¹` on `S` and `θ⁰` off `S`. -/
def mixProfile [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i) (S : Finset ι) : (i : ι) → Θ i :=
  fun j => if j ∈ S then θ1 j else θ0 j

/-- A function independent of `θᵢ` has zero alternating sum over the subsets (the `i`-th
difference vanishes). -/
theorem alternating_sum_indepOwn [Fintype ι] [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i) (i : ι)
    (g : ((j : ι) → Θ j) → ℝ) (hg : ∀ θ (a : Θ i), g (update θ i a) = g θ) :
    ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℝ) ^ S.card * g (mixProfile θ0 θ1 S) = 0 := by
  have hu : (univ : Finset ι) = insert i (univ.erase i) := (insert_erase (mem_univ i)).symm
  rw [hu, sum_powerset_insert (notMem_erase i univ)]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun S hS => ?_
  have hiS : i ∉ S := fun h => (notMem_erase i univ) (mem_powerset.1 hS h)
  have hmix : mixProfile θ0 θ1 (insert i S) = update (mixProfile θ0 θ1 S) i (θ1 i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [mixProfile]
    · simp [mixProfile, hj]
  rw [hmix, hg, card_insert_of_notMem hiS, pow_succ]
  ring

/-- The `I`-fold mixed difference of `∑ᵢ Vᵢ(θ₋ᵢ)` vanishes. -/
theorem mixedDifference_eq_zero [Fintype ι] [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i)
    (V : (i : ι) → ((j : ι) → Θ j) → ℝ) (hV : IndepOwn V) :
    ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℝ) ^ S.card * ∑ i, V i (mixProfile θ0 θ1 S) = 0 := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_eq_zero fun i _ => alternating_sum_indepOwn θ0 θ1 i (V i) (hV i)

/-- **Proposition 23.C.6** (Green and Laffont; MWG, p. 880; proof omitted in MWG). Suppose every
valuation function `K → ℝ` arises for some type of each agent. With at least two agents and at
least two projects, no social choice function `f = (k*, t)` truthfully implementable in dominant
strategies satisfies both (23.C.7) and (23.C.12). (The hypotheses `I ≥ 2` and `|K| ≥ 2` are
needed: see `proposition_23_C_6_false_one_project` and `proposition_23_C_6_false_one_agent`.) -/
theorem proposition_23_C_6 [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι) {a b : K}
    (hab : a ≠ b) {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) : ¬BudgetBalanced t := by
  classical
  intro hBB
  obtain ⟨V, hV, hdec⟩ := exercise_23_C_10a_only_if hI m hrich hk hSP hBB
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : (1 : ℝ) < n := by rw [hn]; exact_mod_cast hI
  -- two types for every agent
  obtain ⟨θ0, hθ0⟩ := (show ∃ θ0 : (i : ι) → Θ i, ∀ i k', v i k' (θ0 i) =
      if k' = a then 0 else if k' = b then -n else -1 from
    ⟨fun i => (hrich i _).choose, fun i => (hrich i _).choose_spec⟩)
  obtain ⟨θ1, hθ1⟩ := (show ∃ θ1 : (i : ι) → Θ i, ∀ i k', v i k' (θ1 i) =
      if k' = a then 0 else if k' = b then 1 else -1 from
    ⟨fun i => (hrich i _).choose, fun i => (hrich i _).choose_spec⟩)
  -- total valuations at the mixed profiles
  have htot : ∀ (S : Finset ι) k', ∑ i, v i k' (mixProfile θ0 θ1 S i) =
      if k' = a then 0 else if k' = b then (n + 1) * S.card - n ^ 2 else -n := by
    intro S k'
    have hcard : ∑ i : ι, (if i ∈ S then (1 : ℝ) else 0) = S.card := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter]
    have e : ∀ i, v i k' (mixProfile θ0 θ1 S i) = if k' = a then 0 else if k' = b then
        (n + 1) * (if i ∈ S then 1 else 0) - n else -1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [mixProfile, hi, ite_true, hθ1]; split_ifs <;> ring
      · simp only [mixProfile, hi, ite_false, hθ0]; split_ifs <;> ring
    simp only [e]
    by_cases ha : k' = a
    · simp [ha]
    · by_cases hb : k' = b
      · simp only [hb, Ne.symm hab, ite_false, ite_true]
        rw [sum_sub_distrib, ← mul_sum, hcard, sum_const, card_univ, nsmul_eq_mul, ← hn]
        ring
      · simp [ha, hb, hn]
  -- the maximal total valuation
  have hVstar : ∀ S : Finset ι, ∑ i, v i (k (mixProfile θ0 θ1 S)) (mixProfile θ0 θ1 S i) =
      if S = univ then n else 0 := by
    intro S
    have hS : (S.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast card_le_univ S
    have ha := hk (mixProfile θ0 θ1 S) a
    have hb := hk (mixProfile θ0 θ1 S) b
    rw [htot] at ha hb ⊢
    rw [htot] at ha hb
    simp only [ite_true, Ne.symm hab, ite_false] at ha hb
    by_cases hSu : S = univ
    · have hc : (S.card : ℝ) = n := by rw [hSu, hn, card_univ]
      rw [hc] at ha hb
      simp only [hSu, ite_true]
      subst hSu
      split_ifs at ha hb ⊢ with h1 h2 <;> nlinarith
    · have hlt : (S.card : ℝ) ≤ n - 1 := by
        have : S.card < Fintype.card ι := by
          obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
            by_contra hall
            exact hSu (eq_univ_of_forall fun i => not_not.1 fun h => hall ⟨i, h⟩)
          exact card_lt_univ_of_notMem hi
        have : (S.card : ℝ) + 1 ≤ n := by rw [hn]; exact_mod_cast this
        linarith
      simp only [hSu, ite_false]
      split_ifs at ha hb ⊢ with h1 h2
      · rfl
      · nlinarith
      · linarith
  have hmix := mixedDifference_eq_zero θ0 θ1 V hV
  simp only [← hdec, hVstar] at hmix
  rw [sum_eq_single univ (fun S _ hS => by simp [hS]) (fun h => absurd (mem_powerset_self _) h)]
    at hmix
  simp only [ite_true, card_univ] at hmix
  have : (-1 : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn0 : n ≠ 0 := by linarith
  exact (mul_ne_zero this hn0) hmix

/-- **Proposition 23.C.6**, correction: with a single project the conclusion fails. Every
valuation `Unit → ℝ` arises, the constant project is efficient, and `t = 0` is strategy-proof
and budget balanced. -/
theorem proposition_23_C_6_false_one_project :
    let v : Fin 2 → Unit → (Unit → ℝ) → ℝ := fun _ k θ => θ k
    (∀ i (w : Unit → ℝ), ∃ θi : Unit → ℝ, ∀ k, v i k θi = w k) ∧
      EfficientProject (ι := Fin 2) (Θ := fun _ => Unit → ℝ) v (fun _ => ()) ∧
      StrategyProof (qlU (ι := Fin 2) (Θ := fun _ => Unit → ℝ) v 0) (fun _ => ((), fun _ => 0)) ∧
      BudgetBalanced (ι := Fin 2) (Θ := fun _ => Unit → ℝ) (fun _ _ => (0 : ℝ)) := by
  intro v
  exact ⟨fun _ w => ⟨w, fun _ => rfl⟩, fun _ _ => le_rfl, fun _ _ _ => le_rfl,
    fun _ => by simp⟩

/-- **Proposition 23.C.6**, correction: with a single agent the conclusion fails (every valuation
arises, the efficient rule with `t = 0` is strategy-proof and budget balanced). -/
theorem proposition_23_C_6_false_one_agent :
    let v : Unit → Bool → (Bool → ℝ) → ℝ := fun _ k θ => θ k
    let k : (Unit → Bool → ℝ) → Bool := fun θ => decide (θ () false ≤ θ () true)
    (∀ i (w : Bool → ℝ), ∃ θi : Bool → ℝ, ∀ k, v i k θi = w k) ∧
      EfficientProject (ι := Unit) (Θ := fun _ => Bool → ℝ) v k ∧
      StrategyProof (qlU (ι := Unit) (Θ := fun _ => Bool → ℝ) v 0) (fun θ => (k θ, fun _ => 0)) ∧
      BudgetBalanced (ι := Unit) (Θ := fun _ => Bool → ℝ) (fun _ _ => (0 : ℝ)) := by
  intro v k
  obtain ⟨h1, h2, h3, -⟩ := exercise_23_C_10a_only_if_false_one_agent
  exact ⟨fun _ w => ⟨w, fun _ => rfl⟩, h1, h2, h3⟩

/-- The quadratic valuations of Exercise 23.C.10(b): `vᵢ(k, θᵢ) = gᵢ(θᵢ)k - k²/2`, where
`gᵢ(θᵢ) ∈ ℝ` is the real type (the identity for `Θᵢ = ℝ`, the inclusion for `Θᵢ = ℝ₊`). -/
noncomputable def quadV (g : (i : ι) → Θ i → ℝ) : (i : ι) → ℝ → Θ i → ℝ :=
  fun i k θi => g i θi * k - k ^ 2 / 2

/-- **Exercise 23.C.10(b)** (MWG, p. 920). With `I ≥ 3` agents, `K = ℝ` and
`vᵢ(k, θᵢ) = θᵢk - k²/2` (types given by any real-valued `gᵢ`, e.g. `Θᵢ = ℝ` or `Θᵢ = ℝ₊`),
`k*(θ) = ∑ᵢθᵢ/I` is efficient, `V*(θ) = (∑ᵢθᵢ)²/(2I)` decomposes as `∑ᵢ Vᵢ(θ₋ᵢ)`, and hence an
ex post efficient, strategy-proof social choice function exists. MWG ask for `I = 3` and remark
that the result extends to any `I > 2`; both are covered. -/
theorem exercise_23_C_10b [Fintype ι] [DecidableEq ι] (hI : 3 ≤ Fintype.card ι)
    (g : (i : ι) → Θ i → ℝ) (m : ι → ℝ) :
    EfficientProject (quadV g) (fun θ => (∑ i, g i (θ i)) / Fintype.card ι) ∧
      ∃ t : ((i : ι) → Θ i) → ι → ℝ,
        StrategyProof (qlU (quadV g) m)
          (fun θ => ((∑ i, g i (θ i)) / Fintype.card ι, t θ)) ∧ BudgetBalanced t := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hI
  have hk : EfficientProject (quadV g) (fun θ => (∑ i, g i (θ i)) / n) := by
    intro θ k'
    simp only [quadV, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, ← hn]
    set s := ∑ i, g i (θ i)
    have : 0 ≤ (n * k' - s) ^ 2 / (2 * n) := by positivity
    have e : s * (s / n) - n * ((s / n) ^ 2 / 2) - (s * k' - n * (k' ^ 2 / 2)) =
        (n * k' - s) ^ 2 / (2 * n) := by field_simp; ring
    linarith
  refine ⟨hk, exercise_23_C_10a_if m hk (fun i θ =>
    ((∑ j ∈ univ.erase i, g j (θ j)) ^ 2 - (∑ j ∈ univ.erase i, g j (θ j) ^ 2) / (n - 1)) /
      (2 * n * (n - 2))) (fun i θ a => ?_) (fun θ => ?_)⟩
  · have e1 : ∑ j ∈ univ.erase i, g j (update θ i a j) = ∑ j ∈ univ.erase i, g j (θ j) :=
      sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    have e2 : ∑ j ∈ univ.erase i, g j (update θ i a j) ^ 2 =
        ∑ j ∈ univ.erase i, g j (θ j) ^ 2 :=
      sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    simp only [e1, e2]
  · have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by intro h; linarith
    have hn2 : n - 2 ≠ 0 := by intro h; linarith
    obtain ⟨s, hsd⟩ : ∃ s, ∑ i, g i (θ i) = s := ⟨_, rfl⟩
    obtain ⟨q, hqd⟩ : ∃ q, ∑ i, g i (θ i) ^ 2 = q := ⟨_, rfl⟩
    have hs : ∀ i, ∑ j ∈ univ.erase i, g j (θ j) = s - g i (θ i) := fun i => by
      rw [sum_erase_eq_sub (mem_univ i), hsd]
    have hq : ∀ i, ∑ j ∈ univ.erase i, g j (θ j) ^ 2 = q - g i (θ i) ^ 2 := fun i => by
      rw [sum_erase_eq_sub (mem_univ i), hqd]
    simp only [quadV, hsd, hs, hq, ← sum_div]
    have h1 : ∑ i, ((s - g i (θ i)) ^ 2 - (q - g i (θ i) ^ 2) / (n - 1)) =
        (n - 2) * s ^ 2 := by
      have : ∀ i, (s - g i (θ i)) ^ 2 - (q - g i (θ i) ^ 2) / (n - 1) =
          s ^ 2 - 2 * s * g i (θ i) + g i (θ i) ^ 2 - q / (n - 1) +
            g i (θ i) ^ 2 / (n - 1) := fun i => by ring
      simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← hn, ← mul_sum, ← sum_div, hsd, hqd]
      field_simp
      ring
    rw [h1, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, ← hn, hsd]
    field_simp
    ring

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Statistically independent types

MWG, Section 23.D, p. 886: types are statistically independent, `φ(θ) = φ₁(θ₁) × ⋯ × φ_I(θ_I)`.
The prior is the product measure `P = Measure.pi μ` of probability measures `μᵢ`; agent `i`'s
belief about `θ₋ᵢ` does not depend on `θᵢ` and is `P` itself (`indepBeliefs`), so
`E_{θ₋ᵢ}[g(θ̂ᵢ, θ₋ᵢ) | θᵢ] = ∫ g(θ̂ᵢ, θ₋ᵢ') dP(θ')`.

The key fact used throughout Sections 23.D-23.F, `E[g(θ)] = E_{θᵢ}[E_{θ₋ᵢ}[g(θᵢ, θ₋ᵢ)]]`
(`integral_integral_update`), is proved from the measure-preserving map
`(θ, θ') ↦ (θᵢ, θ₋ᵢ')` of `P ⊗ P` onto `P` and Fubini's theorem.
-/

namespace MWG.MechanismDesign

open Function MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]

/-- **Section 23.D** (MWG, p. 886). Beliefs with statistically independent types: whatever his
own type, agent `i` believes the profile is distributed according to the prior `P`. -/
def indepBeliefs (P : Measure ((i : ι) → Θ i)) : (i : ι) → Θ i → Measure ((j : ι) → Θ j) :=
  fun _ _ => P

/-- The map `(θ, θ') ↦ (θᵢ, θ₋ᵢ')`. -/
def splice (i : ι) (p : ((j : ι) → Θ j) × ((j : ι) → Θ j)) : (j : ι) → Θ j :=
  update p.2 i (p.1 i)

omit [Fintype ι] in
/-- The map `(θ, θ') ↦ (θᵢ, θ₋ᵢ')` is measurable. -/
theorem measurable_splice (i : ι) : Measurable (splice (Θ := Θ) i) :=
  measurable_update'.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

/-- With independent types, `(θ, θ') ↦ (θᵢ, θ₋ᵢ')` carries `P ⊗ P` to `P`. -/
theorem map_splice (μ : (i : ι) → Measure (Θ i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    ((Measure.pi μ).prod (Measure.pi μ)).map (splice i) = Measure.pi μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_splice i) (MeasurableSet.univ_pi hs)]
  have hpre : splice i ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (update (fun _ => Set.univ) i (s i)) ×ˢ
        Set.pi Set.univ (update s i Set.univ) := by
    ext ⟨θ, θ'⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, splice,
      Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa using h j
        · simp [hj]
      · by_cases hj : j = i
        · subst hj; simp
        · simpa [hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h1 j
      · simpa [hj] using h2 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- **Section 23.D** (MWG, pp. 886, 890). With independent types,
`E_θ[g(θ)] = E_{θᵢ}[E_{θ₋ᵢ}[g(θᵢ, θ₋ᵢ)]]`: integrating the conditional expectation
`θᵢ ↦ ∫ g(θᵢ, θ₋ᵢ') dP(θ')` over `θ` gives the expectation of `g`. -/
theorem integral_integral_update (μ : (i : ι) → Measure (Θ i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) {g : ((j : ι) → Θ j) → ℝ}
    (hg : Integrable g (Measure.pi μ)) :
    ∫ θ, (∫ θ', g (update θ' i (θ i)) ∂Measure.pi μ) ∂Measure.pi μ = ∫ θ, g θ ∂Measure.pi μ := by
  have hmap := map_splice μ i
  have hgm : AEStronglyMeasurable g
      (((Measure.pi μ).prod (Measure.pi μ)).map (splice i)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  have hint : Integrable (g ∘ splice i) ((Measure.pi μ).prod (Measure.pi μ)) := by
    rw [← integrable_map_measure hgm (measurable_splice i).aemeasurable, hmap]
    exact hg
  conv_rhs => rw [← hmap, integral_map (measurable_splice i).aemeasurable hgm]
  rw [integral_prod (fun x => g (splice i x)) hint]
  rfl

omit [DecidableEq ι] in
/-- With independent types, the expectation of a function of `θᵢ` alone is its expectation under
`μᵢ`. -/
theorem integral_eval_pi (μ : (i : ι) → Measure (Θ i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {F : Θ i → ℝ} (hF : AEStronglyMeasurable F (μ i)) :
    ∫ θ, F (θ i) ∂Measure.pi μ = ∫ x, F x ∂μ i :=
  integral_comp_eval hF

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The expected externality mechanism

MWG, Section 23.D, pp. 885-887.

In the quasilinear environment with statistically independent types, the expected externality
(d'Aspremont-Gérard-Varet, Arrow) mechanism pays agent `i`
`ξᵢ(θᵢ) = E_{θ̃₋ᵢ}[∑_{j≠i} vⱼ(k*(θᵢ, θ̃₋ᵢ), θ̃ⱼ)]` plus `hᵢ(θ₋ᵢ)` (23.D.8).

* `agv_bayesianIC`: for any `hᵢ(θ₋ᵢ)`, (23.D.8) is Bayesian incentive compatible.
* `agv_budgetBalanced`: with `hᵢ(θ₋ᵢ) = -(1/(I-1)) ∑_{j≠i} ξⱼ(θⱼ)` (23.D.9) and `I ≥ 2`, the
  transfers balance the budget, (23.D.7).
* `agv_exPostEfficient_bic`: hence, with independent types, an ex post efficient social choice
  function is Bayesian implementable (p. 887).

The integrability hypotheses say that the expectations in (23.D.8) exist; for finitely many
types they hold automatically (`agv_finite`).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
  {K : Type*}

/-- **(23.D.8)** (MWG, p. 886). The expected benefit of the agents `j ≠ i` when `i` announces `a`
and the others tell the truth, `ξᵢ(a) = E_{θ̃₋ᵢ}[∑_{j≠i} vⱼ(k*(a, θ̃₋ᵢ), θ̃ⱼ)]`. -/
noncomputable def expectedExternality (P : Measure ((i : ι) → Θ i))
    (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) (i : ι) (a : Θ i) : ℝ :=
  ∫ θ', ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) ∂P

/-- **(23.D.8)** (MWG, p. 886). The transfers `tᵢ(θ) = ξᵢ(θᵢ) + hᵢ(θ₋ᵢ)`. -/
noncomputable def agvTransfer (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) :
    ((i : ι) → Θ i) → ι → ℝ :=
  fun θ i => expectedExternality P v k i (θ i) + h i θ

/-- **(23.D.9)** (MWG, p. 886). `hᵢ(θ₋ᵢ) = -(1/(I-1)) ∑_{j≠i} ξⱼ(θⱼ)`. -/
noncomputable def agvH (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) : (i : ι) → ((j : ι) → Θ j) → ℝ :=
  fun i θ => -(1 / ((Fintype.card ι : ℝ) - 1)) *
    ∑ j ∈ univ.erase i, expectedExternality P v k j (θ j)

/-- The `hᵢ` of (23.D.9) depends only on `θ₋ᵢ`. -/
theorem agvH_indepOwn (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) : IndepOwn (agvH P v k) := by
  intro i θ a
  simp only [agvH]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Section 23.D** (MWG, p. 886). With independent types (beliefs equal to the prior `P`), the
expected externality mechanism (23.D.8) is Bayesian incentive compatible, for any `hᵢ(θ₋ᵢ)`:
`E[vᵢ(k*(θ̂ᵢ, θ₋ᵢ), θᵢ) + tᵢ(θ̂ᵢ, θ₋ᵢ)] = E[∑ⱼ vⱼ(k*(θ̂ᵢ, θ₋ᵢ), θⱼ)] + E[hᵢ(θ₋ᵢ)]`, which is
maximized by truth telling because `k*` satisfies (23.D.6). -/
theorem agv_bayesianIC (P : Measure ((i : ι) → Θ i)) [IsProbabilityMeasure P]
    {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ) {k : ((i : ι) → Θ i) → K}
    (hk : EfficientProject v k) {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h)
    (hint : ∀ i (a θi : Θ i) j,
      Integrable (fun θ' => v j (k (update θ' i a)) (update θ' i θi j)) P)
    (hhint : ∀ i, Integrable (h i) P) :
    BayesianIC (indepBeliefs P) (qlU v m) (fun θ => (k θ, agvTransfer P v k h θ)) := by
  intro i θi θh
  simp only [indepBeliefs]
  -- the total expected valuation when `i` (of type `θi`) announces `a`
  have key : ∀ a : Θ i, ∫ θ', qlU v m i (k (update θ' i a), agvTransfer P v k h (update θ' i a))
      θi ∂P = ∫ θ', ∑ j, v j (k (update θ' i a)) (update θ' i θi j) ∂P + m i + ∫ θ', h i θ' ∂P := by
    intro a
    have hi1 : Integrable (fun θ' => v i (k (update θ' i a)) θi) P := by
      simpa using hint i a θi i
    have hi2 : Integrable (fun θ' => ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j)) P :=
      integrable_finsetSum _ fun j hj => by
        simpa [update_of_ne (ne_of_mem_erase hj)] using hint i a θi j
    have hsplit : (fun θ' => ∑ j, v j (k (update θ' i a)) (update θ' i θi j)) =
        fun θ' => v i (k (update θ' i a)) θi +
          ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) := by
      funext θ'
      rw [← add_sum_erase _ _ (mem_univ i)]
      simp only [update_self]
      congr 1
      exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    have hpt : (fun θ' => qlU v m i (k (update θ' i a),
        agvTransfer P v k h (update θ' i a)) θi) =
        fun θ' => (v i (k (update θ' i a)) θi + (m i + expectedExternality P v k i a)) +
          h i θ' := by
      funext θ'
      simp only [qlU, agvTransfer, update_self, hh i θ' a]
      ring
    set ξ := expectedExternality P v k i a with hξ
    have e1 : ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) + h i θ' ∂P =
        ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) ∂P + ∫ θ', h i θ' ∂P :=
      integral_add (hi1.add (integrable_const _)) (hhint i)
    have e2 : ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) ∂P =
        ∫ θ', v i (k (update θ' i a)) θi ∂P + (m i + ξ) := by
      rw [integral_add hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    have e3 : ∫ θ', ∑ j, v j (k (update θ' i a)) (update θ' i θi j) ∂P =
        ∫ θ', v i (k (update θ' i a)) θi ∂P +
          ∫ θ', ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) ∂P := by
      rw [hsplit, integral_add hi1 hi2]
    rw [hpt, e1, e2, e3, hξ, expectedExternality]
    ring
  rw [key θh, key θi]
  have hsum : ∀ a : Θ i, Integrable (fun θ' => ∑ j, v j (k (update θ' i a)) (update θ' i θi j)) P :=
    fun a => integrable_finsetSum _ fun j _ => hint i a θi j
  have := integral_mono (hsum θh) (hsum θi) fun θ' => hk (update θ' i θi) (k (update θ' i θh))
  linarith

/-- **(23.D.9)** (MWG, p. 886). With `I ≥ 2` and `hᵢ` as in (23.D.9), the expected externality
mechanism is budget balanced, (23.D.7). -/
theorem agv_budgetBalanced (hI : 2 ≤ Fintype.card ι) (P : Measure ((i : ι) → Θ i))
    (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) :
    BudgetBalanced (agvTransfer P v k (agvH P v k)) := by
  intro θ
  have hI' : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hI
    intro h; linarith
  simp only [agvTransfer, agvH, sum_add_distrib, ← mul_sum,
    sum_sum_erase fun j => expectedExternality P v k j (θ j)]
  field_simp
  ring

/-- **Section 23.D** (MWG, p. 887). With statistically independent types and `I ≥ 2`, the
expected externality mechanism with (23.D.9) implements an ex post efficient social choice
function in Bayesian Nash equilibrium: its project rule satisfies (23.D.6), it is budget
balanced (23.D.7), and it is Bayesian incentive compatible. -/
theorem agv_exPostEfficient_bic (hI : 2 ≤ Fintype.card ι) (P : Measure ((i : ι) → Θ i))
    [IsProbabilityMeasure P] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    (hint : ∀ i (a θi : Θ i) j,
      Integrable (fun θ' => v j (k (update θ' i a)) (update θ' i θi j)) P)
    (hξ : ∀ j : ι, Integrable (fun θ : (l : ι) → Θ l => expectedExternality P v k j (θ j)) P) :
    EfficientProject v k ∧ BudgetBalanced (agvTransfer P v k (agvH P v k)) ∧
      BayesianIC (indepBeliefs P) (qlU v m)
        (fun θ => (k θ, agvTransfer P v k (agvH P v k) θ)) :=
  ⟨hk, agv_budgetBalanced hI P v k, agv_bayesianIC P m hk (agvH_indepOwn P v k) hint
    fun _ => (integrable_finsetSum _ fun j _ => hξ j).const_mul _⟩

/-- **Section 23.D**, the finite case (MWG, p. 887). With finitely many types, the integrability
hypotheses hold, so the expected externality mechanism with (23.D.9) is budget balanced and
Bayesian incentive compatible whenever `k*` satisfies (23.D.6) and `I ≥ 2`. -/
theorem agv_finite (hI : 2 ≤ Fintype.card ι) [Finite ((i : ι) → Θ i)]
    [MeasurableSingletonClass ((i : ι) → Θ i)] (P : Measure ((i : ι) → Θ i))
    [IsProbabilityMeasure P] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) :
    BudgetBalanced (agvTransfer P v k (agvH P v k)) ∧
      BayesianIC (indepBeliefs P) (qlU v m)
        (fun θ => (k θ, agvTransfer P v k (agvH P v k) θ)) :=
  (agv_exPostEfficient_bic hI P m hk (fun _ _ _ _ => Integrable.of_finite)
    fun _ => Integrable.of_finite).2

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two-type beliefs and Example 23.AA.1

MWG, Appendix A, pp. 911-912, Example 23.AA.1 (multiple equilibria in the expected externality
mechanism), with Section 23.D's expected externality mechanism.

Two agents decide on a public project (`k = true` done); each has valuation `θ_L` (type
`false`) or `θ_H` (type `true`) with `θ_H > 0 > θ_L`, `θ_L + θ_H > 0`, independently with
`Prob(θᵢ = θ_L) = λ ∈ (0, 1)`. The project is done unless both valuations are `θ_L`.

* `example_23_AA_1_truth`: truth telling is a Bayesian Nash equilibrium of the expected
  externality mechanism (any `hᵢ(θ₋ᵢ)`).
* **Correction.** MWG claim that "both agents always announce `θ_H`" is a second Bayesian Nash
  equilibrium. It is not: against an opponent who always announces `θ_H`, announcing `θ_L`
  raises the expected transfer by `-λθ_L > 0` and leaves the (certain) project unchanged
  (`example_23_AA_1_alwaysHigh_not_BNE`); MWG's comparison of the expected transfers
  `(λθ_L + (1-λ)θ_H) + hᵢ(θ_H)` and `(1-λ)θ_H + hᵢ(θ_H)` has the wrong sign. In fact truth
  telling is the unique pure strategy Bayesian Nash equilibrium of this mechanism
  (`example_23_AA_1_unique`).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory Finset

/-- The two-point distribution on `Bool` with `Prob(false) = λ`. -/
noncomputable def bern (lam : ℝ) : Measure Bool :=
  ENNReal.ofReal lam • Measure.dirac false + ENNReal.ofReal (1 - lam) • Measure.dirac true

/-- `bern λ` is a probability measure for `λ ∈ [0, 1]`. -/
theorem bern_isProb {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : IsProbabilityMeasure (bern lam) :=
  ⟨by
    simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp⟩

/-- Expectations under `bern λ`. -/
theorem integral_bern (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (g : Bool → ℝ) :
    ∫ x, g x ∂bern lam = lam * g false + (1 - lam) * g true := by
  have hi : ∀ (c : ENNReal) (b : Bool), c ≠ ⊤ → Integrable g (c • Measure.dirac b) :=
    fun c b hc => (integrable_dirac (by simp)).smul_measure hc
  rw [bern, integral_add_measure (hi _ _ ENNReal.ofReal_ne_top) (hi _ _ ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

/-- The valuation of type `b`: `θ_H` for `true`, `θ_L` for `false`. -/
def typeVal (θL θH : ℝ) : Bool → ℝ := fun b => if b then θH else θL

/-- Example 23.AA.1's valuations `vᵢ(k, θᵢ) = θᵢk`. -/
def aaV (θL θH : ℝ) : Fin 2 → Bool → Bool → ℝ := fun _ k b => if k then typeVal θL θH b else 0

/-- Example 23.AA.1's efficient project rule: done unless both valuations are `θ_L`. -/
def aaK (θ : Fin 2 → Bool) : Bool := θ 0 || θ 1

/-- The project rule of Example 23.AA.1 satisfies (23.D.6) when `θ_L < 0` and `θ_L + θ_H > 0`. -/
theorem aaK_efficient {θL θH : ℝ} (hL : θL < 0) (hLH : 0 < θL + θH) :
    EfficientProject (Θ := fun _ => Bool) (aaV θL θH) aaK := by
  intro θ k'
  simp only [Fin.sum_univ_two, aaV, aaK, typeVal]
  obtain ⟨b0, hb0⟩ : ∃ b : Bool, θ 0 = b := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b : Bool, θ 1 = b := ⟨_, rfl⟩
  simp only [hb0, hb1]
  cases b0 <;> cases b1 <;> cases k' <;> simp <;> linarith

/-- The two-agent profile `(a, x)` for agent `0` and `(x, a)` for agent `1`. -/
theorem update_fin_two (θ' : Fin 2 → Bool) (i : Fin 2) (a : Bool) :
    update θ' i a = if i = 0 then ![a, θ' 1] else ![θ' 0, a] := by
  funext j
  fin_cases i <;> fin_cases j <;> simp

/-- The prior of Example 23.AA.1. -/
noncomputable def aaP (lam : ℝ) : Measure (Fin 2 → Bool) := Measure.pi fun _ => bern lam

/-- Agent `i`'s conditional expectation of a function of the profile `(a, θ₋ᵢ)` in
Example 23.AA.1. -/
theorem integral_aaP (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Fin 2) (a : Bool)
    (G : (Fin 2 → Bool) → ℝ) :
    ∫ θ', G (update θ' i a) ∂aaP lam =
      lam * G (update ![false, false] i a) + (1 - lam) * G (update ![true, true] i a) := by
  have := bern_isProb h0 h1
  set c : Fin 2 := if i = 0 then 1 else 0
  have hG : (fun θ' => G (update θ' i a)) =
      fun θ' => (fun x => G (update ![x, x] i a)) (θ' c) := by
    funext θ'
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [c]
  rw [hG, aaP]
  exact (integral_comp_eval (μ := fun _ : Fin 2 => bern lam) (i := c)
    (f := fun x => G (update ![x, x] i a)) (by fun_prop)).trans (integral_bern lam h0 h1 _)

/-- The other agent. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- The expected externality `ξᵢ(a)` in Example 23.AA.1: `ξᵢ(θ_L) = (1-λ)θ_H` and
`ξᵢ(θ_H) = λθ_L + (1-λ)θ_H`. -/
theorem xi_aa (lam θL θH : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Fin 2) (a : Bool) :
    expectedExternality (aaP lam) (aaV θL θH) aaK i a =
      lam * (if a then θL else 0) + (1 - lam) * θH := by
  have e : (fun θ' : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK (update θ' i a)) (θ' j))
      = fun θ' => (fun σ : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK σ) (σ j))
        (update θ' i a) := by
    funext θ'
    exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  unfold expectedExternality
  rw [e, integral_aaP lam h0 h1 i a
    (fun σ : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK σ) (σ j))]
  fin_cases i <;> cases a <;> simp [aaV, aaK, typeVal, sum_erase_eq_sub, Fin.sum_univ_two]

/-- The direct mechanism of Example 23.AA.1: the efficient project with the expected externality
transfers `ξᵢ(θᵢ) + hᵢ(θ₋ᵢ)`. -/
noncomputable def aaMech (lam θL θH : ℝ) (h : Fin 2 → (Fin 2 → Bool) → ℝ) :
    Mechanism (fun _ : Fin 2 => Bool) (Bool × (Fin 2 → ℝ)) :=
  directMechanism (Θ := fun _ => Bool)
    fun θ => (aaK θ, agvTransfer (aaP lam) (aaV θL θH) aaK h θ)

/-- Agent `i`'s gain from announcing `θ_H` rather than `θ_L` in Example 23.AA.1, when the other
agent uses the strategy `s_j`: `θᵢ(1 - q) + λθ_L`, with `q` the probability that the other
announces `θ_H`. -/
theorem aa_gain (lam θL θH : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {h : Fin 2 → (Fin 2 → Bool) → ℝ} (hh : IndepOwn (Θ := fun _ => Bool) h)
    (s : Fin 2 → Bool → Bool) (i : Fin 2) (θi : Bool) :
    interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s i θi true -
      interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s i θi
        false =
      typeVal θL θH θi * (lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then 0 else 1)) + lam * θL := by
  have hform : ∀ a, interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0)
      (aaMech lam θL θH h) s i θi a =
      lam * (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i (aaK (update (play s σ) i a),
        agvTransfer (aaP lam) (aaV θL θH) aaK h (update (play s σ) i a)) θi)
          (update ![false, false] i a) +
      (1 - lam) * (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i (aaK (update (play s σ) i a),
        agvTransfer (aaP lam) (aaV θL θH) aaK h (update (play s σ) i a)) θi)
          (update ![true, true] i a) := by
    intro a
    rw [← integral_aaP lam h0 h1 i a (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i
      (aaK (update (play s σ) i a), agvTransfer (aaP lam) (aaV θL θH) aaK h
        (update (play s σ) i a)) θi)]
    unfold interimUtility indepBeliefs aaMech directMechanism
    congr 1
    funext θ'
    have : update (play s (update θ' i a)) i a = update (play s θ') i a := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [play, update_of_ne hj]
    simp only [this]
  rw [hform true, hform false]
  simp only [qlU, agvTransfer, update_self, Pi.zero_apply, xi_aa lam θL θH h0 h1]
  have hcancel : ∀ b : Bool, h i (update (play s (update ![b, b] i true)) i true) =
      h i (update (play s (update ![b, b] i false)) i false) := by
    intro b
    have e : update (play s (update ![b, b] i true)) i true =
        update (update (play s (update ![b, b] i false)) i false) i true := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [play, update_of_ne hj]
    rw [e, hh]
  rw [hcancel false, hcancel true]
  fin_cases i <;> cases θi <;> cases h0' : s 0 false <;> cases h1' : s 0 true <;>
    cases h2' : s 1 false <;> cases h3' : s 1 true <;>
    simp [aaV, aaK, typeVal, other, play, h0', h1', h2', h3'] <;> ring

/-- **Example 23.AA.1** (MWG, pp. 911-912). Truth telling is a Bayesian Nash equilibrium of the
expected externality mechanism (Section 23.D), for any `hᵢ(θ₋ᵢ)`. -/
theorem example_23_AA_1_truth {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hL : θL < 0)
    (hLH : 0 < θL + θH) {h : Fin 2 → (Fin 2 → Bool) → ℝ}
    (hh : IndepOwn (Θ := fun _ => Bool) h) :
    IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h)
      truthful := by
  have : IsProbabilityMeasure (bern lam) := bern_isProb h0 h1
  have hP : IsProbabilityMeasure (aaP lam) := by unfold aaP; infer_instance
  exact agv_bayesianIC (aaP lam) 0 (aaK_efficient hL hLH) hh
    (fun _ _ _ _ => Integrable.of_finite) fun _ => Integrable.of_finite

/-- **Example 23.AA.1**, correction (MWG, p. 912). "Both agents always announce `θ_H`" is *not* a
Bayesian Nash equilibrium of the expected externality mechanism: against it, announcing `θ_L`
gains `-λθ_L > 0`. -/
theorem example_23_AA_1_alwaysHigh_not_BNE {lam θL θH : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hL : θL < 0) {h : Fin 2 → (Fin 2 → Bool) → ℝ} (hh : IndepOwn (Θ := fun _ => Bool) h) :
    ¬IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h)
      (fun _ _ => true) := by
  intro hB
  have hg := aa_gain lam θL θH h0.le h1 hh (fun _ _ => true) 0 false
  have := hB 0 false false
  simp only [ite_true, mul_zero, add_zero, zero_add] at hg
  have : lam * θL < 0 := mul_neg_of_pos_of_neg h0 hL
  linarith

/-- **Example 23.AA.1**, correction (MWG, p. 912). Truth telling is the *unique* pure strategy
Bayesian Nash equilibrium of the expected externality mechanism in this example (for
`λ ∈ (0, 1)`, `θ_L < 0`, `θ_L + θ_H > 0` and any `hᵢ(θ₋ᵢ)`). -/
theorem example_23_AA_1_unique {lam θL θH : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hL : θL < 0)
    (hLH : 0 < θL + θH) {h : Fin 2 → (Fin 2 → Bool) → ℝ}
    (hh : IndepOwn (Θ := fun _ => Bool) h) (s : Fin 2 → Bool → Bool)
    (hB : IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s) :
    s = truthful := by
  -- low types announce `θ_L`
  have hlow : ∀ i, s i false = false := by
    intro i
    by_contra hne
    have hs : s i false = true := by simpa using hne
    have hg := aa_gain lam θL θH h0.le h1.le hh s i false
    have hdev := hB i false false
    rw [hs] at hdev
    simp only [typeVal, Bool.false_eq_true, ite_false] at hg
    have hq : 0 ≤ lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then (0 : ℝ) else 1) := by
      split_ifs <;> nlinarith
    have : θL * (lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then (0 : ℝ) else 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hL.le hq
    have : lam * θL < 0 := mul_neg_of_pos_of_neg h0 hL
    linarith
  -- high types announce `θ_H`
  have hhigh : ∀ i, s i true = true := by
    intro i
    by_contra hne
    have hs : s i true = false := by simpa using hne
    have hg := aa_gain lam θL θH h0.le h1.le hh s i true
    have hdev := hB i true true
    rw [hs] at hdev
    rw [hlow (other i)] at hg
    simp only [typeVal, Bool.false_eq_true, ite_true, ite_false, mul_one] at hg
    have hq : 0 ≤ (1 - lam) * (if s (other i) true then (0 : ℝ) else 1) := by
      split_ifs <;> nlinarith
    have hH : 0 < θH := by linarith
    have : 0 ≤ θH * ((1 - lam) * (if s (other i) true then (0 : ℝ) else 1)) :=
      mul_nonneg hH.le hq
    nlinarith
  funext i b
  cases b
  · exact hlow i
  · exact hhigh i

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bayesian incentive compatibility with linear utility

MWG, Section 23.D, pp. 887-889: utilities `uᵢ(x, θᵢ) = θᵢvᵢ(k) + tᵢ` with types in intervals
`Θᵢ = [θ̲ᵢ, θ̄ᵢ]`, Proposition 23.D.2.

Agent `i`'s interim expected benefit and transfer when he announces `θ̂ᵢ` (the others telling the
truth) are `v̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[vᵢ(k(θ̂ᵢ, θ₋ᵢ))]` and `t̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[tᵢ(θ̂ᵢ, θ₋ᵢ)]`, and
`Uᵢ(θᵢ) = θᵢv̄ᵢ(θᵢ) + t̄ᵢ(θᵢ)`; (23.D.10) is `E[uᵢ | θᵢ, θ̂ᵢ] = θᵢv̄ᵢ(θ̂ᵢ) + t̄ᵢ(θ̂ᵢ)`.

* `integral_eq_of_slope_bounds`: if `(y - x)v̄(x) ≤ U(y) - U(x) ≤ (y - x)v̄(y)` and `v̄` is
  nondecreasing, then `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} v̄`. (Proved by a telescoping estimate over
  uniform partitions; no differentiability of `U` is used.)
* `linearIC_iff` and **Proposition 23.D.2** (`proposition_23_D_2`): `f` is Bayesian incentive
  compatible iff each `v̄ᵢ` is nondecreasing (23.D.11) and (23.D.12) holds.
* **Correction**: the proof's claim "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all `θᵢ`" fails where `v̄ᵢ` jumps:
  for `k(θ) = 1{θ ≥ 1/2}`, `t(θ) = -k(θ)/2` (Bayesian incentive compatible), `U(θ) =
  max(0, θ - 1/2)` is not differentiable at `1/2` (`proposition_23_D_2_derivative_false`). Only
  the integral form (23.D.12) is needed, and it holds.
* p. 889: the expected transfers are `t̄ᵢ(θᵢ) = t̄ᵢ(θ̲ᵢ) + θ̲ᵢv̄ᵢ(θ̲ᵢ) - θᵢv̄ᵢ(θᵢ) + ∫ v̄ᵢ`
  (`expected_transfer_formula`), and `tᵢ(θ) = t̄ᵢ(θᵢ)` realizes given expected transfers.
-/

namespace MWG.MechanismDesign

open MeasureTheory Set Finset Function

/-- If `v̄` is nondecreasing on `[a, b]` and `(y - x)v̄(x) ≤ U(y) - U(x) ≤ (y - x)v̄(y)` for
`a ≤ x ≤ y ≤ b`, then `U(θ) = U(a) + ∫_a^θ v̄` on `[a, b]`. -/
theorem integral_eq_of_slope_bounds {U vb : ℝ → ℝ} {a b : ℝ} (hvb : MonotoneOn vb (Icc a b))
    (hU : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (y - x) * vb x ≤ U y - U x ∧ U y - U x ≤ (y - x) * vb y) :
    ∀ θ ∈ Icc a b, U θ = U a + ∫ s in a..θ, vb s := by
  intro θ hθ
  have hab : a ≤ b := hθ.1.trans hθ.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  let G : ℝ → ℝ := fun x => U x - ∫ s in a..x, vb s
  have hii : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable vb volume x y :=
    fun x hx y hy => (hvb.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hstep : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |G y - G x| ≤ (y - x) * (vb y - vb x) := by
    intro x hx y hy hxy
    have hsplit : ∫ s in a..y, vb s = (∫ s in a..x, vb s) + ∫ s in x..y, vb s :=
      (intervalIntegral.integral_add_adjacent_intervals (hii a ha x hx) (hii x hx y hy)).symm
    have hlo : (y - x) * vb x ≤ ∫ s in x..y, vb s := by
      have := intervalIntegral.integral_mono_on hxy intervalIntegrable_const (hii x hx y hy)
        fun s hs => hvb hx ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩ hs.1
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hhi : ∫ s in x..y, vb s ≤ (y - x) * vb y := by
      have := intervalIntegral.integral_mono_on hxy (hii x hx y hy) intervalIntegrable_const
        fun s hs => hvb ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩ hy hs.2
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    obtain ⟨h1, h2⟩ := hU x hx y hy hxy
    have hG : G y - G x = (U y - U x) - ∫ s in x..y, vb s := by
      simp only [G, hsplit]; ring
    rw [hG, abs_le]
    constructor <;> nlinarith
  have hvθ : vb a ≤ vb θ := hvb ha hθ hθ.1
  have key : ∀ n : ℕ, 0 < n → |G θ - G a| ≤ (θ - a) * (vb θ - vb a) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set d := (θ - a) / n with hd
    have hd0 : 0 ≤ d := div_nonneg (by linarith [hθ.1]) hn'.le
    let x : ℕ → ℝ := fun k => a + k * d
    have hxn : x n = θ := by simp only [x, d]; field_simp; ring
    have hx0 : x 0 = a := by simp [x]
    have hxmem : ∀ k ≤ n, x k ∈ Icc a b := by
      intro k hk
      have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      refine ⟨by simp only [x]; nlinarith, ?_⟩
      have : x k ≤ x n := by simp only [x]; nlinarith
      rw [hxn] at this
      exact this.trans hθ.2
    have htel : G θ - G a = ∑ k ∈ range n, (G (x (k + 1)) - G (x k)) := by
      rw [sum_range_sub (fun k => G (x k)), hxn, hx0]
    have htel2 : vb θ - vb a = ∑ k ∈ range n, (vb (x (k + 1)) - vb (x k)) := by
      rw [sum_range_sub (fun k => vb (x k)), hxn, hx0]
    have heq : (θ - a) * (vb θ - vb a) / n = d * (vb θ - vb a) := by rw [hd]; ring
    rw [heq, htel, htel2, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hk' : k + 1 ≤ n := mem_range.1 hk
    have hxd : x (k + 1) - x k = d := by simp only [x]; push_cast; ring
    have := hstep (x k) (hxmem k (by omega)) (x (k + 1)) (hxmem (k + 1) hk') (by linarith)
    rwa [hxd] at this
  have hC : 0 ≤ (θ - a) * (vb θ - vb a) := mul_nonneg (by linarith [hθ.1]) (by linarith)
  have hle : |G θ - G a| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ((θ - a) * (vb θ - vb a) / ε)
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hC hε.le) hn
      exact_mod_cast this
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := key n hn0
    have h2 : (θ - a) * (vb θ - vb a) / n ≤ ε := by
      rw [div_le_iff₀ hn']
      rw [div_lt_iff₀ hε] at hn
      linarith
    linarith
  have hG0 : G θ = G a := by
    have := abs_nonneg (G θ - G a)
    have h0 : |G θ - G a| = 0 := le_antisymm hle this
    linarith [abs_eq_zero.1 h0]
  simp only [G, intervalIntegral.integral_same, sub_zero] at hG0
  linarith

/-- **(23.D.1)** in the linear model, for one agent (MWG, p. 888, via (23.D.10)): truth telling
is optimal for every type `θ ∈ [θ̲, θ̄]` facing the interim functions `v̄`, `t̄`:
`θv̄(θ̂) + t̄(θ̂) ≤ θv̄(θ) + t̄(θ)` for all `θ̂ ∈ [θ̲, θ̄]`. -/
def LinearIC (vb tb : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∀ θ ∈ Icc lo hi, ∀ θh ∈ Icc lo hi, θ * vb θh + tb θh ≤ θ * vb θ + tb θ

/-- **Proposition 23.D.2** (MWG, p. 888), one agent's interim functions: incentive compatibility
holds iff `v̄` is nondecreasing (23.D.11) and `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} v̄` (23.D.12), where
`U(θ) = θv̄(θ) + t̄(θ)`. -/
theorem linearIC_iff {vb tb : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC vb tb lo hi ↔ MonotoneOn vb (Icc lo hi) ∧
      ∀ θ ∈ Icc lo hi, θ * vb θ + tb θ = (lo * vb lo + tb lo) + ∫ s in lo..θ, vb s := by
  constructor
  · intro h
    -- (23.D.13)
    have hmono : MonotoneOn vb (Icc lo hi) := by
      intro x hx y hy hxy
      rcases hxy.lt_or_eq with hlt | heq
      · have h1 := h x hx y hy
        have h2 := h y hy x hx
        by_contra hc
        push Not at hc
        nlinarith
      · rw [heq]
    refine ⟨hmono, integral_eq_of_slope_bounds (U := fun θ => θ * vb θ + tb θ) hmono
      fun x hx y hy _ => ⟨?_, ?_⟩⟩
    · have := h y hy x hx; linarith
    · have := h x hx y hy; linarith
  · rintro ⟨hmono, hU⟩ θ hθ θh hθh
    have hii : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, IntervalIntegrable vb volume x y :=
      fun x hx y hy => (hmono.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
    have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hθ.1.trans hθ.2⟩
    have hdiff : (θ * vb θ + tb θ) - (θh * vb θh + tb θh) = ∫ s in θh..θ, vb s := by
      rw [hU θ hθ, hU θh hθh]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii lo hlo θh hθh) (hii θh hθh θ hθ)]
      ring
    rcases le_total θh θ with hle | hle
    · have := intervalIntegral.integral_mono_on hle intervalIntegrable_const (hii θh hθh θ hθ)
        fun s hs => hmono hθh ⟨hθh.1.trans hs.1, hs.2.trans hθ.2⟩ hs.1
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      nlinarith
    · have := intervalIntegral.integral_mono_on hle (hii θ hθ θh hθh) intervalIntegrable_const
        fun s hs => hmono ⟨hθ.1.trans hs.1, hs.2.trans hθh.2⟩ hθh hs.2
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      rw [intervalIntegral.integral_symm] at hdiff
      nlinarith

variable {ι : Type*} [DecidableEq ι] {K : Type*}

/-- Linear utility `uᵢ(x, θᵢ) = θᵢvᵢ(k) + tᵢ` (MWG, p. 887, with `m̄ᵢ = 0`). -/
def linU (vk : ι → K → ℝ) : (i : ι) → K × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => θi * vk i x.1 + x.2 i

/-- Agent `i`'s expected benefit `v̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[vᵢ(k(θ̂ᵢ, θ₋ᵢ))]` (MWG, p. 887). -/
noncomputable def interimBenefit (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (i : ι) (a : ℝ) : ℝ :=
  ∫ θ', vk i (k (update θ' i a)) ∂P

/-- Agent `i`'s expected transfer `t̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[tᵢ(θ̂ᵢ, θ₋ᵢ)]` (MWG, p. 887). -/
noncomputable def interimTransfer (P : Measure (ι → ℝ)) (t : (ι → ℝ) → ι → ℝ) (i : ι)
    (a : ℝ) : ℝ :=
  ∫ θ', t (update θ' i a) i ∂P

/-- Agent `i`'s interim utility from truth telling, `Uᵢ(θᵢ) = θᵢv̄ᵢ(θᵢ) + t̄ᵢ(θᵢ)` (MWG, p. 888). -/
noncomputable def interimU (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (i : ι) (a : ℝ) : ℝ :=
  a * interimBenefit P vk k i a + interimTransfer P t i a

/-- **(23.D.1)** with linear utilities and independent types (MWG, p. 887): for all `i` and
`θᵢ, θ̂ᵢ ∈ [θ̲ᵢ, θ̄ᵢ]`, `E_{θ₋ᵢ}[uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ)] ≤ E_{θ₋ᵢ}[uᵢ(f(θᵢ, θ₋ᵢ), θᵢ)]`, where the
expectation over `θ₋ᵢ` is taken under the prior `P`. -/
def BayesianICOn (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (lo hi : ι → ℝ) : Prop :=
  ∀ i, ∀ θi ∈ Icc (lo i) (hi i), ∀ θh ∈ Icc (lo i) (hi i),
    ∫ θ', linU vk i (k (update θ' i θh), t (update θ' i θh)) θi ∂P ≤
      ∫ θ', linU vk i (k (update θ' i θi), t (update θ' i θi)) θi ∂P

/-- The expectations of (23.D.10) exist: `vᵢ(k(θ̂ᵢ, ·))` and `tᵢ(θ̂ᵢ, ·)` are integrable for every
announcement `θ̂ᵢ ∈ Θᵢ`. -/
def InterimIntegrable (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (lo hi : ι → ℝ) : Prop :=
  ∀ i, ∀ a ∈ Icc (lo i) (hi i), Integrable (fun θ' => vk i (k (update θ' i a))) P ∧
    Integrable (fun θ' => t (update θ' i a) i) P

/-- **(23.D.10)** (MWG, p. 888). `E_{θ₋ᵢ}[uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ)] = θᵢv̄ᵢ(θ̂ᵢ) + t̄ᵢ(θ̂ᵢ)`. -/
theorem eq_23_D_10 {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {i : ι} {a : ℝ} (hv : Integrable (fun θ' => vk i (k (update θ' i a))) P)
    (ht : Integrable (fun θ' => t (update θ' i a) i) P) (θi : ℝ) :
    ∫ θ', linU vk i (k (update θ' i a), t (update θ' i a)) θi ∂P =
      θi * interimBenefit P vk k i a + interimTransfer P t i a := by
  simp only [linU]
  rw [integral_add (hv.const_mul θi) ht, integral_const_mul]
  rfl

/-- **Proposition 23.D.2** (MWG, p. 888). With linear utilities, types in intervals and
independent types (agent `i`'s beliefs about `θ₋ᵢ` are the prior `P` whatever his type), the
social choice function `f = (k, t)` is Bayesian incentive compatible iff for every `i`,
(i) `v̄ᵢ` is nondecreasing on `Θᵢ` (23.D.11) and
(ii) `Uᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ(s) ds` for all `θᵢ ∈ Θᵢ` (23.D.12).
(MWG assume densities `φᵢ > 0`; they are not needed here.) -/
theorem proposition_23_D_2 {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ} (hint : InterimIntegrable P vk k t lo hi) :
    BayesianICOn P vk k t lo hi ↔ ∀ i, MonotoneOn (interimBenefit P vk k i) (Icc (lo i) (hi i)) ∧
      ∀ θ ∈ Icc (lo i) (hi i), interimU P vk k t i θ =
        interimU P vk k t i (lo i) + ∫ s in (lo i)..θ, interimBenefit P vk k i s := by
  have hiff : BayesianICOn P vk k t lo hi ↔
      ∀ i, LinearIC (interimBenefit P vk k i) (interimTransfer P t i) (lo i) (hi i) := by
    refine forall_congr' fun i => ?_
    refine forall₂_congr fun θi hθi => forall₂_congr fun θh hθh => ?_
    rw [eq_23_D_10 (hint i θh hθh).1 (hint i θh hθh).2,
      eq_23_D_10 (hint i θi hθi).1 (hint i θi hθi).2]
  rw [hiff]
  exact forall_congr' fun i => linearIC_iff

/-- **Section 23.D** (MWG, p. 889). For a Bayesian incentive compatible `f`, the expected transfers
are `t̄ᵢ(θᵢ) = t̄ᵢ(θ̲ᵢ) + θ̲ᵢv̄ᵢ(θ̲ᵢ) - θᵢv̄ᵢ(θᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ(s) ds`. -/
theorem expected_transfer_formula {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ} (hint : InterimIntegrable P vk k t lo hi)
    (hf : BayesianICOn P vk k t lo hi) (i : ι) {θ : ℝ} (hθ : θ ∈ Icc (lo i) (hi i)) :
    interimTransfer P t i θ = interimTransfer P t i (lo i) + lo i * interimBenefit P vk k i (lo i)
      - θ * interimBenefit P vk k i θ + ∫ s in (lo i)..θ, interimBenefit P vk k i s := by
  have := ((proposition_23_D_2 hint).1 hf i).2 θ hθ
  simp only [interimU] at this
  linarith

/-- **Section 23.D** (MWG, p. 889). Given expected transfer functions `τᵢ`, the transfers
`tᵢ(θ) = τᵢ(θᵢ)` have expected transfers `t̄ᵢ = τᵢ` (beliefs are probability measures). -/
theorem interimTransfer_of_own {P : Measure (ι → ℝ)} [IsProbabilityMeasure P]
    (τ : ι → ℝ → ℝ) (i : ι) (a : ℝ) :
    interimTransfer P (fun θ j => τ j (θ j)) i a = τ i a := by
  simp [interimTransfer]

/-- **Proposition 23.D.2**, correction (MWG, p. 888). The claim "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all
`θᵢ`" fails at jumps of `v̄ᵢ`: with one agent on `[0, 1]`, `v̄(θ) = 1{θ ≥ 1/2}` and
`t̄ = -v̄/2` satisfy (23.D.1), but `U(θ) = θv̄(θ) + t̄(θ) = max(0, θ - 1/2)` is not differentiable
at `1/2`. -/
theorem proposition_23_D_2_derivative_false :
    let vb : ℝ → ℝ := fun θ => if θ < 1 / 2 then 0 else 1
    LinearIC vb (fun θ => -vb θ / 2) 0 1 ∧
      ¬DifferentiableAt ℝ (fun θ => θ * vb θ + -vb θ / 2) (1 / 2) := by
  intro vb
  have hU : (fun θ => θ * vb θ + -vb θ / 2) = fun θ => ((θ - 1 / 2) + |θ - 1 / 2|) / 2 := by
    funext θ
    simp only [vb]
    split_ifs with h
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith)]; ring
  refine ⟨fun θ _ θh _ => ?_, fun hd => ?_⟩
  · simp only [vb]
    split_ifs <;> nlinarith
  · rw [hU] at hd
    have hd' : DifferentiableAt ℝ (fun θ : ℝ => (θ + 1 / 2 - 1 / 2 + |θ + 1 / 2 - 1 / 2|) / 2) 0 :=
      (differentiableAt_comp_add_const (f := fun θ : ℝ => (θ - 1 / 2 + |θ - 1 / 2|) / 2)
        (a := 0) (b := 1 / 2)).2 (by rw [zero_add]; exact hd)
    have e : (fun θ : ℝ => |θ|) = fun θ => 2 * ((θ + 1 / 2 - 1 / 2 + |θ + 1 / 2 - 1 / 2|) / 2) -
        (θ + 1 / 2 - 1 / 2) := by
      funext θ
      simp only [add_sub_cancel_right]
      ring
    have h3 : DifferentiableAt ℝ (fun θ : ℝ => |θ|) 0 := by
      rw [e]
      exact (hd'.const_mul 2).sub ((differentiableAt_id.add_const _).sub_const _)
    exact not_differentiableAt_abs_zero h3

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Subgame perfect implementation: Example 23.BB.1 (Moore and Repullo)

MWG, Appendix B of Chapter 23, pp. 915-916 (Example 23.BB.1, Figure 23.BB.1), and
Exercise 23.BB.1 (p. 925).

A pure exchange economy with two consumers and two goods; consumer `i`'s type is `θᵢᶜ`
(Cobb-Douglas) or `θᵢᴸ` (Leontief). The social choice function is `f(θ) = xᶜ` if `θ₁ = θ₁ᶜ` and
`f(θ) = xᴸ` if `θ₁ = θ₁ᴸ`. MWG give the allocations only in Figure 23.BB.1; we make the figure
concrete. The Edgeworth box has total endowment `(10, 10)`; an allocation is consumer 1's bundle
`(a, b)` (consumer 2 gets `(10 - a, 10 - b)`); the utilities are
`u₁ᶜ = ab`, `u₁ᴸ = min(a, b)`, `u₂ᶜ = (10 - a)(10 - b)`, `u₂ᴸ = min(10 - a, 10 - b)`
(both Leontief kinks lie on the diagonal, through `xᶜ`), and
`xᶜ = (5, 5)`, `xᴸ = (4, 4)`, `y = (3, 3)`, `z = (9, 2)`. These reproduce the orderings read from
Figure 23.BB.1 (`example_23_BB_1_figure`): consumer 1 always prefers `xᶜ` to `xᴸ` and consumer 2
the reverse; a Cobb-Douglas consumer 1 prefers `z` to `y`, a Leontief consumer 1 prefers `y` to
`z`; consumer 2 of either type ranks `y ≻ xᴸ ≻ xᶜ ≻ z`. (In the figure the two Cobb-Douglas
indifference curves through `xᶜ` are drawn crossing or tangent; our `xᶜ` is on the contract curve,
which plays no role.)

* `example_23_BB_1_lowerContour`, `example_23_BB_1_not_monotonic`,
  `example_23_BB_1_not_strongly`: `Lᵢ(xᶜ, θᶜ) ⊆ Lᵢ(xᶜ, θᴸ)` for `i = 1, 2`, so `f` is not
  monotonic and (Proposition 23.BB.1) no mechanism strongly implements it in Nash equilibrium.
* The three-stage mechanism and its subgame perfect equilibria, defined directly by optimality at
  every decision node (backward induction, which characterizes subgame perfection in this finite
  game of perfect information): `exercise_23_BB_1b`, `example_23_BB_1` (for every profile the
  subgame perfect equilibrium is unique and yields `f(θ)`).
* `exercise_23_BB_1a`: the normal form and all its (pure) Nash equilibria. For `θ₁ = θ₁ᶜ` the
  Nash equilibrium is unique; for `θ₁ = θ₁ᴸ` there are three, one of which yields `xᶜ ≠ f(θ)`.
-/

namespace MWG.MechanismDesign

open Function

/-- **Example 23.BB.1** (MWG, p. 915). Feasible allocations in the Edgeworth box with total
endowment `(10, 10)`, recorded by consumer 1's bundle. -/
abbrev MRBox : Type := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ 10 ∧ 0 ≤ p.2 ∧ p.2 ≤ 10}

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `xᶜ = (5, 5)`. -/
def mrXC : MRBox := ⟨(5, 5), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `xᴸ = (4, 4)`. -/
def mrXL : MRBox := ⟨(4, 4), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `y = (3, 3)`. -/
def mrY : MRBox := ⟨(3, 3), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `z = (9, 2)`. -/
def mrZ : MRBox := ⟨(9, 2), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 915). Utilities: type `true` is Cobb-Douglas (`θᵢᶜ`), type
`false` Leontief (`θᵢᴸ`); consumer 0 is MWG's consumer 1, consumer 1 is MWG's consumer 2. -/
noncomputable def mrU : Fin 2 → MRBox → Bool → ℝ := fun i p b =>
  if i = 0 then (if b then p.1.1 * p.1.2 else min p.1.1 p.1.2)
  else (if b then (10 - p.1.1) * (10 - p.1.2) else min (10 - p.1.1) (10 - p.1.2))

/-- **Example 23.BB.1** (MWG, p. 915). `f(θ) = xᶜ` if `θ₁ = θ₁ᶜ`, `xᴸ` if `θ₁ = θ₁ᴸ`. -/
def mrF (θ : Fin 2 → Bool) : MRBox := if θ 0 then mrXC else mrXL

/-- **Example 23.BB.1** (MWG, p. 916). `xᶜ ≠ xᴸ`. -/
theorem mrXL_ne_mrXC : mrXL ≠ mrXC := by
  intro h
  have h1 := congrArg (fun p : MRBox => p.1.1) h
  norm_num [mrXL, mrXC] at h1

/-- **Example 23.BB.1** (MWG, pp. 915-916, Figure 23.BB.1). The orderings of the figure, for both
types `b` of each consumer: consumer 1 prefers `xᶜ` to `xᴸ`, consumer 2 the reverse; consumer 1
of type `θ₁ᶜ` prefers `z` to `y`, of type `θ₁ᴸ` prefers `xᴸ` to `y` and `y` to `z`; consumer 2
ranks `y ≻ xᴸ ≻ xᶜ ≻ z`. -/
theorem example_23_BB_1_figure :
    (∀ b, mrU 0 mrXL b < mrU 0 mrXC b) ∧ (∀ b, mrU 1 mrXC b < mrU 1 mrXL b) ∧
      mrU 0 mrY true < mrU 0 mrZ true ∧ mrU 0 mrZ true < mrU 0 mrXC true ∧
      mrU 0 mrZ false < mrU 0 mrY false ∧ mrU 0 mrY false < mrU 0 mrXL false ∧
      (∀ b, mrU 1 mrZ b < mrU 1 mrXC b ∧ mrU 1 mrXL b < mrU 1 mrY b) := by
  refine ⟨fun b => ?_, fun b => ?_, ?_, ?_, ?_, ?_, fun b => ?_⟩ <;>
    try cases b
  all_goals norm_num [mrU, mrXC, mrXL, mrY, mrZ, min_def]

/-- **Example 23.BB.1** (MWG, p. 916). `Lᵢ(xᶜ, θᵢᶜ) ⊆ Lᵢ(xᶜ, θᵢᴸ)` for `i = 1, 2`: the Leontief
indifference curve through `xᶜ` has its kink at `xᶜ`, so everything not strictly above `xᶜ` in
both goods is in its lower contour set. -/
theorem example_23_BB_1_lowerContour (i : Fin 2) :
    lowerContour (Θ := fun _ : Fin 2 => Bool) mrU i mrXC true ⊆
      lowerContour (Θ := fun _ : Fin 2 => Bool) mrU i mrXC false := by
  intro p hp
  have hp' : mrU i p true ≤ mrU i mrXC true := hp
  change mrU i p false ≤ mrU i mrXC false
  obtain ⟨⟨a, b⟩, ha0, ha1, hb0, hb1⟩ := p
  fin_cases i
  · simp only [mrU, mrXC, ite_true, Fin.zero_eta, Fin.isValue] at hp' ⊢
    rw [min_self]
    by_contra h
    have h1 : 5 < a := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
    have h2 : 5 < b := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
    nlinarith
  · simp only [mrU, mrXC, Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true] at hp' ⊢
    rw [show min ((10 : ℝ) - 5) (10 - 5) = 5 by norm_num]
    by_contra h
    have h1 : 5 < 10 - a := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
    have h2 : 5 < 10 - b := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
    nlinarith

/-- **Example 23.BB.1** (MWG, p. 916). `f` is not monotonic: the lower contour sets of
`xᶜ = f(θᶜ)` expand from `θᶜ = (θ₁ᶜ, θ₂ᶜ)` to `θᴸ = (θ₁ᴸ, θ₂ᴸ)`, but `f(θᴸ) = xᴸ ≠ xᶜ`. -/
theorem example_23_BB_1_not_monotonic :
    ¬MonotonicSCF (Θ := fun _ : Fin 2 => Bool) mrU mrF := by
  intro hM
  have h := hM (fun _ => true) (fun _ => false) fun i => example_23_BB_1_lowerContour i
  exact mrXL_ne_mrXC h

/-- **Example 23.BB.1** (MWG, p. 916). By Proposition 23.BB.1, no mechanism strongly implements
`f` in Nash equilibrium. -/
theorem example_23_BB_1_not_strongly {S : Fin 2 → Type*} (Γ : Mechanism S MRBox) :
    ¬StronglyImplementsInNash (Θ := fun _ : Fin 2 => Bool) mrU Γ mrF :=
  fun h => example_23_BB_1_not_monotonic (proposition_23_BB_1 h)

/-- **Example 23.BB.1** (MWG, p. 916). Stage 3: consumer 1 chooses `y` (`true`) or `z`
(`false`). -/
def mrStage3 (c3 : Bool) : MRBox := if c3 then mrY else mrZ

/-- **Example 23.BB.1** (MWG, p. 916). Stage 2: consumer 2 agrees (`true`, outcome `xᶜ`) or
challenges (`false`, go to stage 3, where consumer 1 plays `c3`). -/
def mrStage2 (ag c3 : Bool) : MRBox := if ag then mrXC else mrStage3 c3

/-- **Example 23.BB.1** (MWG, p. 916) and **Exercise 23.BB.1(a)** (MWG, p. 925). The outcome
function of the normal form: consumer 1's strategy is `(a₁, c₃)` (stage 1: announce "C"
(`true`) or "L" (`false`, outcome `xᴸ`); stage 3 choice), consumer 2's strategy is his stage-2
action. -/
def mrOutcome (s1 : Bool × Bool) (ag : Bool) : MRBox := if s1.1 then mrStage2 ag s1.2 else mrXL

/-- **Example 23.BB.1** (MWG, p. 916). Subgame perfect Nash equilibrium of the three-stage game of
perfect information at the profile `θ`: consumer 1's stage-3 choice is optimal, consumer 2's
stage-2 action is optimal given it, and consumer 1's stage-1 announcement is optimal given
both (optimality at every decision node, i.e. backward induction). -/
def IsMRSubgamePerfect (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) : Prop :=
  (∀ c, mrU 0 (mrStage3 c) (θ 0) ≤ mrU 0 (mrStage3 s1.2) (θ 0)) ∧
    (∀ g, mrU 1 (mrStage2 g s1.2) (θ 1) ≤ mrU 1 (mrStage2 ag s1.2) (θ 1)) ∧
    (∀ a, mrU 0 (mrOutcome (a, s1.2) ag) (θ 0) ≤ mrU 0 (mrOutcome s1 ag) (θ 0))

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). Nash equilibrium of the normal form at `θ`. -/
def IsMRNash (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) : Prop :=
  (∀ s1', mrU 0 (mrOutcome s1' ag) (θ 0) ≤ mrU 0 (mrOutcome s1 ag) (θ 0)) ∧
    (∀ g, mrU 1 (mrOutcome s1 g) (θ 1) ≤ mrU 1 (mrOutcome s1 ag) (θ 1))

/-- **Exercise 23.BB.1(b)** (MWG, p. 925). For every profile the subgame perfect equilibrium is:
consumer 1 announces his type truthfully ("C" iff `θ₁ = θ₁ᶜ`) and at stage 3 picks `z` if
Cobb-Douglas, `y` if Leontief; consumer 2 agrees iff `θ₁ = θ₁ᶜ`. -/
theorem exercise_23_BB_1b (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) :
    IsMRSubgamePerfect θ s1 ag ↔ s1 = (θ 0, !θ 0) ∧ ag = θ 0 := by
  obtain ⟨a, c⟩ := s1
  cases h0 : θ 0 <;> cases h1 : θ 1 <;> cases a <;> cases c <;> cases ag <;>
    norm_num [IsMRSubgamePerfect, mrOutcome, mrStage2, mrStage3, Bool.forall_bool, h0, h1, mrU,
      mrXC, mrXL, mrY, mrZ, min_def]

/-- **Example 23.BB.1** (MWG, p. 916). For each profile `θ` the three-stage mechanism has a unique
subgame perfect Nash equilibrium, and it results in `f(θ)`: `f` is strongly implemented in
subgame perfect equilibrium. -/
theorem example_23_BB_1 (θ : Fin 2 → Bool) :
    (∃! s : (Bool × Bool) × Bool, IsMRSubgamePerfect θ s.1 s.2) ∧
      ∀ s1 ag, IsMRSubgamePerfect θ s1 ag → mrOutcome s1 ag = mrF θ := by
  refine ⟨⟨((θ 0, !θ 0), θ 0), (exercise_23_BB_1b θ _ _).2 ⟨rfl, rfl⟩, fun s hs => ?_⟩,
    fun s1 ag hs => ?_⟩
  · obtain ⟨h1, h2⟩ := (exercise_23_BB_1b θ s.1 s.2).1 hs
    exact Prod.ext h1 h2
  · obtain ⟨rfl, rfl⟩ := (exercise_23_BB_1b θ s1 ag).1 hs
    cases h0 : θ 0 <;> simp [mrOutcome, mrStage2, mrF, h0]

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). The pure Nash equilibria of the normal form. If
`θ₁ = θ₁ᶜ` the only one is ((C, z), agree), with outcome `xᶜ`. If `θ₁ = θ₁ᴸ` they are
((L, y), challenge), ((L, z), challenge) (outcome `xᴸ`) and ((C, z), agree) (outcome `xᶜ`).
Consumer 2's type does not matter. -/
theorem exercise_23_BB_1a (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) :
    IsMRNash θ s1 ag ↔
      (s1 = (true, false) ∧ ag = true) ∨ (θ 0 = false ∧ s1.1 = false ∧ ag = false) := by
  obtain ⟨a, c⟩ := s1
  cases h0 : θ 0 <;> cases h1 : θ 1 <;> cases a <;> cases c <;> cases ag <;>
    norm_num [IsMRNash, mrOutcome, mrStage2, mrStage3, Bool.forall_bool, Prod.forall, h0, h1,
      mrU, mrXC, mrXL, mrY, mrZ, min_def]

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). With `θ₁ = θ₁ᴸ`, ((C, z), agree) is a Nash equilibrium
of the normal form with outcome `xᶜ ≠ f(θ)`: the mechanism does not strongly implement `f` in
Nash equilibrium (consumer 2's threat to challenge is not credible). -/
theorem exercise_23_BB_1a_not_strongly (θ : Fin 2 → Bool) (h0 : θ 0 = false) :
    IsMRNash θ (true, false) true ∧ mrOutcome (true, false) true ≠ mrF θ := by
  refine ⟨(exercise_23_BB_1a θ _ _).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
  simp only [mrOutcome, mrStage2, mrF, h0, ite_true]
  exact fun h => mrXL_ne_mrXC (by simpa using h.symm)

/-- **Exercise 23.BB.1** (MWG, p. 925). Every subgame perfect equilibrium is a Nash equilibrium of
the normal form. -/
theorem exercise_23_BB_1_spe_nash (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool)
    (h : IsMRSubgamePerfect θ s1 ag) : IsMRNash θ s1 ag := by
  obtain ⟨rfl, rfl⟩ := (exercise_23_BB_1b θ s1 ag).1 h
  rw [exercise_23_BB_1a]
  cases θ 0 <;> simp

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Type distributions with a density

MWG, Section 23.D, pp. 887-891, and Section 23.E, pp. 894-896: agent `i`'s type `θᵢ` lies in
`[θ̲ᵢ, θ̄ᵢ]` and is distributed with distribution function `Φᵢ` and density `φᵢ(θᵢ) > 0` on
`[θ̲ᵢ, θ̄ᵢ]`.

* `TypeDensity`: a density `φ` that is measurable, strictly positive on `[θ̲, θ̄]` (`θ̲ < θ̄`),
  zero outside, with total mass one; its distribution `TypeDensity.measure` is
  `volume.withDensity φ`.
* The distribution is a probability measure concentrated on `[θ̲, θ̄]`
  (`TypeDensity.isProbabilityMeasure`, `TypeDensity.measure_compl_Icc`), has no atoms
  (`TypeDensity.measure_singleton`) and gives positive probability to every open subinterval
  (`TypeDensity.measure_Ioo_pos`); `∫ f dμ = ∫_{θ̲}^{θ̄} f φ` (`TypeDensity.integral_eq`);
  with `Φ(x) = ∫_{θ̲}^{x} φ` (`TypeDensity.cdf`), `μ([s, ∞)) = 1 - Φ(s)`
  (`TypeDensity.measureReal_Ici`).
* The Fubini identity behind MWG's integration by parts on p. 890:
  `E[∫_{θ̲}^{θ} w] = ∫_{θ̲}^{θ̄} w(s) μ([s, ∞)) ds = ∫_{θ̲}^{θ̄} w(s)(1 - Φ(s)) ds`
  (`td_integral_integral_eq`, `TypeDensity.integral_integral_eq`); MWG's integration by parts
  assumes more regularity, the Fubini form needs only `w` integrable on `[θ̲, θ̄]`.
* The uniform distribution on `[a, b]` (`uniformDensity`), in particular on `[0, 1]`.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Section 23.D** (MWG, p. 887). A type distribution on `[θ̲, θ̄]` with a strictly positive
density `φ`: `φ` is measurable, `φ > 0` on `[θ̲, θ̄]`, `φ = 0` outside, and `∫_{θ̲}^{θ̄} φ = 1`. -/
structure TypeDensity where
  /-- The lowest type `θ̲`. -/
  lo : ℝ
  /-- The highest type `θ̄`. -/
  hi : ℝ
  lo_lt_hi : lo < hi
  /-- The density `φ`. -/
  dens : ℝ → ℝ
  measurable_dens : Measurable dens
  dens_pos : ∀ x ∈ Set.Icc lo hi, 0 < dens x
  dens_eq_zero : ∀ x, x ∉ Set.Icc lo hi → dens x = 0
  integral_dens : ∫ x in lo..hi, dens x = 1

namespace TypeDensity

variable (D : TypeDensity)

/-- The distribution of types, `μ = φ · volume`. -/
noncomputable def measure : Measure ℝ :=
  volume.withDensity fun x => ((D.dens x).toNNReal : ENNReal)

/-- The distribution function `Φ(x) = ∫_{θ̲}^{x} φ`. -/
noncomputable def cdf (x : ℝ) : ℝ := ∫ s in D.lo..x, D.dens s

/-- The density is nonnegative. -/
theorem dens_nonneg (x : ℝ) : 0 ≤ D.dens x := by
  by_cases hx : x ∈ Set.Icc D.lo D.hi
  · exact (D.dens_pos x hx).le
  · rw [D.dens_eq_zero x hx]

/-- The density is integrable on `[θ̲, θ̄]` (its integral is `1 ≠ 0`). -/
theorem intervalIntegrable_dens : IntervalIntegrable D.dens volume D.lo D.hi := by
  by_contra h
  have := D.integral_dens
  rw [intervalIntegral.integral_undef h] at this
  exact zero_ne_one this

/-- A function vanishing outside `[θ̲, θ̄]` has `∫ g = ∫_{θ̲}^{θ̄} g`. -/
theorem integral_volume_eq {g : ℝ → ℝ} (hg : ∀ x, x ∉ Set.Icc D.lo D.hi → g x = 0) :
    ∫ x, g x = ∫ x in D.lo..D.hi, g x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le D.lo_lt_hi.le]

/-- The density is integrable on `ℝ`. -/
theorem integrable_dens : Integrable D.dens := by
  have h : D.dens = (Set.Icc D.lo D.hi).indicator D.dens := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]
  rw [h, integrable_indicator_iff measurableSet_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le).1 D.intervalIntegrable_dens

/-- **Section 23.D** (MWG, p. 890). `∫ f dμ = ∫_{θ̲}^{θ̄} f(x) φ(x) dx`. -/
theorem integral_eq (f : ℝ → ℝ) : ∫ x, f x ∂D.measure = ∫ x in D.lo..D.hi, f x * D.dens x := by
  rw [measure, integral_withDensity_eq_integral_smul D.measurable_dens.real_toNNReal]
  have e : ∀ x, (D.dens x).toNNReal • f x = f x * D.dens x := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (D.dens_nonneg x), smul_eq_mul, mul_comm]
  simp only [e]
  exact D.integral_volume_eq fun x hx => by rw [D.dens_eq_zero x hx, mul_zero]

/-- The type distribution is a probability measure. -/
theorem isProbabilityMeasure : IsProbabilityMeasure D.measure := by
  refine ⟨?_⟩
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ x, ENNReal.ofReal (D.dens x) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal D.integrable_dens
    (Filter.Eventually.of_forall D.dens_nonneg), D.integral_volume_eq D.dens_eq_zero,
    D.integral_dens, ENNReal.ofReal_one]

/-- The type distribution is concentrated on `[θ̲, θ̄]`. -/
theorem measure_compl_Icc : D.measure (Set.Icc D.lo D.hi)ᶜ = 0 := by
  rw [measure, withDensity_apply _ measurableSet_Icc.compl]
  rw [setLIntegral_congr_fun measurableSet_Icc.compl (g := fun _ => 0)
    fun x hx => by simp [D.dens_eq_zero x hx]]
  simp

/-- **Section 23.D** (MWG, p. 887). The type distribution has no atoms. -/
theorem measure_singleton (x : ℝ) : D.measure {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- Probabilities of sets as integrals of the density. -/
theorem measure_eq_ofReal {s : Set ℝ} (hs : MeasurableSet s) :
    D.measure s = ENNReal.ofReal (∫ x in s, D.dens x) := by
  rw [measure, withDensity_apply _ hs]
  rw [ofReal_integral_eq_lintegral_ofReal D.integrable_dens.integrableOn
    (Filter.Eventually.of_forall D.dens_nonneg)]
  rfl

/-- **Section 23.D** (MWG, p. 887). With `φ > 0` on `[θ̲, θ̄]`, every open subinterval has
positive probability. -/
theorem measure_Ioo_pos {a b : ℝ} (ha : D.lo ≤ a) (hab : a < b) (hb : b ≤ D.hi) :
    0 < D.measure (Set.Ioo a b) := by
  rw [D.measure_eq_ofReal measurableSet_Ioo, ENNReal.ofReal_pos, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (D.integrable_dens.intervalIntegrable) (fun x hx => D.dens_pos x
      ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩) hab

/-- `x ↦ 1_A(x) φ(x)` is integrable. -/
theorem integrable_indicator_mul {A : Set ℝ} (hA : MeasurableSet A) :
    Integrable fun x => A.indicator 1 x * D.dens x := by
  refine (D.integrable_dens.indicator hA).congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ A <;> simp [hx]

/-- `μ((-∞, s]) = Φ(s)` for `s ∈ [θ̲, θ̄]`. -/
theorem measureReal_Iic {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    D.measure.real (Set.Iic s) = D.cdf s := by
  rw [← integral_indicator_one measurableSet_Iic, D.integral_eq,
    ← intervalIntegral.integral_add_adjacent_intervals (b := s)]
  · have h1 : ∫ x in D.lo..s, (Set.Iic s).indicator 1 x * D.dens x = D.cdf s := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hs.1] at hx
      simp [Set.indicator_of_mem (Set.mem_Iic.2 hx.2)]
    have h2 : ∫ x in s..D.hi, (Set.Iic s).indicator 1 x * D.dens x = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [Set.uIoc_of_le hs.2] at hx
      simp [Set.indicator_of_notMem (show x ∉ Set.Iic s from fun h => absurd hx.1 (not_lt.2 h))]
    rw [h1, h2, add_zero]
  · exact (D.integrable_indicator_mul measurableSet_Iic).intervalIntegrable
  · exact (D.integrable_indicator_mul measurableSet_Iic).intervalIntegrable

/-- **Section 23.D** (MWG, p. 890). `μ([s, ∞)) = 1 - Φ(s)` for `s ∈ [θ̲, θ̄]`. -/
theorem measureReal_Ici {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    D.measure.real (Set.Ici s) = 1 - D.cdf s := by
  have := D.isProbabilityMeasure
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr (Iio_ae_eq_Iic' (D.measure_singleton s)), D.measureReal_Iic hs]

end TypeDensity

/-- **Section 23.D** (MWG, p. 890), the step "integration by parts implies", in Fubini form and
for any type distribution `ν` concentrated on `[θ̲, θ̄]`: for `w` integrable on `[θ̲, θ̄]`,
`E_ν[∫_{θ̲}^{θ} w(s) ds] = ∫_{θ̲}^{θ̄} w(s) ν([s, ∞)) ds`. -/
theorem td_integral_integral_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {lo hi : ℝ}
    (hle : lo ≤ hi) (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume lo hi) :
    ∫ θ, (∫ s in lo..θ, w s) ∂ν = ∫ s in lo..hi, w s * ν.real (Set.Ici s) := by
  have hwρ : Integrable w (volume.restrict (Set.Ioc lo hi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hw
  set F : ℝ → ℝ → ℝ := fun θ s => (Set.Ici s).indicator (fun _ => w s) θ with hF
  have hFm : Integrable (Function.uncurry F) (ν.prod (volume.restrict (Set.Ioc lo hi))) := by
    have hg : Integrable (fun p : ℝ × ℝ => w p.2) (ν.prod (volume.restrict (Set.Ioc lo hi))) :=
      hwρ.comp_snd ν
    have heq : Function.uncurry F = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => w p.2) := by
      funext p
      by_cases h : p.2 ≤ p.1 <;> simp [hF, Set.indicator, h, Function.uncurry]
    rw [heq]
    exact hg.indicator (measurableSet_le measurable_snd measurable_fst)
  have hL : ∀ᵐ θ ∂ν, ∫ s in lo..θ, w s = ∫ s in Set.Ioc lo hi, F θ s := by
    filter_upwards [mem_ae_iff.2 hsupp] with θ hθ
    rw [intervalIntegral.integral_of_le hθ.1]
    have e : ∀ s, F θ s = (Set.Iic θ).indicator w s := by
      intro s
      by_cases h : s ≤ θ <;> simp [hF, Set.indicator, h]
    simp only [e]
    rw [setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, inf_eq_right.2 hθ.2]
  have hR : ∫ s in Set.Ioc lo hi, ∫ θ, F θ s ∂ν = ∫ s in lo..hi, w s * ν.real (Set.Ici s) := by
    rw [intervalIntegral.integral_of_le hle]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hF]
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
  rw [integral_congr_ae hL, integral_integral_swap hFm, hR]

namespace TypeDensity

variable (D : TypeDensity)

/-- **Section 23.D** (MWG, p. 890), "integration by parts implies": for `w` integrable on
`[θ̲, θ̄]`, `∫_{θ̲}^{θ̄} (∫_{θ̲}^{θ} w(s) ds) φ(θ) dθ = ∫_{θ̲}^{θ̄} w(θ)(1 - Φ(θ)) dθ`. -/
theorem integral_integral_eq {w : ℝ → ℝ} (hw : IntervalIntegrable w volume D.lo D.hi) :
    ∫ x in D.lo..D.hi, (∫ s in D.lo..x, w s) * D.dens x =
      ∫ s in D.lo..D.hi, w s * (1 - D.cdf s) := by
  have := D.isProbabilityMeasure
  rw [← D.integral_eq, td_integral_integral_eq D.measure D.lo_lt_hi.le D.measure_compl_Icc hw]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le D.lo_lt_hi.le] at hs
  simp only [D.measureReal_Ici hs]

end TypeDensity

/-- The uniform distribution on `[a, b]`, density `1/(b - a)` on `[a, b]`. -/
noncomputable def uniformDensity (a b : ℝ) (h : a < b) : TypeDensity where
  lo := a
  hi := b
  lo_lt_hi := h
  dens := (Set.Icc a b).indicator fun _ => (b - a)⁻¹
  measurable_dens := measurable_const.indicator measurableSet_Icc
  dens_pos := fun x hx => by rw [Set.indicator_of_mem hx]; exact inv_pos.2 (sub_pos.2 h)
  dens_eq_zero := fun x hx => Set.indicator_of_notMem hx _
  integral_dens := by
    rw [intervalIntegral.integral_congr (g := fun _ => (b - a)⁻¹) fun x hx => by
      rw [Set.uIcc_of_le h.le] at hx; exact Set.indicator_of_mem hx _]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_inv_cancel₀ (sub_pos.2 h).ne']

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def uniform01 : TypeDensity := uniformDensity 0 1 zero_lt_one

/-- Expectations under the uniform distribution on `[0, 1]`: `E[f] = ∫_0^1 f`. -/
theorem uniform01_integral (f : ℝ → ℝ) : ∫ x, f x ∂uniform01.measure = ∫ x in (0 : ℝ)..1, f x := by
  rw [uniform01.integral_eq]
  refine intervalIntegral.integral_congr fun x hx => ?_
  change x ∈ Set.uIcc (0 : ℝ) 1 at hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  change f x * (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) x = f x
  rw [Set.indicator_of_mem hx]
  norm_num

/-- The uniform distribution on `[0, 1]` has `Φ(x) = x` on `[0, 1]`. -/
theorem uniform01_cdf {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : uniform01.cdf x = x := by
  change ∫ s in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) s = x
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun s hs => by
    rw [Set.uIcc_of_le hx.1] at hs
    rw [Set.indicator_of_mem (show s ∈ Set.Icc (0 : ℝ) 1 from ⟨hs.1, hs.2.trans hx.2⟩)]
    norm_num]
  simp

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The revenue equivalence theorem

MWG, Section 23.D, pp. 889-891, and Exercises 23.D.2, 23.D.3 (p. 921).

The auction setting (p. 889): `I` buyers, `yᵢ(θ)` buyer `i`'s probability of getting the good,
`vᵢ(y) = yᵢ` (`allocV`), linear utilities `θᵢyᵢ + tᵢ`, independent types `P = ∏ᵢ μᵢ`.

* `re_expected_transfer`: `E[tᵢ(θ)] = E[t̄ᵢ(θᵢ)]`; `re_interimTransfer_eq`: for a Bayesian
  incentive compatible `f`, `t̄ᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ - θᵢȳᵢ(θᵢ)` on `Θᵢ`.
* **Proposition 23.D.3** (`proposition_23_D_3`), at the level of social choice functions as in
  MWG's proof: two Bayesian incentive compatible social choice functions with the same `y` and the
  same `Uᵢ(θ̲ᵢ)` have the same expected payment from every buyer, hence the same expected revenue.
  Only `μᵢ([θ̲ᵢ, θ̄ᵢ]ᶜ) = 0` is used, not densities.
* With densities (`TypeDensity`): (23.D.14) `eq_23_D_14`, (23.D.15) `eq_23_D_15`, (23.D.16)
  `eq_23_D_16`, with `Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)` (`TypeDensity.virtualValue`). MWG's
  integration by parts is replaced by the Fubini identity `TypeDensity.integral_integral_eq`;
  (23.D.15)-(23.D.16) assume that `E[yᵢ(θ)Jᵢ(θᵢ)]` exists (`eq_23_D_16_instance`: it does, and
  all other hypotheses hold, for the first-price rule with uniform types).
* Two buyers uniform on `[0, 1]` (`unif2`): Exercise 23.D.3 (`exercise_23_D_3`,
  `exercise_23_D_3_revenue_equivalence`): the first-price equilibrium social choice function
  (23.B.9)-(23.B.14) and the second-price one are Bayesian incentive compatible, have the same
  `y`, `Uᵢ(0) = 0`, and expected revenue `1/3` each.
* Exercise 23.D.2: the expected externality mechanism for bilateral trade with uniform types has
  `ξᵢ(a) = (1 - a²)/2` and transfers `t₀ = (θ₁² - θ₀²)/2 = -t₁` (`exercise_23_D_2a`); truth
  telling is a Bayesian Nash equilibrium (`exercise_23_D_2b`, via `agv_bayesianIC`).

No corrections; departures: the revenue equivalence theorem needs no densities, and integrability
hypotheses (expectations exist) are explicit.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The auction setting (MWG, p. 889): an outcome is `(y, t)` with `y = (y₁, …, y_I)` the buyers'
probabilities of getting the good, and buyer `i`'s benefit is `vᵢ(y) = yᵢ`. -/
def allocV : ι → (ι → ℝ) → ℝ := fun i y => y i

/-- Points of `[a, b]` are bounded by `|a| + |b|`. -/
theorem re_abs_le_of_mem {x a b : ℝ} (h : x ∈ Set.Icc a b) : |x| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, h.1]
  · linarith [le_abs_self b, abs_nonneg a, h.2]

/-- With independent types, `θ ↦ E_{θ₋ᵢ}[g(θᵢ, θ₋ᵢ)]` is integrable when `g` is. -/
theorem re_integrable_integral_update (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {g : (ι → ℝ) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    Integrable (fun θ => ∫ θ', g (update θ' i (θ i)) ∂Measure.pi μ) (Measure.pi μ) := by
  have hmap := map_splice (Θ := fun _ => ℝ) μ i
  have hgm : AEStronglyMeasurable g
      (((Measure.pi μ).prod (Measure.pi μ)).map (splice i)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  have hint : Integrable (g ∘ splice i) ((Measure.pi μ).prod (Measure.pi μ)) := by
    rw [← integrable_map_measure hgm (measurable_splice i).aemeasurable, hmap]
    exact hg
  exact hint.integral_prod_left

omit [DecidableEq ι] in
/-- If each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]`, almost every profile lies in `Θ`. -/
theorem re_ae_mem (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) :
    ∀ᵐ θ ∂Measure.pi μ, ∀ i, θ i ∈ Set.Icc (lo i) (hi i) := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ x ∂μ i, x ∈ Set.Icc (lo i) (hi i) := mem_ae_iff.2 (hsupp i)
  exact Measure.tendsto_eval_ae_ae.eventually h

/-- If each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]` and `a ∈ Θᵢ`, almost every `(a, θ₋ᵢ)` lies in
`Θ`. -/
theorem re_ae_update_mem (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {i : ι} {a : ℝ}
    (ha : a ∈ Set.Icc (lo i) (hi i)) :
    ∀ᵐ θ ∂Measure.pi μ, ∀ j, update θ i a j ∈ Set.Icc (lo j) (hi j) := by
  filter_upwards [re_ae_mem μ hsupp] with θ hθ j
  by_cases hj : j = i
  · subst hj; simpa using ha
  · simpa [hj] using hθ j

/-- With independent types, `E[tᵢ(θ)] = E_{θᵢ}[t̄ᵢ(θᵢ)]` (MWG, p. 890). -/
theorem re_expected_transfer (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {t : (ι → ℝ) → ι → ℝ} (i : ι) (ht : Integrable (fun θ => t θ i) (Measure.pi μ)) :
    ∫ θ, t θ i ∂Measure.pi μ = ∫ θ, interimTransfer (Measure.pi μ) t i (θ i) ∂Measure.pi μ :=
  (integral_integral_update (Θ := fun _ => ℝ) μ i ht).symm

omit [Fintype ι] in
/-- For a Bayesian incentive compatible `f = (y, t)` in the linear model, the expected transfer of
type `θᵢ ∈ Θᵢ` is determined by `y` and `Uᵢ(θ̲ᵢ)`:
`t̄ᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ - θᵢv̄ᵢ(θᵢ)` (MWG, pp. 889-890). -/
theorem re_interimTransfer_eq {K : Type*} {P : Measure (ι → ℝ)} {vk : ι → K → ℝ}
    {k : (ι → ℝ) → K} {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ}
    (hint : InterimIntegrable P vk k t lo hi) (hf : BayesianICOn P vk k t lo hi) (i : ι) {x : ℝ}
    (hx : x ∈ Set.Icc (lo i) (hi i)) :
    interimTransfer P t i x = interimU P vk k t i (lo i) + (∫ s in (lo i)..x,
      interimBenefit P vk k i s) - x * interimBenefit P vk k i x := by
  have := ((proposition_23_D_2 hint).1 hf i).2 x hx
  simp only [interimU] at this ⊢
  linarith

/-- **Proposition 23.D.3** (MWG, p. 890), the revenue equivalence theorem, at the level of social
choice functions as in MWG's proof. Buyers' valuations are independent (`P = ∏ᵢ μᵢ`) with `μᵢ`
concentrated on `[θ̲ᵢ, θ̄ᵢ]`. If two Bayesian incentive compatible social choice functions
`(y, t)` and `(y, t')` have (i) the same allocation probabilities `y(θ)` and (ii) the same
`Uᵢ(θ̲ᵢ)` for every buyer, then each buyer's expected payment is the same, so the seller's expected
revenue `∑ᵢ E[-tᵢ(θ)]` is the same. Densities are not needed (only the support condition); the
integrability hypotheses say that the expectations exist. -/
theorem proposition_23_D_3 (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {lo hi : ι → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (ι → ℝ) → ι → ℝ} {t t' : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y t' lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => t' θ i) (Measure.pi μ))
    (hf : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hf' : BayesianICOn (Measure.pi μ) allocV y t' lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y t i (lo i) =
      interimU (Measure.pi μ) allocV y t' i (lo i)) :
    (∀ i, ∫ θ, -t θ i ∂Measure.pi μ = ∫ θ, -t' θ i ∂Measure.pi μ) ∧
      ∑ i, ∫ θ, -t θ i ∂Measure.pi μ = ∑ i, ∫ θ, -t' θ i ∂Measure.pi μ := by
  have hi : ∀ i, ∫ θ, -t θ i ∂Measure.pi μ = ∫ θ, -t' θ i ∂Measure.pi μ := by
    intro i
    rw [integral_neg, integral_neg, re_expected_transfer μ i (ht i),
      re_expected_transfer μ i (ht' i)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [re_ae_mem μ hsupp] with θ hθ
    rw [re_interimTransfer_eq hint hf i (hθ i), re_interimTransfer_eq hint' hf' i (hθ i), hU i]
  exact ⟨hi, Finset.sum_congr rfl fun i _ => hi i⟩

/-! ### Densities: (23.D.14)-(23.D.16) -/

/-- MWG's virtual valuation `θ - (1 - Φ(θ))/φ(θ)` of (23.D.14). -/
noncomputable def TypeDensity.virtualValue (D : TypeDensity) (x : ℝ) : ℝ :=
  x - (1 - D.cdf x) / D.dens x

/-- The distribution is absolutely continuous with respect to Lebesgue measure on `[θ̲, θ̄]`. -/
theorem TypeDensity.absolutelyContinuous (D : TypeDensity) :
    D.measure ≪ volume.restrict (Set.Icc D.lo D.hi) := by
  have h : (fun x => ((D.dens x).toNNReal : ENNReal)) =
      (Set.Icc D.lo D.hi).indicator fun x => ((D.dens x).toNNReal : ENNReal) := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]; simp
  rw [TypeDensity.measure, h, withDensity_indicator measurableSet_Icc]
  exact withDensity_absolutelyContinuous _ _

/-- A function bounded on `(θ̲, θ̄]` and a.e. strongly measurable there, times the density, is
integrable on `[θ̲, θ̄]`. -/
theorem re_intervalIntegrable_mul_dens (D : TypeDensity) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc D.lo D.hi))) (C : ℝ)
    (hC : ∀ x ∈ Set.Ioc D.lo D.hi, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * D.dens x) volume D.lo D.hi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le]
  refine Integrable.bdd_mul (c := C) D.integrable_dens.integrableOn hg ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
    rw [Real.norm_eq_abs]; exact hC x hx

/-- The distribution function is continuous. -/
theorem TypeDensity.continuous_cdf (D : TypeDensity) : Continuous D.cdf :=
  intervalIntegral.continuous_primitive (fun _ _ => D.integrable_dens.intervalIntegrable) D.lo

/-- **(23.D.14)** (MWG, p. 890). For a Bayesian incentive compatible `f = (y, t)` with independent
types with densities, buyer `i`'s expected payment is
`E[-t̄ᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)(θ - (1 - Φᵢ(θ))/φᵢ(θ))φᵢ(θ) dθ - Uᵢ(θ̲ᵢ)`. -/
theorem eq_23_D_14 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure =
      (∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualValue x * (D i).dens x) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  set yb := interimBenefit (Measure.pi fun j => (D j).measure) allocV y i with hyb
  set U0 := interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo with hU0
  set E := D i with hE
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hmono : MonotoneOn yb (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hybI : IntervalIntegrable yb volume E.lo E.hi := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]; exact hmono
  set Cy := |yb E.lo| + |yb E.hi| with hCy
  have hyb_bd : ∀ x ∈ Set.Icc E.lo E.hi, |yb x| ≤ Cy := by
    intro x hx
    have h1 := hmono ⟨le_rfl, hle⟩ hx hx.1
    have h2 := hmono hx ⟨hle, le_rfl⟩ hx.2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (yb E.lo), le_abs_self (yb E.hi), abs_nonneg (yb E.lo),
      abs_nonneg (yb E.hi)]
  have hybm : AEStronglyMeasurable yb (volume.restrict (Set.Ioc E.lo E.hi)) := hybI.1.1
  -- integrability of the pieces
  have hA : IntervalIntegrable (fun x => x * yb x * E.dens x) volume E.lo E.hi :=
    re_intervalIntegrable_mul_dens E (continuous_id.aestronglyMeasurable.mul hybm)
      ((|E.lo| + |E.hi|) * Cy) fun x hx => by
        rw [abs_mul]
        exact mul_le_mul (re_abs_le_of_mem ⟨hx.1.le, hx.2⟩) (hyb_bd x ⟨hx.1.le, hx.2⟩)
          (abs_nonneg _) (by positivity)
  have hprim : ContinuousOn (fun x => ∫ s in E.lo..x, yb s) (Set.uIcc E.lo E.hi) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [Set.uIcc_of_le hle, integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hybI)
  have hC : IntervalIntegrable (fun x => (∫ s in E.lo..x, yb s) * E.dens x) volume E.lo E.hi := by
    refine re_intervalIntegrable_mul_dens E ?_ (Cy * (E.hi - E.lo)) fun x hx => ?_
    · refine (hprim.mono ?_).aestronglyMeasurable measurableSet_Ioc
      rw [Set.uIcc_of_le hle]; exact Set.Ioc_subset_Icc_self
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.lo) (b := x) (f := yb)
        (C := Cy) fun s hs => by
          rw [Set.uIoc_of_le hx.1.le] at hs
          rw [Real.norm_eq_abs]; exact hyb_bd s ⟨hs.1.le, hs.2.trans hx.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - E.lo)] at this
      have : 0 ≤ Cy := by positivity
      nlinarith [hx.2]
  have hB : IntervalIntegrable (fun x => U0 * E.dens x) volume E.lo E.hi :=
    E.intervalIntegrable_dens.const_mul U0
  have hEI : IntervalIntegrable (fun x => yb x * (1 - E.cdf x)) volume E.lo E.hi :=
    hybI.mul_continuousOn (continuous_const.sub E.continuous_cdf).continuousOn
  rw [E.integral_eq]
  have hL : ∫ x in E.lo..E.hi,
      -interimTransfer (Measure.pi fun j => (D j).measure) t i x * E.dens x =
      ∫ x in E.lo..E.hi, ((x * yb x * E.dens x - U0 * E.dens x) -
        (∫ s in E.lo..x, yb s) * E.dens x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [re_interimTransfer_eq hint hf i hx]
    ring
  have hR : ∫ x in E.lo..E.hi, yb x * E.virtualValue x * E.dens x =
      ∫ x in E.lo..E.hi, (x * yb x * E.dens x - yb x * (1 - E.cdf x)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    have := (E.dens_pos x hx).ne'
    simp only [TypeDensity.virtualValue]
    field_simp
  rw [hL, hR, intervalIntegral.integral_sub (hA.sub hB) hC, intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_sub hA hEI, E.integral_integral_eq hybI,
    intervalIntegral.integral_const_mul, E.integral_dens]
  ring

/-- A function monotone on `[θ̲, θ̄]` is a.e. strongly measurable for the type distribution. -/
theorem TypeDensity.aestronglyMeasurable_of_monotoneOn (D : TypeDensity) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc D.lo D.hi)) : AEStronglyMeasurable g D.measure :=
  (hg.integrableOn_isCompact isCompact_Icc).aestronglyMeasurable.mono_ac D.absolutelyContinuous

/-- **(23.D.15)** (MWG, p. 891), the multiple-integral form: with independent types with
densities, `E[yᵢ(θ)Jᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)Jᵢ(θ)φᵢ(θ) dθ`, where
`Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)`. (The integrability hypothesis says the expectation exists.) -/
theorem eq_23_D_15 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι)
    (hyJ : Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) :
    ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualValue x * (D i).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hJ : Measurable (D i).virtualValue :=
    measurable_id.sub (((continuous_const.sub (D i).continuous_cdf).measurable).div
      (D i).measurable_dens)
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) i hyJ]
  simp only [update_self]
  simp_rw [integral_mul_const]
  have h := integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i
    (F := fun x => interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
      (D i).virtualValue x)
    (((D i).aestronglyMeasurable_of_monotoneOn hmono).mul hJ.aestronglyMeasurable)
  rw [(D i).integral_eq] at h
  exact h

/-- **(23.D.16)** (MWG, p. 891). With independent types with densities, the seller's expected
revenue from a Bayesian incentive compatible `f = (y, t)` is
`∑ᵢ E[-tᵢ(θ)] = ∑ᵢ E[yᵢ(θ)Jᵢ(θᵢ)] - ∑ᵢ Uᵢ(θ̲ᵢ)`, `Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)`. Hence any two
Bayesian incentive compatible social choice functions with the same `y` and the same `Uᵢ(θ̲ᵢ)`
generate the same expected revenue. (The integrability hypotheses say the expectations exist.) -/
theorem eq_23_D_16 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hyJ : ∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) :
    ∑ i, ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure) =
      ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) -
        ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_23_D_15 D hint hf i (hyJ i), ← eq_23_D_14 D hint hf i, integral_neg, integral_neg,
    re_expected_transfer (fun j => (D j).measure) i (ht i)]
  congr 1
  set E := D i with hE
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hprim : ContinuousOn (fun x => ∫ s in E.lo..x,
      interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) (Set.Icc E.lo E.hi) := by
    rw [← Set.uIcc_of_le hle]
    refine intervalIntegral.continuousOn_primitive_interval ?_
    rw [Set.uIcc_of_le hle]
    exact hmono.integrableOn_isCompact isCompact_Icc
  have hG : AEStronglyMeasurable (fun x =>
      interimU (Measure.pi fun j => (D j).measure) allocV y t i E.lo +
        (∫ s in E.lo..x, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) -
        x * interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x) E.measure :=
    (aestronglyMeasurable_const.add ((hprim.aestronglyMeasurable measurableSet_Icc).mono_ac
      E.absolutelyContinuous)).sub
      (continuous_id.aestronglyMeasurable.mul (E.aestronglyMeasurable_of_monotoneOn hmono))
  refine integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i (hG.congr ?_)
  filter_upwards [mem_ae_iff.2 E.measure_compl_Icc] with x hx
  exact (re_interimTransfer_eq hint hf i hx).symm

/-! ### Two agents with types uniform on `[0, 1]` -/

/-- The prior of two agents whose types are independent and uniform on `[0, 1]`. -/
noncomputable abbrev unif2 : Measure (Fin 2 → ℝ) := Measure.pi fun _ : Fin 2 => uniform01.measure

/-- `update (x, x) 0 a = (a, x)`. -/
theorem re_update_vec0 (x a : ℝ) : update ![x, x] 0 a = ![a, x] := by
  funext j; fin_cases j <;> simp

/-- `update (x, x) 1 a = (x, a)`. -/
theorem re_update_vec1 (x a : ℝ) : update ![x, x] 1 a = ![x, a] := by
  funext j; fin_cases j <;> simp

/-- With two agents whose types are independent and uniform on `[0, 1]`,
`E_{θ₋ᵢ}[G(a, θ₋ᵢ)] = ∫_0^1 G(update (x, x) i a) dx`. -/
theorem re_unif2_update {G : (Fin 2 → ℝ) → ℝ} (hG : Measurable G) (i : Fin 2) (a : ℝ) :
    ∫ θ', G (update θ' i a) ∂unif2 = ∫ x in (0 : ℝ)..1, G (update ![x, x] i a) := by
  have := uniform01.isProbabilityMeasure
  set c : Fin 2 := if i = 0 then 1 else 0 with hc
  have hG' : (fun θ' => G (update θ' i a)) =
      fun θ' => (fun x => G (update ![x, x] i a)) (θ' c) := by
    funext θ'
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [c]
  have hm : Measurable fun x : ℝ => G (update ![x, x] i a) := by fun_prop
  rw [hG']
  exact (integral_eval_pi (Θ := fun _ => ℝ) (fun _ => uniform01.measure) c
    (F := fun x => G (update ![x, x] i a)) hm.aestronglyMeasurable).trans (uniform01_integral _)

/-- With two agents whose types are independent and uniform on `[0, 1]`,
`E[F(θ)] = ∫_0^1 ∫_0^1 F(a, x) dx da`. -/
theorem re_unif2_integral {F : (Fin 2 → ℝ) → ℝ} (hF : Integrable F unif2) :
    ∫ θ, F θ ∂unif2 = ∫ a in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F ![a, x] := by
  have := uniform01.isProbabilityMeasure
  have hmp := measurePreserving_finTwoArrow uniform01.measure
  have h1 := hmp.integral_comp' (g := fun p => F (MeasurableEquiv.finTwoArrow.symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  have hI : Integrable (fun p => F (MeasurableEquiv.finTwoArrow.symm p))
      (uniform01.measure.prod uniform01.measure) :=
    (hmp.integrable_comp_emb MeasurableEquiv.finTwoArrow.measurableEmbedding).1 (by
      simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]; exact hF)
  rw [h1, integral_prod _ hI, uniform01_integral]
  simp_rw [uniform01_integral]
  rfl

/-- `∫_0^1 1{x ≤ a} g(x) dx = ∫_0^a g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_le {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x ≤ a then g x else 0) = ∫ x in (0 : ℝ)..a, g x := by
  have e : (fun x => if x ≤ a then g x else 0) = (Set.Iic a).indicator g := by
    funext x; simp [Set.indicator_apply]
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.1,
    setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, inf_eq_right.2 ha.2]

/-- `∫_0^1 1{x < a} g(x) dx = ∫_0^a g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_lt {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x < a then g x else 0) = ∫ x in (0 : ℝ)..a, g x := by
  have e : (fun x => if x < a then g x else 0) = (Set.Iio a).indicator g := by
    funext x; simp [Set.indicator_apply]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio a = Set.Ioo 0 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith [ha.2]⟩, h2⟩
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.1,
    setIntegral_indicator measurableSet_Iio, hs, integral_Ioc_eq_integral_Ioo]

/-- `∫_0^1 1{a < x} g(x) dx = ∫_a^1 g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_gt {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if a < x then g x else 0) = ∫ x in a..1, g x := by
  have e : (fun x => if a < x then g x else 0) = (Set.Ioi a).indicator g := by
    funext x; simp [Set.indicator_apply]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi a = Set.Ioc a 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [ha.1], h2⟩, h1⟩
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.2,
    setIntegral_indicator measurableSet_Ioi, hs]

/-- The allocation of Examples 23.B.4-23.B.6 for two agents: agent `1` gets the good iff
`θ₀ < θ₁` (ties go to agent `0`). -/
noncomputable def twoY : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![if θ 1 ≤ θ 0 then 1 else 0, if θ 0 < θ 1 then 1 else 0]

/-- The transfers (23.B.12)-(23.B.14) of the first-price sealed-bid auction equilibrium
(Example 23.B.5): the winner pays half his valuation, `tᵢ = -θᵢyᵢ/2`. -/
noncomputable def firstPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 0 * twoY θ 0 / 2), -(θ 1 * twoY θ 1 / 2)]

/-- The transfers of the second-price sealed-bid auction (Example 23.B.6): the winner pays the
other's valuation, `t₀ = -θ₁y₀`, `t₁ = -θ₀y₁`. -/
noncomputable def secondPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 1 * twoY θ 0), -(θ 0 * twoY θ 1)]

/-- `twoY` is measurable. -/
theorem measurable_twoY (i : Fin 2) : Measurable fun θ => twoY θ i := by
  fin_cases i
  · exact Measurable.ite (measurableSet_le (measurable_pi_apply 1) (measurable_pi_apply 0))
      measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1))
      measurable_const measurable_const

/-- `twoY` is a probability and gives the good to someone. -/
theorem twoY_props (θ : Fin 2 → ℝ) :
    twoY θ 0 + twoY θ 1 = 1 ∧ 0 ≤ twoY θ 1 ∧ twoY θ 1 ≤ 1 ∧ 0 ≤ twoY θ 0 ∧ twoY θ 0 ≤ 1 := by
  simp only [twoY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases h : θ 0 < θ 1
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

/-- `E_{θ₋₀}[y₀(a, θ₋₀)] = a` and `E_{θ₋₁}[y₁(a, θ₋₁)] = a` for `a ∈ [0, 1]`. -/
theorem twoY_interimBenefit {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    interimBenefit unif2 allocV twoY i a = a := by
  unfold interimBenefit
  rw [re_unif2_update (G := fun θ => allocV i (twoY θ)) (measurable_twoY i) i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, allocV, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [re_integral_ite_le ha]; simp
  · simp only [Fin.mk_one, re_update_vec1, allocV, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [re_integral_ite_lt ha]; simp

/-- A measurable function bounded on `[0, 1]²` is integrable for two independent uniform types,
and so is `θ' ↦ F(a, θ'₋ᵢ)` for `a ∈ [0, 1]`. -/
theorem re_unif2_integrable {F : (Fin 2 → ℝ) → ℝ} (hF : Measurable F) (C : ℝ)
    (hC : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → |F θ| ≤ C) :
    Integrable F unif2 ∧ ∀ (i : Fin 2), ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun θ' => F (update θ' i a)) unif2 := by
  have := uniform01.isProbabilityMeasure
  have hsupp : ∀ _ : Fin 2, uniform01.measure (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    fun _ => uniform01.measure_compl_Icc
  refine ⟨Integrable.of_bound hF.aestronglyMeasurable C ?_, fun i a ha =>
    Integrable.of_bound (hF.comp measurable_update_left).aestronglyMeasurable C ?_⟩
  · filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
      (hi := fun _ => 1) hsupp] with θ hθ
    rw [Real.norm_eq_abs]; exact hC θ hθ
  · filter_upwards [re_ae_update_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
      (hi := fun _ => 1) hsupp ha] with θ hθ
    rw [Real.norm_eq_abs]; exact hC _ hθ

/-- **Exercise 23.D.3**, the common computation (MWG, p. 921). With two buyers whose valuations
are independent and uniform on `[0, 1]`, allocation `twoY`, and transfers `t` (measurable, bounded
on `[0, 1]²`) whose interim expectations are `t̄ᵢ(a) = c - a²/2`: `f = (twoY, t)` is Bayesian
incentive compatible, `Uᵢ(0) = c`, and the expected revenue is `∑ᵢ E[-tᵢ] = 1/3 - 2c`. -/
theorem re_twoY_bic {t : (Fin 2 → ℝ) → Fin 2 → ℝ} (htm : ∀ i, Measurable fun θ => t θ i)
    (htb : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i, |t θ i| ≤ 1)
    (c : ℝ) (htt : ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, interimTransfer unif2 t i a = c - a ^ 2 / 2) :
    InterimIntegrable unif2 allocV twoY t (fun _ => 0) (fun _ => 1) ∧
      BayesianICOn unif2 allocV twoY t (fun _ => 0) (fun _ => 1) ∧
      (∀ i, interimU unif2 allocV twoY t i 0 = c) ∧
      ∑ i, ∫ θ, -t θ i ∂unif2 = 1 / 3 - 2 * c := by
  have := uniform01.isProbabilityMeasure
  have hyb : ∀ i θ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → |allocV i (twoY θ)| ≤ 1 := by
    intro i θ _
    obtain ⟨h1, h2, h3, h4, h5⟩ := twoY_props θ
    fin_cases i
    · exact abs_le.2 ⟨by simp [allocV]; linarith, h5⟩
    · exact abs_le.2 ⟨by simp [allocV]; linarith, h3⟩
  have hint : InterimIntegrable unif2 allocV twoY t (fun _ => 0) (fun _ => 1) := fun i a ha =>
    ⟨(re_unif2_integrable (measurable_twoY i) 1 (hyb i)).2 i a ha,
      (re_unif2_integrable (htm i) 1 fun θ hθ => htb θ hθ i).2 i a ha⟩
  have hU : ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, interimU unif2 allocV twoY t i a = a ^ 2 / 2 + c := by
    intro i a ha
    rw [interimU, twoY_interimBenefit ha, htt i a ha]; ring
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hbic : BayesianICOn unif2 allocV twoY t (fun _ => 0) (fun _ => 1) := by
    refine (proposition_23_D_2 hint).2 fun i => ⟨fun a ha b hb hab => ?_, fun θ hθ => ?_⟩
    · rw [twoY_interimBenefit ha, twoY_interimBenefit hb]; exact hab
    · rw [hU i θ hθ, hU i 0 h0, intervalIntegral.integral_congr (g := fun s => s) fun s hs => by
        rw [Set.uIcc_of_le hθ.1] at hs
        exact twoY_interimBenefit ⟨hs.1, hs.2.trans hθ.2⟩ i, integral_id]
      ring
  refine ⟨hint, hbic, fun i => by rw [hU i 0 h0]; ring, ?_⟩
  have hrev : ∀ i, ∫ θ, -t θ i ∂unif2 = 1 / 6 - c := by
    intro i
    rw [integral_neg, re_expected_transfer (fun _ : Fin 2 => uniform01.measure) i
      ((re_unif2_integrable (htm i) 1 fun θ hθ => htb θ hθ i).1)]
    rw [integral_congr_ae (g := fun θ => c - (θ i) ^ 2 / 2) ?_]
    · rw [integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) i
        (F := fun x => c - x ^ 2 / 2) (by fun_prop), uniform01_integral,
        intervalIntegral.integral_sub intervalIntegrable_const
          (((continuous_pow 2).div_const 2).intervalIntegrable 0 1),
        intervalIntegral.integral_const, intervalIntegral.integral_div, integral_pow]
      norm_num
    · filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
        (hi := fun _ => 1) fun _ => uniform01.measure_compl_Icc] with θ hθ
      exact htt i (θ i) (hθ i)
  rw [Fin.sum_univ_two, hrev 0, hrev 1]
  ring

/-- The first-price transfers have `t̄ᵢ(a) = -a ⋅ a/2 = -a²/2` on `[0, 1]` (MWG, p. 868). -/
theorem firstPriceT_interim (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    interimTransfer unif2 firstPriceT i a = -(a ^ 2 / 2) := by
  have hm : Measurable fun θ => firstPriceT θ i := by
    fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => firstPriceT θ i) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, firstPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(a * (if x ≤ a then (1 : ℝ) else 0) / 2) =
        if x ≤ a then -(a / 2) else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha]; simp; ring
  · simp only [Fin.mk_one, re_update_vec1, firstPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(a * (if x < a then (1 : ℝ) else 0) / 2) =
        if x < a then -(a / 2) else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha]; simp; ring

/-- The second-price transfers have `t̄ᵢ(a) = -∫_0^a x dx = -a²/2` on `[0, 1]`. -/
theorem secondPriceT_interim (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    interimTransfer unif2 secondPriceT i a = -(a ^ 2 / 2) := by
  have hm : Measurable fun θ => secondPriceT θ i := by
    fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => secondPriceT θ i) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, secondPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(x * (if x ≤ a then (1 : ℝ) else 0)) =
        if x ≤ a then -x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha, intervalIntegral.integral_neg, integral_id]; ring
  · simp only [Fin.mk_one, re_update_vec1, secondPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(x * (if x < a then (1 : ℝ) else 0)) =
        if x < a then -x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha, intervalIntegral.integral_neg, integral_id]; ring

/-- **Exercise 23.D.3** (MWG, p. 921), with Examples 23.B.5, 23.B.6 and the remark on p. 891. With
two buyers whose valuations are independent and uniform on `[0, 1]`, the social choice function
(23.B.9)-(23.B.14) implemented by the first-price auction equilibrium `bᵢ = θᵢ/2` and the
second-price auction social choice function are both Bayesian incentive compatible, have the same
allocation `y` (the higher valuation wins), give a zero-valuation buyer `Uᵢ(0) = 0`, and both
yield expected revenue `1/3`; Proposition 23.D.3 applies to them. -/
theorem exercise_23_D_3 :
    BayesianICOn unif2 allocV twoY firstPriceT (fun _ => 0) (fun _ => 1) ∧
      BayesianICOn unif2 allocV twoY secondPriceT (fun _ => 0) (fun _ => 1) ∧
      (∀ i, interimU unif2 allocV twoY firstPriceT i 0 = 0) ∧
      (∀ i, interimU unif2 allocV twoY secondPriceT i 0 = 0) ∧
      ∑ i, ∫ θ, -firstPriceT θ i ∂unif2 = 1 / 3 ∧ ∑ i, ∫ θ, -secondPriceT θ i ∂unif2 = 1 / 3 := by
  have bd : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, |firstPriceT θ i| ≤ 1) ∧ ∀ i, |secondPriceT θ i| ≤ 1 := by
    intro θ hθ
    obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp only [firstPriceT, secondPriceT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
      constructor <;> nlinarith
  have hfm : ∀ i, Measurable fun θ => firstPriceT θ i := by
    intro i; fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  have hsm : ∀ i, Measurable fun θ => secondPriceT θ i := by
    intro i; fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  obtain ⟨-, h1, h2, h3⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  obtain ⟨-, h4, h5, h6⟩ := re_twoY_bic hsm (fun θ hθ => (bd θ hθ).2) 0
    fun i a ha => (secondPriceT_interim i ha).trans (by ring)
  exact ⟨h1, h4, h2, h5, h3.trans (by norm_num), h6.trans (by norm_num)⟩

/-- Measurability and bounds of the first- and second-price transfers on `[0, 1]²`. -/
theorem re_price_facts :
    (∀ i, Measurable fun θ => firstPriceT θ i) ∧ (∀ i, Measurable fun θ => secondPriceT θ i) ∧
      ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ i, |firstPriceT θ i| ≤ 1) ∧ ∀ i, |secondPriceT θ i| ≤ 1 := by
  refine ⟨fun i => ?_, fun i => ?_, fun θ hθ => ?_⟩
  · fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  · fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  · obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp only [firstPriceT, secondPriceT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
      constructor <;> nlinarith

/-- **Exercise 23.D.3** via **Proposition 23.D.3** (MWG, pp. 890-891, 921): the first-price and
second-price social choice functions of Examples 23.B.5-23.B.6 satisfy all hypotheses of
`proposition_23_D_3`, which gives equal expected payments buyer by buyer (a proved instance of
the revenue equivalence theorem's hypotheses). -/
theorem exercise_23_D_3_revenue_equivalence :
    ∀ i, ∫ θ, -firstPriceT θ i ∂unif2 = ∫ θ, -secondPriceT θ i ∂unif2 := by
  have := uniform01.isProbabilityMeasure
  obtain ⟨hfm, hsm, bd⟩ := re_price_facts
  obtain ⟨hi1, hb1, hu1, -⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  obtain ⟨hi2, hb2, hu2, -⟩ := re_twoY_bic hsm (fun θ hθ => (bd θ hθ).2) 0
    fun i a ha => (secondPriceT_interim i ha).trans (by ring)
  exact (proposition_23_D_3 (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) (fun _ => uniform01.measure_compl_Icc) hi1 hi2
    (fun i => (re_unif2_integrable (hfm i) 1 fun θ hθ => (bd θ hθ).1 i).1)
    (fun i => (re_unif2_integrable (hsm i) 1 fun θ hθ => (bd θ hθ).2 i).1) hb1 hb2
    fun i => by rw [hu1 i, hu2 i]).1

/-- Non-vacuity of (23.D.14)-(23.D.16): the first-price social choice function with two buyers
uniform on `[0, 1]` satisfies all their hypotheses (here `Jᵢ(θ) = 2θ - 1` on `[0, 1]`). -/
theorem eq_23_D_16_instance :
    InterimIntegrable (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) allocV twoY
      firstPriceT (fun i => ((fun _ => uniform01) i).lo) (fun i => ((fun _ => uniform01) i).hi) ∧
    BayesianICOn (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) allocV twoY
      firstPriceT (fun i => ((fun _ => uniform01) i).lo) (fun i => ((fun _ => uniform01) i).hi) ∧
    (∀ i, Integrable (fun θ => firstPriceT θ i)
      (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure)) ∧
    ∀ i, Integrable (fun θ => twoY θ i * ((fun _ => uniform01) i).virtualValue (θ i))
      (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) := by
  obtain ⟨hfm, -, bd⟩ := re_price_facts
  obtain ⟨hi1, hb1, -, -⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  refine ⟨hi1, hb1, fun i => (re_unif2_integrable (hfm i) 1 fun θ hθ => (bd θ hθ).1 i).1,
    fun i => ?_⟩
  have hJ : Measurable uniform01.virtualValue :=
    measurable_id.sub (((continuous_const.sub uniform01.continuous_cdf).measurable).div
      uniform01.measurable_dens)
  refine (re_unif2_integrable ((measurable_twoY i).mul (hJ.comp (measurable_pi_apply i))) 1
    fun θ hθ => ?_).1
  have hc := uniform01_cdf (hθ i)
  have hd : uniform01.dens (θ i) = 1 := by
    change (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) (θ i) = 1
    rw [Set.indicator_of_mem (hθ i)]; norm_num
  obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
  have hy : |twoY θ i| ≤ 1 :=
    (Fin.forall_fin_two (p := fun i => |twoY θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, h5⟩, abs_le.2 ⟨by linarith, h3⟩⟩ i
  obtain ⟨a, b⟩ := hθ i
  change |twoY θ i * uniform01.virtualValue (θ i)| ≤ 1
  rw [TypeDensity.virtualValue, hc, hd, div_one, abs_mul]
  exact (mul_le_mul hy (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

/-! ### Exercise 23.D.2: the expected externality mechanism for bilateral trade -/

/-- `∫_0^1 1{a ≤ x} g(x) dx = ∫_a^1 g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_ge {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if a ≤ x then g x else 0) = ∫ x in a..1, g x := by
  rw [← re_integral_ite_gt ha g]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := a))] with x hx _
  have hx' : x ≠ a := hx
  by_cases h : a < x
  · simp [h, h.le]
  · have : ¬a ≤ x := fun h' => h (lt_of_le_of_ne h' hx'.symm)
    simp [h, this]

/-- Bilateral trade in the quasilinear form of Section 23.D (Example 23.B.4): `k = true` means
trade; the seller (agent `0`) values the good at `θ₀` and the buyer (agent `1`) at `θ₁`, so
`v₀(k, θ₀) = θ₀` if no trade and `v₁(k, θ₁) = θ₁` if trade (zero otherwise). -/
def bilatV : Fin 2 → Bool → ℝ → ℝ :=
  fun i k x => if k then (if i = 0 then 0 else x) else (if i = 0 then x else 0)

/-- The efficient trading rule: trade iff `θ₀ < θ₁`. -/
noncomputable def bilatK (θ : Fin 2 → ℝ) : Bool := decide (θ 0 < θ 1)

/-- The trading rule `bilatK` satisfies (23.D.6). -/
theorem bilatK_efficient : EfficientProject (Θ := fun _ => ℝ) bilatV bilatK := by
  intro θ k'
  simp only [Fin.sum_univ_two, bilatV, bilatK]
  by_cases h : θ 0 < θ 1
  · cases k'
    · simp [h]; linarith
    · simp [h]
  · cases k'
    · simp [h]
    · simp [h]; linarith [not_lt.1 h]

/-- The integrand of `ξᵢ` is a function of the profile `(a, θ₋ᵢ)`. -/
theorem bilat_xi_integrand (θ' : Fin 2 → ℝ) (i : Fin 2) (a : ℝ) :
    ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK (update θ' i a)) (θ' j) =
      (fun σ : Fin 2 → ℝ => ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK σ) (σ j))
        (update θ' i a) :=
  Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Exercise 23.D.2(a)**, the expected externalities (MWG, p. 921). With `θ₀, θ₁` independent
and uniform on `[0, 1]`, `ξ₀(a) = E[θ₁ 1{a < θ₁}] = (1 - a²)/2` and
`ξ₁(b) = E[θ₀ 1{b ≤ θ₀}] = (1 - b²)/2` for `a, b ∈ [0, 1]`. -/
theorem exercise_23_D_2a_xi (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    expectedExternality unif2 bilatV bilatK i a = (1 - a ^ 2) / 2 := by
  have hm : Measurable fun σ : Fin 2 → ℝ =>
      ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK σ) (σ j) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have hs : MeasurableSet {σ : Fin 2 → ℝ | bilatK σ = true} := by
      simp only [bilatK, decide_eq_true_eq]
      exact measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1)
    have e : (fun σ : Fin 2 → ℝ => bilatV j (bilatK σ) (σ j)) = fun σ =>
        if bilatK σ = true then (if j = 0 then 0 else σ j) else (if j = 0 then σ j else 0) := by
      funext σ; simp only [bilatV]
    rw [e]
    exact Measurable.ite hs (by split_ifs <;> fun_prop) (by split_ifs <;> fun_prop)
  unfold expectedExternality
  simp only [bilat_xi_integrand]
  rw [re_unif2_update hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0]
    have e : ∀ x : ℝ, ∑ j ∈ Finset.univ.erase (0 : Fin 2),
        bilatV j (bilatK ![a, x]) (![a, x] j) = if a < x then x else 0 := by
      intro x
      rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide, Finset.sum_singleton]
      by_cases h : a < x <;> simp [bilatV, bilatK, h]
    simp only [e]
    rw [re_integral_ite_gt ha, integral_id]; ring
  · simp only [Fin.mk_one, re_update_vec1]
    have e : ∀ x : ℝ, ∑ j ∈ Finset.univ.erase (1 : Fin 2),
        bilatV j (bilatK ![x, a]) (![x, a] j) = if a ≤ x then x else 0 := by
      intro x
      rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide, Finset.sum_singleton]
      by_cases h : x < a
      · simp [bilatV, bilatK, h, not_le.2 h]
      · simp [bilatV, bilatK, h, not_lt.1 h]
    simp only [e]
    rw [re_integral_ite_ge ha, integral_id]; ring

/-- **Exercise 23.D.2(a)** (MWG, p. 921). The expected externality transfers (23.D.8)-(23.D.9)
for bilateral trade with types uniform on `[0, 1]` are `t₀(θ) = (θ₁² - θ₀²)/2` and
`t₁(θ) = (θ₀² - θ₁²)/2` on `[0, 1]²`. -/
theorem exercise_23_D_2a {θ : Fin 2 → ℝ} (hθ : ∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) :
    agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ 0 = (θ 1 ^ 2 - θ 0 ^ 2) / 2 ∧
      agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ 1 =
        (θ 0 ^ 2 - θ 1 ^ 2) / 2 := by
  simp only [agvTransfer, agvH, Fintype.card_fin]
  rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide,
    show Finset.univ.erase (1 : Fin 2) = {0} by decide, Finset.sum_singleton,
    Finset.sum_singleton, exercise_23_D_2a_xi 0 (hθ 0), exercise_23_D_2a_xi 1 (hθ 1)]
  constructor <;> ring

/-- **Exercise 23.D.2(b)** (MWG, p. 921). Truth telling is a Bayesian Nash equilibrium of the
expected externality mechanism for bilateral trade with types independent and uniform on
`[0, 1]` (the mechanism is also budget balanced and its trading rule is ex post efficient).
Types are real numbers here, as in Section 23.D; outside `[0, 1]` the prior gives no mass. -/
theorem exercise_23_D_2b (m : Fin 2 → ℝ) :
    BayesianIC (indepBeliefs unif2) (qlU (Θ := fun _ => ℝ) bilatV m)
        (fun θ => (bilatK θ, agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ)) ∧
      BudgetBalanced (Θ := fun _ => ℝ) (agvTransfer unif2 bilatV bilatK
        (agvH unif2 bilatV bilatK)) := by
  have := uniform01.isProbabilityMeasure
  have hsupp : ∀ _ : Fin 2, uniform01.measure (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    fun _ => uniform01.measure_compl_Icc
  have hae := re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) hsupp
  refine ⟨agv_bayesianIC unif2 m bilatK_efficient (agvH_indepOwn _ _ _) ?_ ?_,
    agv_budgetBalanced (by simp) _ _ _⟩
  · intro i a θi j
    have hs : MeasurableSet {θ' : Fin 2 → ℝ | bilatK (update θ' i a) = true} := by
      simp only [bilatK, decide_eq_true_eq]
      exact measurableSet_lt (by fun_prop) (by fun_prop)
    have e : (fun θ' : Fin 2 → ℝ => bilatV j (bilatK (update θ' i a)) (update θ' i θi j)) =
        fun θ' => if bilatK (update θ' i a) = true then (if j = 0 then 0 else update θ' i θi j)
          else (if j = 0 then update θ' i θi j else 0) := by
      funext θ'; simp only [bilatV]
    rw [e]
    refine Integrable.of_bound (Measurable.ite hs (by split_ifs <;> fun_prop)
      (by split_ifs <;> fun_prop)).aestronglyMeasurable (|θi| + 1) ?_
    filter_upwards [hae] with θ' hθ'
    have hb : |update θ' i θi j| ≤ |θi| + 1 := by
      by_cases hj : j = i
      · subst hj; simp
      · rw [update_of_ne hj, abs_le]
        constructor <;> linarith [(hθ' j).1, (hθ' j).2, abs_nonneg θi]
    rw [Real.norm_eq_abs]
    split_ifs <;> simp [hb] <;> linarith [abs_nonneg θi]
  · intro i
    have hxi : ∀ j, Integrable (fun θ : Fin 2 → ℝ =>
        expectedExternality unif2 bilatV bilatK j (θ j)) unif2 := by
      intro j
      refine Integrable.congr (f := fun θ : Fin 2 → ℝ => (1 - θ j ^ 2) / 2)
        (Integrable.of_bound ((measurable_const.sub ((measurable_pi_apply j).pow_const 2)).div_const
          2).aestronglyMeasurable 1 ?_) ?_
      · filter_upwards [hae] with θ hθ
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [(hθ j).1, (hθ j).2]
      · filter_upwards [hae] with θ hθ
        exact (exercise_23_D_2a_xi j (hθ j)).symm
    exact (integrable_finsetSum _ fun j _ => hxi j).const_mul _

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Myerson-Satterthwaite theorem

MWG, Section 23.E, pp. 891-897, and Exercises 23.E.1, 23.E.2, 23.E.3, 23.E.7 (pp. 921-923).

Bilateral trade: agent `0` is the seller, agent `1` the buyer, `uᵢ = θᵢyᵢ + tᵢ` (`allocV`),
`yᵢ(θ)` the probability that `i` ends up with the good, types independent (`P = ∏ᵢ μᵢ`) on
`Θ = [θ̲₀, θ̄₀] × [θ̲₁, θ̄₁]` (`InTypes`). All requirements are imposed on `Θ` only:
ex post efficiency (`ExPostEfficientTrade`: `y₀ + y₁ = 1`, `y₁ ∈ [0, 1]`, trade iff `θ₁ > θ₀`,
ties free) with budget balance (`BudgetBalancedOn`), Bayesian incentive compatibility
(`BayesianICOn`, from `LinearBIC`), interim individual rationality (23.E.2) (`InterimIR`:
`U₀(θ₀) ≥ θ₀`, `U₁(θ₁) ≥ 0`).

* **Proposition 23.E.1** for general type distributions (`proposition_23_E_1_general`: each `μᵢ`
  concentrated on `[θ̲ᵢ, θ̄ᵢ]` with positive mass on open subintervals) and as stated, with
  strictly positive densities (`proposition_23_E_1`). Footnote 41: `footnote_23_41`.
* The proof departs from MWG's (23.E.4)-(23.E.7): `ms_core` compares `f` with the rule
  `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` (dominant strategy incentive compatible, `ms_vcg_bic`); by
  Proposition 23.D.2 the interim transfers differ by constants, budget balance and individual
  rationality at `θ̄₀`, `θ̲₁` give `E[(θ₁ - θ₀)⁺] ≤ E[(θ₁ - θ̄₀)⁺] + E[(θ̲₁ - θ₀)⁺]`, which fails
  because of a strict pointwise inequality on a box of positive probability in the overlap.
* Non-vacuity (uniform types on `[0, 1]`), one instance per dropped requirement:
  without individual rationality the expected externality mechanism (`exercise_23_E_1`); without
  budget balance the comparison rule (`proposition_23_E_1_instance_no_bb`); without efficiency
  the posted price `1/2` (`proposition_23_E_1_instance_no_eff`); without incentive compatibility
  split-the-difference (`proposition_23_E_1_instance_no_bic`).
* p. 894: ex post IR implies interim IR (`ms_interimIR_of_exPostIR`); dominant strategy IC
  implies Bayesian IC (`ms_bic_of_dsic`).
* Exercise 23.E.1: in the expected externality mechanism with uniform types the seller of type
  `1` gets `U₀(1) = 2/3 < 1`. Exercise 23.E.2(a), (b) (`exercise_23_E_2a`, `exercise_23_E_2b`).
  Exercise 23.E.3: a two-type example with a Bayesian incentive compatible, ex post efficient,
  ex post individually rational social choice function (`exercise_23_E_3`). Exercise 23.E.7:
  (a) `≥ 5/6`, (b) `≤ 2/3 = E[max(θ₀, θ₁)]`, together M-S for uniform types.

**Corrections.** Exercise 23.E.2(a), (b) as printed omit ex post efficiency and are then false:
the no-trade rule is dominant strategy incentive compatible, budget balanced and ex post
individually rational (`exercise_23_E_2_literal_false`); with ex post efficiency they follow
from Proposition 23.E.1. In Exercise 23.E.7(a) "ex post efficient" must mean the trading rule
only (no budget balance): with budget balance no such `f` exists (Proposition 23.E.1) and (a)
would be vacuous. Footnote 41's equivalence needs nondegenerate intervals.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-- The type space `Θ = [θ̲₀, θ̄₀] × [θ̲₁, θ̄₁]` of the bilateral trade setting (MWG, p. 894);
agent `0` is the seller and agent `1` the buyer. -/
def InTypes (lo hi : Fin 2 → ℝ) (θ : Fin 2 → ℝ) : Prop := ∀ i, θ i ∈ Set.Icc (lo i) (hi i)

/-- Ex post efficiency in the bilateral trade setting (MWG, pp. 862, 895): on `Θ`, the good is
always held by someone (`y₀ + y₁ = 1`, with `y₁ ∈ [0, 1]` a probability), the buyer gets it when
`θ₁ > θ₀` and the seller keeps it when `θ₁ < θ₀`. -/
def ExPostEfficientTrade (lo hi : Fin 2 → ℝ) (y : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → y θ 0 + y θ 1 = 1 ∧ 0 ≤ y θ 1 ∧ y θ 1 ≤ 1 ∧
    (θ 0 < θ 1 → y θ 1 = 1) ∧ (θ 1 < θ 0 → y θ 1 = 0)

/-- Budget balance on `Θ`: `t₀(θ) + t₁(θ) = 0` (MWG, p. 895). -/
def BudgetBalancedOn (lo hi : Fin 2 → ℝ) (t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → t θ 0 + t θ 1 = 0

/-- Interim individual rationality (23.E.2) in the bilateral trade setting (MWG, p. 894): every
seller type gets `U₀(θ₀) ≥ θ₀` (his utility from consuming the good) and every buyer type gets
`U₁(θ₁) ≥ 0`. -/
def InterimIR (P : Measure (Fin 2 → ℝ)) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) (lo hi : Fin 2 → ℝ) :
    Prop :=
  (∀ x ∈ Set.Icc (lo 0) (hi 0), x ≤ interimU P allocV y t 0 x) ∧
    ∀ x ∈ Set.Icc (lo 1) (hi 1), 0 ≤ interimU P allocV y t 1 x

/-- The comparison transfers: the seller receives the buyer's valuation and the buyer pays the
seller's valuation whenever trade occurs, `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` (a Vickrey-Clarke-Groves
rule; not budget balanced). -/
def msVcgT (y : (Fin 2 → ℝ) → Fin 2 → ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![θ 1 * y θ 1, -(θ 0 * y θ 1)]

/-- `d c ≤ max(d, 0)` for `c ∈ [0, 1]`. -/
theorem ms_mul_le_max {d c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : d * c ≤ max d 0 := by
  rcases le_total d 0 with hd | hd
  · rw [max_eq_right hd]; nlinarith
  · rw [max_eq_left hd]; nlinarith

/-- On `Θ`, the efficient trade gives `(θ₁ - θ₀)y₁(θ) = max(θ₁ - θ₀, 0)`. -/
theorem ms_eff_mul {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {θ : Fin 2 → ℝ} (hθ : InTypes lo hi θ) :
    (θ 1 - θ 0) * y θ 1 = max (θ 1 - θ 0) 0 := by
  obtain ⟨-, -, -, h1, h2⟩ := heff θ hθ
  rcases lt_trichotomy (θ 0) (θ 1) with h | h | h
  · rw [h1 h, max_eq_left (by linarith)]; ring
  · rw [h]; simp
  · rw [h2 h, max_eq_right (by linarith)]; ring

/-- The seller's utility under the comparison transfers: reporting into profile `u ∈ Θ`, a seller
of type `x` gets `x y₀(u) + u₁y₁(u) ≤ x + max(u₁ - x, 0)`, with equality when `u₀ = x`. -/
theorem ms_vcg_seller {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (x : ℝ) :
    linU allocV 0 (y u, msVcgT y u) x ≤ x + max (u 1 - x) 0 ∧
      linU allocV 0 (y u, msVcgT y u) (u 0) = u 0 + max (u 1 - u 0) 0 := by
  obtain ⟨hs, h0, h1, -, -⟩ := heff u hu
  have e : ∀ z, linU allocV 0 (y u, msVcgT y u) z = z + (u 1 - z) * y u 1 := by
    intro z
    simp only [linU, allocV, msVcgT, Matrix.cons_val_zero]
    rw [show y u 0 = 1 - y u 1 by linarith]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; linarith [ms_mul_le_max (d := u 1 - x) h0 h1]
  · rw [e, ms_eff_mul heff hu]

/-- The buyer's utility under the comparison transfers: reporting into profile `u ∈ Θ`, a buyer of
type `x` gets `(x - u₀)y₁(u) ≤ max(x - u₀, 0)`, with equality when `u₁ = x`. -/
theorem ms_vcg_buyer {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (x : ℝ) :
    linU allocV 1 (y u, msVcgT y u) x ≤ max (x - u 0) 0 ∧
      linU allocV 1 (y u, msVcgT y u) (u 1) = max (u 1 - u 0) 0 := by
  obtain ⟨-, h0, h1, -, -⟩ := heff u hu
  have e : ∀ z, linU allocV 1 (y u, msVcgT y u) z = (z - u 0) * y u 1 := by
    intro z
    simp only [linU, allocV, msVcgT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact ms_mul_le_max h0 h1
  · rw [e, ms_eff_mul heff hu]

/-- On `Θ`, `|t^g_i(u)| ≤ |θ̲ⱼ| + |θ̄ⱼ|` for the comparison transfers. -/
theorem ms_vcg_bound {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (i : Fin 2) :
    |msVcgT y u i| ≤ |lo 0| + |hi 0| + (|lo 1| + |hi 1|) := by
  obtain ⟨-, h0, h1, -, -⟩ := heff u hu
  have hy : |y u 1| ≤ 1 := abs_le.2 ⟨by linarith, h1⟩
  have b0 := re_abs_le_of_mem (hu 0)
  have b1 := re_abs_le_of_mem (hu 1)
  fin_cases i
  · simp only [msVcgT, Fin.zero_eta, Matrix.cons_val_zero, abs_mul]
    nlinarith [abs_nonneg (u 1), abs_nonneg (y u 1), abs_nonneg (lo 0), abs_nonneg (hi 0)]
  · simp only [msVcgT, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_neg,
      abs_mul]
    nlinarith [abs_nonneg (u 0), abs_nonneg (y u 1), abs_nonneg (lo 1), abs_nonneg (hi 1)]

/-- The comparison transfers are measurable when `y` is. -/
theorem ms_measurable_vcg {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (i : Fin 2) :
    Measurable fun θ => msVcgT y θ i := by
  have h1 : Measurable fun θ : Fin 2 → ℝ => y θ 1 := (measurable_pi_apply 1).comp hym
  fin_cases i
  · simp only [msVcgT, Fin.zero_eta, Matrix.cons_val_zero]
    exact (measurable_pi_apply 1).mul h1
  · simp only [msVcgT, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ((measurable_pi_apply 0).mul h1).neg

variable (μ : Fin 2 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The comparison rule `(y, t^g)` is Bayesian incentive compatible and its interim expectations
exist, whenever `y` is measurable and ex post efficient (dominant strategy incentive
compatibility on `Θ`, integrated). -/
theorem ms_vcg_bic {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (heff : ExPostEfficientTrade lo hi y)
    (hy : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i),
      Integrable (fun θ' => allocV i (y (update θ' i a))) (Measure.pi μ)) :
    InterimIntegrable (Measure.pi μ) allocV y (msVcgT y) lo hi ∧
      BayesianICOn (Measure.pi μ) allocV y (msVcgT y) lo hi := by
  have hint : InterimIntegrable (Measure.pi μ) allocV y (msVcgT y) lo hi := by
    intro i a ha
    refine ⟨hy i a ha, Integrable.of_bound
      ((ms_measurable_vcg hym i).comp measurable_update_left).aestronglyMeasurable
      (|lo 0| + |hi 0| + (|lo 1| + |hi 1|)) ?_⟩
    filter_upwards [re_ae_update_mem μ hsupp ha] with θ' hθ'
    rw [Real.norm_eq_abs]
    exact ms_vcg_bound heff hθ' i
  refine ⟨hint, ?_⟩
  have hI : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i), ∀ x : ℝ, Integrable (fun θ' =>
      linU allocV i (y (update θ' i a), msVcgT y (update θ' i a)) x) (Measure.pi μ) :=
    fun i a ha x => ((hint i a ha).1.const_mul x).add (hint i a ha).2
  intro i x hx a ha
  refine integral_mono_ae (hI i a ha x) (hI i x hx x) ?_
  filter_upwards [re_ae_update_mem μ hsupp ha, re_ae_update_mem μ hsupp hx] with θ' h1 h2
  fin_cases i
  · have e1 := (ms_vcg_seller heff (u := update θ' 0 a) h1 x).1
    have e2 := (ms_vcg_seller heff (u := update θ' 0 x) h2 x).2
    simp only [Fin.zero_eta, update_self, update_of_ne (Ne.symm zero_ne_one)] at e1 e2 ⊢
    rw [e2]; exact e1
  · have e1 := (ms_vcg_buyer heff (u := update θ' 1 a) h1 x).1
    have e2 := (ms_vcg_buyer heff (u := update θ' 1 x) h2 x).2
    simp only [Fin.mk_one, update_self, update_of_ne zero_ne_one] at e1 e2 ⊢
    rw [e2]; exact e1

/-- A measurable function bounded on `Θ` is integrable under `∏ᵢ μᵢ` when each `μᵢ` is concentrated
on `[θ̲ᵢ, θ̄ᵢ]`. -/
theorem ms_integrable_of_bound {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Measurable F) (C : ℝ) (hC : ∀ θ, InTypes lo hi θ → |F θ| ≤ C) :
    Integrable F (Measure.pi μ) := by
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [re_ae_mem μ hsupp] with θ hθ
  rw [Real.norm_eq_abs]; exact hC θ hθ

/-- `|max(u - v, 0)| ≤ |u| + |v|`. -/
theorem ms_abs_max_sub_le (u v : ℝ) : |max (u - v) 0| ≤ |u| + |v| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (abs_sub _ _)) (by positivity)

/-- The positive parts `(θⱼ - x)⁺` and `(x - θⱼ)⁺`, and `(θ₁ - θ₀)⁺`, are integrable under
`∏ᵢ μᵢ` when each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]`. -/
theorem ms_integrable_pos_parts {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) (j : Fin 2) (x : ℝ) :
    Integrable (fun θ => max (θ j - x) 0) (Measure.pi μ) ∧
      Integrable (fun θ => max (x - θ j) 0) (Measure.pi μ) ∧
      Integrable (fun θ => max (θ 1 - θ 0) 0) (Measure.pi μ) := by
  refine ⟨ms_integrable_of_bound μ hsupp (((measurable_pi_apply j).sub measurable_const).max
      measurable_const) (|lo j| + |hi j| + |x|) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ j)]), ms_integrable_of_bound μ hsupp
      ((measurable_const.sub (measurable_pi_apply j)).max measurable_const)
      (|lo j| + |hi j| + |x|) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ j)]), ms_integrable_of_bound μ hsupp
      (((measurable_pi_apply 1).sub (measurable_pi_apply 0)).max measurable_const)
      (|lo 1| + |hi 1| + (|lo 0| + |hi 0|)) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ 0), re_abs_le_of_mem (hθ 1)])⟩

/-- **Proposition 23.E.1**, the common core of the proof (MWG, pp. 895-896). Let `f = (y, t)` be
Bayesian incentive compatible and interim individually rational with an efficient trading rule
`y` (budget balance is NOT assumed). Then for the comparison transfers
`t^g₀ = θ₁y₁`, `t^g₁ = -θ₀y₁` there are constants `cᵢ` with `E[tᵢ] = E[t^gᵢ] + cᵢ`,
`c₀ ≥ -E[(θ₁ - θ̄₀)⁺]` and `c₁ ≥ -E[(θ̲₁ - θ₀)⁺]`; moreover
`E[t^g₀] + E[t^g₁] = E[(θ₁ - θ₀)⁺]`. -/
theorem ms_core {lo hi : Fin 2 → ℝ} (hlo : ∀ i, lo i ≤ hi i)
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hir : InterimIR (Measure.pi μ) y t lo hi) :
    ∃ c : Fin 2 → ℝ, (∀ i, ∫ θ, t θ i ∂Measure.pi μ = ∫ θ, msVcgT y θ i ∂Measure.pi μ + c i) ∧
      -∫ θ, max (θ 1 - hi 0) 0 ∂Measure.pi μ ≤ c 0 ∧
      -∫ θ, max (lo 1 - θ 0) 0 ∂Measure.pi μ ≤ c 1 ∧
      ∫ θ, msVcgT y θ 0 ∂Measure.pi μ + ∫ θ, msVcgT y θ 1 ∂Measure.pi μ =
        ∫ θ, max (θ 1 - θ 0) 0 ∂Measure.pi μ := by
  have hae := re_ae_mem μ hsupp
  obtain ⟨hintg, hbicg⟩ := ms_vcg_bic μ hsupp hym heff fun i a ha => (hint i a ha).1
  have htg : ∀ i, Integrable (fun θ => msVcgT y θ i) (Measure.pi μ) := fun i =>
    ms_integrable_of_bound μ hsupp (ms_measurable_vcg hym i) _
      fun θ hθ => ms_vcg_bound heff hθ i
  set c : Fin 2 → ℝ := fun i => interimU (Measure.pi μ) allocV y t i (lo i) -
    interimU (Measure.pi μ) allocV y (msVcgT y) i (lo i) with hc
  have hconst : ∀ i, ∀ x ∈ Set.Icc (lo i) (hi i), interimTransfer (Measure.pi μ) t i x =
      interimTransfer (Measure.pi μ) (msVcgT y) i x + c i := by
    intro i x hx
    rw [re_interimTransfer_eq hint hbic i hx, re_interimTransfer_eq hintg hbicg i hx, hc]
    ring
  refine ⟨c, fun i => ?_, ?_, ?_, ?_⟩
  · rw [re_expected_transfer μ i (ht i), re_expected_transfer μ i (htg i)]
    have hI : Integrable (fun θ => interimTransfer (Measure.pi μ) (msVcgT y) i (θ i))
        (Measure.pi μ) := re_integrable_integral_update μ i (htg i)
    rw [integral_congr_ae (g := fun θ => interimTransfer (Measure.pi μ) (msVcgT y) i (θ i) + c i)
      ?_, integral_add hI (integrable_const _)]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    filter_upwards [hae] with θ hθ using hconst i (θ i) (hθ i)
  · have hhi0 : hi 0 ∈ Set.Icc (lo 0) (hi 0) := ⟨hlo 0, le_rfl⟩
    have h1 : interimU (Measure.pi μ) allocV y t 0 (hi 0) -
        interimU (Measure.pi μ) allocV y (msVcgT y) 0 (hi 0) = c 0 := by
      simp only [interimU]; rw [hconst 0 (hi 0) hhi0]; ring
    have h2 : interimU (Measure.pi μ) allocV y (msVcgT y) 0 (hi 0) =
        hi 0 + ∫ θ, max (θ 1 - hi 0) 0 ∂Measure.pi μ := by
      rw [interimU, ← eq_23_D_10 (hintg 0 _ hhi0).1 (hintg 0 _ hhi0).2 (hi 0),
        integral_congr_ae (g := fun θ => hi 0 + max (θ 1 - hi 0) 0) ?_,
        integral_add (integrable_const _) (ms_integrable_pos_parts μ hsupp 1 (hi 0)).1]
      · simp
      filter_upwards [re_ae_update_mem μ hsupp hhi0] with θ' h
      have := (ms_vcg_seller heff h (hi 0)).2
      simp only [update_self, update_of_ne (Ne.symm zero_ne_one)] at this
      rw [this]
    have h3 := hir.1 (hi 0) hhi0
    linarith
  · have hlo1 : lo 1 ∈ Set.Icc (lo 1) (hi 1) := ⟨le_rfl, hlo 1⟩
    have h1 : interimU (Measure.pi μ) allocV y t 1 (lo 1) -
        interimU (Measure.pi μ) allocV y (msVcgT y) 1 (lo 1) = c 1 := by
      simp only [interimU]; rw [hconst 1 (lo 1) hlo1]; ring
    have h2 : interimU (Measure.pi μ) allocV y (msVcgT y) 1 (lo 1) =
        ∫ θ, max (lo 1 - θ 0) 0 ∂Measure.pi μ := by
      rw [interimU, ← eq_23_D_10 (hintg 1 _ hlo1).1 (hintg 1 _ hlo1).2 (lo 1)]
      refine integral_congr_ae ?_
      filter_upwards [re_ae_update_mem μ hsupp hlo1] with θ' h
      have := (ms_vcg_buyer heff h (lo 1)).2
      simp only [update_self, update_of_ne zero_ne_one] at this
      rw [this]
    have h3 := hir.2 (lo 1) hlo1
    linarith
  · rw [← integral_add (htg 0) (htg 1)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    simp only [msVcgT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← ms_eff_mul heff hθ]; ring

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, for general type
distributions. Agent `0` (seller) and agent `1` (buyer) have linear utilities `θᵢyᵢ + tᵢ`, and
independent valuations `θᵢ ~ μᵢ` with `μᵢ` concentrated on `[θ̲ᵢ, θ̄ᵢ]` and giving positive
probability to every open subinterval; gains from trade are possible but not certain,
`(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅` (footnote 41). Then no social choice function `(y, t)` is ex post
efficient (efficient trade and budget balance on `Θ`), Bayesian incentive compatible and interim
individually rational.

Proof (not MWG's integration by parts): compare `f` with the rule `g = (y, t^g)`,
`t^g₀ = θ₁y₁`, `t^g₁ = -θ₀y₁`, which is Bayesian incentive compatible. By Proposition 23.D.2 the
interim transfers of `f` and `g` differ by constants `cᵢ` on `Θᵢ`; budget balance gives
`c₀ + c₁ = -E[(θ₁ - θ₀)⁺]`, and interim individual rationality at `θ₀ = θ̄₀` and `θ₁ = θ̲₁` gives
`c₀ ≥ -E[(θ₁ - θ̄₀)⁺]`, `c₁ ≥ -E[(θ̲₁ - θ₀)⁺]`. But on `Θ`,
`(θ₁ - θ₀)⁺ ≥ (θ₁ - θ̄₀)⁺ + (θ̲₁ - θ₀)⁺`, strictly on a box of positive probability in the
overlap. The integrability hypotheses say the expectations exist; `y` is assumed measurable. -/
theorem proposition_23_E_1_general {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hir : InterimIR (Measure.pi μ) y t lo hi) : False := by
  obtain ⟨z, ⟨hz0, hz0'⟩, ⟨hz1, hz1'⟩⟩ := hov
  have hlo : ∀ i, lo i ≤ hi i := by
    intro i; fin_cases i
    · exact (hz0.trans hz0').le
    · exact (hz1.trans hz1').le
  obtain ⟨c, hE, hc0, hc1, hgE⟩ := ms_core μ hlo hsupp hym hint ht heff hbic hir
  have hae := re_ae_mem μ hsupp
  have hbbE : ∫ θ, t θ 0 ∂Measure.pi μ + ∫ θ, t θ 1 ∂Measure.pi μ = 0 := by
    rw [← integral_add (ht 0) (ht 1), integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [hae] with θ hθ using hbb θ hθ
  set pp : (Fin 2 → ℝ) → ℝ := fun θ => max (θ 1 - θ 0) 0 with hpp
  set q0 : (Fin 2 → ℝ) → ℝ := fun θ => max (θ 1 - hi 0) 0 with hq0
  set q1 : (Fin 2 → ℝ) → ℝ := fun θ => max (lo 1 - θ 0) 0 with hq1
  have hppI : Integrable pp (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 0 0).2.2
  have hq0I : Integrable q0 (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 1 (hi 0)).1
  have hq1I : Integrable q1 (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 0 (lo 1)).2.1
  -- the pointwise inequality and its strict version on a box in the overlap
  have hnn : ∀ θ, InTypes lo hi θ → 0 ≤ pp θ - q0 θ - q1 θ := by
    intro θ hθ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    simp only [hpp, hq0, hq1, max_def]
    split_ifs <;> linarith
  set a := max (lo 0) (lo 1) with ha
  set b := min (hi 0) (hi 1) with hb'
  have haz : a < z := max_lt hz0 hz1
  have hzb : z < b := lt_min hz0' hz1'
  set S : Set (Fin 2 → ℝ) := Set.pi Set.univ ![Set.Ioo a z, Set.Ioo z b] with hS
  have hSpos : 0 < Measure.pi μ S := by
    rw [hS, Measure.pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ENNReal.mul_pos (hpos 0 a z (le_max_left _ _) haz hz0'.le).ne'
      (hpos 1 z b hz1.le hzb (min_le_right _ _)).ne'
  have hSsupp : S ⊆ Function.support fun θ => pp θ - q0 θ - q1 θ := by
    intro θ hθ
    rw [hS, Set.mem_univ_pi] at hθ
    have h0 := hθ 0
    have h1 := hθ 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Set.mem_Ioo] at h0 h1
    have e1 : pp θ = θ 1 - θ 0 := max_eq_left (by linarith)
    have e2 : q0 θ = 0 := max_eq_right (by linarith [min_le_left (hi 0) (hi 1)])
    have e3 : q1 θ = 0 := max_eq_right (by linarith [le_max_right (lo 0) (lo 1)])
    simp only [Function.mem_support, e1, e2, e3]
    linarith
  have hI2 : Integrable (fun θ => pp θ - q0 θ) (Measure.pi μ) := hppI.sub hq0I
  have hI3 : Integrable (fun θ => pp θ - q0 θ - q1 θ) (Measure.pi μ) := hI2.sub hq1I
  have hstrict : 0 < ∫ θ, (pp θ - q0 θ - q1 θ) ∂Measure.pi μ := by
    rw [integral_pos_iff_support_of_nonneg_ae _ hI3]
    · exact hSpos.trans_le (measure_mono hSsupp)
    · filter_upwards [hae] with θ hθ using hnn θ hθ
  rw [integral_sub (f := fun θ => pp θ - q0 θ) hI2 hq1I, integral_sub hppI hq0I] at hstrict
  have := hE 0
  have := hE 1
  linarith

/-- **Footnote 41** (MWG, p. 895). For nondegenerate intervals (`θ̲ᵢ < θ̄ᵢ`),
`(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅` iff `θ̄₁ > θ̲₀` and `θ̄₀ > θ̲₁`. -/
theorem footnote_23_41 {lo hi : Fin 2 → ℝ} (h0 : lo 0 < hi 0) (h1 : lo 1 < hi 1) :
    (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty ↔ lo 0 < hi 1 ∧ lo 1 < hi 0 := by
  constructor
  · rintro ⟨z, ⟨a0, b0⟩, ⟨a1, b1⟩⟩
    exact ⟨a0.trans b1, a1.trans b0⟩
  · rintro ⟨c0, c1⟩
    refine ⟨(max (lo 0) (lo 1) + min (hi 0) (hi 1)) / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, as stated: the
seller's and buyer's valuations are independent with strictly positive densities on
`[θ̲₀, θ̄₀]` and `[θ̲₁, θ̄₁]`, and `(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅`. Then no Bayesian incentive
compatible social choice function is ex post efficient and gives every buyer type and every
seller type nonnegative expected gains from participation. (`y` measurable and the integrability
hypotheses say that the expectations exist.) -/
theorem proposition_23_E_1 (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  exact proposition_23_E_1_general (fun j => (D j).measure) (fun i => (D i).measure_compl_Icc)
    (fun i _ _ ha hab hb => (D i).measure_Ioo_pos ha hab hb) hov hym hint ht heff hbb hbic hir

/-! ### Dominant strategies, ex post participation, and Exercise 23.E.2 -/

/-- Dominant strategy incentive compatibility (23.C.3) on `Θ` in the bilateral trade setting:
for every profile `θ ∈ Θ` and announcement `a ∈ Θᵢ`, `uᵢ(f(a, θ₋ᵢ), θᵢ) ≤ uᵢ(f(θ), θᵢ)`. -/
def DominantICOn (lo hi : Fin 2 → ℝ) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i, ∀ θ, InTypes lo hi θ → ∀ a ∈ Set.Icc (lo i) (hi i),
    linU allocV i (y (update θ i a), t (update θ i a)) (θ i) ≤ linU allocV i (y θ, t θ) (θ i)

/-- Ex post individual rationality (23.E.1) in the bilateral trade setting: on `Θ`, the seller
gets at least `θ₀` and the buyer at least `0`. -/
def ExPostIR (lo hi : Fin 2 → ℝ) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → θ 0 ≤ linU allocV 0 (y θ, t θ) (θ 0) ∧
    0 ≤ linU allocV 1 (y θ, t θ) (θ 1)

/-- `(θ₋ᵢ, x)` lies in `Θ` when `θ` does and `x ∈ Θᵢ`. -/
theorem ms_update_mem {lo hi : Fin 2 → ℝ} {θ : Fin 2 → ℝ} (hθ : InTypes lo hi θ) {i : Fin 2}
    {x : ℝ} (hx : x ∈ Set.Icc (lo i) (hi i)) : InTypes lo hi (update θ i x) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simpa [hj] using hθ j

/-- **Section 23.D** (MWG, p. 884), in the linear bilateral setting: a dominant strategy incentive
compatible social choice function is Bayesian incentive compatible (with independent types
concentrated on `Θ`, the expectations existing). -/
theorem ms_bic_of_dsic {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (hds : DominantICOn lo hi y t) : BayesianICOn (Measure.pi μ) allocV y t lo hi := by
  intro i x hx a ha
  have hI : ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), t (update θ' i b)) x) (Measure.pi μ) :=
    fun b hb => ((hint i b hb).1.const_mul x).add (hint i b hb).2
  refine integral_mono_ae (hI a ha) (hI x hx) ?_
  filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
  have := hds i (update θ' i x) h a ha
  simpa only [update_idem, update_self] using this

/-- **Section 23.E** (MWG, p. 894): ex post individual rationality (23.E.1) implies interim
individual rationality (23.E.2). -/
theorem ms_interimIR_of_exPostIR {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi) (hir : ExPostIR lo hi y t) :
    InterimIR (Measure.pi μ) y t lo hi := by
  have hI : ∀ i, ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), t (update θ' i b)) b) (Measure.pi μ) :=
    fun i b hb => ((hint i b hb).1.const_mul b).add (hint i b hb).2
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [interimU, ← eq_23_D_10 (hint 0 x hx).1 (hint 0 x hx).2 x]
    have h := integral_mono_ae (integrable_const x) (hI 0 x hx) (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      simpa using (hir _ h).1)
    simpa using h
  · rw [interimU, ← eq_23_D_10 (hint 1 x hx).1 (hint 1 x hx).2 x]
    exact integral_nonneg_of_ae (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      simpa using (hir _ h).2)

/-- **Exercise 23.E.2(a)** (MWG, p. 921), corrected. Under the assumptions of Proposition 23.E.1
(general form), no social choice function is dominant strategy incentive compatible, interim
individually rational and ex post efficient (efficient trade and budget balance). -/
theorem exercise_23_E_2a {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hds : DominantICOn lo hi y t) (hir : InterimIR (Measure.pi μ) y t lo hi) : False :=
  proposition_23_E_1_general μ hsupp hpos hov hym hint ht heff hbb
    (ms_bic_of_dsic μ hsupp hint hds) hir

/-- **Exercise 23.E.2(b)** (MWG, p. 922), corrected. Under the assumptions of Proposition 23.E.1
(general form), no social choice function is Bayesian incentive compatible, ex post individually
rational and ex post efficient (efficient trade and budget balance). -/
theorem exercise_23_E_2b {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi) (hir : ExPostIR lo hi y t) : False :=
  proposition_23_E_1_general μ hsupp hpos hov hym hint ht heff hbb hbic
    (ms_interimIR_of_exPostIR μ hsupp hint hir)

/-- The no-trade rule: the seller keeps the good and no money changes hands. -/
def noTradeY : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ => ![1, 0]

/-- **Exercise 23.E.2(a)-(b)** as printed are false (MWG, pp. 921-922): without ex post
efficiency, the no-trade rule (`y = (1, 0)`, `t = 0`) is dominant strategy and Bayesian incentive
compatible, budget balanced, and ex post (hence interim) individually rational, for any
independent prior. -/
theorem exercise_23_E_2_literal_false (lo hi : Fin 2 → ℝ) :
    DominantICOn lo hi noTradeY (fun _ => 0) ∧
      BayesianICOn (Measure.pi μ) allocV noTradeY (fun _ => 0) lo hi ∧
      BudgetBalancedOn lo hi (fun _ => 0) ∧ ExPostIR lo hi noTradeY (fun _ => 0) ∧
      InterimIR (Measure.pi μ) noTradeY (fun _ => 0) lo hi := by
  have hint : InterimIntegrable (Measure.pi μ) allocV noTradeY (fun _ => 0) lo hi :=
    fun _ _ _ => ⟨integrable_const _, integrable_const _⟩
  refine ⟨fun i θ _ a _ => le_rfl, fun i x _ a _ => le_rfl, fun _ _ => by simp,
    fun θ _ => ?_, ⟨fun x _ => ?_, fun x _ => ?_⟩⟩
  · simp [linU, allocV, noTradeY]
  · simp [interimU, interimBenefit, interimTransfer, allocV, noTradeY]
  · simp [interimU, interimBenefit, interimTransfer, allocV, noTradeY]

/-! ### Uniform types on `[0, 1]`: Exercises 23.E.1 and 23.E.7, and non-vacuity -/

/-- The uniform prior on `[0, 1]²` satisfies the hypotheses of Proposition 23.E.1 (general form):
support in `[0, 1]`, positive probability of open subintervals, overlapping intervals. -/
theorem ms_unif_hyps :
    (∀ i : Fin 2, uniform01.measure (Set.Icc ((fun _ => (0 : ℝ)) i) ((fun _ => (1 : ℝ)) i))ᶜ
      = 0) ∧
    (∀ i : Fin 2, ∀ a b, (fun _ => (0 : ℝ)) i ≤ a → a < b → b ≤ (fun _ => (1 : ℝ)) i →
      0 < uniform01.measure (Set.Ioo a b)) ∧
    (Set.Ioo ((fun _ : Fin 2 => (0 : ℝ)) 0) ((fun _ : Fin 2 => (1 : ℝ)) 0) ∩
      Set.Ioo ((fun _ : Fin 2 => (0 : ℝ)) 1) ((fun _ : Fin 2 => (1 : ℝ)) 1)).Nonempty :=
  ⟨fun _ => uniform01.measure_compl_Icc, fun _ _ _ ha hab hb => uniform01.measure_Ioo_pos ha hab hb,
    ⟨1 / 2, by norm_num, by norm_num⟩⟩

/-- Under the uniform prior, `E[θᵢ] = 1/2`. -/
theorem ms_unif_mean (i : Fin 2) : ∫ θ, θ i ∂unif2 = 1 / 2 := by
  have := uniform01.isProbabilityMeasure
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) i (F := fun x => x)
    measurable_id.aestronglyMeasurable, uniform01_integral, integral_id]
  norm_num

/-- Under the uniform prior, the expected gains from trade are `E[(θ₁ - θ₀)⁺] = 1/6`. -/
theorem ms_unif_gains : ∫ θ, max (θ 1 - θ 0) 0 ∂unif2 = 1 / 6 := by
  have := uniform01.isProbabilityMeasure
  rw [re_unif2_integral (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
    (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [intervalIntegral.integral_congr (g := fun a => (1 - a) ^ 2 / 2) fun a ha => ?_]
  · rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2 / 2), intervalIntegral.integral_div,
      integral_pow]
    norm_num
  · rw [Set.uIcc_of_le zero_le_one] at ha
    have e : ∀ x : ℝ, max (x - a) 0 = if a < x then x - a else 0 := by
      intro x
      split_ifs with h
      · exact max_eq_left (by linarith)
      · exact max_eq_right (by linarith [not_lt.1 h])
    simp only [e]
    rw [re_integral_ite_gt ha, intervalIntegral.integral_sub (f := fun x => x)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring

/-- **Exercise 23.E.7(b)** (MWG, p. 923), the expected surplus: `E[max(θ₀, θ₁)] = 2/3`. -/
theorem exercise_23_E_7b_surplus : ∫ θ, max (θ 0) (θ 1) ∂unif2 = 2 / 3 := by
  have := uniform01.isProbabilityMeasure
  have e : (fun θ : Fin 2 → ℝ => max (θ 0) (θ 1)) = fun θ => θ 0 + max (θ 1 - θ 0) 0 := by
    funext θ
    rcases le_total (θ 0) (θ 1) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hI0 : Integrable (fun θ : Fin 2 → ℝ => θ 0) unif2 :=
    (re_unif2_integrable (measurable_pi_apply 0) 1 fun θ hθ =>
      abs_le.2 ⟨by linarith [(hθ 0).1], (hθ 0).2⟩).1
  rw [e, integral_add hI0 (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
    (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2, ms_unif_mean, ms_unif_gains]
  norm_num

/-- **Exercise 23.E.7(b)** (MWG, p. 923). With types uniform on `[0, 1]`, no feasible social choice
function (`yᵢ ≥ 0`, `y₀ + y₁ ≤ 1`, `t₀ + t₁ ≤ 0` on `[0, 1]²`), Bayesian incentive compatible and
individually rational or not, gives the seller and buyer a sum of expected utilities
`E[θ₀y₀ + t₀] + E[θ₁y₁ + t₁]` above `E[max(θ₀, θ₁)] = 2/3`. (The integrability hypotheses say
that the expected utilities exist.) -/
theorem exercise_23_E_7b {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hI : ∀ i, Integrable (fun θ => linU allocV i (y θ, t θ) (θ i)) unif2)
    (hfeas : ∀ θ, InTypes (fun _ => 0) (fun _ => 1) θ →
      0 ≤ y θ 0 ∧ 0 ≤ y θ 1 ∧ y θ 0 + y θ 1 ≤ 1 ∧ t θ 0 + t θ 1 ≤ 0) :
    ∑ i, ∫ θ, linU allocV i (y θ, t θ) (θ i) ∂unif2 ≤ 2 / 3 := by
  have := uniform01.isProbabilityMeasure
  have hmax : Integrable (fun θ : Fin 2 → ℝ => max (θ 0) (θ 1)) unif2 :=
    (re_unif2_integrable ((measurable_pi_apply 0).max (measurable_pi_apply 1)) 1 fun θ hθ =>
      abs_le.2 ⟨by linarith [le_max_left (θ 0) (θ 1), (hθ 0).1],
        max_le (hθ 0).2 (hθ 1).2⟩).1
  rw [Fin.sum_univ_two, ← integral_add (hI 0) (hI 1), ← exercise_23_E_7b_surplus]
  refine integral_mono_ae ((hI 0).add (hI 1)) hmax ?_
  filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) ms_unif_hyps.1] with θ hθ
  obtain ⟨h0, h1, h2, h3⟩ := hfeas θ hθ
  simp only [linU, allocV]
  have m0 := le_max_left (θ 0) (θ 1)
  have m1 := le_max_right (θ 0) (θ 1)
  have mp : 0 ≤ max (θ 0) (θ 1) := (hθ 0).1.trans m0
  nlinarith [mul_le_mul_of_nonneg_right m0 h0, mul_le_mul_of_nonneg_right m1 h1]

/-- **Exercise 23.E.7(a)** (MWG, pp. 922-923). With types uniform on `[0, 1]`, if `f = (y, t)` is
Bayesian incentive compatible and interim individually rational and its trading rule is ex post
efficient (budget balance is not required), then the sum of the seller's and buyer's expected
utilities is at least `5/6`. (`y` measurable; integrability hypotheses say expectations exist.) -/
theorem exercise_23_E_7a {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (ht : ∀ i, Integrable (fun θ => t θ i) unif2)
    (heff : ExPostEfficientTrade (fun _ => 0) (fun _ => 1) y)
    (hbic : BayesianICOn unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (hir : InterimIR unif2 y t (fun _ => 0) (fun _ => 1)) :
    5 / 6 ≤ ∑ i, ∫ θ, linU allocV i (y θ, t θ) (θ i) ∂unif2 := by
  have := uniform01.isProbabilityMeasure
  have hae := re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) ms_unif_hyps.1
  obtain ⟨c, hE, hc0, hc1, hgE⟩ := ms_core (fun _ : Fin 2 => uniform01.measure)
    (fun _ => zero_le_one) ms_unif_hyps.1 hym hint ht heff hbic hir
  have hq0 : ∫ θ, max (θ 1 - (fun _ : Fin 2 => (1 : ℝ)) 0) 0 ∂unif2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with θ hθ
    exact max_eq_right (by linarith [(hθ 1).2])
  have hq1 : ∫ θ, max ((fun _ : Fin 2 => (0 : ℝ)) 1 - θ 0) 0 ∂unif2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with θ hθ
    exact max_eq_right (by linarith [(hθ 0).1])
  have hyI : ∀ i, Integrable (fun θ => θ i * y θ i) unif2 := by
    intro i
    refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
      ((measurable_pi_apply i).mul ((measurable_pi_apply i).comp hym)) 1 fun θ hθ => ?_
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    have hy : |y θ i| ≤ 1 := (Fin.forall_fin_two (p := fun i => |y θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, h1⟩⟩ i
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [(hθ i).1], (hθ i).2⟩) hy (abs_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  have hval : ∫ θ, θ 0 * y θ 0 ∂unif2 + ∫ θ, θ 1 * y θ 1 ∂unif2 = 1 / 2 + 1 / 6 := by
    rw [← integral_add (hyI 0) (hyI 1), ← ms_unif_mean 0, ← ms_unif_gains, ← integral_add
      ((re_unif2_integrable (measurable_pi_apply 0) 1 fun θ hθ =>
        abs_le.2 ⟨by linarith [(hθ 0).1], (hθ 0).2⟩).1)
      (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
        (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    obtain ⟨hs, -, -, -, -⟩ := heff θ hθ
    have := ms_eff_mul heff hθ
    rw [show y θ 0 = 1 - y θ 1 by linarith]
    linarith
  rw [Fin.sum_univ_two]
  simp only [linU, allocV]
  rw [integral_add (hyI 0) (ht 0), integral_add (hyI 1) (ht 1), hE 0, hE 1]
  rw [hq0] at hc0
  rw [hq1] at hc1
  have := ms_unif_gains
  linarith

/-- The trading rule `twoY` (trade iff `θ₀ < θ₁`) is ex post efficient. -/
theorem twoY_efficient (lo hi : Fin 2 → ℝ) : ExPostEfficientTrade lo hi twoY := by
  intro θ _
  obtain ⟨h1, h2, h3, -, -⟩ := twoY_props θ
  refine ⟨h1, h2, h3, fun h => ?_, fun h => ?_⟩
  · simp [twoY, h]
  · simp [twoY, not_lt.2 h.le]

/-- `twoY` is measurable as a map into `ℝ²`. -/
theorem measurable_twoY' : Measurable twoY := Measurable.of_eval measurable_twoY

/-- **Exercise 23.E.7** (MWG, pp. 922-923): parts (a) and (b) together give the
Myerson-Satterthwaite conclusion for uniform types, since an ex post efficient (budget
balanced) social choice function is feasible: `5/6 > 2/3`. -/
theorem exercise_23_E_7 {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (ht : ∀ i, Integrable (fun θ => t θ i) unif2)
    (heff : ExPostEfficientTrade (fun _ => 0) (fun _ => 1) y)
    (hbb : BudgetBalancedOn (fun _ => 0) (fun _ => 1) t)
    (hbic : BayesianICOn unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (hir : InterimIR unif2 y t (fun _ => 0) (fun _ => 1)) : False := by
  have := uniform01.isProbabilityMeasure
  have ha := exercise_23_E_7a hym hint ht heff hbic hir
  have hyI : ∀ i, Integrable (fun θ => θ i * y θ i) unif2 := by
    intro i
    refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
      ((measurable_pi_apply i).mul ((measurable_pi_apply i).comp hym)) 1 fun θ hθ => ?_
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    have hy : |y θ i| ≤ 1 := (Fin.forall_fin_two (p := fun i => |y θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, h1⟩⟩ i
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [(hθ i).1], (hθ i).2⟩) hy (abs_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  have hb := exercise_23_E_7b (y := y) (t := t) (fun i => (hyI i).add (ht i)) fun θ hθ => by
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    exact ⟨by linarith, h0, hs.le, (hbb θ hθ).le⟩
  linarith

/-- The expected externality transfers for bilateral trade with uniform types
(Exercise 23.D.2(a)): `t₀ = (θ₁² - θ₀²)/2`, `t₁ = (θ₀² - θ₁²)/2`. -/
noncomputable def agvBT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![(θ 1 ^ 2 - θ 0 ^ 2) / 2, (θ 0 ^ 2 - θ 1 ^ 2) / 2]

/-- `agvBT` is measurable and bounded by `1` on `[0, 1]²`. -/
theorem agvBT_facts : (∀ i, Measurable fun θ => agvBT θ i) ∧
    ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i, |agvBT θ i| ≤ 1 := by
  refine ⟨fun i => ?_, fun θ hθ i => ?_⟩
  · fin_cases i
    · exact (((measurable_pi_apply 1).pow_const 2).sub
        ((measurable_pi_apply 0).pow_const 2)).div_const 2
    · exact (((measurable_pi_apply 0).pow_const 2).sub
        ((measurable_pi_apply 1).pow_const 2)).div_const 2
  · obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    fin_cases i <;> simp only [agvBT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;> constructor <;> nlinarith

/-- The interim transfers of `agvBT`: `t̄ᵢ(a) = 1/6 - a²/2`. -/
theorem agvBT_interim (i : Fin 2) (a : ℝ) :
    interimTransfer unif2 agvBT i a = 1 / 6 - a ^ 2 / 2 := by
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => agvBT θ i) (agvBT_facts.1 i) i a]
  have hI : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
    (continuous_pow 2).intervalIntegrable _ _
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, agvBT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hI intervalIntegrable_const,
      integral_pow, intervalIntegral.integral_const]
    norm_num; ring
  · simp only [Fin.mk_one, re_update_vec1, agvBT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hI intervalIntegrable_const,
      integral_pow, intervalIntegral.integral_const]
    norm_num; ring

/-- **Exercise 23.E.1** (MWG, p. 921). In the bilateral trade setting with types uniform on
`[0, 1]`, the expected externality mechanism (whose transfers are `agvBT` on `[0, 1]²`, Exercise
23.D.2(a)) is Bayesian incentive compatible, ex post efficient and budget balanced, but the seller
of type `θ₀ = 1` gets expected utility `U₀(1) = 2/3 < 1`, so he strictly prefers not to
participate: interim individual rationality fails. This is the non-vacuity instance of
Proposition 23.E.1 without individual rationality. -/
theorem exercise_23_E_1 :
    (∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i,
      agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ i = agvBT θ i) ∧
    InterimIntegrable unif2 allocV twoY agvBT (fun _ => 0) (fun _ => 1) ∧
    BayesianICOn unif2 allocV twoY agvBT (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) agvBT ∧
    interimU unif2 allocV twoY agvBT 0 1 = 2 / 3 ∧
    ¬InterimIR unif2 twoY agvBT (fun _ => 0) (fun _ => 1) := by
  obtain ⟨hm, hb⟩ := agvBT_facts
  obtain ⟨hint, hbic, -, -⟩ := re_twoY_bic hm hb (1 / 6) fun i a _ => agvBT_interim i a
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hU : interimU unif2 allocV twoY agvBT 0 1 = 2 / 3 := by
    rw [interimU, twoY_interimBenefit h1, agvBT_interim 0 1]; norm_num
  refine ⟨fun θ hθ i => ?_, hint, hbic, twoY_efficient _ _, fun θ _ => ?_, hU, fun hir => ?_⟩
  · obtain ⟨e0, e1⟩ := exercise_23_D_2a hθ
    fin_cases i
    · simp only [Fin.zero_eta, e0, agvBT, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, e1, agvBT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · simp only [agvBT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
  · have := hir.1 1 h1
    rw [hU] at this
    norm_num at this

/-- The comparison rule `(y, t^g)` of the proof of Proposition 23.E.1 is interim individually
rational (each type's expected payoff is `θ₀ + E[(θ₁ - θ₀)⁺]` or `E[(θ₁ - θ₀)⁺]`). -/
theorem ms_vcg_interimIR {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (heff : ExPostEfficientTrade lo hi y)
    (hy : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i),
      Integrable (fun θ' => allocV i (y (update θ' i a))) (Measure.pi μ)) :
    InterimIR (Measure.pi μ) y (msVcgT y) lo hi := by
  obtain ⟨hint, -⟩ := ms_vcg_bic μ hsupp hym heff hy
  have hI : ∀ i, ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), msVcgT y (update θ' i b)) b) (Measure.pi μ) :=
    fun i b hb => ((hint i b hb).1.const_mul b).add (hint i b hb).2
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [interimU, ← eq_23_D_10 (hint 0 x hx).1 (hint 0 x hx).2 x]
    have h := integral_mono_ae (integrable_const x) (hI 0 x hx) (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      have := (ms_vcg_seller heff h x).2
      simp only [update_self] at this
      rw [this]; linarith [le_max_right ((update θ' 0 x) 1 - x) 0])
    simpa using h
  · rw [interimU, ← eq_23_D_10 (hint 1 x hx).1 (hint 1 x hx).2 x]
    exact integral_nonneg_of_ae (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      have := (ms_vcg_buyer heff h x).2
      simp only [update_self] at this
      rw [this]; exact le_max_right _ _)

/-- Non-vacuity of Proposition 23.E.1 without budget balance: with uniform types the comparison
rule `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` with efficient trade is Bayesian incentive compatible, interim
individually rational and ex post efficient in trade, but not budget balanced. -/
theorem proposition_23_E_1_instance_no_bb :
    InterimIntegrable unif2 allocV twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    BayesianICOn unif2 allocV twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    InterimIR unif2 twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    ¬BudgetBalancedOn (fun _ => 0) (fun _ => 1) (msVcgT twoY) := by
  have := uniform01.isProbabilityMeasure
  have hy : ∀ i, ∀ a ∈ Set.Icc ((fun _ : Fin 2 => (0 : ℝ)) i) ((fun _ : Fin 2 => (1 : ℝ)) i),
      Integrable (fun θ' => allocV i (twoY (update θ' i a))) unif2 := by
    intro i a ha
    refine (re_unif2_integrable (measurable_twoY i) 1 fun θ _ => ?_).2 i a ha
    obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    exact (Fin.forall_fin_two (p := fun i => |allocV i (twoY θ)| ≤ 1)).2
      ⟨abs_le.2 ⟨by simp only [allocV]; linarith, h5⟩,
        abs_le.2 ⟨by simp only [allocV]; linarith, h3⟩⟩ i
  obtain ⟨hint, hbic⟩ := ms_vcg_bic (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
    measurable_twoY' (twoY_efficient _ _) hy
  refine ⟨hint, hbic, ms_vcg_interimIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
    measurable_twoY' (twoY_efficient _ _) hy, twoY_efficient _ _, fun hbb => ?_⟩
  have := hbb ![0, 1] fun j => by fin_cases j <;> simp
  simp [msVcgT, twoY] at this

/-- The posted-price rule at price `1/2`: trade iff `θ₀ ≤ 1/2 ≤ θ₁`. -/
noncomputable def postQ (θ : Fin 2 → ℝ) : ℝ :=
  if θ 0 ≤ 1 / 2 then (if 1 / 2 ≤ θ 1 then 1 else 0) else 0

/-- The posted-price allocation `(1 - q, q)`. -/
noncomputable def postY (θ : Fin 2 → ℝ) : Fin 2 → ℝ := ![1 - postQ θ, postQ θ]

/-- The posted-price transfers: the buyer pays the seller `1/2` when they trade. -/
noncomputable def postT (θ : Fin 2 → ℝ) : Fin 2 → ℝ := ![postQ θ / 2, -(postQ θ / 2)]

/-- `postQ` is measurable. -/
theorem measurable_postQ : Measurable postQ :=
  Measurable.ite (measurableSet_le (measurable_pi_apply 0) measurable_const)
    (Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply 1)) measurable_const
      measurable_const) measurable_const

/-- Non-vacuity of Proposition 23.E.1 without ex post efficiency: with uniform types, the
posted-price rule at `1/2` is dominant strategy (hence Bayesian) incentive compatible, ex post
(hence interim) individually rational and budget balanced, but its trading rule is not ex post
efficient (no trade at `θ = (3/4, 7/8)`). -/
theorem proposition_23_E_1_instance_no_eff :
    InterimIntegrable unif2 allocV postY postT (fun _ => 0) (fun _ => 1) ∧
    DominantICOn (fun _ => 0) (fun _ => 1) postY postT ∧
    BayesianICOn unif2 allocV postY postT (fun _ => 0) (fun _ => 1) ∧
    ExPostIR (fun _ => 0) (fun _ => 1) postY postT ∧
    InterimIR unif2 postY postT (fun _ => 0) (fun _ => 1) ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) postT ∧
    ¬ExPostEfficientTrade (fun _ => 0) (fun _ => 1) postY := by
  have := uniform01.isProbabilityMeasure
  have hq : ∀ θ, 0 ≤ postQ θ ∧ postQ θ ≤ 1 := fun θ => by
    simp only [postQ]; split_ifs <;> norm_num
  have hint : InterimIntegrable unif2 allocV postY postT (fun _ => 0) (fun _ => 1) := by
    intro i a ha
    have hb : ∀ θ : Fin 2 → ℝ, |allocV i (postY θ)| ≤ 1 ∧ |postT θ i| ≤ 1 := by
      intro θ
      obtain ⟨h0, h1⟩ := hq θ
      fin_cases i <;> simp only [allocV, postY, postT, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
        constructor <;> constructor <;> linarith
    have hm : Measurable (fun θ => allocV i (postY θ)) ∧ Measurable fun θ => postT θ i := by
      fin_cases i
      · exact ⟨measurable_const.sub measurable_postQ, measurable_postQ.div_const 2⟩
      · exact ⟨measurable_postQ, (measurable_postQ.div_const 2).neg⟩
    exact ⟨(re_unif2_integrable hm.1 1 fun θ _ => (hb θ).1).2 i a ha,
      (re_unif2_integrable hm.2 1 fun θ _ => (hb θ).2).2 i a ha⟩
  have hds : DominantICOn (fun _ => 0) (fun _ => 1) postY postT := by
    intro i θ hθ a ha
    fin_cases i
    · simp only [Fin.zero_eta, linU, allocV, postY, postT, postQ, Matrix.cons_val_zero,
        update_self, update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      split_ifs <;> linarith
    · simp only [Fin.mk_one, linU, allocV, postY, postT, postQ, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, update_self, update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      split_ifs <;> linarith
  have hxir : ExPostIR (fun _ => 0) (fun _ => 1) postY postT := by
    intro θ _
    simp only [linU, allocV, postY, postT, postQ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor <;> split_ifs <;> linarith
  refine ⟨hint, hds, ms_bic_of_dsic (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hds,
    hxir, ms_interimIR_of_exPostIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hxir,
    fun θ _ => by simp [postT], fun heff => ?_⟩
  have h := (heff ![3 / 4, 7 / 8] fun j => by fin_cases j <;> norm_num).2.2.2.1 (by norm_num)
  norm_num [postY, postQ] at h

/-- The split-the-difference rule: trade iff `θ₀ < θ₁`, at the price `(θ₀ + θ₁)/2`. -/
noncomputable def splitT (θ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(θ 0 + θ 1) / 2 * twoY θ 1, -((θ 0 + θ 1) / 2 * twoY θ 1)]

/-- Non-vacuity of Proposition 23.E.1 without incentive compatibility: with uniform types, the
split-the-difference rule is ex post efficient (efficient trade and budget balance) and ex post
(hence interim) individually rational, but not Bayesian incentive compatible: a seller of type
`0` expects `1/4` from the truth and `5/16` from announcing `1/2`. -/
theorem proposition_23_E_1_instance_no_bic :
    InterimIntegrable unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) splitT ∧
    ExPostIR (fun _ => 0) (fun _ => 1) twoY splitT ∧
    InterimIR unif2 twoY splitT (fun _ => 0) (fun _ => 1) ∧
    ¬BayesianICOn unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) := by
  have := uniform01.isProbabilityMeasure
  have hm : ∀ i, Measurable fun θ => splitT θ i := by
    intro i; fin_cases i
    · exact (((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)
    · exact ((((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)).neg
  have hint : InterimIntegrable unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) := by
    intro i a ha
    refine ⟨(re_unif2_integrable (measurable_twoY i) 1 fun θ _ => ?_).2 i a ha,
      (re_unif2_integrable (hm i) 1 fun θ hθ => ?_).2 i a ha⟩
    · obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
      exact (Fin.forall_fin_two (p := fun i => |allocV i (twoY θ)| ≤ 1)).2
        ⟨abs_le.2 ⟨by simp only [allocV]; linarith, h5⟩,
          abs_le.2 ⟨by simp only [allocV]; linarith, h3⟩⟩ i
    · obtain ⟨-, h2, h3, -, -⟩ := twoY_props θ
      obtain ⟨a0, b0⟩ := hθ 0
      obtain ⟨a1, b1⟩ := hθ 1
      fin_cases i <;> simp only [splitT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;> constructor <;> nlinarith
  have hxir : ExPostIR (fun _ => 0) (fun _ => 1) twoY splitT := by
    intro θ _
    simp only [linU, allocV, splitT, twoY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor <;> split_ifs <;> linarith
  refine ⟨hint, twoY_efficient _ _, fun θ _ => by simp [splitT], hxir,
    ms_interimIR_of_exPostIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hxir,
    fun hbic => ?_⟩
  have hG : Measurable fun σ : Fin 2 → ℝ => linU allocV 0 (twoY σ, splitT σ) 0 := by
    simp only [linU, allocV, zero_mul, zero_add]
    exact hm 0
  have hval : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∫ θ', linU allocV 0 (twoY (update θ' 0 a),
      splitT (update θ' 0 a)) 0 ∂unif2 = ∫ x in a..1, (a + x) / 2 := by
    intro a ha
    rw [re_unif2_update hG 0 a]
    simp only [re_update_vec0, linU, allocV, splitT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, zero_add]
    have e : ∀ x : ℝ, (a + x) / 2 * (if a < x then (1 : ℝ) else 0) =
        if a < x then (a + x) / 2 else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    exact re_integral_ite_gt ha _
  have h := hbic 0 0 ⟨le_rfl, zero_le_one⟩ (1 / 2) ⟨by norm_num, by norm_num⟩
  change ∫ θ', linU allocV 0 (twoY (update θ' 0 (1 / 2)), splitT (update θ' 0 (1 / 2))) 0
    ∂unif2 ≤ ∫ θ', linU allocV 0 (twoY (update θ' 0 0), splitT (update θ' 0 0)) 0 ∂unif2 at h
  rw [hval (1 / 2) ⟨by norm_num, by norm_num⟩, hval 0 ⟨le_rfl, zero_le_one⟩] at h
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_add (g := fun x => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_add (g := fun x => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _), integral_id, integral_id,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
    at h
  norm_num at h

/-! ### Exercise 23.E.3: two types each -/

/-- Exercise 23.E.3's valuations: the seller's are `0` (type `false`) or `2` (type `true`), the
buyer's `1` (type `false`) or `3` (type `true`). -/
def discVal : Fin 2 → Bool → ℝ :=
  fun i b => if i = 0 then (if b then 2 else 0) else (if b then 3 else 1)

/-- Linear utilities `θᵢyᵢ + tᵢ` with these valuations; outcomes are `(y, t)`. -/
def discU : Fin 2 → (Fin 2 → ℝ) × (Fin 2 → ℝ) → Bool → ℝ :=
  fun i x b => discVal i b * x.1 i + x.2 i

/-- Trade unless the seller has valuation `2` and the buyer `1` (exactly when `θ₀ < θ₁`), at
price `1` when both valuations are low and `2` otherwise. -/
def discF (θ : Fin 2 → Bool) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  let q : ℝ := if θ 0 = true ∧ θ 1 = false then 0 else 1
  let p : ℝ := if θ 0 = false ∧ θ 1 = false then 1 else 2
  (![1 - q, q], ![p * q, -(p * q)])

/-- **Exercise 23.E.3** (MWG, p. 922). With two equally likely valuations each, seller in
`{0, 2}` and buyer in `{1, 3}` (independent; `(0, 2) ∩ (1, 3) ≠ ∅`, so gains from trade are
possible but not certain), the social choice function `discF` is Bayesian incentive compatible,
ex post efficient (trade exactly when `θ₀ < θ₁`, budget balance) and ex post (hence interim)
individually rational. So the strictly positive density assumption of Proposition 23.E.1 cannot
be dropped. -/
theorem exercise_23_E_3 :
    BayesianIC (indepBeliefs (aaP (1 / 2))) discU discF ∧
    (∀ θ, (discF θ).1 0 + (discF θ).1 1 = 1 ∧
      ((discF θ).1 1 = 1 ↔ discVal 0 (θ 0) < discVal 1 (θ 1)) ∧
      ((discF θ).1 1 = 0 ↔ discVal 1 (θ 1) < discVal 0 (θ 0))) ∧
    (∀ θ, (discF θ).2 0 + (discF θ).2 1 = 0) ∧
    (∀ θ, discVal 0 (θ 0) ≤ discU 0 (discF θ) (θ 0) ∧ 0 ≤ discU 1 (discF θ) (θ 1)) ∧
    (∀ b, discVal 0 b ≤ ∫ θ', discU 0 (discF (update θ' 0 b)) b ∂aaP (1 / 2)) ∧
    (∀ b, 0 ≤ ∫ θ', discU 1 (discF (update θ' 1 b)) b ∂aaP (1 / 2)) := by
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  refine ⟨fun i θi θh => ?_, fun θ => ?_, fun θ => ?_, fun θ => ?_, fun b => ?_, fun b => ?_⟩
  · simp only [indepBeliefs]
    rw [integral_aaP _ h0 h1 i θh (fun σ => discU i (discF σ) θi),
      integral_aaP _ h0 h1 i θi (fun σ => discU i (discF σ) θi)]
    fin_cases i <;> cases θi <;> cases θh <;>
      simp [discU, discF, discVal] <;> norm_num
  · obtain ⟨b0, hb0⟩ : ∃ b, θ 0 = b := ⟨_, rfl⟩
    obtain ⟨b1, hb1⟩ : ∃ b, θ 1 = b := ⟨_, rfl⟩
    cases b0 <;> cases b1 <;> simp [discF, discVal, hb0, hb1]
    norm_num
  · simp [discF]
  · obtain ⟨b0, hb0⟩ : ∃ b, θ 0 = b := ⟨_, rfl⟩
    obtain ⟨b1, hb1⟩ : ∃ b, θ 1 = b := ⟨_, rfl⟩
    cases b0 <;> cases b1 <;> simp [discU, discF, discVal, hb0, hb1] <;> norm_num
  · rw [integral_aaP _ h0 h1 0 b (fun σ => discU 0 (discF σ) b)]
    cases b <;> simp [discU, discF, discVal] <;> norm_num
  · rw [integral_aaP _ h0 h1 1 b (fun σ => discU 1 (discF σ) b)]
    cases b <;> simp [discU, discF, discVal]
    norm_num

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bilateral trade with adverse selection

MWG, Section 23.F, Example 23.F.3 (pp. 906-910), with Exercises 23.F.8, 23.F.9 and 23.F.10
(p. 924).

A seller (agent 1) of one unit has a type `θ_L` or `θ_H` (`Prob(θ_H) = .2`); the buyer (agent 2)
has no private information. A social choice function is `(y_L, t_L, y_H, t_H)` (trade
probability and transfer to the seller for each seller type), with utilities (23.F.11)
`u₁(y, t | θ_L) = t + 20(1 - y)`, `u₁(y, t | θ_H) = t + 40(1 - y)`, `u₂(y, t | θ_L) = 30y - t`,
`u₂(y, t | θ_H) = 50y - t`. We write `.2 = 1/5` and `.8 = 4/5`.

* The incentive feasible set `F*`: interim IR (23.F.12)-(23.F.14) and BIC (23.F.15)-(23.F.16).
* **Exercise 23.F.8**: an ex post (classically) efficient social choice function has
  `y_L = y_H = 1` (and conversely, for the trade probabilities).
* **Exercise 23.F.9(a)-(c)** = properties (i)-(iii) on p. 907.
* Problem (23.F.17), **Steps 1-4**, the reduced problems (23.F.18), (23.F.19), and the explicit
  solution of (23.F.19) (Figure 23.F.1): `y_H = (8 - ū₁H - ū₂)/14`, `t_H = 40 y_H + ū₁H`.
* The interim incentive efficient social choice functions (Definition 23.F.2 with `F = F*`) are
  exactly `y_L = 1`, `t_L = 20 + t_H - 20 y_H` with `(y_H, t_H)` in the shaded set of
  Figure 23.F.2, `{y_H ∈ [0, 1], t_H ≥ 40 y_H, t_H ≤ 26 y_H + 8}` (`bas_interimIE_iff`); they are
  exactly the solutions of (23.F.17) for some `ū₁H, ū₂ ≥ 0`; and `y_H ≤ 4/7`.
* The ex ante incentive efficient social choice functions (Definition 23.F.1 with `F = F*`) are
  exactly those with, in addition, `t_H = 40 y_H` (the boundary segment of Figure 23.F.3,
  `y_H ∈ [0, 4/7]`); the high-quality seller's IR constraint binds; footnote 54: `y_H ≤ 4/7 < 1`.
* **Exercise 23.F.10** (seller IR not imposed, buyer IR imposed): the interim incentive
  efficient set is `y_L = 1`, `t_L = 20 + t_H - 20 y_H`, `y_H ∈ [0, 1]`, `t_H ≤ 26 y_H + 8`; the ex
  ante incentive efficient set is `y_L = y_H = 1`, `t_L = t_H ≤ 34` (all ex post efficient).

Proof device (ours, not MWG's): on `F*` (indeed whenever (IC_L) holds and `y_L ≤ 1`),
`7 U₁(θ_L) + 3 U₁(θ_H) + 10 U₂ ≤ 340` (`bas_key`), with equality exactly when `y_L = 1` and
(IC_L) binds; the ex ante analogue is `14 U₁ + 16 U₂ ≤ 464` on `F*`.
-/

namespace MWG.MechanismDesign

/-- **Example 23.F.3** (MWG, p. 906). A social choice function `(y_L, t_L, y_H, t_H)`: the
probability of trade and the transfer from the buyer to the seller for each seller type. -/
structure BasSCF where
  /-- Probability of trade when the seller's type is `θ_L`. -/
  yL : ℝ
  /-- Transfer to the seller when his type is `θ_L`. -/
  tL : ℝ
  /-- Probability of trade when the seller's type is `θ_H`. -/
  yH : ℝ
  /-- Transfer to the seller when his type is `θ_H`. -/
  tH : ℝ

namespace BasSCF

/-- **(23.F.11)** (MWG, p. 906). The low-quality seller's utility `t_L + 20(1 - y_L)`. -/
def U1L (f : BasSCF) : ℝ := f.tL + 20 * (1 - f.yL)

/-- **(23.F.11)** (MWG, p. 906). The high-quality seller's utility `t_H + 40(1 - y_H)`. -/
def U1H (f : BasSCF) : ℝ := f.tH + 40 * (1 - f.yH)

/-- **(23.F.14)** (MWG, p. 906). The buyer's (interim = ex ante) expected utility
`.2(50 y_H - t_H) + .8(30 y_L - t_L)`. -/
noncomputable def U2 (f : BasSCF) : ℝ := 1 / 5 * (50 * f.yH - f.tH) + 4 / 5 * (30 * f.yL - f.tL)

/-- The seller's ex ante expected utility (MWG, p. 909),
`U₁ = .8(t_L + 20(1 - y_L)) + .2(t_H + 40(1 - y_H))`. -/
noncomputable def U1 (f : BasSCF) : ℝ := 4 / 5 * f.U1L + 1 / 5 * f.U1H

/-- Trade probabilities lie in `[0, 1]`. -/
def Prob (f : BasSCF) : Prop := 0 ≤ f.yL ∧ f.yL ≤ 1 ∧ 0 ≤ f.yH ∧ f.yH ≤ 1

/-- **(23.F.15)** (MWG, p. 907), `(IC_H)`: `t_H + 40(1 - y_H) ≥ t_L + 40(1 - y_L)`. -/
def ICH (f : BasSCF) : Prop := f.tL + 40 * (1 - f.yL) ≤ f.tH + 40 * (1 - f.yH)

/-- **(23.F.16)** (MWG, p. 907), `(IC_L)`: `t_L + 20(1 - y_L) ≥ t_H + 20(1 - y_H)`. -/
def ICL (f : BasSCF) : Prop := f.tH + 20 * (1 - f.yH) ≤ f.tL + 20 * (1 - f.yL)

/-- **(23.F.12)** (MWG, p. 906), `(IR_1L)`: `t_L + 20(1 - y_L) ≥ 20`. -/
def IR1L (f : BasSCF) : Prop := 20 ≤ f.U1L

/-- **(23.F.13)** (MWG, p. 906), `(IR_1H)`: `t_H + 40(1 - y_H) ≥ 40`. -/
def IR1H (f : BasSCF) : Prop := 40 ≤ f.U1H

/-- **(23.F.14)** (MWG, p. 906), `(IR_2)`: `.2(50 y_H - t_H) + .8(30 y_L - t_L) ≥ 0`. -/
def IR2 (f : BasSCF) : Prop := 0 ≤ f.U2

end BasSCF

/-- **Example 23.F.3** (MWG, pp. 906-907). The incentive feasible set `F*`: trade probabilities in
`[0, 1]`, Bayesian incentive compatibility (23.F.15)-(23.F.16) and interim individual
rationality (23.F.12)-(23.F.14). -/
def basFStar : Set BasSCF :=
  {f | f.Prob ∧ f.ICH ∧ f.ICL ∧ f.IR1L ∧ f.IR1H ∧ f.IR2}

/-- **Exercise 23.F.10** (MWG, p. 924). The feasible set when trade is not voluntary for the
seller (but is for the buyer): BIC and the buyer's IR constraint only. -/
def basFBuyerIR : Set BasSCF :=
  {f | f.Prob ∧ f.ICH ∧ f.ICL ∧ f.IR2}

/-- Interim (weak) dominance with one strict improvement: `U₁(θ_L | g) ≥ U₁(θ_L | f)`,
`U₁(θ_H | g) ≥ U₁(θ_H | f)`, `U₂(g) ≥ U₂(f)`, one of them strict. -/
def basInterimDominates (g f : BasSCF) : Prop :=
  f.U1L ≤ g.U1L ∧ f.U1H ≤ g.U1H ∧ f.U2 ≤ g.U2 ∧ (f.U1L < g.U1L ∨ f.U1H < g.U1H ∨ f.U2 < g.U2)

/-- Ex ante (weak) dominance with one strict improvement: `U₁(g) ≥ U₁(f)`, `U₂(g) ≥ U₂(f)`,
one of them strict. -/
def basExAnteDominates (g f : BasSCF) : Prop :=
  f.U1 ≤ g.U1 ∧ f.U2 ≤ g.U2 ∧ (f.U1 < g.U1 ∨ f.U2 < g.U2)

/-- **Definition 23.F.2** (MWG, p. 898) in Example 23.F.3: `f` is interim efficient in `F`. -/
def BasInterimEfficientIn (F : Set BasSCF) (f : BasSCF) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, basInterimDominates g f

/-- **Definition 23.F.1** (MWG, p. 898) in Example 23.F.3: `f` is ex ante efficient in `F`. -/
def BasExAnteEfficientIn (F : Set BasSCF) (f : BasSCF) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, basExAnteDominates g f

/-- Ex post (classical) efficiency of the outcome `(y, t)` for one seller type, whose valuation
is `a` for the seller and `b` for the buyer (Definition 23.B.2 = Definition 23.F.3 with all
social choice functions, p. 900): `y ∈ [0, 1]` and no `(y', t')` with `y' ∈ [0, 1]` makes one
agent better off and neither worse off. -/
def BasPairEfficient (a b y t : ℝ) : Prop :=
  0 ≤ y ∧ y ≤ 1 ∧ ¬ ∃ y' t' : ℝ, 0 ≤ y' ∧ y' ≤ 1 ∧ t + a * (1 - y) ≤ t' + a * (1 - y') ∧
    b * y - t ≤ b * y' - t' ∧ (t + a * (1 - y) < t' + a * (1 - y') ∨ b * y - t < b * y' - t')

/-- **Example 23.F.3** (MWG, p. 906). The social choice function is ex post (classically)
efficient: efficient for each realisation of the seller's type. -/
def BasExPostEfficient (f : BasSCF) : Prop :=
  BasPairEfficient 20 30 f.yL f.tL ∧ BasPairEfficient 40 50 f.yH f.tH

/-- When the buyer values the good more than the seller (`a < b`), an outcome is ex post
efficient iff trade occurs for sure. -/
theorem basPairEfficient_iff {a b y t : ℝ} (hab : a < b) :
    BasPairEfficient a b y t ↔ y = 1 := by
  constructor
  · rintro ⟨h0, h1, hne⟩
    by_contra hy
    have hy' : y < 1 := lt_of_le_of_ne h1 hy
    apply hne
    refine ⟨1, t + a * (1 - y) + (b - a) * (1 - y) / 2, zero_le_one, le_rfl, ?_, ?_, ?_⟩
    · have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      linarith
    · have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      nlinarith
    · left
      have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      linarith
  · rintro rfl
    refine ⟨zero_le_one, le_rfl, ?_⟩
    rintro ⟨y', t', h0, h1, hu1, hu2, hs⟩
    have hp : 0 ≤ (b - a) * (1 - y') := mul_nonneg (by linarith) (by linarith)
    rcases hs with hs | hs <;> nlinarith

/-- **Exercise 23.F.8** (MWG, p. 924). Any ex post classically efficient social choice function in
Example 23.F.3 has `y_L = y_H = 1` (and conversely these trade probabilities make it ex post
efficient, whatever the transfers). -/
theorem exercise_23_F_8 (f : BasSCF) : BasExPostEfficient f ↔ f.yL = 1 ∧ f.yH = 1 := by
  unfold BasExPostEfficient
  rw [basPairEfficient_iff (by norm_num), basPairEfficient_iff (by norm_num)]

/-- **Exercise 23.F.9(a)** (MWG, pp. 907, 924), property (i). No feasible social choice function
(element of `F*`) is ex post (classically) efficient. -/
theorem exercise_23_F_9a (f : BasSCF) (hf : f ∈ basFStar) : ¬ BasExPostEfficient f := by
  rw [exercise_23_F_8]
  rintro ⟨hL, hH⟩
  obtain ⟨-, -, hICL, hIRL, hIRH, hIR2⟩ := hf
  simp only [BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L, BasSCF.U1H,
    BasSCF.U2, hL, hH] at hICL hIRL hIRH hIR2
  linarith

/-- **Exercise 23.F.9(b)** (MWG, pp. 907, 924), property (ii). In any feasible social choice
function `y_H ≤ y_L` and `t_H ≤ t_L` (only incentive compatibility is needed). -/
theorem exercise_23_F_9b (f : BasSCF) (hf : f ∈ basFStar) : f.yH ≤ f.yL ∧ f.tH ≤ f.tL := by
  obtain ⟨-, hICH, hICL, -⟩ := hf
  simp only [BasSCF.ICH, BasSCF.ICL] at hICH hICL
  constructor <;> linarith

/-- **Exercise 23.F.9(c)** (MWG, pp. 907, 924), property (iii). In any feasible social choice
function the low-quality seller's expected gains from trade are at least the high-quality
seller's: `t_L - 20 y_L ≥ t_H - 40 y_H`. -/
theorem exercise_23_F_9c (f : BasSCF) (hf : f ∈ basFStar) :
    f.tH - 40 * f.yH ≤ f.tL - 20 * f.yL := by
  obtain ⟨⟨-, -, hyH, -⟩, -, hICL, -⟩ := hf
  simp only [BasSCF.ICL] at hICL
  linarith

/-! ### Problem (23.F.17) and Steps 1-4 -/

/-- The constraints of problem **(23.F.17)** (MWG, p. 907), for given `ū₁H, ū₂`:
`y_L, y_H ∈ [0, 1]`; (i) `t_H - 40 y_H ≥ t_L - 40 y_L`; (ii) `t_L - 20 y_L ≥ t_H - 20 y_H`;
(iii) `t_H - 40 y_H ≥ ū₁H`; (iv) `.2(50 y_H - t_H) + .8(30 y_L - t_L) ≥ ū₂`. -/
def basC17 (u1H u2 : ℝ) (f : BasSCF) : Prop :=
  f.Prob ∧ f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH ∧ f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL ∧
    u1H ≤ f.tH - 40 * f.yH ∧ u2 ≤ f.U2

/-- `f` solves problem **(23.F.17)** (MWG, p. 907): it maximises `t_L - 20 y_L` subject to the
constraints. -/
def BasSolves17 (u1H u2 : ℝ) (f : BasSCF) : Prop :=
  basC17 u1H u2 f ∧ ∀ g, basC17 u1H u2 g → g.tL - 20 * g.yL ≤ f.tL - 20 * f.yL

/-- **Problem (23.F.17)** (MWG, p. 907): the constraints are the incentive constraints
(23.F.15)-(23.F.16) and the participation constraints `U₁(θ_H) ≥ 40 + ū₁H`, `U₂ ≥ ū₂` with the
constants removed, and the objective is `U₁(θ_L) - 20`. -/
theorem basC17_iff (u1H u2 : ℝ) (f : BasSCF) :
    basC17 u1H u2 f ↔ f.Prob ∧ f.ICH ∧ f.ICL ∧ 40 + u1H ≤ f.U1H ∧ u2 ≤ f.U2 := by
  simp only [basC17, BasSCF.ICH, BasSCF.ICL, BasSCF.U1H]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, by linarith, by linarith, by linarith, h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, by linarith, by linarith, by linarith, h4⟩

/-- **Problem (23.F.17)** (MWG, p. 907). With `ū₁H, ū₂ ≥ 0` its constraints imply membership of
`F*` (the low-quality seller's IR constraint follows from (ii), (iii) and `y_H ≥ 0`). -/
theorem basFStar_of_C17 {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) {f : BasSCF}
    (hf : basC17 u1H u2 f) : f ∈ basFStar := by
  obtain ⟨hP, hi, hii, hiii, hiv⟩ := hf
  have hyH := hP.2.2.1
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H] <;> linarith

/-- **Step 1** (MWG, pp. 907-908). Any solution to problem (23.F.17) has `y_L = 1`: otherwise
`(y_L + ε, t_L + 30ε, y_H, t_H)` (here with `ε = 1 - y_L`) satisfies all constraints and raises
the objective. -/
theorem bas_step1 {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) : f.yL = 1 := by
  obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
  by_contra hne
  have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne
  have hg := hmax ⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩
    ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, by dsimp only; linarith, by dsimp only; linarith,
      hiii, by simp only [BasSCF.U2] at hiv ⊢; linarith⟩
  dsimp only at hg
  linarith

/-- **Step 3** (MWG, p. 908). In any solution to problem (23.F.17), constraint (ii) binds:
otherwise `(y_L, t_L + ε, y_H + ε, t_H + 45ε)` for small `ε > 0` is feasible and raises the
objective. (We take `ε` equal to `1/24` of the slack in (ii); `y_H + ε ≤ 1` then follows from
(i) and `y_L ≤ 1`, so Step 2 is not needed here.) -/
theorem bas_step3 {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) :
    f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
  obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
  by_contra hne
  have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
    rcases lt_or_eq_of_le hii with h | h
    · linarith
    · exact absurd h.symm hne
  set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hg := hmax ⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩
    ⟨⟨h0L, h1L, by linarith, by dsimp only; linarith⟩, by dsimp only; linarith,
      by dsimp only; linarith, by dsimp only; linarith,
      by simp only [BasSCF.U2] at hiv ⊢; linarith⟩
  dsimp only at hg
  linarith

/-- **Step 4** (MWG, p. 908). If constraint (ii) binds and `y_L ≥ y_H`, then constraint (i) is
satisfied. -/
theorem bas_step4 {f : BasSCF} (hii : f.tL - 20 * f.yL = f.tH - 20 * f.yH)
    (hy : f.yH ≤ f.yL) : f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH := by
  linarith

/-- The key inequality: whenever (IC_L) holds and `y_L ≤ 1`,
`7 U₁(θ_L) + 3 U₁(θ_H) + 10 U₂ ≤ 340`, and the slack is
`80 (1 - y_L) + ((t_L - 20 y_L) - (t_H - 20 y_H))`. -/
theorem bas_key (f : BasSCF) :
    7 * f.U1L + 3 * f.U1H + 10 * f.U2 =
      340 - 80 * (1 - f.yL) - ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) := by
  simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
  ring

/-- The constraints of problem **(23.F.19)** (MWG, p. 908): `y_H ∈ [0, 1]`,
(ii) `t_H - 40 y_H ≥ ū₁H`, (iv') `26 y_H - t_H + 8 ≥ ū₂`. -/
def basC19 (u1H u2 yH tH : ℝ) : Prop :=
  0 ≤ yH ∧ yH ≤ 1 ∧ u1H ≤ tH - 40 * yH ∧ u2 ≤ 26 * yH - tH + 8

/-- `(y_H, t_H)` solves problem **(23.F.19)** (MWG, p. 908): it maximises `t_H - 20 y_H` subject
to the constraints. -/
def BasSolves19 (u1H u2 yH tH : ℝ) : Prop :=
  basC19 u1H u2 yH tH ∧ ∀ y t, basC19 u1H u2 y t → t - 20 * y ≤ tH - 20 * yH

/-- **Problem (23.F.19) and Figure 23.F.1** (MWG, pp. 908-909). For `ū₁H, ū₂ ≥ 0`, problem
(23.F.19) has a solution iff `ū₁H + ū₂ ≤ 8`, and its unique solution is the intersection of
`t_H = 40 y_H + ū₁H` and `t_H = 26 y_H + 8 - ū₂`: `y_H = (8 - ū₁H - ū₂)/14`,
`t_H = 40 y_H + ū₁H`. -/
theorem bas_solves19_iff {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) (yH tH : ℝ) :
    BasSolves19 u1H u2 yH tH ↔
      u1H + u2 ≤ 8 ∧ yH = (8 - u1H - u2) / 14 ∧ tH = 40 * yH + u1H := by
  constructor
  · rintro ⟨⟨h0, h1', hii, hiv⟩, hmax⟩
    have hs : u1H + u2 ≤ 8 := by linarith
    have hg := hmax ((8 - u1H - u2) / 14) (40 * ((8 - u1H - u2) / 14) + u1H)
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    refine ⟨hs, ?_, ?_⟩ <;> linarith
  · rintro ⟨hs, hy, ht⟩
    refine ⟨⟨by rw [hy]; linarith, by rw [hy]; linarith, by linarith, by rw [ht, hy]; linarith⟩,
      fun y t ⟨_, _, hii, hiv⟩ => ?_⟩
    rw [ht, hy]
    linarith

/-- **Problems (23.F.17)-(23.F.19)** (MWG, p. 908). For `ū₁H, ū₂ ≥ 0`, `f` solves (23.F.17) iff
`y_L = 1`, `t_L = 20 + t_H - 20 y_H` and `(y_H, t_H)` solves (23.F.19). -/
theorem bas_solves17_iff {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) (f : BasSCF) :
    BasSolves17 u1H u2 f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ BasSolves19 u1H u2 f.yH f.tH := by
  constructor
  · intro hf
    have hL := bas_step1 hf
    have hb := bas_step3 hf
    obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
    simp only [BasSCF.U2] at hiv
    refine ⟨hL, by rw [hL] at hb; linarith,
      ⟨h0H, h1H, hiii, by rw [hL] at hiv; linarith⟩, fun y t ⟨hy0, hy1, hc2, hc4⟩ => ?_⟩
    have hg := hmax ⟨1, 20 + t - 20 * y, y, t⟩
      ⟨⟨zero_le_one, le_rfl, hy0, hy1⟩, by dsimp only; linarith, by dsimp only; linarith,
        hc2, by simp only [BasSCF.U2]; linarith⟩
    dsimp only at hg
    rw [hL] at hb
    linarith
  · rintro ⟨hL, htL, hs⟩
    obtain ⟨hs8, hy, ht⟩ := (bas_solves19_iff h1 h2 _ _).1 hs
    obtain ⟨⟨h0H, h1H, hii, hiv⟩, -⟩ := hs
    refine ⟨⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, by rw [hL]; linarith, by rw [hL]; linarith,
      hii, by simp only [BasSCF.U2]; rw [hL]; linarith⟩, fun g ⟨⟨_, hg1, _, _⟩, _, hgii, hgiii,
        hgiv⟩ => ?_⟩
    have hk := bas_key g
    simp only [BasSCF.U1L, BasSCF.U1H] at hk
    rw [hL]
    linarith

/-- **Step 2** (MWG, p. 908). For `ū₁H, ū₂ ≥ 0`, any solution to problem (23.F.17) has
`y_H < 1`: otherwise it would be ex post efficient and in `F*`, contradicting property (i). -/
theorem bas_step2 {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) {f : BasSCF}
    (hf : BasSolves17 u1H u2 f) : f.yH < 1 := by
  have hF := basFStar_of_C17 h1 h2 hf.1
  have hL := bas_step1 hf
  by_contra hH
  have hH' : f.yH = 1 := le_antisymm hf.1.1.2.2.2 (not_lt.1 hH)
  exact exercise_23_F_9a f hF ((exercise_23_F_8 f).2 ⟨hL, hH'⟩)

/-- **Example 23.F.3** (MWG, p. 908). In any solution of (23.F.17) (with `ū₁H, ū₂ ≥ 0`),
constraint (i) is implied by the others, as Step 4 shows. -/
theorem bas_solves17_i_redundant {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) :
    f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH :=
  bas_step4 (bas_step3 hf) (by rw [bas_step1 hf]; exact hf.1.1.2.2.2)

/-! ### Interim incentive efficiency -/

/-- **Figure 23.F.2** (MWG, p. 909). The shaded set
`{(y_H, t_H) : y_H ∈ [0, 1], t_H ≥ 40 y_H, t_H ≤ 26 y_H + 8}`. -/
def basShaded (yH tH : ℝ) : Prop := 0 ≤ yH ∧ yH ≤ 1 ∧ 40 * yH ≤ tH ∧ tH ≤ 26 * yH + 8

/-- **Figure 23.F.2** (MWG, p. 909). The shaded set is exactly the set of pairs `(y_H, t_H)` that
solve (23.F.19) for some `ū₁H ≥ 0`, `ū₂ ≥ 0`. -/
theorem bas_shaded_iff (yH tH : ℝ) :
    basShaded yH tH ↔ ∃ u1H u2 : ℝ, 0 ≤ u1H ∧ 0 ≤ u2 ∧ BasSolves19 u1H u2 yH tH := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨tH - 40 * yH, 26 * yH + 8 - tH, by linarith, by linarith, ?_⟩
    rw [bas_solves19_iff (by linarith) (by linarith)]
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨u1H, u2, h1, h2, hs⟩
    obtain ⟨hs8, hy, ht⟩ := (bas_solves19_iff h1 h2 _ _).1 hs
    refine ⟨by rw [hy]; linarith, by rw [hy]; linarith, by linarith, by rw [ht, hy]; linarith⟩

/-- **Example 23.F.3** (MWG, p. 909). On the shaded set, `y_H ≤ 4/7`. -/
theorem bas_shaded_yH_le {yH tH : ℝ} (h : basShaded yH tH) : yH ≤ 4 / 7 := by
  obtain ⟨-, -, h2, h3⟩ := h
  linarith

/-- **Example 23.F.3** (MWG, pp. 908-909). The interim incentive efficient social choice
functions (Definition 23.F.2 with `F = F*`) are exactly those with `y_L = 1`,
`t_L = 20 + t_H - 20 y_H` and `(y_H, t_H)` in the shaded set of Figure 23.F.2. -/
theorem bas_interimIE_iff (f : BasSCF) :
    BasInterimEfficientIn basFStar f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ basShaded f.yH f.tH := by
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIRL, hIRH, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H, BasSCF.U2] at hICH hICL hIRL hIRH hIR2
    -- Step 1: `y_L = 1`
    have hL : f.yL = 1 := by
      by_contra hne'
      have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne'
      refine hne ⟨⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    -- Step 3: (IC_L) binds
    have hb : f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
      by_contra hne'
      have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
        rcases lt_or_eq_of_le (show f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL by linarith) with h | h
        · linarith
        · exact absurd h.symm hne'
      set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      refine hne ⟨⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩, ?_, ?_⟩
      · refine ⟨⟨h0L, h1L, by dsimp only; linarith, by dsimp only; linarith⟩, ?_, ?_, ?_, ?_,
          ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    exact ⟨hL, by linarith, h0H, h1H, by linarith, by linarith⟩
  · rintro ⟨hL, htL, h0H, h1H, h2, h3⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
          BasSCF.U1H, BasSCF.U2] <;> linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _⟩, hd1, hd2, hd3, hs⟩
      have hkg := bas_key g
      have hkf := bas_key f
      simp only [BasSCF.ICL] at hgICL
      rw [hL] at hkf
      rcases hs with hs | hs | hs <;> linarith

/-- **Example 23.F.3** (MWG, p. 909). Every interim incentive efficient social choice function
has `y_H ≤ 4/7`. -/
theorem bas_interimIE_yH_le {f : BasSCF} (hf : BasInterimEfficientIn basFStar f) :
    f.yH ≤ 4 / 7 :=
  bas_shaded_yH_le ((bas_interimIE_iff f).1 hf).2.2

/-- **Example 23.F.3** (MWG, pp. 907-908). Problem (23.F.17) characterises the interim
incentive efficient social choice functions: `f` is interim incentive efficient iff it solves
(23.F.17) for some `ū₁H ≥ 0` and `ū₂ ≥ 0`. -/
theorem bas_interimIE_iff_solves17 (f : BasSCF) :
    BasInterimEfficientIn basFStar f ↔
      ∃ u1H u2 : ℝ, 0 ≤ u1H ∧ 0 ≤ u2 ∧ BasSolves17 u1H u2 f := by
  rw [bas_interimIE_iff]
  constructor
  · rintro ⟨hL, htL, hs⟩
    obtain ⟨u1H, u2, h1, h2, h19⟩ := (bas_shaded_iff _ _).1 hs
    exact ⟨u1H, u2, h1, h2, (bas_solves17_iff h1 h2 f).2 ⟨hL, htL, h19⟩⟩
  · rintro ⟨u1H, u2, h1, h2, h17⟩
    obtain ⟨hL, htL, h19⟩ := (bas_solves17_iff h1 h2 f).1 h17
    exact ⟨hL, htL, (bas_shaded_iff _ _).2 ⟨u1H, u2, h1, h2, h19⟩⟩

/-- **Example 23.F.3** (MWG, p. 909). With `y_L = 1` and `t_L = 20 + t_H - 20 y_H`, the ex ante
expected utilities are `U₁ = 24 + t_H - 24 y_H` and `U₂ = 8 + 26 y_H - t_H`. -/
theorem bas_exAnte_utilities {f : BasSCF} (hL : f.yL = 1) (htL : f.tL = 20 + f.tH - 20 * f.yH) :
    f.U1 = 24 + f.tH - 24 * f.yH ∧ f.U2 = 8 + 26 * f.yH - f.tH := by
  simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2, hL, htL]
  constructor <;> ring

/-! ### Ex ante incentive efficiency -/

/-- The ex ante key identity: `14 U₁ + 16 U₂ = 464 - 128(1 - y_L) - (8/5)((t_L - 20 y_L) -
(t_H - 20 y_H)) - 2(t_H - 40 y_H)`. -/
theorem bas_key_exAnte (f : BasSCF) :
    14 * f.U1 + 16 * f.U2 = 464 - 128 * (1 - f.yL) -
      8 / 5 * ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) - 2 * (f.tH - 40 * f.yH) := by
  simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
  ring

/-- **Example 23.F.3** (MWG, pp. 909-910). The ex ante incentive efficient social choice functions
(Definition 23.F.1 with `F = F*`) are exactly those with `y_L = 1`, `t_L = 20 + t_H - 20 y_H`,
`t_H = 40 y_H` and `y_H ∈ [0, 4/7]`: the heavily traced segment of Figure 23.F.3. -/
theorem bas_exAnteIE_iff (f : BasSCF) :
    BasExAnteEfficientIn basFStar f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ f.tH = 40 * f.yH ∧ 0 ≤ f.yH ∧ f.yH ≤ 4 / 7 := by
  constructor
  · rintro ⟨hf, hne⟩
    have hk := bas_key_exAnte f
    have hk' := bas_key f
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIRL, hIRH, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H] at hICH hICL hIRL hIRH hIR2
    simp only [BasSCF.U1L, BasSCF.U1H] at hk'
    have hU2 : f.U2 ≤ 8 := by linarith
    have heq : 14 * f.U1 + 16 * f.U2 = 464 := by
      by_contra hne'
      have hlt : 14 * f.U1 + 16 * f.U2 < 464 := lt_of_le_of_ne (by linarith) hne'
      set s := (8 - f.U2) / 14 with hs
      refine hne ⟨⟨1, 20 + 20 * s, s, 40 * s⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, by rw [hs]; linarith, by rw [hs]; linarith⟩, ?_, ?_, ?_, ?_,
          ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> rw [hs] <;> linarith
      · have e1 : (⟨1, 20 + 20 * s, s, 40 * s⟩ : BasSCF).U1 = 24 + 16 * s := by
          simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H]; ring
        have e2 : (⟨1, 20 + 20 * s, s, 40 * s⟩ : BasSCF).U2 = 8 - 14 * s := by
          simp only [BasSCF.U2]; ring
        rw [basExAnteDominates, e1, e2, hs]
        refine ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    have hL : f.yL = 1 := by linarith
    have hb : f.tH = 40 * f.yH := by linarith
    have hc : f.tL = 20 + f.tH - 20 * f.yH := by linarith
    refine ⟨hL, hc, hb, h0H, ?_⟩
    simp only [BasSCF.U2] at hIR2
    rw [hL, hc, hb] at hIR2
    linarith
  · rintro ⟨hL, htL, hb, h0H, h1H⟩
    refine ⟨(bas_interimIE_iff f).2 ⟨hL, htL, h0H, by linarith, hb.ge, by linarith⟩ |>.1, ?_⟩
    rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _, hgIRH, _⟩, hd1, hd2, hs⟩
    have hkg := bas_key_exAnte g
    have hkf := bas_key_exAnte f
    simp only [BasSCF.ICL] at hgICL
    simp only [BasSCF.IR1H, BasSCF.U1H] at hgIRH
    rw [hL, htL, hb] at hkf
    rcases hs with hs | hs <;> linarith

/-- **Example 23.F.3** (MWG, p. 909). Every ex ante incentive efficient social choice function is
interim incentive efficient. -/
theorem bas_interimIE_of_exAnteIE {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    BasInterimEfficientIn basFStar f := by
  obtain ⟨hL, htL, hb, h0, h1⟩ := (bas_exAnteIE_iff f).1 hf
  exact (bas_interimIE_iff f).2 ⟨hL, htL, h0, by linarith, hb.ge, by linarith⟩

/-- **Example 23.F.3** (MWG, p. 910). In every ex ante incentive efficient social choice function
the high-quality seller's interim IR constraint binds: he receives no gains from trade,
`U₁(θ_H) = 40`. -/
theorem bas_exAnteIE_IR1H_binds {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    f.U1H = 40 := by
  obtain ⟨-, -, hb, -, -⟩ := (bas_exAnteIE_iff f).1 hf
  simp only [BasSCF.U1H, hb]
  ring

/-- **Footnote 54** (MWG, p. 910). In any ex ante incentive efficient social choice function
`y_H ≤ 4/7 < 1`. -/
theorem footnote_23_54 {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    f.yH ≤ 4 / 7 ∧ (4 / 7 : ℝ) < 1 :=
  ⟨((bas_exAnteIE_iff f).1 hf).2.2.2.2, by norm_num⟩

/-- **Example 23.F.3** (MWG, pp. 909-910). Non-vacuity: the interim and the ex ante incentive
efficient sets are nonempty, and the first is strictly larger (`(1, 28, 0, 8)` is interim but not
ex ante incentive efficient; `(1, 20 + 80/7, 4/7, 160/7)` is ex ante incentive efficient). -/
theorem bas_nonvacuous :
    BasExAnteEfficientIn basFStar ⟨1, 20 + 80 / 7, 4 / 7, 160 / 7⟩ ∧
      BasInterimEfficientIn basFStar ⟨1, 28, 0, 8⟩ ∧
      ¬ BasExAnteEfficientIn basFStar ⟨1, 28, 0, 8⟩ := by
  refine ⟨(bas_exAnteIE_iff _).2 ⟨rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    (bas_interimIE_iff _).2 ⟨rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩, fun h => ?_⟩
  have := ((bas_exAnteIE_iff _).1 h).2.2.1
  norm_num at this

/-! ### Exercise 23.F.10: no participation constraint for the seller -/

/-- **Exercise 23.F.10** (MWG, p. 924), interim part. When trade is not voluntary for the seller
(but is for the buyer), the interim incentive efficient social choice functions are exactly those
with `y_L = 1`, `t_L = 20 + t_H - 20 y_H`, `y_H ∈ [0, 1]` and `t_H ≤ 26 y_H + 8`. -/
theorem exercise_23_F_10_interim (f : BasSCF) :
    BasInterimEfficientIn basFBuyerIR f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ 0 ≤ f.yH ∧ f.yH ≤ 1 ∧ f.tH ≤ 26 * f.yH + 8 := by
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] at hICH hICL hIR2
    have hL : f.yL = 1 := by
      by_contra hne'
      have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne'
      refine hne ⟨⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    have hb : f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
      by_contra hne'
      have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
        rcases lt_or_eq_of_le (show f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL by linarith) with h | h
        · linarith
        · exact absurd h.symm hne'
      set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      refine hne ⟨⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩, ?_, ?_⟩
      · refine ⟨⟨h0L, h1L, by dsimp only; linarith, by dsimp only; linarith⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    exact ⟨hL, by linarith, h0H, h1H, by linarith⟩
  · rintro ⟨hL, htL, h0H, h1H, h3⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, ?_, ?_, ?_⟩ <;>
        simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _⟩, hd1, hd2, hd3, hs⟩
      have hkg := bas_key g
      have hkf := bas_key f
      simp only [BasSCF.ICL] at hgICL
      rw [hL] at hkf
      rcases hs with hs | hs | hs <;> linarith

/-- **Exercise 23.F.10** (MWG, p. 924), ex ante part. When trade is not voluntary for the seller
(but is for the buyer), the ex ante incentive efficient social choice functions are exactly those
with `y_L = y_H = 1` and `t_L = t_H ≤ 34`; all of them are ex post efficient (compare
footnote 54 and Section 13.B). -/
theorem exercise_23_F_10_exAnte (f : BasSCF) :
    BasExAnteEfficientIn basFBuyerIR f ↔ f.yL = 1 ∧ f.yH = 1 ∧ f.tL = f.tH ∧ f.tH ≤ 34 := by
  have hsum : ∀ g : BasSCF, g.U1 + g.U2 = 24 + 2 * g.yH + 8 * g.yL := by
    intro g
    simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
    ring
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIR2⟩ := hf
    have heq : f.U1 + f.U2 = 34 := by
      by_contra hne'
      have hlt : f.U1 + f.U2 < 34 := lt_of_le_of_ne (by rw [hsum f]; linarith) hne'
      refine hne ⟨⟨1, 34 - f.U2, 1, 34 - f.U2⟩, ?_, ?_⟩
      · simp only [BasSCF.IR2] at hIR2
        refine ⟨⟨zero_le_one, le_rfl, zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;>
          simp only [BasSCF.U2] at hIR2 <;> linarith
      · have h1 : (⟨1, 34 - f.U2, 1, 34 - f.U2⟩ : BasSCF).U1 = 34 - f.U2 := by
          simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H]; ring
        have h2 : (⟨1, 34 - f.U2, 1, 34 - f.U2⟩ : BasSCF).U2 = f.U2 := by
          simp only [BasSCF.U2]; ring
        rw [basExAnteDominates, h1, h2]
        exact ⟨by linarith, le_rfl, Or.inl (by linarith)⟩
    rw [hsum f] at heq
    have hL : f.yL = 1 := by linarith
    have hH : f.yH = 1 := by linarith
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2, hL, hH] at hICH hICL hIR2
    exact ⟨hL, hH, by linarith, by linarith⟩
  · rintro ⟨hL, hH, ht, h34⟩
    refine ⟨⟨⟨by rw [hL]; norm_num, hL.le, by rw [hH]; norm_num, hH.le⟩, ?_, ?_, ?_⟩, ?_⟩
    · simp only [BasSCF.ICH, hL, hH, ht]; linarith
    · simp only [BasSCF.ICL, hL, hH, ht]; linarith
    · simp only [BasSCF.IR2, BasSCF.U2, hL, hH, ht]; linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, hg2⟩, -⟩, hd1, hd2, hs⟩
      have hg := hsum g
      have hf := hsum f
      rw [hL, hH] at hf
      rcases hs with hs | hs <;> linarith

/-- **Exercise 23.F.10** (MWG, p. 924). Without the seller's participation constraints, ex ante
incentive efficiency still implies interim incentive efficiency, and the interim incentive
efficient set strictly contains the one under `F*`'s constraints (e.g. `(1, 30, 1, 30)` is interim
incentive efficient in the larger set). -/
theorem exercise_23_F_10_compare :
    (∀ f, BasExAnteEfficientIn basFBuyerIR f → BasInterimEfficientIn basFBuyerIR f) ∧
      BasInterimEfficientIn basFBuyerIR ⟨1, 30, 1, 30⟩ ∧
      ¬ BasInterimEfficientIn basFStar ⟨1, 30, 1, 30⟩ := by
  refine ⟨fun f hf => ?_, (exercise_23_F_10_interim _).2 ⟨rfl, by norm_num, by norm_num,
    by norm_num, by norm_num⟩, fun h => ?_⟩
  · obtain ⟨hL, hH, ht, h34⟩ := (exercise_23_F_10_exAnte f).1 hf
    exact (exercise_23_F_10_interim f).2 ⟨hL, by rw [hH, ht]; ring, by rw [hH]; norm_num,
      hH.le, by rw [hH]; linarith⟩
  · have := ((bas_interimIE_iff _).1 h).2.2
    simp only [basShaded] at this
    norm_num at this

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Participation constraints

MWG, Section 23.E, pp. 891-894.

* **Example 23.E.1** (p. 892): public project with `K = {0, 1}`, two agents with types
  `θ̲ < θ̄` (`θ̄ > 2θ̲ > 0`), cost `c ∈ (2θ̲, θ̄)` and the efficient project rule (`k = 1` iff some
  `θᵢ = θ̄`): no social choice function with this project rule is strategy-proof, ex post
  individually rational (withdrawal gives `0`) and feasible (`∑ tᵢ ≤ -ck`)
  (`example_23_E_1`); the same with an outside agent `0` whose participation requires `t₀ ≥ 0`
  (`example_23_E_1_outside`). Each pair of the three requirements is satisfiable
  (`example_23_E_1_sp_ir`, `example_23_E_1_sp_feasible`, `example_23_E_1_ir_feasible`), and the
  project rule is the efficient one (`example_23_E_1_efficient`).
* **(23.E.1)-(23.E.3)** (p. 893): ex post, interim and ex ante participation constraints with
  outside option `ūᵢ(θᵢ)`, in the general Bayesian framework (beliefs `B i θᵢ` as in
  `Bayesian.lean`; ex ante expectations under a marginal `μᵢ` on `Θᵢ`).
* p. 894: (23.E.1) ⇒ (23.E.2) (beliefs are probability measures and the payoffs integrable) and
  (23.E.2) ⇒ (23.E.3) (integrability); "the reverse is not true": two counterexamples with two
  agents, types in `Bool` and independent uniform beliefs.
-/

namespace MWG.MechanismDesign

open Function MeasureTheory

variable {ι : Type*} {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)] {X : Type*}

/-- **Section 23.E** (MWG, p. 893). Agent `i`'s interim expected utility from the social choice
function `f` when his type is `θᵢ`: `Uᵢ(θᵢ | f) = E_{θ₋ᵢ}[uᵢ(f(θᵢ, θ₋ᵢ), θᵢ) | θᵢ]`. -/
noncomputable def scfInterimU [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) (i : ι) (θi : Θ i) : ℝ :=
  ∫ θ, u i (f (update θ i θi)) θi ∂(B i θi)

/-- **Section 23.E** (MWG, p. 893). Agent `i`'s ex ante expected utility
`Uᵢ(f) = E_{θᵢ}[Uᵢ(θᵢ | f)]`, under the marginal distribution `μᵢ` of his type. -/
noncomputable def scfExAnteU [DecidableEq ι] (μ : (i : ι) → Measure (Θ i))
    (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)) (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) (i : ι) : ℝ :=
  ∫ θi, scfInterimU B u f i θi ∂(μ i)

/-- **(23.E.1)** (MWG, p. 893). Ex post participation (individual rationality) constraints:
`uᵢ(f(θᵢ, θ₋ᵢ), θᵢ) ≥ ūᵢ(θᵢ)` for all `i` and `(θᵢ, θ₋ᵢ)`. -/
def ExPostParticipation (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ i (θ : (j : ι) → Θ j), ubar i (θ i) ≤ u i (f θ) (θ i)

/-- **(23.E.2)** (MWG, p. 893). Interim participation constraints: `Uᵢ(θᵢ | f) ≥ ūᵢ(θᵢ)` for all
`i` and `θᵢ`. -/
def InterimParticipation [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ i (θi : Θ i), ubar i θi ≤ scfInterimU B u f i θi

/-- **(23.E.3)** (MWG, p. 893). Ex ante participation constraints: `Uᵢ(f) ≥ E_{θᵢ}[ūᵢ(θᵢ)]` for
all `i`. -/
def ExAnteParticipation [DecidableEq ι] (μ : (i : ι) → Measure (Θ i))
    (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)) (u : (i : ι) → X → Θ i → ℝ)
    (ubar : (i : ι) → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) : Prop :=
  ∀ i, ∫ θi, ubar i θi ∂(μ i) ≤ scfExAnteU μ B u f i

/-- **Section 23.E** (MWG, p. 894). If `f` satisfies (23.E.1) then it satisfies (23.E.2) (beliefs
are probability measures and the conditional expectations exist). -/
theorem interimParticipation_of_exPost [DecidableEq ι]
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} [∀ i θi, IsProbabilityMeasure (B i θi)]
    {u : (i : ι) → X → Θ i → ℝ} {ubar : (i : ι) → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hint : ∀ i (θi : Θ i), Integrable (fun θ => u i (f (update θ i θi)) θi) (B i θi))
    (h : ExPostParticipation u ubar f) : InterimParticipation B u ubar f := by
  intro i θi
  have hc : ∫ _θ, ubar i θi ∂(B i θi) = ubar i θi := by simp
  rw [← hc]
  refine integral_mono (integrable_const _) (hint i θi) fun θ => ?_
  have := h i (update θ i θi)
  simpa using this

/-- **Section 23.E** (MWG, p. 894). If `f` satisfies (23.E.2) then it satisfies (23.E.3) (the
outside options and interim utilities are integrable). -/
theorem exAnteParticipation_of_interim [DecidableEq ι] {μ : (i : ι) → Measure (Θ i)}
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {ubar : (i : ι) → Θ i → ℝ} {f : ((i : ι) → Θ i) → X}
    (hub : ∀ i, Integrable (ubar i) (μ i))
    (hU : ∀ i, Integrable (scfInterimU B u f i) (μ i))
    (h : InterimParticipation B u ubar f) : ExAnteParticipation μ B u ubar f :=
  fun i => integral_mono (hub i) (hU i) fun θi => h i θi

/-! ### "The reverse is not true" (p. 894) -/

/-- Independent uniform beliefs on `Bool` for two agents: the other agent's type is `true` or
`false` with probability `1/2` (agent `i`'s own coordinate is replaced by his type). -/
noncomputable def partUnifBelief : Measure (Fin 2 → Bool) :=
  (1 / 2 : ENNReal) • (Measure.dirac (fun _ => true) + Measure.dirac (fun _ => false))

/-- The beliefs `partUnifBelief` are a probability measure. -/
theorem partUnifBelief_isProb : IsProbabilityMeasure partUnifBelief := by
  constructor
  simp only [partUnifBelief, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Expectations under `partUnifBelief`. -/
theorem part_integral_unif (g : (Fin 2 → Bool) → ℝ) :
    ∫ θ, g θ ∂partUnifBelief = (g (fun _ => true) + g (fun _ => false)) / 2 := by
  rw [partUnifBelief, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite), integral_dirac,
    integral_dirac]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- **Section 23.E** (MWG, p. 894), interim does not imply ex post. Two agents with types in
`Bool`, independent uniform beliefs, utility `uᵢ(x, θᵢ) = x`, outside option `0`, and
`f(θ) = 1` if the types agree, `-1/2` if not: every type's interim utility is `1/4 ≥ 0`, but
(23.E.1) fails at a profile of disagreeing types. -/
theorem participation_interim_not_exPost :
    let f : (Fin 2 → Bool) → ℝ := fun θ => if θ 0 = θ 1 then 1 else -1 / 2
    InterimParticipation (Θ := fun _ : Fin 2 => Bool) (fun _ _ => partUnifBelief)
        (fun _ x _ => x) (fun _ _ => 0) f ∧
      ¬ ExPostParticipation (Θ := fun _ : Fin 2 => Bool) (fun _ x _ => x) (fun _ _ => 0) f := by
  intro f
  refine ⟨fun i θi => ?_, fun h => ?_⟩
  · simp only [scfInterimU, part_integral_unif, f]
    fin_cases i <;> cases θi <;> simp [update] <;> norm_num
  · have := h 0 ![true, false]
    norm_num [f] at this

/-- **Section 23.E** (MWG, p. 894), ex ante does not imply interim. Same setting with
`f(θ) = 2` if agent `0`'s type is `true` and `-1` otherwise, and types uniform on `Bool`: each
agent's ex ante utility is `1/2 ≥ 0`, but agent `0` of type `false` has interim utility `-1`. -/
theorem participation_exAnte_not_interim :
    let f : (Fin 2 → Bool) → ℝ := fun θ => if θ 0 then 2 else -1
    let μ : Measure Bool :=
      (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)
    ExAnteParticipation (Θ := fun _ : Fin 2 => Bool) (fun _ => μ) (fun _ _ => partUnifBelief)
        (fun _ x _ => x) (fun _ _ => 0) f ∧
      ¬ InterimParticipation (Θ := fun _ : Fin 2 => Bool) (fun _ _ => partUnifBelief)
        (fun _ x _ => x) (fun _ _ => 0) f := by
  intro f μ
  have hμ : ∀ g : Bool → ℝ, ∫ b, g b ∂μ = (g true + g false) / 2 := by
    intro g
    simp only [μ]
    rw [integral_smul_measure, integral_add_measure (Integrable.of_finite)
      (Integrable.of_finite), integral_dirac, integral_dirac]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  refine ⟨fun i => ?_, fun h => ?_⟩
  · simp only [scfExAnteU, scfInterimU, hμ, part_integral_unif, f]
    fin_cases i <;> simp [update] <;> norm_num
  · have := h 0 false
    simp only [scfInterimU, part_integral_unif, f] at this
    norm_num [update] at this

/-! ### Example 23.E.1 -/

/-- **Example 23.E.1** (MWG, p. 892). The valuation `θ̄` of type `true` and `θ̲` of type
`false`. -/
def partVal (lo hi : ℝ) (b : Bool) : ℝ := if b then hi else lo

/-- **Example 23.E.1** (MWG, p. 892). The project rule `k*(θ₁, θ₂) = 1` iff some `θᵢ = θ̄`. -/
def partK (θ : Fin 2 → Bool) : Bool := θ 0 || θ 1

/-- **Example 23.E.1** (MWG, p. 892). Agent `i`'s valuation `θᵢ k` of the project decision
`k ∈ {0, 1}` (`true` = do the project). -/
def partV (lo hi : ℝ) : Fin 2 → Bool → Bool → ℝ :=
  fun _ k b => if k then partVal lo hi b else 0

/-- **Example 23.E.1** (MWG, p. 892). The social choice function `(k*(θ), t(θ))`. -/
def partF (t : (Fin 2 → Bool) → Fin 2 → ℝ) (θ : Fin 2 → Bool) : Bool × (Fin 2 → ℝ) :=
  (partK θ, t θ)

/-- **Example 23.E.1** (MWG, p. 892). Feasibility with the cost: `t₁(θ) + t₂(θ) ≤ -c k(θ)`. -/
def PartFeasible (c : ℝ) (t : (Fin 2 → Bool) → Fin 2 → ℝ) : Prop :=
  ∀ θ, ∑ i, t θ i ≤ -(c * if partK θ then 1 else 0)

/-- **Example 23.E.1** (MWG, p. 892). With `θ̄ > 2θ̲ > 0` and `c ∈ (2θ̲, θ̄)`, `k*` is the ex post
efficient project rule: `k*(θ) = 1` iff `θ₁ + θ₂ ≥ c`. -/
theorem example_23_E_1_efficient {lo hi c : ℝ} (h0 : 0 < lo) (hc1 : 2 * lo < c)
    (hc2 : c < hi) (θ : Fin 2 → Bool) :
    partK θ = true ↔ c ≤ partVal lo hi (θ 0) + partVal lo hi (θ 1) := by
  cases h0' : θ 0 <;> cases h1' : θ 1 <;> simp [partK, partVal, h0', h1'] <;> linarith

/-- **Example 23.E.1** (MWG, p. 892). With `θ̄ > 2θ̲ > 0` and `c ∈ (2θ̲, θ̄)`, no social choice
function with the efficient project rule `k*` is strategy-proof, ex post individually rational
when withdrawal gives `0` (23.E.1), and feasible (`∑ tᵢ ≤ -ck`). -/
theorem example_23_E_1 {lo hi c : ℝ} (hc1 : 2 * lo < c)
    (t : (Fin 2 → Bool) → Fin 2 → ℝ) :
    ¬ (StrategyProof (qlU (partV lo hi) 0) (partF t) ∧
      ExPostParticipation (qlU (partV lo hi) 0) (fun _ _ => 0) (partF t) ∧
      PartFeasible c t) := by
  rintro ⟨hsp, hir, hfe⟩
  have s0 := hsp 0 (fun _ => true) false
  have s1 := hsp 1 (fun _ => true) false
  have r0 := hir 0 (update (fun _ => true) 0 false)
  have r1 := hir 1 (update (fun _ => true) 1 false)
  have fe := hfe (fun _ => true)
  simp [qlU, partV, partVal, partF, partK, update, Fin.sum_univ_two] at s0 s1 r0 r1 fe
  linarith

/-- **Example 23.E.1** (MWG, pp. 892-893), outside agent. Agents `1, 2` as before and an outside
agent `0` who does not care about the project; his participation requires `t₀ ≥ 0`. Still no
strategy-proof, ex post individually rational, feasible social choice function with the efficient
project rule exists. -/
theorem example_23_E_1_outside {lo hi c : ℝ} (hc1 : 2 * lo < c)
    (t : (Fin 3 → Bool) → Fin 3 → ℝ) :
    let v : Fin 3 → Bool → Bool → ℝ :=
      fun i k b => if i = 0 then 0 else if k then partVal lo hi b else 0
    let k : (Fin 3 → Bool) → Bool := fun θ => θ 1 || θ 2
    ¬ (StrategyProof (qlU v 0) (fun θ => (k θ, t θ)) ∧
      ExPostParticipation (qlU v 0) (fun _ _ => 0) (fun θ => (k θ, t θ)) ∧
      ∀ θ, ∑ i, t θ i ≤ -(c * if k θ then 1 else 0)) := by
  intro v k
  rintro ⟨hsp, hir, hfe⟩
  have s1 := hsp 1 (fun _ => true) false
  have s2 := hsp 2 (fun _ => true) false
  have r0 := hir 0 (fun _ => true)
  have r1 := hir 1 (update (fun _ => true) 1 false)
  have r2 := hir 2 (update (fun _ => true) 2 false)
  have fe := hfe (fun _ => true)
  simp [qlU, v, k, partVal, update, Fin.sum_univ_three] at s1 s2 r0 r1 r2 fe
  linarith

/-- Profiles of two Boolean types are vectors `![a, b]`. -/
theorem part_vec2 (θ : Fin 2 → Bool) : θ = ![θ 0, θ 1] := by
  ext j; fin_cases j <;> rfl

/-- **Example 23.E.1** (MWG, p. 892), non-vacuity. Strategy-proofness and ex post individual
rationality together are satisfiable: `tᵢ = -θ̲ k*` (each agent pays `θ̲` if the project is
done); this rule is not feasible. -/
theorem example_23_E_1_sp_ir {lo hi c : ℝ} (h0 : 0 < lo) (h1 : 2 * lo < hi) (hc1 : 2 * lo < c) :
    let t : (Fin 2 → Bool) → Fin 2 → ℝ := fun θ _ => if partK θ then -lo else 0
    StrategyProof (qlU (partV lo hi) 0) (partF t) ∧
      ExPostParticipation (qlU (partV lo hi) 0) (fun _ _ => 0) (partF t) ∧
      ¬ PartFeasible c t := by
  intro t
  refine ⟨fun i θ θh => ?_, fun i θ => ?_, fun h => ?_⟩
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> cases θh <;> fin_cases i <;>
      simp [qlU, partV, partVal, partF, partK, t, update] <;> linarith
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> fin_cases i <;>
      simp [qlU, partV, partVal, partF, partK, t] <;> linarith
  · have := h (fun _ => true)
    simp [partK, t] at this
    linarith

/-- **Example 23.E.1** (MWG, p. 892), non-vacuity. Strategy-proofness and feasibility together are
satisfiable: `tᵢ = -c k*`; this rule is not ex post individually rational. -/
theorem example_23_E_1_sp_feasible {lo hi c : ℝ} (h0 : 0 < lo) (hc1 : 2 * lo < c)
    (hc2 : c < hi) :
    let t : (Fin 2 → Bool) → Fin 2 → ℝ := fun θ _ => if partK θ then -c else 0
    StrategyProof (qlU (partV lo hi) 0) (partF t) ∧ PartFeasible c t ∧
      ¬ ExPostParticipation (qlU (partV lo hi) 0) (fun _ _ => 0) (partF t) := by
  intro t
  refine ⟨fun i θ θh => ?_, fun θ => ?_, fun h => ?_⟩
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> cases θh <;> fin_cases i <;>
      simp [qlU, partV, partVal, partF, partK, t, update] <;> linarith
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> simp [partK, t] <;> linarith
  · have := h 0 ![false, true]
    simp [qlU, partV, partVal, partF, partK, t] at this
    linarith

/-- **Example 23.E.1** (MWG, p. 892), non-vacuity. Ex post individual rationality and feasibility
together are satisfiable: the high-valuation agents share the cost equally (`c/2` each if both,
`c` if one); this rule is not strategy-proof. -/
theorem example_23_E_1_ir_feasible {lo hi c : ℝ} (h0 : 0 < lo) (hc1 : 2 * lo < c)
    (hc2 : c < hi) :
    let t : (Fin 2 → Bool) → Fin 2 → ℝ :=
      fun θ i => if θ i then (if θ 0 && θ 1 then -(c / 2) else -c) else 0
    ExPostParticipation (qlU (partV lo hi) 0) (fun _ _ => 0) (partF t) ∧ PartFeasible c t ∧
      ¬ StrategyProof (qlU (partV lo hi) 0) (partF t) := by
  intro t
  refine ⟨fun i θ => ?_, fun θ => ?_, fun h => ?_⟩
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> fin_cases i <;>
      simp [qlU, partV, partVal, partF, partK, t] <;> linarith
  · rw [part_vec2 θ]
    cases θ 0 <;> cases θ 1 <;> simp [partK, t, Fin.sum_univ_two]
  · have := h 0 ![true, true] false
    simp [qlU, partV, partVal, partF, partK, t, update] at this
    linarith

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Welfare criteria with incomplete information

MWG, Section 23.F, pp. 897-900, and Exercise 23.F.1 (p. 923).

* **(23.F.1)-(23.F.2)**: `F_BIC`, the three `F_IR` sets (ex post, interim, ex ante participation),
  and the incentive feasible set `F* = F_BIC ∩ F_IR`.
* **Definitions 23.F.1-23.F.3**: ex ante, interim and ex post efficiency in a set `F` of social
  choice functions (interim utilities `Uᵢ(θᵢ | f)` as in `Participation.lean`, ex ante utilities
  `Uᵢ(f) = E[Uᵢ(θᵢ | f)]` under marginals `μᵢ`).
* **Proposition 23.F.1** (ex ante efficient ⇒ interim efficient) is **false as printed** when some
  types have probability zero: a strict interim improvement for a null type does not raise ex
  ante utility (`proposition_23_F_1_false`: one agent, `θ` uniform on `[0, 1]`, `u = x`,
  `F = {0, 1{θ = 1/2}}`). **Corrected**: an ex ante efficient `f` has no interim improvement
  that is strict on a set of types of positive probability (`proposition_23_F_1`); in particular,
  if every type has positive probability, ex ante efficiency implies interim efficiency
  (`proposition_23_F_1_pointMass`).
* p. 900: ex post efficiency (Definition 23.B.2) ⇔ ex post efficiency in the set of all social
  choice functions (Definition 23.F.3) (`exPostEfficientIn_univ_iff`).
* **Exercise 23.F.1**: in the quasilinear setting with independent types, an `f ∈ F*` that is
  ex post classically efficient in `F_IR` is ex ante incentive efficient, and interim incentive
  efficient when every type has positive probability. We prove it for finite type spaces (so all
  expectations exist) and for any `F_IR` that is closed under ex post (weak) improvements, which
  the ex post and interim participation sets are (`exPostParticipation_upClosed`,
  `interimParticipation_upClosed`). The interim conclusion needs positive probabilities by the
  same counterexample as Proposition 23.F.1.
-/

namespace MWG.MechanismDesign

open Function MeasureTheory

variable {ι : Type*} {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)] {X : Type*}

/-- **(23.F.1)** (MWG, p. 898). The Bayesian incentive compatible social choice functions,
`F_BIC = {f : Θ → X : f is Bayesian incentive compatible}`. -/
def fBIC [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) : Set (((i : ι) → Θ i) → X) :=
  {f | BayesianIC B u f}

/-- **(23.F.2)** (MWG, p. 898). `F_IR` with ex post participation constraints (23.E.1). -/
def fIRExPost (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ) :
    Set (((i : ι) → Θ i) → X) :=
  {f | ExPostParticipation u ubar f}

/-- **(23.F.2)** (MWG, p. 898). `F_IR` with interim participation constraints (23.E.2). -/
def fIRInterim [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ) : Set (((i : ι) → Θ i) → X) :=
  {f | InterimParticipation B u ubar f}

/-- **(23.F.2)** (MWG, p. 898). `F_IR` with ex ante participation constraints (23.E.3). -/
def fIRExAnte [DecidableEq ι] (μ : (i : ι) → Measure (Θ i))
    (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)) (u : (i : ι) → X → Θ i → ℝ)
    (ubar : (i : ι) → Θ i → ℝ) : Set (((i : ι) → Θ i) → X) :=
  {f | ExAnteParticipation μ B u ubar f}

/-- **Section 23.F** (MWG, p. 898). The incentive feasible set `F* = F_BIC ∩ F_IR` (with
`F_IR = {f : Θ → X}` when participation is not voluntary). -/
def incentiveFeasible [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (FIR : Set (((i : ι) → Θ i) → X)) :
    Set (((i : ι) → Θ i) → X) :=
  fBIC B u ∩ FIR

/-- **Section 23.F** (MWG, p. 900). `F* ⊆ F_IR`. -/
theorem incentiveFeasible_subset [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (FIR : Set (((i : ι) → Θ i) → X)) :
    incentiveFeasible B u FIR ⊆ FIR :=
  Set.inter_subset_right

/-- **Definition 23.F.1** (MWG, p. 898). `f ∈ F` is ex ante efficient in `F`: no `f̂ ∈ F` has
`Uᵢ(f̂) ≥ Uᵢ(f)` for all `i` and `Uᵢ(f̂) > Uᵢ(f)` for some `i`. -/
def ExAnteEfficientIn [DecidableEq ι] (μ : (i : ι) → Measure (Θ i))
    (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)) (u : (i : ι) → X → Θ i → ℝ)
    (F : Set (((i : ι) → Θ i) → X)) (f : ((i : ι) → Θ i) → X) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, (∀ i, scfExAnteU μ B u f i ≤ scfExAnteU μ B u g i) ∧
    ∃ i, scfExAnteU μ B u f i < scfExAnteU μ B u g i

/-- **Definition 23.F.2** (MWG, p. 898). `f ∈ F` is interim efficient in `F`: no `f̂ ∈ F` has
`Uᵢ(θᵢ | f̂) ≥ Uᵢ(θᵢ | f)` for all `i`, `θᵢ`, and `>` for some `i` and `θᵢ`. -/
def InterimEfficientIn [DecidableEq ι] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (F : Set (((i : ι) → Θ i) → X)) (f : ((i : ι) → Θ i) → X) :
    Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, (∀ i θi, scfInterimU B u f i θi ≤ scfInterimU B u g i θi) ∧
    ∃ i θi, scfInterimU B u f i θi < scfInterimU B u g i θi

/-- **Definition 23.F.3** (MWG, p. 900). `f ∈ F` is ex post efficient in `F`: no `f̂ ∈ F` has
`uᵢ(f̂(θ), θᵢ) ≥ uᵢ(f(θ), θᵢ)` for all `i`, `θ`, and `>` for some `i` and `θ`. -/
def ExPostEfficientIn (u : (i : ι) → X → Θ i → ℝ) (F : Set (((i : ι) → Θ i) → X))
    (f : ((i : ι) → Θ i) → X) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, (∀ i θ, u i (f θ) (θ i) ≤ u i (g θ) (θ i)) ∧
    ∃ i θ, u i (f θ) (θ i) < u i (g θ) (θ i)

omit [∀ i, MeasurableSpace (Θ i)] in
/-- **Section 23.F** (MWG, p. 900). A social choice function is ex post efficient in the sense of
Definition 23.B.2 iff it is ex post efficient in the sense of Definition 23.F.3 with
`F = {f : Θ → X}`. -/
theorem exPostEfficientIn_univ_iff (u : (i : ι) → X → Θ i → ℝ) (f : ((i : ι) → Θ i) → X) :
    ExPostEfficientIn u Set.univ f ↔ ExPostEfficient u f := by
  classical
  constructor
  · rintro ⟨-, hne⟩ ⟨θ0, x, hx, i, hi⟩
    refine hne ⟨update f θ0 x, Set.mem_univ _, fun j θ => ?_, i, θ0, by simpa using hi⟩
    by_cases h : θ = θ0
    · subst h; simpa using hx j
    · simp [update_of_ne h]
  · rintro h
    refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨g, -, hg, i, θ, hi⟩
    exact h ⟨θ, g θ, fun j => hg j θ, i, hi⟩

/-! ### Proposition 23.F.1 -/

/-- **Proposition 23.F.1** (MWG, p. 899), corrected. If `f` is ex ante efficient in `F` and
`g ∈ F` makes every type of every agent weakly better off, then for every agent the set of types
made strictly better off has probability zero (interim utilities of members of `F` are
`μᵢ`-integrable). MWG's proof needs exactly this: a strict improvement for a set of types of
positive probability raises ex ante utility. -/
theorem proposition_23_F_1 [DecidableEq ι] {μ : (i : ι) → Measure (Θ i)}
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {F : Set (((i : ι) → Θ i) → X)}
    (hint : ∀ g ∈ F, ∀ i, Integrable (scfInterimU B u g i) (μ i))
    {f : ((i : ι) → Θ i) → X} (hf : ExAnteEfficientIn μ B u F f) {g : ((i : ι) → Θ i) → X}
    (hg : g ∈ F) (hdom : ∀ i θi, scfInterimU B u f i θi ≤ scfInterimU B u g i θi) (i : ι) :
    μ i {θi | scfInterimU B u f i θi < scfInterimU B u g i θi} = 0 := by
  obtain ⟨hfF, hne⟩ := hf
  by_contra hpos
  apply hne
  refine ⟨g, hg, fun j => integral_mono (hint f hfF j) (hint g hg j) (hdom j), i, ?_⟩
  have hnn : 0 ≤ fun θi => scfInterimU B u g i θi - scfInterimU B u f i θi :=
    fun θi => sub_nonneg.2 (hdom i θi)
  have hI := (integral_pos_iff_support_of_nonneg hnn ((hint g hg i).sub (hint f hfF i))).2 (by
    have hs : Function.support (fun θi => scfInterimU B u g i θi - scfInterimU B u f i θi) =
        {θi | scfInterimU B u f i θi < scfInterimU B u g i θi} := by
      ext θi
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact ⟨fun h => lt_of_le_of_ne (hdom i θi) (Ne.symm h), fun h => (ne_of_lt h).symm⟩
    rw [hs]
    exact pos_iff_ne_zero.2 hpos)
  rw [integral_sub (hint g hg i) (hint f hfF i), sub_pos] at hI
  exact hI

/-- **Proposition 23.F.1** (MWG, p. 899), corrected: if every type of every agent has positive
probability (e.g. countably many types with positive point masses), ex ante efficiency in `F`
implies interim efficiency in `F`. -/
theorem proposition_23_F_1_pointMass [DecidableEq ι] {μ : (i : ι) → Measure (Θ i)}
    {B : (i : ι) → Θ i → Measure ((j : ι) → Θ j)} {u : (i : ι) → X → Θ i → ℝ}
    {F : Set (((i : ι) → Θ i) → X)}
    (hint : ∀ g ∈ F, ∀ i, Integrable (scfInterimU B u g i) (μ i))
    (hpos : ∀ i (θi : Θ i), 0 < μ i {θi}) {f : ((i : ι) → Θ i) → X}
    (hf : ExAnteEfficientIn μ B u F f) : InterimEfficientIn B u F f := by
  refine ⟨hf.1, ?_⟩
  rintro ⟨g, hg, hdom, i, θi, hlt⟩
  have h0 := proposition_23_F_1 hint hf hg hdom i
  have h1 := measure_mono (μ := μ i) (show {θi} ⊆ {θ | scfInterimU B u f i θ <
    scfInterimU B u g i θ} from fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hlt)
  rw [h0] at h1
  exact (hpos i θi).ne' (nonpos_iff_eq_zero.1 h1)

/-- The social choice function `1{θ = 1/2}` of the counterexample to Proposition 23.F.1. -/
noncomputable def wcSpike : (Unit → ℝ) → ℝ := fun θ => if θ () = 1 / 2 then 1 else 0

/-- **Proposition 23.F.1** (MWG, p. 899) is false as printed. One agent with type `θ` uniform on
`[0, 1]` and utility `u(x, θ) = x`, `F = {f ≡ 0, f̂ = 1{θ = 1/2}}`: `f` is ex ante efficient in
`F` (`f̂` gives the same ex ante utility `0`) but not interim efficient (`f̂` is strictly better
for type `1/2`). -/
theorem proposition_23_F_1_false :
    ExAnteEfficientIn (Θ := fun _ : Unit => ℝ) (fun _ => uniform01.measure)
        (fun _ _ => Measure.dirac (fun _ => 0)) (fun _ x _ => x) {fun _ => 0, wcSpike}
        (fun _ => 0) ∧
      ¬ InterimEfficientIn (Θ := fun _ : Unit => ℝ) (fun _ _ => Measure.dirac (fun _ => 0))
        (fun _ x _ => x) {fun _ => 0, wcSpike} (fun _ => 0) := by
  have hI : ∀ θi : ℝ, scfInterimU (Θ := fun _ : Unit => ℝ)
      (fun _ _ => Measure.dirac (fun _ => 0)) (fun _ x _ => x) wcSpike () θi =
        if θi = 1 / 2 then 1 else 0 := by
    intro θi
    simp [scfInterimU, wcSpike]
  have hI0 : ∀ θi : ℝ, scfInterimU (Θ := fun _ : Unit => ℝ)
      (fun _ _ => Measure.dirac (fun _ => 0)) (fun _ x _ => x) (fun _ => (0 : ℝ)) () θi = 0 := by
    intro θi
    simp [scfInterimU]
  have hA : scfExAnteU (Θ := fun _ : Unit => ℝ) (fun _ => uniform01.measure)
      (fun _ _ => Measure.dirac (fun _ => 0)) (fun _ x _ => x) wcSpike () = 0 := by
    rw [scfExAnteU]
    simp_rw [hI]
    refine integral_eq_zero_of_ae ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) (uniform01.measure_singleton (1 / 2))
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hx
    exact hx
  have hA0 : scfExAnteU (Θ := fun _ : Unit => ℝ) (fun _ => uniform01.measure)
      (fun _ _ => Measure.dirac (fun _ => 0)) (fun _ x _ => x) (fun _ => (0 : ℝ)) () = 0 := by
    rw [scfExAnteU]
    simp_rw [hI0]
    simp
  refine ⟨⟨Set.mem_insert _ _, ?_⟩, ?_⟩
  · rintro ⟨g, hg, -, i, hi⟩
    rcases hg with rfl | hg
    · exact lt_irrefl _ hi
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [hA, hA0] at hi
      exact lt_irrefl _ hi
  · rintro ⟨-, hne⟩
    refine hne ⟨wcSpike, by simp, fun i θi => ?_, (), 1 / 2, ?_⟩
    · rw [hI0, hI]
      split_ifs <;> norm_num
    · rw [hI0, hI]
      norm_num

/-! ### Exercise 23.F.1 -/

/-- `F_IR` is closed under ex post (weak) improvements: if `f ∈ F_IR` and `g` gives every agent
at least `f`'s utility at every profile, then `g ∈ F_IR`. -/
def UpClosed (u : (i : ι) → X → Θ i → ℝ) (FIR : Set (((i : ι) → Θ i) → X)) : Prop :=
  ∀ f ∈ FIR, ∀ g : ((i : ι) → Θ i) → X, (∀ i θ, u i (f θ) (θ i) ≤ u i (g θ) (θ i)) → g ∈ FIR

omit [∀ i, MeasurableSpace (Θ i)] in
/-- The ex post participation set (23.E.1) is closed under ex post improvements. -/
theorem exPostParticipation_upClosed (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ) :
    UpClosed u (fIRExPost u ubar) :=
  fun _ hf _ hg i θ => (hf i θ).trans (hg i θ)

/-- With finite type spaces, the interim participation set (23.E.2) is closed under ex post
improvements. -/
theorem interimParticipation_upClosed [DecidableEq ι] [Finite ((j : ι) → Θ j)]
    [MeasurableSingletonClass ((j : ι) → Θ j)] (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    [∀ i θi, IsFiniteMeasure (B i θi)] (u : (i : ι) → X → Θ i → ℝ) (ubar : (i : ι) → Θ i → ℝ) :
    UpClosed u (fIRInterim B u ubar) := by
  intro f hf g hg i θi
  refine (hf i θi).trans (integral_mono Integrable.of_finite Integrable.of_finite fun θ => ?_)
  have := hg i (update θ i θi)
  simpa using this

variable [Fintype ι] [DecidableEq ι] [∀ i, Finite (Θ i)] [∀ i, MeasurableSingletonClass (Θ i)]
  {K : Type*}

omit [∀ i, MeasurableSingletonClass (Θ i)] in
/-- With independent types, the ex ante utility is the expectation of the ex post utility:
`Uᵢ(f) = E_θ[uᵢ(f(θ), θᵢ)]` (MWG, p. 893). -/
theorem wc_exAnteU_eq [∀ i, MeasurableSingletonClass (Θ i)] (μ : (i : ι) → Measure (Θ i))
    [∀ i, IsProbabilityMeasure (μ i)] (u : (i : ι) → X → Θ i → ℝ)
    (f : ((i : ι) → Θ i) → X) (i : ι) :
    scfExAnteU μ (indepBeliefs (Measure.pi μ)) u f i = ∫ θ, u i (f θ) (θ i) ∂Measure.pi μ := by
  have h := integral_integral_update μ i (g := fun θ => u i (f θ) (θ i)) Integrable.of_finite
  have h2 := integral_eval_pi μ i (F := fun a => ∫ θ', u i (f (update θ' i a)) a ∂Measure.pi μ)
    (measurable_of_finite _).aestronglyMeasurable
  simp only [update_self] at h
  rw [scfExAnteU]
  simp only [scfInterimU, indepBeliefs]
  rw [← h2, h]

omit [∀ i, MeasurableSpace (Θ i)] [DecidableEq ι] [∀ i, Finite (Θ i)]
  [∀ i, MeasurableSingletonClass (Θ i)] in
/-- **Exercise 23.F.1** (MWG, p. 923), key step. In the quasilinear setting, if `f` is ex post
efficient in an `F_IR` closed under ex post improvements, then every feasible `g` has total
utility `∑ᵢ uᵢ(g(θ), θᵢ) ≤ ∑ᵢ uᵢ(f(θ), θᵢ)` at every profile. -/
theorem wc_sum_le_of_exPostEfficientIn [Nonempty ι] {v : (i : ι) → K → Θ i → ℝ} {m : ι → ℝ}
    {FIR : Set (((i : ι) → Θ i) → QLAlt ι K)}
    (hup : UpClosed (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    {f : ((i : ι) → Θ i) → QLAlt ι K}
    (hf : ExPostEfficientIn (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR f)
    (g : ((i : ι) → Θ i) → QLAlt ι K) (θ : (i : ι) → Θ i) :
    ∑ i, qlU v m i (g θ).1 (θ i) ≤ ∑ i, qlU v m i (f θ).1 (θ i) := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set S := ∑ i, qlU v m i (g θ).1 (θ i) - ∑ i, qlU v m i (f θ).1 (θ i) with hS
  have hSpos : 0 < S := by rw [hS]; linarith
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : 0 < S / Fintype.card ι := div_pos hSpos hI
  let t' : ι → ℝ := fun i => (f θ).1.2 i + v i (f θ).1.1 (θ i) - v i (g θ).1.1 (θ i) +
    S / Fintype.card ι
  have hfeas : ∑ i, t' i ≤ 0 := by
    have : ∑ i, t' i = ∑ i, (g θ).1.2 i := by
      simp only [t', Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hI.ne', hS]
      simp only [qlU, Finset.sum_add_distrib]
      ring
    rw [this]; exact (g θ).2
  let x : QLAlt ι K := ⟨((g θ).1.1, t'), hfeas⟩
  have hx : ∀ i, qlU v m i x.1 (θ i) = qlU v m i (f θ).1 (θ i) + S / Fintype.card ι := by
    intro i; simp only [qlU, x, t']; ring
  have hle : ∀ i θ', qlU v m i (f θ').1 (θ' i) ≤ qlU v m i (update f θ x θ').1 (θ' i) := by
    intro i θ'
    by_cases h : θ' = θ
    · subst h; rw [update_self, hx]; linarith
    · rw [update_of_ne h]
  refine hf.2 ⟨update f θ x, hup f hf.1 _ hle, hle, Classical.arbitrary ι, θ, ?_⟩
  simp only [update_self]
  rw [hx]
  linarith

/-- **Exercise 23.F.1** (MWG, p. 923), ex ante part. Quasilinear setting, independent types with
finitely many values: if `f ∈ F*` is ex post classically efficient in `F_IR` (and `F_IR` is closed
under ex post improvements), then `f` is ex ante incentive efficient (ex ante efficient in
`F*`). -/
theorem exercise_23_F_1_exAnte [Nonempty ι] (μ : (i : ι) → Measure (Θ i))
    [∀ i, IsProbabilityMeasure (μ i)] {v : (i : ι) → K → Θ i → ℝ} {m : ι → ℝ}
    {FIR : Set (((i : ι) → Θ i) → QLAlt ι K)}
    (hup : UpClosed (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    {f : ((i : ι) → Θ i) → QLAlt ι K}
    (hfF : f ∈ incentiveFeasible (indepBeliefs (Measure.pi μ))
      (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    (hf : ExPostEfficientIn (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR f) :
    ExAnteEfficientIn μ (indepBeliefs (Measure.pi μ)) (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi)
      (incentiveFeasible (indepBeliefs (Measure.pi μ))
        (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR) f := by
  refine ⟨hfF, ?_⟩
  rintro ⟨g, -, hge, i, hi⟩
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hge j) ⟨i, Finset.mem_univ i, hi⟩
  simp only [wc_exAnteU_eq] at hsum
  rw [← integral_finsetSum _ fun j _ => Integrable.of_finite,
    ← integral_finsetSum _ fun j _ => Integrable.of_finite] at hsum
  have hle := integral_mono (μ := Measure.pi μ) Integrable.of_finite Integrable.of_finite
    fun θ => wc_sum_le_of_exPostEfficientIn hup hf g θ
  exact absurd hsum (not_lt.2 hle)

/-- **Exercise 23.F.1** (MWG, p. 923), interim part. In the same setting, if every type has
positive probability, `f` is also interim incentive efficient (interim efficient in `F*`). Without
positive probabilities this can fail, as for Proposition 23.F.1. -/
theorem exercise_23_F_1_interim [Nonempty ι] (μ : (i : ι) → Measure (Θ i))
    [∀ i, IsProbabilityMeasure (μ i)] (hpos : ∀ i (θi : Θ i), 0 < μ i {θi})
    {v : (i : ι) → K → Θ i → ℝ} {m : ι → ℝ} {FIR : Set (((i : ι) → Θ i) → QLAlt ι K)}
    (hup : UpClosed (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    {f : ((i : ι) → Θ i) → QLAlt ι K}
    (hfF : f ∈ incentiveFeasible (indepBeliefs (Measure.pi μ))
      (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    (hf : ExPostEfficientIn (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR f) :
    InterimEfficientIn (indepBeliefs (Measure.pi μ)) (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi)
      (incentiveFeasible (indepBeliefs (Measure.pi μ))
        (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR) f :=
  proposition_23_F_1_pointMass (fun _ _ _ => Integrable.of_finite) hpos
    (exercise_23_F_1_exAnte μ hup hfF hf)

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Optimal auctions

MWG, Section 23.F, Example 23.F.2 (pp. 903-905), and Exercises 23.F.3, 23.F.4 (p. 923).

`I` buyers with linear utilities `θᵢyᵢ + tᵢ`, independent types with densities `φᵢ > 0` on
`[θ̲ᵢ, θ̄ᵢ]` (`TypeDensity`), virtual valuations `Jᵢ(θᵢ) = θᵢ - (1 - Φᵢ(θᵢ))/φᵢ(θᵢ)`. A social
choice function is `(y, t)`; the seller's expected revenue is `∑ᵢ E[-tᵢ(θ)]` (no waste,
footnote 51).

* `OptAuctionFeasible`: `y(θ)` a feasible allocation on `Θ` (constraint (ii)), Bayesian incentive
  compatible, interim individually rational, with the expectations existing.
* **Example 23.F.2** (`example_23_F_2`): if `(y*, t*)` is feasible in this sense, has
  `Uᵢ(θ̲ᵢ) = 0`, and `y*(θ)` maximises `∑ᵢ yᵢJᵢ(θᵢ)` over feasible allocations at every `θ ∈ Θ`
  (the relaxed problem (23.F.8)), it maximises expected revenue among all feasible `(y, t)`. The
  proof is (23.F.7)-(23.F.8) via (23.D.16) (`eq_23_D_16`), and (iv) ⇔ (iv') (`eq_23_F_iv_iff`).
* (23.F.9): a pointwise maximiser gives the good to `i` when `Jᵢ > max{0, max_{k≠i} Jₖ}` and not
  when `Jᵢ < max{0, max_{k≠i} Jₖ}` (`eq_23_F_9`); conversely without ties these conditions give a
  maximiser (`eq_23_F_9_converse`).
* Remark (1): with asymmetric bidders (uniform on `[0, 1]` and `[0, 2]`) the optimal auction can
  give the good to a bidder without the highest valuation (`example_23_F_2_remark1`).
* Remark (2): symmetric bidders with `J` nondecreasing and `J(θ̲) > 0`: giving the good to a
  highest-valuation bidder solves (23.F.8) (`example_23_F_2_remark2_pointwise`), so any feasible
  mechanism doing this with `U(θ̲) = 0` (first-price, second-price) is optimal
  (`example_23_F_2_remark2`).
* Remark (3): `I = 1`: the posted price `p*` with `J(p*) = 0` solves (23.F.8)
  (`example_23_F_2_remark3_pointwise`); the FOC of `p(1 - Φ(p))` is `1 - Φ(p) - pφ(p) = 0`
  (`example_23_F_2_remark3_foc`, at a continuity point of `φ`) and is equivalent to `J(p) = 0`.
  Instance: uniform on `[0, 1]`, posted price `1/2` is an optimal mechanism
  (`example_23_F_2_instance`).
* Exercise 23.F.3: with symmetric bidders a second-price auction with reserve `r`, `J(r) = 0`,
  solves (23.F.8) (`exercise_23_F_3`). Exercise 23.F.4: with seller valuation `θ₀`, the seller's
  expected payoff is `∑ᵢ E[yᵢ(Jᵢ - θ₀)] + θ₀ - ∑ᵢ Uᵢ(θ̲ᵢ)` and a pointwise maximiser of
  `∑ᵢ yᵢ(Jᵢ - θ₀)` is optimal; it gives the good to `i` iff `Jᵢ > max{θ₀, max_{k≠i} Jₖ}`
  (`exercise_23_F_4`, `exercise_23_F_4_rule`).

Departures: feasibility is required on `Θ` and the competing social choice functions are those
whose expectations exist (integrability is part of `OptAuctionFeasible`); MWG's ties
(`Jᵢ = max{…}`, probability zero) are left free, and optimality is stated for any pointwise
maximiser.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Example 23.F.2** (MWG, p. 904), constraint (ii): a feasible allocation `yᵢ ≥ 0`,
`∑ᵢ yᵢ ≤ 1` (so `yᵢ ∈ [0, 1]`; the seller keeps `y₀ = 1 - ∑ᵢ yᵢ`). -/
def FeasAlloc (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ 1

/-- The allocation `w` maximises `∑ᵢ wᵢJᵢ` over feasible allocations: it solves the relaxed
problem (23.F.8) at one profile, with `Jv i = Jᵢ(θᵢ)`. -/
def PointwiseOptAlloc (Jv w : ι → ℝ) : Prop :=
  FeasAlloc w ∧ ∀ w', FeasAlloc w' → ∑ i, w' i * Jv i ≤ ∑ i, w i * Jv i

/-- The seller's expected revenue `∑ᵢ E[-tᵢ(θ)]` (MWG, p. 904). -/
noncomputable def auctionRevenue (D : ι → TypeDensity) (t : (ι → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure)

/-- **Example 23.F.2** (MWG, p. 904). The social choice functions the seller may choose:
`y(θ)` is a feasible allocation for `θ ∈ Θ` (ii); `(y, t)` is Bayesian incentive compatible;
interim individually rational `Uᵢ(θᵢ) ≥ 0` (iv); and the expectations involved exist. -/
def OptAuctionFeasible (D : ι → TypeDensity) (y t : (ι → ℝ) → ι → ℝ) : Prop :=
  (∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) → FeasAlloc (y θ)) ∧
    InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    (∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure)) ∧
    (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) ∧
    ∀ i, ∀ x ∈ Set.Icc (D i).lo (D i).hi,
      0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i x

/-- **Example 23.F.2** (MWG, p. 904), (iv) ⇔ (iv'): for a Bayesian incentive compatible `(y, t)`,
`Uᵢ(θᵢ) ≥ 0` for all `θᵢ ∈ Θᵢ` iff `Uᵢ(θ̲ᵢ) ≥ 0` (since `Uᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ` and
`ȳᵢ ≥ 0`). -/
theorem eq_23_F_iv_iff (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hy0 : ∀ θ i, 0 ≤ y θ i) (i : ι) :
    (∀ x ∈ Set.Icc (D i).lo (D i).hi,
        0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i x) ↔
      0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  refine ⟨fun h => h _ ⟨le_rfl, (D i).lo_lt_hi.le⟩, fun h x hx => ?_⟩
  rw [((proposition_23_D_2 hint).1 hf i).2 x hx]
  have : 0 ≤ ∫ s in (D i).lo..x, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s :=
    intervalIntegral.integral_nonneg hx.1 fun s _ => integral_nonneg fun θ => hy0 _ _
  linarith

/-- **Example 23.F.2** (MWG, pp. 904-905). If `(y*, t*)` is feasible, leaves the lowest type of
every buyer with `Uᵢ(θ̲ᵢ) = 0`, and `y*(θ)` solves the relaxed problem (23.F.8) pointwise on `Θ`,
then `(y*, t*)` maximises the seller's expected revenue among all feasible social choice
functions. -/
theorem example_23_F_2 (D : ι → TypeDensity) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible D ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV ys ts i (D i).lo = 0)
    (hopt : ∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) →
      PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (ys θ))
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible D y t) :
    auctionRevenue D t ≤ auctionRevenue D ts := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hyF, hint, hbic, ht, hyJ, hIR⟩ := h
  obtain ⟨-, hint', hbic', ht', hyJ', -⟩ := hs
  rw [auctionRevenue, auctionRevenue, eq_23_D_16 D hint hbic ht hyJ,
    eq_23_D_16 D hint' hbic' ht' hyJ']
  simp only [hU0, Finset.sum_const_zero, sub_zero]
  have hU : 0 ≤ ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo :=
    Finset.sum_nonneg fun i _ => hIR i _ ⟨le_rfl, (D i).lo_lt_hi.le⟩
  have hle : ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) ≤
      ∑ i, ∫ θ, ys θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) := by
    rw [← integral_finsetSum _ fun i _ => hyJ i, ← integral_finsetSum _ fun i _ => hyJ' i]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => hyJ i)
      (integrable_finsetSum _ fun i _ => hyJ' i) ?_
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    have h1 := (hopt θ hθ).2 (y θ) (hyF θ hθ)
    simpa using h1
  linarith

/-! ### (23.F.9) -/

/-- `∑ₖ fₖ = fᵢ + ∑_{k ≠ i} fₖ`. -/
theorem oa_sum_split (f : ι → ℝ) (i : ι) :
    ∑ k, f k = f i + ∑ k ∈ Finset.univ.erase i, f k :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

omit [DecidableEq ι] in
/-- **(23.F.9)** (MWG, p. 905). A solution of the relaxed problem (23.F.8) at a profile has
`yᵢ = 1` if `Jᵢ > max{0, max_{k≠i} Jₖ}` and `yᵢ = 0` if `Jᵢ < max{0, max_{k≠i} Jₖ}`. -/
theorem eq_23_F_9 {Jv w : ι → ℝ} (h : PointwiseOptAlloc Jv w) (i : ι) :
    ((0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < 0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0) := by
  classical
  obtain ⟨⟨hw0, hw1⟩, hmax⟩ := h
  have hsw := oa_sum_split w i
  have hswJ := oa_sum_split (fun k => w k * Jv k) i
  refine ⟨fun ⟨hJ, hk⟩ => ?_, fun hcase => ?_⟩
  · by_contra hne
    set A := ∑ k ∈ Finset.univ.erase i, w k * Jv k
    set Wn := ∑ k ∈ Finset.univ.erase i, w k
    have hA : A ≤ Wn * Jv i := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk' =>
        mul_le_mul_of_nonneg_left (hk k (Finset.ne_of_mem_erase hk')).le (hw0 k)
    have hWn : 0 ≤ Wn := Finset.sum_nonneg fun k _ => hw0 k
    have hstrict : A + w i * Jv i < Jv i := by
      rcases lt_or_eq_of_le (show w i + Wn ≤ 1 by linarith) with hlt | heq
      · nlinarith
      · have hWpos : 0 < Wn := by
          rcases lt_or_eq_of_le hWn with h' | h'
          · exact h'
          · exact absurd (by linarith : w i = 1) hne
        obtain ⟨k, hkm, hkpos⟩ : ∃ k ∈ Finset.univ.erase i, 0 < w k := by
          by_contra hn
          push Not at hn
          have : Wn ≤ 0 := Finset.sum_nonpos hn
          linarith
        have hA' : A < Wn * Jv i := by
          rw [Finset.sum_mul]
          exact Finset.sum_lt_sum (fun k hk' =>
            mul_le_mul_of_nonneg_left (hk k (Finset.ne_of_mem_erase hk')).le (hw0 k))
            ⟨k, hkm, mul_lt_mul_of_pos_left (hk k (Finset.ne_of_mem_erase hkm)) hkpos⟩
        nlinarith
    have hw' : FeasAlloc (fun k => if k = i then (1 : ℝ) else 0) :=
      ⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have := hmax _ hw'
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    linarith
  · by_contra hne
    have hpos : 0 < w i := lt_of_le_of_ne (hw0 i) (Ne.symm hne)
    rcases hcase with hJ | ⟨k, hki, hk⟩
    · have hw' : FeasAlloc (fun l => w l - if l = i then w i else 0) := by
        refine ⟨fun l => ?_, ?_⟩
        · by_cases hl : l = i
          · subst hl; simp
          · simp [hl, hw0 l]
        · rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          linarith
      have := hmax _ hw'
      simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at this
      nlinarith
    · have hw' : FeasAlloc
          (fun l => w l + (if l = k then w i else 0) - if l = i then w i else 0) := by
        refine ⟨fun l => ?_, ?_⟩
        · by_cases hl : l = i
          · subst hl; simp [hki.symm]
          · by_cases hlk : l = k
            · subst hlk; simp [hl]; linarith [hw0 l]
            · simp [hl, hlk, hw0 l]
        · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          linarith
      have := hmax _ hw'
      simp only [sub_mul, add_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      nlinarith

omit [DecidableEq ι] in
/-- **(23.F.9)** (MWG, p. 905), converse. If there is no tie (`Jᵢ = max{0, max_{k≠i} Jₖ}` has
probability zero), any feasible allocation satisfying the two conditions of (23.F.9) solves the
relaxed problem (23.F.8). -/
theorem eq_23_F_9_converse {Jv w : ι → ℝ} (hw : FeasAlloc w)
    (h9 : ∀ i, ((0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < 0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0))
    (hnt : (∃ i, 0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) ∨ ∀ i, Jv i < 0) :
    PointwiseOptAlloc Jv w := by
  classical
  refine ⟨hw, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  rcases hnt with ⟨i, hJ, hk⟩ | hneg
  · have hwi := (h9 i).1 ⟨hJ, hk⟩
    have hwk : ∀ k ∈ Finset.univ.erase i, w k * Jv k = 0 := fun k hk' => by
      rw [(h9 k).2 (Or.inr ⟨i, (Finset.ne_of_mem_erase hk').symm,
        hk k (Finset.ne_of_mem_erase hk')⟩), zero_mul]
    rw [oa_sum_split (fun k => w k * Jv k) i, Finset.sum_eq_zero hwk, hwi]
    calc ∑ k, w' k * Jv k ≤ ∑ k, w' k * Jv i := Finset.sum_le_sum fun k _ => by
          by_cases hki : k = i
          · rw [hki]
          · exact mul_le_mul_of_nonneg_left (hk k hki).le (hw0' k)
      _ = (∑ k, w' k) * Jv i := by rw [Finset.sum_mul]
      _ ≤ 1 * Jv i := mul_le_mul_of_nonneg_right hw1' hJ.le
      _ = 1 * Jv i + 0 := by ring
  · have hw0 : ∀ k, w k = 0 := fun k => (h9 k).2 (Or.inl (hneg k))
    simp only [hw0, zero_mul, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0' k) (hneg k).le

/-! ### Remarks on p. 905 -/

/-- The uniform distribution on `[a, b]` has `Φ(x) = (x - a)/(b - a)` on `[a, b]`. -/
theorem oa_uniform_cdf {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (uniformDensity a b h).cdf x = (x - a) / (b - a) := by
  change ∫ s in a..x, (Set.Icc a b).indicator (fun _ => (b - a)⁻¹) s = (x - a) / (b - a)
  rw [intervalIntegral.integral_congr (g := fun _ => (b - a)⁻¹) fun s hs => by
    rw [Set.uIcc_of_le hx.1] at hs
    rw [Set.indicator_of_mem (show s ∈ Set.Icc a b from ⟨hs.1, hs.2.trans hx.2⟩)]]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The uniform distribution on `[a, b]` has virtual valuation `J(x) = 2x - b` on `[a, b]`. -/
theorem oa_uniform_virtualValue {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (uniformDensity a b h).virtualValue x = 2 * x - b := by
  have hd : (uniformDensity a b h).dens x = (b - a)⁻¹ := by
    change (Set.Icc a b).indicator (fun _ => (b - a)⁻¹) x = _
    exact Set.indicator_of_mem hx _
  have hba : b - a ≠ 0 := (sub_pos.2 h).ne'
  rw [TypeDensity.virtualValue, oa_uniform_cdf h hx, hd]
  field_simp
  ring

/-- **Example 23.F.2**, remark (1) (MWG, p. 905). With asymmetric bidders, uniform on `[0, 1]`
and on `[0, 2]` (`J₁(θ) = 2θ - 1`, `J₂(θ) = 2θ - 2`), at `θ = (9/10, 1)` every solution of the
relaxed problem gives the good to bidder `1` although bidder `2` has the higher valuation: the
optimal auction is not ex post (classically) efficient. -/
theorem example_23_F_2_remark1 (w : Fin 2 → ℝ)
    (hw : PointwiseOptAlloc (fun i => (![uniformDensity 0 1 zero_lt_one,
      uniformDensity 0 2 zero_lt_two] i).virtualValue (![9 / 10, 1] i)) w) :
    w 0 = 1 ∧ w 1 = 0 ∧ (![9 / 10, 1] : Fin 2 → ℝ) 0 < ![9 / 10, 1] 1 := by
  have h0 : (uniformDensity 0 1 zero_lt_one).virtualValue (9 / 10) = 4 / 5 := by
    rw [oa_uniform_virtualValue _ ⟨by norm_num, by norm_num⟩]; norm_num
  have h1 : (uniformDensity 0 2 zero_lt_two).virtualValue 1 = 0 := by
    rw [oa_uniform_virtualValue _ ⟨by norm_num, by norm_num⟩]; norm_num
  obtain ⟨⟨hw0, hw1⟩, hmax⟩ := hw
  have := hmax ![1, 0] ⟨fun i => by fin_cases i <;> norm_num, by simp⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1] at this hw1
  have := hw0 1
  have := hw0 0
  refine ⟨by linarith, by linarith, by norm_num⟩

/-- **Example 23.F.2**, remark (2) (MWG, p. 905). Symmetric bidders, `J` nondecreasing on
`[θ̲, θ̄]` with `J(θ̲) > 0`: giving the good to a bidder `i` with the highest valuation solves the
relaxed problem (23.F.8). -/
theorem example_23_F_2_remark2_pointwise {J : ℝ → ℝ} {lo hi : ℝ}
    (hJ : MonotoneOn J (Set.Icc lo hi)) (hJlo : 0 < J lo) {θ : ι → ℝ}
    (hθ : ∀ k, θ k ∈ Set.Icc lo hi) {i : ι} (hi : ∀ k, θ k ≤ θ i) :
    PointwiseOptAlloc (fun k => J (θ k)) (fun k => if k = i then 1 else 0) := by
  have hJi : 0 < J (θ i) := lt_of_lt_of_le hJlo (hJ ⟨le_rfl, (hθ i).1.trans (hθ i).2⟩ (hθ i)
    (hθ i).1)
  refine ⟨⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc ∑ k, w' k * J (θ k) ≤ ∑ k, w' k * J (θ i) := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hJ (hθ k) (hθ i) (hi k)) (hw0' k)
    _ = (∑ k, w' k) * J (θ i) := by rw [Finset.sum_mul]
    _ ≤ 1 * J (θ i) := mul_le_mul_of_nonneg_right hw1' hJi.le
    _ = J (θ i) := one_mul _

/-- **Example 23.F.2**, remark (2) (MWG, p. 905). Symmetric bidders (all `Dᵢ = D`), `J`
nondecreasing with `J(θ̲) > 0`: any feasible social choice function that gives the good to a
highest-valuation bidder and leaves `U(θ̲) = 0` (e.g. the first-price or second-price auction
equilibrium, by the revenue equivalence theorem) is an optimal auction. -/
theorem example_23_F_2_remark2 (D : TypeDensity) (hJ : MonotoneOn D.virtualValue
      (Set.Icc D.lo D.hi)) (hJlo : 0 < D.virtualValue D.lo) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible (fun _ => D) ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun _ => D.measure) allocV ys ts i D.lo = 0)
    (hwin : ∀ θ, (∀ k, θ k ∈ Set.Icc D.lo D.hi) →
      ∃ i, (∀ k, θ k ≤ θ i) ∧ ys θ = fun k => if k = i then 1 else 0)
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible (fun _ => D) y t) :
    auctionRevenue (fun _ => D) t ≤ auctionRevenue (fun _ => D) ts := by
  refine example_23_F_2 (fun _ => D) hs hU0 (fun θ hθ => ?_) h
  obtain ⟨i, hi, he⟩ := hwin θ hθ
  rw [he]
  exact example_23_F_2_remark2_pointwise hJ hJlo hθ hi

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). One buyer: if `J` is nondecreasing on
`[θ̲, θ̄]` and `J(p*) = 0` with `p* ∈ [θ̲, θ̄]`, the posted price `p*` (sell iff `θ ≥ p*`) solves
the relaxed problem (23.F.8) at every type. -/
theorem example_23_F_2_remark3_pointwise {J : ℝ → ℝ} {lo hi p : ℝ}
    (hJ : MonotoneOn J (Set.Icc lo hi)) (hp : p ∈ Set.Icc lo hi) (hJp : J p = 0) {x : ℝ}
    (hx : x ∈ Set.Icc lo hi) :
    PointwiseOptAlloc (fun _ : Fin 1 => J x) (fun _ => if p ≤ x then 1 else 0) := by
  refine ⟨⟨fun _ => by split_ifs <;> norm_num, by simp; split_ifs <;> norm_num⟩,
    fun w' ⟨hw0', hw1'⟩ => ?_⟩
  simp only [Fin.sum_univ_one] at hw1' ⊢
  have h0 := hw0' 0
  split_ifs with hpx
  · have : 0 ≤ J x := hJp ▸ hJ hp hx hpx
    nlinarith
  · have : J x ≤ 0 := hJp ▸ hJ hx hp (le_of_lt (not_le.1 hpx))
    nlinarith

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). Where `φ(p) > 0`, the first-order condition
`1 - Φ(p) - pφ(p) = 0` of the posted price problem is equivalent to `J(p) = 0`. -/
theorem example_23_F_2_remark3_foc_iff (D : TypeDensity) {p : ℝ} (hp : 0 < D.dens p) :
    1 - D.cdf p - p * D.dens p = 0 ↔ D.virtualValue p = 0 := by
  rw [TypeDensity.virtualValue, sub_eq_zero, sub_eq_zero, eq_div_iff hp.ne']
  constructor <;> intro h <;> linarith

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). At a point `p` where the density is
continuous, the posted-price revenue `p(1 - Φ(p))` has derivative `1 - Φ(p) - pφ(p)`. -/
theorem example_23_F_2_remark3_foc (D : TypeDensity) {p : ℝ} (hc : ContinuousAt D.dens p) :
    HasDerivAt (fun q => q * (1 - D.cdf q)) (1 - D.cdf p - p * D.dens p) p := by
  have hΦ : HasDerivAt D.cdf (D.dens p) p :=
    intervalIntegral.integral_hasDerivAt_right (D.integrable_dens.intervalIntegrable)
      (D.measurable_dens.stronglyMeasurable.stronglyMeasurableAtFilter) hc
  have := (hasDerivAt_id' p).mul ((hasDerivAt_const p (1 : ℝ)).sub hΦ)
  exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)

/-- **Exercise 23.F.3** (MWG, p. 923). Symmetric bidders with `θ̲ = 0`, `J` nondecreasing and
`J(r) = 0`: the second-price auction with reserve price `r` (the good goes to a highest bidder if
his valuation is at least `r`, and is kept otherwise) solves the relaxed problem (23.F.8), so the
optimal reserve price is the `r` with `J(r) = 0`, independent of the number of bidders. -/
theorem exercise_23_F_3 {J : ℝ → ℝ} {hi r : ℝ} (hJ : MonotoneOn J (Set.Icc 0 hi))
    (hr : r ∈ Set.Icc 0 hi) (hJr : J r = 0) {θ : ι → ℝ} (hθ : ∀ k, θ k ∈ Set.Icc 0 hi)
    {i : ι} (hi : ∀ k, θ k ≤ θ i) :
    PointwiseOptAlloc (fun k => J (θ k)) (fun k => if k = i ∧ r ≤ θ i then 1 else 0) := by
  refine ⟨⟨fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  · by_cases hri : r ≤ θ i
    · simp [hri]
    · simp [hri]
  · by_cases hri : r ≤ θ i
    · have hJi : 0 ≤ J (θ i) := hJr ▸ hJ hr (hθ i) hri
      simp only [hri, and_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      calc ∑ k, w' k * J (θ k) ≤ ∑ k, w' k * J (θ i) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hJ (hθ k) (hθ i) (hi k)) (hw0' k)
        _ = (∑ k, w' k) * J (θ i) := by rw [Finset.sum_mul]
        _ ≤ 1 * J (θ i) := mul_le_mul_of_nonneg_right hw1' hJi
        _ = J (θ i) := one_mul _
    · simp only [hri, and_false, ite_false, zero_mul, Finset.sum_const_zero]
      refine Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0' k) ?_
      have := hJ (hθ k) hr ((hi k).trans (le_of_lt (not_le.1 hri)))
      linarith

/-- **Exercise 23.F.4** (MWG, p. 923). When the seller values the object at `θ₀`, his expected
payoff `∑ᵢ E[-tᵢ(θ)] + θ₀E[1 - ∑ᵢ yᵢ(θ)]` equals `∑ᵢ E[yᵢ(θ)(Jᵢ(θᵢ) - θ₀)] + θ₀ - ∑ᵢ Uᵢ(θ̲ᵢ)`; hence
a feasible `(y*, t*)` with `Uᵢ(θ̲ᵢ) = 0` whose allocation maximises `∑ᵢ yᵢ(Jᵢ(θᵢ) - θ₀)` at every
`θ ∈ Θ` maximises the seller's expected payoff among feasible social choice functions. -/
theorem exercise_23_F_4 (D : ι → TypeDensity) (θ0 : ℝ) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible D ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV ys ts i (D i).lo = 0)
    (hopt : ∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) →
      PointwiseOptAlloc (fun i => (D i).virtualValue (θ i) - θ0) (ys θ))
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible D y t)
    (hy : ∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure))
    (hys : ∀ i, Integrable (fun θ => ys θ i) (Measure.pi fun j => (D j).measure)) :
    auctionRevenue D t + θ0 * ∫ θ, (1 - ∑ i, y θ i) ∂Measure.pi (fun j => (D j).measure) ≤
      auctionRevenue D ts + θ0 * ∫ θ, (1 - ∑ i, ys θ i) ∂Measure.pi (fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hyF, hint, hbic, ht, hyJ, hIR⟩ := h
  obtain ⟨-, hint', hbic', ht', hyJ', -⟩ := hs
  -- the seller's payoff identity
  have key : ∀ (y t : (ι → ℝ) → ι → ℝ),
      (∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure)) →
      (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
        (Measure.pi fun j => (D j).measure)) →
      ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) +
        θ0 * ∫ θ, (1 - ∑ i, y θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ θ, ∑ i, y θ i * ((D i).virtualValue (θ i) - θ0) ∂Measure.pi (fun j => (D j).measure) +
        θ0 := by
    intro y t hy hyJ
    have hs1 : Integrable (fun θ => ∑ i, y θ i) (Measure.pi fun j => (D j).measure) :=
      integrable_finsetSum _ fun i _ => hy i
    have hi : ∀ i, Integrable (fun θ => y θ i * ((D i).virtualValue (θ i) - θ0))
        (Measure.pi fun j => (D j).measure) ∧
        ∫ θ, y θ i * ((D i).virtualValue (θ i) - θ0) ∂Measure.pi (fun j => (D j).measure) =
          ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) -
            (∫ θ, y θ i ∂Measure.pi (fun j => (D j).measure)) * θ0 := by
      intro i
      simp_rw [mul_sub]
      exact ⟨(hyJ i).sub ((hy i).mul_const θ0), by
        rw [integral_sub (hyJ i) ((hy i).mul_const θ0), integral_mul_const]⟩
    rw [integral_sub (integrable_const _) hs1, integral_const, probReal_univ, one_smul,
      integral_finsetSum _ fun i _ => hy i, integral_finsetSum _ fun i _ => (hi i).1]
    simp_rw [fun i => (hi i).2]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [auctionRevenue, auctionRevenue, eq_23_D_16 D hint hbic ht hyJ,
    eq_23_D_16 D hint' hbic' ht' hyJ']
  simp only [hU0, Finset.sum_const_zero, sub_zero]
  have k1 := key y t hy hyJ
  have k2 := key ys ts hys hyJ'
  have hU : 0 ≤ ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo :=
    Finset.sum_nonneg fun i _ => hIR i _ ⟨le_rfl, (D i).lo_lt_hi.le⟩
  have hint1 : ∀ (y : (ι → ℝ) → ι → ℝ),
      (∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure)) →
      (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
        (Measure.pi fun j => (D j).measure)) →
      Integrable (fun θ => ∑ i, y θ i * ((D i).virtualValue (θ i) - θ0))
        (Measure.pi fun j => (D j).measure) := fun y hy hyJ =>
    integrable_finsetSum _ fun i _ => by
      simp_rw [mul_sub]; exact (hyJ i).sub ((hy i).mul_const θ0)
  have hle := integral_mono_ae (hint1 y hy hyJ) (hint1 ys hys hyJ') (by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    exact (hopt θ hθ).2 (y θ) (hyF θ hθ))
  linarith

omit [DecidableEq ι] in
/-- **Exercise 23.F.4** (MWG, p. 923). With seller valuation `θ₀`, the optimal allocation gives the
good to buyer `i` if `Jᵢ(θᵢ) > max{θ₀, max_{k≠i} Jₖ(θₖ)}` and not if
`Jᵢ(θᵢ) < max{θ₀, max_{k≠i} Jₖ(θₖ)}` (the (23.F.9) rule with `Jᵢ - θ₀`). -/
theorem exercise_23_F_4_rule {Jv w : ι → ℝ} {θ0 : ℝ}
    (h : PointwiseOptAlloc (fun i => Jv i - θ0) w) (i : ι) :
    ((θ0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < θ0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0) := by
  obtain ⟨h1, h2⟩ := eq_23_F_9 h i
  refine ⟨fun ⟨ha, hb⟩ => h1 ⟨by linarith, fun k hk => by linarith [hb k hk]⟩,
    fun hc => h2 ?_⟩
  rcases hc with hc | ⟨k, hk, hc⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨k, hk, by linarith⟩

/-! ### A concrete instance: one buyer, uniform on `[0, 1]`, posted price `1/2` -/

/-- The posted price `1/2` allocation: the buyer gets the good iff `θ ≥ 1/2`. -/
noncomputable def oaPostY : (Fin 1 → ℝ) → Fin 1 → ℝ := fun θ _ => if 1 / 2 ≤ θ 0 then 1 else 0

/-- The posted price `1/2` transfers: the buyer pays `1/2` iff he gets the good. -/
noncomputable def oaPostT : (Fin 1 → ℝ) → Fin 1 → ℝ :=
  fun θ _ => -(1 / 2) * (if 1 / 2 ≤ θ 0 then 1 else 0)

/-- The uniform distribution on `[0, 1]` has `J(x) = 2x - 1` on `[0, 1]`. -/
theorem oa_uniform01_virtualValue {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    uniform01.virtualValue x = 2 * x - 1 :=
  oa_uniform_virtualValue zero_lt_one hx

/-- **Example 23.F.2**, remark (3) (MWG, p. 905), instance. One buyer with type uniform on
`[0, 1]` (`J(θ) = 2θ - 1`, `J(1/2) = 0`): the posted price `1/2` is feasible (Bayesian incentive
compatible, interim individually rational), leaves `U(0) = 0`, solves (23.F.8), and so maximises
expected revenue among all feasible social choice functions. -/
theorem example_23_F_2_instance :
    OptAuctionFeasible (fun _ : Fin 1 => uniform01) oaPostY oaPostT ∧
      ∀ y t, OptAuctionFeasible (fun _ : Fin 1 => uniform01) y t →
        auctionRevenue (fun _ : Fin 1 => uniform01) t ≤
          auctionRevenue (fun _ : Fin 1 => uniform01) oaPostT := by
  have : IsProbabilityMeasure uniform01.measure := uniform01.isProbabilityMeasure
  have hm : Measurable fun θ : Fin 1 → ℝ => (if 1 / 2 ≤ θ 0 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply 0))
      measurable_const measurable_const
  have hb : ∀ (i : Fin 1) (a : ℝ), interimBenefit (Measure.pi fun j => uniform01.measure)
      allocV oaPostY i a = if 1 / 2 ≤ a then 1 else 0 := by
    intro i a
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [interimBenefit, allocV, oaPostY]
  have hU : ∀ (i : Fin 1) (a : ℝ), interimU (Measure.pi fun j => uniform01.measure)
      allocV oaPostY oaPostT i a = (a - 1 / 2) * (if 1 / 2 ≤ a then 1 else 0) := by
    intro i a
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [interimU, hb]
    simp only [interimTransfer, oaPostT, update_self, integral_const, probReal_univ, one_smul]
    ring
  have hJm : Measurable uniform01.virtualValue :=
    measurable_id.sub (((continuous_const.sub uniform01.continuous_cdf).measurable).div
      uniform01.measurable_dens)
  have hfeas : OptAuctionFeasible (fun _ : Fin 1 => uniform01) oaPostY oaPostT := by
    refine ⟨fun θ _ => ⟨fun i => ?_, ?_⟩, fun i a _ => ?_, fun i θi hθi θh hθh => ?_,
      fun i => ?_, fun i => ?_, fun i x hx => ?_⟩
    · simp only [oaPostY]; split_ifs <;> norm_num
    · simp only [oaPostY, Fin.sum_univ_one]; split_ifs <;> norm_num
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      simp only [allocV, oaPostY, oaPostT, update_self]
      exact ⟨integrable_const _, integrable_const _⟩
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      simp only [linU, allocV, oaPostY, oaPostT, update_self, integral_const, probReal_univ,
        one_smul]
      split_ifs <;> nlinarith [hθi.1]
    · exact Integrable.of_bound (hm.const_mul _).aestronglyMeasurable 1
        (ae_of_all _ fun θ => by
          simp only [oaPostT, Real.norm_eq_abs]; split_ifs <;> norm_num)
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      refine Integrable.of_bound ((hm.mul (hJm.comp (measurable_pi_apply 0)))).aestronglyMeasurable
        1 ?_
      filter_upwards [re_ae_mem (fun j => ((fun _ : Fin 1 => uniform01) j).measure)
        fun j => ((fun _ : Fin 1 => uniform01) j).measure_compl_Icc] with θ hθ
      have h0 : θ 0 ∈ Set.Icc (0 : ℝ) 1 := hθ 0
      simp only [oaPostY, Real.norm_eq_abs]
      rw [oa_uniform01_virtualValue h0]
      have := h0.1
      have := h0.2
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp
    · rw [hU]
      split_ifs <;> nlinarith
  refine ⟨hfeas, fun y t h => example_23_F_2 _ hfeas (fun i => ?_) (fun θ hθ => ?_) h⟩
  · rw [hU]; norm_num [uniform01, uniformDensity]
  · have hJ : MonotoneOn uniform01.virtualValue (Set.Icc 0 1) := fun a ha b hb' hab => by
      rw [oa_uniform01_virtualValue ha, oa_uniform01_virtualValue hb']; linarith
    have hp := example_23_F_2_remark3_pointwise hJ (p := 1 / 2) ⟨by norm_num, by norm_num⟩
      (by rw [oa_uniform01_virtualValue ⟨by norm_num, by norm_num⟩]; norm_num) (hθ 0)
    have he : (fun i : Fin 1 => uniform01.virtualValue (θ i)) =
        fun _ => uniform01.virtualValue (θ 0) :=
      funext fun i => by rw [Subsingleton.elim i 0]
    rw [he]
    exact hp

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A principal-agent problem with hidden information

MWG, Section 23.F, Example 23.F.1 (pp. 900-903).

The agent's type `θ ∈ [θ̲, θ̄]` (`θ̄ < 0`) has a density `φ > 0` (`TypeDensity`); he chooses effort
`e ≥ 0` and receives `t`, with utility `t + θg(e)`; the principal's utility is `v(e) - t`. A
contract is `(e(·), t(·))`; `U(θ) = t(θ) + θg(e(θ))`; reservation utility `ū`;
`J(θ) = θ - (1 - Φ(θ))/φ(θ)`.

* (23.F.3): Bayesian incentive compatibility ⇔ (i) `g(e(·))` nondecreasing (⇔ `e(·)`
  nondecreasing, as `g` is increasing) and (ii) `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} g(e(s)) ds`
  (`eq_23_F_3`, `oc_monotone_comp_iff`); (iii) ⇔ (iii') (`eq_23_F_iii_iff`).
* (23.F.4): `E[v(e(θ)) - t(θ)] = E[v(e(θ)) + g(e(θ))J(θ)] - U(θ̲)` (`eq_23_F_4`), by the Fubini
  form of the integration by parts.
* `U(θ̲) = ū` in any optimal contract (`eq_23_F_5`).
* `example_23_F_1`: if `e*(θ)` maximises `v(e) + g(e)J(θ)` over `e ≥ 0` for every `θ` (the relaxed
  problem), and `(e*, t*)` is incentive compatible with `U*(θ̲) = ū`, it is optimal among all
  incentive compatible and individually rational contracts.
* (23.F.6): at an interior optimum `v'(e) + g'(e)J(θ) = 0` (`eq_23_F_6`). MWG's implicit
  function theorem argument for monotonicity of `e(·)` is replaced by monotone comparative
  statics (`oc_maximizer_mono`, `oc_maximizer_monotoneOn`): with `g` strictly increasing, `J`
  nondecreasing and unique maximisers, `e(·)` is nondecreasing.
* p. 903: `e(θ) ≤ e^*(θ)` (first best) everywhere, `= ` at `θ̄`, and `<` for `θ < θ̄` given
  differentiability, `g' > 0` on `e > 0`, `g'(0) = 0`, `v'(0) > 0` (`example_23_F_1_le_firstBest`,
  `example_23_F_1_eq_firstBest_hi`, `example_23_F_1_lt_firstBest`).
* Instance: `θ` uniform on `[-2, -1]` (`J(θ) = 2θ + 1`), `g(e) = e²`, `v(e) = 2e - e²`:
  `e*(θ) = -1/(2θ)`, `t*(θ) = -1/(2θ) - 1/8`, `ū = 0`, first best `1/(1 - θ)`
  (`example_23_F_1_instance`).

Departures: the derivative hypotheses on `v`, `g` are replaced where possible by their
consequences (strict monotonicity of `g` on `e ≥ 0`, uniqueness of maximisers); integrability of
the payoffs is assumed explicitly; the "heuristic" perturbation argument (footnote 49) is verbal.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Example 23.F.1** (MWG, p. 901). The agent's utility from truth telling,
`U(θ) = t(θ) + θg(e(θ))`. -/
def ocU (g e t : ℝ → ℝ) (θ : ℝ) : ℝ := t θ + θ * g (e θ)

/-- **Example 23.F.1** (MWG, pp. 901-902). A feasible contract: effort `e(θ) ≥ 0`, Bayesian
incentive compatible (truth telling optimal for every type), individually rational
(`U(θ) ≥ ū`), and with the expectations involved existing. -/
def OCFeasible (D : TypeDensity) (v g : ℝ → ℝ) (ubar : ℝ) (e t : ℝ → ℝ) : Prop :=
  (∀ θ, 0 ≤ e θ) ∧ LinearIC (fun θ => g (e θ)) t D.lo D.hi ∧
    (∀ θ ∈ Set.Icc D.lo D.hi, ubar ≤ ocU g e t θ) ∧ Integrable (fun θ => v (e θ)) D.measure ∧
    Integrable t D.measure ∧ Integrable (fun θ => θ * g (e θ)) D.measure ∧
    Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure

/-- The principal's expected payoff `E[v(e(θ)) - t(θ)]`. -/
noncomputable def ocPayoff (D : TypeDensity) (v : ℝ → ℝ) (e t : ℝ → ℝ) : ℝ :=
  ∫ θ, (v (e θ) - t θ) ∂D.measure

/-- **(23.F.3)** (MWG, p. 902), constraints (i)-(ii): the contract is Bayesian incentive
compatible iff `g(e(·))` is nondecreasing and `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} g(e(s)) ds`
(Proposition 23.D.2 with `k = e`, `v₁(k) = g(e)`). -/
theorem eq_23_F_3 {g e t : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC (fun θ => g (e θ)) t lo hi ↔ MonotoneOn (fun θ => g (e θ)) (Set.Icc lo hi) ∧
      ∀ θ ∈ Set.Icc lo hi, ocU g e t θ = ocU g e t lo + ∫ s in lo..θ, g (e s) := by
  rw [linearIC_iff]
  simp only [ocU]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun θ hθ => ?_⟩ <;> have := h2 θ hθ <;>
    linarith

/-- **(23.F.3)** (MWG, p. 902), "constraint (i) follows because `g` is increasing": when `g` is
strictly increasing on `e ≥ 0` and efforts are nonnegative, `g(e(·))` is nondecreasing iff `e(·)`
is. -/
theorem oc_monotone_comp_iff {g e : ℝ → ℝ} {S : Set ℝ} (hg : StrictMonoOn g (Set.Ici 0))
    (he : ∀ θ, 0 ≤ e θ) : MonotoneOn (fun θ => g (e θ)) S ↔ MonotoneOn e S := by
  constructor
  · intro h x hx y hy hxy
    by_contra hlt
    rw [not_le] at hlt
    have := hg (Set.mem_Ici.2 (he y)) (Set.mem_Ici.2 (he x)) hlt
    have := h hx hy hxy
    simp only at this
    linarith
  · intro h x hx y hy hxy
    exact hg.monotoneOn (Set.mem_Ici.2 (he x)) (Set.mem_Ici.2 (he y)) (h hx hy hxy)

/-- **(23.F.3)** (MWG, p. 902), (iii) ⇔ (iii'): given (ii) and `g ≥ 0` on effort levels used,
`U(θ) ≥ ū` for all `θ` iff `U(θ̲) ≥ ū`. -/
theorem eq_23_F_iii_iff {g e t : ℝ → ℝ} {lo hi ubar : ℝ} (hle : lo ≤ hi)
    (hg0 : ∀ θ, 0 ≤ g (e θ))
    (hii : ∀ θ ∈ Set.Icc lo hi, ocU g e t θ = ocU g e t lo + ∫ s in lo..θ, g (e s)) :
    (∀ θ ∈ Set.Icc lo hi, ubar ≤ ocU g e t θ) ↔ ubar ≤ ocU g e t lo := by
  refine ⟨fun h => h lo ⟨le_rfl, hle⟩, fun h θ hθ => ?_⟩
  rw [hii θ hθ]
  have := intervalIntegral.integral_nonneg (μ := volume) hθ.1 fun s _ => hg0 s
  linarith

/-- For `s ∈ [θ̲, θ̄]`, `1 - Φ(s) ≥ 0`. -/
theorem oc_one_sub_cdf_nonneg (D : TypeDensity) {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    0 ≤ 1 - D.cdf s := by
  rw [← D.measureReal_Ici hs]; exact measureReal_nonneg

/-- For `s ∈ [θ̲, θ̄)`, `1 - Φ(s) > 0`. -/
theorem oc_one_sub_cdf_pos (D : TypeDensity) {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) (hlt : s < D.hi) :
    0 < 1 - D.cdf s := by
  have := D.isProbabilityMeasure
  rw [← D.measureReal_Ici hs, measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  exact (lt_of_lt_of_le (D.measure_Ioo_pos hs.1 hlt le_rfl)
    (measure_mono fun x hx => Set.mem_Ici.2 hx.1.le)).ne'

/-- **(23.F.4)** (MWG, p. 902). For an incentive compatible contract (with the expectations
existing), `E[v(e(θ)) - t(θ)] = E[v(e(θ)) + g(e(θ))J(θ)] - U(θ̲)`, `J(θ) = θ - (1 - Φ(θ))/φ(θ)`. -/
theorem eq_23_F_4 (D : TypeDensity) {v g e t : ℝ → ℝ}
    (hIC : LinearIC (fun θ => g (e θ)) t D.lo D.hi)
    (hv : Integrable (fun θ => v (e θ)) D.measure) (ht : Integrable t D.measure)
    (hθg : Integrable (fun θ => θ * g (e θ)) D.measure)
    (hgr : Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure) :
    ocPayoff D v e t = ∫ θ, (v (e θ) + g (e θ) * D.virtualValue θ) ∂D.measure -
      ocU g e t D.lo := by
  have := D.isProbabilityMeasure
  have hle : D.lo ≤ D.hi := D.lo_lt_hi.le
  obtain ⟨hmono, hii⟩ := eq_23_F_3.1 hIC
  set P : ℝ → ℝ := fun θ => ∫ s in D.lo..θ, g (e s) with hP
  have hw : IntervalIntegrable (fun s => g (e s)) volume D.lo D.hi := by
    apply MonotoneOn.intervalIntegrable; rw [Set.uIcc_of_le hle]; exact hmono
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have htP : t =ᵐ[D.measure] fun θ => ocU g e t D.lo + P θ - θ * g (e θ) := by
    filter_upwards [hae] with θ hθ
    have := hii θ hθ
    simp only [ocU] at this ⊢
    simp only [hP]
    linarith
  have hPint : Integrable P D.measure := by
    have h1 : Integrable (fun θ => t θ + θ * g (e θ) - ocU g e t D.lo) D.measure :=
      (ht.add hθg).sub (integrable_const _)
    refine h1.congr ?_
    filter_upwards [htP] with θ hθ
    rw [hθ]; ring
  have hEP : ∫ θ, P θ ∂D.measure = ∫ s in D.lo..D.hi, g (e s) * (1 - D.cdf s) := by
    rw [hP, td_integral_integral_eq D.measure hle D.measure_compl_Icc hw]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    simp only [D.measureReal_Ici hs]
  have hEr : ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure =
      ∫ s in D.lo..D.hi, g (e s) * (1 - D.cdf s) := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    have := (D.dens_pos s hs).ne'
    field_simp
  have hEt : ∫ θ, t θ ∂D.measure =
      ocU g e t D.lo + ∫ θ, P θ ∂D.measure - ∫ θ, θ * g (e θ) ∂D.measure := by
    have h1 : Integrable (fun θ => ocU g e t D.lo + P θ) D.measure :=
      (integrable_const _).add hPint
    have e1 : ∫ θ, (ocU g e t D.lo + P θ - θ * g (e θ)) ∂D.measure =
        ∫ θ, (ocU g e t D.lo + P θ) ∂D.measure - ∫ θ, θ * g (e θ) ∂D.measure :=
      integral_sub h1 hθg
    have e2 : ∫ θ, (ocU g e t D.lo + P θ) ∂D.measure =
        ∫ _θ, ocU g e t D.lo ∂D.measure + ∫ θ, P θ ∂D.measure :=
      integral_add (integrable_const _) hPint
    rw [integral_congr_ae htP, e1, e2, integral_const, probReal_univ, one_smul]
  have hEJ : ∫ θ, (v (e θ) + g (e θ) * D.virtualValue θ) ∂D.measure =
      ∫ θ, v (e θ) ∂D.measure + ∫ θ, θ * g (e θ) ∂D.measure -
        ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure := by
    have e1 : ∫ θ, (v (e θ) + θ * g (e θ)) ∂D.measure =
        ∫ θ, v (e θ) ∂D.measure + ∫ θ, θ * g (e θ) ∂D.measure := integral_add hv hθg
    have e2 : ∫ θ, (v (e θ) + θ * g (e θ) - g (e θ) * ((1 - D.cdf θ) / D.dens θ)) ∂D.measure =
        ∫ θ, (v (e θ) + θ * g (e θ)) ∂D.measure -
          ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure := integral_sub (hv.add hθg) hgr
    rw [← e1, ← e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [TypeDensity.virtualValue]
    ring
  rw [ocPayoff, integral_sub hv ht, hEt, hEJ, hEP, hEr]
  ring

/-- **Example 23.F.1** (MWG, p. 902). "In any solution we must have `U(θ̲) = ū`": a feasible
contract that maximises the principal's expected payoff among feasible contracts leaves the lowest
type exactly his reservation utility (otherwise lower all transfers by `U(θ̲) - ū`); here
`g ≥ 0` on `e ≥ 0` (MWG: `g(0) = 0`, `g(e) > 0` for `e > 0`). -/
theorem eq_23_F_5 (D : TypeDensity) {v g : ℝ → ℝ} {ubar : ℝ} {e t : ℝ → ℝ}
    (hg0 : ∀ x, 0 ≤ x → 0 ≤ g x) (hf : OCFeasible D v g ubar e t)
    (hopt : ∀ e' t', OCFeasible D v g ubar e' t' → ocPayoff D v e' t' ≤ ocPayoff D v e t) :
    ocU g e t D.lo = ubar := by
  have := D.isProbabilityMeasure
  obtain ⟨he, hIC, hIR, hv, ht, hθg, hgr⟩ := hf
  by_contra hne
  have hlt : ubar < ocU g e t D.lo := lt_of_le_of_ne (hIR _ ⟨le_rfl, D.lo_lt_hi.le⟩) (Ne.symm hne)
  set δ := ocU g e t D.lo - ubar with hδ
  have hfeas : OCFeasible D v g ubar e (fun θ => t θ - δ) := by
    refine ⟨he, fun θ hθ θh hθh => ?_, fun θ hθ => ?_, hv, ht.sub (integrable_const _), hθg, hgr⟩
    · have := hIC θ hθ θh hθh; simp only at this ⊢; linarith
    · have hlo : D.lo ∈ Set.Icc D.lo D.hi := ⟨le_rfl, D.lo_lt_hi.le⟩
      have h1 := hIC θ hθ D.lo hlo
      have h2 := mul_nonneg (sub_nonneg.2 hθ.1) (hg0 (e D.lo) (he D.lo))
      simp only [ocU, hδ] at h1 h2 ⊢
      nlinarith
  have := hopt e _ hfeas
  rw [ocPayoff, ocPayoff] at this
  have he2 : ∫ θ, (v (e θ) - (t θ - δ)) ∂D.measure = ∫ θ, (v (e θ) - t θ) ∂D.measure + δ := by
    have e : ∫ θ, ((v (e θ) - t θ) + δ) ∂D.measure =
        ∫ θ, (v (e θ) - t θ) ∂D.measure + ∫ _θ, δ ∂D.measure :=
      integral_add (hv.sub ht) (integrable_const δ)
    rw [integral_const, probReal_univ, one_smul] at e
    rw [← e]
    congr 1; funext θ; ring
  rw [he2] at this
  linarith

/-- `x ≥ 0` maximises `h` over effort levels `e ≥ 0`. -/
def OCArgmax (h : ℝ → ℝ) (x : ℝ) : Prop := 0 ≤ x ∧ ∀ e, 0 ≤ e → h e ≤ h x

/-- With incentive compatibility, `v(e) + g(e)J` is integrable when the payoffs are. -/
theorem oc_integrable_vJ (D : TypeDensity) {v g e : ℝ → ℝ}
    (hv : Integrable (fun θ => v (e θ)) D.measure)
    (hθg : Integrable (fun θ => θ * g (e θ)) D.measure)
    (hgr : Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure) :
    Integrable (fun θ => v (e θ) + g (e θ) * D.virtualValue θ) D.measure := by
  refine ((hv.add hθg).sub hgr).congr (Filter.Eventually.of_forall fun θ => ?_)
  simp only [TypeDensity.virtualValue, Pi.add_apply, Pi.sub_apply]
  ring

/-- **Example 23.F.1** (MWG, pp. 902-903). If `e*(θ)` maximises `v(e) + g(e)J(θ)` over `e ≥ 0`
for every `θ ∈ [θ̲, θ̄]` (the relaxed problem (23.F.5) without constraint (i)), and `(e*, t*)` is a
feasible contract with `U*(θ̲) = ū` (so `t*` is given by (ii)), then `(e*, t*)` maximises the
principal's expected payoff among all feasible contracts. -/
theorem example_23_F_1 (D : TypeDensity) {v g : ℝ → ℝ} {ubar : ℝ} {es ts : ℝ → ℝ}
    (hs : OCFeasible D v g ubar es ts) (hU : ocU g es ts D.lo = ubar)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * D.virtualValue θ) (es θ))
    {e t : ℝ → ℝ} (h : OCFeasible D v g ubar e t) :
    ocPayoff D v e t ≤ ocPayoff D v es ts := by
  obtain ⟨he, hIC, hIR, hv, ht, hθg, hgr⟩ := h
  obtain ⟨-, hIC', -, hv', ht', hθg', hgr'⟩ := hs
  rw [eq_23_F_4 D hIC hv ht hθg hgr, eq_23_F_4 D hIC' hv' ht' hθg' hgr', hU]
  have hlo := hIR D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
  have hle := integral_mono_ae (oc_integrable_vJ D hv hθg hgr) (oc_integrable_vJ D hv' hθg' hgr')
    (by
      filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with θ hθ
      exact (hmax θ hθ).2 (e θ) (he θ))
  linarith

/-- **(23.F.6)** (MWG, p. 902). At an interior solution `e > 0` of `max_{e ≥ 0} v(e) + g(e)c`
(with `c = J(θ)`), the first-order condition `v'(e) + g'(e)c = 0` holds. -/
theorem eq_23_F_6 {v g : ℝ → ℝ} {v' g' c x : ℝ} (hv : HasDerivAt v v' x) (hg : HasDerivAt g g' x)
    (hx : 0 < x) (hmax : OCArgmax (fun e => v e + g e * c) x) : v' + g' * c = 0 := by
  have hloc : IsLocalMax (fun e => v e + g e * c) x :=
    Filter.mem_of_superset (Ioi_mem_nhds hx) fun e he => hmax.2 e (le_of_lt he)
  exact hloc.hasDerivAt_eq_zero (hv.add (hg.mul_const c))

/-- Monotone comparative statics (replacing MWG's implicit function theorem argument, p. 902):
with `g` strictly increasing on `e ≥ 0`, a maximiser of `v(e) + g(e)c₁` is at most any maximiser
of `v(e) + g(e)c₂` when `c₁ < c₂`. -/
theorem oc_maximizer_mono {v g : ℝ → ℝ} (hg : StrictMonoOn g (Set.Ici 0)) {c1 c2 x1 x2 : ℝ}
    (hc : c1 < c2) (h1 : OCArgmax (fun e => v e + g e * c1) x1)
    (h2 : OCArgmax (fun e => v e + g e * c2) x2) : x1 ≤ x2 := by
  by_contra hlt
  rw [not_le] at hlt
  have hgx := hg (Set.mem_Ici.2 h2.1) (Set.mem_Ici.2 h1.1) hlt
  have a1 := h1.2 x2 h2.1
  have a2 := h2.2 x1 h1.1
  simp only at a1 a2
  nlinarith

/-- A strictly concave function has at most one maximiser on `e ≥ 0`. -/
theorem oc_argmax_unique {h : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Set.Ici 0) h) {x y : ℝ}
    (hx : OCArgmax h x) (hy : OCArgmax h y) : x = y := by
  by_contra hne
  have hmid := hc.2 (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hy.1) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have h1 := hx.2 (1 / 2 * x + 1 / 2 * y) (by have := hx.1; have := hy.1; linarith)
  have h2 := hx.2 y hy.1
  have h3 := hy.2 x hx.1
  linarith

/-- With `v` strictly concave, `g` convex and `c ≤ 0` (MWG: `v'' < 0`, `g'' > 0`, and
`J(θ) ≤ θ < 0`), `v(e) + g(e)c` is strictly concave on `e ≥ 0`, so its maximiser is unique. -/
theorem oc_strictConcave {v g : ℝ → ℝ} {c : ℝ} (hv : StrictConcaveOn ℝ (Set.Ici 0) v)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hc : c ≤ 0) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun e => v e + g e * c) := by
  refine hv.add_concaveOn ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have := hg.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith

/-- **Example 23.F.1** (MWG, p. 902). With `g` strictly increasing on `e ≥ 0`, `J` nondecreasing
and a unique maximiser `e(θ)` of `v(e) + g(e)J(θ)` for every `θ`, the solution `e(·)` of the
relaxed problem is nondecreasing, so it satisfies constraint (i). -/
theorem oc_maximizer_monotoneOn {v g J es : ℝ → ℝ} {lo hi : ℝ} (hg : StrictMonoOn g (Set.Ici 0))
    (hJ : MonotoneOn J (Set.Icc lo hi))
    (hmax : ∀ θ ∈ Set.Icc lo hi, OCArgmax (fun x => v x + g x * J θ) (es θ))
    (huniq : ∀ θ ∈ Set.Icc lo hi, ∀ x, OCArgmax (fun x => v x + g x * J θ) x → x = es θ) :
    MonotoneOn es (Set.Icc lo hi) := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (hJ ha hb hab) with hlt | heq
  · exact oc_maximizer_mono hg hlt (hmax a ha) (hmax b hb)
  · have := huniq a ha (es b) (by rw [heq]; exact hmax b hb)
    rw [this]

/-- `J(θ) ≤ θ` on `[θ̲, θ̄]`, with `J(θ) < θ` for `θ < θ̄`, and `J(θ̄) = θ̄`. -/
theorem oc_virtualValue_facts (D : TypeDensity) :
    (∀ θ ∈ Set.Icc D.lo D.hi, D.virtualValue θ ≤ θ) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, θ < D.hi → D.virtualValue θ < θ) ∧ D.virtualValue D.hi = D.hi := by
  refine ⟨fun θ hθ => ?_, fun θ hθ hlt => ?_, ?_⟩
  · have := div_nonneg (oc_one_sub_cdf_nonneg D hθ) (D.dens_pos θ hθ).le
    simp only [TypeDensity.virtualValue]; linarith
  · have := div_pos (oc_one_sub_cdf_pos D hθ hlt) (D.dens_pos θ hθ)
    simp only [TypeDensity.virtualValue]; linarith
  · have h1 : D.cdf D.hi = 1 := D.integral_dens
    simp [TypeDensity.virtualValue, h1]

/-- **Example 23.F.1** (MWG, p. 903). With `g` strictly increasing on `e ≥ 0`, the optimal effort
`e(θ)` (maximising `v(e) + g(e)J(θ)`) is at most the first-best (ex post classically efficient)
effort `e*(θ)` (maximising `v(e) + g(e)θ`) for every `θ < θ̄`. -/
theorem example_23_F_1_le_firstBest (D : TypeDensity) {v g : ℝ → ℝ}
    (hg : StrictMonoOn g (Set.Ici 0)) {θ x y : ℝ} (hθ : θ ∈ Set.Icc D.lo D.hi) (hlt : θ < D.hi)
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue θ) x)
    (hy : OCArgmax (fun e => v e + g e * θ) y) : x ≤ y :=
  oc_maximizer_mono hg ((oc_virtualValue_facts D).2.1 θ hθ hlt) hx hy

/-- **Example 23.F.1** (MWG, p. 903). At `θ̄`, `J(θ̄) = θ̄`: the optimal and the first-best effort
problems coincide, so with a unique maximiser `e(θ̄) = e*(θ̄)`. -/
theorem example_23_F_1_eq_firstBest_hi (D : TypeDensity) {v g : ℝ → ℝ} {x y : ℝ}
    (hc : StrictConcaveOn ℝ (Set.Ici 0) (fun e => v e + g e * D.hi))
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue D.hi) x)
    (hy : OCArgmax (fun e => v e + g e * D.hi) y) : x = y := by
  rw [(oc_virtualValue_facts D).2.2] at hx
  exact oc_argmax_unique hc hx hy

/-- If `h'(0) > 0` then `0` does not maximise `h` over `e ≥ 0`. -/
theorem oc_not_argmax_zero {h : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt h d 0) (hpos : 0 < d) :
    ¬ OCArgmax h 0 := by
  rintro ⟨-, hmax⟩
  have ht := hasDerivAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < slope h 0 e :=
    (nhdsWithin_mono _ (fun e (he : 0 < e) => ne_of_gt he) |>.trans le_rfl)
      (ht.eventually (lt_mem_nhds hpos))
  obtain ⟨e, he, hpos'⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [slope_def_field, sub_zero] at he
  have := hmax e (le_of_lt hpos')
  have : (h e - h 0) / e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hpos'.le
  linarith

/-- **Example 23.F.1** (MWG, p. 903): `e(θ) < e*(θ)` for `θ < θ̄`. Hypotheses as printed: `v`, `g`
differentiable, `g'(0) = 0`, `g'(e) > 0` for `e > 0`, `v' > 0`; `g` strictly increasing on
`e ≥ 0` (which these imply with `g(0) = 0`). -/
theorem example_23_F_1_lt_firstBest (D : TypeDensity) {v g v' g' : ℝ → ℝ}
    (hv : ∀ e, HasDerivAt v (v' e) e) (hgd : ∀ e, HasDerivAt g (g' e) e) (hg'0 : g' 0 = 0)
    (hg'pos : ∀ e, 0 < e → 0 < g' e) (hv'pos : ∀ e, 0 ≤ e → 0 < v' e)
    (hg : StrictMonoOn g (Set.Ici 0)) {θ x y : ℝ} (hθ : θ ∈ Set.Icc D.lo D.hi) (hlt : θ < D.hi)
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue θ) x)
    (hy : OCArgmax (fun e => v e + g e * θ) y) : x < y := by
  have hle := example_23_F_1_le_firstBest D hg hθ hlt hx hy
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    subst h
    rcases lt_or_eq_of_le hx.1 with hpos | hzero
    · have f1 := eq_23_F_6 (hv x) (hgd x) hpos hx
      have f2 := eq_23_F_6 (hv x) (hgd x) hpos hy
      have hJ := (oc_virtualValue_facts D).2.1 θ hθ hlt
      have := hg'pos x hpos
      nlinarith
    · rw [← hzero] at hy
      refine oc_not_argmax_zero (d := v' 0 + g' 0 * θ) ((hv 0).add ((hgd 0).mul_const θ)) ?_ hy
      rw [hg'0, zero_mul, add_zero]
      exact hv'pos 0 le_rfl

/-- A measurable function bounded on `[θ̲, θ̄]` is integrable for the type distribution. -/
theorem oc_integrable_of_bound (D : TypeDensity) {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc D.lo D.hi, |f x| ≤ C) : Integrable f D.measure := by
  have := D.isProbabilityMeasure
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with x hx
  rw [Real.norm_eq_abs]
  exact hC x hx

/-- **Example 23.F.1** (MWG, pp. 901-903), instance. Types uniform on `[-2, -1]`
(`J(θ) = 2θ + 1`, nondecreasing), `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`. The contract
`e(θ) = -1/(2θ)`, `t(θ) = -1/(2θ) - 1/8` (written with `|θ|`) is feasible, gives `U(θ̲) = ū`,
solves the relaxed problem and hence is optimal; the first-best effort is `e*(θ) = 1/(1 - θ)`, and
`e(θ) < e*(θ)` for `θ < θ̄ = -1`, with equality at `θ̄`. -/
theorem example_23_F_1_instance :
    let D := uniformDensity (-2) (-1) (by norm_num)
    let v : ℝ → ℝ := fun e => 2 * e - e ^ 2
    let g : ℝ → ℝ := fun e => e ^ 2
    let es : ℝ → ℝ := fun θ => 1 / (2 * |θ|)
    let ts : ℝ → ℝ := fun θ => 1 / (2 * |θ|) - 1 / 8
    OCFeasible D v g 0 es ts ∧ ocU g es ts D.lo = 0 ∧
      (∀ e t, OCFeasible D v g 0 e t → ocPayoff D v e t ≤ ocPayoff D v es ts) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * θ) (1 / (1 - θ))) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, θ < D.hi → es θ < 1 / (1 - θ)) ∧ es D.hi = 1 / (1 - D.hi) := by
  intro D v g es ts
  have hlo : D.lo = -2 := rfl
  have hhi : D.hi = -1 := rfl
  -- basic facts about `e(θ)` on `[-2, -1]`
  have hes : ∀ θ ∈ Set.Icc D.lo D.hi, 2 * -θ * es θ = 1 ∧ 1 / 4 ≤ es θ ∧ es θ ≤ 1 / 2 := by
    intro θ hθ
    rw [hlo, hhi] at hθ
    have hθ0 : θ < 0 := by linarith [hθ.2]
    simp only [es, abs_of_neg hθ0]
    refine ⟨by have := hθ0.ne; field_simp, ?_, ?_⟩
    · rw [le_div_iff₀ (by linarith)]; linarith [hθ.1]
    · rw [div_le_iff₀ (by linarith)]; linarith [hθ.2]
  have hesm : Measurable es :=
    measurable_const.div (measurable_const.mul continuous_abs.measurable)
  have hJ : ∀ θ ∈ Set.Icc D.lo D.hi, D.virtualValue θ = 2 * θ + 1 := by
    intro θ hθ
    have h := oa_uniform_virtualValue (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    exact h.trans (by ring)
  have hr : ∀ θ ∈ Set.Icc D.lo D.hi, (1 - D.cdf θ) / D.dens θ = -1 - θ := by
    intro θ hθ
    have hd : D.dens θ = ((-1) - (-2) : ℝ)⁻¹ := by
      change (Set.Icc (-2 : ℝ) (-1)).indicator (fun _ => ((-1) - (-2) : ℝ)⁻¹) θ = _
      exact Set.indicator_of_mem hθ _
    have h := oa_uniform_cdf (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    change (1 - (uniformDensity (-2) (-1) (by norm_num)).cdf θ) / D.dens θ = _
    rw [h, hd]; norm_num; ring
  have hfeas : OCFeasible D v g 0 es ts := by
    refine ⟨fun θ => by simp only [es]; positivity, fun θ hθ θh hθh => ?_, fun θ hθ => ?_,
      oc_integrable_of_bound D ((measurable_const.mul hesm).sub (hesm.pow_const 2)) 1
        fun θ hθ => ?_,
      oc_integrable_of_bound D (hesm.sub measurable_const) 1 fun θ hθ => ?_,
      oc_integrable_of_bound D (measurable_id.mul (hesm.pow_const 2)) 1 fun θ hθ => ?_,
      oc_integrable_of_bound D ((hesm.pow_const 2).mul ((measurable_const.sub
        D.continuous_cdf.measurable).div D.measurable_dens)) 1 fun θ hθ => ?_⟩
    · obtain ⟨he, -, -⟩ := hes θ hθ
      have key : (θ * es θ ^ 2 + (es θ - 1 / 8)) - (θ * es θh ^ 2 + (es θh - 1 / 8)) =
          (-θ) * (es θh - es θ) ^ 2 := by linear_combination (es θh - es θ) * he
      have hθ0 : 0 ≤ -θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
      have := mul_nonneg hθ0 (sq_nonneg (es θh - es θ))
      simp only [g, ts]
      change θ * es θh ^ 2 + (es θh - 1 / 8) ≤ θ * es θ ^ 2 + (es θ - 1 / 8)
      linarith
    · obtain ⟨he, h1, -⟩ := hes θ hθ
      simp only [ocU, g, ts]
      change (0 : ℝ) ≤ es θ - 1 / 8 + θ * es θ ^ 2
      nlinarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      rw [abs_le]; constructor <;> nlinarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      simp only [ts]
      change |es θ - 1 / 8| ≤ 1
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      have := hθ; rw [hlo, hhi] at this
      simp only [g]
      rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      have := hθ; rw [hlo, hhi] at this
      simp only [g]
      rw [hr θ hθ, abs_le]; constructor <;> nlinarith [this.1, this.2]
  have hU : ocU g es ts D.lo = 0 := by
    rw [hlo]; simp only [ocU, g, ts, es]; norm_num
  refine ⟨hfeas, hU, fun e t h => example_23_F_1 D hfeas hU (fun θ hθ => ?_) h,
    fun θ hθ => ?_, fun θ hθ hlt => ?_, ?_⟩
  · obtain ⟨he, h1, -⟩ := hes θ hθ
    refine ⟨by linarith, fun x _ => ?_⟩
    have hθ0 : 0 ≤ -θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
    have key : (v (es θ) + g (es θ) * D.virtualValue θ) - (v x + g x * D.virtualValue θ) =
        2 * (-θ) * (x - es θ) ^ 2 := by
      rw [hJ θ hθ]; simp only [v, g]; linear_combination (2 * (x - es θ)) * he
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ0) (sq_nonneg (x - es θ))
    linarith
  · have hθ1 : 0 < 1 - θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
    have hy : (1 - θ) * (1 / (1 - θ)) = 1 := by field_simp
    refine ⟨by positivity, fun x _ => ?_⟩
    have key : (v (1 / (1 - θ)) + g (1 / (1 - θ)) * θ) - (v x + g x * θ) =
        (1 - θ) * (x - 1 / (1 - θ)) ^ 2 := by
      simp only [v, g]; linear_combination (2 * (x - 1 / (1 - θ))) * hy
    have := mul_nonneg hθ1.le (sq_nonneg (x - 1 / (1 - θ)))
    linarith
  · rw [hlo, hhi] at hθ
    rw [hhi] at hlt
    have hθ0 : θ < 0 := by linarith
    simp only [es, abs_of_neg hθ0]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith
  · rw [hhi]; simp only [es]; norm_num

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Examples 23.B.1-23.B.4 and Exercise 23.B.1

MWG, Section 23.B, pp. 860-864, and Exercise 23.B.1 (p. 918).

* **Example 23.B.1** (p. 860): `X = {x, y, z}` (`0, 1, 2`), agent 1 has the single type `θ̄₁`
  (`Unit`) and ranks `x ≻ y ≻ z`; agent 2 has types `θ₂'` (`true`: `z ≻ y ≻ x`) and `θ₂''`
  (`false`: `y ≻ x ≻ z`). The social choice function `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = x` is
  ex post efficient (`example_23_B_1_efficient`), but agent 2 of type `θ₂''` gains by claiming
  `θ₂'` (`example_23_B_1`). Since agent 1 has a single type, strategy-proofness is exactly
  agent 2's willingness to reveal his type (`b1_strategyProof_iff`).
* **Exercise 23.B.1** (a)-(e): agent 2 reveals truthfully for (a)-(d), not for (e).
* **Example 23.B.2** (pp. 860-861, Figure 23.B.1): made concrete in `WalrasManipulation`.
* **Example 23.B.3** (pp. 861-862), the public project with cost `c` and feasible set
  `X = {(k, t) : k ∈ {0, 1}, ∑ᵢ tᵢ ≤ -ck}`: a social choice function is ex post efficient iff at
  every `θ` the project is built when `∑ᵢ θᵢ > c`, not built when `∑ᵢ θᵢ < c`, and
  `∑ᵢ tᵢ(θ) = -ck(θ)` (`example_23_B_3_efficient_iff`); so (23.B.1)-(23.B.2) are sufficient
  (`example_23_B_3_efficient`), as MWG state ("is ex post efficient if"); at `∑ᵢ θᵢ = c` either
  project level is efficient. With the egalitarian contribution rule, `Θᵢ = {θ̄ᵢ}` (`i ≠ 1`),
  `Θ₁ = [0, ∞)` and `c > ∑_{i≠1} θ̄ᵢ > c(I - 1)/I`, agent 1's type is critical, the others gain
  from the bridge, and agent 1 of type `c - ∑_{i≠1} θ̄ᵢ + ε` (small `ε > 0`) gains by claiming
  `θ₁ = 0` (`example_23_B_3`).
* **Example 23.B.4** (pp. 862-863): with one indivisible good, `X = {(y, t) : yᵢ ∈ {0, 1},
  ∑ᵢ yᵢ = 1, ∑ᵢ tᵢ ≤ 0}` (the winner `k` with `yᵢ = 1` iff `k = i`), ex post efficiency is
  `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` together with `∑ᵢ tᵢ(θ) = 0`
  (`example_23_B_4_efficient_iff`); the three bilateral trade cases (`example_23_B_4_bilateral`).
  The auction parts of Example 23.B.4 are in `Auctions23B.lean`.

Departures: types are real numbers (`Θᵢ = ℝ`) in Examples 23.B.3-23.B.4; MWG's type sets are
subsets (`[0, ∞)`, `{θ̄ᵢ}`, `[θ̲ᵢ, θ̄ᵢ]`) and ex post efficiency is a condition profile by profile,
so it restricts to them. No corrections.
-/

namespace MWG.MechanismDesign

open Function

/-! ### Example 23.B.1 and Exercise 23.B.1 -/

/-- **Example 23.B.1** (MWG, p. 860). The type sets: `Θ₁ = {θ̄₁}` (`Unit`) and `Θ₂ = {θ₂', θ₂''}`
(`true`, `false`). -/
abbrev b1Θ : Fin 2 → Type := ![Unit, Bool]

/-- **Example 23.B.1** (MWG, p. 860). Rank utilities on `X = {x, y, z}` (`0, 1, 2`):
`≿₁(θ̄₁)`: `x ≻ y ≻ z`; `≿₂(θ₂')`: `z ≻ y ≻ x`; `≿₂(θ₂'')`: `y ≻ x ≻ z`. -/
noncomputable def b1U : (i : Fin 2) → Fin 3 → b1Θ i → ℝ
  | 0 => fun x _ => ((![2, 1, 0] : Fin 3 → ℕ) x : ℝ)
  | 1 => fun x (b : Bool) => (((if b then ![0, 1, 2] else ![1, 2, 0]) : Fin 3 → ℕ) x : ℝ)

/-- A social choice function of Example 23.B.1, given by `g(θ₂) = f(θ̄₁, θ₂)`. -/
def b1F (g : Bool → Fin 3) : ((i : Fin 2) → b1Θ i) → Fin 3 := fun θ => g (θ 1)

/-- The type profile `(θ̄₁, θ₂)`. -/
def b1Prof (b : Bool) : (i : Fin 2) → b1Θ i := fun i => match i with
  | 0 => ()
  | 1 => b

/-- **Example 23.B.1** (MWG, p. 860). Agent 1 has a single type, so `f` is truthfully
implementable in dominant strategies iff agent 2 is always willing to reveal his type:
`u₂(f(θ̄₁, θ̂₂), θ₂) ≤ u₂(f(θ̄₁, θ₂), θ₂)` for all `θ₂, θ̂₂`. -/
theorem b1_strategyProof_iff (g : Bool → Fin 3) :
    StrategyProof b1U (b1F g) ↔ ∀ b b' : Bool, b1U 1 (g b') b ≤ b1U 1 (g b) b := by
  constructor
  · intro h b b'
    have := h 1 (b1Prof b) b'
    have e : b1F g (update (b1Prof b) 1 b') = g b' := by
      simp only [b1F]; exact congrArg g (update_self (β := b1Θ) 1 b' (b1Prof b))
    rw [e] at this; exact this
  · intro h i θ θh
    fin_cases i
    · have e : update θ 0 θh = θ := by
        funext j
        fin_cases j
        · rfl
        · rfl
      simp [e]
    · simpa [b1F] using h (θ 1) θh

/-- **Example 23.B.1** (MWG, p. 860). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = x`. -/
def b1Example : Bool → Fin 3 := fun b => if b then 1 else 0

/-- **Example 23.B.1** (MWG, p. 860). The social choice function `f(θ̄₁, θ₂') = y`,
`f(θ̄₁, θ₂'') = x` is ex post efficient: `y` and `x` are Pareto optimal for the respective
profiles. -/
theorem example_23_B_1_efficient : ExPostEfficient b1U (b1F b1Example) := by
  rw [exPostEfficient_iff]
  intro θ x hx i
  have h0 := hx 0
  have h1 := hx 1
  simp only [b1F, b1Example] at h0 h1 ⊢
  generalize θ 1 = b at h0 h1 ⊢
  revert h0 h1
  fin_cases i <;> fin_cases x <;> cases b <;> norm_num [b1U]

/-- **Example 23.B.1** (MWG, p. 860). Agent 2 of type `θ₂''` strictly prefers `y = f(θ̄₁, θ₂')` to
`x = f(θ̄₁, θ₂'')`, so he will claim to be of type `θ₂'`: `f` is not truthfully implementable
in dominant strategies. -/
theorem example_23_B_1 :
    b1U 1 (b1F b1Example (b1Prof false)) false < b1U 1 (b1F b1Example (b1Prof true)) false ∧
      ¬StrategyProof b1U (b1F b1Example) := by
  refine ⟨by norm_num [b1U, b1F, b1Example, b1Prof], fun h => ?_⟩
  have := (b1_strategyProof_iff _).1 h false true
  norm_num [b1U, b1Example] at this

/-- **Exercise 23.B.1(a)** (MWG, p. 918). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = y`: agent 2 reveals his
type truthfully. -/
theorem exercise_23_B_1a : StrategyProof b1U (b1F fun _ => 1) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(b)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = x`: agent 2 reveals his
type truthfully. -/
theorem exercise_23_B_1b : StrategyProof b1U (b1F fun b => if b then 2 else 0) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(c)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = y`: agent 2 reveals his
type truthfully (he always gets his best alternative). -/
theorem exercise_23_B_1c : StrategyProof b1U (b1F fun b => if b then 2 else 1) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(d)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = z`: agent 2 reveals his
type truthfully (a constant function). -/
theorem exercise_23_B_1d : StrategyProof b1U (b1F fun _ => 2) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(e)** (MWG, p. 918). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = z`: agent 2 of type
`θ₂'` prefers `z` to `y`, so he claims `θ₂''`; `f` is not truthfully implementable. -/
theorem exercise_23_B_1e : ¬StrategyProof b1U (b1F fun b => if b then 1 else 2) := by
  intro h
  have := (b1_strategyProof_iff _).1 h true false
  norm_num [b1U] at this

/-! ### Example 23.B.3: a public project -/

/-- The project level `k ∈ {0, 1}` (`false`, `true`) as a real number. -/
def ppK (k : Bool) : ℝ := if k then 1 else 0

/-- **Example 23.B.3** (MWG, p. 861). The feasible alternatives with project cost `c`:
`X = {(k, t₁, …, t_I) : k ∈ {0, 1}, ∑ᵢ tᵢ ≤ -ck}`. -/
def PPAlt (ι : Type*) [Fintype ι] (c : ℝ) : Type _ :=
  {x : Bool × (ι → ℝ) // ∑ i, x.2 i ≤ -(c * ppK x.1)}

/-- **Example 23.B.3** (MWG, p. 861). `uᵢ(x, θᵢ) = θᵢk + (m̄ᵢ + tᵢ)`. -/
def ppU {ι : Type*} (m : ι → ℝ) : (i : ι) → Bool × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => θi * ppK x.1 + (m i + x.2 i)

variable {ι : Type*}

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). If at `θ` the alternative `(k, t)` leaves a surplus
`δ = (∑ᵢ θᵢ - c)(k' - k) - (∑ᵢ tᵢ + ck) > 0` by switching to project level `k'`, then some
feasible alternative makes every agent strictly better off (each gets `δ/I` more). -/
theorem pp_improve [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ) (θ : ι → ℝ) (x : PPAlt ι c)
    (k' : Bool)
    (hδ : 0 < (∑ i, θ i - c) * (ppK k' - ppK x.1.1) - (∑ i, x.1.2 i + c * ppK x.1.1)) :
    ∃ x' : PPAlt ι c, ∀ i, ppU m i x.1 (θ i) < ppU m i x'.1 (θ i) := by
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set δ := (∑ i, θ i - c) * (ppK k' - ppK x.1.1) - (∑ i, x.1.2 i + c * ppK x.1.1) with hδdef
  let t' : ι → ℝ := fun i => x.1.2 i + θ i * (ppK x.1.1 - ppK k') + δ / Fintype.card ι
  have hsum : ∑ i, t' i = -(c * ppK k') := by
    simp only [t', sum_add_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    rw [hδdef]
    ring
  refine ⟨⟨(k', t'), hsum.le⟩, fun i => ?_⟩
  simp only [ppU, t']
  have := div_pos hδ hI
  nlinarith

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). With the feasible set `∑ᵢ tᵢ ≤ -ck`, a social choice function
`f(θ) = (k(θ), t(θ))` is ex post efficient iff for all `θ` the project is built when
`∑ᵢ θᵢ > c`, not built when `∑ᵢ θᵢ < c`, and there is no waste: `∑ᵢ tᵢ(θ) = -ck(θ)`. -/
theorem example_23_B_3_efficient_iff [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ)
    (f : (ι → ℝ) → PPAlt ι c) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi) f ↔
      ∀ θ, (c < ∑ i, θ i → (f θ).1.1 = true) ∧ (∑ i, θ i < c → (f θ).1.1 = false) ∧
        ∑ i, (f θ).1.2 i = -(c * ppK (f θ).1.1) := by
  constructor
  · intro hE θ
    have no : ∀ k', ¬0 < (∑ i, θ i - c) * (ppK k' - ppK (f θ).1.1) -
        (∑ i, (f θ).1.2 i + c * ppK (f θ).1.1) := by
      intro k' hδ
      obtain ⟨x', hx'⟩ := pp_improve c m θ (f θ) k' hδ
      exact hE ⟨θ, x', fun i => (hx' i).le, Classical.arbitrary ι, hx' _⟩
    have hfeas := (f θ).2
    refine ⟨fun hc => ?_, fun hc => ?_, ?_⟩
    · by_contra hk
      have := no true
      simp only [Bool.not_eq_true] at hk
      simp only [hk, ppK, Bool.false_eq_true, ↓reduceIte] at this hfeas
      apply this; linarith
    · by_contra hk
      have := no false
      simp only [Bool.not_eq_false] at hk
      simp only [hk, ppK, Bool.false_eq_true, ↓reduceIte] at this hfeas
      apply this; linarith
    · by_contra hne
      have := no (f θ).1.1
      apply this
      have := lt_of_le_of_ne hfeas hne
      linarith
  · rintro hf ⟨θ, x, hx, j, hj⟩
    have hsum : ∑ i, ppU m i (f θ).1 (θ i) < ∑ i, ppU m i x.1 (θ i) :=
      sum_lt_sum (fun i _ => hx i) ⟨j, mem_univ j, hj⟩
    simp only [ppU, sum_add_distrib, ← sum_mul] at hsum
    obtain ⟨h1, h2, h3⟩ := hf θ
    have hx2 := x.2
    have key : (∑ i, θ i - c) * ppK x.1.1 ≤ (∑ i, θ i - c) * ppK (f θ).1.1 := by
      have hK : ppK x.1.1 = 0 ∨ ppK x.1.1 = 1 := by
        cases x.1.1 <;> simp [ppK]
      rcases lt_trichotomy (∑ i, θ i) c with hlt | heq | hgt
      · have e : ppK (f θ).1.1 = 0 := by rw [h2 hlt]; simp [ppK]
        rw [e, mul_zero]
        rcases hK with h | h
        · rw [h, mul_zero]
        · rw [h, mul_one]; linarith
      · rw [heq]; simp
      · have e : ppK (f θ).1.1 = 1 := by rw [h1 hgt]; simp [ppK]
        rw [e, mul_one]
        rcases hK with h | h
        · rw [h, mul_zero]; linarith
        · rw [h, mul_one]
    nlinarith

open Finset in
/-- **Example 23.B.3**, (23.B.1)-(23.B.2) (MWG, p. 861). If `k(θ) = 1` iff `∑ᵢ θᵢ ≥ c` and
`∑ᵢ tᵢ(θ) = -ck(θ)` for all `θ`, then `f` is ex post efficient. -/
theorem example_23_B_3_efficient [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ)
    (f : (ι → ℝ) → PPAlt ι c) (hk : ∀ θ, (f θ).1.1 = decide (c ≤ ∑ i, θ i))
    (ht : ∀ θ, ∑ i, (f θ).1.2 i = -(c * ppK (f θ).1.1)) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi) f := by
  refine (example_23_B_3_efficient_iff c m f).2 fun θ => ⟨fun h => ?_, fun h => ?_, ht θ⟩
  · rw [hk θ]; exact decide_eq_true h.le
  · rw [hk θ]; exact decide_eq_false (not_le.2 h)

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). The ex post efficient social choice function with the
egalitarian contribution rule: `k(θ) = 1` iff `∑ᵢ θᵢ ≥ c`, `tᵢ(θ) = -(c/I)k(θ)`. -/
noncomputable def ppEgal [Fintype ι] (c : ℝ) (θ : ι → ℝ) : PPAlt ι c :=
  ⟨(decide (c ≤ ∑ i, θ i), fun _ => -(c / Fintype.card ι * ppK (decide (c ≤ ∑ i, θ i)))), by
    by_cases h : Fintype.card ι = 0
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h
      simp only [univ_eq_empty, sum_empty, ppK]
      split_ifs with hc
      · simp only [decide_eq_true_eq] at hc; linarith
      · simp
    · simp only [sum_const, card_univ, nsmul_eq_mul]
      field_simp
      exact le_rfl⟩

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). The egalitarian social choice function is ex post
efficient. -/
theorem ppEgal_efficient [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi)
      (ppEgal c) := by
  have hI : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine example_23_B_3_efficient c m _ (fun _ => rfl) fun θ => ?_
  simp only [ppEgal, sum_const, card_univ, nsmul_eq_mul]
  field_simp

open Finset in
/-- **Example 23.B.3** (MWG, p. 862). With the egalitarian rule, `Θᵢ = {θ̄ᵢ}` for `i ≠ 1` and
`c > ∑_{i≠1} θ̄ᵢ > c(I - 1)/I`, writing `S = ∑_{i≠1} θ̄ᵢ`:
(i) agent 1's type is critical: the bridge is built iff `θ₁ ≥ c - S`;
(ii) the other agents' total utility gain from the bridge, `∑_{i≠1} (θ̄ᵢ - c/I)`, is positive;
(iii) for `0 < ε < S - c(I - 1)/I`, agent 1 of type `θ₁ = c - S + ε ∈ Θ₁ = [0, ∞)` gets
`(c(I - 1)/I - S + ε) + m̄₁ < m̄₁` by telling the truth, and `m̄₁` by claiming `θ₁ = 0`. -/
theorem example_23_B_3 [Fintype ι] [DecidableEq ι] (c : ℝ) (m : ι → ℝ) (i₀ : ι)
    (θbar : ι → ℝ) (hc1 : ∑ j ∈ univ.erase i₀, θbar j < c)
    (hc2 : c * (Fintype.card ι - 1) / Fintype.card ι < ∑ j ∈ univ.erase i₀, θbar j)
    {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < ∑ j ∈ univ.erase i₀, θbar j - c * (Fintype.card ι - 1) / Fintype.card ι) :
    (∀ a, (ppEgal c (update θbar i₀ a)).1.1 = true ↔ c - ∑ j ∈ univ.erase i₀, θbar j ≤ a) ∧
      0 < ∑ j ∈ univ.erase i₀, (θbar j - c / Fintype.card ι) ∧
      0 ≤ c - ∑ j ∈ univ.erase i₀, θbar j + ε ∧
      ppU m i₀ (ppEgal c (update θbar i₀ (c - ∑ j ∈ univ.erase i₀, θbar j + ε))).1
          (c - ∑ j ∈ univ.erase i₀, θbar j + ε) =
        (c * (Fintype.card ι - 1) / Fintype.card ι - ∑ j ∈ univ.erase i₀, θbar j + ε) + m i₀ ∧
      ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - ∑ j ∈ univ.erase i₀, θbar j + ε) = m i₀ ∧
      ppU m i₀ (ppEgal c (update θbar i₀ (c - ∑ j ∈ univ.erase i₀, θbar j + ε))).1
          (c - ∑ j ∈ univ.erase i₀, θbar j + ε) <
        ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - ∑ j ∈ univ.erase i₀, θbar j + ε) := by
  set S := ∑ j ∈ univ.erase i₀, θbar j with hS
  have hne : Nonempty ι := ⟨i₀⟩
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hk : ∀ a, (ppEgal c (update θbar i₀ a)).1.1 = decide (c - S ≤ a) := by
    intro a
    simp only [ppEgal, bb_sum_update, ← hS]
    congr 1
    exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  have hcrit : ∀ a, (ppEgal c (update θbar i₀ a)).1.1 = true ↔ c - S ≤ a := by
    intro a; rw [hk a]; simp
  have hcard : ((univ.erase i₀).card : ℝ) = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ i₀), card_univ, Nat.cast_sub Fintype.card_pos]; simp
  have hothers : ∑ j ∈ univ.erase i₀, (θbar j - c / Fintype.card ι) =
      S - c * (Fintype.card ι - 1) / Fintype.card ι := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]; ring
  have htrue : ppU m i₀ (ppEgal c (update θbar i₀ (c - S + ε))).1 (c - S + ε) =
      (c * (Fintype.card ι - 1) / Fintype.card ι - S + ε) + m i₀ := by
    have h1 := (hcrit (c - S + ε)).2 (by linarith)
    simp only [ppU]
    rw [h1]
    simp only [ppEgal] at h1 ⊢
    rw [h1]
    simp only [ppK, ↓reduceIte]
    field_simp
    ring
  have hlie : ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - S + ε) = m i₀ := by
    have h0 : (ppEgal c (update θbar i₀ 0)).1.1 = false := by
      rw [hk 0]; simp only [decide_eq_false_iff_not, not_le]; linarith
    simp only [ppU]
    rw [h0]
    simp only [ppEgal] at h0 ⊢
    rw [h0]
    simp [ppK]
  refine ⟨hcrit, by rw [hothers]; exact sub_pos.2 hc2, by linarith, htrue, hlie, ?_⟩
  rw [htrue, hlie]
  linarith

/-! ### Example 23.B.4: allocation of a single indivisible good -/

open Finset in
/-- **Example 23.B.4** (MWG, p. 862). With the good going to agent `k` (`yᵢ = 1` iff `k = i`) and
`vᵢ(k, θᵢ) = θᵢyᵢ`, the project rule is efficient (23.C.7) iff it always gives the good to a
highest valuation: `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` and `θ`. -/
theorem goodV_efficient_iff [Fintype ι] [DecidableEq ι] [Nonempty ι] (k : (ι → ℝ) → ι) :
    EfficientProject (Θ := fun _ => ℝ) goodV k ↔
      ∀ θ i, (if k θ = i then (1 : ℝ) else 0) * (θ i - univ.sup' univ_nonempty θ) = 0 := by
  have hs : ∀ (θ : ι → ℝ) (w : ι), ∑ i, goodV i w (θ i) = θ w := by
    intro θ w
    simp [goodV]
  constructor
  · intro h θ i
    by_cases hi : k θ = i
    · subst hi
      have hle : univ.sup' univ_nonempty θ ≤ θ (k θ) :=
        sup'_le _ _ fun j _ => by have := h θ j; rwa [hs, hs] at this
      have hge := le_sup' θ (mem_univ (k θ))
      simp only [↓reduceIte, one_mul]
      linarith
    · simp [hi]
  · intro h θ w
    have := h θ (k θ)
    simp only [↓reduceIte, one_mul, sub_eq_zero] at this
    rw [hs, hs, this]
    exact le_sup' θ (mem_univ w)

open Finset in
/-- **Example 23.B.4** (MWG, p. 862). A social choice function `f(θ) = (y(θ), t(θ))` allocating a
single indivisible good, with feasible set `X = {(y, t) : ∑ᵢ yᵢ = 1, ∑ᵢ tᵢ ≤ 0}` (the good goes to
agent `k`), is ex post efficient iff `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` and `∑ᵢ tᵢ(θ) = 0`, for
all `θ`. -/
theorem example_23_B_4_efficient_iff [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ι → ℝ)
    (f : (ι → ℝ) → QLAlt ι ι) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : QLAlt ι ι) θi => qlU goodV m i x.1 θi) f ↔
      (∀ θ i, (if (f θ).1.1 = i then (1 : ℝ) else 0) * (θ i - univ.sup' univ_nonempty θ) = 0) ∧
        ∀ θ, ∑ i, (f θ).1.2 i = 0 := by
  rw [exPostEfficient_ql_iff (Θ := fun _ => ℝ) goodV m f, goodV_efficient_iff]
  rfl

/-- **Example 23.B.4**, bilateral trade (MWG, p. 863). Seller (agent 1) and buyer (agent 2) with
`θ₁ ∈ [lo₁, hi₁]`, `θ₂ ∈ [lo₂, hi₂]`: if `lo₂ > hi₁` there are certainly gains from trade; if
`lo₁ > hi₂` there are certainly none; if `lo₂ < hi₁` and `lo₁ < hi₂` both can happen. -/
theorem example_23_B_4_bilateral {lo1 hi1 lo2 hi2 : ℝ} (h1 : lo1 ≤ hi1) (h2 : lo2 ≤ hi2) :
    (hi1 < lo2 → ∀ θ1 ∈ Set.Icc lo1 hi1, ∀ θ2 ∈ Set.Icc lo2 hi2, θ1 < θ2) ∧
      (hi2 < lo1 → ∀ θ1 ∈ Set.Icc lo1 hi1, ∀ θ2 ∈ Set.Icc lo2 hi2, θ2 < θ1) ∧
      (lo2 < hi1 → lo1 < hi2 → (∃ θ1 ∈ Set.Icc lo1 hi1, ∃ θ2 ∈ Set.Icc lo2 hi2, θ1 < θ2) ∧
        ∃ θ1 ∈ Set.Icc lo1 hi1, ∃ θ2 ∈ Set.Icc lo2 hi2, θ2 < θ1) := by
  refine ⟨fun h θ1 hθ1 θ2 hθ2 => by linarith [hθ1.2, hθ2.1],
    fun h θ1 hθ1 θ2 hθ2 => by linarith [hθ1.1, hθ2.2], fun ha hb => ⟨?_, ?_⟩⟩
  · exact ⟨lo1, ⟨le_rfl, h1⟩, hi2, ⟨h2, le_rfl⟩, hb⟩
  · exact ⟨hi1, ⟨h1, le_rfl⟩, lo2, ⟨le_rfl, h2⟩, ha⟩

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Auctions and bilateral trade in Section 23.B

MWG, Section 23.B, pp. 863-869 (Examples 23.B.4-23.B.7, Definitions 23.B.3-23.B.4 for auctions)
and Exercises 23.B.2-23.B.4 (p. 918).

Two buyers (or a seller `0` and a buyer `1`) with types independent and uniform on `[0, 1]`
(`unif2`); an outcome is `(y, t)` with `y` the vector of probabilities of holding the good and
`uᵢ((y, t), θᵢ) = θᵢyᵢ + tᵢ` (`linU allocV`). The allocation `twoY` gives the good to agent `0`
iff `θ₁ ≤ θ₀` (ties to the lowest index, MWG's footnotes 8 and 10). Agent `0` here is MWG's buyer
1 (or seller), agent `1` MWG's buyer 2 (or buyer); the auctioneer of footnote 5 is left out, as
his transfer `t₀ = -(t₁ + t₂)` does not affect the buyers.

* **Example 23.B.4** (pp. 863-864): for the social choice function (23.B.3)-(23.B.8) (the winner
  pays his valuation), if the other buyer tells the truth, buyer `i`'s expected utility from
  announcing `θ̂ ∈ [0, 1]` is `(θᵢ - θ̂)θ̂`, uniquely maximized at `θ̂ = θᵢ/2`; truth telling is not
  optimal (`example_23_B_4_firstPriceType`). For the second-price variant truth telling is a
  weakly dominant strategy (`example_23_B_4_secondPriceType`).
* **Example 23.B.5** (pp. 865-866), the first-price sealed-bid auction: against `b_j = α_jθ_j`
  (`α_j > 0`), bidding `b ≥ 0` gives `(θᵢ - b) min(b/α_j, 1)` (`fp_interim`), maximized at
  `min(θᵢ/2, α_j)` (`example_23_B_5_bestResponse`); `bᵢ = θᵢ/2` is a Bayesian Nash
  equilibrium that implements (23.B.9)-(23.B.14) (`example_23_B_5`).
* **Example 23.B.6** and **Exercise 23.B.3** (pp. 866-867, 918), the second-price sealed-bid
  auction with any number of buyers: `bᵢ = θᵢ` is weakly dominant (`exercise_23_B_3`), for any
  real bids (`sp_truth_dominant`); with two buyers it implements the second-price social choice
  function (`example_23_B_6`). The general first- and second-price outcome functions (p. 867)
  are `firstPriceOutcome`, `secondPriceOutcome` (winner: lowest index among the highest bids).
* **Example 23.B.7** (pp. 868-869): in the direct mechanism for (23.B.9)-(23.B.14), announcing
  `θ̂` gives `(θᵢ - θ̂/2)θ̂`, maximized at `θ̂ = θᵢ` (`example_23_B_7`).
* **Exercise 23.B.2** (the split-the-difference rule `splitT` of `MyersonSatterthwaite.lean`:
  trade iff `θ₁ > θ₀`, at price `(θ₀ + θ₁)/2`): if the seller tells the truth, the buyer's
  expected utility from announcing `θ̂` is `θ₂θ̂ - 3θ̂²/4`, maximized at `θ̂ = 2θ₂/3`: the buyer
  understates his valuation (`exercise_23_B_2`). Also `example_23_B_4_auction_efficient`: the
  social choice function (23.B.3)-(23.B.8) is ex post efficient (p. 863).
* **Exercise 23.B.4**, the double auction: `b₁ = 2θ₁/3 + 1/4`, `b₂ = 2θ₂/3 + 1/12` is a Bayesian
  Nash equilibrium (`exercise_23_B_4a`); it implements "trade iff `θ₂ > θ₁ + 1/4`, at price
  `(θ₁ + θ₂)/3 + 1/6`" (`exercise_23_B_4a_outcome`), which is not ex post efficient
  (`exercise_23_B_4a_not_efficient`) and is Bayesian incentive compatible (`exercise_23_B_4b`).

Departures. Types are real numbers with the uniform prior on `[0, 1]`; a Bayesian Nash
equilibrium is required for the types in `[0, 1]` and bids `b ≥ 0` (`IsBNEOn`); the interim
expected utilities are computed exactly from the uniform distribution, as MWG pose the buyers'
problems. Exercise 23.B.4(a) asks for "a" linear equilibrium: we verify the
Chatterjee-Samuelson one (MWG's other linear equilibria are not classified).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function Set

/-! ### Integration tools -/

/-- `max 0 (min τ 1)`, the point of `[0, 1]` nearest to `τ`. -/
def clamp01 (τ : ℝ) : ℝ := max 0 (min τ 1)

/-- `clamp01 τ ∈ [0, 1]`. -/
theorem clamp01_mem (τ : ℝ) : clamp01 τ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

/-- `clamp01 τ = τ` on `[0, 1]`. -/
theorem clamp01_of_mem {τ : ℝ} (h : τ ∈ Icc (0 : ℝ) 1) : clamp01 τ = τ := by
  simp [clamp01, h.1, h.2]

/-- `clamp01 τ = 0` for `τ ≤ 0`. -/
theorem clamp01_of_nonpos {τ : ℝ} (h : τ ≤ 0) : clamp01 τ = 0 := by
  simp [clamp01, h.trans zero_le_one, h]

/-- `clamp01 τ = 1` for `τ ≥ 1`. -/
theorem clamp01_of_one_le {τ : ℝ} (h : 1 ≤ τ) : clamp01 τ = 1 := by
  simp [clamp01, h]

/-- `∫_0^1 1{x ≤ τ} g(x) dx = ∫_0^{clamp τ} g` for every real `τ`. -/
theorem au_int_le (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x ≤ τ then g x else 0) = ∫ x in (0 : ℝ)..clamp01 τ, g x := by
  rcases le_or_gt τ 0 with h | h
  · rw [clamp01_of_nonpos h, intervalIntegral.integral_same,
      intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    simp [not_le.2 (lt_of_le_of_lt h hx.1)]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h.le, h1⟩]; exact re_integral_ite_le ⟨h.le, h1⟩ g
    · rw [clamp01_of_one_le h1.le]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp [hx.2.trans h1.le]

/-- `∫_0^1 1{x < τ} g(x) dx = ∫_0^{clamp τ} g` for every real `τ`. -/
theorem au_int_lt (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x < τ then g x else 0) = ∫ x in (0 : ℝ)..clamp01 τ, g x := by
  rcases le_or_gt τ 0 with h | h
  · rw [clamp01_of_nonpos h, intervalIntegral.integral_same]
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_).trans
      (by simp)
    rw [uIcc_of_le zero_le_one] at hx
    simp [not_lt.2 (h.trans hx.1)]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h.le, h1⟩]; exact re_integral_ite_lt ⟨h.le, h1⟩ g
    · rw [clamp01_of_one_le h1.le]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp [lt_of_le_of_lt hx.2 h1]

/-- `∫_0^1 1{τ < x} g(x) dx = ∫_{clamp τ}^1 g` for every real `τ`. -/
theorem au_int_gt (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if τ < x then g x else 0) = ∫ x in clamp01 τ..1, g x := by
  rcases lt_or_ge τ 0 with h | h
  · rw [clamp01_of_nonpos h.le]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp [lt_of_lt_of_le h hx.1]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h, h1⟩]; exact re_integral_ite_gt ⟨h, h1⟩ g
    · rw [clamp01_of_one_le h1.le, intervalIntegral.integral_same]
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_).trans
        (by simp)
      rw [uIcc_of_le zero_le_one] at hx
      simp [not_lt.2 (hx.2.trans h1.le)]

/-- `∫_a^b (A + Bx) dx = A(b - a) + B(b² - a²)/2`. -/
theorem au_int_affine (A B a b : ℝ) :
    ∫ x in a..b, (A + B * x) = A * (b - a) + B * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun x : ℝ => B * x).intervalIntegrable a b),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- With two independent uniform types, the expectation of a function of `θⱼ` alone is
`∫_0^1`. -/
theorem au_eval {H : ℝ → ℝ} (hH : Measurable H) (j : Fin 2) :
    ∫ θ, H (θ j) ∂unif2 = ∫ x in (0 : ℝ)..1, H x := by
  have := uniform01.isProbabilityMeasure
  exact (integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) j
    hH.aestronglyMeasurable).trans (uniform01_integral _)

/-- `x ↦ 1{x ≤ τ}(A + Bx)` is measurable. -/
theorem au_meas_le (τ A B : ℝ) : Measurable fun x : ℝ => if x ≤ τ then A + B * x else 0 :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

/-- `x ↦ 1{x < τ}(A + Bx)` is measurable. -/
theorem au_meas_lt (τ A B : ℝ) : Measurable fun x : ℝ => if x < τ then A + B * x else 0 :=
  Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

/-- `x ↦ 1{τ < x}(A + Bx)` is measurable. -/
theorem au_meas_gt (τ A B : ℝ) : Measurable fun x : ℝ => if τ < x then A + B * x else 0 :=
  Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-! ### Example 23.B.4: the auction social choice functions -/

/-- **(23.B.6)-(23.B.7)** (MWG, p. 863). The winner pays his own valuation:
`tᵢ(θ) = -θᵢyᵢ(θ)`. -/
noncomputable def fullPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 0 * twoY θ 0), -(θ 1 * twoY θ 1)]

/-- **Example 23.B.4** (MWG, pp. 863-864). For the social choice function (23.B.3)-(23.B.8), with
the other buyer truthful, buyer `i`'s expected utility from announcing `a ∈ [0, 1]` is
`(θᵢ - a) Prob(θⱼ ≤ a) = (θᵢ - a)a`. -/
theorem fullPrice_interim (i : Fin 2) (θi : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 =
      (θi - a) * a := by
  have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV i (twoY θ, fullPriceT θ) θi := by
    simp only [linU, allocV]
    refine (measurable_const.mul (measurable_twoY i)).add ?_
    fin_cases i
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 1)).neg
  rw [re_unif2_update (G := fun θ => linU allocV i (twoY θ, fullPriceT θ) θi) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, linU, allocV, fullPriceT, twoY,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, θi * (if x ≤ a then (1 : ℝ) else 0) + -(a * if x ≤ a then 1 else 0) =
        if x ≤ a then (θi - a) + 0 * x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha, au_int_affine]; ring
  · simp only [Fin.mk_one, re_update_vec1, linU, allocV, fullPriceT, twoY,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, θi * (if x < a then (1 : ℝ) else 0) + -(a * if x < a then 1 else 0) =
        if x < a then (θi - a) + 0 * x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha, au_int_affine]; ring

/-- **Example 23.B.4** (MWG, pp. 863-864). Buyer `i`'s problem `max_{θ̂} (θᵢ - θ̂)θ̂` over
`θ̂ ∈ [0, 1]` has the unique solution `θ̂ = θᵢ/2`; for `θᵢ ∈ (0, 1]` truth telling is not optimal
(it gives `0 < θᵢ²/4`). -/
theorem example_23_B_4_firstPriceType (i : Fin 2) {θi : ℝ} (hθ : θi ∈ Icc (0 : ℝ) 1) :
    θi / 2 ∈ Icc (0 : ℝ) 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1,
        ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 ≤
          ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)), fullPriceT (update θ' i (θi / 2)))
            θi ∂unif2) ∧
      (∀ a ∈ Icc (0 : ℝ) 1,
        ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 =
          ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)), fullPriceT (update θ' i (θi / 2)))
            θi ∂unif2 → a = θi / 2) ∧
      (0 < θi → ∫ θ', linU allocV i (twoY (update θ' i θi), fullPriceT (update θ' i θi)) θi
          ∂unif2 < ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)),
            fullPriceT (update θ' i (θi / 2))) θi ∂unif2) := by
  have hh : θi / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  refine ⟨hh, fun a ha => ?_, fun a ha he => ?_, fun hpos => ?_⟩
  · rw [fullPrice_interim i θi ha, fullPrice_interim i θi hh]; nlinarith [sq_nonneg (a - θi / 2)]
  · rw [fullPrice_interim i θi ha, fullPrice_interim i θi hh] at he
    nlinarith [sq_nonneg (a - θi / 2)]
  · rw [fullPrice_interim i θi hθ, fullPrice_interim i θi hh]; nlinarith

/-- **Example 23.B.4** (MWG, p. 864). For the second-price social choice function (the winner pays
the other's valuation), truth telling is a weakly dominant strategy for each buyer, whatever the
other announces: the social choice function is strategy-proof (for all real valuations). -/
theorem example_23_B_4_secondPriceType :
    StrategyProof (Θ := fun _ : Fin 2 => ℝ) (linU allocV) fun θ => (twoY θ, secondPriceT θ) := by
  intro i θ θh
  fin_cases i
  · simp only [Fin.zero_eta, linU, allocV, twoY, secondPriceT, update_self,
      update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith
  · simp only [Fin.mk_one, linU, allocV, twoY, secondPriceT, update_self,
      update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith

/-- **Example 23.B.4** (MWG, p. 863). The auction social choice function (23.B.3)-(23.B.8) with the
seller as agent `0` and buyers `1, 2` (footnote 5), as an allocation of the good (`QLAlt`): buyer
`1` gets the good iff `θ₁ ≥ θ₂`, the winner pays his valuation to the seller. -/
noncomputable def auctionSCF (θ : Fin 3 → ℝ) : QLAlt (Fin 3) (Fin 3) :=
  ⟨(if θ 2 ≤ θ 1 then 1 else 2,
    ![θ 1 * (if θ 2 ≤ θ 1 then 1 else 0) + θ 2 * (if θ 2 ≤ θ 1 then 0 else 1),
      -(θ 1 * if θ 2 ≤ θ 1 then 1 else 0), -(θ 2 * if θ 2 ≤ θ 1 then 0 else 1)]),
    le_of_eq (by simp [Fin.sum_univ_three])⟩

/-- **Example 23.B.4** (MWG, p. 863). "`f(·)` is ex post efficient": at every profile with the
seller's valuation `θ₀ = 0` and buyers' valuations in `[0, 1]` (only `θ₁ ≥ 0` is used), no
feasible alternative (`∑ᵢ yᵢ = 1`, `∑ᵢ tᵢ ≤ 0`) makes someone better off and nobody worse off. -/
theorem example_23_B_4_auction_efficient (θ : Fin 3 → ℝ) (h0 : θ 0 = 0) (h1 : 0 ≤ θ 1) :
    ¬∃ x : QLAlt (Fin 3) (Fin 3), (∀ i, qlU goodV 0 i (auctionSCF θ).1 (θ i) ≤
      qlU goodV 0 i x.1 (θ i)) ∧ ∃ i, qlU goodV 0 i (auctionSCF θ).1 (θ i) <
        qlU goodV 0 i x.1 (θ i) := by
  rintro ⟨x, hx, j, hj⟩
  have hsum := Finset.sum_lt_sum (fun i _ => hx i) ⟨j, Finset.mem_univ j, hj⟩
  simp only [qlU, goodV, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Pi.zero_apply, zero_add] at hsum
  have hmax : ∀ k : Fin 3, θ k ≤ θ (auctionSCF θ).1.1 := by
    intro k
    simp only [auctionSCF]
    fin_cases k <;> split_ifs with h <;> simp <;> linarith
  have hx2 := x.2
  have ht : ∑ i, (auctionSCF θ).1.2 i = 0 := by simp [auctionSCF, Fin.sum_univ_three]
  linarith [hmax x.1.1]

/-! ### Example 23.B.7 and Exercise 23.B.2 -/

/-- **Example 23.B.7** (MWG, pp. 868-869). In the direct revelation mechanism for
(23.B.9)-(23.B.14), buyer `i`'s expected utility from announcing `a ∈ [0, 1]` when the other
tells the truth is `(θᵢ - a/2) Prob(θⱼ ≤ a) = (θᵢ - a/2)a`; it is maximized at `a = θᵢ`, so truth
telling is optimal, and the social choice function is Bayesian incentive compatible. -/
theorem example_23_B_7 (i : Fin 2) (θi : ℝ) :
    (∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV i (twoY (update θ' i a), firstPriceT (update θ' i a)) θi ∂unif2 =
        (θi - a / 2) * a) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, (θi - a / 2) * a ≤ (θi - θi / 2) * θi) ∧
      BayesianICOn unif2 allocV twoY firstPriceT (fun _ => 0) (fun _ => 1) := by
  have key : ∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV i (twoY (update θ' i a), firstPriceT (update θ' i a)) θi ∂unif2 =
        (θi - a / 2) * a := by
    intro a ha
    have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV i (twoY θ, firstPriceT θ) θi := by
      simp only [linU, allocV]
      refine (measurable_const.mul (measurable_twoY i)).add ?_
      fin_cases i
      · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
      · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
    rw [re_unif2_update (G := fun θ => linU allocV i (twoY θ, firstPriceT θ) θi) hm i a]
    fin_cases i
    · simp only [Fin.zero_eta, re_update_vec0, linU, allocV, firstPriceT, twoY,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have e : ∀ x : ℝ, θi * (if x ≤ a then (1 : ℝ) else 0) + -(a * (if x ≤ a then 1 else 0) / 2)
          = if x ≤ a then (θi - a / 2) + 0 * x else 0 := fun x => by split_ifs <;> ring
      simp only [e]
      rw [re_integral_ite_le ha, au_int_affine]; ring
    · simp only [Fin.mk_one, re_update_vec1, linU, allocV, firstPriceT, twoY,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have e : ∀ x : ℝ, θi * (if x < a then (1 : ℝ) else 0) + -(a * (if x < a then 1 else 0) / 2)
          = if x < a then (θi - a / 2) + 0 * x else 0 := fun x => by split_ifs <;> ring
      simp only [e]
      rw [re_integral_ite_lt ha, au_int_affine]; ring
  exact ⟨key, fun a _ => by nlinarith [sq_nonneg (a - θi)], exercise_23_D_3.1⟩

/-- **Exercise 23.B.2** (MWG, p. 918). For the social choice function `(twoY, splitT)` (the
buyer gets the good iff `θ₁ > θ₀` and pays `(θ₀ + θ₁)/2`), with the seller truthful and both
types uniform on `[0, 1]`, the buyer's expected utility from announcing `a ∈ [0, 1]` is
`∫_0^a (θ₂ - (x + a)/2) dx = θ₂a - 3a²/4`. It is maximized at `a = 2θ₂/3`, so for `θ₂ ∈ (0, 1]`
the buyer does not reveal his type: he understates his valuation to lower the price, at the
cost of trading less often (like a monopsonist). -/
theorem exercise_23_B_2 {θb : ℝ} (hθ : θb ∈ Icc (0 : ℝ) 1) :
    (∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV 1 (twoY (update θ' 1 a), splitT (update θ' 1 a)) θb ∂unif2 =
        θb * a - 3 * a ^ 2 / 4) ∧
      2 * θb / 3 ∈ Icc (0 : ℝ) 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1, θb * a - 3 * a ^ 2 / 4 ≤ θb * (2 * θb / 3) - 3 * (2 * θb / 3) ^ 2 / 4) ∧
      (0 < θb → θb * θb - 3 * θb ^ 2 / 4 < θb * (2 * θb / 3) - 3 * (2 * θb / 3) ^ 2 / 4) := by
  refine ⟨fun a ha => ?_, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩,
    fun a _ => by nlinarith [sq_nonneg (a - 2 * θb / 3)], fun h => by nlinarith⟩
  have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV 1 (twoY θ, splitT θ) θb := by
    simp only [linU, allocV, splitT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (measurable_const.mul (measurable_twoY 1)).add
      ((((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)).neg
  rw [re_unif2_update (G := fun θ => linU allocV 1 (twoY θ, splitT θ) θb) hm 1 a]
  simp only [re_update_vec1, linU, allocV, splitT, twoY, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have e : ∀ x : ℝ, θb * (if x < a then (1 : ℝ) else 0) + -((x + a) / 2 * if x < a then 1 else 0)
      = if x < a then (θb - a / 2) + (-1 / 2) * x else 0 := fun x => by split_ifs <;> ring
  simp only [e]
  rw [re_integral_ite_lt ha, au_int_affine]; ring

/-! ### Bayesian Nash equilibrium on the type space -/

/-- **Definition 23.D.1** (MWG, p. 883; used informally on p. 865) relative to a type space
`Tᵢ ⊆ Θᵢ` and a strategy space `Aᵢ ⊆ Sᵢ`: `sᵢ*(θᵢ) ∈ Aᵢ` and, for every type `θᵢ ∈ Tᵢ`, no action
in `Aᵢ` gives a higher interim expected utility than `sᵢ*(θᵢ)`. -/
def IsBNEOn {ι : Type*} [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
    {X : Type*} {S : ι → Type*} (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (s : (i : ι) → Θ i → S i)
    (T : (i : ι) → Set (Θ i)) (A : (i : ι) → Set (S i)) : Prop :=
  (∀ i, ∀ θi ∈ T i, s i θi ∈ A i) ∧ ∀ i, ∀ θi ∈ T i, ∀ a ∈ A i,
    interimUtility B u Γ s i θi a ≤ interimUtility B u Γ s i θi (s i θi)

/-! ### Example 23.B.5: the first-price sealed-bid auction -/

/-- **Example 23.B.5** (MWG, pp. 865, 867). The first-price sealed-bid auction with two bidders:
bids `bᵢ`, the highest bid wins (ties to bidder `0`, footnote 8) and the winner pays his bid,
`tᵢ = -bᵢyᵢ`. -/
noncomputable def fpMech2 : Mechanism (fun _ : Fin 2 => ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  ⟨fun b => (twoY b, fullPriceT b)⟩

/-- **Example 23.B.5** (MWG, p. 865). Linear bidding strategies `bᵢ(θᵢ) = αᵢθᵢ`. -/
def linStrat (α : Fin 2 → ℝ) : (i : Fin 2) → ℝ → ℝ := fun i θ => α i * θ

/-- **Example 23.B.5** (MWG, p. 865). If the other bidder `j` bids `αⱼθⱼ` (`αⱼ > 0`), bidder `i`
of type `θᵢ` bidding `b` has expected utility `(θᵢ - b) Prob(αⱼθⱼ ≤ b) = (θᵢ - b) clamp(b/αⱼ)`
(`clamp(b/αⱼ) = b/αⱼ` for `b ∈ [0, αⱼ]`, as in MWG's restated problem, and `1` for `b ≥ αⱼ`). -/
theorem fp_interim (α : Fin 2 → ℝ) (hα : ∀ j, 0 < α j) (i : Fin 2) (θi b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi b =
      (θi - b) * clamp01 (b / α (1 - i)) := by
  unfold interimUtility indepBeliefs
  fin_cases i
  · have e : (fun θ : Fin 2 → ℝ => linU allocV 0
        (fpMech2.outcome (update (play (linStrat α) θ) 0 b)) θi) =
        fun θ => (fun x => if x ≤ b / α 1 then (θi - b) + 0 * x else 0) (θ 1) := by
      funext θ
      simp only [fpMech2, play, linStrat, linU, allocV, twoY, fullPriceT, update_self,
        update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hiff : α 1 * θ 1 ≤ b ↔ θ 1 ≤ b / α 1 := by rw [le_div_iff₀ (hα 1), mul_comm]
      by_cases h : α 1 * θ 1 ≤ b
      · simp only [h, hiff.1 h, ↓reduceIte]; ring
      · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
    simp only [Fin.zero_eta, sub_zero]
    rw [e, au_eval (au_meas_le _ _ _) 1, au_int_le, au_int_affine]; ring
  · have e : (fun θ : Fin 2 → ℝ => linU allocV 1
        (fpMech2.outcome (update (play (linStrat α) θ) 1 b)) θi) =
        fun θ => (fun x => if x < b / α 0 then (θi - b) + 0 * x else 0) (θ 0) := by
      funext θ
      simp only [fpMech2, play, linStrat, linU, allocV, twoY, fullPriceT, update_self,
        update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hiff : α 0 * θ 0 < b ↔ θ 0 < b / α 0 := by rw [lt_div_iff₀ (hα 0), mul_comm]
      by_cases h : α 0 * θ 0 < b
      · simp only [h, hiff.1 h, ↓reduceIte]; ring
      · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
    simp only [Fin.mk_one, sub_self]
    rw [e, au_eval (au_meas_lt _ _ _) 0, au_int_lt, au_int_affine]; ring

/-- The bidder's problem of Example 23.B.5: for `α > 0` and `θ ≥ 0`, the bid
`b* = min(θ/2, α)` maximizes `(θ - b) clamp(b/α)` over `b ≥ 0`. -/
theorem fp_br_ineq {θ α b : ℝ} (hα : 0 < α) (hθ : 0 ≤ θ) (hb : 0 ≤ b) :
    (θ - b) * clamp01 (b / α) ≤ (θ - min (θ / 2) α) * clamp01 (min (θ / 2) α / α) := by
  rcases le_or_gt (θ / 2) α with h | h
  · rw [min_eq_left h, clamp01_of_mem ⟨div_nonneg (by linarith) hα.le,
      (div_le_one hα).2 h⟩]
    rcases le_or_gt b α with hb' | hb'
    · rw [clamp01_of_mem ⟨div_nonneg hb hα.le, (div_le_one hα).2 hb'⟩, mul_div_assoc',
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (b - θ / 2)]) hα.le
    · rw [clamp01_of_one_le ((one_le_div hα).2 hb'.le), mul_one, mul_div_assoc',
        le_div_iff₀ hα]
      nlinarith [sq_nonneg (θ - 2 * α)]
  · rw [min_eq_right h.le, div_self hα.ne', clamp01_of_one_le le_rfl, mul_one]
    rcases le_or_gt b α with hb' | hb'
    · rw [clamp01_of_mem ⟨div_nonneg hb hα.le, (div_le_one hα).2 hb'⟩, mul_div_assoc',
        div_le_iff₀ hα]
      nlinarith
    · rw [clamp01_of_one_le ((one_le_div hα).2 hb'.le), mul_one]; linarith

/-- **Example 23.B.5** (MWG, p. 865). If bidder `j` uses `bⱼ = αⱼθⱼ` with `αⱼ > 0`, bidder `i`'s
best response is `bᵢ(θᵢ) = θᵢ/2` if `θᵢ/2 ≤ αⱼ` and `αⱼ` if `θᵢ/2 > αⱼ` (for `θᵢ ≥ 0`); on
`[0, αⱼ]` his objective is MWG's `(θᵢ - bᵢ)(bᵢ/αⱼ)`. -/
theorem example_23_B_5_bestResponse (α : Fin 2 → ℝ) (hα : ∀ j, 0 < α j) (i : Fin 2)
    {θi : ℝ} (hθ : 0 ≤ θi) :
    (∀ b ∈ Icc 0 (α (1 - i)), interimUtility (indepBeliefs unif2) (linU allocV) fpMech2
      (linStrat α) i θi b = (θi - b) * (b / α (1 - i))) ∧
    0 ≤ min (θi / 2) (α (1 - i)) ∧
    ∀ b, 0 ≤ b → interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi b ≤
      interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi
        (min (θi / 2) (α (1 - i))) := by
  refine ⟨fun b hb => ?_, le_min (by linarith) (hα _).le, fun b hb => ?_⟩
  · rw [fp_interim α hα, clamp01_of_mem ⟨div_nonneg hb.1 (hα _).le,
      (div_le_one (hα _)).2 hb.2⟩]
  · rw [fp_interim α hα, fp_interim α hα]
    exact fp_br_ineq (hα _) hθ hb

/-- **Example 23.B.5** (MWG, pp. 865-866). With two bidders whose valuations are independent and
uniform on `[0, 1]`, `bᵢ(θᵢ) = θᵢ/2` is a Bayesian Nash equilibrium of the first-price
sealed-bid auction (for types in `[0, 1]` and bids `b ≥ 0`), and it yields the outcomes of the
social choice function (23.B.9)-(23.B.14) (`twoY`, `firstPriceT`): the auction implements it
(Definition 23.B.4). -/
theorem example_23_B_5 :
    IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat fun _ => 1 / 2)
      (fun _ => Icc 0 1) (fun _ => Ici 0) ∧
    (∀ θ, fpMech2.outcome (play (linStrat fun _ => 1 / 2) θ) = (twoY θ, firstPriceT θ)) ∧
    Implements {s | IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 s (fun _ => Icc 0 1)
      (fun _ => Ici 0)} fpMech2 fun θ => (twoY θ, firstPriceT θ) := by
  have hα : ∀ j : Fin 2, (0 : ℝ) < (fun _ => 1 / 2) j := fun _ => by norm_num
  have hbne : IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat fun _ => 1 / 2)
      (fun _ => Icc 0 1) (fun _ => Ici 0) := by
    refine ⟨fun i θi hθ => ?_, fun i θi hθ b hb => ?_⟩
    · simp only [linStrat, mem_Ici]; linarith [hθ.1]
    · have hmin : min (θi / 2) ((fun _ : Fin 2 => (1 : ℝ) / 2) (1 - i)) = linStrat
          (fun _ => 1 / 2) i θi := by
        simp only [linStrat]; rw [min_eq_left (by linarith [hθ.2])]; ring
      have := (example_23_B_5_bestResponse _ hα i hθ.1).2.2 b hb
      rwa [hmin] at this
  have hout : ∀ θ, fpMech2.outcome (play (linStrat fun _ => 1 / 2) θ) =
      (twoY θ, firstPriceT θ) := by
    intro θ
    have hy : twoY (play (linStrat fun _ => 1 / 2) θ) = twoY θ := by
      funext j
      fin_cases j <;> simp [twoY, play, linStrat]
    simp only [fpMech2, hy, Prod.mk.injEq, true_and]
    funext j
    simp only [fullPriceT, firstPriceT, hy]
    fin_cases j <;> simp [play, linStrat] <;> ring
  exact ⟨hbne, hout, ⟨_, hbne, hout⟩⟩

/-! ### Sealed-bid auctions with any number of bidders (p. 867) -/

/-- Some bidder makes the highest bid. -/
theorem au_maxSet_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] (b : ι → ℝ) :
    (Finset.univ.filter fun i => ∀ j, b j ≤ b i).Nonempty := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j => hi j (Finset.mem_univ j)⟩⟩

/-- **Section 23.B** (MWG, p. 867, footnotes 8 and 10). The winner of a sealed-bid auction: the
lowest-numbered of the highest bidders, `min{j : bⱼ = max{b₁, …, b_I}}`. -/
noncomputable def auctionWinner {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) : ι :=
  (Finset.univ.filter fun i => ∀ j, b j ≤ b i).min' (au_maxSet_nonempty b)

/-- The winner makes a highest bid. -/
theorem auctionWinner_max {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (b : ι → ℝ)
    (j : ι) : b j ≤ b (auctionWinner b) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (au_maxSet_nonempty b))).2 j

/-- The winner has the lowest index among the highest bidders. -/
theorem auctionWinner_le {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (b : ι → ℝ)
    {i : ι} (hi : ∀ j, b j ≤ b i) : auctionWinner b ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)

/-- A strictly highest bidder wins. -/
theorem auctionWinner_eq_of_gt {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) {i : ι} (hi : ∀ j, j ≠ i → b j < b i) : auctionWinner b = i := by
  by_contra hne
  exact absurd (auctionWinner_max b i) (not_le.2 (hi _ hne))

/-- With two bidders, bidder `0` wins iff `b₁ ≤ b₀`. -/
theorem auctionWinner_fin_two (b : Fin 2 → ℝ) :
    auctionWinner b = if b 1 ≤ b 0 then 0 else 1 := by
  split_ifs with h
  · refine le_antisymm (auctionWinner_le b fun j => ?_) (Fin.zero_le _)
    fin_cases j
    · exact le_rfl
    · exact h
  · refine auctionWinner_eq_of_gt b fun j hj => ?_
    fin_cases j
    · exact not_le.1 h
    · exact absurd rfl hj

/-- The other bidders are a nonempty set when there are at least two bidders. -/
theorem au_erase_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (i : ι) :
    (Finset.univ.erase i).Nonempty :=
  let ⟨j, hj⟩ := exists_ne i
  ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩⟩

/-- The highest bid of the bidders other than `i`, `max{bⱼ : j ≠ i}`. -/
noncomputable def othersMax {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (b : ι → ℝ) (i : ι) : ℝ :=
  (Finset.univ.erase i).sup' (au_erase_nonempty i) b

/-- With two bidders, the other bid is the highest other bid. -/
theorem othersMax_fin_two (b : Fin 2 → ℝ) : othersMax b 0 = b 1 ∧ othersMax b 1 = b 0 := by
  refine ⟨le_antisymm (Finset.sup'_le _ _ fun j hj => ?_)
    (Finset.le_sup' b (Finset.mem_erase.2 ⟨by decide, Finset.mem_univ _⟩)),
    le_antisymm (Finset.sup'_le _ _ fun j hj => ?_)
    (Finset.le_sup' b (Finset.mem_erase.2 ⟨by decide, Finset.mem_univ _⟩))⟩
  · fin_cases j
    · exact absurd rfl (Finset.ne_of_mem_erase hj)
    · exact le_rfl
  · fin_cases j
    · exact le_rfl
    · exact absurd rfl (Finset.ne_of_mem_erase hj)

/-- **Section 23.B** (MWG, p. 867). The outcome function of the first-price sealed-bid auction:
the winner `min{j : bⱼ = max b}` gets the good and pays his bid, `tᵢ = -bᵢyᵢ`. An outcome is the
winner and the transfers. -/
noncomputable def firstPriceOutcome {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) : ι × (ι → ℝ) :=
  (auctionWinner b, fun j => if auctionWinner b = j then -b j else 0)

/-- **Section 23.B** (MWG, p. 867). The outcome function of the second-price sealed-bid auction:
the same winner pays the highest other bid, `tᵢ = -max{bⱼ : j ≠ i} yᵢ`. -/
noncomputable def secondPriceOutcome {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    [Nontrivial ι] (b : ι → ℝ) : ι × (ι → ℝ) :=
  (auctionWinner b, fun j => if auctionWinner b = j then -othersMax b j else 0)

/-- Buyer `i`'s utility `θᵢyᵢ + tᵢ` when the outcome is (winner, transfers). -/
def winU {ι : Type*} [DecidableEq ι] : (i : ι) → ι × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => (if x.1 = i then θi else 0) + x.2 i

/-- With two bidders, the first-price outcome function is `fpMech2`'s: bidder `i` wins iff
`twoY b i = 1`, and pays `-fullPriceT b i`. -/
theorem firstPriceOutcome_fin_two (b : Fin 2 → ℝ) (i : Fin 2) :
    twoY b i = (if (firstPriceOutcome b).1 = i then 1 else 0) ∧
      fullPriceT b i = (firstPriceOutcome b).2 i := by
  simp only [firstPriceOutcome, auctionWinner_fin_two]
  fin_cases i <;> by_cases h : b 1 ≤ b 0 <;>
    simp [h, twoY, fullPriceT, not_le.1]

/-- **Exercise 23.B.3** (MWG, p. 918), the core: in the second-price sealed-bid auction with any
number `I ≥ 2` of bidders, bidding one's valuation is weakly dominant: whatever (real) bids the
others make, no bid gives bidder `i` a higher utility than `bᵢ = θᵢ`. -/
theorem sp_truth_dominant {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι]
    (i : ι) (θi a : ℝ) (σ : ι → ℝ) :
    winU i (secondPriceOutcome (update σ i a)) θi ≤
      winU i (secondPriceOutcome (update σ i θi)) θi := by
  have hm : ∀ β, othersMax (update σ i β) i = othersMax σ i := fun β =>
    Finset.sup'_congr _ rfl fun j hj => update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hpay : ∀ β, winU i (secondPriceOutcome (update σ i β)) θi =
      if auctionWinner (update σ i β) = i then θi - othersMax σ i else 0 := by
    intro β
    simp only [winU, secondPriceOutcome, hm]
    by_cases h : auctionWinner (update σ i β) = i
    · simp only [h, ↓reduceIte]; ring
    · simp [h]
  have hA : ∀ β, auctionWinner (update σ i β) = i → othersMax σ i ≤ β := by
    intro β h
    rw [← hm β]
    refine Finset.sup'_le _ _ fun j _ => ?_
    have := auctionWinner_max (update σ i β) j
    rwa [h, update_self] at this
  have hB : ∀ β, othersMax σ i < β → auctionWinner (update σ i β) = i := by
    intro β h
    refine auctionWinner_eq_of_gt _ fun j hj => ?_
    rw [update_of_ne hj, update_self]
    exact lt_of_le_of_lt (Finset.le_sup' σ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)) h
  rw [hpay, hpay]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · by_contra hlt
    exact h2 (hB θi (by linarith))
  · linarith [hA θi h2]
  · exact le_rfl

/-- **Example 23.B.6** (MWG, p. 866). The second-price sealed-bid auction with MWG's spaces:
types `θᵢ ∈ [0, 1]`, bids `bᵢ ≥ 0`. -/
noncomputable def spMech (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι] :
    Mechanism (fun _ : ι => ↥(Ici (0 : ℝ))) (ι × (ι → ℝ)) :=
  ⟨fun b => secondPriceOutcome fun j => (b j : ℝ)⟩

/-- Bid your valuation: `bᵢ(θᵢ) = θᵢ`. -/
def bidValue (ι : Type*) : (i : ι) → ↥(Icc (0 : ℝ) 1) → ↥(Ici (0 : ℝ)) :=
  fun _ θ => ⟨θ, θ.2.1⟩

/-- **Exercise 23.B.3** (MWG, p. 918) and **Example 23.B.6** (p. 866). In the second-price
sealed-bid auction with `I ≥ 2` bidders, valuations `θᵢ ∈ [0, 1]` and bids `bᵢ ≥ 0`, bidding
`bᵢ(θᵢ) = θᵢ` is a weakly dominant strategy for every bidder: truth telling is a dominant
strategy equilibrium. -/
theorem exercise_23_B_3 (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι] :
    IsDominantStrategyEquilibrium (fun i x (θi : ↥(Icc (0 : ℝ) 1)) => winU i x (θi : ℝ))
      (spMech ι) (bidValue ι) := by
  intro i θi s' σ
  have e : ∀ c : ↥(Ici (0 : ℝ)), (fun j => ((update σ i c j : ↥(Ici (0 : ℝ))) : ℝ)) =
      update (fun j => (σ j : ℝ)) i (c : ℝ) := by
    intro c
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simp only [spMech, bidValue, e]
  exact sp_truth_dominant i _ _ _

/-- **Example 23.B.6** (MWG, p. 866). With two bidders, the second-price sealed-bid auction
implements in dominant strategies the second-price social choice function: bidder `0` gets the
good iff `θ₁ ≤ θ₀`, and the winner pays the other's valuation (`secondPriceT`). -/
theorem example_23_B_6 :
    ImplementsInDominantStrategies (fun i x (θi : ↥(Icc (0 : ℝ) 1)) => winU i x (θi : ℝ))
      (spMech (Fin 2)) fun θ => (if (θ 1 : ℝ) ≤ θ 0 then 0 else 1,
        secondPriceT fun j => (θ j : ℝ)) := by
  refine ⟨bidValue (Fin 2), exercise_23_B_3 (Fin 2), fun θ => ?_⟩
  obtain ⟨h0, h1⟩ := othersMax_fin_two fun j => (θ j : ℝ)
  simp only [spMech, play, bidValue, secondPriceOutcome, auctionWinner_fin_two, Prod.mk.injEq]
  refine ⟨rfl, funext fun j => ?_⟩
  fin_cases j <;> rcases le_or_gt (θ 1 : ℝ) (θ 0) with h | h
  · simp [h, h0, secondPriceT, twoY]
  · simp [h, not_le.2 h, secondPriceT, twoY]
  · simp [h, not_lt.2 h, secondPriceT, twoY]
  · simp [h, not_le.2 h, h1, secondPriceT, twoY]

/-! ### Exercise 23.B.4: the double auction -/

/-- `x ↦ 1{τ < x}(A + Bx)` is interval integrable on `[0, 1]`. -/
theorem au_ii_gt (τ A B : ℝ) :
    IntervalIntegrable (fun x : ℝ => if τ < x then A + B * x else 0) volume 0 1 := by
  have h : (fun x : ℝ => if τ < x then A + B * x else 0) =
      (Ioi τ).indicator fun x => A + B * x := by
    funext x; simp [indicator_apply]
  rw [h, intervalIntegrable_iff]
  exact ((by fun_prop : Continuous fun x : ℝ => A + B * x).intervalIntegrable 0 1).def'.indicator
    measurableSet_Ioi

/-- **Exercise 23.B.4** (MWG, p. 918). The double auction: the seller (agent `0`) and the buyer
(agent `1`) submit bids; if `b₀ ≥ b₁` the seller keeps the good and no transfer is made, if
`b₁ > b₀` the buyer gets the good and pays the seller `(b₀ + b₁)/2` (`twoY`, `splitT`). -/
noncomputable def daMech : Mechanism (fun _ : Fin 2 => ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  ⟨fun b => (twoY b, splitT b)⟩

/-- **Exercise 23.B.4(a)**. The seller's expected utility from bidding `b` when the buyer bids
`p + qθ₁` (`q > 0`): `θ₀ + ((b + p)/2 - θ₀)(1 - c) + (q/4)(1 - c²)`, `c = clamp((b - p)/q)`. -/
theorem da_seller_interim (s : (i : Fin 2) → ℝ → ℝ) {p q : ℝ} (hq : 0 < q)
    (hs : ∀ x, s 1 x = p + q * x) (θ0 b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) daMech s 0 θ0 b =
      θ0 + ((b + p) / 2 - θ0) * (1 - clamp01 ((b - p) / q)) +
        q / 4 * (1 - clamp01 ((b - p) / q) ^ 2) := by
  unfold interimUtility indepBeliefs
  have e : (fun θ : Fin 2 → ℝ => linU allocV 0 (daMech.outcome (update (play s θ) 0 b)) θ0) =
      fun θ => (fun x => θ0 + if (b - p) / q < x then ((b + p) / 2 - θ0) + q / 2 * x else 0)
        (θ 1) := by
    funext θ
    simp only [daMech, play, linU, allocV, twoY, splitT, update_self,
      update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hs]
    have hiff : b < p + q * θ 1 ↔ (b - p) / q < θ 1 := by
      rw [div_lt_iff₀ hq]; constructor <;> intro h <;> linarith
    by_cases h : b < p + q * θ 1
    · simp only [h, hiff.1 h, not_le.2 h, ↓reduceIte]; ring
    · simp only [h, mt hiff.2 h, not_lt.1 h, ↓reduceIte]; ring
  rw [e, au_eval (H := fun x => θ0 + if (b - p) / q < x then ((b + p) / 2 - θ0) + q / 2 * x
      else 0) (measurable_const.add (au_meas_gt _ _ _)) 1,
    intervalIntegral.integral_add intervalIntegrable_const (au_ii_gt _ _ _),
    intervalIntegral.integral_const, au_int_gt, au_int_affine, smul_eq_mul]
  ring

/-- **Exercise 23.B.4(a)**. The buyer's expected utility from bidding `b` when the seller bids
`p + qθ₀` (`q > 0`): `(θ₁ - (p + b)/2)c - (q/4)c²`, `c = clamp((b - p)/q)`. -/
theorem da_buyer_interim (s : (i : Fin 2) → ℝ → ℝ) {p q : ℝ} (hq : 0 < q)
    (hs : ∀ x, s 0 x = p + q * x) (θ1 b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) daMech s 1 θ1 b =
      (θ1 - (p + b) / 2) * clamp01 ((b - p) / q) - q / 4 * clamp01 ((b - p) / q) ^ 2 := by
  unfold interimUtility indepBeliefs
  have e : (fun θ : Fin 2 → ℝ => linU allocV 1 (daMech.outcome (update (play s θ) 1 b)) θ1) =
      fun θ => (fun x => if x < (b - p) / q then (θ1 - (p + b) / 2) + (-(q / 2)) * x else 0)
        (θ 0) := by
    funext θ
    simp only [daMech, play, linU, allocV, twoY, splitT, update_self,
      update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hs]
    have hiff : p + q * θ 0 < b ↔ θ 0 < (b - p) / q := by
      rw [lt_div_iff₀ hq]; constructor <;> intro h <;> linarith
    by_cases h : p + q * θ 0 < b
    · simp only [h, hiff.1 h, ↓reduceIte]; ring
    · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
  rw [e, au_eval (au_meas_lt _ _ _) 0, au_int_lt, au_int_affine]
  ring

/-- **Exercise 23.B.4(a)**. The seller's optimal bid against `b₁ = 2θ₁/3 + 1/12` is
`2θ₀/3 + 1/4` (for `θ₀ ∈ [0, 1]`; when `θ₀ > 3/4` this bid never trades, which is optimal). -/
theorem da_seller_ineq {θ0 : ℝ} (hθ : θ0 ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    θ0 + ((b + 1 / 12) / 2 - θ0) * (1 - clamp01 ((b - 1 / 12) / (2 / 3))) +
        2 / 3 / 4 * (1 - clamp01 ((b - 1 / 12) / (2 / 3)) ^ 2) ≤
      θ0 + ((2 / 3 * θ0 + 1 / 4 + 1 / 12) / 2 - θ0) *
          (1 - clamp01 ((2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3))) +
        2 / 3 / 4 * (1 - clamp01 ((2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3)) ^ 2) := by
  obtain ⟨h0, h1⟩ := hθ
  have e1 : (2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3) = θ0 + 1 / 4 := by ring
  have e2 : (2 / 3 * θ0 + 1 / 4 + 1 / 12) / 2 = (θ0 + 1 / 4) / 3 + 1 / 12 := by ring
  have e3 : (b + 1 / 12) / 2 = (b - 1 / 12) / (2 / 3) / 3 + 1 / 12 := by ring
  rw [e1, e2, e3]
  generalize (b - 1 / 12) / (2 / 3) = t
  rcases le_or_gt θ0 (3 / 4) with hθ' | hθ'
  · rw [clamp01_of_mem (τ := θ0 + 1 / 4) ⟨by linarith, by linarith⟩]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - (θ0 + 1 / 4))]
      · rw [clamp01_of_one_le h'.le]; nlinarith [sq_nonneg (θ0 - 3 / 4)]
  · rw [clamp01_of_one_le (τ := θ0 + 1 / 4) (by linarith)]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - 1)]
      · rw [clamp01_of_one_le h'.le]; nlinarith

/-- **Exercise 23.B.4(a)**. The buyer's optimal bid against `b₀ = 2θ₀/3 + 1/4` is
`2θ₁/3 + 1/12` (for `θ₁ ∈ [0, 1]`; when `θ₁ < 1/4` this bid never trades, which is optimal). -/
theorem da_buyer_ineq {θ1 : ℝ} (hθ : θ1 ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    (θ1 - (1 / 4 + b) / 2) * clamp01 ((b - 1 / 4) / (2 / 3)) -
        2 / 3 / 4 * clamp01 ((b - 1 / 4) / (2 / 3)) ^ 2 ≤
      (θ1 - (1 / 4 + (2 / 3 * θ1 + 1 / 12)) / 2) *
          clamp01 ((2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3)) -
        2 / 3 / 4 * clamp01 ((2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3)) ^ 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have e1 : (2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3) = θ1 - 1 / 4 := by ring
  have e2 : (1 / 4 + (2 / 3 * θ1 + 1 / 12)) / 2 = 1 / 4 + (θ1 - 1 / 4) / 3 := by ring
  have e3 : (1 / 4 + b) / 2 = 1 / 4 + (b - 1 / 4) / (2 / 3) / 3 := by ring
  rw [e1, e2, e3]
  generalize (b - 1 / 4) / (2 / 3) = t
  rcases le_or_gt (1 / 4) θ1 with hθ' | hθ'
  · rw [clamp01_of_mem (τ := θ1 - 1 / 4) ⟨by linarith, by linarith⟩]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - (θ1 - 1 / 4))]
      · rw [clamp01_of_one_le h'.le]; nlinarith [sq_nonneg (θ1 - 5 / 4)]
  · rw [clamp01_of_nonpos (τ := θ1 - 1 / 4) (by linarith)]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith
      · rw [clamp01_of_one_le h'.le]; nlinarith

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The linear (Chatterjee-Samuelson) strategies
`b₀(θ₀) = 2θ₀/3 + 1/4`, `b₁(θ₁) = 2θ₁/3 + 1/12`. -/
noncomputable def daStrat : (i : Fin 2) → ℝ → ℝ := fun i θ => 2 / 3 * θ + ![1 / 4, 1 / 12] i

/-- **Exercise 23.B.4(a)** (MWG, p. 918). With both types uniform on `[0, 1]`, the linear
strategies `b₀ = 2θ₀/3 + 1/4`, `b₁ = 2θ₁/3 + 1/12` (`αᵢ + βᵢθᵢ` with `β = 2/3`) form a Bayesian
Nash equilibrium of the double auction (types in `[0, 1]`, bids `b ≥ 0`). -/
theorem exercise_23_B_4a :
    IsBNEOn (indepBeliefs unif2) (linU allocV) daMech daStrat (fun _ => Icc 0 1)
      (fun _ => Ici 0) := by
  refine ⟨fun i θi hθ => ?_, fun i θi hθ b _ => ?_⟩
  · fin_cases i <;> simp [daStrat] <;> linarith [hθ.1]
  · fin_cases i
    · have hs : ∀ x, daStrat 1 x = 1 / 12 + 2 / 3 * x := fun x => by simp [daStrat]; ring
      have h0 : daStrat 0 θi = 2 / 3 * θi + 1 / 4 := by simp [daStrat]
      simp only [Fin.zero_eta]
      rw [da_seller_interim daStrat (by norm_num) hs, da_seller_interim daStrat (by norm_num) hs,
        h0]
      exact da_seller_ineq hθ b
    · have hs : ∀ x, daStrat 0 x = 1 / 4 + 2 / 3 * x := fun x => by simp [daStrat]; ring
      have h1 : daStrat 1 θi = 2 / 3 * θi + 1 / 12 := by simp [daStrat]
      simp only [Fin.mk_one]
      rw [da_buyer_interim daStrat (by norm_num) hs, da_buyer_interim daStrat (by norm_num) hs,
        h1]
      exact da_buyer_ineq hθ b

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The social choice function implemented by this
equilibrium: trade iff `θ₁ > θ₀ + 1/4` (MWG: `θ₂ > θ₁ + 1/4`), at the price
`(b₀ + b₁)/2 = (θ₀ + θ₁)/3 + 1/6`. -/
theorem exercise_23_B_4a_outcome (θ : Fin 2 → ℝ) :
    daMech.outcome (play daStrat θ) =
      (![if θ 1 ≤ θ 0 + 1 / 4 then 1 else 0, if θ 0 + 1 / 4 < θ 1 then 1 else 0],
        ![((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0),
          -(((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0))]) := by
  have hiff : 2 / 3 * θ 0 + 1 / 4 < 2 / 3 * θ 1 + 1 / 12 ↔ θ 0 + 1 / 4 < θ 1 := by
    constructor <;> intro h <;> linarith
  have hiff' : 2 / 3 * θ 1 + 1 / 12 ≤ 2 / 3 * θ 0 + 1 / 4 ↔ θ 1 ≤ θ 0 + 1 / 4 := by
    constructor <;> intro h <;> linarith
  simp only [daMech, play, daStrat, twoY, splitT, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hiff, hiff', Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  funext j
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> ring

/-- **Exercise 23.B.4(a)**. The double auction's equilibrium social choice function as an
allocation of the single good (Example 23.B.4): the good ends with the buyer iff
`θ₁ > θ₀ + 1/4`, and the transfers balance. -/
noncomputable def daQL (θ : Fin 2 → ℝ) : QLAlt (Fin 2) (Fin 2) :=
  ⟨(if θ 0 + 1 / 4 < θ 1 then 1 else 0,
    ![((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0),
      -(((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0))]), by simp⟩

/-- `daQL` represents the outcomes of the double auction equilibrium: every agent's utility is
the same in both representations. -/
theorem daQL_utility (θ : Fin 2 → ℝ) (i : Fin 2) (θi : ℝ) :
    qlU goodV 0 i (daQL θ).1 θi = linU allocV i (daMech.outcome (play daStrat θ)) θi := by
  rw [exercise_23_B_4a_outcome]
  fin_cases i <;> simp [qlU, goodV, linU, allocV, daQL]

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The social choice function implemented by the double
auction equilibrium is not ex post efficient: at `θ = (0, 1/8)` the buyer values the good more
than the seller, but there is no trade. -/
theorem exercise_23_B_4a_not_efficient :
    ¬ExPostEfficient (Θ := fun _ : Fin 2 => ℝ)
      (fun i (x : QLAlt (Fin 2) (Fin 2)) θi => qlU goodV 0 i x.1 θi) daQL := by
  rw [example_23_B_4_efficient_iff]
  rintro ⟨h, -⟩
  have hs : Finset.univ.sup' Finset.univ_nonempty (![0, 1 / 8] : Fin 2 → ℝ) = 1 / 8 := by
    refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) ?_
    · fin_cases j <;> norm_num
    · exact Finset.le_sup' (![0, 1 / 8] : Fin 2 → ℝ) (Finset.mem_univ 1)
  have := h ![0, 1 / 8] 0
  rw [hs] at this
  norm_num [daQL] at this

/-- **Exercise 23.B.4(b)** (MWG, p. 918). The social choice function implemented by the double
auction equilibrium (trade iff `θ₁ > θ₀ + 1/4` at price `(θ₀ + θ₁)/3 + 1/6`) is Bayesian
incentive compatible: reporting `θ̂ᵢ` in its direct mechanism is bidding `bᵢ(θ̂ᵢ)` in the double
auction, and the equilibrium bid `bᵢ(θᵢ)` is optimal (the revelation principle). -/
theorem exercise_23_B_4b :
    BayesianICOn unif2 allocV (fun θ => twoY (play daStrat θ)) (fun θ => splitT (play daStrat θ))
      (fun _ => 0) (fun _ => 1) := by
  intro i θi hθi θh hθh
  have hplay : ∀ (θ' : Fin 2 → ℝ) c,
      play daStrat (update θ' i c) = update (play daStrat θ') i (daStrat i c) := by
    intro θ' c
    funext j
    by_cases hj : j = i
    · subst hj; simp [play]
    · simp [play, update_of_ne hj]
  have hnn : daStrat i θh ∈ Ici (0 : ℝ) := exercise_23_B_4a.1 i θh hθh
  have := exercise_23_B_4a.2 i θi hθi (daStrat i θh) hnn
  simp only [interimUtility, indepBeliefs, daMech] at this
  simp only [hplay]
  exact this

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The differentiable case of dominant strategy implementation

MWG, Section 23.C, "The differentiable case", pp. 881-882 (with footnote 26), and Exercises
23.C.9 and 23.C.10(c)-(d) (p. 920).

`K = ℝ`; agent `i`'s valuation `vᵢ(k, θᵢ)` has continuous partial derivatives `∂vᵢ/∂k`,
`∂²vᵢ/∂k²`, `∂²vᵢ/∂k∂θᵢ` with `∂²vᵢ/∂k² < 0` and `∂²vᵢ/∂k∂θᵢ ≠ 0` (`SmallTypeEnv`); types lie
in boxes `θᵢ ∈ [θ̲ᵢ, θ̄ᵢ]`. A profile is `θ : ι → ℝ`, and the derivative of a function of `θ` with
respect to `θᵢ` is the derivative of its slice `s ↦ g(update θ i s)`.

* (23.C.13) `eq_23_C_13`: the first-order condition of truth telling at interior types.
* (23.C.14) `eq_23_C_14`: the transfer formula, by the fundamental theorem of calculus.
* (23.C.15) `eq_23_C_15`: the first-order condition of an efficient project rule.
* Implicit function theorem (p. 882): an efficient `k*` is differentiable in each `θᵢ` at interior
  types, continuous along each coordinate of the box, and `∂k*/∂θᵢ ≠ 0`
  (`efficient_slice_hasDerivAt`, `efficient_slice_continuousOn`, `efficient_slice_deriv_ne_zero`);
  proved with Mathlib's bivariate implicit function theorem.
* The Groves form (p. 882): a strategy-proof `f = (k*, t)` with efficient `k*` and differentiable
  transfers has `tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k*(θ), θⱼ) - ∑_{j≠i} vⱼ(k*(θ̲ᵢ, θ₋ᵢ), θⱼ)`
  (`differentiable_case_groves`), so it is a Groves mechanism, and conversely
  (`differentiable_case_groves_iff`). Footnote 26 (any differentiable `k*`):
  `footnote_23_26`. The proof shows that `tᵢ - ∑_{j≠i} vⱼ(k*(·), θⱼ)` has zero `θᵢ`-derivative.
* Budget balance with `I = 2` (p. 882): impossible (`differentiable_case_no_budget_balance`).
* **Exercise 23.C.9**: with `∂²v/∂k∂θ > 0`, a `C¹` social choice function is strategy-proof iff
  `k` is nondecreasing in each `θᵢ` and the transfers satisfy the integral formula
  (`exercise_23_C_9`).
* **Exercise 23.C.10(c)**: for `I = 2`, `V* = V₁(θ₂) + V₂(θ₁)` forces `∂²V*/∂θ₁∂θ₂ = 0`
  (`exercise_23_C_10c`), and conversely (`exercise_23_C_10c_sufficient`); in the differentiable
  case an efficient, budget balanced, strategy-proof rule forces `V* = ∑ᵢ Vᵢ(θ₋ᵢ)` for any `I ≥ 2`
  (`exercise_23_C_10c_decomposition`); the `I`-fold finite-difference form is
  `mixedDifference_eq_zero`. **(d)**: `exercise_23_C_10d`.

**Departures.** (1) Valuations, the project rule and the transfers are functions on all of `ℝ`
(resp. `ℝ^I`); the box enters through strategy-proofness and efficiency, which are required only
on the box. (2) The `I = 2` impossibility is proved through the decomposition
`V*(θ) = -h₁(θ₂) - h₂(θ₁)` and a strictly nonzero mixed *difference* of `V*`, not through
(23.C.16)-(23.C.17): those take second derivatives of `tᵢ` and `k*`, which need more smoothness
than MWG assume (`f` is only `C¹`, and the implicit function theorem gives `k*` only `C¹` when
`v` is `C²`). Exercise 23.C.10(d) is proved the same way (the finite-difference form of (c)).
(3) Exercise 23.C.9 does not need `∂²v/∂k² < 0`, and its "only if" for monotonicity needs no
differentiability.
-/

namespace MWG.MechanismDesign

open Function Finset

open scoped Topology

/-! ## One-dimensional lemmas -/

/-- **(23.C.13)**, one-dimensional form (MWG, p. 881). If reporting `r ∈ [a, b]` is never better
than reporting the true type `s ∈ (a, b)`, and `k`, `t` are differentiable at `s`, then
`∂v(k(s), s)/∂k · k'(s) + t'(s) = 0`. -/
theorem dc_foc_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {k t : ℝ → ℝ} {a b s k' t' : ℝ}
    (hIC : ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) (hs : s ∈ Set.Ioo a b)
    (hk : HasDerivAt k k' s) (ht : HasDerivAt t t' s) : vk (k s) s * k' + t' = 0 := by
  have hmax : IsLocalMax (fun r => v (k r) s + t r) s :=
    Filter.eventually_of_mem (Icc_mem_nhds hs.1 hs.2) fun r hr => hIC r hr
  exact hmax.hasDerivAt_eq_zero (((hv (k s) s).comp s hk).add ht)

/-- **(23.C.14)**, one-dimensional form (MWG, p. 881). For a `C¹` slice `(k, t)` along which
truth telling is optimal on `[a, b]`, `t(θ) = t(a) - ∫ₐ^θ ∂v(k(s), s)/∂k · k'(s) ds`. -/
theorem dc_integral_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x)
    (hcvk : Continuous fun p : ℝ × ℝ => vk p.1 p.2) {k t : ℝ → ℝ} {a b : ℝ}
    (hk : ContDiff ℝ 1 k) (ht : ContDiff ℝ 1 t)
    (hIC : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) :
    ∀ θ ∈ Set.Icc a b, t θ = t a - ∫ s in a..θ, vk (k s) s * deriv k s := by
  intro θ hθ
  have hg : Continuous fun s => vk (k s) s * deriv k s :=
    (hcvk.comp (hk.continuous.prodMk continuous_id)).mul (hk.continuous_deriv_one)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := t)
    (f' := fun s => -(vk (k s) s * deriv k s)) hθ.1 ht.continuous.continuousOn
    (fun x hx => ?_) (hg.neg.intervalIntegrable _ _)
  · rw [intervalIntegral.integral_neg] at hint
    linarith
  · have hx' : x ∈ Set.Ioo a b := ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩
    have hkd := (hk.differentiable (by norm_num) x).hasDerivAt
    have htd := (ht.differentiable (by norm_num) x).hasDerivAt
    have hfoc := dc_foc_slice hv (hIC x (Set.Ioo_subset_Icc_self hx')) hx' hkd htd
    have : deriv t x = -(vk (k x) x * deriv k x) := by linarith
    rw [← this]
    exact htd

/-- A function monotone on `[a, b]` (`a < b`) and differentiable at `x ∈ [a, b]` has
`f'(x) ≥ 0`. -/
theorem dc_deriv_nonneg_of_monotoneOn {k : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hm : MonotoneOn k (Set.Icc a b)) (hx : x ∈ Set.Icc a b) (hd : DifferentiableAt ℝ k x) :
    0 ≤ deriv k x := by
  rw [← hd.derivWithin (uniqueDiffOn_Icc hab x hx)]
  exact hm.derivWithin_nonneg

/-- **Exercise 23.C.9**, one-dimensional form (MWG, p. 920). Let `∂v/∂k` be continuous and
strictly increasing in `θ` on `[a, b]`, and let `k`, `t` be `C¹`. Truth telling is optimal on
`[a, b]` iff `k` is nondecreasing on `[a, b]` and
`t(θ) = t(a) - ∫ₐ^θ ∂v(k(s), s)/∂k · k'(s) ds` on `[a, b]`. -/
theorem dc_sp_slice_iff {v vk : ℝ → ℝ → ℝ} {a b : ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x)
    (hcvk : Continuous fun p : ℝ × ℝ => vk p.1 p.2)
    (hmono : ∀ x, StrictMonoOn (vk x) (Set.Icc a b)) {k t : ℝ → ℝ}
    (hk : ContDiff ℝ 1 k) (ht : ContDiff ℝ 1 t) :
    (∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) ↔
      MonotoneOn k (Set.Icc a b) ∧
        ∀ θ ∈ Set.Icc a b, t θ = t a - ∫ s in a..θ, vk (k s) s * deriv k s := by
  constructor
  · intro hIC
    refine ⟨fun s hs r hr hsr => ?_, dc_integral_slice hv hcvk hk ht hIC⟩
    rcases hsr.lt_or_eq with hlt | heq
    · by_contra hcon
      rw [not_le] at hcon
      -- `φ(x) = v(x, r) - v(x, s)` is strictly increasing
      have hφ : StrictMono fun x => v x r - v x s := by
        apply strictMono_of_deriv_pos
        intro x
        rw [((hv x r).fun_sub (hv x s)).deriv]
        exact sub_pos.2 (hmono x hs hr hlt)
      have h1 := hIC s hs r hr
      have h2 := hIC r hr s hs
      have h3 := hφ hcon
      simp only at h3
      linarith
    · rw [heq]
  · rintro ⟨hm, hform⟩ s hs r hr
    have hg : Continuous fun x => vk (k x) x * deriv k x :=
      (hcvk.comp (hk.continuous.prodMk continuous_id)).mul (hk.continuous_deriv_one)
    have hgs : Continuous fun x => vk (k x) s * deriv k x :=
      (hcvk.comp (hk.continuous.prodMk continuous_const)).mul (hk.continuous_deriv_one)
    -- `v(k(s), s) - v(k(r), s) = ∫_r^s ∂v(k(x), s)/∂k · k'(x) dx`
    have hv_int : ∫ x in r..s, vk (k x) s * deriv k x = v (k s) s - v (k r) s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => v (k x) s)
        (fun x _ => (hv (k x) s).comp x (hk.differentiable (by norm_num) x).hasDerivAt)
        (hgs.intervalIntegrable _ _)
    -- `t(s) - t(r) = -∫_r^s ∂v(k(x), x)/∂k · k'(x) dx`
    have ht_int : t s - t r = -∫ x in r..s, vk (k x) x * deriv k x := by
      rw [hform s hs, hform r hr, ← intervalIntegral.integral_interval_sub_left
        (hg.intervalIntegrable a s) (hg.intervalIntegrable a r)]
      ring
    have hdiff : 0 ≤ ∫ x in r..s, (vk (k x) s - vk (k x) x) * deriv k x := by
      rcases lt_trichotomy r s with hrs | hrs | hrs
      · have hab : a < b := lt_of_le_of_lt hr.1 (lt_of_lt_of_le hrs hs.2)
        apply intervalIntegral.integral_nonneg hrs.le
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨le_trans hr.1 hx.1, le_trans hx.2 hs.2⟩
        apply mul_nonneg
        · exact sub_nonneg.2 ((hmono (k x)).monotoneOn hxI hs hx.2)
        · exact dc_deriv_nonneg_of_monotoneOn hab hm hxI
            (hk.differentiable (by norm_num) x)
      · rw [hrs, intervalIntegral.integral_same]
      · have hab : a < b := lt_of_le_of_lt hs.1 (lt_of_lt_of_le hrs hr.2)
        rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_nonneg hrs.le
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨le_trans hs.1 hx.1, le_trans hx.2 hr.2⟩
        have h1 : vk (k x) s ≤ vk (k x) x := (hmono (k x)).monotoneOn hs hxI hx.1
        have h2 := dc_deriv_nonneg_of_monotoneOn hab hm hxI (hk.differentiable (by norm_num) x)
        nlinarith
    have e2 : ∫ x in r..s, (vk (k x) s - vk (k x) x) * deriv k x =
        (∫ x in r..s, vk (k x) s * deriv k x) - ∫ x in r..s, vk (k x) x * deriv k x := by
      rw [← intervalIntegral.integral_sub (hgs.intervalIntegrable r s)
        (hg.intervalIntegrable r s)]
      congr 1
      funext x
      ring
    rw [e2, hv_int] at hdiff
    linarith

/-- The implicit function theorem for a real function of two real variables with continuous
partial derivatives (from Mathlib's `implicitFunctionOfBivariate`): if `∂G/∂x(s₀, x₀) ≠ 0`,
there is `ψ`, strictly differentiable at `s₀` with `ψ'(s₀) = -(∂G/∂s)/(∂G/∂x)`, `ψ(s₀) = x₀`,
and `G(s, ψ(s)) = G(s₀, x₀)` near `s₀`. -/
theorem dc_implicit {G Gs Gx : ℝ → ℝ → ℝ}
    (hGs : ∀ s x, HasDerivAt (fun r => G r x) (Gs s x) s)
    (hGx : ∀ s x, HasDerivAt (fun y => G s y) (Gx s x) x)
    (hcs : Continuous fun p : ℝ × ℝ => Gs p.1 p.2)
    (hcx : Continuous fun p : ℝ × ℝ => Gx p.1 p.2) {s0 x0 : ℝ} (hne : Gx s0 x0 ≠ 0) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(Gs s0 x0) / Gx s0 x0) s0 ∧ ψ s0 = x0 ∧
      ∀ᶠ s in 𝓝 s0, G s (ψ s) = G s0 x0 := by
  let u : ℝ × ℝ := (s0, x0)
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun s x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gs s x)
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun s x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s x)
  have df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (G · v.2) (f₁ v.1 v.2) v.1 :=
    Filter.Eventually.of_forall fun v => (hGs v.1 v.2).hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (G v.1 ·) (f₂ v.1 v.2) v.2 :=
    Filter.Eventually.of_forall fun v => (hGx v.1 v.2).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) u :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp hcs).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry f₂) u :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp hcx).continuousAt
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (Gx s0 x0) hne)
  have he : (e : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s0 x0) := by
    ext; simp [e]
  have if₂ : (f₂ u.1 u.2).IsInvertible := ⟨e, he⟩
  refine ⟨implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂ if₂, ?_, ?_, ?_⟩
  · have h := (hasStrictFDerivAt_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂)
      df₁ df₂ cf₁ cf₂ if₂).hasStrictDerivAt
    convert h using 1
    change _ = (-(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s0 x0)).inverse ∘L
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gs s0 x0)) 1
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp [e]
    field_simp
  · have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂)
      df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    exact h.1 rfl
  · exact eventually_apply_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂ if₂

/-- The implicit function theorem applied to a root function: if `κ(s)` is a root of `G(s, ·)`
for `s ∈ S`, each `G(s, ·)` is injective, and `∂G/∂x(s₀, κ(s₀)) ≠ 0`, then `κ` agrees near `s₀`
(within `S`) with a function strictly differentiable at `s₀` with derivative
`-(∂G/∂s)/(∂G/∂x)`. -/
theorem dc_implicit_root {G Gs Gx : ℝ → ℝ → ℝ}
    (hGs : ∀ s x, HasDerivAt (fun r => G r x) (Gs s x) s)
    (hGx : ∀ s x, HasDerivAt (fun y => G s y) (Gx s x) x)
    (hcs : Continuous fun p : ℝ × ℝ => Gs p.1 p.2)
    (hcx : Continuous fun p : ℝ × ℝ => Gx p.1 p.2) {κ : ℝ → ℝ} {S : Set ℝ}
    (hroot : ∀ s ∈ S, G s (κ s) = 0) (hinj : ∀ s, Injective (G s)) {s0 : ℝ} (hs0 : s0 ∈ S)
    (hne : Gx s0 (κ s0) ≠ 0) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(Gs s0 (κ s0)) / Gx s0 (κ s0)) s0 ∧ ψ s0 = κ s0 ∧
      κ =ᶠ[𝓝[S] s0] ψ := by
  obtain ⟨ψ, hψ, hψ0, hev⟩ := dc_implicit hGs hGx hcs hcx hne
  refine ⟨ψ, hψ, hψ0, ?_⟩
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [hev] with s hs hsS
  rw [hroot s0 hs0] at hs
  exact hinj s ((hroot s hsS).trans hs.symm)

/-- A strictly concave function (`S'' < 0`) with `S'(c) = 0` has its unique maximum at `c`. -/
theorem dc_strict_max {S S' S'' : ℝ → ℝ} (hS : ∀ x, HasDerivAt S (S' x) x)
    (hS' : ∀ x, HasDerivAt S' (S'' x) x) (hneg : ∀ x, S'' x < 0) {c : ℝ} (hc : S' c = 0)
    {x : ℝ} (hx : x ≠ c) : S x < S c := by
  have hanti : StrictAnti S' := strictAnti_of_deriv_neg fun y => by
    rw [(hS' y).deriv]; exact hneg y
  have hcont : Continuous S := continuous_iff_continuousAt.2 fun y => (hS y).continuousAt
  rcases hx.lt_or_gt with h | h
  · have hm : StrictMonoOn S (Set.Icc x c) :=
      strictMonoOn_of_deriv_pos (convex_Icc x c) hcont.continuousOn fun y hy => by
        rw [interior_Icc] at hy
        rw [(hS y).deriv, ← hc]
        exact hanti hy.2
    exact hm ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
  · have hm : StrictAntiOn S (Set.Icc c x) :=
      strictAntiOn_of_deriv_neg (convex_Icc c x) hcont.continuousOn fun y hy => by
        rw [interior_Icc] at hy
        rw [(hS y).deriv, ← hc]
        exact hanti hy.1
    exact hm ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h

/-- The Groves form, one-dimensional form (MWG, p. 882). Along a slice on which truth telling
is optimal, if `k` and `t` are continuous on `[a, b]` and differentiable on `(a, b)`, and the
efficiency condition `∂v(k(s), s)/∂k + w'(k(s)) = 0` holds (`w` = the others' total valuation),
then `t - w ∘ k` is constant: `t(θ) = t(a) + w(k(θ)) - w(k(a))`. -/
theorem dc_groves_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {w wk : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (wk x) x) {k t : ℝ → ℝ} {a b : ℝ}
    (hkc : ContinuousOn k (Set.Icc a b)) (htc : ContinuousOn t (Set.Icc a b))
    (hkd : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ k s)
    (htd : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ t s)
    (hIC : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s)
    (hfoc : ∀ s ∈ Set.Ioo a b, vk (k s) s + wk (k s) = 0) :
    ∀ θ ∈ Set.Icc a b, t θ = t a + w (k θ) - w (k a) := by
  intro θ hθ
  rcases hθ.1.eq_or_lt with h | h
  · rw [← h]; ring
  · have hwc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
    have hsub : Set.Icc a θ ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hθ.2
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => t s - w (k s))
      (fun s => deriv t s - wk (k s) * deriv k s) h
      ((htc.mono hsub).sub (hwc.comp_continuousOn (hkc.mono hsub)))
      (fun x hx => ((htd x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩).hasDerivAt).sub
        ((hw (k x)).comp x (hkd x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩).hasDerivAt))
    have hc' : c ∈ Set.Ioo a b := ⟨hc.1, lt_of_lt_of_le hc.2 hθ.2⟩
    have h1 := dc_foc_slice hv (hIC c (Set.Ioo_subset_Icc_self hc')) hc'
      (hkd c hc').hasDerivAt (htd c hc').hasDerivAt
    have h2 : vk (k c) c = -wk (k c) := by linarith [hfoc c hc']
    rw [h2] at h1
    have h0 : deriv t c - wk (k c) * deriv k c = 0 := by linarith
    rw [h0, eq_comm, div_eq_zero_iff] at hslope
    rcases hslope with hs | hs
    · linarith
    · exfalso; linarith

/-- The mixed difference of the maximal total valuation is strictly positive when both
valuations have increasing differences between the types used, the maximiser is unique at
`(b₁, b₂)` and the efficient project moves with each type. -/
theorem dc_mixed_pos {w1 w2 : ℝ → ℝ → ℝ} {κ : ℝ → ℝ → ℝ} {a1 b1 a2 b2 : ℝ}
    (hAA : ∀ x, w1 x a1 + w2 x a2 ≤ w1 (κ a1 a2) a1 + w2 (κ a1 a2) a2)
    (hBB : ∀ x, x ≠ κ b1 b2 → w1 x b1 + w2 x b2 < w1 (κ b1 b2) b1 + w2 (κ b1 b2) b2)
    (hm1 : Monotone fun x => w1 x b1 - w1 x a1) (hm2 : Monotone fun x => w2 x b2 - w2 x a2)
    (hne1 : κ a1 b2 ≠ κ b1 b2) (hne2 : κ b1 a2 ≠ κ b1 b2) :
    0 < (w1 (κ b1 b2) b1 + w2 (κ b1 b2) b2) - (w1 (κ a1 b2) a1 + w2 (κ a1 b2) b2) -
      (w1 (κ b1 a2) b1 + w2 (κ b1 a2) a2) + (w1 (κ a1 a2) a1 + w2 (κ a1 a2) a2) := by
  rcases le_or_gt (κ a1 b2) (κ b1 a2) with h | h
  · have e1 := hm2 h
    have e2 := hBB (κ b1 a2) hne2
    have e3 := hAA (κ a1 b2)
    simp only at e1
    linarith
  · have e1 := hm1 h.le
    have e2 := hBB (κ a1 b2) hne1
    have e3 := hAA (κ b1 a2)
    simp only at e1
    linarith

/-- If `∂v/∂k(x, a) < ∂v/∂k(x, b)` for every `x`, then `v(x, b) - v(x, a)` is nondecreasing in
`x` (increasing differences). -/
theorem dc_delta_monotone {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {a b : ℝ}
    (hlt : ∀ x, vk x a < vk x b) : Monotone fun x => v x b - v x a :=
  monotone_of_deriv_nonneg (fun x => ((hv x b).sub (hv x a)).differentiableAt) fun x => by
    rw [((hv x b).fun_sub (hv x a)).deriv]
    exact (sub_pos.2 (hlt x)).le

/-- A continuous function on `ℝ × ℝ` that never vanishes has a constant sign. -/
theorem dc_sign_of_ne {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hne : ∀ p, f p ≠ 0) :
    (∀ p, 0 < f p) ∨ ∀ p, f p < 0 := by
  rcases (hne 0).lt_or_gt with h0 | h0
  · right
    intro p
    rcases (hne p).lt_or_gt with hp | hp
    · exact hp
    · obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ (0 : ℝ × ℝ))
        (Set.mem_univ p) hf.continuousOn ⟨h0.le, hp.le⟩
      exact absurd hz (hne z)
  · left
    intro p
    rcases (hne p).lt_or_gt with hp | hp
    · obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ p)
        (Set.mem_univ (0 : ℝ × ℝ)) hf.continuousOn ⟨hp.le, h0.le⟩
      exact absurd hz (hne z)
    · exact hp

/-! ## The environment -/

/-- **The differentiable case** (MWG, p. 881). `K = ℝ`; agent `i`'s valuation `vᵢ(k, θᵢ)` has
partial derivatives `vkᵢ = ∂vᵢ/∂k`, `vkkᵢ = ∂²vᵢ/∂k²`, `vkθᵢ = ∂²vᵢ/∂k∂θᵢ`, continuous in
`(k, θᵢ)`, with `∂²vᵢ/∂k² < 0` and `∂²vᵢ/∂k∂θᵢ ≠ 0` everywhere. (This is what MWG use of
"`vᵢ` twice continuously differentiable".) -/
structure SmallTypeEnv (ι : Type*) where
  /-- The valuation `vᵢ(k, θᵢ)`. -/
  v : ι → ℝ → ℝ → ℝ
  /-- `∂vᵢ/∂k`. -/
  vk : ι → ℝ → ℝ → ℝ
  /-- `∂²vᵢ/∂k²`. -/
  vkk : ι → ℝ → ℝ → ℝ
  /-- `∂²vᵢ/∂k∂θᵢ`. -/
  vkθ : ι → ℝ → ℝ → ℝ
  hasDerivAt_v : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x
  hasDerivAt_vk : ∀ i x θ, HasDerivAt (fun y => vk i y θ) (vkk i x θ) x
  hasDerivAt_vkθ : ∀ i x θ, HasDerivAt (fun s => vk i x s) (vkθ i x θ) θ
  continuous_vk : ∀ i, Continuous fun p : ℝ × ℝ => vk i p.1 p.2
  continuous_vkk : ∀ i, Continuous fun p : ℝ × ℝ => vkk i p.1 p.2
  continuous_vkθ : ∀ i, Continuous fun p : ℝ × ℝ => vkθ i p.1 p.2
  vkk_neg : ∀ i x θ, vkk i x θ < 0
  vkθ_ne : ∀ i x θ, vkθ i x θ ≠ 0

/-- The quadratic environment `vᵢ(k, θᵢ) = θᵢk - k²/2` (`∂²v/∂k² = -1`, `∂²v/∂k∂θ = 1`): an
instance of `SmallTypeEnv`. -/
noncomputable def quadEnv (ι : Type*) : SmallTypeEnv ι where
  v := fun _ x θ => θ * x - x ^ 2 / 2
  vk := fun _ x θ => θ - x
  vkk := fun _ _ _ => -1
  vkθ := fun _ _ _ => 1
  hasDerivAt_v := fun _ x θ => by
    have h := ((hasDerivAt_id x).const_mul θ).fun_sub ((hasDerivAt_pow 2 x).div_const 2)
    convert h using 1
    · funext y; simp only [id]
    · norm_num
  hasDerivAt_vk := fun _ x θ => by simpa using (hasDerivAt_id x).const_sub θ
  hasDerivAt_vkθ := fun _ x θ => by simpa using (hasDerivAt_id θ).sub_const x
  continuous_vk := fun _ => by fun_prop
  continuous_vkk := fun _ => continuous_const
  continuous_vkθ := fun _ => continuous_const
  vkk_neg := fun _ _ _ => by norm_num
  vkθ_ne := fun _ _ _ => one_ne_zero

variable {ι : Type*}

/-- **The differentiable case** (MWG, p. 881). The box of types: `θᵢ ∈ [θ̲ᵢ, θ̄ᵢ]` for all `i`. -/
def InBox (lo hi : ι → ℝ) (θ : ι → ℝ) : Prop :=
  ∀ i, θ i ∈ Set.Icc (lo i) (hi i)

/-- Changing one coordinate within its interval stays in the box. -/
theorem inBox_update [DecidableEq ι] {lo hi θ : ι → ℝ} (hθ : InBox lo hi θ) {i : ι} {s : ℝ}
    (hs : s ∈ Set.Icc (lo i) (hi i)) : InBox lo hi (update θ i s) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hs
  · simpa [update_of_ne h] using hθ j

/-- **Definition 23.C.3** on the box (MWG, p. 871): `f = (k, t)` with `K = ℝ` and quasilinear
utilities `vᵢ(k, θᵢ) + tᵢ` is strategy-proof when types range over the box. -/
def StrategyProofOnBox [DecidableEq ι] (v : ι → ℝ → ℝ → ℝ) (lo hi : ι → ℝ)
    (k : (ι → ℝ) → ℝ) (t : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ i θ, InBox lo hi θ → ∀ s ∈ Set.Icc (lo i) (hi i),
    v i (k (update θ i s)) (θ i) + t (update θ i s) i ≤ v i (k θ) (θ i) + t θ i

/-- **(23.C.7)** on the box (MWG, p. 877): `k` is efficient at every profile of the box. -/
def EfficientOnBox [Fintype ι] (v : ι → ℝ → ℝ → ℝ) (lo hi : ι → ℝ) (k : (ι → ℝ) → ℝ) :
    Prop :=
  ∀ θ, InBox lo hi θ → ∀ x, ∑ i, v i x (θ i) ≤ ∑ i, v i (k θ) (θ i)

/-- An efficient project rule (23.C.7) on all profiles is efficient on the box. -/
theorem EfficientProject.efficientOnBox [Fintype ι] {v : ι → ℝ → ℝ → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientProject v k) (lo hi : ι → ℝ) :
    EfficientOnBox v lo hi k :=
  fun θ _ x => hk θ x

/-- `StrategyProofOnBox` is `StrategyProof` (Definition 23.C.3) for the quasilinear utilities
`qlU` with type sets `Θᵢ = [θ̲ᵢ, θ̄ᵢ]`. -/
theorem strategyProofOnBox_iff [DecidableEq ι] (v : ι → ℝ → ℝ → ℝ) (m : ι → ℝ)
    (lo hi : ι → ℝ) (k : (ι → ℝ) → ℝ) (t : (ι → ℝ) → ι → ℝ) :
    StrategyProofOnBox v lo hi k t ↔
      StrategyProof (Θ := fun i => Set.Icc (lo i) (hi i))
        (qlU (fun i x (θi : Set.Icc (lo i) (hi i)) => v i x θi) m)
        (fun θ => (k fun i => θ i, t fun i => θ i)) := by
  have hupd : ∀ (θ : (i : ι) → Set.Icc (lo i) (hi i)) i (a : Set.Icc (lo i) (hi i)),
      (fun j => (update θ i a j : ℝ)) = update (fun j => (θ j : ℝ)) i a := by
    intro θ i a
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [update_of_ne h]
  constructor
  · intro hSP i θ θh
    simp only [qlU, hupd]
    have := hSP i (fun j => θ j) (fun j => (θ j).2) θh θh.2
    linarith
  · intro hSP i θ hθ s hs
    have := hSP i (fun j => ⟨θ j, hθ j⟩) ⟨s, hs⟩
    simp only [qlU, hupd] at this
    linarith

/-- Strategy-proofness on the box gives optimality of truth telling along every slice. -/
theorem sp_slice [DecidableEq ι] {v : ι → ℝ → ℝ → ℝ} {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hSP : StrategyProofOnBox v lo hi k t) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) :
    ∀ s ∈ Set.Icc (lo i) (hi i), ∀ r ∈ Set.Icc (lo i) (hi i),
      v i (k (update θ i r)) s + t (update θ i r) i ≤
        v i (k (update θ i s)) s + t (update θ i s) i := by
  intro s hs r hr
  have := hSP i (update θ i s) (inBox_update hθ hs) r hr
  simpa only [update_idem, update_self] using this

/-- `∑ⱼ gⱼ((θ with θᵢ = s)ⱼ) = gᵢ(s) + ∑_{j≠i} gⱼ(θⱼ)`. -/
theorem sum_update_split [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι)
    (s : ℝ) : ∑ j, g j (update θ i s j) = g i s + ∑ j ∈ univ.erase i, g j (θ j) := by
  rw [← add_sum_erase _ _ (mem_univ i), update_self]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **(23.C.13)** (MWG, p. 881). If `f = (k, t)` is strategy-proof on the box and `k`, `tᵢ` are
differentiable in `θᵢ` at an interior type, then
`∂vᵢ(k(θ), θᵢ)/∂k · ∂k(θ)/∂θᵢ + ∂tᵢ(θ)/∂θᵢ = 0`. -/
theorem eq_23_C_13 [DecidableEq ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hSP : StrategyProofOnBox E.v lo hi k t) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) {i : ι} (hθi : θ i ∈ Set.Ioo (lo i) (hi i)) {dk dt : ℝ}
    (hk : HasDerivAt (fun s => k (update θ i s)) dk (θ i))
    (ht : HasDerivAt (fun s => t (update θ i s) i) dt (θ i)) :
    E.vk i (k θ) (θ i) * dk + dt = 0 := by
  have h := dc_foc_slice (E.hasDerivAt_v i) (k := fun s => k (update θ i s))
    (t := fun s => t (update θ i s) i)
    (fun r hr => sp_slice hSP hθ i (θ i) (Set.Ioo_subset_Icc_self hθi) r hr) hθi hk ht
  simpa only [update_eq_self] using h

/-- **(23.C.14)** (MWG, p. 881). If `f = (k, t)` is `C¹` and strategy-proof on the box, then
`tᵢ(θᵢ, θ₋ᵢ) = tᵢ(θ̲ᵢ, θ₋ᵢ) - ∫_{θ̲ᵢ}^{θᵢ} ∂vᵢ(k(s, θ₋ᵢ), s)/∂k · ∂k(s, θ₋ᵢ)/∂s ds`. -/
theorem eq_23_C_14 [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hk : ContDiff ℝ 1 k) (ht : ∀ i, ContDiff ℝ 1 fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i -
      ∫ s in lo i..θ i, E.vk i (k (update θ i s)) s * deriv (fun y => k (update θ i y)) s := by
  have h := dc_integral_slice (E.hasDerivAt_v i) (E.continuous_vk i)
    (k := fun s => k (update θ i s)) (t := fun s => t (update θ i s) i)
    (hk.comp (contDiff_update 1 θ i)) ((ht i).comp (contDiff_update 1 θ i))
    (sp_slice hSP hθ i) (θ i) (hθ i)
  simpa only [update_eq_self] using h

/-- (23.C.15) for any valuations differentiable in `k`: an efficient project rule satisfies
`∑ⱼ ∂vⱼ(k(θ), θⱼ)/∂k = 0` on the box. -/
theorem efficient_foc [Fintype ι] {v vk : ι → ℝ → ℝ → ℝ}
    (hv : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    ∑ j, vk j (k θ) (θ j) = 0 := by
  have hmax : IsLocalMax (fun x => ∑ j, v j x (θ j)) (k θ) :=
    Filter.Eventually.of_forall fun x => hk θ hθ x
  exact hmax.hasDerivAt_eq_zero (HasDerivAt.fun_sum fun j _ => hv j (k θ) (θ j))

/-- **(23.C.15)** (MWG, p. 882). An efficient project rule satisfies
`∑ⱼ ∂vⱼ(k*(θ), θⱼ)/∂k = 0` at every profile of the box. -/
theorem eq_23_C_15 [Fintype ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    ∑ j, E.vk j (k θ) (θ j) = 0 :=
  efficient_foc E.hasDerivAt_v hk hθ

/-- **Exercise 23.C.9** (MWG, p. 920). Suppose `∂²vᵢ/∂k∂θᵢ > 0`. A `C¹` social choice function
`f = (k, t)` is truthfully implementable in dominant strategies (on the box) iff for all `i`,
`k(θ)` is nondecreasing in `θᵢ` and
`tᵢ(θᵢ, θ₋ᵢ) = tᵢ(θ̲ᵢ, θ₋ᵢ) - ∫_{θ̲ᵢ}^{θᵢ} ∂vᵢ(k(s, θ₋ᵢ), s)/∂k · ∂k(s, θ₋ᵢ)/∂s ds`. -/
theorem exercise_23_C_9 [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    (hpos : ∀ i x θ, 0 < E.vkθ i x θ)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ} (hk : ContDiff ℝ 1 k)
    (ht : ∀ i, ContDiff ℝ 1 fun θ => t θ i) :
    StrategyProofOnBox E.v lo hi k t ↔ ∀ i θ, InBox lo hi θ →
      MonotoneOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)) ∧
        t θ i = t (update θ i (lo i)) i - ∫ s in lo i..θ i,
          E.vk i (k (update θ i s)) s * deriv (fun y => k (update θ i y)) s := by
  have hmono : ∀ i x, StrictMonoOn (E.vk i x) (Set.Icc (lo i) (hi i)) := fun i x =>
    (strictMono_of_deriv_pos fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact hpos i x θ).strictMonoOn _
  have hslice := fun i θ => dc_sp_slice_iff (E.hasDerivAt_v i) (E.continuous_vk i) (hmono i)
    (k := fun s => k (update θ i s)) (t := fun s => t (update θ i s) i)
    (hk.comp (contDiff_update 1 θ i)) ((ht i).comp (contDiff_update 1 θ i))
  constructor
  · intro hSP i θ hθ
    have h := (hslice i θ).1 (sp_slice hSP hθ i)
    refine ⟨h.1, ?_⟩
    have h2 := h.2 (θ i) (hθ i)
    simpa only [update_eq_self] using h2
  · intro h i θ hθ s hs
    have hIC := (hslice i θ).2 ⟨(h i θ hθ).1, fun y hy => by
      have h2 := (h i (update θ i y) (inBox_update hθ hy)).2
      simpa only [update_idem, update_self] using h2⟩
    have h3 := hIC (θ i) (hθ i) s hs
    simpa only [update_eq_self] using h3

/-- **Footnote 26** (MWG, p. 882). The Groves form for any project rule that is efficient and
differentiable (continuous along each coordinate of the box and differentiable at interior
types), with valuations differentiable in `k` and differentiable transfers: if `f = (k, t)` is
strategy-proof on the box, then
`tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k(θ), θⱼ) - ∑_{j≠i} vⱼ(k(θ̲ᵢ, θ₋ᵢ), θⱼ)`.
(No concavity or single-crossing assumption is used.) -/
theorem footnote_23_26 [Fintype ι] [DecidableEq ι] {v vk : ι → ℝ → ℝ → ℝ}
    (hv : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ} (hk : EfficientOnBox v lo hi k)
    (hSP : StrategyProofOnBox v lo hi k t)
    (hkc : ∀ i θ, InBox lo hi θ →
      ContinuousOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)))
    (hkd : ∀ i θ, InBox lo hi θ → ∀ s ∈ Set.Ioo (lo i) (hi i),
      DifferentiableAt ℝ (fun s => k (update θ i s)) s)
    (ht : ∀ i, Differentiable ℝ fun θ => t θ i) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i + ∑ j ∈ univ.erase i, v j (k θ) (θ j) -
      ∑ j ∈ univ.erase i, v j (k (update θ i (lo i))) (θ j) := by
  have hupd : Differentiable ℝ (update θ i) :=
    (contDiff_update 1 θ i).differentiable (by norm_num)
  have htd : Differentiable ℝ fun s => t (update θ i s) i := (ht i).comp hupd
  have h := dc_groves_slice (hv i) (w := fun x => ∑ j ∈ univ.erase i, v j x (θ j))
    (wk := fun x => ∑ j ∈ univ.erase i, vk j x (θ j))
    (fun x => HasDerivAt.fun_sum fun j _ => hv j x (θ j)) (hkc i θ hθ)
    htd.continuous.continuousOn (hkd i θ hθ) (fun s _ => htd s) (sp_slice hSP hθ i)
    (fun s hs => by
      have h0 := efficient_foc hv hk (inBox_update hθ (Set.Ioo_subset_Icc_self hs))
      rwa [sum_update_split (fun j x => vk j (k (update θ i s)) x)] at h0)
    (θ i) (hθ i)
  simp only [update_eq_self] at h
  exact h

/-- The others' types are unchanged by the update of `θᵢ`. -/
theorem sum_erase_update [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι)
    (s : ℝ) : ∑ j ∈ univ.erase i, g j (update θ i s j) = ∑ j ∈ univ.erase i, g j (θ j) :=
  sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Implicit function theorem** (MWG, p. 882). In the differentiable case, an efficient
project rule `k*` agrees, along the `θᵢ`-coordinate through any profile of the box, with a
function strictly differentiable at `θᵢ` with derivative
`∂k*/∂θᵢ = -(∂²vᵢ/∂k∂θᵢ)/(∑ⱼ ∂²vⱼ/∂k²)`. -/
theorem efficient_slice_implicit [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) {s0 : ℝ} (hs0 : s0 ∈ Set.Icc (lo i) (hi i)) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(E.vkθ i (k (update θ i s0)) s0) /
        (E.vkk i (k (update θ i s0)) s0 +
          ∑ j ∈ univ.erase i, E.vkk j (k (update θ i s0)) (θ j))) s0 ∧
      ψ s0 = k (update θ i s0) ∧
      (fun s => k (update θ i s)) =ᶠ[𝓝[Set.Icc (lo i) (hi i)] s0] ψ := by
  have hGx : ∀ s x, HasDerivAt (fun y => E.vk i y s + ∑ j ∈ univ.erase i, E.vk j y (θ j))
      (E.vkk i x s + ∑ j ∈ univ.erase i, E.vkk j x (θ j)) x := fun s x =>
    (E.hasDerivAt_vk i x s).add (HasDerivAt.fun_sum fun j _ => E.hasDerivAt_vk j x (θ j))
  have hneg : ∀ s x, E.vkk i x s + ∑ j ∈ univ.erase i, E.vkk j x (θ j) < 0 := fun s x =>
    add_neg_of_neg_of_nonpos (E.vkk_neg i x s)
      (sum_nonpos fun j _ => (E.vkk_neg j x (θ j)).le)
  have hinj : ∀ s, Injective fun y => E.vk i y s + ∑ j ∈ univ.erase i, E.vk j y (θ j) :=
    fun s => (strictAnti_of_deriv_neg fun x => by
      rw [(hGx s x).deriv]; exact hneg s x).injective
  have hcx : Continuous fun p : ℝ × ℝ =>
      E.vkk i p.2 p.1 + ∑ j ∈ univ.erase i, E.vkk j p.2 (θ j) :=
    ((E.continuous_vkk i).comp continuous_swap).add (continuous_finsetSum _ fun j _ =>
      (E.continuous_vkk j).comp (continuous_snd.prodMk continuous_const))
  obtain ⟨ψ, h1, h2, h3⟩ := dc_implicit_root
    (G := fun s x => E.vk i x s + ∑ j ∈ univ.erase i, E.vk j x (θ j))
    (fun s x => (E.hasDerivAt_vkθ i x s).add_const _) hGx
    ((E.continuous_vkθ i).comp continuous_swap) hcx
    (κ := fun s => k (update θ i s)) (S := Set.Icc (lo i) (hi i))
    (fun s hs => by
      have h0 := efficient_foc E.hasDerivAt_v hk (inBox_update hθ hs)
      rwa [sum_update_split (fun j x => E.vk j (k (update θ i s)) x)] at h0)
    hinj hs0 (hneg s0 _).ne
  exact ⟨ψ, h1, h2, h3⟩

/-- **Implicit function theorem** (MWG, p. 882): an efficient `k*` is continuous along each
coordinate of the box. -/
theorem efficient_slice_continuousOn [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) :
    ContinuousOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)) := by
  intro s0 hs0
  obtain ⟨ψ, h1, h2, h3⟩ := efficient_slice_implicit E hk hθ i hs0
  exact h1.hasDerivAt.continuousAt.continuousWithinAt.congr_of_eventuallyEq h3 h2.symm

/-- **Implicit function theorem** (MWG, p. 882): at interior types an efficient `k*` is
differentiable in `θᵢ`, with `∂k*/∂θᵢ = -(∂²vᵢ/∂k∂θᵢ)/(∑ⱼ ∂²vⱼ/∂k²)`. -/
theorem efficient_slice_hasDerivAt [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) {s0 : ℝ} (hs0 : s0 ∈ Set.Ioo (lo i) (hi i)) :
    HasDerivAt (fun s => k (update θ i s)) (-(E.vkθ i (k (update θ i s0)) s0) /
        (E.vkk i (k (update θ i s0)) s0 +
          ∑ j ∈ univ.erase i, E.vkk j (k (update θ i s0)) (θ j))) s0 := by
  obtain ⟨ψ, h1, -, h3⟩ := efficient_slice_implicit E hk hθ i (Set.Ioo_subset_Icc_self hs0)
  rw [nhdsWithin_eq_nhds.2 (Icc_mem_nhds hs0.1 hs0.2)] at h3
  exact h1.hasDerivAt.congr_of_eventuallyEq h3

/-- **Implicit function theorem** (MWG, p. 882): `∂k*(θ)/∂θᵢ ≠ 0` at interior types. -/
theorem efficient_slice_deriv_ne_zero [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) (hθi : θ i ∈ Set.Ioo (lo i) (hi i)) :
    deriv (fun s => k (update θ i s)) (θ i) ≠ 0 := by
  rw [(efficient_slice_hasDerivAt E hk hθ i hθi).deriv]
  have hneg : E.vkk i (k (update θ i (θ i))) (θ i) +
      ∑ j ∈ univ.erase i, E.vkk j (k (update θ i (θ i))) (θ j) < 0 :=
    add_neg_of_neg_of_nonpos (E.vkk_neg _ _ _) (sum_nonpos fun j _ => (E.vkk_neg _ _ _).le)
  exact div_ne_zero (neg_ne_zero.2 (E.vkθ_ne _ _ _)) hneg.ne

/-- **The Groves form in the differentiable case** (MWG, p. 882). If `f = (k*, t)` with `k*`
efficient and differentiable transfers is strategy-proof on the box, then
`tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k*(θ), θⱼ) - ∑_{j≠i} vⱼ(k*(θ̲ᵢ, θ₋ᵢ), θⱼ)`. The
differentiability of `k*` comes from the implicit function theorem. -/
theorem differentiable_case_groves [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (hSP : StrategyProofOnBox E.v lo hi k t)
    (ht : ∀ i, Differentiable ℝ fun θ => t θ i) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i + ∑ j ∈ univ.erase i, E.v j (k θ) (θ j) -
      ∑ j ∈ univ.erase i, E.v j (k (update θ i (lo i))) (θ j) :=
  footnote_23_26 E.hasDerivAt_v hk hSP (fun i _ hθ => efficient_slice_continuousOn E hk hθ i)
    (fun i _ hθ _ hs => (efficient_slice_hasDerivAt E hk hθ i hs).differentiableAt) ht i hθ

/-- **Proposition 23.C.4** on the box (MWG, p. 877): a Groves mechanism is strategy-proof on the
box. -/
theorem groves_strategyProofOnBox [Fintype ι] [DecidableEq ι] {v : ι → ℝ → ℝ → ℝ}
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox v lo hi k)
    {h : ι → (ι → ℝ) → ℝ} (hh : IndepOwn h) :
    StrategyProofOnBox v lo hi k (grovesTransfer v k h) := by
  intro i θ hθ s _
  simp only [grovesTransfer]
  rw [hh, sum_erase_update (fun j x => v j (k (update θ i s)) x)]
  have e1 := (add_sum_erase univ (fun j => v j (k (update θ i s)) (θ j)) (mem_univ i)).symm
  have e2 := (add_sum_erase univ (fun j => v j (k θ) (θ j)) (mem_univ i)).symm
  have := hk θ hθ (k (update θ i s))
  linarith

/-- **The Groves characterisation in the differentiable case** (MWG, p. 882): with `k*`
efficient and differentiable transfers, `f = (k*, t)` is strategy-proof on the box iff it is a
Groves mechanism there, i.e. `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)` (23.C.8). -/
theorem differentiable_case_groves_iff [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i) :
    StrategyProofOnBox E.v lo hi k t ↔ ∃ h : ι → (ι → ℝ) → ℝ, IndepOwn h ∧
      ∀ θ, InBox lo hi θ → t θ = grovesTransfer E.v k h θ := by
  constructor
  · intro hSP
    refine ⟨fun i θ => t (update θ i (lo i)) i -
      ∑ j ∈ univ.erase i, E.v j (k (update θ i (lo i))) (θ j), fun i θ a => ?_,
      fun θ hθ => funext fun i => ?_⟩
    · simp only [update_idem]
      rw [sum_erase_update (fun j x => E.v j (k (update θ i (lo i))) x)]
    · rw [differentiable_case_groves E hk hSP ht i hθ]
      simp only [grovesTransfer]
      ring
  · rintro ⟨h, hh, hth⟩ i θ hθ s hs
    rw [hth θ hθ, hth _ (inBox_update hθ hs)]
    exact groves_strategyProofOnBox hk hh i θ hθ s hs

/-- **Exercise 23.C.10(c)** (MWG, p. 920), the decomposition in the differentiable case: with
`I ≥ 2`, if `f = (k*, t)` (efficient `k*`, differentiable transfers) is strategy-proof and budget
balanced on the box, then `V*(θ) = ∑ᵢ vᵢ(k*(θ), θᵢ) = ∑ᵢ Vᵢ(θ₋ᵢ)` on the box. -/
theorem exercise_23_C_10c_decomposition [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) (hBB : ∀ θ, InBox lo hi θ → ∑ i, t θ i = 0) :
    ∃ V : ι → (ι → ℝ) → ℝ, IndepOwn V ∧
      ∀ θ, InBox lo hi θ → ∑ i, E.v i (k θ) (θ i) = ∑ i, V i θ := by
  obtain ⟨h, hh, hth⟩ := (differentiable_case_groves_iff E hk ht).1 hSP
  have hI' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hI
  refine ⟨fun i θ => -h i θ / ((Fintype.card ι : ℝ) - 1), fun i θ a => by simp [hh i θ a],
    fun θ hθ => ?_⟩
  have h0 := hBB θ hθ
  rw [hth θ hθ, sum_grovesTransfer] at h0
  have hne : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by linarith
  rw [← sum_div, sum_neg_distrib, eq_div_iff hne]
  linarith

/-- **Exercise 23.C.10(c)** (MWG, p. 920), `I = 2`: if `V*(θ₁, θ₂) = V₁(θ₂) + V₂(θ₁)` then
`∂²V*/∂θ₁∂θ₂ = 0` everywhere. -/
theorem exercise_23_C_10c {F : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} (h : ∀ x y, F x y = A y + B x)
    (x y : ℝ) : deriv (fun y' => deriv (fun x' => F x' y') x) y = 0 := by
  simp only [h, deriv_const_add, deriv_const]

/-- **Exercise 23.C.10(c)** (MWG, p. 920), "(In fact, this is a sufficient condition as
well.)", `I = 2`: if `∂²V*/∂θ₁∂θ₂ = 0` everywhere (with the partial derivatives existing), then
`V*(θ₁, θ₂) = V₁(θ₂) + V₂(θ₁)`; by Exercise 23.C.10(a) (`exercise_23_C_10a_if`) an efficient,
budget balanced, strategy-proof rule then exists. -/
theorem exercise_23_C_10c_sufficient {F Fx Fxy : ℝ → ℝ → ℝ}
    (hF : ∀ x y, HasDerivAt (fun x' => F x' y) (Fx x y) x)
    (hFx : ∀ x y, HasDerivAt (fun y' => Fx x y') (Fxy x y) y) (h0 : ∀ x y, Fxy x y = 0) :
    ∃ A B : ℝ → ℝ, ∀ x y, F x y = A y + B x := by
  have hc : ∀ x y, Fx x y = Fx x 0 := fun x y =>
    is_const_of_deriv_eq_zero (f := fun y' => Fx x y')
      (fun y' => (hFx x y').differentiableAt) (fun y' => by rw [(hFx x y').deriv, h0]) y 0
  refine ⟨fun y => F 0 y - F 0 0, fun x => F x 0, fun x y => ?_⟩
  have := is_const_of_deriv_eq_zero (f := fun x' => F x' y - F x' 0)
    (fun x' => ((hF x' y).sub (hF x' 0)).differentiableAt)
    (fun x' => by rw [((hF x' y).fun_sub (hF x' 0)).deriv, hc x' y, sub_self]) x 0
  linarith

/-- Two-agent profiles: changing agent 1's type (index `0`). -/
theorem vec2_update0 (x y z : ℝ) : update ![x, y] 0 z = ![z, y] := by
  funext j; fin_cases j <;> rfl

/-- Two-agent profiles: changing agent 2's type (index `1`). -/
theorem vec2_update1 (x y z : ℝ) : update ![x, y] 1 z = ![x, z] := by
  funext j; fin_cases j <;> rfl

/-- A two-agent profile is in the box when each type is in its interval. -/
theorem vec2_inBox {lo hi : Fin 2 → ℝ} {x y : ℝ} (hx : x ∈ Set.Icc (lo 0) (hi 0))
    (hy : y ∈ Set.Icc (lo 1) (hi 1)) : InBox lo hi ![x, y] := by
  intro j; fin_cases j <;> simpa

/-- In the differentiable case, for each agent there are two types `a ≠ b` in the box with
`∂vᵢ/∂k(x, a) < ∂vᵢ/∂k(x, b)` for every `x` (by the constant sign of `∂²vᵢ/∂k∂θᵢ`). -/
theorem smallTypeEnv_exists_pair (E : SmallTypeEnv ι) (i : ι) {lo hi : ℝ} (hlt : lo < hi) :
    ∃ a b, a ∈ Set.Icc lo hi ∧ b ∈ Set.Icc lo hi ∧ a ≠ b ∧ ∀ x, E.vk i x a < E.vk i x b := by
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlt.le⟩
  have hhi : hi ∈ Set.Icc lo hi := ⟨hlt.le, le_rfl⟩
  rcases dc_sign_of_ne (E.continuous_vkθ i) (fun p => E.vkθ_ne i p.1 p.2) with h | h
  · refine ⟨lo, hi, hlo, hhi, hlt.ne, fun x => ?_⟩
    exact strictMono_of_deriv_pos (fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact h (x, θ)) hlt
  · refine ⟨hi, lo, hhi, hlo, hlt.ne', fun x => ?_⟩
    exact strictAnti_of_deriv_neg (fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact h (x, θ)) hlt

/-- In the differentiable case the efficient total valuation has a unique maximiser. -/
theorem smallTypeEnv_strict_max [Fintype ι] [Nonempty ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ)
    {x : ℝ} (hx : x ≠ k θ) : ∑ i, E.v i x (θ i) < ∑ i, E.v i (k θ) (θ i) :=
  dc_strict_max (S := fun y => ∑ i, E.v i y (θ i)) (S' := fun y => ∑ i, E.vk i y (θ i))
    (S'' := fun y => ∑ i, E.vkk i y (θ i))
    (fun y => HasDerivAt.fun_sum fun i _ => E.hasDerivAt_v i y (θ i))
    (fun y => HasDerivAt.fun_sum fun i _ => E.hasDerivAt_vk i y (θ i))
    (fun y => sum_neg (fun i _ => E.vkk_neg i y (θ i)) univ_nonempty)
    (eq_23_C_15 E hk hθ) hx

/-- **Exercise 23.C.10(d)** (MWG, p. 920). Under the small-type assumptions with `I = 2`, the
maximal total valuation `V*` of an efficient project rule is not of the form `V₁(θ₂) + V₂(θ₁)`
on any box with nondegenerate type intervals: its mixed difference over suitable corner types
is nonzero (the finite-difference form of (c)). -/
theorem exercise_23_C_10d (E : SmallTypeEnv (Fin 2)) {lo hi : Fin 2 → ℝ}
    (hlt : ∀ i, lo i < hi i) {k : (Fin 2 → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) :
    ¬∃ V : Fin 2 → (Fin 2 → ℝ) → ℝ, IndepOwn V ∧
      ∀ θ, InBox lo hi θ → ∑ i, E.v i (k θ) (θ i) = ∑ i, V i θ := by
  rintro ⟨V, hV, hdec⟩
  obtain ⟨a1, b1, ha1, hb1, hab1, hlt1⟩ := smallTypeEnv_exists_pair E 0 (hlt 0)
  obtain ⟨a2, b2, ha2, hb2, hab2, hlt2⟩ := smallTypeEnv_exists_pair E 1 (hlt 1)
  have hbox : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      InBox lo hi ![x, y] := fun x y hx hy => vec2_inBox hx hy
  -- the first-order condition at the corners
  have hfoc : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      E.vk 0 (k ![x, y]) x + E.vk 1 (k ![x, y]) y = 0 := fun x y hx hy => by
    have := eq_23_C_15 E hk (hbox x y hx hy)
    simpa [Fin.sum_univ_two] using this
  have hne1 : k ![a1, b2] ≠ k ![b1, b2] := by
    intro h
    have e1 := hfoc a1 b2 ha1 hb2
    have e2 := hfoc b1 b2 hb1 hb2
    rw [h] at e1
    have := hlt1 (k ![b1, b2])
    linarith
  have hne2 : k ![b1, a2] ≠ k ![b1, b2] := by
    intro h
    have e1 := hfoc b1 a2 hb1 ha2
    have e2 := hfoc b1 b2 hb1 hb2
    rw [h] at e1
    have := hlt2 (k ![b1, b2])
    linarith
  have hpos := dc_mixed_pos (w1 := E.v 0) (w2 := E.v 1) (κ := fun x y => k ![x, y])
    (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)
    (fun x => by simpa [Fin.sum_univ_two] using hk _ (hbox a1 a2 ha1 ha2) x)
    (fun x hx => by
      simpa [Fin.sum_univ_two] using smallTypeEnv_strict_max E hk (hbox b1 b2 hb1 hb2) hx)
    (dc_delta_monotone (E.hasDerivAt_v 0) hlt1) (dc_delta_monotone (E.hasDerivAt_v 1) hlt2)
    hne1 hne2
  have hd : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      E.v 0 (k ![x, y]) x + E.v 1 (k ![x, y]) y = V 0 ![x, y] + V 1 ![x, y] :=
    fun x y hx hy => by simpa [Fin.sum_univ_two] using hdec _ (hbox x y hx hy)
  have hV0 : ∀ x x' y, V 0 ![x, y] = V 0 ![x', y] := fun x x' y => by
    rw [← hV 0 ![x', y] x, vec2_update0]
  have hV1 : ∀ x y y', V 1 ![x, y] = V 1 ![x, y'] := fun x y y' => by
    rw [← hV 1 ![x, y'] y, vec2_update1]
  rw [hd b1 b2 hb1 hb2, hd a1 b2 ha1 hb2, hd b1 a2 hb1 ha2, hd a1 a2 ha1 ha2,
    hV0 b1 a1 b2, hV0 b1 a1 a2, hV1 b1 b2 a2, hV1 a1 b2 a2] at hpos
  linarith

/-- **Budget balance in the differentiable case** (MWG, p. 882). With `I = 2`, nondegenerate
type intervals and the small-type assumptions, no social choice function `f = (k*, t)` with an
efficient project rule (23.C.15) and differentiable transfers is strategy-proof and budget
balanced on the box. (Proved through the Groves form and `exercise_23_C_10d`, not through
(23.C.16)-(23.C.17), which need second derivatives that MWG's assumptions do not provide.) -/
theorem differentiable_case_no_budget_balance (E : SmallTypeEnv (Fin 2)) {lo hi : Fin 2 → ℝ}
    (hlt : ∀ i, lo i < hi i) {k : (Fin 2 → ℝ) → ℝ} {t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) :
    ¬∀ θ, InBox lo hi θ → ∑ i, t θ i = 0 := fun hBB =>
  exercise_23_C_10d E hlt hk
    (exercise_23_C_10c_decomposition (by simp) E hk ht hSP hBB)

/-- The efficient project rule of the quadratic environment, `k*(θ) = ∑ᵢθᵢ/I`. -/
noncomputable def quadK [Fintype ι] (θ : ι → ℝ) : ℝ :=
  (∑ i, θ i) / Fintype.card ι

/-- The quadratic environment's `k*(θ) = ∑ᵢθᵢ/I` satisfies (23.C.7). -/
theorem quadK_efficient [Fintype ι] [Nonempty ι] :
    EfficientProject (quadEnv ι).v (quadK (ι := ι)) := by
  intro θ x
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  simp only [quadEnv, quadK, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
  set s := ∑ i, θ i
  set n : ℝ := (Fintype.card ι : ℝ)
  have : 0 ≤ (n * x - s) ^ 2 / (2 * n) := by positivity
  have e : s * (s / n) - n * ((s / n) ^ 2 / 2) - (s * x - n * (x ^ 2 / 2)) =
      (n * x - s) ^ 2 / (2 * n) := by field_simp; ring
  linarith

/-- **The differentiable case**, non-vacuity (MWG, pp. 881-882 and Exercise 23.C.9): in the
quadratic environment the Groves mechanism `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ)` with
`k*(θ) = ∑ᵢθᵢ/I` is `C¹`, efficient, strategy-proof on any box, has `∂²v/∂k∂θ > 0`, and `k*` is
nondecreasing in each `θᵢ`; so the hypotheses of `eq_23_C_14`, `exercise_23_C_9`,
`differentiable_case_groves` and `differentiable_case_no_budget_balance` (all but budget
balance) are jointly satisfiable. -/
theorem differentiable_case_instance [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lo hi : ι → ℝ) :
    EfficientOnBox (quadEnv ι).v lo hi quadK ∧
      StrategyProofOnBox (quadEnv ι).v lo hi quadK
        (grovesTransfer (quadEnv ι).v quadK fun _ _ => 0) ∧
      ContDiff ℝ 1 (quadK (ι := ι)) ∧
      (∀ i, ContDiff ℝ 1 fun θ => grovesTransfer (quadEnv ι).v quadK (fun _ _ => 0) θ i) ∧
      (∀ i x θ, 0 < (quadEnv ι).vkθ i x θ) ∧
      ∀ i (θ : ι → ℝ), Monotone fun s => quadK (update θ i s) := by
  have hk := quadK_efficient.efficientOnBox (ι := ι) lo hi
  have hcd : ContDiff ℝ 1 (quadK (ι := ι)) := by
    unfold quadK
    fun_prop
  refine ⟨hk, groves_strategyProofOnBox hk fun _ _ _ => rfl, hcd, fun i => ?_,
    fun _ _ _ => one_pos, fun i θ s s' hss' => ?_⟩
  · simp only [grovesTransfer, quadEnv, add_zero]
    exact ContDiff.sum fun j _ => ((contDiff_apply ℝ ℝ j).mul hcd).sub
      ((hcd.pow 2).div_const 2)
  · simp only [quadK]
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [sum_update_split (fun _ x => x), sum_update_split (fun _ x => x)]
    gcongr

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bargaining, trading and auction exercises

MWG, Exercises 23.D.1, 23.D.4, 23.D.5, 23.D.6 (pp. 920-921) and 23.E.4, 23.E.5, 23.E.6
(p. 922).

* **Exercise 23.D.1** (Myerson): (a) the alternatives (`BargainX`); (b) with seller types
  `{0, 9}`, buyer value `10`, prices `(10 + θₛ)/2`, immediate trade for `θₛ = 0` and trade in
  period `n + 1` for `θₛ = 9`, the outcome is incentive compatible iff `19δⁿ ≤ 10`, i.e. iff
  `n ≥ ⌈log(10/19)/log δ⌉` (`exercise_23_D_1b`): the earliest trade time is
  `1 + ⌈log(10/19)/log δ⌉`.
* **Exercise 23.D.4** (first-price auction): (a) the interim probability of winning is
  nondecreasing in the type and bids are nondecreasing among types that win with positive
  probability (`exercise_23_D_4a`); (b) no interval of types bids the same amount when tying
  bidders win with positive probability and winning ties for sure is a discrete gain
  (`exercise_23_D_4b`), so equilibrium bids are strictly increasing
  (`exercise_23_D_4b_strictMono`); (c) revenue equivalence with the second-price auction
  (`exercise_23_D_4c`). Non-vacuity: the two-bidder uniform equilibrium `b(θ) = θ/2`
  (`exercise_23_D_4_instance`).
* **Exercise 23.D.5** (all-pay auction): monotonicity (`exercise_23_D_5_monotone`) and revenue
  equivalence (`exercise_23_D_5`).
* **Exercise 23.D.6** (queue): `I = n + 1` individuals with uniform values; waiting `w` hours
  before the office opens costs `βw` to the first in line only (a first-price auction with bid
  `βw`). `w(θ) = nθ/((n + 1)β)` is a symmetric equilibrium (`exercise_23_D_6_bne`) and the
  expected wait of the first in line is `(I - 1)/((I + 1)β)` (`exercise_23_D_6`): doubling `β`
  halves it, doubling `I` raises it.
* **Exercise 23.E.4** (discounting): ex post efficiency requires immediate trade when `θ₂ > θ₁`
  and no trade when `θ₁ > θ₂` (`exercise_23_E_4_efficient`); with `ȳ = δ^(t-1)` the trading
  process is a bilateral trade social choice function (`exercise_23_E_4_payoffs`), and
  Proposition 23.E.1 rules out ex post efficiency (`exercise_23_E_4`).
* **Exercise 23.E.5** (continuum of traders): (a) the threshold rule at a market-clearing price
  maximises the gains from trade among all mass-balanced trades (`exercise_23_E_5a`); (b) the
  competitive (posted price) mechanism makes truth telling dominant (hence Bayesian incentive
  compatible), is individually rational and balances the budget (`exercise_23_E_5b`).
* **Exercise 23.E.6** (partnership): (a) the higher valuation gets both units
  (`exercise_23_E_6a`); (b) `b(θ) = 2θ/3` is a symmetric Bayesian Nash equilibrium of "highest
  bidder buys and pays his bid" (`exercise_23_E_6b`); (c) the implemented social choice function
  is Bayesian incentive compatible, ex post efficient and individually rational, with
  `Uᵢ(θᵢ) = θᵢ² + 1/3 > θᵢ` (`exercise_23_E_6c`).

**Departures.** Exercise 23.D.4(a) is proved for types with positive winning probability (bids
that never win are payoff irrelevant and are not pinned down by the equilibrium conditions);
the auction-theoretic primitives of 23.D.4(a), (b) and 23.D.5 are stated for a general
winning-probability function `P(b)` (nondecreasing in the bid, as it is whatever the others'
strategies). In 23.D.6 the probability that a given individual is first in line, given his
value `θ`, is the independence formula `θⁿ`. In 23.E.5 traders are modelled by finite
measures of sellers' and buyers' values (equal masses are not needed).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-! ## Exercise 23.D.1 -/

/-- **Exercise 23.D.1(a)** (MWG, p. 920). The set of alternatives of the bargaining problem:
`none` is "no trade" and `some (n, p)` is "trade in period `n + 1` at price `p`", that is
`X = {no trade} ∪ ({1, 2, …} × ℝ)`. -/
def BargainX : Type := Option (ℕ × ℝ)

/-- **Exercise 23.D.1(a)**: the seller's (discounted) gain from an alternative,
`δ^(t-1)(p - θₛ)` if trade occurs in period `t` at price `p`, `0` without trade. -/
noncomputable def bargSellerU (δ θs : ℝ) (x : BargainX) : ℝ :=
  Option.elim x 0 fun np => δ ^ np.1 * (np.2 - θs)

/-- **Exercise 23.D.1(a)**: the buyer's (discounted) gain `δ^(t-1)(θ_b - p)`. -/
noncomputable def bargBuyerU (δ θb : ℝ) (x : BargainX) : ℝ :=
  Option.elim x 0 fun np => δ ^ np.1 * (θb - np.2)

/-- The outcome of Exercise 23.D.1(b): price `(10 + θₛ)/2`, immediate trade when `θₛ = 0`
(`false`) and trade in period `n + 1` when `θₛ = 9` (`true`). -/
noncomputable def bargOutcome (n : ℕ) (high : Bool) : BargainX :=
  if high then some (n, 19 / 2) else some (0, 5)

/-- The seller's valuation: `0` (`false`) or `9` (`true`). -/
def bargSellerVal (high : Bool) : ℝ := if high then 9 else 0

/-- **Exercise 23.D.1(b)** (MWG, pp. 920-921). By the revelation principle the outcome of a
Bayesian Nash equilibrium is incentive compatible for the seller (the buyer's value `10` is
known). With discount factor `0 < δ < 1`, the outcome (immediate trade at `5` when `θₛ = 0`,
trade in period `n + 1` at `9.5` when `θₛ = 9`) is incentive compatible and individually
rational iff `19δⁿ ≤ 10`, iff `n ≥ log(10/19)/log δ`, iff `n ≥ ⌈log(10/19)/log δ⌉`. So the
earliest possible time of trade when `θₛ = 9` is period `1 + ⌈log(10/19)/log δ⌉`. -/
theorem exercise_23_D_1b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    ((∀ θ θh : Bool, bargSellerU δ (bargSellerVal θ) (bargOutcome n θh) ≤
        bargSellerU δ (bargSellerVal θ) (bargOutcome n θ)) ∧
      (∀ θ, 0 ≤ bargSellerU δ (bargSellerVal θ) (bargOutcome n θ)) ∧
      ∀ θ, 0 ≤ bargBuyerU δ 10 (bargOutcome n θ)) ↔ 19 * δ ^ n ≤ 10 ∧
      (19 * δ ^ n ≤ 10 ↔ Real.log (10 / 19) / Real.log δ ≤ n) ∧
      (19 * δ ^ n ≤ 10 ↔ ⌈Real.log (10 / 19) / Real.log δ⌉₊ ≤ n) := by
  have hpos : 0 < δ ^ n := pow_pos hδ0 n
  have hlog : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  have hiff : 19 * δ ^ n ≤ 10 ↔ Real.log (10 / 19) / Real.log δ ≤ n := by
    rw [div_le_iff_of_neg hlog, ← Real.log_pow, Real.log_le_log_iff hpos (by norm_num)]
    constructor <;> intro h <;> linarith
  have hiff2 : 19 * δ ^ n ≤ 10 ↔ ⌈Real.log (10 / 19) / Real.log δ⌉₊ ≤ n := by
    rw [Nat.ceil_le, hiff]
  constructor
  · rintro ⟨hic, -, -⟩
    have h := hic false true
    simp [bargSellerU, bargOutcome, bargSellerVal] at h
    exact ⟨by linarith, hiff, hiff2⟩
  · rintro ⟨h, -, -⟩
    refine ⟨fun θ θh => ?_, fun θ => ?_, fun θ => ?_⟩
    · cases θ <;> cases θh <;> simp [bargSellerU, bargOutcome, bargSellerVal] <;> nlinarith
    · cases θ <;> simp [bargSellerU, bargOutcome, bargSellerVal]
      nlinarith
    · cases θ <;> simp [bargBuyerU, bargOutcome] <;> nlinarith

/-! ## Exercise 23.E.4 -/

/-- **Exercise 23.E.4** (MWG, p. 922). A (deterministic) trading process: `τ(θ) = some n` is
trade in period `n + 1`, `none` no trade. The seller (agent `0`) holds the good with
"probability" `ȳ₀ = 1 - δⁿ` and the buyer with `ȳ₁ = δⁿ` (expected discounted trade). -/
noncomputable def discY (δ : ℝ) (τ : (Fin 2 → ℝ) → Option ℕ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => Option.elim (τ θ) ![1, 0] fun n => ![1 - δ ^ n, δ ^ n]

/-- **Exercise 23.E.4** (MWG, p. 922). With trade in period `n + 1` at price `p` the seller gets
`θ₁ + δⁿ(p - θ₁) = θ₁(1 - δⁿ) + δⁿp` and the buyer `δⁿ(θ₂ - p) = θ₂δⁿ - δⁿp`: utilities of the
form `θᵢȳᵢ + tᵢ` with `ȳ = discY` and discounted transfers, so the discounted setting is the
bilateral trade setting of Section 23.E. -/
theorem exercise_23_E_4_payoffs (δ θs θb p : ℝ) (n : ℕ) :
    θs + δ ^ n * (p - θs) = θs * (1 - δ ^ n) + δ ^ n * p ∧
      δ ^ n * (θb - p) = θb * δ ^ n + -(δ ^ n * p) := by
  constructor <;> ring

/-- Total surplus of a trading outcome: `θ₁ + δⁿ(θ₂ - θ₁)` with trade in period `n + 1`, `θ₁`
without trade. -/
noncomputable def discSurplus (δ : ℝ) (θ : Fin 2 → ℝ) (o : Option ℕ) : ℝ :=
  θ 0 + Option.elim o 0 (fun n => δ ^ n) * (θ 1 - θ 0)

/-- **Exercise 23.E.4** (MWG, p. 922), "Note that ex post efficiency requires that trade occur
in period 1 whenever `θ₂ > θ₁`, and that trade not occur whenever `θ₁ > θ₂`": with
`0 < δ < 1`, an outcome maximises total surplus iff it has these two properties. -/
theorem exercise_23_E_4_efficient {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (θ : Fin 2 → ℝ)
    (o : Option ℕ) :
    (∀ o', discSurplus δ θ o' ≤ discSurplus δ θ o) ↔
      (θ 0 < θ 1 → o = some 0) ∧ (θ 1 < θ 0 → o = none) := by
  have hw : ∀ o' : Option ℕ, 0 ≤ Option.elim o' 0 (fun n => δ ^ n) ∧
      Option.elim o' 0 (fun n => δ ^ n) ≤ 1 := by
    intro o'
    cases o' with
    | none => simp
    | some n => exact ⟨by simp [(pow_pos hδ0 n).le], by simp [pow_le_one₀ hδ0.le hδ1.le]⟩
  constructor
  · intro h
    refine ⟨fun hlt => ?_, fun hlt => ?_⟩
    · have h0 := h (some 0)
      cases o with
      | none => simp only [discSurplus, Option.elim] at h0; norm_num at h0; linarith
      | some n =>
        rcases n with _ | n
        · rfl
        · simp only [discSurplus, Option.elim, pow_zero] at h0
          have : δ ^ (n + 1) < 1 := pow_lt_one₀ hδ0.le hδ1 (by omega)
          nlinarith
    · have h0 := h none
      cases o with
      | none => rfl
      | some n =>
        simp only [discSurplus, Option.elim] at h0
        have := pow_pos hδ0 n
        nlinarith
  · rintro ⟨h1, h2⟩ o'
    obtain ⟨hw0, hw1⟩ := hw o'
    have e1 : Option.elim (some 0) (0 : ℝ) (fun n => δ ^ n) = 1 := by simp
    have e0 : Option.elim (none : Option ℕ) (0 : ℝ) (fun n => δ ^ n) = 0 := rfl
    rcases lt_trichotomy (θ 0) (θ 1) with hlt | heq | hgt
    · rw [h1 hlt]
      simp only [discSurplus, e1]
      nlinarith
    · simp only [discSurplus, heq, sub_self, mul_zero, le_refl]
    · rw [h2 hgt]
      simp only [discSurplus, e0]
      nlinarith

/-- **Exercise 23.E.4** (MWG, p. 922). Under the assumptions of Proposition 23.E.1 (independent
valuations with strictly positive densities, `(θ̲₂, θ̄₂) ∩ (θ̲₁, θ̄₁) ≠ ∅`) and discounting
`0 < δ < 1`, no voluntary trading process achieves ex post efficiency: no trading process with
immediate trade when `θ₂ > θ₁` and no trade when `θ₁ > θ₂`, budget balanced (discounted)
transfers, Bayesian incentive compatibility and interim individual rationality exists. (The
seller is agent `0`, the buyer agent `1`; the process enters through `ȳ = discY δ τ`.) -/
theorem exercise_23_E_4 (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {τ : (Fin 2 → ℝ) → Option ℕ} {t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable (discY δ τ))
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV (discY δ τ) t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ →
      (θ 0 < θ 1 → τ θ = some 0) ∧ (θ 1 < θ 0 → τ θ = none))
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV (discY δ τ) t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) (discY δ τ) t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  refine proposition_23_E_1 D hov hym hint ht (fun θ hθ => ?_) hbb hbic hir
  obtain ⟨h1, h2⟩ := heff θ hθ
  have hb : ∀ n : ℕ, 0 ≤ δ ^ n ∧ δ ^ n ≤ 1 := fun n =>
    ⟨(pow_pos hδ0 n).le, pow_le_one₀ hδ0.le hδ1.le⟩
  refine ⟨?_, ?_, ?_, fun hlt => ?_, fun hlt => ?_⟩
  · simp only [discY]
    cases τ θ <;> simp
  · simp only [discY]
    cases τ θ <;> simp [hb]
  · simp only [discY]
    cases τ θ <;> simp [hb]
  · simp [discY, h1 hlt]
  · simp [discY, h2 hlt]

/-! ## Exercise 23.E.5 -/

/-- **Exercise 23.E.5** (MWG, p. 922). A price `p` clears the market: the mass of sellers with
valuation below `p` equals the mass of buyers with valuation above `p`. -/
def MarketClears (μS μB : Measure ℝ) (p : ℝ) : Prop :=
  μS.real (Set.Iio p) = μB.real (Set.Ioi p)

/-- **Exercise 23.E.5(a)** (MWG, p. 922). With a continuum of sellers (valuations distributed
by the finite measure `μS`) and buyers (`μB`), let `p` clear the market. Among all trades in
which a measurable set `S` of seller valuations sells and a measurable set `B` of buyer
valuations buys, with equal masses `μS(S) = μB(B)`, the gains from trade
`∫_B θ dμB - ∫_S θ dμS` are maximised by the threshold rule: sellers with `θ₁ < p` sell and
buyers with `θ₂ > p` buy. -/
theorem exercise_23_E_5a {μS μB : Measure ℝ} [IsFiniteMeasure μS] [IsFiniteMeasure μB]
    (hS : Integrable (fun x : ℝ => x) μS) (hB : Integrable (fun x : ℝ => x) μB) {p : ℝ}
    (hp : MarketClears μS μB p) {S B : Set ℝ} (hSm : MeasurableSet S) (hBm : MeasurableSet B)
    (hbal : μS.real S = μB.real B) :
    (∫ x in B, x ∂μB) - (∫ x in S, x ∂μS) ≤
      (∫ x in Set.Ioi p, x ∂μB) - ∫ x in Set.Iio p, x ∂μS := by
  have hgS : Integrable (fun x : ℝ => x - p) μS := hS.sub (integrable_const p)
  have hgB : Integrable (fun x : ℝ => x - p) μB := hB.sub (integrable_const p)
  have split : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], Integrable (fun x : ℝ => x) μ →
      ∀ A : Set ℝ, ∫ x in A, x ∂μ = (∫ x in A, (x - p) ∂μ) + μ.real A * p := by
    intro μ _ hμ A
    rw [integral_sub hμ.integrableOn (integrableOn_const), setIntegral_const, smul_eq_mul]
    ring
  rw [split μB hB B, split μS hS S, split μB hB (Set.Ioi p), split μS hS (Set.Iio p), hbal, hp]
  have hB' : ∫ x in B, (x - p) ∂μB ≤ ∫ x in Set.Ioi p, (x - p) ∂μB := by
    rw [← integral_indicator hBm, ← integral_indicator measurableSet_Ioi]
    refine integral_mono (hgB.indicator hBm) (hgB.indicator measurableSet_Ioi) fun x => ?_
    by_cases hxB : x ∈ B <;> by_cases hxp : p < x <;>
      simp [Set.indicator, hxB, hxp] <;> linarith
  have hS' : ∫ x in Set.Iio p, (x - p) ∂μS ≤ ∫ x in S, (x - p) ∂μS := by
    rw [← integral_indicator hSm, ← integral_indicator measurableSet_Iio]
    refine integral_mono (hgS.indicator measurableSet_Iio) (hgS.indicator hSm) fun x => ?_
    by_cases hxS : x ∈ S <;> by_cases hxp : x < p <;>
      simp [Set.indicator, hxS, hxp] <;> linarith
  linarith

/-- The competitive mechanism of Exercise 23.E.5(b) for a seller of valuation `θ` who reports
`r`: he sells at the market price `p` iff `r < p`. -/
noncomputable def compSellerU (p θ r : ℝ) : ℝ := if r < p then p else θ

/-- The competitive mechanism for a buyer of valuation `θ` who reports `r`: he buys at `p` iff
`r > p`. -/
noncomputable def compBuyerU (p θ r : ℝ) : ℝ := if p < r then θ - p else 0

/-- **Exercise 23.E.5(b)** (MWG, p. 922). In the competitive mechanism (a single trader's report
does not affect the market-clearing price `p` of a continuum economy) truth telling is a dominant
strategy for every seller and buyer, hence Bayesian incentive compatible; it is individually
rational (a seller gets at least his valuation, a buyer at least `0`); it implements the
threshold trading rule of (a); and with a market-clearing price the payments balance. -/
theorem exercise_23_E_5b (p : ℝ) :
    (∀ θ r, compSellerU p θ r ≤ compSellerU p θ θ) ∧
      (∀ θ r, compBuyerU p θ r ≤ compBuyerU p θ θ) ∧
      (∀ θ, θ ≤ compSellerU p θ θ) ∧ (∀ θ, 0 ≤ compBuyerU p θ θ) ∧
      ∀ μS μB : Measure ℝ, MarketClears μS μB p →
        p * μB.real (Set.Ioi p) - p * μS.real (Set.Iio p) = 0 := by
  refine ⟨fun θ r => ?_, fun θ r => ?_, fun θ => ?_, fun θ => ?_, fun μS μB h => ?_⟩
  · simp only [compSellerU]; split_ifs <;> linarith
  · simp only [compBuyerU]; split_ifs <;> linarith
  · simp only [compSellerU]; split_ifs <;> linarith
  · simp only [compBuyerU]; split_ifs <;> linarith
  · rw [h]; ring

/-! ## Exercise 23.E.6 -/

/-- **Exercise 23.E.6(a)** (MWG, p. 922). Each partner owns one unit and values each unit
consumed at `θᵢ`. Among allocations `x₀ + x₁ = 2`, `xᵢ ≥ 0`, total value is at most
`2 max(θ₀, θ₁)`, attained by giving both units to the higher valuation; when `θ₀ < θ₁` it is
attained only by `x₁ = 2` (the efficient trading rule: the higher valuation buys the other's
unit). -/
theorem exercise_23_E_6a (θ0 θ1 x0 x1 : ℝ) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hsum : x0 + x1 = 2) :
    θ0 * x0 + θ1 * x1 ≤ 2 * max θ0 θ1 ∧
      (θ0 < θ1 → (θ0 * x0 + θ1 * x1 = 2 * max θ0 θ1 ↔ x1 = 2)) := by
  have hx0' : x0 = 2 - x1 := by linarith
  subst hx0'
  refine ⟨?_, fun hlt => ?_⟩
  · rcases le_total θ0 θ1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right hlt.le]
    constructor
    · intro h
      by_contra hne
      have : x1 < 2 := lt_of_le_of_ne (by linarith) hne
      nlinarith
    · intro h; rw [h]; ring

/-- `x ↦ 1{x ≤ τ} A` is interval integrable on `[0, 1]`. -/
theorem trade_ii_le (τ A : ℝ) :
    IntervalIntegrable (fun x : ℝ => if x ≤ τ then A else 0) volume 0 1 := by
  have h : (fun x : ℝ => if x ≤ τ then A else 0) = (Set.Iic τ).indicator fun _ => A := by
    funext x; simp [Set.indicator_apply]
  rw [h, intervalIntegrable_iff]
  exact (intervalIntegrable_const (c := A) (a := (0 : ℝ)) (b := 1)).def'.indicator
    measurableSet_Iic

/-- Exercise 23.E.6(b): the expected utility of a partner with valuation `θ` who bids `β` when
the other (valuation `s ~ U[0, 1]`) bids `2s/3`: if `β ≥ 2s/3` he buys the other's unit and pays
`β` (utility `2θ - β`), otherwise the other buys and pays him `2s/3`. -/
noncomputable def partnerEU (β θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, if 2 * s / 3 ≤ β then 2 * θ - β else 2 * s / 3

/-- Closed form of `partnerEU`: with `c = clamp(3β/2)`, `(2θ - β)c + (1 - c²)/3`. -/
theorem partnerEU_eq (β θ : ℝ) :
    partnerEU β θ = (2 * θ - β) * clamp01 (3 * β / 2) + (1 - clamp01 (3 * β / 2) ^ 2) / 3 := by
  have e : (fun s : ℝ => if 2 * s / 3 ≤ β then 2 * θ - β else 2 * s / 3) =
      fun s => (if s ≤ 3 * β / 2 then 2 * θ - β else 0) +
        (if 3 * β / 2 < s then 0 + 2 / 3 * s else 0) := by
    funext s
    by_cases h : 2 * s / 3 ≤ β
    · have h1 : s ≤ 3 * β / 2 := by linarith
      simp [h, h1, not_lt.2 h1]
    · have h1 : ¬s ≤ 3 * β / 2 := by intro h'; apply h; linarith
      have h2 : 3 * β / 2 < s := lt_of_not_ge h1
      simp only [h, h1, h2, ite_false, ite_true]
      ring
  rw [partnerEU, e, intervalIntegral.integral_add (trade_ii_le _ _) (au_ii_gt _ _ _),
    au_int_le, au_int_gt, au_int_affine, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Exercise 23.E.6(b)** (MWG, p. 922). In the mechanism "each partner bids; the highest
bidder buys the other's unit and pays him his bid", with valuations independent and uniform on
`[0, 1]`, the linear strategy `b(θ) = 2θ/3` is a symmetric Bayesian Nash equilibrium: against
`b`, no bid `β ∈ ℝ` does better than `2θ/3`. -/
theorem exercise_23_E_6b {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (β : ℝ) :
    partnerEU β θ ≤ partnerEU (2 * θ / 3) θ := by
  have e : 3 * (2 * θ / 3) / 2 = θ := by ring
  rw [partnerEU_eq, partnerEU_eq, e, clamp01_of_mem hθ]
  rcases le_or_gt (3 * β / 2) 0 with h | h
  · rw [clamp01_of_nonpos h]; nlinarith
  · rcases le_or_gt 1 (3 * β / 2) with h1 | h1
    · rw [clamp01_of_one_le h1]; nlinarith [hθ.2]
    · rw [clamp01_of_mem ⟨h.le, h1.le⟩]; nlinarith [sq_nonneg (θ - 3 * β / 2)]

/-- The interim utility of the equilibrium of Exercise 23.E.6(b): `U(θ) = θ² + 1/3`. -/
theorem partnerEU_eq_equilibrium {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    partnerEU (2 * θ / 3) θ = θ ^ 2 + 1 / 3 := by
  have e : 3 * (2 * θ / 3) / 2 = θ := by ring
  rw [partnerEU_eq, e, clamp01_of_mem hθ]
  ring

/-- The social choice function implemented in Exercise 23.E.6(c): agent `0` gets both units
(`2`) iff `θ₁ ≤ θ₀`, and the buyer pays the seller `2θ_buyer/3`. -/
noncomputable def partnerSCF (θ : Fin 2 → ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  if θ 1 ≤ θ 0 then (![2, 0], ![-(2 * θ 0 / 3), 2 * θ 0 / 3])
  else (![0, 2], ![2 * θ 1 / 3, -(2 * θ 1 / 3)])

/-- **Exercise 23.E.6(c)** (MWG, p. 922). The social choice function implemented by the
equilibrium of (b) (the higher valuation buys the other's unit at two thirds of his valuation)
is Bayesian incentive compatible (announcing `r` amounts to bidding `2r/3`), ex post efficient
(both units go to the higher valuation and transfers balance), and individually rational:
`Uᵢ(θᵢ) = θᵢ² + 1/3 > θᵢ`, the value of consuming one's own unit. Unlike the
Myerson-Satterthwaite setting, ownership is split, so every type is a potential buyer and
seller. -/
theorem exercise_23_E_6c :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      partnerEU (2 * r / 3) θ ≤ partnerEU (2 * θ / 3) θ) ∧
      (∀ θ : Fin 2 → ℝ, θ 0 * (partnerSCF θ).1 0 + θ 1 * (partnerSCF θ).1 1 =
        2 * max (θ 0) (θ 1) ∧ (partnerSCF θ).2 0 + (partnerSCF θ).2 1 = 0) ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, partnerEU (2 * θ / 3) θ = θ ^ 2 + 1 / 3 ∧
        θ < partnerEU (2 * θ / 3) θ := by
  refine ⟨fun θ hθ r _ => exercise_23_E_6b hθ _, fun θ => ?_, fun θ hθ => ?_⟩
  · simp only [partnerSCF]
    split_ifs with h
    · simp [max_eq_left h]; ring
    · simp [max_eq_right (le_of_lt (lt_of_not_ge h))]; ring
  · rw [partnerEU_eq_equilibrium hθ]
    exact ⟨rfl, by nlinarith [sq_nonneg (θ - 1 / 2)]⟩

/-! ## Exercises 23.D.4 and 23.D.5 -/

/-- **Exercise 23.D.4(a)** (MWG, p. 921). In a first-price auction let `P(b)` be a bidder's
probability of winning with bid `b` given the others' strategies (nondecreasing in `b`), and let
`b*(θ)` be a best response for every type in `[θ̲, θ̄]`: `(θ - b)P(b) ≤ (θ - b*(θ))P(b*(θ))`.
Then for `θ < θ'`: the interim probability of winning is nondecreasing,
`P(b*(θ)) ≤ P(b*(θ'))` (the monotonicity of `ȳ` that Bayesian incentive compatibility
requires), and if `θ` wins with positive probability then `b*(θ) ≤ b*(θ')`. -/
theorem exercise_23_D_4a {P b : ℝ → ℝ} (hP : Monotone P) {lo hi : ℝ}
    (hBR : ∀ θ ∈ Set.Icc lo hi, ∀ β, (θ - β) * P β ≤ (θ - b θ) * P (b θ)) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc lo hi) (hθ' : θ' ∈ Set.Icc lo hi) (hlt : θ < θ') :
    P (b θ) ≤ P (b θ') ∧ (0 < P (b θ) → b θ ≤ b θ') := by
  have h1 := hBR θ hθ (b θ')
  have h2 := hBR θ' hθ' (b θ)
  have hy : P (b θ) ≤ P (b θ') := by nlinarith
  refine ⟨hy, fun hpos => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have heq : P (b θ') = P (b θ) := le_antisymm (hP hcon.le) hy
  rw [heq] at h1
  nlinarith

/-- **Exercise 23.D.4(b)** (MWG, p. 921). Suppose types in `(θ', θ'')`, `θ' < θ''`, all bid the
same `β` in a symmetric equilibrium. Then tying bidders win with positive probability,
`P(β) > 0`, and bidding slightly more wins all ties: `P(β) + q ≤ P(β')` for all `β' > β`, for
some `q > 0`. Under these conditions no such interval of types can be best responding. -/
theorem exercise_23_D_4b {P b : ℝ → ℝ} {θ' θ'' β : ℝ} (hlt : θ' < θ'')
    (hBR : ∀ θ ∈ Set.Ioo θ' θ'', ∀ β', (θ - β') * P β' ≤ (θ - b θ) * P (b θ))
    (hflat : ∀ θ ∈ Set.Ioo θ' θ'', b θ = β) (hpos : 0 < P β)
    (hjump : ∃ q > 0, ∀ β' > β, P β + q ≤ P β') : False := by
  obtain ⟨q, hq, hj⟩ := hjump
  -- a type in the interval different from `β`
  obtain ⟨θ, hθ, hne⟩ : ∃ θ ∈ Set.Ioo θ' θ'', θ ≠ β := by
    by_cases h : (θ' + θ'') / 2 = β
    · refine ⟨(3 * θ' + θ'') / 4, ⟨by linarith, by linarith⟩, ?_⟩
      intro h'; linarith
    · exact ⟨(θ' + θ'') / 2, ⟨by linarith, by linarith⟩, h⟩
  have hb := hflat θ hθ
  rcases hne.lt_or_gt with hθβ | hθβ
  · -- bidding `θ` gives `0 > (θ - β)P(β)`
    have := hBR θ hθ θ
    rw [hb] at this
    nlinarith
  · -- bidding `β + ε` with `ε = (θ - β)q/(2(P(β) + q))` is better
    set d := θ - β with hd
    have hd0 : 0 < d := by linarith
    set ε := d * q / (2 * (P β + q)) with hε
    have hε0 : 0 < ε := by positivity
    have hεd : ε < d := by
      rw [hε, div_lt_iff₀ (by positivity)]
      nlinarith
    have h1 := hBR θ hθ (β + ε)
    have h2 := hj (β + ε) (by linarith)
    rw [hb] at h1
    have h3 : (θ - (β + ε)) * (P β + q) ≤ (θ - (β + ε)) * P (β + ε) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : (θ - (β + ε)) * (P β + q) = d * P β + (d * q - ε * (P β + q)) := by ring
    have h5 : ε * (P β + q) = d * q / 2 := by
      rw [hε]; field_simp
    nlinarith

/-- **Exercise 23.D.4(b)**, conclusion (MWG, p. 921): bids that are nondecreasing on an interval
and constant on no subinterval are strictly increasing there. -/
theorem exercise_23_D_4b_strictMono {b : ℝ → ℝ} {lo hi : ℝ}
    (hmono : MonotoneOn b (Set.Icc lo hi))
    (hnoflat : ∀ θ' θ'', lo ≤ θ' → θ' < θ'' → θ'' ≤ hi → ¬∀ θ ∈ Set.Ioo θ' θ'', b θ = b θ') :
    StrictMonoOn b (Set.Icc lo hi) := by
  intro x hx y hy hxy
  rcases (hmono hx hy hxy.le).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hnoflat x y hx.1 hxy hy.2
    intro θ hθ
    have h1 := hmono hx ⟨hx.1.trans hθ.1.le, hθ.2.le.trans hy.2⟩ hθ.1.le
    have h2 := hmono ⟨hx.1.trans hθ.1.le, hθ.2.le.trans hy.2⟩ hy hθ.2.le
    rw [← h] at h2
    exact le_antisymm h2 h1

/-- Non-vacuity of Exercise 23.D.4(a): with two bidders uniform on `[0, 1]`, against the other's
bid `θ/2` the winning probability is `P(b) = clamp(2b)` and `b*(θ) = θ/2` is a best response for
every type (Example 23.B.5). -/
theorem exercise_23_D_4_instance :
    Monotone (fun β : ℝ => clamp01 (2 * β)) ∧ ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ β,
      (θ - β) * clamp01 (2 * β) ≤ (θ - θ / 2) * clamp01 (2 * (θ / 2)) := by
  refine ⟨fun x y hxy => ?_, fun θ hθ β => ?_⟩
  · simp only [clamp01]
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · have e : 2 * (θ / 2) = θ := by ring
    rw [e, clamp01_of_mem hθ]
    rcases le_or_gt (2 * β) 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith [hθ.1]
    · rcases le_or_gt 1 (2 * β) with h1 | h1
      · rw [clamp01_of_one_le h1]; nlinarith [hθ.2]
      · rw [clamp01_of_mem ⟨h.le, h1.le⟩]; nlinarith [sq_nonneg (θ - 2 * β)]

/-- **Exercise 23.D.4(c)** (MWG, p. 921). By the revenue equivalence theorem: the social choice
function of any symmetric equilibrium of the first-price auction and that of the dominant
strategy equilibrium of the second-price auction are Bayesian incentive compatible, have the same
allocation `y` (by (b), the highest valuation wins) and give the lowest types `Uᵢ(θ̲ᵢ) = 0`;
hence they yield the same expected revenue (`proposition_23_D_3`). -/
theorem exercise_23_D_4c {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y tFP tSP : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y tFP lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y tSP lo hi)
    (ht : ∀ i, Integrable (fun θ => tFP θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => tSP θ i) (Measure.pi μ))
    (hFP : BayesianICOn (Measure.pi μ) allocV y tFP lo hi)
    (hSP : BayesianICOn (Measure.pi μ) allocV y tSP lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y tFP i (lo i) = 0)
    (hU' : ∀ i, interimU (Measure.pi μ) allocV y tSP i (lo i) = 0) :
    ∑ i, ∫ θ, -tFP θ i ∂Measure.pi μ = ∑ i, ∫ θ, -tSP θ i ∂Measure.pi μ :=
  (proposition_23_D_3 μ hsupp hint hint' ht ht' hFP hSP fun i => (hU i).trans (hU' i).symm).2

/-- **Exercise 23.D.5** (MWG, p. 921), the all-pay auction, monotonicity step (as in
Exercise 23.D.4(a)): if every type best responds, `θP(β) - β ≤ θP(b(θ)) - b(θ)`, then the
interim winning probability and the bid are nondecreasing in the type. -/
theorem exercise_23_D_5_monotone {P b : ℝ → ℝ} (hP : Monotone P) {lo hi : ℝ}
    (hBR : ∀ θ ∈ Set.Icc lo hi, ∀ β, θ * P β - β ≤ θ * P (b θ) - b θ) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc lo hi) (hθ' : θ' ∈ Set.Icc lo hi) (hlt : θ < θ') :
    P (b θ) ≤ P (b θ') ∧ b θ ≤ b θ' := by
  have h1 := hBR θ hθ (b θ')
  have h2 := hBR θ' hθ' (b θ)
  have hy : P (b θ) ≤ P (b θ') := by nlinarith
  refine ⟨hy, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have heq : P (b θ') = P (b θ) := le_antisymm (hP hcon.le) hy
  rw [heq] at h1
  linarith

/-- **Exercise 23.D.5** (MWG, p. 921). The all-pay auction: its symmetric equilibrium social
choice function (every buyer pays his bid, the highest bidder wins) is Bayesian incentive
compatible with the same allocation as the second-price auction and `Uᵢ(θ̲ᵢ) = 0`, so by the
revenue equivalence theorem it yields the same expected revenue. -/
theorem exercise_23_D_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y tAP tSP : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y tAP lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y tSP lo hi)
    (ht : ∀ i, Integrable (fun θ => tAP θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => tSP θ i) (Measure.pi μ))
    (hAP : BayesianICOn (Measure.pi μ) allocV y tAP lo hi)
    (hSP : BayesianICOn (Measure.pi μ) allocV y tSP lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y tAP i (lo i) = 0)
    (hU' : ∀ i, interimU (Measure.pi μ) allocV y tSP i (lo i) = 0) :
    ∑ i, ∫ θ, -tAP θ i ∂Measure.pi μ = ∑ i, ∫ θ, -tSP θ i ∂Measure.pi μ :=
  exercise_23_D_4c μ hsupp hint hint' ht ht' hAP hSP hU hU'

/-! ## Exercise 23.D.6 -/

/-- `(n + 1)θxⁿ - nxⁿ⁺¹ ≤ θⁿ⁺¹` for `x > 0`, `θ ≥ 0` (Bernoulli's inequality). -/
theorem queue_bernoulli (n : ℕ) {θ x : ℝ} (hθ : 0 ≤ θ) (hx : 0 < x) :
    (n + 1) * θ * x ^ n - n * x ^ (n + 1) ≤ θ ^ (n + 1) := by
  have hb := one_add_mul_le_pow (a := θ / x - 1) (by have := div_nonneg hθ hx.le; linarith)
    (n + 1)
  have e : 1 + (θ / x - 1) = θ / x := by ring
  rw [e, div_pow] at hb
  have hxn : 0 < x ^ (n + 1) := pow_pos hx _
  rw [le_div_iff₀ hxn] at hb
  have e2 : (1 + ((n + 1 : ℕ) : ℝ) * (θ / x - 1)) * x ^ (n + 1) =
      (n + 1) * θ * x ^ n - n * x ^ (n + 1) := by
    push_cast
    field_simp
    ring
  linarith

/-- **Exercise 23.D.6** (MWG, p. 921), equilibrium. `I = n + 1` individuals with values
independent and uniform on `[0, 1]`; waiting `w` hours costs `βw` (`β > 0`) to the first in line
only. Against others who wait `w*(s) = ns/((n + 1)β)`, waiting `w` gets the ticket with
probability `clamp((n + 1)βw/n)ⁿ` (independence), and `w*(θ)` is a best response for every
`θ ∈ [0, 1]` (this is the first-price auction with bid `βw`). -/
theorem exercise_23_D_6_bne (n : ℕ) (hn : 1 ≤ n) {β : ℝ} (hβ : 0 < β) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) :
    (θ - β * w) * clamp01 ((n + 1) * β * w / n) ^ n ≤
      (θ - β * (n * θ / ((n + 1) * β))) *
        clamp01 ((n + 1) * β * (n * θ / ((n + 1) * β)) / n) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (n + 1) * β * (n * θ / ((n + 1) * β)) / n = θ := by field_simp
  have e2 : θ - β * (n * θ / ((n + 1) * β)) = θ / (n + 1) := by field_simp; ring
  rw [e1, e2, clamp01_of_mem hθ]
  have hR : θ / (n + 1) * θ ^ n = θ ^ (n + 1) / (n + 1) := by rw [pow_succ]; ring
  rw [hR]
  set z := (n + 1) * β * w / n with hz
  have hw : β * w = n * z / (n + 1) := by rw [hz]; field_simp
  rcases le_or_gt z 0 with h | h
  · rw [clamp01_of_nonpos h, zero_pow (by omega), mul_zero]
    have := pow_nonneg hθ.1 (n + 1)
    positivity
  · rcases le_or_gt 1 z with h1 | h1
    · rw [clamp01_of_one_le h1, one_pow, mul_one, hw]
      have hb := queue_bernoulli n hθ.1 one_pos
      simp only [one_pow, mul_one] at hb
      rw [le_div_iff₀ (by positivity)]
      have : n * z / (n + 1) * (n + 1) = n * z := by field_simp
      nlinarith
    · rw [clamp01_of_mem ⟨h.le, h1.le⟩, hw]
      have hb := queue_bernoulli n hθ.1 h
      rw [le_div_iff₀ (by positivity)]
      have e3 : (θ - n * z / (n + 1)) * z ^ n * (n + 1) =
          (n + 1) * θ * z ^ n - n * z ^ (n + 1) := by
        field_simp
        ring
      linarith

/-- The expected wait of the first in line in Exercise 23.D.6: each of the `n + 1` individuals
is first in line with probability `θⁿ` given his value `θ` and then waits `w*(θ)`, so the
expected wait is `(n + 1)∫₀¹ w*(θ)θⁿ dθ`. -/
noncomputable def queueExpectedWait (n : ℕ) (β : ℝ) : ℝ :=
  (n + 1) * ∫ θ in (0 : ℝ)..1, n * θ / ((n + 1) * β) * θ ^ n

/-- **Exercise 23.D.6** (MWG, p. 921). With `I = n + 1` individuals the expected number of hours
the first in line waits is `(I - 1)/((I + 1)β) = n/((n + 2)β)`; it halves when `β` doubles and
rises when `I` doubles (`n ↦ 2n + 1`). -/
theorem exercise_23_D_6 (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    queueExpectedWait n β = n / ((n + 2) * β) ∧
      queueExpectedWait n (2 * β) = queueExpectedWait n β / 2 ∧
      (1 ≤ n → queueExpectedWait n β < queueExpectedWait (2 * n + 1) β) := by
  have key : ∀ (m : ℕ) (γ : ℝ), 0 < γ → queueExpectedWait m γ = m / ((m + 2) * γ) := by
    intro m γ hγ
    have e : (fun θ : ℝ => m * θ / ((m + 1) * γ) * θ ^ m) =
        fun θ => m / ((m + 1) * γ) * θ ^ (m + 1) := by
      funext θ; rw [pow_succ]; ring
    rw [queueExpectedWait, e, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    field_simp
    ring
  refine ⟨key n β hβ, ?_, fun hn => ?_⟩
  · rw [key n (2 * β) (by positivity), key n β hβ]
    field_simp
  · rw [key n β hβ, key (2 * n + 1) β hβ, div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Optimal selling, regulation and production-rights exercises

MWG, Exercises 23.F.2, 23.F.5, 23.F.6 and 23.F.7 (pp. 923-924).

* **Exercise 23.F.2** (Maskin-Riley): the consumer's utility `θv(x) - t` is the agent's utility
  of Example 23.F.1 with effort `x`, `g = v` and transfer `-t`; the monopolist's profit `t - cx` is
  the principal's payoff with `v(e) = -ce`. Hence (`exercise_23_F_2`): if `x*(θ)` maximises the
  virtual surplus `J(θ)v(x) - cx` over `x ≥ 0` for every type, and `(x*, t*)` is incentive
  compatible and individually rational with `U*(θ̲) = 0`, it is the optimal selling mechanism.
  At interior quantities `J(θ)v'(x*) = c` (`exercise_23_F_2_foc`); types with `J(θ) ≤ 0` are
  excluded (`exercise_23_F_2_exclusion`); `x*` is nondecreasing (`oc_maximizer_monotoneOn`).
* **Exercise 23.F.5**: (a) quantities `qᵢ` (prices `pᵢ = Pᵢ(qᵢ)`) are optimal when each `qᵢ`
  maximises `Rᵢ(q) - λq` for a common `λ ≥ 0` with complementary slackness
  (`exercise_23_F_5a`): marginal revenues are equalised (`exercise_23_F_5a_foc`); (b) with demand
  `x(p) = 1 - Φ(p)`, marginal revenue in quantity is the virtual valuation
  `J(p) = p - (1 - Φ(p))/φ(p)` of Example 23.F.2 (`exercise_23_F_5b`).
* **Exercise 23.F.6** (Baron-Myerson): (a) with profit `π = (p - θ)x(p) + t`, incentive
  compatibility iff `x(p(·))` is nonincreasing and `Π(θ) = Π(θ̲) - ∫_{θ̲}^{θ} x(p(s)) ds`
  (`exercise_23_F_6a`); `x(p(·))` nonincreasing iff `p(·)` nondecreasing (`exercise_23_F_6a_price`);
  individual rationality iff `Π(θ̄) ≥ 0` (`exercise_23_F_6a_ir`). (b) expected welfare equals
  `E[S(p) + (p - θ - (1 - α)Φ/φ)x(p)] - (1 - α)Π(θ̄)` (`exercise_23_F_6b_objective`); for
  `α < 1` the pointwise maximiser with `Π(θ̄) = 0` is optimal (`exercise_23_F_6b`), and
  `p*(θ) = θ + (1 - α)Φ(θ)/φ(θ)` (`exercise_23_F_6b_price`); for `α = 1` the objective is
  `E[S(p) + (p - θ)x(p)]` (marginal-cost pricing, transfers irrelevant) and for `α > 1` it is
  unbounded (`exercise_23_F_6b_alpha_ge_one`).
* **Exercise 23.F.7** (Dana-Spier): the Cournot outcomes with `p = 1 - x` and marginal cost `c`
  (`exercise_23_F_7_monopoly`, `exercise_23_F_7_duopoly`); the virtual welfare of a market
  structure (`dsVirtualWelfare`) with virtual cost `λθⱼ + (λ - 1)Φ(θⱼ)/φ(θⱼ)`; and its
  monotonicity: lowering a firm's virtual cost never makes excluding it better
  (`exercise_23_F_7`).

**Corrections.** Exercise 23.F.6(b) as printed maximises `∫_{p}^{∞} x + απ` with consumer surplus
gross of the transfer; then raising `t` by `c` preserves incentive compatibility and individual
rationality and raises the objective by `αc`, so for `α > 0` there is no optimum
(`exercise_23_F_6b_printed_unbounded`). We use consumer surplus net of the transfer,
`S(p) - t + απ` (as in Baron-Myerson). **Departures.** Prices are restricted to `p ≥ 0`
(MWG: `p > 0`). Exercise 23.F.7: the reduction of the planner's expected welfare to the expected
virtual welfare (the two-firm analogue of (23.F.4)) is not formalised; we prove the pointwise
characterisation and its monotonicity.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-! ## Exercise 23.F.2 -/

/-- **Exercise 23.F.2** (MWG, p. 923), Maskin-Riley. A consumer of type `θ ∈ [θ̲, θ̄]` (`θ̲ > 0`,
density `φ > 0`) gets `θv(x) - t`; the monopolist's unit cost is `c`. In the notation of
Example 23.F.1 the consumer is the agent with effort `x`, `g = v`, transfer `-t` and reservation
utility `0`, and the monopolist's profit `t - cx` is the principal's payoff with `v(e) = -ce`
(`OCFeasible` = incentive compatible, individually rational, expectations exist). If `x*(θ)`
maximises the virtual surplus `v(x)J(θ) - cx` over `x ≥ 0` for every type and `(x*, t*)` is
feasible with `U*(θ̲) = 0`, then `(x*, t*)` maximises expected profit
`E[t(θ) - cx(θ)]` among all feasible mechanisms. -/
theorem exercise_23_F_2 (D : TypeDensity) {v : ℝ → ℝ} {c : ℝ} {xs ts : ℝ → ℝ}
    (hs : OCFeasible D (fun q => -(c * q)) v 0 xs fun θ => -ts θ)
    (hU : ocU v xs (fun θ => -ts θ) D.lo = 0)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi,
      OCArgmax (fun q => -(c * q) + v q * D.virtualValue θ) (xs θ))
    {x t : ℝ → ℝ} (h : OCFeasible D (fun q => -(c * q)) v 0 x fun θ => -t θ) :
    ∫ θ, (t θ - c * x θ) ∂D.measure ≤ ∫ θ, (ts θ - c * xs θ) ∂D.measure := by
  have := example_23_F_1 D hs hU hmax h
  simp only [ocPayoff, sub_neg_eq_add] at this
  have e : ∀ (y s : ℝ → ℝ), (fun θ => -(c * y θ) + s θ) = fun θ => s θ - c * y θ :=
    fun y s => funext fun θ => by ring
  rwa [e, e] at this

/-- **Exercise 23.F.2** (MWG, p. 923): at an interior optimal quantity `x*(θ) > 0`,
`J(θ)v'(x*) = c` (marginal virtual surplus equals marginal cost). -/
theorem exercise_23_F_2_foc {v : ℝ → ℝ} {v' c J q : ℝ} (hv : HasDerivAt v v' q) (hq : 0 < q)
    (hmax : OCArgmax (fun x => -(c * x) + v x * J) q) : J * v' = c := by
  have := eq_23_F_6 ((hasDerivAt_id q).const_mul c).neg hv hq hmax
  simp only [mul_one] at this
  linarith

/-- **Exercise 23.F.2** (MWG, p. 923): with `c > 0`, `v(0) = 0` and `v ≥ 0` on `x ≥ 0`, a type
with `J(θ) ≤ 0` is excluded: `0` is the unique maximiser of `v(x)J(θ) - cx`. -/
theorem exercise_23_F_2_exclusion {v : ℝ → ℝ} {c J : ℝ} (hc : 0 < c) (hv0 : v 0 = 0)
    (hv : ∀ x, 0 ≤ x → 0 ≤ v x) (hJ : J ≤ 0) :
    OCArgmax (fun x => -(c * x) + v x * J) 0 ∧
      ∀ q, OCArgmax (fun x => -(c * x) + v x * J) q → q = 0 := by
  have key : ∀ x, 0 ≤ x → -(c * x) + v x * J ≤ -(c * x) := fun x hx => by
    nlinarith [hv x hx]
  refine ⟨⟨le_rfl, fun x hx => ?_⟩, fun q hq => ?_⟩
  · simp only [mul_zero, neg_zero, hv0, zero_mul, add_zero]
    have := key x hx
    nlinarith
  · by_contra hne
    have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hne)
    have h1 := hq.2 0 le_rfl
    have h2 := key q hq.1
    simp only [mul_zero, neg_zero, hv0, zero_mul, add_zero] at h1
    nlinarith

/-! ## Exercise 23.F.5 -/

/-- **Exercise 23.F.5(a)** (MWG, p. 923). A monopolist with one divisible unit and two buyers with
decreasing demands sells `qᵢ` to buyer `i` at the price `Pᵢ(qᵢ)` (`Pᵢ` the inverse demand), with
revenue `Rᵢ(q) = Pᵢ(q)q`. If for some `λ ≥ 0` each `qᵢ` maximises `Rᵢ(q) - λq` over `q ≥ 0` and
`λ(1 - q₁ - q₂) = 0`, then no feasible `q₁' + q₂' ≤ 1` earns more; so when also
`q₁ + q₂ ≤ 1`, the prices `Pᵢ(qᵢ)` are optimal. -/
theorem exercise_23_F_5a {R1 R2 : ℝ → ℝ} {q1 q2 lam : ℝ} (hlam : 0 ≤ lam)
    (h1 : ∀ q, 0 ≤ q → R1 q - lam * q ≤ R1 q1 - lam * q1)
    (h2 : ∀ q, 0 ≤ q → R2 q - lam * q ≤ R2 q2 - lam * q2) (hcs : lam * (1 - q1 - q2) = 0)
    {q1' q2' : ℝ} (hq1 : 0 ≤ q1') (hq2 : 0 ≤ q2') (hq' : q1' + q2' ≤ 1) :
    R1 q1' + R2 q2' ≤ R1 q1 + R2 q2 := by
  have := h1 q1' hq1
  have := h2 q2' hq2
  nlinarith

/-- **Exercise 23.F.5(a)** (MWG, p. 923): at interior quantities the marginal revenues are equal
to the shadow value `λ` of the unit. -/
theorem exercise_23_F_5a_foc {R1 R2 : ℝ → ℝ} {R1' R2' q1 q2 lam : ℝ}
    (hR1 : HasDerivAt R1 R1' q1) (hR2 : HasDerivAt R2 R2' q2) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (h1 : ∀ q, 0 ≤ q → R1 q - lam * q ≤ R1 q1 - lam * q1)
    (h2 : ∀ q, 0 ≤ q → R2 q - lam * q ≤ R2 q2 - lam * q2) : R1' = lam ∧ R2' = lam := by
  have l1 : IsLocalMax (fun q => R1 q - lam * q) q1 :=
    Filter.mem_of_superset (Ioi_mem_nhds hq1) fun q hq => h1 q (le_of_lt hq)
  have l2 : IsLocalMax (fun q => R2 q - lam * q) q2 :=
    Filter.mem_of_superset (Ioi_mem_nhds hq2) fun q hq => h2 q (le_of_lt hq)
  have d1 := l1.hasDerivAt_eq_zero (hR1.sub ((hasDerivAt_id q1).const_mul lam))
  have d2 := l2.hasDerivAt_eq_zero (hR2.sub ((hasDerivAt_id q2).const_mul lam))
  simp only [mul_one] at d1 d2
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 23.F.5(b)** (MWG, p. 923). Relation to the optimal auction of Example 23.F.2: if a
buyer's demand is `x(p) = 1 - Φ(p)` (the probability that his valuation exceeds `p`), with
`x'(p) = -φ(p) ≠ 0`, then the marginal revenue with respect to quantity,
`(d(p x(p))/dp)/(dx/dp) = (x(p) + p x'(p))/x'(p)`, is the virtual valuation
`J(p) = p - (1 - Φ(p))/φ(p)`. So the monopolist's rule "equalise marginal revenues" is the
optimal auction's rule "allocate by virtual valuations" (Bulow and Roberts). -/
theorem exercise_23_F_5b (D : TypeDensity) {p : ℝ} (hp : D.dens p ≠ 0) :
    ((1 - D.cdf p) + p * (-D.dens p)) / (-D.dens p) = D.virtualValue p := by
  simp only [TypeDensity.virtualValue]
  field_simp
  ring

/-! ## Exercise 23.F.6 -/

/-- The truthful profit `Π(θ) = (p(θ) - θ)x(p(θ)) + t(θ)` of Exercise 23.F.6. -/
def bmProfit (x p t : ℝ → ℝ) (θ : ℝ) : ℝ := (p θ - θ) * x (p θ) + t θ

/-- **Exercise 23.F.6(a)** (MWG, pp. 923-924), Proposition 23.D.2 adapted. The type-`θ` firm's
profit from announcing `θ̂` is `θ·(-x(p(θ̂))) + (p(θ̂)x(p(θ̂)) + t(θ̂))`, linear in `θ`. The scheme
`(p, t)` is incentive compatible iff `-x(p(·))` is nondecreasing and
`Π(θ) = Π(θ̲) - ∫_{θ̲}^{θ} x(p(s)) ds`. -/
theorem exercise_23_F_6a {x p t : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC (fun θ => -x (p θ)) (fun θ => p θ * x (p θ) + t θ) lo hi ↔
      MonotoneOn (fun θ => -x (p θ)) (Set.Icc lo hi) ∧
        ∀ θ ∈ Set.Icc lo hi, bmProfit x p t θ = bmProfit x p t lo - ∫ s in lo..θ, x (p s) := by
  rw [linearIC_iff]
  simp only [bmProfit, intervalIntegral.integral_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun θ hθ => ?_⟩ <;> have := h2 θ hθ <;>
    linarith

/-- **Exercise 23.F.6(a)**: with `x` strictly decreasing on prices `p ≥ 0`, `x(p(·))` is
nonincreasing iff the price `p(·)` is nondecreasing in the cost. -/
theorem exercise_23_F_6a_price {x p : ℝ → ℝ} {S : Set ℝ} (hx : StrictAntiOn x (Set.Ici 0))
    (hp : ∀ θ, 0 ≤ p θ) : MonotoneOn (fun θ => -x (p θ)) S ↔ MonotoneOn p S := by
  have hg : StrictMonoOn (fun q => -x q) (Set.Ici 0) := fun a ha b hb hab =>
    neg_lt_neg (hx ha hb hab)
  exact oc_monotone_comp_iff hg hp

/-- **Exercise 23.F.6(a)**: given the profit formula and `x ≥ 0`, the firm is guaranteed a
nonnegative profit at every cost iff `Π(θ̄) ≥ 0`. -/
theorem exercise_23_F_6a_ir {x p t : ℝ → ℝ} {lo hi : ℝ} (hle : lo ≤ hi)
    (hx0 : ∀ θ, 0 ≤ x (p θ)) (hint : IntervalIntegrable (fun s => x (p s)) volume lo hi)
    (hii : ∀ θ ∈ Set.Icc lo hi, bmProfit x p t θ = bmProfit x p t lo - ∫ s in lo..θ, x (p s)) :
    (∀ θ ∈ Set.Icc lo hi, 0 ≤ bmProfit x p t θ) ↔ 0 ≤ bmProfit x p t hi := by
  refine ⟨fun h => h hi ⟨hle, le_rfl⟩, fun h θ hθ => ?_⟩
  have hmono : ∫ s in lo..θ, x (p s) ≤ ∫ s in lo..hi, x (p s) :=
    intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
      (Filter.Eventually.of_forall fun s => hx0 s) hint
  rw [hii θ hθ]
  rw [hii hi ⟨hle, le_rfl⟩] at h
  linarith

/-- The regulator's weighted welfare at cost `θ` for Exercise 23.F.6(b), with consumer surplus net
of the transfer: `S(p(θ)) - t(θ) + απ(p(θ), t(θ), θ)`, where `S(p) = ∫_p^∞ x(s) ds`. -/
def bmWelfare (S x p t : ℝ → ℝ) (α θ : ℝ) : ℝ := S (p θ) - t θ + α * bmProfit x p t θ

/-- The virtual welfare of price `q` at cost `θ`:
`S(q) + (q - θ - (1 - α)Φ(θ)/φ(θ))x(q)`. -/
noncomputable def bmVirtual (D : TypeDensity) (S x : ℝ → ℝ) (α θ q : ℝ) : ℝ :=
  S q + (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x q

/-- A feasible regulatory scheme for Exercise 23.F.6: incentive compatible, individually rational
(`Π(θ) ≥ 0`), with the expectations involved existing. -/
def BMFeasible (D : TypeDensity) (S x p t : ℝ → ℝ) : Prop :=
  LinearIC (fun θ => -x (p θ)) (fun θ => p θ * x (p θ) + t θ) D.lo D.hi ∧
    (∀ θ ∈ Set.Icc D.lo D.hi, 0 ≤ bmProfit x p t θ) ∧
    Integrable (fun θ => S (p θ)) D.measure ∧
    Integrable (fun θ => (p θ - θ) * x (p θ)) D.measure ∧ Integrable t D.measure ∧
    Integrable (fun θ => x (p θ) * (D.cdf θ / D.dens θ)) D.measure

/-- **Exercise 23.F.6(b)** (MWG, p. 924). For a feasible scheme the expected weighted welfare is
`E[S(p) + (p - θ - (1 - α)Φ/φ)x(p)] - (1 - α)Π(θ̄)` (the analogue of (23.F.4), by the Fubini form
of the integration by parts). -/
theorem exercise_23_F_6b_objective (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) :
    ∫ θ, bmWelfare S x p t α θ ∂D.measure =
      ∫ θ, bmVirtual D S x α θ (p θ) ∂D.measure - (1 - α) * bmProfit x p t D.hi := by
  have := D.isProbabilityMeasure
  obtain ⟨hIC, -, hS, hpx, ht, hr⟩ := hf
  obtain ⟨hmono, hii⟩ := exercise_23_F_6a.1 hIC
  have hle : D.lo ≤ D.hi := D.lo_lt_hi.le
  have hw : IntervalIntegrable (fun s => x (p s)) volume D.lo D.hi := by
    have h1 : IntervalIntegrable (fun s => -x (p s)) volume D.lo D.hi := by
      apply MonotoneOn.intervalIntegrable; rw [Set.uIcc_of_le hle]; exact hmono
    convert h1.neg using 1
    funext s; simp
  have hProf : Integrable (bmProfit x p t) D.measure := hpx.add ht
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have hP : (fun θ => bmProfit x p t D.lo - bmProfit x p t θ) =ᵐ[D.measure]
      fun θ => ∫ s in D.lo..θ, x (p s) := by
    filter_upwards [hae] with θ hθ
    rw [hii θ hθ]; ring
  have hPint : Integrable (fun θ => ∫ s in D.lo..θ, x (p s)) D.measure :=
    ((integrable_const _).sub hProf).congr hP
  have hEP : ∫ θ, (∫ s in D.lo..θ, x (p s)) ∂D.measure =
      ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) := by
    rw [td_integral_integral_eq D.measure hle D.measure_compl_Icc hw]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    simp only [D.measureReal_Ici hs]
  have hEProf : ∫ θ, bmProfit x p t θ ∂D.measure =
      bmProfit x p t D.lo - ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) := by
    rw [← hEP]
    have e1 : ∫ θ, bmProfit x p t θ ∂D.measure =
        ∫ θ, (bmProfit x p t D.lo - ∫ s in D.lo..θ, x (p s)) ∂D.measure := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with θ hθ
      rw [hii θ hθ]
    rw [e1, integral_sub (integrable_const _) hPint, integral_const, probReal_univ, one_smul]
  have hhi := hii D.hi ⟨hle, le_rfl⟩
  have hcdf : IntervalIntegrable (fun s => x (p s) * D.cdf s) volume D.lo D.hi :=
    hw.mul_continuousOn D.continuous_cdf.continuousOn
  have hsplit : ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) =
      (∫ s in D.lo..D.hi, x (p s)) - ∫ s in D.lo..D.hi, x (p s) * D.cdf s := by
    rw [← intervalIntegral.integral_sub hw hcdf]
    congr 1; funext s; ring
  have hr' : ∫ θ, x (p θ) * (D.cdf θ / D.dens θ) ∂D.measure =
      ∫ s in D.lo..D.hi, x (p s) * D.cdf s := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    have := (D.dens_pos s hs).ne'
    field_simp
  have eW : ∫ θ, bmWelfare S x p t α θ ∂D.measure = ∫ θ, S (p θ) ∂D.measure +
      ∫ θ, (p θ - θ) * x (p θ) ∂D.measure - (1 - α) * ∫ θ, bmProfit x p t θ ∂D.measure := by
    have e : (fun θ => bmWelfare S x p t α θ) = fun θ =>
        (S (p θ) + (p θ - θ) * x (p θ)) - (1 - α) * bmProfit x p t θ := by
      funext θ; simp only [bmWelfare, bmProfit]; ring
    have i1 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ) - (1 - α) * bmProfit x p t θ) ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure -
          ∫ θ, (1 - α) * bmProfit x p t θ ∂D.measure :=
      integral_sub (hS.add hpx) (hProf.const_mul _)
    have i2 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure =
        ∫ θ, S (p θ) ∂D.measure + ∫ θ, (p θ - θ) * x (p θ) ∂D.measure := integral_add hS hpx
    rw [e, i1, i2, integral_const_mul]
  have eV : ∫ θ, bmVirtual D S x α θ (p θ) ∂D.measure = ∫ θ, S (p θ) ∂D.measure +
      ∫ θ, (p θ - θ) * x (p θ) ∂D.measure -
        (1 - α) * ∫ θ, x (p θ) * (D.cdf θ / D.dens θ) ∂D.measure := by
    have e : (fun θ => bmVirtual D S x α θ (p θ)) = fun θ =>
        (S (p θ) + (p θ - θ) * x (p θ)) - (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ)) := by
      funext θ; simp only [bmVirtual]; ring
    have i1 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ) -
        (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ))) ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure -
          ∫ θ, (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ)) ∂D.measure :=
      integral_sub (hS.add hpx) (hr.const_mul _)
    have i2 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure =
        ∫ θ, S (p θ) ∂D.measure + ∫ θ, (p θ - θ) * x (p θ) ∂D.measure := integral_add hS hpx
    rw [e, i1, i2, integral_const_mul]
  rw [eW, eV, hEProf, hsplit, hr']
  rw [hhi]
  ring

/-- **Exercise 23.F.6(b)** (MWG, p. 924), `α < 1`. If `p*(θ) ≥ 0` maximises the virtual welfare
`S(q) + (q - θ - (1 - α)Φ(θ)/φ(θ))x(q)` over prices `q ≥ 0` for every cost, and `(p*, t*)` is
feasible with `Π*(θ̄) = 0`, then it maximises expected welfare among all feasible schemes with
nonnegative prices. -/
theorem exercise_23_F_6b (D : TypeDensity) {S x : ℝ → ℝ} {α : ℝ} (hα : α < 1)
    {ps ts : ℝ → ℝ} (hs : BMFeasible D S x ps ts) (hProf : bmProfit x ps ts D.hi = 0)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, ∀ q, 0 ≤ q →
      bmVirtual D S x α θ q ≤ bmVirtual D S x α θ (ps θ))
    {p t : ℝ → ℝ} (h : BMFeasible D S x p t) (hp : ∀ θ, 0 ≤ p θ) :
    ∫ θ, bmWelfare S x p t α θ ∂D.measure ≤ ∫ θ, bmWelfare S x ps ts α θ ∂D.measure := by
  rw [exercise_23_F_6b_objective D h, exercise_23_F_6b_objective D hs, hProf]
  have hIR := h.2.1 D.hi ⟨D.lo_lt_hi.le, le_rfl⟩
  have hV : ∀ {p t : ℝ → ℝ}, BMFeasible D S x p t →
      Integrable (fun θ => bmVirtual D S x α θ (p θ)) D.measure := by
    intro p t hf
    obtain ⟨-, -, hS, hpx, -, hr⟩ := hf
    refine ((hS.add hpx).sub (hr.const_mul (1 - α))).congr
      (Filter.Eventually.of_forall fun θ => ?_)
    simp only [bmVirtual, Pi.add_apply, Pi.sub_apply]
    ring
  have hle := integral_mono_ae (hV h) (hV hs) (by
    filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with θ hθ
    exact hmax θ hθ (p θ) (hp θ))
  have : 0 ≤ (1 - α) * bmProfit x p t D.hi := mul_nonneg (by linarith) hIR
  linarith

/-- **Exercise 23.F.6(b)** (MWG, p. 924), the optimal price: if `S' = -x`, `x` is differentiable
with `x'(q) ≠ 0`, and `q` is a local maximiser of the virtual welfare at cost `θ`, then
`q = θ + (1 - α)Φ(θ)/φ(θ)`: the price exceeds marginal cost by `(1 - α)Φ/φ` (nondecreasing in
`θ` when `Φ/φ` is). -/
theorem exercise_23_F_6b_price (D : TypeDensity) {S x : ℝ → ℝ} {α θ q x' : ℝ}
    (hS : HasDerivAt S (-x q) q) (hx : HasDerivAt x x' q) (hx' : x' ≠ 0)
    (hloc : IsLocalMax (bmVirtual D S x α θ) q) :
    q = θ + (1 - α) * (D.cdf θ / D.dens θ) := by
  have hd : HasDerivAt (bmVirtual D S x α θ)
      (-x q + (1 * x q + (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x')) q :=
    hS.add ((((hasDerivAt_id' q).sub_const θ).sub_const _).fun_mul hx)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have h1 : (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x' = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h | h
  · linarith
  · exact absurd h hx'

/-- **Exercise 23.F.6(b)** (MWG, p. 924), "What if `α ≥ 1`?". Raising every transfer by `c ≥ 0`
keeps the scheme feasible and changes expected welfare by `(α - 1)c`: for `α > 1` the objective
is unbounded (no optimal scheme), and for `α = 1` expected welfare is
`E[S(p) + (p - θ)x(p)]`, independent of transfers, maximised by marginal-cost pricing. -/
theorem exercise_23_F_6b_alpha_ge_one (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) {c : ℝ} (hc : 0 ≤ c) :
    BMFeasible D S x p (fun θ => t θ + c) ∧
      ∫ θ, bmWelfare S x p (fun θ => t θ + c) α θ ∂D.measure =
        ∫ θ, bmWelfare S x p t α θ ∂D.measure + (α - 1) * c ∧
      (α = 1 → ∫ θ, bmWelfare S x p t α θ ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure) := by
  have := D.isProbabilityMeasure
  obtain ⟨hIC, hIR, hS, hpx, ht, hr⟩ := hf
  have hf' : BMFeasible D S x p (fun θ => t θ + c) := by
    refine ⟨fun θ hθ θh hθh => ?_, fun θ hθ => ?_, hS, hpx, ht.add (integrable_const c), hr⟩
    · have := hIC θ hθ θh hθh; simp only at this ⊢; linarith
    · have := hIR θ hθ; simp only [bmProfit] at this ⊢; linarith
  refine ⟨hf', ?_, fun hα => ?_⟩
  · have hW : Integrable (fun θ => bmWelfare S x p t α θ) D.measure := by
      refine ((hS.sub ht).add ((hpx.add ht).const_mul α)).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      simp only [bmWelfare, bmProfit, Pi.add_apply, Pi.sub_apply]
    have e : (fun θ => bmWelfare S x p (fun θ => t θ + c) α θ) =
        fun θ => bmWelfare S x p t α θ + (α - 1) * c := by
      funext θ; simp only [bmWelfare, bmProfit]; ring
    rw [e, integral_add hW (integrable_const _), integral_const, probReal_univ, one_smul]
  · have h := exercise_23_F_6b_objective (α := α) D ⟨hIC, hIR, hS, hpx, ht, hr⟩
    rw [hα] at h ⊢
    rw [h]
    simp only [sub_self, zero_mul, sub_zero, bmVirtual]

/-- **Exercise 23.F.6(b)**, correction (MWG, p. 924): with the printed objective
`∫_{p(θ)}^{∞} x + απ` (consumer surplus gross of the transfer), raising every transfer by `c`
keeps the scheme feasible (`exercise_23_F_6b_alpha_ge_one`) and raises the objective by `αc`, so
for `α > 0` no optimal scheme exists. -/
theorem exercise_23_F_6b_printed_unbounded (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) (c : ℝ) :
    ∫ θ, (S (p θ) + α * bmProfit x p (fun θ => t θ + c) θ) ∂D.measure =
      ∫ θ, (S (p θ) + α * bmProfit x p t θ) ∂D.measure + α * c := by
  have := D.isProbabilityMeasure
  obtain ⟨-, -, hS, hpx, ht, -⟩ := hf
  have hI : Integrable (fun θ => S (p θ) + α * bmProfit x p t θ) D.measure :=
    hS.add ((hpx.add ht).const_mul α)
  have e : (fun θ => S (p θ) + α * bmProfit x p (fun θ => t θ + c) θ) =
      fun θ => (S (p θ) + α * bmProfit x p t θ) + α * c := by
    funext θ; simp only [bmProfit]; ring
  rw [e, integral_add hI (integrable_const _), integral_const, probReal_univ, one_smul]

/-- Non-vacuity of `BMFeasible`: costs uniform on `[0, 1]`, unit demand `x = 1`, `S = 0`,
marginal-cost prices `p(θ) = θ` and transfers `t(θ) = 1 - θ` (so `Π(θ) = 1 - θ`, `Π(θ̄) = 0`). -/
theorem bmFeasible_instance :
    BMFeasible uniform01 (fun _ => 0) (fun _ => 1) (fun θ => θ) (fun θ => 1 - θ) ∧
      bmProfit (fun _ => 1) (fun θ => θ) (fun θ => 1 - θ) uniform01.hi = 0 := by
  have := uniform01.isProbabilityMeasure
  have hb : ∀ {f : ℝ → ℝ}, Measurable f → (∀ θ ∈ Set.Icc (0 : ℝ) 1, |f θ| ≤ 1) →
      Integrable f uniform01.measure := fun hf hC => oc_integrable_of_bound uniform01 hf 1 hC
  refine ⟨⟨fun θ _ θh _ => ?_, fun θ hθ => ?_, integrable_const _, ?_, ?_, ?_⟩, ?_⟩
  · simp only; linarith
  · simp only [bmProfit]; change θ ∈ Set.Icc (0 : ℝ) 1 at hθ; linarith [hθ.2]
  · simp only [sub_self, zero_mul]; exact integrable_const _
  · exact hb (by fun_prop) fun θ hθ => by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · refine hb ((uniform01.continuous_cdf.measurable.div uniform01.measurable_dens).const_mul 1)
      fun θ hθ => ?_
    have hd : uniform01.dens θ = 1 := by
      change (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) θ = 1
      rw [Set.indicator_of_mem hθ]; norm_num
    rw [hd, uniform01_cdf hθ, div_one, one_mul, abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  · simp [bmProfit, uniform01, uniformDensity]

/-! ## Exercise 23.F.7 -/

/-- **Exercise 23.F.7** (MWG, p. 924), the unregulated monopoly: with inverse demand
`p = 1 - x` and marginal cost `c`, output `(1 - c)/2` maximises the gross profit
`(1 - q - c)q`, which is then `(1 - c)²/4`; consumer surplus is `((1 - c)/2)²/2 = (1 - c)²/8`. -/
theorem exercise_23_F_7_monopoly (c : ℝ) :
    (∀ q, (1 - q - c) * q ≤ (1 - (1 - c) / 2 - c) * ((1 - c) / 2)) ∧
      (1 - (1 - c) / 2 - c) * ((1 - c) / 2) = (1 - c) ^ 2 / 4 ∧
      ((1 - c) / 2) ^ 2 / 2 = (1 - c) ^ 2 / 8 := by
  refine ⟨fun q => ?_, by ring, by ring⟩
  nlinarith [sq_nonneg (q - (1 - c) / 2)]

/-- **Exercise 23.F.7** (MWG, p. 924), the Cournot duopoly: each firm producing `(1 - c)/3` is a
Nash equilibrium (each output is a best response to the other), each gross profit is
`(1 - c)²/9` and consumer surplus is `(2(1 - c)/3)²/2 = 2(1 - c)²/9`. -/
theorem exercise_23_F_7_duopoly (c : ℝ) :
    (∀ q, (1 - q - (1 - c) / 3 - c) * q ≤
      (1 - (1 - c) / 3 - (1 - c) / 3 - c) * ((1 - c) / 3)) ∧
      (1 - (1 - c) / 3 - (1 - c) / 3 - c) * ((1 - c) / 3) = (1 - c) ^ 2 / 9 ∧
      (2 * (1 - c) / 3) ^ 2 / 2 = 2 * (1 - c) ^ 2 / 9 := by
  refine ⟨fun q => ?_, by ring, by ring⟩
  nlinarith [sq_nonneg (q - (1 - c) / 3)]

/-- Whether firm `j` (`false` = firm 1, `true` = firm 2) is awarded production rights in the
market structure `y`. -/
def dsProduces (y : Bool × Bool) (j : Bool) : Bool := if j then y.2 else y.1

/-- The Cournot gross profit of firm `j` in market structure `y` (Exercise 23.F.7). -/
noncomputable def dsGross (c : ℝ) (y : Bool × Bool) (j : Bool) : ℝ :=
  if dsProduces y j then (if y.1 && y.2 then (1 - c) ^ 2 / 9 else (1 - c) ^ 2 / 4) else 0

/-- Consumer surplus in market structure `y` (Exercise 23.F.7). -/
noncomputable def dsSurplus (c : ℝ) (y : Bool × Bool) : ℝ :=
  if y.1 && y.2 then 2 * (1 - c) ^ 2 / 9 else if y.1 || y.2 then (1 - c) ^ 2 / 8 else 0

/-- A firm's virtual cost in Exercise 23.F.7, `λθ + (λ - 1)Φ(θ)/φ(θ)`: the expected welfare cost
of letting a firm with fixed cost `θ` produce when transfers carry shadow cost `λ > 1`. -/
noncomputable def dsVirtualCost (D : TypeDensity) (lam θ : ℝ) : ℝ :=
  lam * θ + (lam - 1) * (D.cdf θ / D.dens θ)

/-- The planner's virtual welfare of market structure `y` given the firms' virtual costs `vc`:
`S(y) + ∑_{j producing} (λπⱼ(y) - vcⱼ)`. -/
noncomputable def dsVirtualWelfare (c lam : ℝ) (vc : Bool → ℝ) (y : Bool × Bool) : ℝ :=
  dsSurplus c y + (if dsProduces y false then lam * dsGross c y false - vc false else 0) +
    (if dsProduces y true then lam * dsGross c y true - vc true else 0)

/-- **Exercise 23.F.7** (MWG, p. 924): with `λ > 1` and `Φ/φ` increasing the virtual cost is
strictly increasing in the fixed cost. -/
theorem dsVirtualCost_strictMono (D : TypeDensity) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : MonotoneOn (fun θ => D.cdf θ / D.dens θ) (Set.Icc D.lo D.hi)) :
    StrictMonoOn (dsVirtualCost D lam) (Set.Icc D.lo D.hi) := by
  intro a ha b hb hab
  have := hΦ ha hb hab.le
  simp only [dsVirtualCost] at this ⊢
  nlinarith

/-- **Exercise 23.F.7** (MWG, p. 924), the characterisation of the optimal auction of production
rights at each profile: the market structure maximises the virtual welfare
`S(y) + ∑_{j producing}(λπⱼ(y) - λθⱼ - (λ - 1)Φ(θⱼ)/φ(θⱼ))` (`dsVirtualWelfare`), and this rule
satisfies the monotonicity required by incentive compatibility: if `y*` is optimal at virtual
costs `vc` and awards rights to firm `j`, then after lowering `j`'s virtual cost (the other
firm's unchanged) no structure excluding `j` does better than `y*`. -/
theorem exercise_23_F_7 (c lam : ℝ) {vc vc' : Bool → ℝ} {j : Bool} (hj : vc' j ≤ vc j)
    (hother : vc' (!j) = vc (!j)) {ys : Bool × Bool}
    (hopt : ∀ y, dsVirtualWelfare c lam vc y ≤ dsVirtualWelfare c lam vc ys)
    (hys : dsProduces ys j = true) {y : Bool × Bool} (hy : dsProduces y j = false) :
    dsVirtualWelfare c lam vc' y ≤ dsVirtualWelfare c lam vc' ys := by
  have h := hopt y
  cases j <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
    simp only [dsVirtualWelfare, hys, hy, ite_true, hother] at h ⊢ <;>
    split_ifs at h ⊢ <;> linarith

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# MWG's own proof of the Myerson-Satterthwaite theorem

MWG, Section 23.E, pp. 895-896 (proof of Proposition 23.E.1), and Exercise 23.E.6(b) (p. 922).

Agent `0` is the seller (MWG's agent 1) and agent `1` the buyer (MWG's agent 2); types are
independent with densities `φᵢ > 0` on `[θ̲ᵢ, θ̄ᵢ]` (`TypeDensity`), `Jᵢ(θ) = θ - (1 - Φᵢ)/φᵢ`
(`TypeDensity.virtualValue`) and `Kᵢ(θ) = θ + Φᵢ/φᵢ` (`TypeDensity.virtualCost`).

* **Step 1**, every display: (23.E.5) `eq_23_E_5`; `U₁(θ̲₁) = U₁(θ̄₁) - ∫∫ y₁φ₂`
  (`eq_23_E_5_seller_U`, with `ȳ₁(θ₁) = ∫ y₁(θ₁, ·)φ₂` in `mss_interimBenefit_seller`); (23.E.6)
  `eq_23_E_6` (from the general `mss_payment_from_top`); `∫∫ (θ₁ + Φ₁/φ₁)φ₁φ₂ = ∫ (θ₁φ₁ + Φ₁)
  = [θ₁Φ₁] = θ̄₁` (`mss_integral_virtualCost`, `mss_expect_virtualCost`); (23.E.7) `eq_23_E_7`;
  `E[-t₁] + E[-t₂] = 0` and `[U₁(θ̄₁) - θ̄₁] + U₂(θ̲₂) = ∫∫ y₂[J₂ - K₁]φ₁φ₂` (`eq_23_E_sum`);
  (23.E.4) `eq_23_E_4`, with a non-vacuity instance (`eq_23_E_4_instance`, posted price `1/2`).
* **Step 2**, every display: the left side of (23.E.4) as MWG's iterated integral with inner
  limit `Min{θ₂, θ̄₁}` (`mss_step2_display1`, via `mss_step2_inner`); the bracket evaluation
  (`mss_step2_display23`); the split at `θ̄₁` (`mss_step2_display4`); the vanishing of
  `[(θ₂ - θ̄₁)(Φ₂ - 1)]_{θ̄₁}^{θ̄₂}` (`mss_step2_display5`); `-∫_{θ̲₂}^{θ̄₁}[1 - Φ₂]Φ₁ < 0`
  (`mss_step2_neg`); together `mss_step2`.
* **Proposition 23.E.1** by MWG's route (`proposition_23_E_1_mwg`), with the hypotheses of
  `proposition_23_E_1`.
* **Exercise 23.E.6(b)**, uniqueness: among linear strategies `aθ + d` with `a > 0` the only
  symmetric Bayesian Nash equilibrium is `2θ/3` (`exercise_23_E_6b_unique`).

**Checks against the printed proof.** Every display of pp. 895-896 is correct as printed,
reading `φᵢ = 0` outside `[θ̲ᵢ, θ̄ᵢ]` and `Φᵢ = 0` below, `= 1` above (our `TypeDensity`
convention): this is needed when `θ₂ < θ̲₁` (the inner interval `[θ̲₁, Min{θ₂, θ̄₁}]` is reversed;
the inner integral is `0`) and when `θ̄₁ > θ̄₂` (the second integral of the fourth display runs
over a reversed interval, where its integrand vanishes). **Departures.** MWG evaluate
`∫(θφ + Φ) = [θΦ]` and `∫[(θ₂ - θ̄₁)φ₂ + Φ₂ - 1] = [(θ₂ - θ̄₁)(Φ₂ - 1)]` by the
fundamental theorem of calculus, which needs `Φ' = φ`, i.e. `φ` continuous; we prove both
identities for measurable densities by Fubini (`mss_integral_cdf`, `mss_integral_key`). In
Step 1 the expectations `E[y₂J₂]`, `E[y₂K₁]` are assumed to exist (they do for bounded
measurable `y`: `mss_integrable_y_mul`); `y₁ + y₂ = 1` and `t₁ + t₂ = 0` are needed on `Θ` only. In
Exercise 23.E.6(b) uniqueness is proved among strictly increasing linear strategies; for
constant strategies ties have positive probability and the tie rule of the mechanism matters.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-! ### The distribution function outside and inside `[θ̲, θ̄]` -/

/-- MWG's seller term `θ + Φ(θ)/φ(θ)` of (23.E.4) (MWG, p. 895), a "virtual cost". -/
noncomputable def TypeDensity.virtualCost (D : TypeDensity) (x : ℝ) : ℝ :=
  x + D.cdf x / D.dens x

/-- The density vanishes on the open interval `(a, θ̲)` below the support. -/
theorem mss_integral_below (D : TypeDensity) {a : ℝ} (ha : a ≤ D.lo) (g : ℝ → ℝ)
    (hg : ∀ x, x < D.lo → g x = 0) : ∫ x in a..D.lo, g x = 0 := by
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun x hx => hg x hx.2]
  simp

/-- The density vanishes on the open interval `(θ̄, a)` above the support. -/
theorem mss_integral_above (D : TypeDensity) {a : ℝ} (ha : D.hi ≤ a) (g : ℝ → ℝ)
    (hg : ∀ x, D.hi < x → g x = 0) : ∫ x in D.hi..a, g x = 0 := by
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun x hx => hg x hx.1]
  simp

/-- `Φ(x) = 0` for `x ≤ θ̲`. -/
theorem mss_cdf_of_le (D : TypeDensity) {x : ℝ} (hx : x ≤ D.lo) : D.cdf x = 0 := by
  rw [TypeDensity.cdf, intervalIntegral.integral_symm,
    mss_integral_below D hx _ fun s hs => D.dens_eq_zero s fun h => absurd h.1 (not_le.2 hs),
    neg_zero]

/-- `Φ(x) = 1` for `x ≥ θ̄`. -/
theorem mss_cdf_of_ge (D : TypeDensity) {x : ℝ} (hx : D.hi ≤ x) : D.cdf x = 1 := by
  rw [TypeDensity.cdf, ← intervalIntegral.integral_add_adjacent_intervals
    D.integrable_dens.intervalIntegrable D.integrable_dens.intervalIntegrable, D.integral_dens,
    mss_integral_above D hx _ fun s hs => D.dens_eq_zero s fun h => absurd h.2 (not_le.2 hs),
    add_zero]

/-- `Φ(θ̲) = 0`. -/
theorem mss_cdf_lo (D : TypeDensity) : D.cdf D.lo = 0 := mss_cdf_of_le D le_rfl

/-- `Φ(θ̄) = 1`. -/
theorem mss_cdf_hi (D : TypeDensity) : D.cdf D.hi = 1 := mss_cdf_of_ge D le_rfl

/-- `Φ(x) > 0` for `x > θ̲`. -/
theorem mss_cdf_pos (D : TypeDensity) {x : ℝ} (hx : D.lo < x) : 0 < D.cdf x := by
  rcases le_or_gt x D.hi with h | h
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on D.integrable_dens.intervalIntegrable
      (fun s hs => D.dens_pos s ⟨hs.1.le, hs.2.le.trans h⟩) hx
  · rw [mss_cdf_of_ge D h.le]; exact one_pos

/-- `1 - Φ(x) > 0` for `x < θ̄`. -/
theorem mss_one_sub_cdf_pos (D : TypeDensity) {x : ℝ} (hx : x < D.hi) : 0 < 1 - D.cdf x := by
  rcases le_or_gt D.lo x with h | h
  · exact oc_one_sub_cdf_pos D ⟨h, hx.le⟩ hx
  · rw [mss_cdf_of_le D h.le]; exact by norm_num

/-- `0 ≤ Φ(x) ≤ 1` for every `x`. -/
theorem mss_cdf_mem (D : TypeDensity) (x : ℝ) : 0 ≤ D.cdf x ∧ D.cdf x ≤ 1 := by
  rcases le_or_gt x D.lo with h | h
  · rw [mss_cdf_of_le D h]; norm_num
  rcases le_or_gt D.hi x with h' | h'
  · rw [mss_cdf_of_ge D h']; norm_num
  exact ⟨(mss_cdf_pos D h).le, by linarith [mss_one_sub_cdf_pos D h']⟩

/-- `x ↦ g(x)φ(x)` is integrable on every interval when `g` is continuous. -/
theorem mss_ii_mul_dens (D : TypeDensity) {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * D.dens x) volume a b :=
  D.integrable_dens.intervalIntegrable.continuousOn_mul hg.continuousOn

/-- `Φ` is integrable on every interval. -/
theorem mss_ii_cdf (D : TypeDensity) (a b : ℝ) : IntervalIntegrable D.cdf volume a b :=
  D.continuous_cdf.intervalIntegrable a b

/-- The Fubini identity behind MWG's integrations by parts on pp. 895-896: for `θ̲ < a`,
`∫_{θ̲}^{a} Φ(x) dx = ∫_{θ̲}^{a} (a - s)φ(s) ds`. -/
theorem mss_integral_cdf (D : TypeDensity) {a : ℝ} (ha : D.lo < a) :
    ∫ x in D.lo..a, D.cdf x = ∫ s in D.lo..a, (a - s) * D.dens s := by
  set U := uniformDensity D.lo a ha with hU
  have := U.isProbabilityMeasure
  have hw : IntervalIntegrable D.dens volume D.lo a := D.integrable_dens.intervalIntegrable
  have h := td_integral_integral_eq U.measure ha.le U.measure_compl_Icc hw
  have hUlo : U.lo = D.lo := rfl
  have hUhi : U.hi = a := rfl
  have hne : a - D.lo ≠ 0 := (sub_pos.2 ha).ne'
  rw [U.integral_eq, hUlo, hUhi] at h
  have hL : ∫ x in D.lo..a, (∫ s in D.lo..x, D.dens s) * U.dens x =
      (a - D.lo)⁻¹ * ∫ x in D.lo..a, D.cdf x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ha.le] at hx
    change (∫ s in D.lo..x, D.dens s) * (Set.Icc D.lo a).indicator (fun _ => (a - D.lo)⁻¹) x = _
    rw [Set.indicator_of_mem hx, TypeDensity.cdf]
    ring
  have hR : ∫ s in D.lo..a, D.dens s * U.measure.real (Set.Ici s) =
      (a - D.lo)⁻¹ * ∫ s in D.lo..a, (a - s) * D.dens s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ha.le] at hx
    rw [U.measureReal_Ici hx, hU, oa_uniform_cdf ha hx]
    field_simp
    ring
  rw [hL, hR] at h
  have := mul_left_cancel₀ (inv_ne_zero hne) h
  exact this

/-- The key computation in Step 2 of MWG's proof (p. 896), for every upper limit `a` and
constant `c`: `∫_{θ̲}^{a} ((c - x)φ(x) - Φ(x)) dx = (c - a)Φ(a)`, i.e.
`[(c - x)Φ(x)]_{θ̲}^{a}` (MWG's integration by parts, valid also for `a` outside `[θ̲, θ̄]`
with `φ = 0` there). -/
theorem mss_integral_key (D : TypeDensity) (a c : ℝ) :
    ∫ x in D.lo..a, ((c - x) * D.dens x - D.cdf x) = (c - a) * D.cdf a := by
  rcases le_or_gt a D.lo with ha | ha
  · rw [mss_cdf_of_le D ha, mul_zero, intervalIntegral.integral_symm,
      mss_integral_below D ha _ fun x hx => by
        rw [D.dens_eq_zero x fun h => absurd h.1 (not_le.2 hx), mss_cdf_of_le D hx.le]; ring,
      neg_zero]
  have h1 : IntervalIntegrable (fun x => (c - x) * D.dens x) volume D.lo a :=
    mss_ii_mul_dens D (continuous_const.sub continuous_id) _ _
  have h2 : IntervalIntegrable (fun x => (a - x) * D.dens x) volume D.lo a :=
    mss_ii_mul_dens D (continuous_const.sub continuous_id) _ _
  rw [intervalIntegral.integral_sub h1 (mss_ii_cdf D _ _), mss_integral_cdf D ha,
    ← intervalIntegral.integral_sub h1 h2]
  have e : ∀ x, (c - x) * D.dens x - (a - x) * D.dens x = (c - a) * D.dens x := fun x => by ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, TypeDensity.cdf]

/-! ### `θ - (1 - Φ)/φ` and `θ + Φ/φ` -/

/-- On `[θ̲, θ̄]`, `J(x)φ(x) = xφ(x) - (1 - Φ(x))` for `J(x) = x - (1 - Φ(x))/φ(x)`. -/
theorem mss_virtualValue_mul (D : TypeDensity) {x : ℝ} (hx : x ∈ Set.Icc D.lo D.hi) :
    D.virtualValue x * D.dens x = x * D.dens x - (1 - D.cdf x) := by
  have := (D.dens_pos x hx).ne'
  simp only [TypeDensity.virtualValue]
  field_simp

/-- On `[θ̲, θ̄]`, `K(x)φ(x) = xφ(x) + Φ(x)` for `K(x) = x + Φ(x)/φ(x)`. -/
theorem mss_virtualCost_mul (D : TypeDensity) {x : ℝ} (hx : x ∈ Set.Icc D.lo D.hi) :
    D.virtualCost x * D.dens x = x * D.dens x + D.cdf x := by
  have := (D.dens_pos x hx).ne'
  simp only [TypeDensity.virtualCost]
  field_simp

/-- `J` is measurable. -/
theorem mss_measurable_virtualValue (D : TypeDensity) : Measurable D.virtualValue :=
  measurable_id.sub (((continuous_const.sub D.continuous_cdf).measurable).div D.measurable_dens)

/-- `K` is measurable. -/
theorem mss_measurable_virtualCost (D : TypeDensity) : Measurable D.virtualCost :=
  measurable_id.add (D.continuous_cdf.measurable.div D.measurable_dens)

/-- A function `g` with `g φ = h` on `[θ̲, θ̄]` and `h` integrable on `[θ̲, θ̄]` is integrable
for the type distribution (even if `g` itself is unbounded, as `Φ/φ` may be). -/
theorem mss_integrable_of_mul_dens (D : TypeDensity) {g h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume D.lo D.hi)
    (e : ∀ x ∈ Set.Icc D.lo D.hi, g x * D.dens x = h x) : Integrable g D.measure := by
  rw [TypeDensity.measure, integrable_withDensity_iff_integrable_smul
    D.measurable_dens.real_toNNReal]
  have heq : (fun x => (D.dens x).toNNReal • g x) = (Set.Icc D.lo D.hi).indicator h := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx, NNReal.smul_def, Real.coe_toNNReal _ (D.dens_nonneg x),
        smul_eq_mul, mul_comm, e x hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]; simp
  rw [heq, integrable_indicator_iff measurableSet_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le).1 hh

/-- `J(θ)` has an expectation. -/
theorem mss_integrable_virtualValue (D : TypeDensity) : Integrable D.virtualValue D.measure :=
  mss_integrable_of_mul_dens D
    ((mss_ii_mul_dens D continuous_id _ _).sub
      ((continuous_const.sub D.continuous_cdf).intervalIntegrable _ _))
    fun _ hx => mss_virtualValue_mul D hx

/-- `K(θ)` has an expectation. -/
theorem mss_integrable_virtualCost (D : TypeDensity) : Integrable D.virtualCost D.measure :=
  mss_integrable_of_mul_dens D
    ((mss_ii_mul_dens D continuous_id _ _).add (mss_ii_cdf D _ _))
    fun _ hx => mss_virtualCost_mul D hx

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896), the display after (23.E.6):
`∫∫ (θ₁ + Φ₁(θ₁)/φ₁(θ₁)) φ₁(θ₁)φ₂(θ₂) dθ₂ dθ₁ = ∫ (θ₁φ₁(θ₁) + Φ₁(θ₁)) dθ₁ = [θ₁Φ₁(θ₁)] = θ̄₁`.
Here for one type distribution: `E[K(θ)] = ∫_{θ̲}^{θ̄} (xφ + Φ) = θ̄Φ(θ̄) - θ̲Φ(θ̲) = θ̄` (proved by
the Fubini identity, not by differentiating `xΦ(x)`, which needs `φ` continuous). -/
theorem mss_integral_virtualCost (D : TypeDensity) :
    ∫ x, D.virtualCost x ∂D.measure = ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) ∧
      ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) = D.hi * D.cdf D.hi - D.lo * D.cdf D.lo ∧
      D.hi * D.cdf D.hi - D.lo * D.cdf D.lo = D.hi := by
  have h1 : ∫ x, D.virtualCost x ∂D.measure = ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le D.lo_lt_hi.le] at hx
    exact mss_virtualCost_mul D hx
  have h2 : ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) = D.hi := by
    have := mss_integral_key D D.hi 0
    rw [mss_cdf_hi] at this
    have e : ∀ x, (0 - x) * D.dens x - D.cdf x = -(x * D.dens x + D.cdf x) := fun x => by ring
    simp only [e, intervalIntegral.integral_neg] at this
    linarith
  refine ⟨h1, ?_, ?_⟩ <;> rw [mss_cdf_hi, mss_cdf_lo] <;> [rw [h2]; skip] <;> ring

/-! ### Bayesian incentive compatible social choice functions with densities -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (23.D.15) for any measurable weight `G` (MWG, p. 891, used on p. 895 with
`G = θ + Φ/φ`): `E[yᵢ(θ)G(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(x)G(x)φᵢ(x) dx`. -/
theorem mss_expect_mul (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) {G : ℝ → ℝ} (hG : Measurable G)
    (hyG : Integrable (fun θ => y θ i * G (θ i)) (Measure.pi fun j => (D j).measure)) :
    ∫ θ, y θ i * G (θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        G x * (D i).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := ((proposition_23_D_2 hint).1 hf i).1
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) i hyG]
  simp only [update_self]
  simp_rw [integral_mul_const]
  have h := integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i
    (F := fun x => interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x * G x)
    (((D i).aestronglyMeasurable_of_monotoneOn hmono).mul hG.aestronglyMeasurable)
  rw [(D i).integral_eq] at h
  exact h

/-- With independent types with densities, `E[-tᵢ(θ)] = E[-t̄ᵢ(θᵢ)]` for a Bayesian incentive
compatible social choice function (MWG, p. 896). -/
theorem mss_expected_transfer (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι)
    (ht : Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure)) :
    ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure) =
      ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [integral_neg, integral_neg, re_expected_transfer (fun j => (D j).measure) i ht]
  congr 1
  set E := D i with hE
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hprim : ContinuousOn (fun x => ∫ s in E.lo..x,
      interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) (Set.Icc E.lo E.hi) := by
    rw [← Set.uIcc_of_le hle]
    refine intervalIntegral.continuousOn_primitive_interval ?_
    rw [Set.uIcc_of_le hle]
    exact hmono.integrableOn_isCompact isCompact_Icc
  have hG : AEStronglyMeasurable (fun x =>
      interimU (Measure.pi fun j => (D j).measure) allocV y t i E.lo +
        (∫ s in E.lo..x, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) -
        x * interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x) E.measure :=
    (aestronglyMeasurable_const.add ((hprim.aestronglyMeasurable measurableSet_Icc).mono_ac
      E.absolutelyContinuous)).sub
      (continuous_id.aestronglyMeasurable.mul (E.aestronglyMeasurable_of_monotoneOn hmono))
  refine integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i (hG.congr ?_)
  filter_upwards [mem_ae_iff.2 E.measure_compl_Icc] with x hx
  exact (re_interimTransfer_eq hint hf i hx).symm

/-- For a Bayesian incentive compatible `f`, the functions `ȳᵢ`, `xȳᵢ(x)φᵢ(x)` and `ȳᵢΦᵢ` are
integrable on `[θ̲ᵢ, θ̄ᵢ]` (`ȳᵢ` is monotone there, hence bounded). -/
theorem mss_ybar_ii (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    IntervalIntegrable (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i) volume
        (D i).lo (D i).hi ∧
      IntervalIntegrable (fun x => x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x) volume (D i).lo (D i).hi ∧
      IntervalIntegrable (fun x => interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) volume (D i).lo (D i).hi := by
  set yb := interimBenefit (Measure.pi fun j => (D j).measure) allocV y i with hyb
  set E := D i with hE
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hmono : MonotoneOn yb (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hybI : IntervalIntegrable yb volume E.lo E.hi := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]; exact hmono
  set Cy := |yb E.lo| + |yb E.hi| with hCy
  have hyb_bd : ∀ x ∈ Set.Icc E.lo E.hi, |yb x| ≤ Cy := by
    intro x hx
    have h1 := hmono ⟨le_rfl, hle⟩ hx hx.1
    have h2 := hmono hx ⟨hle, le_rfl⟩ hx.2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (yb E.lo), le_abs_self (yb E.hi), abs_nonneg (yb E.lo),
      abs_nonneg (yb E.hi)]
  have hybm : AEStronglyMeasurable yb (volume.restrict (Set.Ioc E.lo E.hi)) := hybI.1.1
  refine ⟨hybI, ?_, hybI.mul_continuousOn E.continuous_cdf.continuousOn⟩
  exact re_intervalIntegrable_mul_dens E (continuous_id.aestronglyMeasurable.mul hybm)
    ((|E.lo| + |E.hi|) * Cy) fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (re_abs_le_of_mem ⟨hx.1.le, hx.2⟩) (hyb_bd x ⟨hx.1.le, hx.2⟩)
        (abs_nonneg _) (by positivity)

/-- **(23.E.6)**, general form (MWG, p. 895): for a Bayesian incentive compatible `f` with
independent types with densities, agent `i`'s expected payment, computed from the TOP type
(`Uᵢ(θᵢ) = Uᵢ(θ̄ᵢ) - ∫_{θᵢ}^{θ̄ᵢ} ȳᵢ`), is
`E[-t̄ᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)(θ + Φᵢ(θ)/φᵢ(θ))φᵢ(θ) dθ - Uᵢ(θ̄ᵢ)`. -/
theorem mss_payment_from_top (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure =
      (∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualCost x * (D i).dens x) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).hi := by
  obtain ⟨h0, h1, h2⟩ := mss_ybar_ii D hint hf i
  have hle : (D i).lo ≤ (D i).hi := (D i).lo_lt_hi.le
  have hU := ((proposition_23_D_2 hint).1 hf i).2 (D i).hi ⟨hle, le_rfl⟩
  rw [eq_23_D_14 D hint hf i]
  have hJ : ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure)
      allocV y i x * (D i).virtualValue x * (D i).dens x =
      ∫ x in (D i).lo..(D i).hi, ((x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x + interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) - interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [mul_assoc, mss_virtualValue_mul (D i) hx]
    ring
  have hK : ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure)
      allocV y i x * (D i).virtualCost x * (D i).dens x =
      ∫ x in (D i).lo..(D i).hi, (x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x + interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [mul_assoc, mss_virtualCost_mul (D i) hx]
    ring
  rw [hJ, hK, intervalIntegral.integral_sub (h1.add h2) h0, hU]
  ring

/-! ### Step 1 of MWG's proof: (23.E.4)-(23.E.7)

Agent `0` is the seller (MWG's agent 1) and agent `1` the buyer (MWG's agent 2). -/

/-- `x ↦ (s, x)` is measurable. -/
theorem mss_measurable_vec1 (s : ℝ) : Measurable fun x : ℝ => (![s, x] : Fin 2 → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · exact measurable_const
  · exact measurable_id

/-- `x ↦ (x, b)` is measurable. -/
theorem mss_measurable_vec0 (b : ℝ) : Measurable fun x : ℝ => (![x, b] : Fin 2 → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · exact measurable_id
  · exact measurable_const

/-- `update θ 0 s = (s, θ₁)`. -/
theorem mss_update0 (θ : Fin 2 → ℝ) (s : ℝ) : update θ 0 s = ![s, θ 1] := by
  funext j; fin_cases j <;> simp

/-- `update θ 1 b = (θ₀, b)`. -/
theorem mss_update1 (θ : Fin 2 → ℝ) (b : ℝ) : update θ 1 b = ![θ 0, b] := by
  funext j; fin_cases j <;> simp

/-- The seller's expected trading probability as MWG's inner integral (p. 895):
`ȳ₁(θ₁) = ∫_{θ̲₂}^{θ̄₂} y₁(θ₁, θ₂)φ₂(θ₂) dθ₂` (here `ȳ₀(s) = ∫ y₀(s, x)φ₁(x) dx`). -/
theorem mss_interimBenefit_seller (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y) (s : ℝ) :
    interimBenefit (Measure.pi fun j => (D j).measure) allocV y 0 s =
      ∫ x in (D 1).lo..(D 1).hi, y ![s, x] 0 * (D 1).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [interimBenefit, ← (D 1).integral_eq]
  simp only [allocV, mss_update0]
  exact integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 1
    (F := fun x => y ![s, x] 0)
    (((measurable_pi_apply 0).comp (hym.comp (mss_measurable_vec1 s))).aestronglyMeasurable)

/-- **(23.E.5)** (MWG, p. 895): for a Bayesian incentive compatible `f`, the buyer's expected
payment is `E[-t̄₂(θ₂)] = ∫∫ y₂(θ₁, θ₂)(θ₂ - (1 - Φ₂(θ₂))/φ₂(θ₂))φ₁φ₂ - U₂(θ̲₂)` (the double
integral is the expectation under the product of the densities; it is assumed to exist). -/
theorem eq_23_E_5 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 1 x ∂(D 1).measure =
      ∫ θ, y θ 1 * (D 1).virtualValue (θ 1) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 1 (D 1).lo := by
  rw [eq_23_D_14 D hint hf 1, eq_23_D_15 D hint hf 1 hyJ]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 895), "because (23.D.12) implies that
`U₁(θ̲₁) = U₁(θ̄₁) - ∫∫ y₁(θ₁, θ₂)φ₂(θ₂) dθ₂ dθ₁`": for a Bayesian incentive compatible `f` with
`y` measurable, `U₀(θ̲₀) = U₀(θ̄₀) - ∫_{θ̲₀}^{θ̄₀} ∫_{θ̲₁}^{θ̄₁} y₀(s, x)φ₁(x) dx ds`. -/
theorem eq_23_E_5_seller_U (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) :
    interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).lo =
      interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi -
        ∫ s in (D 0).lo..(D 0).hi, ∫ x in (D 1).lo..(D 1).hi, y ![s, x] 0 * (D 1).dens x := by
  have hU := ((proposition_23_D_2 hint).1 hf 0).2 (D 0).hi ⟨(D 0).lo_lt_hi.le, le_rfl⟩
  simp only [mss_interimBenefit_seller D hym] at hU
  linarith

/-- **(23.E.6)** (MWG, p. 895): for a Bayesian incentive compatible `f`, the seller's expected
payment is `E[-t̄₁(θ₁)] = ∫∫ y₁(θ₁, θ₂)(θ₁ + Φ₁(θ₁)/φ₁(θ₁))φ₁φ₂ - U₁(θ̄₁)` (expectation assumed
to exist). -/
theorem eq_23_E_6 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hyK : Integrable (fun θ => y θ 0 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 0 x ∂(D 0).measure =
      ∫ θ, y θ 0 * (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi := by
  rw [mss_payment_from_top D hint hf 0,
    mss_expect_mul D hint hf 0 (mss_measurable_virtualCost (D 0)) hyK]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896): `∫∫ (θ₁ + Φ₁/φ₁)φ₁φ₂ = θ̄₁`, as an
expectation under the product of the two densities. -/
theorem mss_expect_virtualCost (D : Fin 2 → TypeDensity) :
    ∫ θ, (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) = (D 0).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 0
    (mss_measurable_virtualCost (D 0)).aestronglyMeasurable]
  obtain ⟨h1, h2, h3⟩ := mss_integral_virtualCost (D 0)
  rw [h1, h2, h3]

/-- **(23.E.7)** (MWG, p. 896): if moreover `y₁ + y₂ = 1` on `Θ`, the seller's expected payment
is `E[-t̄₁(θ₁)] = θ̄₁ - ∫∫ y₂(θ₁, θ₂)(θ₁ + Φ₁(θ₁)/φ₁(θ₁))φ₁φ₂ - U₁(θ̄₁)`. -/
theorem eq_23_E_7 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 0 x ∂(D 0).measure =
      (D 0).hi - ∫ θ, y θ 1 * (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hK : Integrable (fun θ => (D 0).virtualCost (θ 0)) (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualCost (D 0))
  have hae : (fun θ => (D 0).virtualCost (θ 0) - y θ 1 * (D 0).virtualCost (θ 0)) =ᵐ[
      Measure.pi fun j => (D j).measure] fun θ => y θ 0 * (D 0).virtualCost (θ 0) := by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    rw [show y θ 0 = 1 - y θ 1 by linarith [hsum θ hθ]]
    ring
  rw [eq_23_E_6 D hint hf ((hK.sub hyK).congr hae), ← integral_congr_ae hae,
    integral_sub hK hyK, mss_expect_virtualCost D]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896): budget balance `t₁ + t₂ = 0` gives
`E[-t₁] + E[-t₂] = 0`, and adding (23.E.5) and (23.E.7),
`[U₁(θ̄₁) - θ̄₁] + U₂(θ̲₂) = ∫∫ y₂[(θ₂ - (1 - Φ₂)/φ₂) - (θ₁ + Φ₁/φ₁)]φ₁φ₂`. -/
theorem eq_23_E_sum (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure))
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ θ, -t θ 0 ∂Measure.pi (fun j => (D j).measure) +
        ∫ θ, -t θ 1 ∂Measure.pi (fun j => (D j).measure) = 0 ∧
      interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi - (D 0).hi +
        interimU (Measure.pi fun j => (D j).measure) allocV y t 1 (D 1).lo =
      ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hbbE : ∫ θ, -t θ 0 ∂Measure.pi (fun j => (D j).measure) +
      ∫ θ, -t θ 1 ∂Measure.pi (fun j => (D j).measure) = 0 := by
    rw [← integral_add (f := fun θ => -t θ 0) (g := fun θ => -t θ 1) (ht 0).neg (ht 1).neg,
      integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    linarith [hbb θ hθ]
  refine ⟨hbbE, ?_⟩
  rw [mss_expected_transfer D hint hf 0 (ht 0), mss_expected_transfer D hint hf 1 (ht 1),
    eq_23_E_7 D hint hf hsum hyK, eq_23_E_5 D hint hf hyJ] at hbbE
  simp_rw [mul_sub]
  rw [integral_sub hyJ hyK]
  linarith

/-- **(23.E.4)**, Step 1 of MWG's proof of Proposition 23.E.1 (MWG, p. 895). In any Bayesian
incentive compatible and interim individually rational social choice function with
`y₁ + y₂ = 1` and `t₁ + t₂ = 0` (on `Θ`), independent types with densities `φᵢ > 0`,
`∫∫ y₂(θ₁, θ₂)[(θ₂ - (1 - Φ₂(θ₂))/φ₂(θ₂)) - (θ₁ + Φ₁(θ₁)/φ₁(θ₁))]φ₁φ₂ ≥ 0`
(the two expectations involved are assumed to exist; `mss_integrable_y_mul` proves this for
bounded measurable `y`). Agent `0` is the seller, agent `1` the buyer. -/
theorem eq_23_E_4 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure))
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    0 ≤ ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
      ∂Measure.pi (fun j => (D j).measure) := by
  rw [← (eq_23_E_sum D hint hf ht hsum hbb hyJ hyK).2]
  have h0 := hir.1 (D 0).hi ⟨(D 0).lo_lt_hi.le, le_rfl⟩
  have h1 := hir.2 (D 1).lo ⟨le_rfl, (D 1).lo_lt_hi.le⟩
  linarith

/-- For `y` measurable with `|y₂| ≤ 1` on `Θ`, the expectations `E[y₂J₂(θ₂)]`, `E[y₂K₁(θ₁)]` and
`E[y₂(J₂(θ₂) - K₁(θ₁))]` of (23.E.4)-(23.E.7) exist (`J₂ = θ - (1 - Φ₂)/φ₂`,
`K₁ = θ + Φ₁/φ₁`). -/
theorem mss_integrable_y_mul (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable fun θ => y θ 1)
    (hb : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → |y θ 1| ≤ 1) :
    Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1)) (Measure.pi fun j => (D j).measure) ∧
      Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
        (Measure.pi fun j => (D j).measure) ∧
      Integrable (fun θ => y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0)))
        (Measure.pi fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hbd : ∀ᵐ θ ∂Measure.pi (fun j => (D j).measure), ‖y θ 1‖ ≤ 1 := by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    rw [Real.norm_eq_abs]; exact hb θ hθ
  have hJ : Integrable (fun θ : Fin 2 → ℝ => (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualValue (D 1))
  have hK : Integrable (fun θ : Fin 2 → ℝ => (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualCost (D 0))
  exact ⟨hJ.bdd_mul hym.aestronglyMeasurable hbd, hK.bdd_mul hym.aestronglyMeasurable hbd,
    (hJ.sub hK).bdd_mul hym.aestronglyMeasurable hbd⟩

/-! ### Step 2 of MWG's proof -/

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), the inner integral over the seller's
type. With the efficient trading rule (`y₂ = 1` if `θ₂ > θ₁`, `0` if `θ₂ < θ₁`, ties free) and
a buyer type `b ∈ [θ̲₂, θ̄₂]`,
`E_{θ₁}[y₂(θ₁, b)(J₂(b) - K₁(θ₁))] = (J₂(b) - Min{b, θ̄₁})Φ₁(Min{b, θ̄₁})`. -/
theorem mss_step2_inner (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y) (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    {b : ℝ} (hb : b ∈ Set.Icc (D 1).lo (D 1).hi) :
    ∫ θ', y (update θ' 1 b) 1 * ((D 1).virtualValue (update θ' 1 b 1) -
        (D 0).virtualCost (update θ' 1 b 0)) ∂Measure.pi (fun j => (D j).measure) =
      ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set E := D 0 with hE
  set c := (D 1).virtualValue b with hc
  simp only [mss_update1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 0
    (F := fun x => y ![x, b] 1 * (c - E.virtualCost x))
    ((((measurable_pi_apply 1).comp (hym.comp (mss_measurable_vec0 b))).mul
      (measurable_const.sub (mss_measurable_virtualCost E))).aestronglyMeasurable),
    E.integral_eq]
  set m' := max E.lo (min b E.hi) with hm'
  have hm'mem : m' ∈ Set.Icc E.lo E.hi :=
    ⟨le_max_left _ _, max_le E.lo_lt_hi.le (min_le_right _ _)⟩
  have hmem : ∀ x ∈ Set.Icc E.lo E.hi,
      InTypes (fun i => (D i).lo) (fun i => (D i).hi) ![x, b] := by
    intro x hx j; fin_cases j
    · exact hx
    · exact hb
  rw [intervalIntegral.integral_congr_ae (g := Set.indicator {x | x ≤ m'}
    fun x => (c - x) * E.dens x - E.cdf x), intervalIntegral.integral_indicator hm'mem,
    mss_integral_key]
  · rcases le_or_gt E.lo b with h | h
    · rw [hm', max_eq_right (le_min h E.lo_lt_hi.le)]
    · rw [hm', max_eq_left ((min_le_left _ _).trans h.le), mss_cdf_of_le E le_rfl,
        mss_cdf_of_le E ((min_le_left _ _).trans h.le)]
      ring
  filter_upwards [Measure.ae_ne volume b] with x hxb hx
  rw [Set.uIoc_of_le E.lo_lt_hi.le] at hx
  have hxI : x ∈ Set.Icc E.lo E.hi := ⟨hx.1.le, hx.2⟩
  obtain ⟨-, -, -, h1, h2⟩ := heff _ (hmem x hxI)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1 h2
  by_cases hxm : x ≤ m'
  · rw [Set.indicator_of_mem (show x ∈ {x | x ≤ m'} from hxm)]
    have hxlt : x < b := by
      rcases lt_or_gt_of_ne hxb with h | h
      · exact h
      · exfalso
        have : m' ≤ max E.lo b := max_le_max le_rfl (min_le_left _ _)
        rcases le_total E.lo b with h' | h'
        · rw [max_eq_right h'] at this; linarith
        · rw [max_eq_left h'] at this; linarith [hx.1]
    rw [h1 hxlt, one_mul, sub_mul, mss_virtualCost_mul E hxI]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {x | x ≤ m'} from hxm)]
    have hbx : b < x := by
      push Not at hxm
      have : min b E.hi < x := lt_of_le_of_lt (le_max_right _ _) hxm
      rcases le_total b E.hi with h' | h'
      · rw [min_eq_left h'] at this; exact this
      · rw [min_eq_right h'] at this; linarith [hx.2]
    rw [h2 hbx, zero_mul, zero_mul]

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), first display: with the efficient
trading rule the left side of (23.E.4) can be written as
`∫_{θ̲₂}^{θ̄₂} ∫_{θ̲₁}^{Min{θ₂, θ̄₁}} [((θ₂ - (1 - Φ₂)/φ₂) - θ₁)φ₁(θ₁) - Φ₁(θ₁)]φ₂(θ₂) dθ₁ dθ₂`
(when `θ₂ < θ̲₁` the inner interval is reversed and the inner integral is `0`, as `φ₁ = 0`
and `Φ₁ = 0` below `θ̲₁`). -/
theorem mss_step2_display1 (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y)
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y) :
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      ∫ b in (D 1).lo..(D 1).hi, (∫ x in (D 0).lo..min b (D 0).hi,
        (((D 1).virtualValue b - x) * (D 0).dens x - (D 0).cdf x)) * (D 1).dens b := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hy1 : Measurable fun θ => y θ 1 := (measurable_pi_apply 1).comp hym
  have hF := (mss_integrable_y_mul D hy1 fun θ hθ => by
    obtain ⟨-, h0, h1, -, -⟩ := heff θ hθ
    exact abs_le.2 ⟨by linarith, h1⟩).2.2
  set H : ℝ → ℝ := fun b => ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi)
    with hH
  have hHm : Measurable H :=
    ((mss_measurable_virtualValue (D 1)).sub (measurable_id.min measurable_const)).mul
      ((D 0).continuous_cdf.measurable.comp (measurable_id.min measurable_const))
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) 1 hF,
    integral_congr_ae (g := fun θ => H (θ 1)) ?_,
    integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 1 hHm.aestronglyMeasurable,
    (D 1).integral_eq]
  · refine intervalIntegral.integral_congr fun b _ => ?_
    simp only [hH]
    rw [mss_integral_key]
  filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
    with θ hθ
  exact mss_step2_inner D hym heff (hθ 1)

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), second and third displays: the inner
integral is `[((θ₂ - (1 - Φ₂)/φ₂) - θ₁)Φ₁(θ₁)]_{θ̲₁}^{Min{θ₂, θ̄₁}}`, which equals
`((θ₂ - (1 - Φ₂)/φ₂) - Min{θ₂, θ̄₁})Φ₁(Min{θ₂, θ̄₁})`. -/
theorem mss_step2_display23 (D : Fin 2 → TypeDensity) :
    ∫ b in (D 1).lo..(D 1).hi, (∫ x in (D 0).lo..min b (D 0).hi,
        (((D 1).virtualValue b - x) * (D 0).dens x - (D 0).cdf x)) * (D 1).dens b =
      ∫ b in (D 1).lo..(D 1).hi,
        ((((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) -
          ((D 1).virtualValue b - (D 0).lo) * (D 0).cdf (D 0).lo) * (D 1).dens b) ∧
    ∫ b in (D 1).lo..(D 1).hi,
        ((((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) -
          ((D 1).virtualValue b - (D 0).lo) * (D 0).cdf (D 0).lo) * (D 1).dens b) =
      ∫ b in (D 1).lo..(D 1).hi,
        ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) * (D 1).dens b := by
  refine ⟨intervalIntegral.integral_congr fun b _ => ?_,
    intervalIntegral.integral_congr fun b _ => ?_⟩
  · rw [mss_integral_key, mss_cdf_lo]
    ring
  · rw [mss_cdf_lo]
    ring

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), fourth display: splitting the
buyer's types at `θ̄₁` (where `θ̲₂ < θ̄₁`),
`∫_{θ̲₂}^{θ̄₂} ((θ₂ - (1 - Φ₂)/φ₂) - Min{θ₂, θ̄₁})Φ₁(Min{θ₂, θ̄₁})φ₂ dθ₂
 = -∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ + ∫_{θ̄₁}^{θ̄₂} [(θ₂ - θ̄₁)φ₂(θ₂) + (Φ₂(θ₂) - 1)] dθ₂`.
(If `θ̄₁ > θ̄₂` the second interval is reversed; the identity holds with `φ₂ = 0`, `Φ₂ = 1`
above `θ̄₂`.) -/
theorem mss_step2_display4 (D : Fin 2 → TypeDensity) (hov : (D 1).lo < (D 0).hi) :
    ∫ b in (D 1).lo..(D 1).hi,
        ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) * (D 1).dens b =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) +
        ∫ b in (D 0).hi..(D 1).hi, ((b - (D 0).hi) * (D 1).dens b + ((D 1).cdf b - 1)) := by
  set E := D 1 with hE
  set F := D 0 with hF
  set G : ℝ → ℝ := fun b => (E.virtualValue b - min b F.hi) * F.cdf (min b F.hi) * E.dens b
    with hG
  have e1 : ∀ x ∈ Set.uIoc E.lo F.hi, G x = -((1 - E.cdf x) * F.cdf x) := by
    intro x hx
    rw [Set.uIoc_of_le hov.le] at hx
    simp only [hG, min_eq_left hx.2]
    rcases le_or_gt x E.hi with h | h
    · rw [mul_right_comm, sub_mul, mss_virtualValue_mul E ⟨hx.1.le, h⟩]; ring
    · rw [E.dens_eq_zero x fun h' => absurd h'.2 (not_le.2 h), mss_cdf_of_ge E h.le]; ring
  have e2 : ∀ x ∈ Set.uIoc F.hi E.hi, G x = (x - F.hi) * E.dens x + (E.cdf x - 1) := by
    intro x hx
    rcases Set.mem_uIoc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hG, min_eq_right h1.le, mss_cdf_hi, mul_one]
      rw [sub_mul, mss_virtualValue_mul E ⟨hov.le.trans h1.le, h2⟩]; ring
    · simp only [hG]
      rw [E.dens_eq_zero x fun h' => absurd h'.2 (not_le.2 h1), mss_cdf_of_ge E h1.le]; ring
  have i1 : IntervalIntegrable (fun x => -((1 - E.cdf x) * F.cdf x)) volume E.lo F.hi :=
    (((continuous_const.sub E.continuous_cdf).mul F.continuous_cdf).neg).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => (x - F.hi) * E.dens x + (E.cdf x - 1)) volume
      F.hi E.hi :=
    (mss_ii_mul_dens E (continuous_id.sub continuous_const) _ _).add
      ((E.continuous_cdf.sub continuous_const).intervalIntegrable _ _)
  have j1 : IntervalIntegrable G volume E.lo F.hi := by
    rw [intervalIntegrable_iff] at i1 ⊢
    exact i1.congr_fun (fun x hx => (e1 x hx).symm) measurableSet_uIoc
  have j2 : IntervalIntegrable G volume F.hi E.hi := by
    rw [intervalIntegrable_iff] at i2 ⊢
    exact i2.congr_fun (fun x hx => (e2 x hx).symm) measurableSet_uIoc
  rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e1),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e2),
    intervalIntegral.integral_neg]

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), fifth display:
`∫_{θ̄₁}^{θ̄₂} [(θ₂ - θ̄₁)φ₂(θ₂) + (Φ₂(θ₂) - 1)] dθ₂ = [(θ₂ - θ̄₁)(Φ₂(θ₂) - 1)]_{θ̄₁}^{θ̄₂} = 0`
(for any `θ̄₁`; proved by the Fubini identity rather than by differentiating, which would need
`φ₂` continuous). -/
theorem mss_step2_display5 (D : Fin 2 → TypeDensity) :
    ∫ b in (D 0).hi..(D 1).hi, ((b - (D 0).hi) * (D 1).dens b + ((D 1).cdf b - 1)) =
      ((D 1).hi - (D 0).hi) * ((D 1).cdf (D 1).hi - 1) -
        ((D 0).hi - (D 0).hi) * ((D 1).cdf (D 0).hi - 1) ∧
    ((D 1).hi - (D 0).hi) * ((D 1).cdf (D 1).hi - 1) -
        ((D 0).hi - (D 0).hi) * ((D 1).cdf (D 0).hi - 1) = 0 := by
  set E := D 1 with hE
  set a := (D 0).hi with ha
  have hz : ((E.hi - a) * (E.cdf E.hi - 1) - (a - a) * (E.cdf a - 1)) = 0 := by
    rw [mss_cdf_hi]; ring
  refine ⟨?_, hz⟩
  rw [hz]
  have k1 := mss_integral_key E E.hi a
  have k2 := mss_integral_key E a a
  have ii : ∀ u v : ℝ, IntervalIntegrable (fun x => (a - x) * E.dens x - E.cdf x) volume u v :=
    fun u v => (mss_ii_mul_dens E (continuous_const.sub continuous_id) _ _).sub (mss_ii_cdf E _ _)
  have k3 := intervalIntegral.integral_interval_sub_left (ii E.lo E.hi) (ii E.lo a)
  rw [k1, k2, mss_cdf_hi] at k3
  have e : ∀ x, (x - a) * E.dens x + (E.cdf x - 1) = -((a - x) * E.dens x - E.cdf x) - 1 :=
    fun x => by ring
  simp only [e]
  rw [intervalIntegral.integral_sub (f := fun x => -((a - x) * E.dens x - E.cdf x))
    (g := fun _ => (1 : ℝ)) (ii a E.hi).neg intervalIntegrable_const,
    intervalIntegral.integral_neg, ← k3, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), last display:
`-∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ < 0` "because `θ̄₁ > θ̲₂` and `θ̲₁ < θ̄₂`". -/
theorem mss_step2_neg (D : Fin 2 → TypeDensity) (h01 : (D 0).lo < (D 1).hi)
    (h10 : (D 1).lo < (D 0).hi) :
    -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) < 0 := by
  set E := D 1 with hE
  set F := D 0 with hF
  set g : ℝ → ℝ := fun b => (1 - E.cdf b) * F.cdf b with hg
  have gc : Continuous g := (continuous_const.sub E.continuous_cdf).mul F.continuous_cdf
  have g0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (by linarith [(mss_cdf_mem E x).2])
    (mss_cdf_mem F x).1
  set a := max F.lo E.lo with ha
  set b := min F.hi E.hi with hb
  have hab : a < b := max_lt (lt_min F.lo_lt_hi h01) (lt_min h10 E.lo_lt_hi)
  have h1 : E.lo ≤ a := le_max_right _ _
  have h2 : b ≤ F.hi := min_le_left _ _
  have p1 : 0 ≤ ∫ x in E.lo..a, g x := intervalIntegral.integral_nonneg h1 fun x _ => g0 x
  have p3 : 0 ≤ ∫ x in b..F.hi, g x := intervalIntegral.integral_nonneg h2 fun x _ => g0 x
  have p2 : 0 < ∫ x in a..b, g x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (gc.intervalIntegrable _ _)
      (fun x hx => mul_pos (mss_one_sub_cdf_pos E (lt_of_lt_of_le hx.2 (min_le_right _ _)))
        (mss_cdf_pos F (lt_of_le_of_lt (le_max_left _ _) hx.1))) hab
  have s1 := intervalIntegral.integral_add_adjacent_intervals (a := E.lo) (b := a) (c := F.hi)
    (gc.intervalIntegrable (μ := volume) _ _) (gc.intervalIntegrable (μ := volume) _ _)
  have s2 := intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b) (c := F.hi)
    (gc.intervalIntegrable (μ := volume) _ _) (gc.intervalIntegrable (μ := volume) _ _)
  change -(∫ x in E.lo..F.hi, g x) < 0
  linarith

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896): condition (23.E.4) cannot be
satisfied by the efficient trading rule (`y₂ = 1` whenever `θ₂ > θ₁`, `y₂ = 0` whenever
`θ₂ < θ₁`): its left side equals `-∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ < 0` when
`(θ̲₁, θ̄₁) ∩ (θ̲₂, θ̄₂) ≠ ∅`. -/
theorem mss_step2 (D : Fin 2 → TypeDensity) (h01 : (D 0).lo < (D 1).hi)
    (h10 : (D 1).lo < (D 0).hi) {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y) :
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) ∧
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) < 0 := by
  have h : ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) := by
    rw [mss_step2_display1 D hym heff, (mss_step2_display23 D).1, (mss_step2_display23 D).2,
      mss_step2_display4 D h10, (mss_step2_display5 D).1, (mss_step2_display5 D).2, add_zero]
  exact ⟨h, h ▸ mss_step2_neg D h01 h10⟩

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, by MWG's own
two-step proof: Step 1 (`eq_23_E_4`) says that any Bayesian incentive compatible, interim
individually rational social choice function with `y₁ + y₂ = 1` and `t₁ + t₂ = 0` satisfies
(23.E.4); Step 2 (`mss_step2`) says that the efficient trading rule violates (23.E.4). Same
hypotheses as `proposition_23_E_1` (the expectations in (23.E.4) exist because `y` is
measurable and `y₂ ∈ [0, 1]`). -/
theorem proposition_23_E_1_mwg (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  obtain ⟨z, ⟨hz0, hz0'⟩, ⟨hz1, hz1'⟩⟩ := hov
  obtain ⟨hyJ, hyK, -⟩ := mss_integrable_y_mul D ((measurable_pi_apply 1).comp hym)
    fun θ hθ => by
      obtain ⟨-, h0, h1, -, -⟩ := heff θ hθ
      exact abs_le.2 ⟨by linarith, h1⟩
  have h1 := eq_23_E_4 D hint hbic ht (fun θ hθ => (heff θ hθ).1) hbb hir hyJ hyK
  have h2 := (mss_step2 D (hz0.trans hz1') (hz1.trans hz0') hym heff).2
  linarith

/-- Non-vacuity of Step 1 (`eq_23_E_4`): with both types uniform on `[0, 1]`, the posted-price
rule at `1/2` satisfies every hypothesis of (23.E.4) (Bayesian incentive compatibility, interim
individual rationality, `y₁ + y₂ = 1`, budget balance, the expectations existing). -/
theorem eq_23_E_4_instance :
    InterimIntegrable (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) allocV
      postY postT (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    BayesianICOn (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) allocV
      postY postT (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    (∀ i, Integrable (fun θ => postT θ i)
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure)) ∧
    (∀ θ, postY θ 0 + postY θ 1 = 1) ∧
    BudgetBalancedOn (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) postT ∧
    InterimIR (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) postY postT
      (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    Integrable (fun θ => postY θ 1 * uniform01.virtualValue (θ 1))
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) ∧
    Integrable (fun θ => postY θ 1 * uniform01.virtualCost (θ 0))
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) := by
  have := uniform01.isProbabilityMeasure
  obtain ⟨hint, -, hbic, -, hir, hbb, -⟩ := proposition_23_E_1_instance_no_eff
  have hq : ∀ θ, 0 ≤ postQ θ ∧ postQ θ ≤ 1 := fun θ => by
    simp only [postQ]; split_ifs <;> norm_num
  obtain ⟨hyJ, hyK, -⟩ := mss_integrable_y_mul (fun _ : Fin 2 => uniform01) (y := postY)
    (by simpa [postY] using measurable_postQ) fun θ _ => by
      simp only [postY, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact abs_le.2 ⟨by linarith [(hq θ).1], (hq θ).2⟩
  refine ⟨hint, hbic, fun i => ?_, fun θ => by simp [postY], hbb, hir, hyJ, hyK⟩
  refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 ?_ 1
    fun θ _ => ?_
  · fin_cases i
    · simpa [postT] using measurable_postQ.div_const 2
    · simpa [postT] using measurable_postQ.div_const 2
  · fin_cases i <;> simp only [postT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_neg] <;>
      rw [abs_le] <;> constructor <;> linarith [hq θ]

/-! ### Exercise 23.E.6(b): uniqueness of the symmetric linear equilibrium -/

/-- Exercise 23.E.6(b) with a general linear strategy of the other partner: the expected utility
of a partner with valuation `θ` who bids `β` when the other (valuation `s ~ U[0, 1]`) bids
`as + d`: if `β ≥ as + d` he buys the other's unit at `β` (utility `2θ - β`), otherwise the other
buys his unit and pays `as + d`. -/
noncomputable def partnerEULin (a d β θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, if a * s + d ≤ β then 2 * θ - β else a * s + d

/-- `partnerEULin` against `b(s) = 2s/3` is `partnerEU`. -/
theorem partnerEULin_two_thirds (β θ : ℝ) : partnerEULin (2 / 3) 0 β θ = partnerEU β θ := by
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : 2 / 3 * s + 0 = 2 * s / 3 := by ring
  simp only [e]

/-- Closed form of `partnerEULin` for a bid `β = ap + d` with `p ∈ [0, 1]` (the bidder wins
exactly when the other's valuation is at most `p`), `a > 0`:
`(2θ - β)p + a(1 - p²)/2 + d(1 - p)`. -/
theorem partnerEULin_eq {a d θ p : ℝ} (ha : 0 < a) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    partnerEULin a d (a * p + d) θ =
      (2 * θ - (a * p + d)) * p + a * (1 - p ^ 2) / 2 + d * (1 - p) := by
  set g : ℝ → ℝ := fun s => if a * s + d ≤ a * p + d then 2 * θ - (a * p + d) else a * s + d
    with hg
  have e1 : ∀ x ∈ Set.uIoc 0 p, g x = 2 * θ - (a * p + d) := by
    intro x hx
    rw [Set.uIoc_of_le hp.1] at hx
    have : a * x + d ≤ a * p + d := by nlinarith [hx.2]
    simp only [hg, this, ite_true]
  have e2 : ∀ x ∈ Set.uIoc p 1, g x = a * x + d := by
    intro x hx
    rw [Set.uIoc_of_le hp.2] at hx
    have : ¬a * x + d ≤ a * p + d := by nlinarith [hx.1]
    simp only [hg, this, ite_false]
  have j1 : IntervalIntegrable g volume 0 p := by
    have i1 : IntervalIntegrable (fun _ : ℝ => 2 * θ - (a * p + d)) volume 0 p :=
      intervalIntegrable_const
    rw [intervalIntegrable_iff] at i1 ⊢
    exact i1.congr_fun (fun x hx => (e1 x hx).symm) measurableSet_uIoc
  have j2 : IntervalIntegrable g volume p 1 := by
    have i2 : IntervalIntegrable (fun x : ℝ => a * x + d) volume p 1 :=
      (continuous_const.mul continuous_id |>.add continuous_const).intervalIntegrable _ _
    rw [intervalIntegrable_iff] at i2 ⊢
    exact i2.congr_fun (fun x hx => (e2 x hx).symm) measurableSet_uIoc
  change ∫ s in (0 : ℝ)..1, g s = _
  rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e1),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e2),
    intervalIntegral.integral_add (f := fun x => a * x) (g := fun _ => d)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  ring

/-- In a symmetric linear equilibrium, the derivative of the bidder's objective in the winning
probability vanishes at every interior type: `2θ - 3aθ - 2d = 0`. -/
theorem partner_foc {a d θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (heq : ∀ β, partnerEULin a d β θ ≤ partnerEULin a d (a * θ + d) θ) :
    2 * θ - 3 * a * θ - 2 * d = 0 := by
  set D := 2 * θ - 3 * a * θ - 2 * d with hD
  set m := min θ (1 - θ) with hm
  have hm0 : 0 < m := lt_min hθ.1 (by linarith [hθ.2])
  set ε := m / (3 * a + 2 * |D| + 2) with hε
  have hden : 0 < 3 * a + 2 * |D| + 2 := by positivity
  have hε0 : 0 < ε := div_pos hm0 hden
  have hεD : |ε * D| ≤ m / 2 := by
    rw [abs_mul, abs_of_pos hε0, hε, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [abs_nonneg D]
  have hεa : 3 * a * ε ≤ m := by
    rw [hε, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith [abs_nonneg D]
  have hm1 : m ≤ 1 := (min_le_left _ _).trans hθ.2.le
  have hp : θ + ε * D ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 := abs_le.1 hεD
    have h2 : m ≤ θ := min_le_left _ _
    have h3 : m ≤ 1 - θ := min_le_right _ _
    constructor <;> linarith [h1.1, h1.2]
  have h := heq (a * (θ + ε * D) + d)
  rw [partnerEULin_eq ha hp, partnerEULin_eq ha ⟨hθ.1.le, hθ.2.le⟩] at h
  have key : ε * D ^ 2 * (1 - 3 * a * ε / 2) ≤ 0 := by nlinarith
  have hpos : 0 < 1 - 3 * a * ε / 2 := by linarith
  have : D ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos (mul_pos hε0 hc) hpos
    linarith
  nlinarith [sq_nonneg D]

/-- **Exercise 23.E.6(b)** (MWG, p. 922), uniqueness: among strictly increasing linear
strategies `b(θ) = aθ + d` (`a > 0`), `b(θ) = 2θ/3` is the only symmetric Bayesian Nash
equilibrium of "the highest bidder buys the other's unit and pays his bid" with valuations
uniform on `[0, 1]`: if no type `θ ∈ [0, 1]` gains by any bid `β` when the other partner uses
`b`, then `a = 2/3` and `d = 0`; conversely `b(θ) = 2θ/3` is an equilibrium
(`exercise_23_E_6b`). (With `a > 0` ties have probability zero, so the tie rule is
irrelevant.) -/
theorem exercise_23_E_6b_unique {a d : ℝ} (ha : 0 < a) :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ β, partnerEULin a d β θ ≤ partnerEULin a d (a * θ + d) θ) ↔
      a = 2 / 3 ∧ d = 0 := by
  constructor
  · intro heq
    have h1 := partner_foc ha (θ := 1 / 2) ⟨by norm_num, by norm_num⟩
      (heq (1 / 2) ⟨by norm_num, by norm_num⟩)
    have h2 := partner_foc ha (θ := 1 / 4) ⟨by norm_num, by norm_num⟩
      (heq (1 / 4) ⟨by norm_num, by norm_num⟩)
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩ θ hθ β
    rw [partnerEULin_two_thirds, partnerEULin_two_thirds,
      show 2 / 3 * θ + 0 = 2 * θ / 3 by ring]
    exact exercise_23_E_6b hθ β

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 23.F.7 (Dana-Spier): the reduction to virtual welfare

MWG, Exercise 23.F.7 (p. 924). Two firms `j ∈ {false, true}` with private fixed costs `θⱼ`,
independent with densities `φⱼ > 0` on `[θ̲ⱼ, θ̄ⱼ]`; demand `p = 1 - x`, marginal cost `c`;
the planner chooses a market structure `k(θ)` (neither, one, or both firms licensed; Cournot
competition when both) and transfers `tⱼ(θ)` from firm `j`, maximising
`E[W]`, `W = ∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ` (`dsWelfare`), over Bayesian incentive compatible,
interim individually rational mechanisms (`DSFeasible`). In the linear form of Section 23.D
firm `j` has utility `θⱼvⱼ + τⱼ` with `vⱼ = -xⱼ` (`dsAlloc`) and `τⱼ = πᶜⱼ - tⱼ` (`dsTau`),
so Proposition 23.D.2 and the revenue formulas apply.

* `exercise_23_F_7_reduction`, the missing step (the two-firm analogue of (23.F.4)):
  `E[W] = E[S + ∑ⱼ xⱼ(λπᶜⱼ - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))] - (λ - 1)∑ⱼ Uⱼ(θ̄ⱼ)`, the
  virtual welfare being `dsVirtualWelfare` with virtual costs `dsVirtualCost` (from
  `RegulationExercises`).
* `exercise_23_F_7_optimal`: for `λ > 1`, a feasible mechanism with `Uⱼ(θ̄ⱼ) = 0` that maximises
  virtual welfare at every cost profile is optimal; with `Φ/φ` increasing this pointwise rule has
  the monotonicity incentive compatibility needs (`exercise_23_F_7`, `dsVirtualCost_strictMono`).
* `exercise_23_F_7_instance`: costs uniform on `[0, 1/100]`, `c = 0`, `λ = 2`: licensing both
  firms and charging each `1/9 - 1/100` is optimal.

**Departures.** Participation is interim (`Uⱼ(θⱼ) ≥ 0`); market structures are deterministic;
the reduction holds for any `λ` and for different densities of the two firms. That for every
`(c, λ > 1, φ)` with `Φ/φ` nondecreasing the pointwise virtual-welfare rule can be completed by
transfers into a feasible mechanism is `exercise_23_F_7_general` (`EnvelopeCompletion`).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-- Exercise 23.F.7: `xⱼ(y) = 1` if firm `j` is awarded production rights in market structure
`y`, `0` otherwise. -/
noncomputable def dsX (y : Bool × Bool) (j : Bool) : ℝ := if dsProduces y j then 1 else 0

/-- Exercise 23.F.7 in the linear form of Section 23.D: firm `j` of fixed cost `θⱼ` has utility
`θⱼvⱼ + τⱼ` with `vⱼ = -xⱼ(k(θ))` (the fixed cost is paid only when producing). -/
noncomputable def dsAlloc (k : (Bool → ℝ) → Bool × Bool) : (Bool → ℝ) → Bool → ℝ :=
  fun θ j => -dsX (k θ) j

/-- Exercise 23.F.7 in the linear form: firm `j`'s type-independent payoff
`τⱼ = (Cournot profit before fixed cost) - tⱼ`, `tⱼ` the transfer from firm `j` to the
planner. -/
noncomputable def dsTau (c : ℝ) (k : (Bool → ℝ) → Bool × Bool) (t : (Bool → ℝ) → Bool → ℝ) :
    (Bool → ℝ) → Bool → ℝ :=
  fun θ j => dsGross c (k θ) j - t θ j

/-- Exercise 23.F.7: firm `j`'s gross (pretransfer) profit `πⱼ = Cournot profit - θⱼxⱼ`. -/
noncomputable def dsProfit (c : ℝ) (y : Bool × Bool) (θ : Bool → ℝ) (j : Bool) : ℝ :=
  dsGross c y j - θ j * dsX y j

/-- **Exercise 23.F.7** (MWG, p. 924): social welfare `W = ∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ` in
market structure `y` with fixed costs `θ` and transfers `t` to the planner. -/
noncomputable def dsWelfare (c lam : ℝ) (y : Bool × Bool) (θ : Bool → ℝ) (t : Bool → ℝ) : ℝ :=
  ∑ j, dsProfit c y θ j + dsSurplus c y + (lam - 1) * ∑ j, t j

/-- Exercise 23.F.7: firm `j`'s utility in the linear form is its profit net of the transfer,
`θⱼvⱼ + τⱼ = πⱼ - tⱼ`. -/
theorem ds_linU (c : ℝ) (k : (Bool → ℝ) → Bool × Bool) (t : (Bool → ℝ) → Bool → ℝ)
    (θ : Bool → ℝ) (j : Bool) :
    linU allocV j (dsAlloc k θ, dsTau c k t θ) (θ j) = dsProfit c (k θ) θ j - t θ j := by
  simp only [linU, allocV, dsAlloc, dsTau, dsProfit]
  ring

/-- **Exercise 23.F.7** (MWG, p. 924): the mechanisms the planner may use. The types
`θ = (θ_false, θ_true)` (fixed costs) are independent with densities `φⱼ > 0` on `[θ̲ⱼ, θ̄ⱼ]`;
`k` (measurable) chooses the market structure and `t` the transfers; the induced social choice
function is Bayesian incentive compatible and interim individually rational (`Uⱼ(θⱼ) ≥ 0`), and
the expectations involved exist. -/
def DSFeasible (D : Bool → TypeDensity) (c : ℝ) (k : (Bool → ℝ) → Bool × Bool)
    (t : (Bool → ℝ) → Bool → ℝ) : Prop :=
  Measurable k ∧ (∀ j, Integrable (fun θ => t θ j) (Measure.pi fun i => (D i).measure)) ∧
    InterimIntegrable (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t)
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    BayesianICOn (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t)
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    ∀ j, ∀ x ∈ Set.Icc (D j).lo (D j).hi,
      0 ≤ interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t) j x

/-- A function of the market structure is integrable. -/
theorem ds_integrable_comp (D : Bool → TypeDensity) {k : (Bool → ℝ) → Bool × Bool}
    (hk : Measurable k) (f : Bool × Bool → ℝ) :
    Integrable (fun θ => f (k θ)) (Measure.pi fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  refine Integrable.of_bound ((measurable_of_finite f).comp hk).aestronglyMeasurable
    (∑ y, |f y|) (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun y => |f y|) (fun y _ => abs_nonneg _)
    (Finset.mem_univ (k θ))

/-- `0 ≤ xⱼ ≤ 1`. -/
theorem ds_x_mem (y : Bool × Bool) (j : Bool) : 0 ≤ dsX y j ∧ dsX y j ≤ 1 := by
  simp only [dsX]; split_ifs <;> norm_num

/-- `xⱼ(k(θ))g(θⱼ)` is integrable when `g` is integrable for `μⱼ`. -/
theorem ds_integrable_x_mul (D : Bool → TypeDensity) {k : (Bool → ℝ) → Bool × Bool}
    (hk : Measurable k) (j : Bool) {g : ℝ → ℝ} (hg : Integrable g (D j).measure) :
    Integrable (fun θ => dsX (k θ) j * g (θ j)) (Measure.pi fun i => (D i).measure) := by
  have : ∀ i, IsProbabilityMeasure (D i).measure := fun i => (D i).isProbabilityMeasure
  refine (integrable_comp_eval hg).bdd_mul (c := 1)
    ((measurable_of_finite fun y => dsX y j).comp hk).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ds_x_mem (k θ) j]

/-- The identity function has an expectation under a type distribution. -/
theorem ds_integrable_id (E : TypeDensity) : Integrable (fun x => x) E.measure :=
  mss_integrable_of_mul_dens E (mss_ii_mul_dens E continuous_id _ _) fun _ _ => rfl

/-- Gross Cournot profits vanish for firms without production rights: `πᶜⱼ = xⱼπᶜⱼ`. -/
theorem ds_gross_eq (c : ℝ) (y : Bool × Bool) (j : Bool) :
    dsGross c y j = dsX y j * dsGross c y j := by
  simp only [dsX, dsGross]; split_ifs <;> ring

/-- `dsVirtualWelfare` as a sum over firms: `S + ∑ⱼ xⱼ(λπᶜⱼ - vcⱼ)`. -/
theorem ds_virtualWelfare_eq (c lam : ℝ) (vc : Bool → ℝ) (y : Bool × Bool) :
    dsVirtualWelfare c lam vc y = dsSurplus c y + ∑ j, dsX y j * (lam * dsGross c y j - vc j) := by
  simp only [dsVirtualWelfare, Fintype.sum_bool, dsX]
  split_ifs <;> ring

/-- **Exercise 23.F.7** (MWG, p. 924), the missing step: the planner's expected welfare is
expected VIRTUAL welfare (the two-firm analogue of (23.F.4)). For every feasible mechanism
`(k, t)`,
`E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ] = E[S(k(θ)) + ∑ⱼ xⱼ(λπᶜⱼ - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))]
  - (λ - 1)∑ⱼ Uⱼ(θ̄ⱼ)`,
where `πᶜⱼ` is the Cournot profit before the fixed cost; the virtual welfare is
`dsVirtualWelfare` with virtual costs `dsVirtualCost` (and it has an expectation). This holds
for any `λ` and any (possibly different) type densities. -/
theorem exercise_23_F_7_reduction (D : Bool → TypeDensity) (c lam : ℝ)
    {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ} (h : DSFeasible D c k t) :
    Integrable (fun θ => dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ))
        (Measure.pi fun i => (D i).measure) ∧
      ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) =
        ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)
          ∂Measure.pi (fun i => (D i).measure) -
        (lam - 1) * ∑ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k)
          (dsTau c k t) j (D j).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hk, ht, hint, hbic, -⟩ := h
  set P := Measure.pi fun i => (D i).measure with hP
  -- integrability of the pieces
  have iG : ∀ j, Integrable (fun θ => dsGross c (k θ) j) P := fun j =>
    ds_integrable_comp D hk fun y => dsGross c y j
  have iS : Integrable (fun θ => dsSurplus c (k θ)) P := ds_integrable_comp D hk _
  have iXK : ∀ j, Integrable (fun θ => dsX (k θ) j * (D j).virtualCost (θ j)) P := fun j =>
    ds_integrable_x_mul D hk j (mss_integrable_virtualCost (D j))
  have iXT : ∀ j, Integrable (fun θ => θ j * dsX (k θ) j) P := fun j =>
    (ds_integrable_x_mul D hk j (ds_integrable_id (D j))).congr
      (Filter.Eventually.of_forall fun θ => by simp only [mul_comm])
  have iTau : ∀ j, Integrable (fun θ => dsTau c k t θ j) P := fun j => (iG j).sub (ht j)
  -- the expected transfer of each firm
  have hT : ∀ j, ∫ θ, t θ j ∂P = ∫ θ, dsGross c (k θ) j ∂P -
      ∫ θ, dsX (k θ) j * (D j).virtualCost (θ j) ∂P -
      interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    intro j
    have e1 := mss_expected_transfer D hint hbic j (iTau j)
    have hyK : Integrable (fun θ => dsAlloc k θ j * (D j).virtualCost (θ j)) P :=
      ((iXK j).neg).congr (Filter.Eventually.of_forall fun θ => by
        simp only [dsAlloc, Pi.neg_apply]; ring)
    have e2 := mss_payment_from_top D hint hbic j
    have e3 := mss_expect_mul D hint hbic j (mss_measurable_virtualCost (D j)) hyK
    rw [← e3, ← e1] at e2
    have e4 : ∫ θ, dsAlloc k θ j * (D j).virtualCost (θ j) ∂P =
        -∫ θ, dsX (k θ) j * (D j).virtualCost (θ j) ∂P := by
      rw [← integral_neg]; congr 1; funext θ; simp only [dsAlloc]; ring
    have e5 : ∫ θ, -dsTau c k t θ j ∂P = -(∫ θ, dsGross c (k θ) j ∂P - ∫ θ, t θ j ∂P) := by
      rw [integral_neg]; congr 1; exact integral_sub (iG j) (ht j)
    rw [e4, e5] at e2
    linarith
  -- the pointwise identity
  set A : (Bool → ℝ) → ℝ := fun θ => dsWelfare c lam (k θ) θ (t θ) with hA
  set B : (Bool → ℝ) → ℝ := fun θ => ∑ j, (t θ j - dsGross c (k θ) j +
    dsX (k θ) j * (D j).virtualCost (θ j)) with hB
  have hpt : ∀ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ) =
      A θ - (lam - 1) * B θ := by
    intro θ
    rw [ds_virtualWelfare_eq]
    simp only [hA, hB, dsWelfare, dsProfit, Fintype.sum_bool, dsVirtualCost,
      TypeDensity.virtualCost]
    linear_combination (-lam) * ds_gross_eq c (k θ) true + (-lam) * ds_gross_eq c (k θ) false
  have iB : Integrable B P := by
    simp only [hB, Fintype.sum_bool]
    exact (((ht true).sub (iG true)).add (iXK true)).add (((ht false).sub (iG false)).add
      (iXK false))
  have iA : Integrable A P := by
    simp only [hA, dsWelfare, dsProfit, Fintype.sum_bool]
    exact ((((iG true).sub (iXT true)).add ((iG false).sub (iXT false))).add iS).add
      (((ht true).add (ht false)).const_mul (lam - 1))
  have iV : Integrable (fun θ => dsVirtualWelfare c lam
      (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)) P := by
    simp only [hpt]; exact iA.sub (iB.const_mul (lam - 1))
  refine ⟨iV, ?_⟩
  have hBj : ∀ j, ∫ θ, (t θ j - dsGross c (k θ) j + dsX (k θ) j * (D j).virtualCost (θ j)) ∂P =
      -interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    intro j
    rw [integral_add (f := fun θ => t θ j - dsGross c (k θ) j)
      (g := fun θ => dsX (k θ) j * (D j).virtualCost (θ j)) ((ht j).sub (iG j)) (iXK j),
      integral_sub (ht j) (iG j), hT j]
    ring
  have hBE : ∫ θ, B θ ∂P = -∑ j, interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    simp only [hB, Fintype.sum_bool]
    rw [integral_add (f := fun θ => t θ true - dsGross c (k θ) true +
        dsX (k θ) true * (D true).virtualCost (θ true))
      (g := fun θ => t θ false - dsGross c (k θ) false +
        dsX (k θ) false * (D false).virtualCost (θ false))
      (((ht true).sub (iG true)).add (iXK true)) (((ht false).sub (iG false)).add (iXK false)),
      hBj true, hBj false]
    ring
  simp only [hpt]
  rw [integral_sub iA (iB.const_mul (lam - 1)), integral_const_mul, hBE]
  ring

/-- **Exercise 23.F.7** (MWG, p. 924), the optimal auction of production rights. Let `λ > 1`.
If a feasible mechanism `(k*, t*)` leaves the highest-cost type of each firm with
`Uⱼ(θ̄ⱼ) = 0` and, at every cost profile `θ ∈ Θ`, chooses a market structure maximising the
virtual welfare `S(y) + ∑_{j producing}(λπᶜⱼ(y) - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))`, then it
maximises the planner's expected welfare `E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ]` among all feasible
mechanisms. (`exercise_23_F_7` shows that this pointwise rule has the monotonicity Bayesian
incentive compatibility requires.) -/
theorem exercise_23_F_7_optimal (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    {ks : (Bool → ℝ) → Bool × Bool} {ts : (Bool → ℝ) → Bool → ℝ} (hs : DSFeasible D c ks ts)
    (hU : ∀ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc ks)
      (dsTau c ks ts) j (D j).hi = 0)
    (hopt : ∀ θ, (∀ j, θ j ∈ Set.Icc (D j).lo (D j).hi) → ∀ y,
      dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) y ≤
        dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (ks θ))
    {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ} (h : DSFeasible D c k t) :
    ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) ≤
      ∫ θ, dsWelfare c lam (ks θ) θ (ts θ) ∂Measure.pi (fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨iV, hW⟩ := exercise_23_F_7_reduction D c lam h
  obtain ⟨iVs, hWs⟩ := exercise_23_F_7_reduction D c lam hs
  rw [hW, hWs]
  simp only [hU, Finset.sum_const_zero, mul_zero, sub_zero]
  have hIR : 0 ≤ ∑ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k)
      (dsTau c k t) j (D j).hi :=
    Finset.sum_nonneg fun j _ => h.2.2.2.2 j _ ⟨(D j).lo_lt_hi.le, le_rfl⟩
  have hle : ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)
      ∂Measure.pi (fun i => (D i).measure) ≤
      ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (ks θ)
      ∂Measure.pi (fun i => (D i).measure) := by
    refine integral_mono_ae iV iVs ?_
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ using hopt θ hθ (k θ)
  nlinarith

/-- Fixed costs uniform on `[0, 1/100]` (the instance of Exercise 23.F.7 below). -/
noncomputable def dsUnif : TypeDensity := uniformDensity 0 (1 / 100) (by norm_num)

/-- For costs uniform on `[0, 1/100]` and `λ = 2`, the virtual cost is `3θ`. -/
theorem ds_unif_virtualCost {x : ℝ} (hx : x ∈ Set.Icc dsUnif.lo dsUnif.hi) :
    dsVirtualCost dsUnif 2 x = 3 * x := by
  have hd : dsUnif.dens x = (1 / 100 - 0 : ℝ)⁻¹ := by
    change (Set.Icc (0 : ℝ) (1 / 100)).indicator (fun _ => (1 / 100 - 0 : ℝ)⁻¹) x = _
    exact Set.indicator_of_mem hx _
  have hc : dsUnif.cdf x = (x - 0) / (1 / 100 - 0) := oa_uniform_cdf (by norm_num) hx
  rw [dsVirtualCost, hd, hc]
  field_simp
  ring

/-- **Exercise 23.F.7** (MWG, p. 924), a solved instance (non-vacuity of
`exercise_23_F_7_optimal`): with fixed costs independent and uniform on `[0, 1/100]`, `c = 0`
and `λ = 2`, licensing both firms (Cournot duopoly) and charging each firm `1/9 - 1/100`
(so the highest-cost type just breaks even) is feasible and maximises the planner's expected
welfare among all feasible mechanisms. -/
theorem exercise_23_F_7_instance {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ}
    (h : DSFeasible (fun _ => dsUnif) 0 k t) :
    DSFeasible (fun _ => dsUnif) 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100) ∧
    ∫ θ, dsWelfare 0 2 (k θ) θ (t θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) ≤
      ∫ θ, dsWelfare 0 2 (true, true) θ (fun _ => 1 / 9 - 1 / 100)
        ∂Measure.pi (fun _ : Bool => dsUnif.measure) := by
  have := dsUnif.isProbabilityMeasure
  have hA : ∀ θ j, dsAlloc (fun _ => (true, true)) θ j = -1 := fun θ j => by
    cases j <;> simp [dsAlloc, dsX, dsProduces]
  have hT : ∀ θ j, dsTau 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100) θ j = 1 / 100 :=
    fun θ j => by cases j <;> simp [dsTau, dsGross, dsProduces]
  have hB : ∀ j a, interimBenefit (Measure.pi fun _ : Bool => dsUnif.measure) allocV
      (dsAlloc fun _ => (true, true)) j a = -1 := fun j a => by
    simp [interimBenefit, allocV, hA]
  have hTr : ∀ j a, interimTransfer (Measure.pi fun _ : Bool => dsUnif.measure)
      (dsTau 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100)) j a = 1 / 100 :=
    fun j a => by simp only [interimTransfer, hT]; simp
  have hF : DSFeasible (fun _ => dsUnif) 0 (fun _ => (true, true))
      (fun _ _ => 1 / 9 - 1 / 100) := by
    refine ⟨measurable_const, fun j => integrable_const _, fun j a _ => ?_, ?_, ?_⟩
    · simp only [allocV, hA, hT]; exact ⟨integrable_const _, integrable_const _⟩
    · intro j x _ a _
      simp only [linU, allocV, hA, hT, le_refl]
    · intro j x hx
      simp only [interimU, hB, hTr]
      have : x ≤ 1 / 100 := hx.2
      linarith
  refine ⟨hF, exercise_23_F_7_optimal (fun _ => dsUnif) 0 (by norm_num : (1 : ℝ) < 2) hF
    (fun j => ?_) (fun θ hθ y => ?_) h⟩
  · simp only [interimU, hB, hTr]
    change (1 / 100 : ℝ) * -1 + 1 / 100 = 0
    norm_num
  · have hv : (fun j => dsVirtualCost ((fun _ => dsUnif) j) 2 (θ j)) = fun j => 3 * θ j :=
      funext fun j => ds_unif_virtualCost (hθ j)
    have b0 : θ false ≤ 1 / 100 := (hθ false).2
    have b1 : θ true ≤ 1 / 100 := (hθ true).2
    have c0 : 0 ≤ θ false := (hθ false).1
    have c1 : 0 ≤ θ true := (hθ true).1
    rw [hv]
    rcases y with ⟨_ | _, _ | _⟩ <;>
      simp [dsVirtualWelfare, dsSurplus, dsGross, dsProduces] <;> norm_num <;> linarith

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Completing a monotone allocation rule by envelope transfers

MWG, Section 23.D, Proposition 23.D.2 (p. 888), sufficiency half, used in Example 23.F.2
(p. 905): "the optimal transfer functions can then be set as `tᵢ(θ) = Uᵢ(θᵢ) - θᵢȳᵢ(θᵢ)`, where
`Uᵢ(θᵢ)` is calculated from constraint (iii)".

* `ecTransfer`: given an allocation rule `y` with independent types with densities, the
  envelope transfers `tᵢ(θ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ - θᵢȳᵢ(θᵢ)`.
* `ec_mechanism`: if every `yᵢ` is measurable, bounded by `1` in absolute value and
  nondecreasing in the agent's own type (for every profile of the others), then `(y, t)` is
  Bayesian incentive compatible, the expectations exist, and `Uᵢ(θᵢ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ`.
* **Example 23.F.2** for general densities (`example_23_F_2_general`): with every virtual
  valuation `Jᵢ` nondecreasing on `[θ̲ᵢ, θ̄ᵢ]` (MWG's assumption), the rule `oaRule` (the good
  goes to the bidder with the largest positive `Jᵢ(θᵢ)`, ties to the lowest index) solves the
  relaxed problem (23.F.8) at every profile, has `yᵢ` nondecreasing in `θᵢ`, and with the
  envelope transfers (`cᵢ = 0`, so `Uᵢ(θ̲ᵢ) = 0`) is a feasible mechanism that maximises the
  seller's expected revenue among all feasible social choice functions. Instance: two bidders
  uniform on `[0, 1]` and `[0, 2]` (`example_23_F_2_general_instance`).

Departure: MWG leave ties `Jᵢ = max{0, maxₖ≠ᵢ Jₖ}` free, saying they have probability zero;
that is not true when some `Jᵢ` is constant on an interval, so the rule breaks ties by a fixed
order of the bidders, which keeps `yᵢ` nondecreasing in `θᵢ`.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Example 23.F.2** (MWG, p. 905) and Proposition 23.D.2: the envelope transfers
`tᵢ(θ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ(s) ds - θᵢȳᵢ(θᵢ)` completing an allocation rule `y`. -/
noncomputable def ecTransfer (D : ι → TypeDensity) (y : (ι → ℝ) → ι → ℝ) (c : ι → ℝ) :
    (ι → ℝ) → ι → ℝ :=
  fun θ i => c i + (∫ s in (D i).lo..(θ i),
      interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) -
    θ i * interimBenefit (Measure.pi fun j => (D j).measure) allocV y i (θ i)

/-- With `yᵢ` measurable and `|yᵢ| ≤ 1`, `yᵢ(a, θ₋ᵢ)` is integrable for every announcement. -/
theorem ec_integrable_update (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1) (i : ι) (a : ℝ) :
    Integrable (fun θ' => y (update θ' i a) i) (Measure.pi fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  exact Integrable.of_bound ((hym i).comp measurable_update_left).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun θ' => by rw [Real.norm_eq_abs]; exact hyb _ i)

/-- `|ȳᵢ| ≤ 1` when `|yᵢ| ≤ 1`. -/
theorem ec_interimBenefit_abs_le (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hyb : ∀ θ i, |y θ i| ≤ 1) (i : ι) (a : ℝ) :
    |interimBenefit (Measure.pi fun j => (D j).measure) allocV y i a| ≤ 1 := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun j => (D j).measure)
    (f := fun θ' => y (update θ' i a) i) (C := 1)
    (Filter.Eventually.of_forall fun θ' => by rw [Real.norm_eq_abs]; exact hyb _ i)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- If `yᵢ` is nondecreasing in the agent's own type for every `θ₋ᵢ`, so is `ȳᵢ`. -/
theorem ec_interimBenefit_mono (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1)
    (hmono : ∀ i θ', ∀ a ∈ Set.Icc (D i).lo (D i).hi, ∀ b ∈ Set.Icc (D i).lo (D i).hi, a ≤ b →
      y (update θ' i a) i ≤ y (update θ' i b) i) (i : ι) :
    MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := fun a ha b hb hab =>
  integral_mono (ec_integrable_update D hym hyb i a) (ec_integrable_update D hym hyb i b)
    fun θ' => hmono i θ' a ha b hb hab

/-- **Proposition 23.D.2** (MWG, p. 888), sufficiency half, as used in Example 23.F.2 (p. 905):
an allocation rule `y` that is measurable, bounded (`|yᵢ| ≤ 1`) and nondecreasing in each
agent's own type, completed by the envelope transfers `ecTransfer`, is Bayesian incentive
compatible, its expectations exist, and `Uᵢ(θᵢ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ`. -/
theorem ec_mechanism (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1)
    (hmono : ∀ i θ', ∀ a ∈ Set.Icc (D i).lo (D i).hi, ∀ b ∈ Set.Icc (D i).lo (D i).hi, a ≤ b →
      y (update θ' i a) i ≤ y (update θ' i b) i) (c : ι → ℝ) :
    InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c)
        (fun i => (D i).lo) (fun i => (D i).hi) ∧
      BayesianICOn (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c)
        (fun i => (D i).lo) (fun i => (D i).hi) ∧
      (∀ i, Integrable (fun θ => ecTransfer D y c θ i) (Measure.pi fun j => (D j).measure)) ∧
      ∀ i a, interimU (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c) i a =
        c i + ∫ s in (D i).lo..a, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s
  := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set P := Measure.pi fun j => (D j).measure with hP
  have hmon := ec_interimBenefit_mono D hym hyb hmono
  have hU : ∀ i a, interimU P allocV y (ecTransfer D y c) i a =
      c i + ∫ s in (D i).lo..a, interimBenefit P allocV y i s := by
    intro i a
    simp only [interimU, interimTransfer, ecTransfer, update_self, integral_const, probReal_univ,
      one_smul]
    ring
  have hint : InterimIntegrable P allocV y (ecTransfer D y c) (fun i => (D i).lo)
      (fun i => (D i).hi) := by
    intro i a _
    refine ⟨ec_integrable_update D hym hyb i a, ?_⟩
    simp only [ecTransfer, update_self]
    exact integrable_const _
  refine ⟨hint, (proposition_23_D_2 hint).2 fun i => ⟨hmon i, fun θ _ => ?_⟩, fun i => ?_, hU⟩
  · rw [hU, hU, intervalIntegral.integral_same, add_zero]
  · -- the transfer is a bounded, a.e. strongly measurable function of `θᵢ`
    set E := D i with hE
    have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
    have hprim : ContinuousOn (fun x => ∫ s in E.lo..x, interimBenefit P allocV y i s)
        (Set.Icc E.lo E.hi) := by
      rw [← Set.uIcc_of_le hle]
      refine intervalIntegral.continuousOn_primitive_interval ?_
      rw [Set.uIcc_of_le hle]
      exact (hmon i).integrableOn_isCompact isCompact_Icc
    have hG : AEStronglyMeasurable (fun x => c i + (∫ s in E.lo..x,
        interimBenefit P allocV y i s) - x * interimBenefit P allocV y i x) E.measure :=
      (aestronglyMeasurable_const.add ((hprim.aestronglyMeasurable measurableSet_Icc).mono_ac
        E.absolutelyContinuous)).sub
        (continuous_id.aestronglyMeasurable.mul (E.aestronglyMeasurable_of_monotoneOn (hmon i)))
    have hGi : Integrable (fun x => c i + (∫ s in E.lo..x,
        interimBenefit P allocV y i s) - x * interimBenefit P allocV y i x) E.measure := by
      refine Integrable.of_bound hG (|c i| + (E.hi - E.lo) + (|E.lo| + |E.hi|)) ?_
      filter_upwards [mem_ae_iff.2 E.measure_compl_Icc] with x hx
      have h1 : |∫ s in E.lo..x, interimBenefit P allocV y i s| ≤ 1 * |x - E.lo| := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.lo) (b := x)
          (C := 1) (f := interimBenefit P allocV y i) fun s _ => by
            rw [Real.norm_eq_abs]; exact ec_interimBenefit_abs_le D hyb i s
        rwa [Real.norm_eq_abs] at this
      have h2 : |x * interimBenefit P allocV y i x| ≤ |x| * 1 := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ec_interimBenefit_abs_le D hyb i x) (abs_nonneg x)
      have h3 : |x - E.lo| ≤ E.hi - E.lo := by
        rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
      have h4 : |x| ≤ |E.lo| + |E.hi| := re_abs_le_of_mem hx
      rw [Real.norm_eq_abs]
      calc |c i + (∫ s in E.lo..x, interimBenefit P allocV y i s) -
            x * interimBenefit P allocV y i x|
          ≤ |c i| + |∫ s in E.lo..x, interimBenefit P allocV y i s| +
            |x * interimBenefit P allocV y i x| := by
            refine (abs_sub _ _).trans ?_
            exact add_le_add (abs_add_le _ _) le_rfl
        _ ≤ |c i| + (E.hi - E.lo) + (|E.lo| + |E.hi|) := by nlinarith
    exact integrable_comp_eval (μ := fun j => (D j).measure) (i := i) hGi

/-! ### Example 23.F.2 for general densities -/

/-- **Example 23.F.2** (MWG, p. 905): bidder `i` wins under the (23.F.9) rule at virtual
valuations `J`: `Jᵢ(θᵢ) > 0` and `Jᵢ(θᵢ)` is the largest virtual valuation, ties going to the
lowest index. -/
def oaWins {n : ℕ} (J : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) (i : Fin n) : Prop :=
  0 < J i (θ i) ∧ ∀ k, J k (θ k) < J i (θ i) ∨ (J k (θ k) = J i (θ i) ∧ i ≤ k)

open Classical in
/-- **Example 23.F.2** (MWG, p. 905), the pointwise rule (23.F.9) with a fixed tie-break: the
good goes to the bidder with the largest positive virtual valuation `Jᵢ(θᵢ)` (lowest index on a
tie) and is kept if all `Jᵢ(θᵢ) ≤ 0`. -/
noncomputable def oaRule {n : ℕ} (D : Fin n → TypeDensity) : (Fin n → ℝ) → Fin n → ℝ :=
  fun θ i => if oaWins (fun k => (D k).virtualValue) θ i then 1 else 0

/-- At most one bidder wins. -/
theorem oa_wins_unique {n : ℕ} {J : Fin n → ℝ → ℝ} {θ : Fin n → ℝ} {i j : Fin n}
    (hi : oaWins J θ i) (hj : oaWins J θ j) : i = j := by
  rcases hi.2 j with h1 | ⟨h1, h1'⟩ <;> rcases hj.2 i with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact le_antisymm h1' h2'

/-- If some virtual valuation is positive, some bidder wins. -/
theorem oa_exists_wins {n : ℕ} {J : Fin n → ℝ → ℝ} {θ : Fin n → ℝ} {k : Fin n}
    (hk : 0 < J k (θ k)) : ∃ i, oaWins J θ i := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun l => J l (θ l))
    ⟨k, Finset.mem_univ k⟩
  set S := Finset.univ.filter fun l => J l (θ l) = J m (θ m) with hS
  have hSne : S.Nonempty := ⟨m, by simp [hS]⟩
  set i := S.min' hSne with hi
  have hiS : i ∈ S := S.min'_mem hSne
  have hJi : J i (θ i) = J m (θ m) := (Finset.mem_filter.1 hiS).2
  refine ⟨i, ⟨?_, fun l => ?_⟩⟩
  · rw [hJi]; exact lt_of_lt_of_le hk (hm k (Finset.mem_univ k))
  · rcases lt_or_eq_of_le (hm l (Finset.mem_univ l)) with h | h
    · left; rw [hJi]; exact h
    · right
      refine ⟨by rw [hJi, h], S.min'_le l ?_⟩
      simp [hS, h]

/-- The rule gives a feasible allocation and solves the relaxed problem (23.F.8) at every
profile (for any virtual valuations). -/
theorem oaRule_pointwiseOpt {n : ℕ} (D : Fin n → TypeDensity) (θ : Fin n → ℝ) :
    PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (oaRule D θ) := by
  classical
  set J : Fin n → ℝ → ℝ := fun k => (D k).virtualValue with hJ
  have hy : ∀ i, oaRule D θ i = if oaWins J θ i then 1 else 0 := fun i => by
    simp only [oaRule, hJ]
  have hsum : ∀ w : Fin n → ℝ, ∀ i, oaWins J θ i →
      ∑ k, oaRule D θ k * w k = w i := by
    intro w i hi
    rw [Finset.sum_eq_single i (fun k _ hk => by
      have hk' : ¬oaWins J θ k := fun hk' => hk (oa_wins_unique hk' hi)
      simp [hy, hk'])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [hy, hi]
  have hfeas : FeasAlloc (oaRule D θ) := by
    refine ⟨fun i => by rw [hy]; split_ifs <;> norm_num, ?_⟩
    by_cases hw : ∃ i, oaWins J θ i
    · obtain ⟨i, hi⟩ := hw
      have := hsum (fun _ => 1) i hi
      simp only [mul_one] at this
      rw [this]
    · push Not at hw
      simp [hy, hw]
  refine ⟨hfeas, fun w' ⟨hw0, hw1⟩ => ?_⟩
  by_cases hw : ∃ i, oaWins J θ i
  · obtain ⟨i, hi⟩ := hw
    have h1 := hsum (fun k => J k (θ k)) i hi
    simp only [hJ] at h1
    rw [h1]
    have hle : ∀ k, J k (θ k) ≤ J i (θ i) := fun k => by
      rcases hi.2 k with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    calc ∑ k, w' k * (D k).virtualValue (θ k) ≤ ∑ k, w' k * J i (θ i) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (hw0 k)
      _ = (∑ k, w' k) * J i (θ i) := by rw [Finset.sum_mul]
      _ ≤ 1 * J i (θ i) := mul_le_mul_of_nonneg_right hw1 hi.1.le
      _ = (D i).virtualValue (θ i) := by rw [one_mul]
  · push Not at hw
    have hneg : ∀ k, J k (θ k) ≤ 0 := fun k => by
      by_contra h
      obtain ⟨i, hi⟩ := oa_exists_wins (J := J) (θ := θ) (not_le.1 h)
      exact hw i hi
    have h0 : ∑ k, oaRule D θ k * (D k).virtualValue (θ k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hy, hw k]
    rw [h0]
    exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0 k) (hneg k)

/-- **Example 23.F.2** (MWG, p. 905): with `Jᵢ` nondecreasing, the rule's `yᵢ` is
nondecreasing in `θᵢ` for every profile of the other bidders' types. -/
theorem oaRule_mono {n : ℕ} (D : Fin n → TypeDensity)
    (hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi)) (i : Fin n)
    (θ' : Fin n → ℝ) {a b : ℝ} (ha : a ∈ Set.Icc (D i).lo (D i).hi)
    (hb : b ∈ Set.Icc (D i).lo (D i).hi) (hab : a ≤ b) :
    oaRule D (update θ' i a) i ≤ oaRule D (update θ' i b) i := by
  classical
  have hJab := hJ i ha hb hab
  simp only [oaRule]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    apply h2
    simp only [oaWins, update_self] at h1 ⊢
    refine ⟨lt_of_lt_of_le h1.1 hJab, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk; right; simp
    · rcases h1.2 k with h | ⟨h, h'⟩
      · left; rw [update_of_ne hk] at h ⊢; linarith
      · rw [update_of_ne hk] at h ⊢
        rcases lt_or_eq_of_le hJab with hlt | heq
        · left; linarith
        · right; exact ⟨by rw [h, heq], h'⟩
  · norm_num
  · exact le_rfl

/-- The virtual valuation is measurable. -/
theorem oa_measurable_virtualValue (D : TypeDensity) : Measurable D.virtualValue :=
  measurable_id.sub (((continuous_const.sub D.continuous_cdf).measurable).div D.measurable_dens)

/-- The virtual valuation has an expectation: `Jφ = θφ - (1 - Φ)` on `[θ̲, θ̄]`. -/
theorem oa_integrable_virtualValue (D : TypeDensity) : Integrable D.virtualValue D.measure :=
  mss_integrable_of_mul_dens D (h := fun x => x * D.dens x - (1 - D.cdf x))
    ((mss_ii_mul_dens D continuous_id _ _).sub
      ((continuous_const.sub D.continuous_cdf).intervalIntegrable _ _)) fun x hx => by
      have := (D.dens_pos x hx).ne'
      simp only [TypeDensity.virtualValue]
      rw [sub_mul, div_mul_cancel₀ _ this]

/-- The rule is measurable. -/
theorem oaRule_measurable {n : ℕ} (D : Fin n → TypeDensity) (i : Fin n) :
    Measurable fun θ => oaRule D θ i := by
  classical
  have hJ : ∀ k, Measurable fun θ : Fin n → ℝ => (D k).virtualValue (θ k) := fun k =>
    (oa_measurable_virtualValue (D k)).comp (measurable_pi_apply k)
  refine Measurable.ite ?_ measurable_const measurable_const
  refine measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1
    (measurableSet_lt measurable_const (hJ i))) (Measurable.forall fun k => Measurable.or
      (measurableSet_setOfPred.1 (measurableSet_lt (hJ k) (hJ i)))
      (Measurable.and (measurableSet_setOfPred.1 (measurableSet_eq_fun (hJ k) (hJ i)))
        measurable_const)))

/-- **Example 23.F.2** (MWG, pp. 904-905) for general densities: suppose every virtual valuation
`Jᵢ(θᵢ) = θᵢ - (1 - Φᵢ(θᵢ))/φᵢ(θᵢ)` is nondecreasing on `[θ̲ᵢ, θ̄ᵢ]`. Then the rule (23.F.9)
(`oaRule`, ties to the lowest index) completed by the transfers
`tᵢ(θ) = Uᵢ(θᵢ) - θᵢȳᵢ(θᵢ)`, `Uᵢ(θᵢ) = ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ` (constraint (iii) with `Uᵢ(θ̲ᵢ) = 0`), is
a feasible mechanism (constraints (i)-(iv)), it solves the relaxed problem (23.F.8) at every
profile, and it maximises the seller's expected revenue among all feasible social choice
functions. -/
theorem example_23_F_2_general {n : ℕ} (D : Fin n → TypeDensity)
    (hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi)) :
    OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) ∧
      (∀ i, interimU (Measure.pi fun j => (D j).measure) allocV (oaRule D)
        (ecTransfer D (oaRule D) 0) i (D i).lo = 0) ∧
      (∀ θ, PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (oaRule D θ)) ∧
      ∀ y t, OptAuctionFeasible D y t →
        auctionRevenue D t ≤ auctionRevenue D (ecTransfer D (oaRule D) 0) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hy01 : ∀ θ i, 0 ≤ oaRule D θ i ∧ oaRule D θ i ≤ 1 := fun θ i => by
    simp only [oaRule]; split_ifs <;> norm_num
  have hyb : ∀ θ i, |oaRule D θ i| ≤ 1 := fun θ i => by
    rw [abs_le]; constructor <;> linarith [hy01 θ i]
  obtain ⟨hint, hbic, ht, hU⟩ := ec_mechanism D (oaRule_measurable D) hyb
    (fun i θ' a ha b hb hab => oaRule_mono D hJ i θ' ha hb hab) 0
  have hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV (oaRule D)
      (ecTransfer D (oaRule D) 0) i (D i).lo = 0 := fun i => by
    rw [hU, intervalIntegral.integral_same, Pi.zero_apply, add_zero]
  have hfeas : OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) := by
    refine ⟨fun θ _ => (oaRule_pointwiseOpt D θ).1, hint, hbic, ht, fun i => ?_,
      fun i x hx => ?_⟩
    · refine (integrable_comp_eval (μ := fun j => (D j).measure) (i := i)
        (oa_integrable_virtualValue (D i))).bdd_mul (c := 1)
        (oaRule_measurable D i).aestronglyMeasurable
        (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_eq_abs]; exact hyb θ i
    · rw [hU, Pi.zero_apply, zero_add]
      exact intervalIntegral.integral_nonneg hx.1 fun s _ =>
        integral_nonneg fun θ' => (hy01 _ i).1
  exact ⟨hfeas, hU0, oaRule_pointwiseOpt D, fun y t h =>
    example_23_F_2 D hfeas hU0 (fun θ _ => oaRule_pointwiseOpt D θ) h⟩

/-- **Example 23.F.2**, non-vacuity of `example_23_F_2_general`: two bidders uniform on `[0, 1]`
and `[0, 2]` (`J₁(θ) = 2θ - 1`, `J₂(θ) = 2θ - 2`, both nondecreasing): the completed rule is an
optimal auction. -/
theorem example_23_F_2_general_instance :
    let D : Fin 2 → TypeDensity := ![uniformDensity 0 1 zero_lt_one,
      uniformDensity 0 2 zero_lt_two]
    OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) ∧
      ∀ y t, OptAuctionFeasible D y t →
        auctionRevenue D t ≤ auctionRevenue D (ecTransfer D (oaRule D) 0) := by
  intro D
  have hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi) := by
    intro i
    fin_cases i
    · intro a ha b hb hab
      have ha' : a ∈ Set.Icc (0 : ℝ) 1 := ha
      have hb' : b ∈ Set.Icc (0 : ℝ) 1 := hb
      change (uniformDensity 0 1 zero_lt_one).virtualValue a ≤
        (uniformDensity 0 1 zero_lt_one).virtualValue b
      rw [oa_uniform_virtualValue _ ha', oa_uniform_virtualValue _ hb']; linarith
    · intro a ha b hb hab
      have ha' : a ∈ Set.Icc (0 : ℝ) 2 := ha
      have hb' : b ∈ Set.Icc (0 : ℝ) 2 := hb
      change (uniformDensity 0 2 zero_lt_two).virtualValue a ≤
        (uniformDensity 0 2 zero_lt_two).virtualValue b
      rw [oa_uniform_virtualValue _ ha', oa_uniform_virtualValue _ hb']; linarith
  obtain ⟨h1, -, -, h4⟩ := example_23_F_2_general D hJ
  exact ⟨h1, h4⟩

/-! ### Exercise 23.F.7: completing the virtual-welfare rule -/

/-- Exercise 23.F.7: the virtual welfare of market structure `y` at cost profile `θ`. -/
noncomputable def dsVW (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) (y : Bool × Bool) :
    ℝ :=
  dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) y

open Classical in
/-- **Exercise 23.F.7** (MWG, p. 924): the pointwise virtual-welfare rule, a maximiser of the
virtual welfare over the four market structures, ties broken in the fixed order duopoly,
monopoly of `false`, monopoly of `true`, no production. -/
noncomputable def dsRule (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) : Bool × Bool :=
  if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (true, true) then (true, true)
  else if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (true, false) then (true, false)
  else if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (false, true) then (false, true)
  else (false, false)

/-- The rule maximises virtual welfare at every profile. -/
theorem dsRule_max (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) (y : Bool × Bool) :
    dsVW D c lam θ y ≤ dsVW D c lam θ (dsRule D c lam θ) := by
  classical
  obtain ⟨m, hm⟩ := Finite.exists_max (dsVW D c lam θ)
  unfold dsRule
  split_ifs with h1 h2 h3
  · exact h1 y
  · exact h2 y
  · exact h3 y
  · rcases m with ⟨_ | _, _ | _⟩
    · exact hm y
    · exact absurd hm h3
    · exact absurd hm h2
    · exact absurd hm h1

/-- The virtual cost is measurable. -/
theorem ds_measurable_virtualCost (D : TypeDensity) (lam : ℝ) :
    Measurable (dsVirtualCost D lam) :=
  (measurable_const.mul measurable_id).add
    (measurable_const.mul (D.continuous_cdf.measurable.div D.measurable_dens))

/-- The rule is measurable. -/
theorem dsRule_measurable (D : Bool → TypeDensity) (c lam : ℝ) :
    Measurable (dsRule D c lam) := by
  classical
  have hvc : ∀ j, Measurable fun θ : Bool → ℝ => dsVirtualCost (D j) lam (θ j) := fun j =>
    (ds_measurable_virtualCost (D j) lam).comp (measurable_pi_apply j)
  have hV : ∀ y, Measurable fun θ => dsVW D c lam θ y := by
    intro y
    have hf := hvc false
    have ht := hvc true
    rcases y with ⟨_ | _, _ | _⟩ <;>
      simp only [dsVW, dsVirtualWelfare, dsProduces, Bool.false_eq_true, ↓reduceIte] <;>
      fun_prop
  have hS : ∀ y0, MeasurableSet {θ : Bool → ℝ | ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ y0} :=
    fun y0 => measurableSet_setOfPred.2 (Measurable.forall fun y =>
      measurableSet_setOfPred.1 (measurableSet_le (hV y) (hV y0)))
  exact Measurable.ite (hS _) measurable_const (Measurable.ite (hS _) measurable_const
    (Measurable.ite (hS _) measurable_const measurable_const))

/-- Lowering firm `j`'s virtual cost (the other's unchanged) raises the virtual welfare of every
structure in which `j` produces by the difference, and leaves the others unchanged. -/
theorem ds_vw_shift (c lam : ℝ) {vc vc' : Bool → ℝ} {j : Bool} (hother : vc' (!j) = vc (!j))
    (y : Bool × Bool) :
    dsVirtualWelfare c lam vc' y =
      dsVirtualWelfare c lam vc y + if dsProduces y j then vc j - vc' j else 0 := by
  cases j <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
    rcases y with ⟨_ | _, _ | _⟩ <;>
    simp [dsVirtualWelfare, dsProduces, hother] <;> ring

/-- **Exercise 23.F.7** (MWG, p. 924): with `λ > 1` and `Φⱼ/φⱼ` nondecreasing, the rule awards
production rights to firm `j` at cost `a` whenever it does at a higher cost `b ≥ a` (the other
firm's cost unchanged): `xⱼ` is nonincreasing in `θⱼ`. -/
theorem dsRule_mono (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : ∀ j, MonotoneOn (fun θ => (D j).cdf θ / (D j).dens θ)
      (Set.Icc (D j).lo (D j).hi)) (j : Bool) (θ' : Bool → ℝ) {a b : ℝ}
    (ha : a ∈ Set.Icc (D j).lo (D j).hi) (hb : b ∈ Set.Icc (D j).lo (D j).hi) (hab : a ≤ b) :
    dsX (dsRule D c lam (update θ' j b)) j ≤ dsX (dsRule D c lam (update θ' j a)) j := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · set yA := dsRule D c lam (update θ' j a)
    set yB := dsRule D c lam (update θ' j b)
    have hvc := dsVirtualCost_strictMono (D j) hlam (hΦ j) ha hb hlt
    have hother : (fun k => dsVirtualCost (D k) lam (update θ' j a k)) (!j) =
        (fun k => dsVirtualCost (D k) lam (update θ' j b k)) (!j) := by
      have hne : (!j) ≠ j := by cases j <;> simp
      simp only [update_of_ne hne]
    have hsh := fun y => ds_vw_shift c lam (vc := fun k => dsVirtualCost (D k) lam
      (update θ' j b k)) (vc' := fun k => dsVirtualCost (D k) lam (update θ' j a k)) hother y
    simp only [update_self] at hsh
    have hA : dsVW D c lam (update θ' j a) yB ≤ dsVW D c lam (update θ' j a) yA :=
      dsRule_max D c lam (update θ' j a) yB
    have hB : dsVW D c lam (update θ' j b) yA ≤ dsVW D c lam (update θ' j b) yB :=
      dsRule_max D c lam (update θ' j b) yA
    simp only [dsVW] at hA hB
    rw [hsh yA, hsh yB] at hA
    simp only [dsX]
    by_cases h1 : dsProduces yB j = true
    · by_cases h2 : dsProduces yA j = true
      · simp [h1, h2]
      · exfalso
        have h2' : dsProduces yA j = false := by simpa using h2
        rw [h1, h2'] at hA
        simp only [ite_true, Bool.false_eq_true, ite_false, add_zero] at hA
        linarith
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> norm_num
  · rw [heq]

/-- **Exercise 23.F.7** (MWG, p. 924): the transfers from the firms completing `dsRule`,
`tⱼ(θ) = πᶜⱼ - τⱼ(θⱼ)` with `τⱼ` the envelope transfers normalised so that `Uⱼ(θ̄ⱼ) = 0`. -/
noncomputable def dsRuleT (D : Bool → TypeDensity) (c lam : ℝ) : (Bool → ℝ) → Bool → ℝ :=
  fun θ j => dsGross c (dsRule D c lam θ) j -
    ecTransfer D (dsAlloc (dsRule D c lam)) (fun i => -∫ s in (D i).lo..(D i).hi,
      interimBenefit (Measure.pi fun l => (D l).measure) allocV (dsAlloc (dsRule D c lam)) i s)
      θ j

/-- **Exercise 23.F.7** (MWG, p. 924), the optimal auction of production rights for general
densities. Let `λ > 1` and `Φⱼ/φⱼ` be nondecreasing for both firms (MWG: increasing). The
pointwise virtual-welfare rule `dsRule` completed by the envelope transfers `dsRuleT` is a
feasible mechanism (Bayesian incentive compatible, interim individually rational, expectations
existing), leaves each firm's highest-cost type with `Uⱼ(θ̄ⱼ) = 0`, and maximises the planner's
expected welfare `E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ]` among all feasible mechanisms. -/
theorem exercise_23_F_7_general (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : ∀ j, MonotoneOn (fun θ => (D j).cdf θ / (D j).dens θ)
      (Set.Icc (D j).lo (D j).hi)) :
    DSFeasible D c (dsRule D c lam) (dsRuleT D c lam) ∧
      (∀ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc (dsRule D c lam))
        (dsTau c (dsRule D c lam) (dsRuleT D c lam)) j (D j).hi = 0) ∧
      ∀ k t, DSFeasible D c k t →
        ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) ≤
          ∫ θ, dsWelfare c lam (dsRule D c lam θ) θ (dsRuleT D c lam θ)
            ∂Measure.pi (fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set P := Measure.pi fun i => (D i).measure with hP
  set ks := dsRule D c lam with hks
  set y := dsAlloc ks with hy
  set cst : Bool → ℝ := fun i => -∫ s in (D i).lo..(D i).hi, interimBenefit P allocV y i s
    with hcst
  have hkm : Measurable ks := dsRule_measurable D c lam
  have hym : ∀ j, Measurable fun θ => y θ j := fun j =>
    ((measurable_of_finite fun z => dsX z j).comp hkm).neg
  have hyb : ∀ θ j, |y θ j| ≤ 1 := fun θ j => by
    simp only [hy, dsAlloc, abs_neg]
    rw [abs_le]; constructor <;> linarith [ds_x_mem (ks θ) j]
  have hmono : ∀ j θ', ∀ a ∈ Set.Icc (D j).lo (D j).hi, ∀ b ∈ Set.Icc (D j).lo (D j).hi,
      a ≤ b → y (update θ' j a) j ≤ y (update θ' j b) j := fun j θ' a ha b hb hab => by
    simp only [hy, dsAlloc, neg_le_neg_iff]
    exact dsRule_mono D c hlam hΦ j θ' ha hb hab
  obtain ⟨hint, hbic, ht, hU⟩ := ec_mechanism D hym hyb hmono cst
  have htau : dsTau c ks (dsRuleT D c lam) = ecTransfer D y cst := by
    funext θ j
    simp only [dsTau, dsRuleT, hks, hy, hcst, hP]
    ring
  have hmon := ec_interimBenefit_mono D hym hyb hmono
  have hii : ∀ j, ∀ a ∈ Set.Icc (D j).lo (D j).hi, ∀ b ∈ Set.Icc (D j).lo (D j).hi,
      IntervalIntegrable (interimBenefit P allocV y j) volume a b := fun j a ha b hb =>
    ((hmon j).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hUx : ∀ j x, x ∈ Set.Icc (D j).lo (D j).hi →
      interimU P allocV y (ecTransfer D y cst) j x =
        -∫ s in x..(D j).hi, interimBenefit P allocV y j s := by
    intro j x hx
    have hlo : (D j).lo ∈ Set.Icc (D j).lo (D j).hi := ⟨le_rfl, (D j).lo_lt_hi.le⟩
    have hhi : (D j).hi ∈ Set.Icc (D j).lo (D j).hi := ⟨(D j).lo_lt_hi.le, le_rfl⟩
    rw [hU]
    change -(∫ s in (D j).lo..(D j).hi, interimBenefit P allocV y j s) +
      (∫ s in (D j).lo..x, interimBenefit P allocV y j s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii j _ hlo _ hx)
      (hii j _ hx _ hhi)]
    ring
  have hy0 : ∀ j s, interimBenefit P allocV y j s ≤ 0 := fun j s =>
    integral_nonpos fun θ' => by
      simp only [allocV, hy, dsAlloc, Pi.zero_apply]
      linarith [(ds_x_mem (ks (update θ' j s)) j).1]
  have hfeas : DSFeasible D c ks (dsRuleT D c lam) := by
    refine ⟨hkm, fun j => ?_, ?_, ?_, fun j x hx => ?_⟩
    · exact ((ds_integrable_comp D hkm fun z => dsGross c z j).sub (ht j)).congr
        (Filter.Eventually.of_forall fun θ => rfl)
    · rw [htau]; exact hint
    · rw [htau]; exact hbic
    · rw [htau, hUx j x hx, neg_nonneg]
      have := intervalIntegral.integral_nonneg (μ := volume) hx.2 fun s _ =>
        neg_nonneg.2 (hy0 j s)
      rw [intervalIntegral.integral_neg] at this
      linarith
  have hUhi : ∀ j, interimU P allocV (dsAlloc ks) (dsTau c ks (dsRuleT D c lam)) j
      (D j).hi = 0 := fun j => by
    rw [htau, hUx j _ ⟨(D j).lo_lt_hi.le, le_rfl⟩, intervalIntegral.integral_same, neg_zero]
  exact ⟨hfeas, hUhi, fun k t h => exercise_23_F_7_optimal D c hlam hfeas hUhi
    (fun θ _ y' => dsRule_max D c lam θ y') h⟩

/-- **Exercise 23.F.7**, non-vacuity of `exercise_23_F_7_general`: fixed costs uniform on
`[0, 1/100]` have `Φ/φ = θ`, nondecreasing; with `c = 0`, `λ = 2` the completed rule is optimal. -/
theorem exercise_23_F_7_general_instance :
    DSFeasible (fun _ => dsUnif) 0 (dsRule (fun _ => dsUnif) 0 2)
        (dsRuleT (fun _ => dsUnif) 0 2) ∧
      ∀ k t, DSFeasible (fun _ => dsUnif) 0 k t →
        ∫ θ, dsWelfare 0 2 (k θ) θ (t θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) ≤
          ∫ θ, dsWelfare 0 2 (dsRule (fun _ => dsUnif) 0 2 θ) θ
            (dsRuleT (fun _ => dsUnif) 0 2 θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) := by
  have hΦ : ∀ j : Bool, MonotoneOn (fun θ => ((fun _ => dsUnif) j).cdf θ /
      ((fun _ => dsUnif) j).dens θ) (Set.Icc ((fun _ => dsUnif) j).lo
        ((fun _ => dsUnif) j).hi) := by
    intro j
    have hr : ∀ x ∈ Set.Icc dsUnif.lo dsUnif.hi, dsUnif.cdf x / dsUnif.dens x = x := by
      intro x hx
      have hd : dsUnif.dens x = (1 / 100 - 0 : ℝ)⁻¹ := by
        change (Set.Icc (0 : ℝ) (1 / 100)).indicator (fun _ => (1 / 100 - 0 : ℝ)⁻¹) x = _
        exact Set.indicator_of_mem hx _
      have hc : dsUnif.cdf x = (x - 0) / (1 / 100 - 0) := oa_uniform_cdf (by norm_num) hx
      rw [hd, hc]
      field_simp
      ring
    intro a ha b hb hab
    simp only at ha hb ⊢
    rw [hr a ha, hr b hb]
    exact hab
  obtain ⟨h1, -, h3⟩ := exercise_23_F_7_general (fun _ => dsUnif) 0 (by norm_num : (1 : ℝ) < 2)
    hΦ
  exact ⟨h1, h3⟩

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Example 23.F.1: interiority and the first-best contract

MWG, Section 23.F, Example 23.F.1 (pp. 900-903), footnote 48 (p. 902), and the parenthetical
claim of Exercise 23.F.1 (p. 923).

* **Footnote 48** (`footnote_23_48`): "under our assumptions, the optimal contract is interior,
  that is, has `e(θ) > 0` for (almost) all `θ`". If a feasible contract solving the relaxed
  problem pointwise exists (the hypotheses of `example_23_F_1`), every optimal feasible contract
  `(e, t)` has `e(θ) > 0` for almost every type: an optimal `e(θ)` maximises `v(e) + g(e)J(θ)`
  for almost every `θ`, and `0` never does, because the derivative there is
  `v'(0) + g'(0)J(θ) = v'(0) > 0`. Instance: the uniform example of `example_23_F_1_instance`
  (`footnote_23_48_instance`).
* **Exercise 23.F.1**, parenthetical claim about Example 23.F.1: the first-best effort `e*(θ)`
  with the agent as residual claimant, `t(θ) = v(e*(θ)) - (v(e*(θ̲)) + θ̲g(e*(θ̲))) + ū`, is ex
  post classically efficient, Bayesian incentive compatible and individually rational
  (`exercise_23_F_1_firstBest`); in the uniform instance it is incentive feasible in the full
  sense of `OCFeasible`, while the optimal (interim incentive efficient) contract is not ex post
  efficient at `θ = -2` (`exercise_23_F_1_example`).
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Footnote 48** (MWG, p. 902). Suppose `v'(0) > 0` and `g'(0) = 0`, and a feasible contract
`(e*, t*)` with `U*(θ̲) = ū` solves the relaxed problem pointwise (so it is optimal,
`example_23_F_1`). Then every optimal feasible contract `(e, t)` (expected payoff at least that
of `(e*, t*)`) is interior: `e(θ) > 0` for almost every type `θ`. -/
theorem footnote_23_48 (D : TypeDensity) {v g : ℝ → ℝ} {v0 g0 ubar : ℝ}
    (hv : HasDerivAt v v0 0) (hg : HasDerivAt g g0 0) (hg0 : g0 = 0) (hv0 : 0 < v0)
    {es ts : ℝ → ℝ} (hs : OCFeasible D v g ubar es ts) (hU : ocU g es ts D.lo = ubar)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * D.virtualValue θ) (es θ))
    {e t : ℝ → ℝ} (h : OCFeasible D v g ubar e t) (hopt : ocPayoff D v es ts ≤ ocPayoff D v e t) :
    ∀ᵐ θ ∂D.measure, 0 < e θ := by
  have := D.isProbabilityMeasure
  obtain ⟨he, hIC, hIR, hvi, ht, hθg, hgr⟩ := h
  obtain ⟨-, hIC', -, hvi', ht', hθg', hgr'⟩ := hs
  rw [eq_23_F_4 D hIC hvi ht hθg hgr, eq_23_F_4 D hIC' hvi' ht' hθg' hgr', hU] at hopt
  have hlo := hIR D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
  have iE := oc_integrable_vJ D hvi hθg hgr
  have iS := oc_integrable_vJ D hvi' hθg' hgr'
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have hnn : 0 ≤ᵐ[D.measure] fun θ => (v (es θ) + g (es θ) * D.virtualValue θ) -
      (v (e θ) + g (e θ) * D.virtualValue θ) := by
    filter_upwards [hae] with θ hθ
    exact sub_nonneg.2 ((hmax θ hθ).2 (e θ) (he θ))
  have hint0 : ∫ θ, ((v (es θ) + g (es θ) * D.virtualValue θ) -
      (v (e θ) + g (e θ) * D.virtualValue θ)) ∂D.measure = 0 := by
    rw [integral_sub iS iE]
    have := integral_nonneg_of_ae hnn
    rw [integral_sub iS iE] at this
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (iS.sub iE)).1 hint0
  filter_upwards [hz, hae] with θ hθ hθm
  simp only [Pi.zero_apply, sub_eq_zero] at hθ
  have hargmax : OCArgmax (fun x => v x + g x * D.virtualValue θ) (e θ) :=
    ⟨he θ, fun x hx => by
      have := (hmax θ hθm).2 x hx
      simp only at this ⊢
      linarith⟩
  have hd : HasDerivAt (fun x => v x + g x * D.virtualValue θ)
      (v0 + g0 * D.virtualValue θ) 0 := hv.add (hg.mul_const _)
  rcases lt_or_eq_of_le (he θ) with hpos | hzero
  · exact hpos
  · exfalso
    rw [← hzero] at hargmax
    exact oc_not_argmax_zero hd (by rw [hg0, zero_mul, add_zero]; exact hv0) hargmax

/-- The uniform instance of Example 23.F.1 solves the relaxed problem pointwise: for `θ ∈ [-2, -1]`,
`e(θ) = 1/(2|θ|)` maximises `v(e) + g(e)J(θ) = 2e - e² + e²(2θ + 1)` over `e ≥ 0`. -/
theorem oc_instance_argmax {θ : ℝ}
    (hθ : θ ∈ Set.Icc (uniformDensity (-2) (-1) (by norm_num)).lo
      (uniformDensity (-2) (-1) (by norm_num)).hi) :
    OCArgmax (fun x => (2 * x - x ^ 2) + x ^ 2 *
      (uniformDensity (-2) (-1) (by norm_num)).virtualValue θ) (1 / (2 * |θ|)) := by
  have hθ' : θ ∈ Set.Icc (-2 : ℝ) (-1) := hθ
  have hθ0 : θ < 0 := by linarith [hθ'.2]
  have hJ : (uniformDensity (-2) (-1) (by norm_num)).virtualValue θ = 2 * θ + 1 := by
    have h := oa_uniform_virtualValue (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    exact h.trans (by ring)
  have he : 2 * -θ * (1 / (2 * |θ|)) = 1 := by
    rw [abs_of_neg hθ0]; have := hθ0.ne; field_simp
  refine ⟨by positivity, fun x _ => ?_⟩
  simp only [hJ]
  have key : (2 * (1 / (2 * |θ|)) - (1 / (2 * |θ|)) ^ 2 + (1 / (2 * |θ|)) ^ 2 * (2 * θ + 1)) -
      (2 * x - x ^ 2 + x ^ 2 * (2 * θ + 1)) = 2 * (-θ) * (x - 1 / (2 * |θ|)) ^ 2 := by
    linear_combination (2 * (x - 1 / (2 * |θ|))) * he
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ -θ))
    (sq_nonneg (x - 1 / (2 * |θ|)))
  linarith

/-- **Footnote 48** (MWG, p. 902), instance: in the uniform example (types uniform on
`[-2, -1]`, `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`; `v'(0) = 2 > 0`, `g'(0) = 0`), every optimal
feasible contract has `e(θ) > 0` for almost every type. -/
theorem footnote_23_48_instance {e t : ℝ → ℝ}
    (h : OCFeasible (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2)
      (fun e => e ^ 2) 0 e t)
    (hopt : ∀ e' t', OCFeasible (uniformDensity (-2) (-1) (by norm_num))
      (fun e => 2 * e - e ^ 2) (fun e => e ^ 2) 0 e' t' →
      ocPayoff (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2) e' t' ≤
        ocPayoff (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2) e t) :
    ∀ᵐ θ ∂(uniformDensity (-2) (-1) (by norm_num)).measure, 0 < e θ := by
  obtain ⟨hs, hU, -⟩ := example_23_F_1_instance
  have hv : HasDerivAt (fun e : ℝ => 2 * e - e ^ 2) 2 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul 2).sub (hasDerivAt_pow 2 (0 : ℝ))).congr_deriv
      (by norm_num)
  have hg : HasDerivAt (fun e : ℝ => e ^ 2) 0 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).congr_deriv (by norm_num)
  exact footnote_23_48 _ hv hg rfl (by norm_num) hs hU (fun θ hθ => oc_instance_argmax hθ) h
    (hopt _ _ hs)

/-! ### Exercise 23.F.1: the first-best contract in Example 23.F.1 -/

/-- **Exercise 23.F.1** (MWG, p. 923), claim about Example 23.F.1. Let `e*(θ)` be the first-best
effort, maximising `v(e) + θg(e)` over `e ≥ 0` for every `θ ∈ [θ̲, θ̄]`, with `g ≥ 0` on
`e ≥ 0`. Make the agent the residual claimant: `t(θ) = v(e*(θ)) - (v(e*(θ̲)) + θ̲g(e*(θ̲))) + ū`.
This social choice function is ex post classically efficient (the total surplus
`(v(e) - t) + (t + θg(e))` is maximal at every type), Bayesian incentive compatible and
individually rational: an ex post classically efficient social choice function is incentive
feasible. -/
theorem exercise_23_F_1_firstBest {v g ef : ℝ → ℝ} {lo hi ubar : ℝ} (hlohi : lo ≤ hi)
    (hg0 : ∀ x, 0 ≤ x → 0 ≤ g x)
    (hfb : ∀ θ ∈ Set.Icc lo hi, OCArgmax (fun x => v x + g x * θ) (ef θ)) :
    let t : ℝ → ℝ := fun θ => v (ef θ) - (v (ef lo) + lo * g (ef lo)) + ubar
    (∀ θ ∈ Set.Icc lo hi, ∀ x, 0 ≤ x → ∀ s : ℝ,
      (v x - s) + (s + θ * g x) ≤ (v (ef θ) - t θ) + (t θ + θ * g (ef θ))) ∧
      LinearIC (fun θ => g (ef θ)) t lo hi ∧ ∀ θ ∈ Set.Icc lo hi, ubar ≤ ocU g ef t θ := by
  intro t
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
  refine ⟨fun θ hθ x hx s => ?_, fun θ hθ θh hθh => ?_, fun θ hθ => ?_⟩
  · have := (hfb θ hθ).2 x hx
    simp only at this
    linarith
  · have := (hfb θ hθ).2 (ef θh) (hfb θh hθh).1
    simp only [t] at this ⊢
    linarith
  · have h1 := (hfb θ hθ).2 (ef lo) (hfb lo hlo).1
    have h2 : lo * g (ef lo) ≤ θ * g (ef lo) :=
      mul_le_mul_of_nonneg_right hθ.1 (hg0 _ (hfb lo hlo).1)
    simp only [ocU, t] at h1 ⊢
    linarith

/-- **Exercise 23.F.1** (MWG, p. 923), the parenthetical claim in the uniform instance of
Example 23.F.1 (types uniform on `[-2, -1]`, `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`): the
first-best contract `e*(θ) = 1/(1 - θ)` (written `1/(1 + |θ|)`) with the agent as residual
claimant is incentive feasible (`OCFeasible`) and ex post classically efficient, while the
optimal contract `e(θ) = 1/(2|θ|)` derived in the example is not ex post efficient: at `θ = -2`
its total surplus is strictly below the first best. -/
theorem exercise_23_F_1_example :
    let D := uniformDensity (-2) (-1) (by norm_num)
    let v : ℝ → ℝ := fun e => 2 * e - e ^ 2
    let g : ℝ → ℝ := fun e => e ^ 2
    let ef : ℝ → ℝ := fun θ => 1 / (1 + |θ|)
    let tf : ℝ → ℝ := fun θ => v (ef θ) - (v (ef D.lo) + D.lo * g (ef D.lo))
    OCFeasible D v g 0 ef tf ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, ∀ x, 0 ≤ x → v x + θ * g x ≤ v (ef θ) + θ * g (ef θ)) ∧
      v (1 / (2 * |(-2 : ℝ)|)) + (-2) * g (1 / (2 * |(-2 : ℝ)|)) <
        v (ef (-2)) + (-2) * g (ef (-2))
  := by
  intro D v g ef tf
  have hlo : D.lo = -2 := rfl
  have hhi : D.hi = -1 := rfl
  obtain ⟨-, -, -, hfb, -, -⟩ := example_23_F_1_instance
  have hefeq : ∀ θ ∈ Set.Icc D.lo D.hi, ef θ = 1 / (1 - θ) := by
    intro θ hθ
    rw [hlo, hhi] at hθ
    simp only [ef, abs_of_neg (by linarith [hθ.2] : θ < 0), sub_eq_add_neg]
  have hfb' : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * θ) (ef θ) :=
    fun θ hθ => by rw [hefeq θ hθ]; exact hfb θ hθ
  have hef : ∀ θ ∈ Set.Icc D.lo D.hi, 1 / 3 ≤ ef θ ∧ ef θ ≤ 1 / 2 := by
    intro θ hθ
    rw [hefeq θ hθ]
    rw [hlo, hhi] at hθ
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (by linarith [hθ.2])]; linarith [hθ.1]
    · rw [div_le_iff₀ (by linarith [hθ.2])]; linarith [hθ.2]
  have hefm : Measurable ef :=
    measurable_const.div (measurable_const.add continuous_abs.measurable)
  obtain ⟨_, hIC, hIR⟩ := exercise_23_F_1_firstBest (v := v) (g := g) (ubar := 0)
    D.lo_lt_hi.le (fun x _ => sq_nonneg x) hfb'
  have htf : tf = fun θ => v (ef θ) - (v (ef D.lo) + D.lo * g (ef D.lo)) + 0 := by
    funext θ; simp only [tf, add_zero]
  refine ⟨⟨fun θ => ?_, by rw [htf]; exact hIC, fun θ hθ => by rw [htf]; exact hIR θ hθ,
    oc_integrable_of_bound D ((measurable_const.mul hefm).sub (hefm.pow_const 2)) 2
      fun θ hθ => ?_,
    oc_integrable_of_bound D (((measurable_const.mul hefm).sub (hefm.pow_const 2)).sub
      measurable_const) 4 fun θ hθ => ?_,
    oc_integrable_of_bound D (measurable_id.mul (hefm.pow_const 2)) 2 fun θ hθ => ?_,
    oc_integrable_of_bound D ((hefm.pow_const 2).mul ((measurable_const.sub
      D.continuous_cdf.measurable).div D.measurable_dens)) 1 fun θ hθ => ?_⟩,
    fun θ hθ x hx => ?_, ?_⟩
  · simp only [ef]; positivity
  · obtain ⟨h1, h2⟩ := hef θ hθ
    simp only [v]
    rw [abs_le]; constructor <;> nlinarith
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have h3 := hef D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
    simp only [tf, v, g]
    rw [abs_le]; constructor <;> nlinarith [h3.1, h3.2]
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have := hθ; rw [hlo, hhi] at this
    simp only [g]
    rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have := hθ; rw [hlo, hhi] at this
    have hd : D.dens θ = ((-1) - (-2) : ℝ)⁻¹ := by
      change (Set.Icc (-2 : ℝ) (-1)).indicator (fun _ => ((-1) - (-2) : ℝ)⁻¹) θ = _
      exact Set.indicator_of_mem hθ _
    have hc := oa_uniform_cdf (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    have hr : (1 - D.cdf θ) / D.dens θ = -1 - θ := by
      change (1 - (uniformDensity (-2) (-1) (by norm_num)).cdf θ) / D.dens θ = _
      rw [hc, hd]; norm_num; ring
    simp only [g]
    rw [hr, abs_le]; constructor <;> nlinarith [this.1, this.2]
  · have := (hfb' θ hθ).2 x hx
    simp only at this
    linarith
  · simp only [v, g, ef]
    norm_num

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 23.F.1 for general type spaces

MWG, Exercise 23.F.1 (p. 923), the ex ante part, for arbitrary measurable type spaces (not only
finite ones, as in `exercise_23_F_1_exAnte`).

Ex ante utilities `Uᵢ(g) = E[Uᵢ(θᵢ | g)]` are only defined when the expectations exist; with
infinite type spaces we therefore compare `f` with the incentive feasible social choice
functions whose ex post utilities `θ ↦ uᵢ(g(θ), θᵢ)` are measurable and integrable
(`WcRegular`), as in Example 23.F.2 (`OptAuctionFeasible`).

* `wc_exAnteU_eq_general`: with independent types, `Uᵢ(g) = E_θ[uᵢ(g(θ), θᵢ)]` for such `g`.
* `exercise_23_F_1_exAnte_general`: in the quasilinear setting with independent types, an
  `f ∈ F*` with integrable utilities that is ex post classically efficient in `F_IR` (closed
  under ex post improvements) is ex ante efficient in `F* ∩ WcRegular`.
* `exercise_23_F_1_exAnte_general_instance`: non-vacuity with a continuum of types (one agent,
  type uniform on `[0, 1]`).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
  {X : Type*}

/-- **Exercise 23.F.1** (MWG, p. 923): social choice functions whose ex post utilities
`θ ↦ uᵢ(g(θ), θᵢ)` are measurable and integrable under the prior `∏ᵢ μᵢ`, so that their ex ante
utilities exist. -/
def WcRegular (μ : (i : ι) → Measure (Θ i)) (u : (i : ι) → X → Θ i → ℝ) :
    Set (((i : ι) → Θ i) → X) :=
  {g | ∀ i, Measurable (fun θ => u i (g θ) (θ i)) ∧
    Integrable (fun θ => u i (g θ) (θ i)) (Measure.pi μ)}

/-- With independent types, the ex ante utility of a social choice function with measurable,
integrable utilities is the expectation of its ex post utility: `Uᵢ(g) = E_θ[uᵢ(g(θ), θᵢ)]`
(MWG, p. 893), for arbitrary measurable type spaces. -/
theorem wc_exAnteU_eq_general (μ : (i : ι) → Measure (Θ i)) [∀ i, IsProbabilityMeasure (μ i)]
    (u : (i : ι) → X → Θ i → ℝ) {g : ((i : ι) → Θ i) → X} (hg : g ∈ WcRegular μ u) (i : ι) :
    scfExAnteU μ (indepBeliefs (Measure.pi μ)) u g i = ∫ θ, u i (g θ) (θ i) ∂Measure.pi μ := by
  obtain ⟨hm, hi⟩ := hg i
  set h : ((j : ι) → Θ j) → ℝ := fun θ => u i (g θ) (θ i) with hh
  have e : ∀ (x : Θ i) (θ' : (j : ι) → Θ j), u i (g (update θ' i x)) x = h (update θ' i x) := by
    intro x θ'; simp [hh]
  have hF : StronglyMeasurable fun x : Θ i => ∫ θ', h (update θ' i x) ∂Measure.pi μ := by
    refine StronglyMeasurable.integral_prod_right (f := fun x θ' => h (update θ' i x)) ?_
    exact (hm.comp (measurable_update'.comp measurable_swap)).stronglyMeasurable
  have h1 := integral_integral_update μ i hi
  have h2 := integral_eval_pi μ i hF.aestronglyMeasurable
  rw [scfExAnteU]
  simp only [scfInterimU, indepBeliefs, e]
  rw [← h2, h1]

/-- **Exercise 23.F.1** (MWG, p. 923), ex ante part, for general type spaces. Quasilinear
setting, independent types `θ ~ ∏ᵢ μᵢ` on arbitrary measurable type spaces: if `f ∈ F*` has
measurable, integrable utilities and is ex post classically efficient in `F_IR` (with `F_IR`
closed under ex post improvements), then `f` is ex ante efficient among the incentive feasible
social choice functions whose ex ante utilities exist. -/
theorem exercise_23_F_1_exAnte_general {K : Type*} [Nonempty ι] (μ : (i : ι) → Measure (Θ i))
    [∀ i, IsProbabilityMeasure (μ i)] {v : (i : ι) → K → Θ i → ℝ} {m : ι → ℝ}
    {FIR : Set (((i : ι) → Θ i) → QLAlt ι K)}
    (hup : UpClosed (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    {f : ((i : ι) → Θ i) → QLAlt ι K}
    (hfF : f ∈ incentiveFeasible (indepBeliefs (Measure.pi μ))
      (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR)
    (hfr : f ∈ WcRegular μ (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi))
    (hf : ExPostEfficientIn (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR f) :
    ExAnteEfficientIn μ (indepBeliefs (Measure.pi μ))
      (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi)
      (incentiveFeasible (indepBeliefs (Measure.pi μ))
        (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) FIR ∩
        WcRegular μ (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi)) f := by
  refine ⟨⟨hfF, hfr⟩, ?_⟩
  rintro ⟨g, ⟨-, hgr⟩, hge, i, hi⟩
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hge j) ⟨i, Finset.mem_univ i, hi⟩
  simp only [wc_exAnteU_eq_general μ _ hfr, wc_exAnteU_eq_general μ _ hgr] at hsum
  rw [← integral_finsetSum _ fun j _ => (hfr j).2,
    ← integral_finsetSum _ fun j _ => (hgr j).2] at hsum
  have hle := integral_mono (μ := Measure.pi μ) (integrable_finsetSum _ fun j _ => (hgr j).2)
    (integrable_finsetSum _ fun j _ => (hfr j).2)
    fun θ => wc_sum_le_of_exPostEfficientIn hup hf g θ
  exact absurd hsum (not_lt.2 hle)

/-- **Exercise 23.F.1**, non-vacuity of `exercise_23_F_1_exAnte_general` with a continuum of
types: one agent with type uniform on `[0, 1]`, one project (`K = Unit`, `v = 0`, `m = 0`), no
participation constraint (`F_IR` = all social choice functions); the zero-transfer rule is
incentive feasible, has integrable utilities, is ex post classically efficient, and hence ex
ante incentive efficient. -/
theorem exercise_23_F_1_exAnte_general_instance :
    let u : (i : Unit) → QLAlt Unit Unit → ℝ → ℝ :=
      fun i x θi => qlU (Θ := fun _ => ℝ) (fun _ _ _ => 0) (fun _ => 0) i x.1 θi
    let f : (Unit → ℝ) → QLAlt Unit Unit := fun _ => ⟨((), fun _ => 0), by simp⟩
    ExAnteEfficientIn (Θ := fun _ => ℝ) (fun _ => uniform01.measure)
      (indepBeliefs (Measure.pi fun _ => uniform01.measure)) u
      (incentiveFeasible (indepBeliefs (Measure.pi fun _ => uniform01.measure)) u Set.univ ∩
        WcRegular (Θ := fun _ => ℝ) (fun _ => uniform01.measure) u) f := by
  intro u f
  have := uniform01.isProbabilityMeasure
  have hfu : ∀ i θ, u i (f θ) (θ i) = 0 := fun i θ => by simp [u, f, qlU]
  refine exercise_23_F_1_exAnte_general (Θ := fun _ => ℝ) (fun _ => uniform01.measure)
    (fun _ _ _ _ => Set.mem_univ _) ⟨fun i θi θh => le_rfl, Set.mem_univ _⟩
    (fun i => ?_) ⟨Set.mem_univ _, ?_⟩
  · have e : (fun θ : Unit → ℝ => u i (f θ) (θ i)) = fun _ => 0 := funext fun θ => hfu i θ
    change Measurable (fun θ : Unit → ℝ => u i (f θ) (θ i)) ∧
      Integrable (fun θ : Unit → ℝ => u i (f θ) (θ i)) (Measure.pi fun _ => uniform01.measure)
    rw [e]
    exact ⟨measurable_const, integrable_const _⟩
  · rintro ⟨g, -, -, i, θ, hlt⟩
    cases i
    change u () (f θ) (θ ()) < (0 : ℝ) + (0 + (g θ).1.2 ()) at hlt
    rw [hfu] at hlt
    have hg : (g θ).1.2 () ≤ 0 := by simpa using (g θ).2
    linarith

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 23.E.5: existence of a market-clearing price

MWG, Exercise 23.E.5 (p. 922). A continuum of sellers, of total mass `m_S ≥ 0`, with valuations
distributed on `[θ̲₁, θ̄₁]` with density `φ₁ > 0`, and a continuum of buyers, of mass `m_B ≥ 0`,
with valuations distributed on `[θ̲₂, θ̄₂]` with density `φ₂ > 0`. Parts (a)-(b)
(`exercise_23_E_5a`, `exercise_23_E_5b`) take a market-clearing price as given; here it is
shown to exist.

* `cp_measureReal_Iic`: `μ((-∞, p]) = Φ(max(θ̲, min(p, θ̄)))` for every `p`, a continuous function
  of `p`.
* `exercise_23_E_5_clearing`: there is a price `p ∈ [min(θ̲₁, θ̲₂), max(θ̄₁, θ̄₂)]` at which the
  mass of sellers with valuation below `p`, `m_SΦ₁(p)`, equals the mass of buyers with valuation
  above `p`, `m_B(1 - Φ₂(p))` (intermediate value theorem: supply minus demand is continuous,
  `-m_B ≤ 0` at the bottom and `m_S ≥ 0` at the top).
* `exercise_23_E_5_competitive`: hence the competitive mechanism of part (b) exists: at that
  price it is dominant strategy incentive compatible, individually rational and balances the
  budget.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- `μ((-∞, p]) = Φ(max(θ̲, min(p, θ̄)))` for every `p ∈ ℝ`. -/
theorem cp_measureReal_Iic (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Iic p) = D.cdf (max D.lo (min p D.hi)) := by
  have := D.isProbabilityMeasure
  have hle := D.lo_lt_hi.le
  rcases lt_or_ge p D.lo with hp | hp
  · rw [min_eq_left (by linarith), max_eq_left hp.le]
    have h0 : D.measure (Set.Iic p) = 0 := measure_mono_null (fun x hx => fun hx' =>
      absurd (lt_of_le_of_lt (Set.mem_Iic.1 hx) hp) (not_lt.2 hx'.1)) D.measure_compl_Icc
    simp [measureReal_def, h0, TypeDensity.cdf]
  · rcases le_or_gt p D.hi with hp' | hp'
    · rw [min_eq_left hp', max_eq_right hp]
      exact D.measureReal_Iic ⟨hp, hp'⟩
    · rw [min_eq_right hp'.le, max_eq_right hle]
      have h1 : D.measure (Set.Iic p)ᶜ = 0 := measure_mono_null (fun x hx => fun hx' =>
        hx (Set.mem_Iic.2 (hx'.2.trans hp'.le))) D.measure_compl_Icc
      rw [prob_compl_eq_zero_iff measurableSet_Iic] at h1
      simp [measureReal_def, h1, TypeDensity.cdf, D.integral_dens]

/-- `μ((-∞, p)) = Φ(max(θ̲, min(p, θ̄)))` (no atoms). -/
theorem cp_measureReal_Iio (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Iio p) = D.cdf (max D.lo (min p D.hi)) := by
  rw [measureReal_congr (Iio_ae_eq_Iic' (D.measure_singleton p)), cp_measureReal_Iic]

/-- `μ((p, ∞)) = 1 - Φ(max(θ̲, min(p, θ̄)))`. -/
theorem cp_measureReal_Ioi (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Ioi p) = 1 - D.cdf (max D.lo (min p D.hi)) := by
  have := D.isProbabilityMeasure
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, cp_measureReal_Iic]

/-- The measure of a set under `c • μ`, `c = ofReal m` with `m ≥ 0`, is `m μ(s)`. -/
theorem cp_smul_real {m : ℝ} (hm : 0 ≤ m) (μ : Measure ℝ) (s : Set ℝ) :
    ((ENNReal.ofReal m) • μ).real s = m * μ.real s := by
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hm, measureReal_def]

/-- `Φ(θ̲) = 0` and `Φ(θ̄) = 1`. -/
theorem cp_cdf_lo_hi (D : TypeDensity) : D.cdf D.lo = 0 ∧ D.cdf D.hi = 1 :=
  ⟨intervalIntegral.integral_same, D.integral_dens⟩

/-- **Exercise 23.E.5** (MWG, p. 922), existence of a market-clearing price. With sellers of
mass `m_S ≥ 0` whose valuations have density `φ₁ > 0` on `[θ̲₁, θ̄₁]` and buyers of mass
`m_B ≥ 0` whose valuations have density `φ₂ > 0` on `[θ̲₂, θ̄₂]`, there is a price
`p ∈ [min(θ̲₁, θ̲₂), max(θ̄₁, θ̄₂)]` at which the mass of sellers with valuation below `p` equals
the mass of buyers with valuation above `p`. -/
theorem exercise_23_E_5_clearing (D1 D2 : TypeDensity) {mS mB : ℝ} (hS : 0 ≤ mS)
    (hB : 0 ≤ mB) :
    ∃ p ∈ Set.Icc (min D1.lo D2.lo) (max D1.hi D2.hi),
      MarketClears ((ENNReal.ofReal mS) • D1.measure) ((ENNReal.ofReal mB) • D2.measure) p := by
  set F : ℝ → ℝ := fun p => mS * D1.cdf (max D1.lo (min p D1.hi)) -
    mB * (1 - D2.cdf (max D2.lo (min p D2.hi))) with hF
  have hc : Continuous F := by
    refine (continuous_const.mul (D1.continuous_cdf.comp ?_)).sub
      (continuous_const.mul (continuous_const.sub (D2.continuous_cdf.comp ?_)))
    · exact continuous_const.max (continuous_id.min continuous_const)
    · exact continuous_const.max (continuous_id.min continuous_const)
  set a := min D1.lo D2.lo
  set b := max D1.hi D2.hi
  have hab : a ≤ b := (min_le_left _ _).trans (D1.lo_lt_hi.le.trans (le_max_left _ _))
  have h1 := D1.lo_lt_hi.le
  have h2 := D2.lo_lt_hi.le
  have hFa : F a = -mB := by
    have e1 : max D1.lo (min a D1.hi) = D1.lo :=
      max_eq_left ((min_le_left _ _).trans (min_le_left _ _))
    have e2 : max D2.lo (min a D2.hi) = D2.lo :=
      max_eq_left ((min_le_left _ _).trans (min_le_right _ _))
    simp only [hF, e1, e2, (cp_cdf_lo_hi D1).1, (cp_cdf_lo_hi D2).1]
    ring
  have hFb : F b = mS := by
    have e1 : max D1.lo (min b D1.hi) = D1.hi := by
      rw [min_eq_right (le_max_left _ _), max_eq_right h1]
    have e2 : max D2.lo (min b D2.hi) = D2.hi := by
      rw [min_eq_right (le_max_right _ _), max_eq_right h2]
    simp only [hF, e1, e2, (cp_cdf_lo_hi D1).2, (cp_cdf_lo_hi D2).2]
    ring
  obtain ⟨p, hp, hp0⟩ := intermediate_value_Icc hab hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F a) (F b) by rw [hFa, hFb]; exact ⟨by linarith, hS⟩)
  refine ⟨p, hp, ?_⟩
  rw [MarketClears, cp_smul_real hS, cp_smul_real hB, cp_measureReal_Iio, cp_measureReal_Ioi]
  simp only [hF] at hp0
  linarith

/-- **Exercise 23.E.5(b)** (MWG, p. 922) with the clearing price constructed: there is a price
`p` at which the competitive mechanism (sellers below `p` sell, buyers above `p` buy, all at `p`)
makes truth telling a dominant strategy, is individually rational and balances the budget. -/
theorem exercise_23_E_5_competitive (D1 D2 : TypeDensity) {mS mB : ℝ} (hS : 0 ≤ mS)
    (hB : 0 ≤ mB) :
    ∃ p, MarketClears ((ENNReal.ofReal mS) • D1.measure) ((ENNReal.ofReal mB) • D2.measure) p ∧
      (∀ θ r, compSellerU p θ r ≤ compSellerU p θ θ) ∧
      (∀ θ r, compBuyerU p θ r ≤ compBuyerU p θ θ) ∧
      (∀ θ, θ ≤ compSellerU p θ θ) ∧ (∀ θ, 0 ≤ compBuyerU p θ θ) ∧
      p * ((ENNReal.ofReal mB) • D2.measure).real (Set.Ioi p) -
        p * ((ENNReal.ofReal mS) • D1.measure).real (Set.Iio p) = 0 := by
  obtain ⟨p, -, hp⟩ := exercise_23_E_5_clearing D1 D2 hS hB
  obtain ⟨h1, h2, h3, h4, h5⟩ := exercise_23_E_5b p
  exact ⟨p, hp, h1, h2, h3, h4, h5 _ _ hp⟩

end MWG.MechanismDesign

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Example 23.B.2: manipulating the Walrasian social choice function

MWG, Section 23.B, Example 23.B.2 and Figure 23.B.1 (pp. 860-861). A two-consumer, two-good
exchange economy; consumer 1 has one possible type, consumer 2 has all individualistic,
monotone, convex preferences. The social choice function that selects the Walrasian equilibrium
allocation for each announced profile is ex post efficient, but consumer 2 can gain by
misreporting. MWG argue with offer curves in Figure 23.B.1; we make the example concrete.

Endowments `ω₁ = (0, 1)`, `ω₂ = (1, 0)`; consumer 1 has `u₁(x, y) = xy`; consumer 2's true type
`θ₂'` has `u₂(x, y) = xy` and the misreported type `θ₂''` has the (monotone, convex) Leontief
preference `min(x, 3y/2)`. Prices are `p = (p₁, p₂) ≫ 0`.

* Demands: `xy` demands `(w/(2p₁), w/(2p₂))` (`wm_cd_opt_iff`); `min(x, βy)` demands
  `(βw/(βp₁ + p₂), w/(βp₁ + p₂))` (`wm_leontief_opt_iff`), uniquely.
* With the true preferences the unique Walrasian equilibrium allocation gives each consumer
  `(1/2, 1/2)` (prices `p₁ = p₂`, `example_23_B_2_truthful`); with consumer 2 announcing `θ₂''`
  it gives consumer 1 `(1/4, 1/2)` and consumer 2 `(3/4, 1/2)` (prices `p₂ = p₁/2`,
  `example_23_B_2_misreport`).
* `example_23_B_2`: the Walrasian social choice function is well defined (unique equilibria)
  and consumer 2 of true type `θ₂'` strictly prefers the allocation he gets by announcing `θ₂''`
  (`3/8 > 1/4`): truth telling is not optimal for him.
* `wm_first_welfare`: the first welfare theorem in this setting, so the Walrasian social choice
  function is ex post efficient (`example_23_B_2_efficient`).
-/

namespace MWG.MechanismDesign

/-- **Example 23.B.2** (MWG, p. 860): `z` is an optimal bundle for utility `u` at prices
`p ≫ 0` and wealth `w`: `z ≥ 0`, `p · z ≤ w`, and `u(z') ≤ u(z)` for every affordable `z' ≥ 0`. -/
def WmOpt (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (w : ℝ) (z : ℝ × ℝ) : Prop :=
  0 ≤ z.1 ∧ 0 ≤ z.2 ∧ p.1 * z.1 + p.2 * z.2 ≤ w ∧
    ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w → u z' ≤ u z

/-- **Example 23.B.2** (MWG, p. 860): a Walrasian equilibrium of the two-consumer exchange
economy with utilities `u₁`, `u₂` and endowments `ω₁`, `ω₂`: prices `p ≫ 0`, each consumer's
bundle optimal given the value of his endowment, and markets clear. -/
def WmEq (u1 u2 : ℝ × ℝ → ℝ) (ω1 ω2 p z1 z2 : ℝ × ℝ) : Prop :=
  0 < p.1 ∧ 0 < p.2 ∧ z1.1 + z2.1 = ω1.1 + ω2.1 ∧ z1.2 + z2.2 = ω1.2 + ω2.2 ∧
    WmOpt u1 p (p.1 * ω1.1 + p.2 * ω1.2) z1 ∧ WmOpt u2 p (p.1 * ω2.1 + p.2 * ω2.2) z2

/-- Cobb-Douglas utility `u(x, y) = xy`. -/
def wmCD (z : ℝ × ℝ) : ℝ := z.1 * z.2

/-- Leontief utility `u(x, y) = min(x, βy)`. -/
noncomputable def wmLeontief (β : ℝ) (z : ℝ × ℝ) : ℝ := min z.1 (β * z.2)

/-- With `u = xy`, prices `p ≫ 0` and wealth `w > 0`, the optimal bundle is unique:
`(w/(2p₁), w/(2p₂))`. -/
theorem wm_cd_opt_iff {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2) {w : ℝ} (hw : 0 < w)
    (z : ℝ × ℝ) : WmOpt wmCD p w z ↔ z = (w / (2 * p.1), w / (2 * p.2)) := by
  have bound : ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w →
      4 * (p.1 * p.2) * (z'.1 * z'.2) ≤ w ^ 2 := by
    intro z' h1 h2 hb
    have hs : 0 ≤ p.1 * z'.1 + p.2 * z'.2 := by positivity
    nlinarith [sq_nonneg (p.1 * z'.1 - p.2 * z'.2)]
  have hval : 4 * (p.1 * p.2) * (w / (2 * p.1) * (w / (2 * p.2))) = w ^ 2 := by
    field_simp; ring
  have hpp : 0 < 4 * (p.1 * p.2) := by positivity
  constructor
  · rintro ⟨h1, h2, hb, hmax⟩
    have hge := hmax (w / (2 * p.1), w / (2 * p.2)) (by positivity) (by positivity)
      (by simp only; field_simp; linarith)
    simp only [wmCD] at hge
    have hle := bound z h1 h2 hb
    have heq : 4 * (p.1 * p.2) * (z.1 * z.2) = w ^ 2 := by nlinarith
    have hs : 0 ≤ p.1 * z.1 + p.2 * z.2 := by positivity
    have hd : (p.1 * z.1 - p.2 * z.2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p.1 * z.1 - p.2 * z.2)]
    have hd' : p.1 * z.1 = p.2 * z.2 := by
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hd
      linarith
    have hsum : p.1 * z.1 + p.2 * z.2 = w := by nlinarith
    obtain ⟨a, b⟩ := z
    simp only at hd' hsum ⊢
    refine Prod.ext ?_ ?_
    · simp only; field_simp; linarith
    · simp only; field_simp; linarith
  · rintro rfl
    refine ⟨by positivity, by positivity, by simp only; field_simp; linarith,
      fun z' h1 h2 hb => ?_⟩
    have := bound z' h1 h2 hb
    simp only [wmCD]
    nlinarith

/-- With `u = min(x, βy)`, `β > 0`, prices `p ≫ 0` and wealth `w ≥ 0`, the optimal bundle is
unique: `(βw/(βp₁ + p₂), w/(βp₁ + p₂))`. -/
theorem wm_leontief_opt_iff {β : ℝ} (hβ : 0 < β) {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    {w : ℝ} (hw : 0 ≤ w) (z : ℝ × ℝ) :
    WmOpt (wmLeontief β) p w z ↔ z = (β * w / (β * p.1 + p.2), w / (β * p.1 + p.2)) := by
  have hD : 0 < β * p.1 + p.2 := by positivity
  set m := β * w / (β * p.1 + p.2) with hm
  have hm' : m * (β * p.1 + p.2) = β * w := by rw [hm]; field_simp
  have bound : ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w →
      wmLeontief β z' ≤ m := by
    intro z' h1 h2 hb
    simp only [wmLeontief]
    set k := min z'.1 (β * z'.2)
    have k1 : k ≤ z'.1 := min_le_left _ _
    have k2 : k ≤ β * z'.2 := min_le_right _ _
    have : k * (β * p.1 + p.2) ≤ β * w := by
      nlinarith [mul_le_mul_of_nonneg_left k1 (mul_nonneg hβ.le hp1.le),
        mul_le_mul_of_nonneg_left k2 hp2.le, mul_le_mul_of_nonneg_left hb hβ.le]
    rw [hm, le_div_iff₀ hD]
    linarith
  constructor
  · rintro ⟨h1, h2, hb, hmax⟩
    have hge := hmax (m, w / (β * p.1 + p.2)) (by positivity) (by positivity)
      (by simp only; rw [hm]; field_simp; linarith)
    have hval : wmLeontief β (m, w / (β * p.1 + p.2)) = m := by
      simp only [wmLeontief]
      rw [min_eq_left (le_of_eq (by rw [hm]; field_simp))]
    rw [hval] at hge
    simp only [wmLeontief] at hge
    have k1 : m ≤ z.1 := hge.trans (min_le_left _ _)
    have k2 : m ≤ β * z.2 := hge.trans (min_le_right _ _)
    have s : β * p.1 * (z.1 - m) + p.2 * (β * z.2 - m) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hb hβ.le]
    have t1 : 0 ≤ β * p.1 * (z.1 - m) := mul_nonneg (by positivity) (by linarith)
    have t2 : 0 ≤ p.2 * (β * z.2 - m) := mul_nonneg hp2.le (by linarith)
    have e1 : z.1 = m := by
      by_contra hne
      have : 0 < β * p.1 * (z.1 - m) :=
        mul_pos (by positivity) (by rcases lt_or_gt_of_ne hne with h | h <;> linarith)
      linarith
    have e2 : β * z.2 = m := by
      by_contra hne
      have : 0 < p.2 * (β * z.2 - m) :=
        mul_pos hp2 (by rcases lt_or_gt_of_ne hne with h | h <;> linarith)
      linarith
    obtain ⟨a, b⟩ := z
    simp only at e1 e2 ⊢
    refine Prod.ext e1 ?_
    simp only
    rw [hm] at e2
    field_simp at e2 ⊢
    nlinarith
  · rintro rfl
    refine ⟨by positivity, by positivity, by simp only; rw [hm]; field_simp; linarith,
      fun z' h1 h2 hb => ?_⟩
    have hval : wmLeontief β (m, w / (β * p.1 + p.2)) = m := by
      simp only [wmLeontief]
      rw [min_eq_left (le_of_eq (by rw [hm]; field_simp))]
    rw [hval]
    exact bound z' h1 h2 hb

/-- Consumer 2's utility by type: `true` is his true type `θ₂'` (`xy`), `false` the
misreported type `θ₂''` (`min(x, 3y/2)`). -/
noncomputable def wmU2 (b : Bool) : ℝ × ℝ → ℝ := if b then wmCD else wmLeontief (3 / 2)

/-- **Example 23.B.2** (MWG, pp. 860-861), the truthful profile: with both consumers having
`u = xy` and endowments `(0, 1)`, `(1, 0)`, prices `(1, 1)` and the allocation
`((1/2, 1/2), (1/2, 1/2))` are a Walrasian equilibrium, and every Walrasian equilibrium has this
allocation. -/
theorem example_23_B_2_truthful :
    WmEq wmCD (wmU2 true) (0, 1) (1, 0) (1, 1) (1 / 2, 1 / 2) (1 / 2, 1 / 2) ∧
      ∀ p z1 z2, WmEq wmCD (wmU2 true) (0, 1) (1, 0) p z1 z2 →
        z1 = (1 / 2, 1 / 2) ∧ z2 = (1 / 2, 1 / 2) := by
  simp only [wmU2, ite_true]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · rw [wm_cd_opt_iff (p := (1, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rw [wm_cd_opt_iff (p := (1, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rintro ⟨p1, p2⟩ z1 z2 ⟨hp1, hp2, hc1, hc2, ho1, ho2⟩
    rw [wm_cd_opt_iff (p := (p1, p2)) hp1 hp2 (by simp only; linarith)] at ho1 ho2
    subst ho1 ho2
    have h1 : (p1 * 0 + p2 * 1) / (2 * p2) = 1 / 2 := by field_simp; ring
    have h2 : (p1 * 1 + p2 * 0) / (2 * p2) = 1 / 2 := by linarith
    rw [div_eq_iff (by positivity)] at h2
    have e : p1 = p2 := by linarith
    subst e
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> field_simp <;> ring

/-- **Example 23.B.2** (MWG, pp. 860-861), the misreported profile: with consumer 2 announcing
the Leontief type `min(x, 3y/2)`, prices `(2, 1)` and the allocation `((1/4, 1/2), (3/4, 1/2))`
are a Walrasian equilibrium, and every Walrasian equilibrium has this allocation. -/
theorem example_23_B_2_misreport :
    WmEq wmCD (wmU2 false) (0, 1) (1, 0) (2, 1) (1 / 4, 1 / 2) (3 / 4, 1 / 2) ∧
      ∀ p z1 z2, WmEq wmCD (wmU2 false) (0, 1) (1, 0) p z1 z2 →
        z1 = (1 / 4, 1 / 2) ∧ z2 = (3 / 4, 1 / 2) := by
  simp only [wmU2, Bool.false_eq_true, ite_false]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · rw [wm_cd_opt_iff (p := (2, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rw [wm_leontief_opt_iff (by norm_num) (p := (2, 1)) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rintro ⟨p1, p2⟩ z1 z2 ⟨hp1, hp2, hc1, hc2, ho1, ho2⟩
    rw [wm_cd_opt_iff (p := (p1, p2)) hp1 hp2 (by simp only; linarith)] at ho1
    rw [wm_leontief_opt_iff (by norm_num) (p := (p1, p2)) hp1 hp2
      (by simp only; linarith)] at ho2
    subst ho1 ho2
    have hD : 0 < 3 / 2 * p1 + p2 := by positivity
    have h1 : (p1 * 0 + p2 * 1) / (2 * p2) = 1 / 2 := by field_simp; ring
    have h2 : (p1 * 1 + p2 * 0) / (3 / 2 * p1 + p2) = 1 / 2 := by linarith
    rw [div_eq_iff hD.ne'] at h2
    have e : p2 = p1 / 2 := by linarith
    subst e
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> field_simp <;> ring

/-- **Example 23.B.2** (MWG, pp. 860-861; Figure 23.B.1). The Walrasian social choice function
`f(θ₂)` (the unique Walrasian equilibrium allocation for the announced profile) is not truthfully
implementable: when consumer 2's true type is `θ₂'` (`u₂ = xy`), announcing `θ₂''` gives him
`(3/4, 1/2)`, which he strictly prefers (`3/8 > 1/4`) to his truthful allocation `(1/2, 1/2)`. -/
theorem example_23_B_2 :
    (∀ p z1 z2, WmEq wmCD (wmU2 true) (0, 1) (1, 0) p z1 z2 → z2 = (1 / 2, 1 / 2)) ∧
      (∀ p z1 z2, WmEq wmCD (wmU2 false) (0, 1) (1, 0) p z1 z2 → z2 = (3 / 4, 1 / 2)) ∧
      wmU2 true (1 / 2, 1 / 2) < wmU2 true (3 / 4, 1 / 2) :=
  ⟨fun p z1 z2 h => (example_23_B_2_truthful.2 p z1 z2 h).2,
    fun p z1 z2 h => (example_23_B_2_misreport.2 p z1 z2 h).2,
    by simp only [wmU2, ite_true, wmCD]; norm_num⟩

/-- Local nonsatiation in the form used: adding `δ > 0` of both goods to a bundle `z ≥ 0` makes
the consumer strictly better off. -/
def WmLNS (u : ℝ × ℝ → ℝ) : Prop :=
  ∀ z : ℝ × ℝ, 0 ≤ z.1 → 0 ≤ z.2 → ∀ δ : ℝ, 0 < δ → u z < u (z.1 + δ, z.2 + δ)

/-- If `z'` is affordable or strictly cheaper and `u` is locally nonsatiated, an optimal bundle
`z` with `u(z') ≥ u(z)` forces `p · z' ≥ w`, and `u(z') > u(z)` forces `p · z' > w`. -/
theorem wm_cost_ge {u : ℝ × ℝ → ℝ} (hu : WmLNS u) {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    {w : ℝ} {z z' : ℝ × ℝ} (hz : WmOpt u p w z) (h1 : 0 ≤ z'.1) (h2 : 0 ≤ z'.2) :
    (u z ≤ u z' → w ≤ p.1 * z'.1 + p.2 * z'.2) ∧
      (u z < u z' → w < p.1 * z'.1 + p.2 * z'.2) := by
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · by_contra hc
    rw [not_le] at hc
    set δ := (w - (p.1 * z'.1 + p.2 * z'.2)) / (p.1 + p.2) with hδ
    have hpp : 0 < p.1 + p.2 := by linarith
    have hδ0 : 0 < δ := div_pos (by linarith) hpp
    have hcost : p.1 * (z'.1 + δ) + p.2 * (z'.2 + δ) ≤ w := by
      have : δ * (p.1 + p.2) = w - (p.1 * z'.1 + p.2 * z'.2) := by
        rw [hδ]; field_simp
      nlinarith
    have := hz.2.2.2 (z'.1 + δ, z'.2 + δ) (by simp only; linarith) (by simp only; linarith)
      hcost
    have := hu z' h1 h2 δ hδ0
    linarith
  · by_contra hc
    rw [not_lt] at hc
    have := hz.2.2.2 z' h1 h2 hc
    linarith

/-- **Example 23.B.2** (MWG, p. 860), "this social choice function is ex post efficient": the
first welfare theorem for the two-consumer exchange economy with locally nonsatiated utilities.
A Walrasian equilibrium allocation is Pareto optimal: no feasible allocation makes one consumer
better off and the other strictly better off. -/
theorem wm_first_welfare {u1 u2 : ℝ × ℝ → ℝ} (hu1 : WmLNS u1) (hu2 : WmLNS u2)
    {ω1 ω2 p z1 z2 : ℝ × ℝ} (h : WmEq u1 u2 ω1 ω2 p z1 z2) :
    ¬∃ y1 y2 : ℝ × ℝ, 0 ≤ y1.1 ∧ 0 ≤ y1.2 ∧ 0 ≤ y2.1 ∧ 0 ≤ y2.2 ∧
      y1.1 + y2.1 ≤ ω1.1 + ω2.1 ∧ y1.2 + y2.2 ≤ ω1.2 + ω2.2 ∧
      u1 z1 ≤ u1 y1 ∧ u2 z2 ≤ u2 y2 ∧ (u1 z1 < u1 y1 ∨ u2 z2 < u2 y2) := by
  obtain ⟨hp1, hp2, -, -, ho1, ho2⟩ := h
  rintro ⟨y1, y2, a1, a2, b1, b2, c1, c2, d1, d2, hs⟩
  have k1 := wm_cost_ge hu1 hp1 hp2 ho1 a1 a2
  have k2 := wm_cost_ge hu2 hp1 hp2 ho2 b1 b2
  have f1 : p.1 * (y1.1 + y2.1) ≤ p.1 * (ω1.1 + ω2.1) := mul_le_mul_of_nonneg_left c1 hp1.le
  have f2 : p.2 * (y1.2 + y2.2) ≤ p.2 * (ω1.2 + ω2.2) := mul_le_mul_of_nonneg_left c2 hp2.le
  rcases hs with hs | hs
  · have := k1.2 hs
    have := k2.1 d2
    nlinarith
  · have := k1.1 d1
    have := k2.2 hs
    nlinarith

/-- `xy` is locally nonsatiated on `z ≥ 0`. -/
theorem wm_cd_lns : WmLNS wmCD := fun z h1 h2 δ hδ => by
  simp only [wmCD]; nlinarith [mul_pos hδ hδ]

/-- `min(x, βy)`, `β > 0`, is locally nonsatiated. -/
theorem wm_leontief_lns {β : ℝ} (hβ : 0 < β) : WmLNS (wmLeontief β) := fun z _ _ δ hδ => by
  simp only [wmLeontief]
  rcases le_total z.1 (β * z.2) with h | h
  · rw [min_eq_left h]
    refine lt_min (by linarith) ?_
    nlinarith
  · rw [min_eq_right h]
    refine lt_min (by linarith) ?_
    nlinarith

/-- **Example 23.B.2** (MWG, p. 860): the Walrasian social choice function is ex post efficient at
both announced profiles. -/
theorem example_23_B_2_efficient (b : Bool) {p z1 z2 : ℝ × ℝ}
    (h : WmEq wmCD (wmU2 b) (0, 1) (1, 0) p z1 z2) :
    ¬∃ y1 y2 : ℝ × ℝ, 0 ≤ y1.1 ∧ 0 ≤ y1.2 ∧ 0 ≤ y2.1 ∧ 0 ≤ y2.2 ∧
      y1.1 + y2.1 ≤ (0 : ℝ) + 1 ∧ y1.2 + y2.2 ≤ (1 : ℝ) + 0 ∧
      wmCD z1 ≤ wmCD y1 ∧ wmU2 b z2 ≤ wmU2 b y2 ∧
      (wmCD z1 < wmCD y1 ∨ wmU2 b z2 < wmU2 b y2) := by
  have hu2 : WmLNS (wmU2 b) := by
    cases b
    · simp only [wmU2, Bool.false_eq_true, ite_false]; exact wm_leontief_lns (by norm_num)
    · simp only [wmU2, ite_true]; exact wm_cd_lns
  exact wm_first_welfare wm_cd_lns hu2 h

end MWG.MechanismDesign

set_option linter.style.longLine false
#print axioms MWG.MechanismDesign.SocialChoiceFunction
#print axioms MWG.MechanismDesign.ExPostEfficient
#print axioms MWG.MechanismDesign.inducedPref
#print axioms MWG.MechanismDesign.prefSet
#print axioms MWG.MechanismDesign.inducedPref_rational
#print axioms MWG.MechanismDesign.exPostEfficient_iff
#print axioms MWG.MechanismDesign.play
#print axioms MWG.MechanismDesign.Mechanism
#print axioms MWG.MechanismDesign.Mechanism.mk
#print axioms MWG.MechanismDesign.Mechanism.outcome
#print axioms MWG.MechanismDesign.Implements
#print axioms MWG.MechanismDesign.directMechanism
#print axioms MWG.MechanismDesign.truthful
#print axioms MWG.MechanismDesign.play_truthful
#print axioms MWG.MechanismDesign.TruthfullyImplementable
#print axioms MWG.MechanismDesign.implements_of_truthfullyImplementable
#print axioms MWG.MechanismDesign.IsDominantStrategyEquilibrium
#print axioms MWG.MechanismDesign.ImplementsInDominantStrategies
#print axioms MWG.MechanismDesign.StrategyProof
#print axioms MWG.MechanismDesign.strategyProof_iff_truthfullyImplementable
#print axioms MWG.MechanismDesign.proposition_23_C_1
#print axioms MWG.MechanismDesign.lowerContour
#print axioms MWG.MechanismDesign.WeakPreferenceReversal
#print axioms MWG.MechanismDesign.exercise_23_C_1
#print axioms MWG.MechanismDesign.proposition_23_C_2
#print axioms MWG.MechanismDesign.strategyProof_implements
#print axioms MWG.MechanismDesign.interimUtility
#print axioms MWG.MechanismDesign.IsBayesianNash
#print axioms MWG.MechanismDesign.ImplementsInBNE
#print axioms MWG.MechanismDesign.BayesianIC
#print axioms MWG.MechanismDesign.bayesianIC_iff
#print axioms MWG.MechanismDesign.proposition_23_D_1
#print axioms MWG.MechanismDesign.isBayesianNash_of_dominant
#print axioms MWG.MechanismDesign.implementsInBNE_of_dominant
#print axioms MWG.MechanismDesign.bayesianIC_of_strategyProof
#print axioms MWG.MechanismDesign.WeaklyDominantInExpectation
#print axioms MWG.MechanismDesign.WeaklyDominantExPost
#print axioms MWG.MechanismDesign.footnote_23_16_expost
#print axioms MWG.MechanismDesign.footnote_23_16_expectation
#print axioms MWG.MechanismDesign.footnote_23_16
#print axioms MWG.MechanismDesign.Dictatorial
#print axioms MWG.MechanismDesign.MonotonicSCF
#print axioms MWG.MechanismDesign.eq_of_utility_eq
#print axioms MWG.MechanismDesign.lt_of_le_of_ne'
#print axioms MWG.MechanismDesign.gs_single_change
#print axioms MWG.MechanismDesign.gs_change_on
#print axioms MWG.MechanismDesign.gs_step_1
#print axioms MWG.MechanismDesign.topPref
#print axioms MWG.MechanismDesign.topPref_mem
#print axioms MWG.MechanismDesign.topPref_top
#print axioms MWG.MechanismDesign.topPref_outside
#print axioms MWG.MechanismDesign.topTwo
#print axioms MWG.MechanismDesign.topTwo_mem
#print axioms MWG.MechanismDesign.topTwo_first
#print axioms MWG.MechanismDesign.topTwo_second
#print axioms MWG.MechanismDesign.exists_type_of_pref
#print axioms MWG.MechanismDesign.gs_step_2
#print axioms MWG.MechanismDesign.gs_step_3
#print axioms MWG.MechanismDesign.strategyProof_of_dictatorial
#print axioms MWG.MechanismDesign.proposition_23_C_3
#print axioms MWG.MechanismDesign.footnote_23_19
#print axioms MWG.MechanismDesign.rankUtil
#print axioms MWG.MechanismDesign.rankUtil_le_iff
#print axioms MWG.MechanismDesign.StrictType
#print axioms MWG.MechanismDesign.RationalType
#print axioms MWG.MechanismDesign.rankU
#print axioms MWG.MechanismDesign.prefSet_rankU
#print axioms MWG.MechanismDesign.topOf
#print axioms MWG.MechanismDesign.topOf_spec
#print axioms MWG.MechanismDesign.topPref_singleton_top
#print axioms MWG.MechanismDesign.exists_strict_top
#print axioms MWG.MechanismDesign.dictatorRule
#print axioms MWG.MechanismDesign.proposition_23_C_3_instance
#print axioms MWG.MechanismDesign.exercise_23_C_3
#print axioms MWG.MechanismDesign.exercise_23_C_4
#print axioms MWG.MechanismDesign.corollary_23_C_1
#print axioms MWG.MechanismDesign.botOf
#print axioms MWG.MechanismDesign.botOf_spec
#print axioms MWG.MechanismDesign.optU
#print axioms MWG.MechanismDesign.tieBreakRule
#print axioms MWG.MechanismDesign.zeroBottom
#print axioms MWG.MechanismDesign.zeroTop
#print axioms MWG.MechanismDesign.corollary_23_C_1_converse_false
#print axioms MWG.MechanismDesign.extendPref
#print axioms MWG.MechanismDesign.extendPref_mem
#print axioms MWG.MechanismDesign.extendPref_restrict
#print axioms MWG.MechanismDesign.DictatorialOn
#print axioms MWG.MechanismDesign.corollary_23_C_2
#print axioms MWG.MechanismDesign.strategyProof_of_dictatorialOn
#print axioms MWG.MechanismDesign.corollary_23_C_2_converse_false
#print axioms MWG.MechanismDesign.qlU
#print axioms MWG.MechanismDesign.QLAlt
#print axioms MWG.MechanismDesign.EfficientProject
#print axioms MWG.MechanismDesign.BudgetBalanced
#print axioms MWG.MechanismDesign.exPostEfficient_ql_iff
#print axioms MWG.MechanismDesign.grovesTransfer
#print axioms MWG.MechanismDesign.IndepOwn
#print axioms MWG.MechanismDesign.proposition_23_C_4
#print axioms MWG.MechanismDesign.clarkeH
#print axioms MWG.MechanismDesign.EfficientForOthers
#print axioms MWG.MechanismDesign.clarke_strategyProof
#print axioms MWG.MechanismDesign.clarke_transfer_props
#print axioms MWG.MechanismDesign.footnote_23_23
#print axioms MWG.MechanismDesign.footnote_23_23_not_necessary
#print axioms MWG.MechanismDesign.clarke_pivotal_zero_tax
#print axioms MWG.MechanismDesign.goodV
#print axioms MWG.MechanismDesign.clarke_single_good
#print axioms MWG.MechanismDesign.proposition_23_C_5
#print axioms MWG.MechanismDesign.footnote_23_20
#print axioms MWG.MechanismDesign.exercise_23_C_11
#print axioms MWG.MechanismDesign.outside_agent
#print axioms MWG.MechanismDesign.sum_sum_erase
#print axioms MWG.MechanismDesign.sum_grovesTransfer
#print axioms MWG.MechanismDesign.exercise_23_C_10a_if
#print axioms MWG.MechanismDesign.exercise_23_C_10a_only_if
#print axioms MWG.MechanismDesign.exercise_23_C_10a_only_if_false_one_agent
#print axioms MWG.MechanismDesign.mixProfile
#print axioms MWG.MechanismDesign.alternating_sum_indepOwn
#print axioms MWG.MechanismDesign.mixedDifference_eq_zero
#print axioms MWG.MechanismDesign.proposition_23_C_6
#print axioms MWG.MechanismDesign.proposition_23_C_6_false_one_project
#print axioms MWG.MechanismDesign.proposition_23_C_6_false_one_agent
#print axioms MWG.MechanismDesign.quadV
#print axioms MWG.MechanismDesign.exercise_23_C_10b
#print axioms MWG.MechanismDesign.indepBeliefs
#print axioms MWG.MechanismDesign.splice
#print axioms MWG.MechanismDesign.measurable_splice
#print axioms MWG.MechanismDesign.map_splice
#print axioms MWG.MechanismDesign.integral_integral_update
#print axioms MWG.MechanismDesign.integral_eval_pi
#print axioms MWG.MechanismDesign.expectedExternality
#print axioms MWG.MechanismDesign.agvTransfer
#print axioms MWG.MechanismDesign.agvH
#print axioms MWG.MechanismDesign.agvH_indepOwn
#print axioms MWG.MechanismDesign.agv_bayesianIC
#print axioms MWG.MechanismDesign.agv_budgetBalanced
#print axioms MWG.MechanismDesign.agv_exPostEfficient_bic
#print axioms MWG.MechanismDesign.agv_finite
#print axioms MWG.MechanismDesign.bern
#print axioms MWG.MechanismDesign.bern_isProb
#print axioms MWG.MechanismDesign.integral_bern
#print axioms MWG.MechanismDesign.typeVal
#print axioms MWG.MechanismDesign.aaV
#print axioms MWG.MechanismDesign.aaK
#print axioms MWG.MechanismDesign.aaK_efficient
#print axioms MWG.MechanismDesign.update_fin_two
#print axioms MWG.MechanismDesign.aaP
#print axioms MWG.MechanismDesign.integral_aaP
#print axioms MWG.MechanismDesign.other
#print axioms MWG.MechanismDesign.xi_aa
#print axioms MWG.MechanismDesign.aaMech
#print axioms MWG.MechanismDesign.aa_gain
#print axioms MWG.MechanismDesign.example_23_AA_1_truth
#print axioms MWG.MechanismDesign.example_23_AA_1_alwaysHigh_not_BNE
#print axioms MWG.MechanismDesign.example_23_AA_1_unique
#print axioms MWG.MechanismDesign.integral_eq_of_slope_bounds
#print axioms MWG.MechanismDesign.LinearIC
#print axioms MWG.MechanismDesign.linearIC_iff
#print axioms MWG.MechanismDesign.linU
#print axioms MWG.MechanismDesign.interimBenefit
#print axioms MWG.MechanismDesign.interimTransfer
#print axioms MWG.MechanismDesign.interimU
#print axioms MWG.MechanismDesign.BayesianICOn
#print axioms MWG.MechanismDesign.InterimIntegrable
#print axioms MWG.MechanismDesign.eq_23_D_10
#print axioms MWG.MechanismDesign.proposition_23_D_2
#print axioms MWG.MechanismDesign.expected_transfer_formula
#print axioms MWG.MechanismDesign.interimTransfer_of_own
#print axioms MWG.MechanismDesign.proposition_23_D_2_derivative_false
#print axioms MWG.MechanismDesign.IsNashAt
#print axioms MWG.MechanismDesign.ImplementsInNash
#print axioms MWG.MechanismDesign.implementsInNash_iff
#print axioms MWG.MechanismDesign.StronglyImplementsInNash
#print axioms MWG.MechanismDesign.EveryNashYields
#print axioms MWG.MechanismDesign.stronglyImplementsInNash_iff
#print axioms MWG.MechanismDesign.definition_23_BB_1_literal_counterexample
#print axioms MWG.MechanismDesign.dominant_implementsInNash
#print axioms MWG.MechanismDesign.nash_exists_third
#print axioms MWG.MechanismDesign.nash_allBut_iff_card
#print axioms MWG.MechanismDesign.agreementMech
#print axioms MWG.MechanismDesign.agreementMech_outcome
#print axioms MWG.MechanismDesign.nash_agreement_isNash
#print axioms MWG.MechanismDesign.nash_any_implementable
#print axioms MWG.MechanismDesign.nash_agreement_every_value
#print axioms MWG.MechanismDesign.proposition_23_BB_1
#print axioms MWG.MechanismDesign.dictatorMech
#print axioms MWG.MechanismDesign.dictatorMech_strongly
#print axioms MWG.MechanismDesign.proposition_23_BB_2_necessity
#print axioms MWG.MechanismDesign.proposition_23_BB_2
#print axioms MWG.MechanismDesign.proposition_23_BB_2_instance
#print axioms MWG.MechanismDesign.NoVetoPower
#print axioms MWG.MechanismDesign.noVetoPower_iff_card
#print axioms MWG.MechanismDesign.noVetoPower_of_noCommonTop
#print axioms MWG.MechanismDesign.MonotonicSCC
#print axioms MWG.MechanismDesign.NoVetoPowerSCC
#print axioms MWG.MechanismDesign.StronglyImplementsSCCInNash
#print axioms MWG.MechanismDesign.FullyImplementsInNash
#print axioms MWG.MechanismDesign.FullyImplementsInNash.stronglyImplementsSCC
#print axioms MWG.MechanismDesign.stronglyImplementsInNash_iff_full
#print axioms MWG.MechanismDesign.proposition_23_BB_1_correspondence
#print axioms MWG.MechanismDesign.monotonicSCC_singleton
#print axioms MWG.MechanismDesign.noVetoPowerSCC_singleton
#print axioms MWG.MechanismDesign.MaskinMsg
#print axioms MWG.MechanismDesign.maskinOutcome
#print axioms MWG.MechanismDesign.maskinMech
#print axioms MWG.MechanismDesign.maskin_rule1
#print axioms MWG.MechanismDesign.maskin_rule2
#print axioms MWG.MechanismDesign.maskin_rule3
#print axioms MWG.MechanismDesign.maskin_win
#print axioms MWG.MechanismDesign.maskin_fullyImplements
#print axioms MWG.MechanismDesign.proposition_23_BB_3
#print axioms MWG.MechanismDesign.nvpU
#print axioms MWG.MechanismDesign.proposition_23_BB_3_instance
#print axioms MWG.MechanismDesign.ParetoSet
#print axioms MWG.MechanismDesign.WeakParetoSet
#print axioms MWG.MechanismDesign.weakParetoSet_monotonic
#print axioms MWG.MechanismDesign.nashParetoCxU
#print axioms MWG.MechanismDesign.paretoSet_not_monotonic
#print axioms MWG.MechanismDesign.nashQLU
#print axioms MWG.MechanismDesign.nash_ql_no_best
#print axioms MWG.MechanismDesign.noVetoPower_ql
#print axioms MWG.MechanismDesign.noVetoPowerSCC_ql
#print axioms MWG.MechanismDesign.nash_ql_strong_iff_monotonic
#print axioms MWG.MechanismDesign.paretoSet_ql_monotonic
#print axioms MWG.MechanismDesign.nash_ql_pareto_fullyImplements
#print axioms MWG.MechanismDesign.c8U
#print axioms MWG.MechanismDesign.c8F
#print axioms MWG.MechanismDesign.exercise_23_BB_2b_strategyProof
#print axioms MWG.MechanismDesign.exercise_23_BB_2b_implementable
#print axioms MWG.MechanismDesign.exercise_23_BB_2b_not_monotonic
#print axioms MWG.MechanismDesign.exercise_23_BB_2b_not_strongly
#print axioms MWG.MechanismDesign.bbV
#print axioms MWG.MechanismDesign.bbU
#print axioms MWG.MechanismDesign.GrovesPropertyI
#print axioms MWG.MechanismDesign.GrovesPropertyII
#print axioms MWG.MechanismDesign.bbK
#print axioms MWG.MechanismDesign.bbV_sum
#print axioms MWG.MechanismDesign.bbK_efficient
#print axioms MWG.MechanismDesign.bb_eff_true
#print axioms MWG.MechanismDesign.bb_eff_false
#print axioms MWG.MechanismDesign.bb_sum_update
#print axioms MWG.MechanismDesign.bb_erase_update
#print axioms MWG.MechanismDesign.bb_sum_erase_single
#print axioms MWG.MechanismDesign.bbF0
#print axioms MWG.MechanismDesign.bbF1
#print axioms MWG.MechanismDesign.exercise_23_BB_3_weak
#print axioms MWG.MechanismDesign.exercise_23_BB_3_weak_not_II
#print axioms MWG.MechanismDesign.exercise_23_BB_3_weak_not_I
#print axioms MWG.MechanismDesign.bb_lower_up
#print axioms MWG.MechanismDesign.bb_lower_down
#print axioms MWG.MechanismDesign.exercise_23_BB_3_constant
#print axioms MWG.MechanismDesign.exercise_23_BB_3_strong_I
#print axioms MWG.MechanismDesign.exercise_23_BB_3_strong_not_II
#print axioms MWG.MechanismDesign.exercise_23_BB_3_strong_exists
#print axioms MWG.MechanismDesign.MRBox
#print axioms MWG.MechanismDesign.mrXC
#print axioms MWG.MechanismDesign.mrXL
#print axioms MWG.MechanismDesign.mrY
#print axioms MWG.MechanismDesign.mrZ
#print axioms MWG.MechanismDesign.mrU
#print axioms MWG.MechanismDesign.mrF
#print axioms MWG.MechanismDesign.mrXL_ne_mrXC
#print axioms MWG.MechanismDesign.example_23_BB_1_figure
#print axioms MWG.MechanismDesign.example_23_BB_1_lowerContour
#print axioms MWG.MechanismDesign.example_23_BB_1_not_monotonic
#print axioms MWG.MechanismDesign.example_23_BB_1_not_strongly
#print axioms MWG.MechanismDesign.mrStage3
#print axioms MWG.MechanismDesign.mrStage2
#print axioms MWG.MechanismDesign.mrOutcome
#print axioms MWG.MechanismDesign.IsMRSubgamePerfect
#print axioms MWG.MechanismDesign.IsMRNash
#print axioms MWG.MechanismDesign.exercise_23_BB_1b
#print axioms MWG.MechanismDesign.example_23_BB_1
#print axioms MWG.MechanismDesign.exercise_23_BB_1a
#print axioms MWG.MechanismDesign.exercise_23_BB_1a_not_strongly
#print axioms MWG.MechanismDesign.exercise_23_BB_1_spe_nash
#print axioms MWG.MechanismDesign.TypeDensity
#print axioms MWG.MechanismDesign.TypeDensity.mk
#print axioms MWG.MechanismDesign.TypeDensity.lo
#print axioms MWG.MechanismDesign.TypeDensity.hi
#print axioms MWG.MechanismDesign.TypeDensity.lo_lt_hi
#print axioms MWG.MechanismDesign.TypeDensity.dens
#print axioms MWG.MechanismDesign.TypeDensity.measurable_dens
#print axioms MWG.MechanismDesign.TypeDensity.dens_pos
#print axioms MWG.MechanismDesign.TypeDensity.dens_eq_zero
#print axioms MWG.MechanismDesign.TypeDensity.integral_dens
#print axioms MWG.MechanismDesign.TypeDensity.measure
#print axioms MWG.MechanismDesign.TypeDensity.cdf
#print axioms MWG.MechanismDesign.TypeDensity.dens_nonneg
#print axioms MWG.MechanismDesign.TypeDensity.intervalIntegrable_dens
#print axioms MWG.MechanismDesign.TypeDensity.integral_volume_eq
#print axioms MWG.MechanismDesign.TypeDensity.integrable_dens
#print axioms MWG.MechanismDesign.TypeDensity.integral_eq
#print axioms MWG.MechanismDesign.TypeDensity.isProbabilityMeasure
#print axioms MWG.MechanismDesign.TypeDensity.measure_compl_Icc
#print axioms MWG.MechanismDesign.TypeDensity.measure_singleton
#print axioms MWG.MechanismDesign.TypeDensity.measure_eq_ofReal
#print axioms MWG.MechanismDesign.TypeDensity.measure_Ioo_pos
#print axioms MWG.MechanismDesign.TypeDensity.integrable_indicator_mul
#print axioms MWG.MechanismDesign.TypeDensity.measureReal_Iic
#print axioms MWG.MechanismDesign.TypeDensity.measureReal_Ici
#print axioms MWG.MechanismDesign.td_integral_integral_eq
#print axioms MWG.MechanismDesign.TypeDensity.integral_integral_eq
#print axioms MWG.MechanismDesign.uniformDensity
#print axioms MWG.MechanismDesign.uniform01
#print axioms MWG.MechanismDesign.uniform01_integral
#print axioms MWG.MechanismDesign.uniform01_cdf
#print axioms MWG.MechanismDesign.allocV
#print axioms MWG.MechanismDesign.re_abs_le_of_mem
#print axioms MWG.MechanismDesign.re_integrable_integral_update
#print axioms MWG.MechanismDesign.re_ae_mem
#print axioms MWG.MechanismDesign.re_ae_update_mem
#print axioms MWG.MechanismDesign.re_expected_transfer
#print axioms MWG.MechanismDesign.re_interimTransfer_eq
#print axioms MWG.MechanismDesign.proposition_23_D_3
#print axioms MWG.MechanismDesign.TypeDensity.virtualValue
#print axioms MWG.MechanismDesign.TypeDensity.absolutelyContinuous
#print axioms MWG.MechanismDesign.re_intervalIntegrable_mul_dens
#print axioms MWG.MechanismDesign.TypeDensity.continuous_cdf
#print axioms MWG.MechanismDesign.eq_23_D_14
#print axioms MWG.MechanismDesign.TypeDensity.aestronglyMeasurable_of_monotoneOn
#print axioms MWG.MechanismDesign.eq_23_D_15
#print axioms MWG.MechanismDesign.eq_23_D_16
#print axioms MWG.MechanismDesign.unif2
#print axioms MWG.MechanismDesign.re_update_vec0
#print axioms MWG.MechanismDesign.re_update_vec1
#print axioms MWG.MechanismDesign.re_unif2_update
#print axioms MWG.MechanismDesign.re_unif2_integral
#print axioms MWG.MechanismDesign.re_integral_ite_le
#print axioms MWG.MechanismDesign.re_integral_ite_lt
#print axioms MWG.MechanismDesign.re_integral_ite_gt
#print axioms MWG.MechanismDesign.twoY
#print axioms MWG.MechanismDesign.firstPriceT
#print axioms MWG.MechanismDesign.secondPriceT
#print axioms MWG.MechanismDesign.measurable_twoY
#print axioms MWG.MechanismDesign.twoY_props
#print axioms MWG.MechanismDesign.twoY_interimBenefit
#print axioms MWG.MechanismDesign.re_unif2_integrable
#print axioms MWG.MechanismDesign.re_twoY_bic
#print axioms MWG.MechanismDesign.firstPriceT_interim
#print axioms MWG.MechanismDesign.secondPriceT_interim
#print axioms MWG.MechanismDesign.exercise_23_D_3
#print axioms MWG.MechanismDesign.re_price_facts
#print axioms MWG.MechanismDesign.exercise_23_D_3_revenue_equivalence
#print axioms MWG.MechanismDesign.eq_23_D_16_instance
#print axioms MWG.MechanismDesign.re_integral_ite_ge
#print axioms MWG.MechanismDesign.bilatV
#print axioms MWG.MechanismDesign.bilatK
#print axioms MWG.MechanismDesign.bilatK_efficient
#print axioms MWG.MechanismDesign.bilat_xi_integrand
#print axioms MWG.MechanismDesign.exercise_23_D_2a_xi
#print axioms MWG.MechanismDesign.exercise_23_D_2a
#print axioms MWG.MechanismDesign.exercise_23_D_2b
#print axioms MWG.MechanismDesign.InTypes
#print axioms MWG.MechanismDesign.ExPostEfficientTrade
#print axioms MWG.MechanismDesign.BudgetBalancedOn
#print axioms MWG.MechanismDesign.InterimIR
#print axioms MWG.MechanismDesign.msVcgT
#print axioms MWG.MechanismDesign.ms_mul_le_max
#print axioms MWG.MechanismDesign.ms_eff_mul
#print axioms MWG.MechanismDesign.ms_vcg_seller
#print axioms MWG.MechanismDesign.ms_vcg_buyer
#print axioms MWG.MechanismDesign.ms_vcg_bound
#print axioms MWG.MechanismDesign.ms_measurable_vcg
#print axioms MWG.MechanismDesign.ms_vcg_bic
#print axioms MWG.MechanismDesign.ms_integrable_of_bound
#print axioms MWG.MechanismDesign.ms_abs_max_sub_le
#print axioms MWG.MechanismDesign.ms_integrable_pos_parts
#print axioms MWG.MechanismDesign.ms_core
#print axioms MWG.MechanismDesign.proposition_23_E_1_general
#print axioms MWG.MechanismDesign.footnote_23_41
#print axioms MWG.MechanismDesign.proposition_23_E_1
#print axioms MWG.MechanismDesign.DominantICOn
#print axioms MWG.MechanismDesign.ExPostIR
#print axioms MWG.MechanismDesign.ms_update_mem
#print axioms MWG.MechanismDesign.ms_bic_of_dsic
#print axioms MWG.MechanismDesign.ms_interimIR_of_exPostIR
#print axioms MWG.MechanismDesign.exercise_23_E_2a
#print axioms MWG.MechanismDesign.exercise_23_E_2b
#print axioms MWG.MechanismDesign.noTradeY
#print axioms MWG.MechanismDesign.exercise_23_E_2_literal_false
#print axioms MWG.MechanismDesign.ms_unif_hyps
#print axioms MWG.MechanismDesign.ms_unif_mean
#print axioms MWG.MechanismDesign.ms_unif_gains
#print axioms MWG.MechanismDesign.exercise_23_E_7b_surplus
#print axioms MWG.MechanismDesign.exercise_23_E_7b
#print axioms MWG.MechanismDesign.exercise_23_E_7a
#print axioms MWG.MechanismDesign.twoY_efficient
#print axioms MWG.MechanismDesign.measurable_twoY'
#print axioms MWG.MechanismDesign.exercise_23_E_7
#print axioms MWG.MechanismDesign.agvBT
#print axioms MWG.MechanismDesign.agvBT_facts
#print axioms MWG.MechanismDesign.agvBT_interim
#print axioms MWG.MechanismDesign.exercise_23_E_1
#print axioms MWG.MechanismDesign.ms_vcg_interimIR
#print axioms MWG.MechanismDesign.proposition_23_E_1_instance_no_bb
#print axioms MWG.MechanismDesign.postQ
#print axioms MWG.MechanismDesign.postY
#print axioms MWG.MechanismDesign.postT
#print axioms MWG.MechanismDesign.measurable_postQ
#print axioms MWG.MechanismDesign.proposition_23_E_1_instance_no_eff
#print axioms MWG.MechanismDesign.splitT
#print axioms MWG.MechanismDesign.proposition_23_E_1_instance_no_bic
#print axioms MWG.MechanismDesign.discVal
#print axioms MWG.MechanismDesign.discU
#print axioms MWG.MechanismDesign.discF
#print axioms MWG.MechanismDesign.exercise_23_E_3
#print axioms MWG.MechanismDesign.BasSCF
#print axioms MWG.MechanismDesign.BasSCF.mk
#print axioms MWG.MechanismDesign.BasSCF.yL
#print axioms MWG.MechanismDesign.BasSCF.tL
#print axioms MWG.MechanismDesign.BasSCF.yH
#print axioms MWG.MechanismDesign.BasSCF.tH
#print axioms MWG.MechanismDesign.BasSCF.U1L
#print axioms MWG.MechanismDesign.BasSCF.U1H
#print axioms MWG.MechanismDesign.BasSCF.U2
#print axioms MWG.MechanismDesign.BasSCF.U1
#print axioms MWG.MechanismDesign.BasSCF.Prob
#print axioms MWG.MechanismDesign.BasSCF.ICH
#print axioms MWG.MechanismDesign.BasSCF.ICL
#print axioms MWG.MechanismDesign.BasSCF.IR1L
#print axioms MWG.MechanismDesign.BasSCF.IR1H
#print axioms MWG.MechanismDesign.BasSCF.IR2
#print axioms MWG.MechanismDesign.basFStar
#print axioms MWG.MechanismDesign.basFBuyerIR
#print axioms MWG.MechanismDesign.basInterimDominates
#print axioms MWG.MechanismDesign.basExAnteDominates
#print axioms MWG.MechanismDesign.BasInterimEfficientIn
#print axioms MWG.MechanismDesign.BasExAnteEfficientIn
#print axioms MWG.MechanismDesign.BasPairEfficient
#print axioms MWG.MechanismDesign.BasExPostEfficient
#print axioms MWG.MechanismDesign.basPairEfficient_iff
#print axioms MWG.MechanismDesign.exercise_23_F_8
#print axioms MWG.MechanismDesign.exercise_23_F_9a
#print axioms MWG.MechanismDesign.exercise_23_F_9b
#print axioms MWG.MechanismDesign.exercise_23_F_9c
#print axioms MWG.MechanismDesign.basC17
#print axioms MWG.MechanismDesign.BasSolves17
#print axioms MWG.MechanismDesign.basC17_iff
#print axioms MWG.MechanismDesign.basFStar_of_C17
#print axioms MWG.MechanismDesign.bas_step1
#print axioms MWG.MechanismDesign.bas_step3
#print axioms MWG.MechanismDesign.bas_step4
#print axioms MWG.MechanismDesign.bas_key
#print axioms MWG.MechanismDesign.basC19
#print axioms MWG.MechanismDesign.BasSolves19
#print axioms MWG.MechanismDesign.bas_solves19_iff
#print axioms MWG.MechanismDesign.bas_solves17_iff
#print axioms MWG.MechanismDesign.bas_step2
#print axioms MWG.MechanismDesign.bas_solves17_i_redundant
#print axioms MWG.MechanismDesign.basShaded
#print axioms MWG.MechanismDesign.bas_shaded_iff
#print axioms MWG.MechanismDesign.bas_shaded_yH_le
#print axioms MWG.MechanismDesign.bas_interimIE_iff
#print axioms MWG.MechanismDesign.bas_interimIE_yH_le
#print axioms MWG.MechanismDesign.bas_interimIE_iff_solves17
#print axioms MWG.MechanismDesign.bas_exAnte_utilities
#print axioms MWG.MechanismDesign.bas_key_exAnte
#print axioms MWG.MechanismDesign.bas_exAnteIE_iff
#print axioms MWG.MechanismDesign.bas_interimIE_of_exAnteIE
#print axioms MWG.MechanismDesign.bas_exAnteIE_IR1H_binds
#print axioms MWG.MechanismDesign.footnote_23_54
#print axioms MWG.MechanismDesign.bas_nonvacuous
#print axioms MWG.MechanismDesign.exercise_23_F_10_interim
#print axioms MWG.MechanismDesign.exercise_23_F_10_exAnte
#print axioms MWG.MechanismDesign.exercise_23_F_10_compare
#print axioms MWG.MechanismDesign.scfInterimU
#print axioms MWG.MechanismDesign.scfExAnteU
#print axioms MWG.MechanismDesign.ExPostParticipation
#print axioms MWG.MechanismDesign.InterimParticipation
#print axioms MWG.MechanismDesign.ExAnteParticipation
#print axioms MWG.MechanismDesign.interimParticipation_of_exPost
#print axioms MWG.MechanismDesign.exAnteParticipation_of_interim
#print axioms MWG.MechanismDesign.partUnifBelief
#print axioms MWG.MechanismDesign.partUnifBelief_isProb
#print axioms MWG.MechanismDesign.part_integral_unif
#print axioms MWG.MechanismDesign.participation_interim_not_exPost
#print axioms MWG.MechanismDesign.participation_exAnte_not_interim
#print axioms MWG.MechanismDesign.partVal
#print axioms MWG.MechanismDesign.partK
#print axioms MWG.MechanismDesign.partV
#print axioms MWG.MechanismDesign.partF
#print axioms MWG.MechanismDesign.PartFeasible
#print axioms MWG.MechanismDesign.example_23_E_1_efficient
#print axioms MWG.MechanismDesign.example_23_E_1
#print axioms MWG.MechanismDesign.example_23_E_1_outside
#print axioms MWG.MechanismDesign.part_vec2
#print axioms MWG.MechanismDesign.example_23_E_1_sp_ir
#print axioms MWG.MechanismDesign.example_23_E_1_sp_feasible
#print axioms MWG.MechanismDesign.example_23_E_1_ir_feasible
#print axioms MWG.MechanismDesign.fBIC
#print axioms MWG.MechanismDesign.fIRExPost
#print axioms MWG.MechanismDesign.fIRInterim
#print axioms MWG.MechanismDesign.fIRExAnte
#print axioms MWG.MechanismDesign.incentiveFeasible
#print axioms MWG.MechanismDesign.incentiveFeasible_subset
#print axioms MWG.MechanismDesign.ExAnteEfficientIn
#print axioms MWG.MechanismDesign.InterimEfficientIn
#print axioms MWG.MechanismDesign.ExPostEfficientIn
#print axioms MWG.MechanismDesign.exPostEfficientIn_univ_iff
#print axioms MWG.MechanismDesign.proposition_23_F_1
#print axioms MWG.MechanismDesign.proposition_23_F_1_pointMass
#print axioms MWG.MechanismDesign.wcSpike
#print axioms MWG.MechanismDesign.proposition_23_F_1_false
#print axioms MWG.MechanismDesign.UpClosed
#print axioms MWG.MechanismDesign.exPostParticipation_upClosed
#print axioms MWG.MechanismDesign.interimParticipation_upClosed
#print axioms MWG.MechanismDesign.wc_exAnteU_eq
#print axioms MWG.MechanismDesign.wc_sum_le_of_exPostEfficientIn
#print axioms MWG.MechanismDesign.exercise_23_F_1_exAnte
#print axioms MWG.MechanismDesign.exercise_23_F_1_interim
#print axioms MWG.MechanismDesign.FeasAlloc
#print axioms MWG.MechanismDesign.PointwiseOptAlloc
#print axioms MWG.MechanismDesign.auctionRevenue
#print axioms MWG.MechanismDesign.OptAuctionFeasible
#print axioms MWG.MechanismDesign.eq_23_F_iv_iff
#print axioms MWG.MechanismDesign.example_23_F_2
#print axioms MWG.MechanismDesign.oa_sum_split
#print axioms MWG.MechanismDesign.eq_23_F_9
#print axioms MWG.MechanismDesign.eq_23_F_9_converse
#print axioms MWG.MechanismDesign.oa_uniform_cdf
#print axioms MWG.MechanismDesign.oa_uniform_virtualValue
#print axioms MWG.MechanismDesign.example_23_F_2_remark1
#print axioms MWG.MechanismDesign.example_23_F_2_remark2_pointwise
#print axioms MWG.MechanismDesign.example_23_F_2_remark2
#print axioms MWG.MechanismDesign.example_23_F_2_remark3_pointwise
#print axioms MWG.MechanismDesign.example_23_F_2_remark3_foc_iff
#print axioms MWG.MechanismDesign.example_23_F_2_remark3_foc
#print axioms MWG.MechanismDesign.exercise_23_F_3
#print axioms MWG.MechanismDesign.exercise_23_F_4
#print axioms MWG.MechanismDesign.exercise_23_F_4_rule
#print axioms MWG.MechanismDesign.oaPostY
#print axioms MWG.MechanismDesign.oaPostT
#print axioms MWG.MechanismDesign.oa_uniform01_virtualValue
#print axioms MWG.MechanismDesign.example_23_F_2_instance
#print axioms MWG.MechanismDesign.ocU
#print axioms MWG.MechanismDesign.OCFeasible
#print axioms MWG.MechanismDesign.ocPayoff
#print axioms MWG.MechanismDesign.eq_23_F_3
#print axioms MWG.MechanismDesign.oc_monotone_comp_iff
#print axioms MWG.MechanismDesign.eq_23_F_iii_iff
#print axioms MWG.MechanismDesign.oc_one_sub_cdf_nonneg
#print axioms MWG.MechanismDesign.oc_one_sub_cdf_pos
#print axioms MWG.MechanismDesign.eq_23_F_4
#print axioms MWG.MechanismDesign.eq_23_F_5
#print axioms MWG.MechanismDesign.OCArgmax
#print axioms MWG.MechanismDesign.oc_integrable_vJ
#print axioms MWG.MechanismDesign.example_23_F_1
#print axioms MWG.MechanismDesign.eq_23_F_6
#print axioms MWG.MechanismDesign.oc_maximizer_mono
#print axioms MWG.MechanismDesign.oc_argmax_unique
#print axioms MWG.MechanismDesign.oc_strictConcave
#print axioms MWG.MechanismDesign.oc_maximizer_monotoneOn
#print axioms MWG.MechanismDesign.oc_virtualValue_facts
#print axioms MWG.MechanismDesign.example_23_F_1_le_firstBest
#print axioms MWG.MechanismDesign.example_23_F_1_eq_firstBest_hi
#print axioms MWG.MechanismDesign.oc_not_argmax_zero
#print axioms MWG.MechanismDesign.example_23_F_1_lt_firstBest
#print axioms MWG.MechanismDesign.oc_integrable_of_bound
#print axioms MWG.MechanismDesign.example_23_F_1_instance
#print axioms MWG.MechanismDesign.b1Θ
#print axioms MWG.MechanismDesign.b1U
#print axioms MWG.MechanismDesign.b1F
#print axioms MWG.MechanismDesign.b1Prof
#print axioms MWG.MechanismDesign.b1_strategyProof_iff
#print axioms MWG.MechanismDesign.b1Example
#print axioms MWG.MechanismDesign.example_23_B_1_efficient
#print axioms MWG.MechanismDesign.example_23_B_1
#print axioms MWG.MechanismDesign.exercise_23_B_1a
#print axioms MWG.MechanismDesign.exercise_23_B_1b
#print axioms MWG.MechanismDesign.exercise_23_B_1c
#print axioms MWG.MechanismDesign.exercise_23_B_1d
#print axioms MWG.MechanismDesign.exercise_23_B_1e
#print axioms MWG.MechanismDesign.ppK
#print axioms MWG.MechanismDesign.PPAlt
#print axioms MWG.MechanismDesign.ppU
#print axioms MWG.MechanismDesign.pp_improve
#print axioms MWG.MechanismDesign.example_23_B_3_efficient_iff
#print axioms MWG.MechanismDesign.example_23_B_3_efficient
#print axioms MWG.MechanismDesign.ppEgal
#print axioms MWG.MechanismDesign.ppEgal_efficient
#print axioms MWG.MechanismDesign.example_23_B_3
#print axioms MWG.MechanismDesign.goodV_efficient_iff
#print axioms MWG.MechanismDesign.example_23_B_4_efficient_iff
#print axioms MWG.MechanismDesign.example_23_B_4_bilateral
#print axioms MWG.MechanismDesign.clamp01
#print axioms MWG.MechanismDesign.clamp01_mem
#print axioms MWG.MechanismDesign.clamp01_of_mem
#print axioms MWG.MechanismDesign.clamp01_of_nonpos
#print axioms MWG.MechanismDesign.clamp01_of_one_le
#print axioms MWG.MechanismDesign.au_int_le
#print axioms MWG.MechanismDesign.au_int_lt
#print axioms MWG.MechanismDesign.au_int_gt
#print axioms MWG.MechanismDesign.au_int_affine
#print axioms MWG.MechanismDesign.au_eval
#print axioms MWG.MechanismDesign.au_meas_le
#print axioms MWG.MechanismDesign.au_meas_lt
#print axioms MWG.MechanismDesign.au_meas_gt
#print axioms MWG.MechanismDesign.fullPriceT
#print axioms MWG.MechanismDesign.fullPrice_interim
#print axioms MWG.MechanismDesign.example_23_B_4_firstPriceType
#print axioms MWG.MechanismDesign.example_23_B_4_secondPriceType
#print axioms MWG.MechanismDesign.auctionSCF
#print axioms MWG.MechanismDesign.example_23_B_4_auction_efficient
#print axioms MWG.MechanismDesign.example_23_B_7
#print axioms MWG.MechanismDesign.exercise_23_B_2
#print axioms MWG.MechanismDesign.IsBNEOn
#print axioms MWG.MechanismDesign.fpMech2
#print axioms MWG.MechanismDesign.linStrat
#print axioms MWG.MechanismDesign.fp_interim
#print axioms MWG.MechanismDesign.fp_br_ineq
#print axioms MWG.MechanismDesign.example_23_B_5_bestResponse
#print axioms MWG.MechanismDesign.example_23_B_5
#print axioms MWG.MechanismDesign.au_maxSet_nonempty
#print axioms MWG.MechanismDesign.auctionWinner
#print axioms MWG.MechanismDesign.auctionWinner_max
#print axioms MWG.MechanismDesign.auctionWinner_le
#print axioms MWG.MechanismDesign.auctionWinner_eq_of_gt
#print axioms MWG.MechanismDesign.auctionWinner_fin_two
#print axioms MWG.MechanismDesign.au_erase_nonempty
#print axioms MWG.MechanismDesign.othersMax
#print axioms MWG.MechanismDesign.othersMax_fin_two
#print axioms MWG.MechanismDesign.firstPriceOutcome
#print axioms MWG.MechanismDesign.secondPriceOutcome
#print axioms MWG.MechanismDesign.winU
#print axioms MWG.MechanismDesign.firstPriceOutcome_fin_two
#print axioms MWG.MechanismDesign.sp_truth_dominant
#print axioms MWG.MechanismDesign.spMech
#print axioms MWG.MechanismDesign.bidValue
#print axioms MWG.MechanismDesign.exercise_23_B_3
#print axioms MWG.MechanismDesign.example_23_B_6
#print axioms MWG.MechanismDesign.au_ii_gt
#print axioms MWG.MechanismDesign.daMech
#print axioms MWG.MechanismDesign.da_seller_interim
#print axioms MWG.MechanismDesign.da_buyer_interim
#print axioms MWG.MechanismDesign.da_seller_ineq
#print axioms MWG.MechanismDesign.da_buyer_ineq
#print axioms MWG.MechanismDesign.daStrat
#print axioms MWG.MechanismDesign.exercise_23_B_4a
#print axioms MWG.MechanismDesign.exercise_23_B_4a_outcome
#print axioms MWG.MechanismDesign.daQL
#print axioms MWG.MechanismDesign.daQL_utility
#print axioms MWG.MechanismDesign.exercise_23_B_4a_not_efficient
#print axioms MWG.MechanismDesign.exercise_23_B_4b
#print axioms MWG.MechanismDesign.numPref
#print axioms MWG.MechanismDesign.IsMajorityVoting
#print axioms MWG.MechanismDesign.OrdinalSCF
#print axioms MWG.MechanismDesign.numPref_update
#print axioms MWG.MechanismDesign.inducedPref_bool_eq
#print axioms MWG.MechanismDesign.exercise_23_C_2
#print axioms MWG.MechanismDesign.exercise_23_C_2_instance
#print axioms MWG.MechanismDesign.exercise_23_C_2_cardinal
#print axioms MWG.MechanismDesign.typeProfile
#print axioms MWG.MechanismDesign.strict_inducedPref_iff
#print axioms MWG.MechanismDesign.exercise_23_C_5
#print axioms MWG.MechanismDesign.singlePeaked_fin3
#print axioms MWG.MechanismDesign.exercise_23_C_5_instance
#print axioms MWG.MechanismDesign.IPM
#print axioms MWG.MechanismDesign.ipm_iff
#print axioms MWG.MechanismDesign.exercise_23_C_6a
#print axioms MWG.MechanismDesign.c6U
#print axioms MWG.MechanismDesign.c6F
#print axioms MWG.MechanismDesign.exercise_23_C_6b
#print axioms MWG.MechanismDesign.exercise_23_C_6c
#print axioms MWG.MechanismDesign.exercise_23_C_6d
#print axioms MWG.MechanismDesign.exercise_23_C_6_instance
#print axioms MWG.MechanismDesign.NonnegResponsive
#print axioms MWG.MechanismDesign.exercise_23_C_7
#print axioms MWG.MechanismDesign.exercise_23_C_7_instance
#print axioms MWG.MechanismDesign.exercise_23_C_8a
#print axioms MWG.MechanismDesign.exercise_23_C_8b
#print axioms MWG.MechanismDesign.WeaklyDominantAction
#print axioms MWG.MechanismDesign.c8Untruthful
#print axioms MWG.MechanismDesign.exercise_23_C_8c
#print axioms MWG.MechanismDesign.EveryEquilibriumYields
#print axioms MWG.MechanismDesign.StronglyImplements
#print axioms MWG.MechanismDesign.StronglyImplements.implements
#print axioms MWG.MechanismDesign.stronglyImplements_strategyProof
#print axioms MWG.MechanismDesign.definition_23_AA_1_literal_counterexample
#print axioms MWG.MechanismDesign.StronglyImplementsSCC
#print axioms MWG.MechanismDesign.stronglyImplementsSCC_singleton
#print axioms MWG.MechanismDesign.StrictlyDominantAction
#print axioms MWG.MechanismDesign.weaklyDominantAction_of_dse
#print axioms MWG.MechanismDesign.strong_of_strictlyDominant
#print axioms MWG.MechanismDesign.strong_of_strictlyDominant_instance
#print axioms MWG.MechanismDesign.weaklyDominant_indifferent
#print axioms MWG.MechanismDesign.dse_outcome_eq
#print axioms MWG.MechanismDesign.strong_of_noIndifference
#print axioms MWG.MechanismDesign.noIndifference_not_strictlyDominant
#print axioms MWG.MechanismDesign.aa1G
#print axioms MWG.MechanismDesign.aa1Mech
#print axioms MWG.MechanismDesign.aa1S
#print axioms MWG.MechanismDesign.exercise_23_AA_1
#print axioms MWG.MechanismDesign.exercise_23_AA_1_direct_not_strong
#print axioms MWG.MechanismDesign.gr_sum_update
#print axioms MWG.MechanismDesign.grovesMech
#print axioms MWG.MechanismDesign.valU
#print axioms MWG.MechanismDesign.groves_payoff
#print axioms MWG.MechanismDesign.exercise_23_AA_2a
#print axioms MWG.MechanismDesign.effChoice
#print axioms MWG.MechanismDesign.effChoice_spec
#print axioms MWG.MechanismDesign.exercise_23_AA_2_instance
#print axioms MWG.MechanismDesign.NormVal
#print axioms MWG.MechanismDesign.normGrovesMech
#print axioms MWG.MechanismDesign.normalize
#print axioms MWG.MechanismDesign.norm_update_coe
#print axioms MWG.MechanismDesign.eff_eq_of_strict_max
#print axioms MWG.MechanismDesign.exercise_23_AA_2b
#print axioms MWG.MechanismDesign.dc_foc_slice
#print axioms MWG.MechanismDesign.dc_integral_slice
#print axioms MWG.MechanismDesign.dc_deriv_nonneg_of_monotoneOn
#print axioms MWG.MechanismDesign.dc_sp_slice_iff
#print axioms MWG.MechanismDesign.dc_implicit
#print axioms MWG.MechanismDesign.dc_implicit_root
#print axioms MWG.MechanismDesign.dc_strict_max
#print axioms MWG.MechanismDesign.dc_groves_slice
#print axioms MWG.MechanismDesign.dc_mixed_pos
#print axioms MWG.MechanismDesign.dc_delta_monotone
#print axioms MWG.MechanismDesign.dc_sign_of_ne
#print axioms MWG.MechanismDesign.SmallTypeEnv
#print axioms MWG.MechanismDesign.SmallTypeEnv.mk
#print axioms MWG.MechanismDesign.SmallTypeEnv.v
#print axioms MWG.MechanismDesign.SmallTypeEnv.vk
#print axioms MWG.MechanismDesign.SmallTypeEnv.vkk
#print axioms MWG.MechanismDesign.SmallTypeEnv.vkθ
#print axioms MWG.MechanismDesign.SmallTypeEnv.hasDerivAt_v
#print axioms MWG.MechanismDesign.SmallTypeEnv.hasDerivAt_vk
#print axioms MWG.MechanismDesign.SmallTypeEnv.hasDerivAt_vkθ
#print axioms MWG.MechanismDesign.SmallTypeEnv.continuous_vk
#print axioms MWG.MechanismDesign.SmallTypeEnv.continuous_vkk
#print axioms MWG.MechanismDesign.SmallTypeEnv.continuous_vkθ
#print axioms MWG.MechanismDesign.SmallTypeEnv.vkk_neg
#print axioms MWG.MechanismDesign.SmallTypeEnv.vkθ_ne
#print axioms MWG.MechanismDesign.quadEnv
#print axioms MWG.MechanismDesign.InBox
#print axioms MWG.MechanismDesign.inBox_update
#print axioms MWG.MechanismDesign.StrategyProofOnBox
#print axioms MWG.MechanismDesign.EfficientOnBox
#print axioms MWG.MechanismDesign.EfficientProject.efficientOnBox
#print axioms MWG.MechanismDesign.strategyProofOnBox_iff
#print axioms MWG.MechanismDesign.sp_slice
#print axioms MWG.MechanismDesign.sum_update_split
#print axioms MWG.MechanismDesign.eq_23_C_13
#print axioms MWG.MechanismDesign.eq_23_C_14
#print axioms MWG.MechanismDesign.efficient_foc
#print axioms MWG.MechanismDesign.eq_23_C_15
#print axioms MWG.MechanismDesign.exercise_23_C_9
#print axioms MWG.MechanismDesign.footnote_23_26
#print axioms MWG.MechanismDesign.sum_erase_update
#print axioms MWG.MechanismDesign.efficient_slice_implicit
#print axioms MWG.MechanismDesign.efficient_slice_continuousOn
#print axioms MWG.MechanismDesign.efficient_slice_hasDerivAt
#print axioms MWG.MechanismDesign.efficient_slice_deriv_ne_zero
#print axioms MWG.MechanismDesign.differentiable_case_groves
#print axioms MWG.MechanismDesign.groves_strategyProofOnBox
#print axioms MWG.MechanismDesign.differentiable_case_groves_iff
#print axioms MWG.MechanismDesign.exercise_23_C_10c_decomposition
#print axioms MWG.MechanismDesign.exercise_23_C_10c
#print axioms MWG.MechanismDesign.exercise_23_C_10c_sufficient
#print axioms MWG.MechanismDesign.vec2_update0
#print axioms MWG.MechanismDesign.vec2_update1
#print axioms MWG.MechanismDesign.vec2_inBox
#print axioms MWG.MechanismDesign.smallTypeEnv_exists_pair
#print axioms MWG.MechanismDesign.smallTypeEnv_strict_max
#print axioms MWG.MechanismDesign.exercise_23_C_10d
#print axioms MWG.MechanismDesign.differentiable_case_no_budget_balance
#print axioms MWG.MechanismDesign.quadK
#print axioms MWG.MechanismDesign.quadK_efficient
#print axioms MWG.MechanismDesign.differentiable_case_instance
#print axioms MWG.MechanismDesign.BargainX
#print axioms MWG.MechanismDesign.bargSellerU
#print axioms MWG.MechanismDesign.bargBuyerU
#print axioms MWG.MechanismDesign.bargOutcome
#print axioms MWG.MechanismDesign.bargSellerVal
#print axioms MWG.MechanismDesign.exercise_23_D_1b
#print axioms MWG.MechanismDesign.discY
#print axioms MWG.MechanismDesign.exercise_23_E_4_payoffs
#print axioms MWG.MechanismDesign.discSurplus
#print axioms MWG.MechanismDesign.exercise_23_E_4_efficient
#print axioms MWG.MechanismDesign.exercise_23_E_4
#print axioms MWG.MechanismDesign.MarketClears
#print axioms MWG.MechanismDesign.exercise_23_E_5a
#print axioms MWG.MechanismDesign.compSellerU
#print axioms MWG.MechanismDesign.compBuyerU
#print axioms MWG.MechanismDesign.exercise_23_E_5b
#print axioms MWG.MechanismDesign.exercise_23_E_6a
#print axioms MWG.MechanismDesign.trade_ii_le
#print axioms MWG.MechanismDesign.partnerEU
#print axioms MWG.MechanismDesign.partnerEU_eq
#print axioms MWG.MechanismDesign.exercise_23_E_6b
#print axioms MWG.MechanismDesign.partnerEU_eq_equilibrium
#print axioms MWG.MechanismDesign.partnerSCF
#print axioms MWG.MechanismDesign.exercise_23_E_6c
#print axioms MWG.MechanismDesign.exercise_23_D_4a
#print axioms MWG.MechanismDesign.exercise_23_D_4b
#print axioms MWG.MechanismDesign.exercise_23_D_4b_strictMono
#print axioms MWG.MechanismDesign.exercise_23_D_4_instance
#print axioms MWG.MechanismDesign.exercise_23_D_4c
#print axioms MWG.MechanismDesign.exercise_23_D_5_monotone
#print axioms MWG.MechanismDesign.exercise_23_D_5
#print axioms MWG.MechanismDesign.queue_bernoulli
#print axioms MWG.MechanismDesign.exercise_23_D_6_bne
#print axioms MWG.MechanismDesign.queueExpectedWait
#print axioms MWG.MechanismDesign.exercise_23_D_6
#print axioms MWG.MechanismDesign.exercise_23_F_2
#print axioms MWG.MechanismDesign.exercise_23_F_2_foc
#print axioms MWG.MechanismDesign.exercise_23_F_2_exclusion
#print axioms MWG.MechanismDesign.exercise_23_F_5a
#print axioms MWG.MechanismDesign.exercise_23_F_5a_foc
#print axioms MWG.MechanismDesign.exercise_23_F_5b
#print axioms MWG.MechanismDesign.bmProfit
#print axioms MWG.MechanismDesign.exercise_23_F_6a
#print axioms MWG.MechanismDesign.exercise_23_F_6a_price
#print axioms MWG.MechanismDesign.exercise_23_F_6a_ir
#print axioms MWG.MechanismDesign.bmWelfare
#print axioms MWG.MechanismDesign.bmVirtual
#print axioms MWG.MechanismDesign.BMFeasible
#print axioms MWG.MechanismDesign.exercise_23_F_6b_objective
#print axioms MWG.MechanismDesign.exercise_23_F_6b
#print axioms MWG.MechanismDesign.exercise_23_F_6b_price
#print axioms MWG.MechanismDesign.exercise_23_F_6b_alpha_ge_one
#print axioms MWG.MechanismDesign.exercise_23_F_6b_printed_unbounded
#print axioms MWG.MechanismDesign.bmFeasible_instance
#print axioms MWG.MechanismDesign.exercise_23_F_7_monopoly
#print axioms MWG.MechanismDesign.exercise_23_F_7_duopoly
#print axioms MWG.MechanismDesign.dsProduces
#print axioms MWG.MechanismDesign.dsGross
#print axioms MWG.MechanismDesign.dsSurplus
#print axioms MWG.MechanismDesign.dsVirtualCost
#print axioms MWG.MechanismDesign.dsVirtualWelfare
#print axioms MWG.MechanismDesign.dsVirtualCost_strictMono
#print axioms MWG.MechanismDesign.exercise_23_F_7
#print axioms MWG.MechanismDesign.TypeDensity.virtualCost
#print axioms MWG.MechanismDesign.mss_integral_below
#print axioms MWG.MechanismDesign.mss_integral_above
#print axioms MWG.MechanismDesign.mss_cdf_of_le
#print axioms MWG.MechanismDesign.mss_cdf_of_ge
#print axioms MWG.MechanismDesign.mss_cdf_lo
#print axioms MWG.MechanismDesign.mss_cdf_hi
#print axioms MWG.MechanismDesign.mss_cdf_pos
#print axioms MWG.MechanismDesign.mss_one_sub_cdf_pos
#print axioms MWG.MechanismDesign.mss_cdf_mem
#print axioms MWG.MechanismDesign.mss_ii_mul_dens
#print axioms MWG.MechanismDesign.mss_ii_cdf
#print axioms MWG.MechanismDesign.mss_integral_cdf
#print axioms MWG.MechanismDesign.mss_integral_key
#print axioms MWG.MechanismDesign.mss_virtualValue_mul
#print axioms MWG.MechanismDesign.mss_virtualCost_mul
#print axioms MWG.MechanismDesign.mss_measurable_virtualValue
#print axioms MWG.MechanismDesign.mss_measurable_virtualCost
#print axioms MWG.MechanismDesign.mss_integrable_of_mul_dens
#print axioms MWG.MechanismDesign.mss_integrable_virtualValue
#print axioms MWG.MechanismDesign.mss_integrable_virtualCost
#print axioms MWG.MechanismDesign.mss_integral_virtualCost
#print axioms MWG.MechanismDesign.mss_expect_mul
#print axioms MWG.MechanismDesign.mss_expected_transfer
#print axioms MWG.MechanismDesign.mss_ybar_ii
#print axioms MWG.MechanismDesign.mss_payment_from_top
#print axioms MWG.MechanismDesign.mss_measurable_vec1
#print axioms MWG.MechanismDesign.mss_measurable_vec0
#print axioms MWG.MechanismDesign.mss_update0
#print axioms MWG.MechanismDesign.mss_update1
#print axioms MWG.MechanismDesign.mss_interimBenefit_seller
#print axioms MWG.MechanismDesign.eq_23_E_5
#print axioms MWG.MechanismDesign.eq_23_E_5_seller_U
#print axioms MWG.MechanismDesign.eq_23_E_6
#print axioms MWG.MechanismDesign.mss_expect_virtualCost
#print axioms MWG.MechanismDesign.eq_23_E_7
#print axioms MWG.MechanismDesign.eq_23_E_sum
#print axioms MWG.MechanismDesign.eq_23_E_4
#print axioms MWG.MechanismDesign.mss_integrable_y_mul
#print axioms MWG.MechanismDesign.mss_step2_inner
#print axioms MWG.MechanismDesign.mss_step2_display1
#print axioms MWG.MechanismDesign.mss_step2_display23
#print axioms MWG.MechanismDesign.mss_step2_display4
#print axioms MWG.MechanismDesign.mss_step2_display5
#print axioms MWG.MechanismDesign.mss_step2_neg
#print axioms MWG.MechanismDesign.mss_step2
#print axioms MWG.MechanismDesign.proposition_23_E_1_mwg
#print axioms MWG.MechanismDesign.eq_23_E_4_instance
#print axioms MWG.MechanismDesign.partnerEULin
#print axioms MWG.MechanismDesign.partnerEULin_two_thirds
#print axioms MWG.MechanismDesign.partnerEULin_eq
#print axioms MWG.MechanismDesign.partner_foc
#print axioms MWG.MechanismDesign.exercise_23_E_6b_unique
#print axioms MWG.MechanismDesign.dsX
#print axioms MWG.MechanismDesign.dsAlloc
#print axioms MWG.MechanismDesign.dsTau
#print axioms MWG.MechanismDesign.dsProfit
#print axioms MWG.MechanismDesign.dsWelfare
#print axioms MWG.MechanismDesign.ds_linU
#print axioms MWG.MechanismDesign.DSFeasible
#print axioms MWG.MechanismDesign.ds_integrable_comp
#print axioms MWG.MechanismDesign.ds_x_mem
#print axioms MWG.MechanismDesign.ds_integrable_x_mul
#print axioms MWG.MechanismDesign.ds_integrable_id
#print axioms MWG.MechanismDesign.ds_gross_eq
#print axioms MWG.MechanismDesign.ds_virtualWelfare_eq
#print axioms MWG.MechanismDesign.exercise_23_F_7_reduction
#print axioms MWG.MechanismDesign.exercise_23_F_7_optimal
#print axioms MWG.MechanismDesign.dsUnif
#print axioms MWG.MechanismDesign.ds_unif_virtualCost
#print axioms MWG.MechanismDesign.exercise_23_F_7_instance
#print axioms MWG.MechanismDesign.ecTransfer
#print axioms MWG.MechanismDesign.ec_integrable_update
#print axioms MWG.MechanismDesign.ec_interimBenefit_abs_le
#print axioms MWG.MechanismDesign.ec_interimBenefit_mono
#print axioms MWG.MechanismDesign.ec_mechanism
#print axioms MWG.MechanismDesign.oaWins
#print axioms MWG.MechanismDesign.oaRule
#print axioms MWG.MechanismDesign.oa_wins_unique
#print axioms MWG.MechanismDesign.oa_exists_wins
#print axioms MWG.MechanismDesign.oaRule_pointwiseOpt
#print axioms MWG.MechanismDesign.oaRule_mono
#print axioms MWG.MechanismDesign.oa_measurable_virtualValue
#print axioms MWG.MechanismDesign.oa_integrable_virtualValue
#print axioms MWG.MechanismDesign.oaRule_measurable
#print axioms MWG.MechanismDesign.example_23_F_2_general
#print axioms MWG.MechanismDesign.example_23_F_2_general_instance
#print axioms MWG.MechanismDesign.dsVW
#print axioms MWG.MechanismDesign.dsRule
#print axioms MWG.MechanismDesign.dsRule_max
#print axioms MWG.MechanismDesign.ds_measurable_virtualCost
#print axioms MWG.MechanismDesign.dsRule_measurable
#print axioms MWG.MechanismDesign.ds_vw_shift
#print axioms MWG.MechanismDesign.dsRule_mono
#print axioms MWG.MechanismDesign.dsRuleT
#print axioms MWG.MechanismDesign.exercise_23_F_7_general
#print axioms MWG.MechanismDesign.exercise_23_F_7_general_instance
#print axioms MWG.MechanismDesign.footnote_23_48
#print axioms MWG.MechanismDesign.oc_instance_argmax
#print axioms MWG.MechanismDesign.footnote_23_48_instance
#print axioms MWG.MechanismDesign.exercise_23_F_1_firstBest
#print axioms MWG.MechanismDesign.exercise_23_F_1_example
#print axioms MWG.MechanismDesign.WcRegular
#print axioms MWG.MechanismDesign.wc_exAnteU_eq_general
#print axioms MWG.MechanismDesign.exercise_23_F_1_exAnte_general
#print axioms MWG.MechanismDesign.exercise_23_F_1_exAnte_general_instance
#print axioms MWG.MechanismDesign.cp_measureReal_Iic
#print axioms MWG.MechanismDesign.cp_measureReal_Iio
#print axioms MWG.MechanismDesign.cp_measureReal_Ioi
#print axioms MWG.MechanismDesign.cp_smul_real
#print axioms MWG.MechanismDesign.cp_cdf_lo_hi
#print axioms MWG.MechanismDesign.exercise_23_E_5_clearing
#print axioms MWG.MechanismDesign.exercise_23_E_5_competitive
#print axioms MWG.MechanismDesign.MtRich
#print axioms MWG.MechanismDesign.mt_counts
#print axioms MWG.MechanismDesign.mt_profile
#print axioms MWG.MechanismDesign.majority_nondictatorial
#print axioms MWG.MechanismDesign.majorityTieTrue
#print axioms MWG.MechanismDesign.majority_tieTrue_nondictatorial
#print axioms MWG.MechanismDesign.majority_tieTrue_strategyProof
#print axioms MWG.MechanismDesign.remark_23_C_majority
#print axioms MWG.MechanismDesign.majorityTieZero
#print axioms MWG.MechanismDesign.majority_two_agents_dictatorial
#print axioms MWG.MechanismDesign.WmOpt
#print axioms MWG.MechanismDesign.WmEq
#print axioms MWG.MechanismDesign.wmCD
#print axioms MWG.MechanismDesign.wmLeontief
#print axioms MWG.MechanismDesign.wm_cd_opt_iff
#print axioms MWG.MechanismDesign.wm_leontief_opt_iff
#print axioms MWG.MechanismDesign.wmU2
#print axioms MWG.MechanismDesign.example_23_B_2_truthful
#print axioms MWG.MechanismDesign.example_23_B_2_misreport
#print axioms MWG.MechanismDesign.example_23_B_2
#print axioms MWG.MechanismDesign.WmLNS
#print axioms MWG.MechanismDesign.wm_cost_ge
#print axioms MWG.MechanismDesign.wm_first_welfare
#print axioms MWG.MechanismDesign.wm_cd_lns
#print axioms MWG.MechanismDesign.wm_leontief_lns
#print axioms MWG.MechanismDesign.example_23_B_2_efficient
