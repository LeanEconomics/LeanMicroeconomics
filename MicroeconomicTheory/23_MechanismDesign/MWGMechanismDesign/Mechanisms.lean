/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.SocialChoiceFunctions
import Mathlib.Order.Basic

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
