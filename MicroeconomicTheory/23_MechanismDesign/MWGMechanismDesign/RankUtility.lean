/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.GibbardSatterthwaite

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
