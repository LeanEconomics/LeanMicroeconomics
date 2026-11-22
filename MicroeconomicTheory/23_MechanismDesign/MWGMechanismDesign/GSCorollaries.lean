/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.RankUtility

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
