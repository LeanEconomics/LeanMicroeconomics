/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Mechanisms

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
