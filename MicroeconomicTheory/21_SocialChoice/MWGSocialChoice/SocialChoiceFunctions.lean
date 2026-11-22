/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.ArrowConditions

/-!
# Social choice functions

MWG, Section 21.E, pp. 807-811: Definitions 21.E.1-21.E.6, Propositions 21.E.1 and 21.E.2 with
the seven-step proof, footnote 15, and Exercises 21.E.1-21.E.4 (pp. 815-816).

A social choice function on a domain `A` is a map `f : Profile ι X → X` (only its values on `A`
matter). We define weak Pareto optimality (21.E.2), maintaining one's position (21.E.3),
monotonicity (21.E.4), dictators (21.E.5) and taking a set to the top (21.E.6), and prove
Proposition 21.E.1 (with at least three alternatives, domain `𝓡^I` or `𝓟^I`, a weakly Paretian
monotonic social choice function is dictatorial) by the book's construction of a social welfare
functional `F` from `f` and Arrow's theorem, Steps 1-7. Profiles taking a set `X'` to the top are
built explicitly (`topProfile`), keeping the order outside `X'`. Proposition 21.E.2: a weakly
Paretian social choice function on `𝓟^I` with no incentive to misrepresent is monotonic, hence
dictatorial; the book's "without loss of generality" single-agent change is an induction over
the set of agents whose preferences change.

**Correction (Exercise 21.E.2).** On `𝓡^I` the "smallest label among agent 1's most preferred
alternatives" rule is dictatorial and weakly Paretian but *not* monotonic (with at least two
alternatives): `exercise_21_E_2_not_monotonic`. On `𝓟^I` it is monotonic, as is every
dictatorial social choice function (MWG, p. 808).
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {ι X : Type*}

/-- **Definition 21.E.2** (MWG, p. 808). `f` is weakly Paretian on `A`: if every agent strictly
prefers `x` to `y`, then `y` is not chosen. -/
def WeaklyParetian (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∀ p ∈ A, ∀ x y, (∀ i, Strict (p i) x y) → y ≠ f p

/-- **Definition 21.E.3** (MWG, p. 808). `x` maintains its position from `p` to `p'`:
`x ≿ᵢ y` implies `x ≿'ᵢ y` for every `i` and `y`. -/
def MaintainsPosition (x : X) (p p' : Profile ι X) : Prop := ∀ i y, p i x y → p' i x y

/-- **Footnote 15** (MWG, p. 808). The lower contour set `L(x, ≿) = {y : x ≿ y}`. -/
def lowerContour (r : X → X → Prop) (x : X) : Set X := {y | r x y}

/-- **Definition 21.E.3** (MWG, p. 808). `x` maintains its position iff every agent's lower
contour set at `x` weakly expands. -/
theorem maintainsPosition_iff (x : X) (p p' : Profile ι X) :
    MaintainsPosition x p p' ↔ ∀ i, lowerContour (p i) x ⊆ lowerContour (p' i) x :=
  ⟨fun h i _ hy => h i _ hy, fun h i _ hy => h i hy⟩

/-- **Definition 21.E.4** (MWG, p. 808). `f` is monotonic on `A`: if the chosen alternative
maintains its position from `p` to `p'` (both in `A`), it is still chosen at `p'`. -/
def Monotonic (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∀ p ∈ A, ∀ p' ∈ A, MaintainsPosition (f p) p p' → f p' = f p

/-- **Definition 21.E.5** (MWG, p. 808). `h` is a dictator for `f`: `f(p)` is a most preferred
alternative for `≿ₕ` at every profile of `A`. -/
def IsSCFDictator (A : Set (Profile ι X)) (f : Profile ι X → X) (h : ι) : Prop :=
  ∀ p ∈ A, ∀ y, p h (f p) y

/-- **Definition 21.E.5** (MWG, p. 808). `f` is dictatorial if it admits a dictator. -/
def DictatorialSCF (A : Set (Profile ι X)) (f : Profile ι X → X) : Prop :=
  ∃ h, IsSCFDictator A f h

/-- **Section 21.E** (MWG, p. 807). With finitely many alternatives, every social welfare
functional `F` on `A` induces a social choice function choosing, at each profile of `A`, a most
preferred alternative for `F(p)`. -/
theorem induced_scf_exists [Finite X] [Nonempty X] {A : Set (Profile ι X)}
    {F : Profile ι X → X → X → Prop} (hF : IsSWF A F) :
    ∃ f : Profile ι X → X, ∀ p ∈ A, ∀ y, F p (f p) y := by
  classical
  have := Fintype.ofFinite X
  have hex : ∀ p, ∃ x, p ∈ A → ∀ y, F p x y := by
    intro p
    by_cases hp : p ∈ A
    · obtain ⟨x, -, hx⟩ := rational_acyclic (hF p hp) univ univ_nonempty
      exact ⟨x, fun _ y => hx y (mem_univ y)⟩
    · obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨x, fun h => absurd h hp⟩
  choose f hf using hex
  exact ⟨f, fun p hp => hf p hp⟩

/-- **Section 21.E** (MWG, p. 807). With an odd number of agents and the domain `𝓟_≥^I`, a
social choice function induced by pairwise majority voting chooses the Condorcet winner. -/
theorem induced_scf_condorcet [Fintype ι] [LinearOrder X] {f : Profile ι X → X}
    (hf : ∀ p ∈ StrictSinglePeakedProfiles ι X, ∀ y, majorityRel p (f p) y) :
    ∀ p ∈ StrictSinglePeakedProfiles ι X, IsCondorcetWinner p (f p) :=
  fun p hp => hf p hp

/-- **Definition 21.E.6** (MWG, p. 809). The profile `p'` takes `X'` to the top from `p`: every
alternative of `X'` is strictly preferred to every alternative outside `X'`, and the ranking
within `X'` is unchanged. -/
def TakesToTop (X' : Set X) (p p' : Profile ι X) : Prop :=
  ∀ i, (∀ x ∈ X', ∀ y ∉ X', Strict (p' i) x y) ∧ (∀ x ∈ X', ∀ y ∈ X', (p i x y ↔ p' i x y))

/-- The profile taking `X'` to the top from `p`, keeping each agent's ranking inside `X'` and
outside `X'`. -/
def topProfile (X' : Set X) (p : Profile ι X) : Profile ι X :=
  fun i a b => (a ∈ X' ∧ b ∈ X' ∧ p i a b) ∨ (a ∈ X' ∧ b ∉ X') ∨ (a ∉ X' ∧ b ∉ X' ∧ p i a b)

/-- `topProfile X' p` takes `X'` to the top from `p`, and stays in `𝓡` (resp. `𝓟`). -/
theorem topProfile_spec (X' : Set X) (p : Profile ι X) :
    TakesToTop X' p (topProfile X' p) ∧
      (∀ i, Rational (p i) → Rational (topProfile X' p i)) ∧
      (∀ i, p i ∈ StrictPrefs X → topProfile X' p i ∈ StrictPrefs X) := by
  have rat : ∀ i, Rational (p i) → Rational (topProfile X' p i) := by
    intro i hr
    refine ⟨fun a b => ?_, fun a b c hab hbc => ?_⟩
    · by_cases ha : a ∈ X' <;> by_cases hb : b ∈ X'
      · rcases hr.1 a b with h | h
        · exact Or.inl (Or.inl ⟨ha, hb, h⟩)
        · exact Or.inr (Or.inl ⟨hb, ha, h⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
      · rcases hr.1 a b with h | h
        · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, h⟩))
    · simp only [topProfile] at hab hbc ⊢
      rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
        rcases hbc with ⟨hb', hc, h2⟩ | ⟨hb', hc⟩ | ⟨hb', hc, h2⟩
      all_goals first
        | exact absurd hb' hb | exact absurd hb hb'
        | exact Or.inl ⟨ha, hc, hr.2 a b c h1 h2⟩
        | exact Or.inr (Or.inl ⟨ha, hc⟩)
        | exact Or.inr (Or.inr ⟨ha, hc, hr.2 a b c h1 h2⟩)
  refine ⟨fun i => ⟨fun x hx y hy => ⟨Or.inr (Or.inl ⟨hx, hy⟩), fun h => ?_⟩,
    fun x hx y hy => ?_⟩, rat, fun i hi => ⟨rat i hi.1, fun a b hab hba => ?_⟩⟩
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩
    · exact hy h1
    · exact hy h1
    · exact h1 hx
  · simp only [topProfile]
    constructor
    · exact fun h => Or.inl ⟨hx, hy, h⟩
    · rintro (⟨-, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd hy h
      · exact absurd hx h
  · simp only [topProfile] at hab hba
    rcases hab with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
      rcases hba with ⟨hb', ha', h2⟩ | ⟨hb', ha'⟩ | ⟨hb', ha', h2⟩
    all_goals first
      | exact hi.2 a b h1 h2
      | (exfalso; tauto)

/-- **Section 21.E** (MWG, p. 809). If `p'` takes `X'` to the top from `p`, every `x ∈ X'`
maintains its position from `p` to `p'`. -/
theorem TakesToTop.maintains {X' : Set X} {p p' : Profile ι X} (h : TakesToTop X' p p') {x : X}
    (hx : x ∈ X') : MaintainsPosition x p p' := by
  intro i y hy
  by_cases hyX : y ∈ X'
  · exact ((h i).2 x hx y hyX).1 hy
  · exact ((h i).1 x hx y hyX).1

/-- Taking `Y` to the top and then `X' ⊆ Y` to the top takes `X'` to the top. -/
theorem TakesToTop.trans {X' Y : Set X} {p q r : Profile ι X} (hq : TakesToTop Y p q)
    (hr : TakesToTop X' q r) (hXY : X' ⊆ Y) : TakesToTop X' p r :=
  fun i => ⟨(hr i).1, fun x hx y hy => ((hq i).2 x (hXY hx) y (hXY hy)).trans ((hr i).2 x hx y hy)⟩

/-- **Section 21.E** (MWG, p. 809). The illustration of Definition 21.E.6: from
`x ≻ y ≻ z ≻ w`, the preference `y ≻' w ≻' z ≻' x` takes `{y, w}` to the top (alternatives
`x, y, z, w = 0, 1, 2, 3`, one agent). -/
theorem definition_21_E_6_example :
    TakesToTop ({1, 3} : Set (Fin 4)) (fun _ : Fin 1 => natPref ![4, 3, 2, 1])
      (fun _ => natPref ![1, 4, 2, 3]) := by
  intro _
  refine ⟨fun x hx y hy => (natPref_strict_iff _ _ _).2 ?_, fun x hx y hy => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    fin_cases x <;> fin_cases y <;> simp_all
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [natPref]

variable {A : Set (Profile ι X)} {f : Profile ι X → X}

/-- A weakly Paretian social choice function chooses inside `X'` at any profile of `A` that takes
the nonempty set `X'` to the top. -/
theorem WeaklyParetian.mem_top (hW : WeaklyParetian A f) {X' : Set X} (hne : X'.Nonempty)
    {p p' : Profile ι X} (hp' : p' ∈ A) (h : TakesToTop X' p p') : f p' ∈ X' := by
  by_contra hn
  obtain ⟨x, hx⟩ := hne
  exact hW p' hp' x (f p') (fun i => (h i).1 x hx _ hn) rfl

/-- **Step 1** of the proof of Proposition 21.E.1 (MWG, p. 809). If two profiles of `A` take
the nonempty set `X'` to the top from `p`, then `f` chooses the same alternative at both. -/
theorem scf_step_1 (hW : WeaklyParetian A f) (hM : Monotonic A f) {X' : Set X}
    (hne : X'.Nonempty) {p p' p'' : Profile ι X} (hp' : p' ∈ A) (hp'' : p'' ∈ A)
    (h' : TakesToTop X' p p') (h'' : TakesToTop X' p p'') : f p' = f p'' := by
  have hx := hW.mem_top hne hp' h'
  refine (hM p' hp' p'' hp'' fun i y hy => ?_).symm
  by_cases hyX : y ∈ X'
  · exact ((h'' i).2 _ hx y hyX).1 (((h' i).2 _ hx y hyX).2 hy)
  · exact ((h'' i).1 _ hx y hyX).1

/-- **Step 2** of the proof of Proposition 21.E.1 (MWG, p. 809). The social relation built
from `f`: `x` is socially at least as good as `y` iff `x = y` or `x` is chosen at the profile
taking `{x, y}` to the top. (By Step 1 any such profile may be used: `scf_step_2`.) -/
def scfRelation (f : Profile ι X → X) (p : Profile ι X) (x y : X) : Prop :=
  x = y ∨ x = f (topProfile {x, y} p)

/-- **Step 2** of the proof of Proposition 21.E.1 (MWG, p. 809). `scfRelation` is well defined:
any profile of `A` taking `{x, y}` to the top from `p` gives the same choice. -/
theorem scf_step_2 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p p' : Profile ι X} (hp : p ∈ A) (hp' : p' ∈ A) {x y : X}
    (h' : TakesToTop {x, y} p p') : f p' = f (topProfile {x, y} p) := by
  have htop := topProfile_spec ({x, y} : Set X) p
  have hmem : topProfile {x, y} p ∈ A := by
    rcases hA with rfl | rfl
    · exact fun i => htop.2.1 i (hp i)
    · exact fun i => htop.2.2 i (hp i)
  exact scf_step_1 hW hM ⟨x, Or.inl rfl⟩ hp' hmem h' htop.1

/-- Profiles taking a set to the top stay in a standard domain. -/
theorem StandardDomain.topProfile_mem (hA : StandardDomain A) {p : Profile ι X} (hp : p ∈ A)
    (X' : Set X) : topProfile X' p ∈ A := by
  have htop := topProfile_spec X' p
  rcases hA with rfl | rfl
  · exact fun i => htop.2.1 i (hp i)
  · exact fun i => htop.2.2 i (hp i)

/-- The alternative chosen at the profile taking `{x, y}` to the top is `x` or `y`. -/
theorem scf_choice_pair (hA : StandardDomain A) (hW : WeaklyParetian A f) {p : Profile ι X}
    (hp : p ∈ A) (x y : X) : f (topProfile {x, y} p) = x ∨ f (topProfile {x, y} p) = y :=
  hW.mem_top (X' := {x, y}) ⟨x, Or.inl rfl⟩ (hA.topProfile_mem hp _) (topProfile_spec _ p).1

/-- Part of **Step 3** of the proof of Proposition 21.E.1 (MWG, p. 810): if `x` is socially at
least as good as `y` and `x ≠ y`, then `y` is not chosen at a profile `p''` taking a superset
`Y ⊇ {x, y}` to the top. -/
theorem scf_not_chosen (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) {x y : X} (hxy : x ≠ y) (h : scfRelation f p x y)
    {Y : Set X} (hY : ({x, y} : Set X) ⊆ Y) {p'' : Profile ι X} (hp'' : p'' ∈ A)
    (h'' : TakesToTop Y p p'') : y ≠ f p'' := by
  intro hy
  have hfx : f (topProfile {x, y} p) = x := (h.resolve_left hxy).symm
  have htop := topProfile_spec ({x, y} : Set X) p''
  have hp' := hA.topProfile_mem hp'' ({x, y} : Set X)
  have h1 : f (topProfile {x, y} p'') = y := by
    rw [hM p'' hp'' _ hp' (hy ▸ htop.1.maintains (Or.inr rfl))]
    exact hy.symm
  have h2 : TakesToTop {x, y} p (topProfile {x, y} p'') := h''.trans htop.1 hY
  rw [scf_step_2 hA hW hM hp hp' h2, hfx] at h1
  exact hxy h1

/-- **Step 3** of the proof of Proposition 21.E.1 (MWG, pp. 809-810). For every profile of `A`,
the social relation is complete and transitive and no two distinct alternatives are socially
indifferent: it lies in `𝓟`. -/
theorem scf_step_3 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) : scfRelation f p ∈ StrictPrefs X := by
  have hnoind : NoIndifference (scfRelation f p) := by
    intro x y hxy hyx
    by_contra hne
    have h1 : f (topProfile {x, y} p) = x := (hxy.resolve_left hne).symm
    have h2 : f (topProfile {y, x} p) = y := (hyx.resolve_left (Ne.symm hne)).symm
    rw [Set.pair_comm, h1] at h2
    exact hne h2
  refine ⟨⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩, hnoind⟩
  · rcases scf_choice_pair hA hW hp x y with h | h
    · exact Or.inl (Or.inr h.symm)
    · refine Or.inr (Or.inr ?_)
      rw [Set.pair_comm]
      exact h.symm
  · by_cases e1 : x = y
    · subst e1
      exact hyz
    by_cases e2 : y = z
    · subst e2
      exact hxy
    by_cases e3 : x = z
    · exact Or.inl e3
    set p'' := topProfile ({x, y, z} : Set X) p with hp''
    have hp''A : p'' ∈ A := hA.topProfile_mem hp _
    have h'' : TakesToTop {x, y, z} p p'' := (topProfile_spec _ p).1
    have hmem : f p'' ∈ ({x, y, z} : Set X) := hW.mem_top ⟨x, Or.inl rfl⟩ hp''A h''
    have hny : y ≠ f p'' := scf_not_chosen hA hW hM hp e1 hxy
      (by intro a ha; rcases ha with rfl | rfl <;> simp) hp''A h''
    have hnz : z ≠ f p'' := scf_not_chosen hA hW hM hp e2 hyz
      (by intro a ha; rcases ha with rfl | rfl <;> simp) hp''A h''
    have hfx : f p'' = x := by
      rcases hmem with h | h | h
      · exact h
      · exact absurd h.symm hny
      · exact absurd (Set.mem_singleton_iff.1 h).symm hnz
    refine Or.inr ?_
    have htop := topProfile_spec ({x, z} : Set X) p''
    have hp' := hA.topProfile_mem hp''A ({x, z} : Set X)
    have hsub : ({x, z} : Set X) ⊆ {x, y, z} := by
      intro a ha
      rcases ha with rfl | rfl <;> simp
    have h1 : f (topProfile {x, z} p'') = x := by
      rw [hM p'' hp''A _ hp' (hfx ▸ htop.1.maintains (Or.inl rfl))]
      exact hfx
    have h2 := scf_step_2 hA hW hM hp hp' (h''.trans htop.1 hsub)
    rw [← h2, h1]

/-- **Exercise 21.E.3** (MWG, p. 816). The case of the pair `{y, z}` in Step 3: if
`y F(≿) z` with `y ≠ z`, then `z` is not chosen at the profile taking `{x, y, z}` to the top. -/
theorem exercise_21_E_3 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) {x y z : X} (hyz : y ≠ z) (h : scfRelation f p y z) :
    z ≠ f (topProfile {x, y, z} p) :=
  scf_not_chosen hA hW hM hp hyz h (by intro a ha; rcases ha with rfl | rfl <;> simp)
    (hA.topProfile_mem hp _) (topProfile_spec _ p).1

/-- **Step 4** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation
rationalizes `f`: `f(p)` is a most preferred alternative for it. -/
theorem scf_step_4 (hA : StandardDomain A) (hM : Monotonic A f)
    {p : Profile ι X} (hp : p ∈ A) (y : X) : scfRelation f p (f p) y := by
  by_cases hy : f p = y
  · exact Or.inl hy
  refine Or.inr ?_
  have htop := topProfile_spec ({f p, y} : Set X) p
  exact (hM p hp _ (hA.topProfile_mem hp _) (htop.1.maintains (Or.inl rfl))).symm

/-- **Step 5** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation is
Paretian. -/
theorem scf_step_5 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    Paretian A (scfRelation f) := by
  intro p hp x y hall
  by_cases hxy : x = y
  · subst hxy
    have hι : IsEmpty ι := ⟨fun i => (hall i).2 (hall i).1⟩
    exact absurd rfl (hW p hp x (f p) fun i => hι.elim i)
  have htop := topProfile_spec ({x, y} : Set X) p
  have hmemA := hA.topProfile_mem hp ({x, y} : Set X)
  have hstrict : ∀ i, Strict (topProfile {x, y} p i) x y := fun i =>
    ⟨((htop.1 i).2 x (Or.inl rfl) y (Or.inr rfl)).1 (hall i).1,
      fun h => (hall i).2 (((htop.1 i).2 y (Or.inr rfl) x (Or.inl rfl)).2 h)⟩
  have hfx : f (topProfile {x, y} p) = x :=
    (scf_choice_pair hA hW hp x y).resolve_right fun h => hW _ hmemA x y hstrict h.symm
  have hrel : scfRelation f p x y := Or.inr hfx.symm
  exact ⟨hrel, fun h => hxy ((scf_step_3 hA hW hM hp).2 x y hrel h)⟩

/-- **Step 6** of the proof of Proposition 21.E.1 (MWG, p. 810). The social relation satisfies
the pairwise independence condition. -/
theorem scf_step_6 (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    PairwiseIndependent A (scfRelation f) := by
  intro p hp p' hp' x y hag
  have hrefl : ∀ i a, p i a a ∧ p' i a a := fun i a =>
    ⟨complete_refl (hA.rational hp i).1 a, complete_refl (hA.rational hp' i).1 a⟩
  have htop := topProfile_spec ({x, y} : Set X) p
  have hT : TakesToTop {x, y} p' (topProfile {x, y} p) := by
    intro i
    refine ⟨(htop.1 i).1, fun a ha b hb => ?_⟩
    refine Iff.trans ?_ ((htop.1 i).2 a ha b hb)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact iff_of_true (hrefl i _).2 (hrefl i _).1
    · exact (hag i).1.symm
    · exact (hag i).2.symm
    · exact iff_of_true (hrefl i _).2 (hrefl i _).1
  have heq : f (topProfile {x, y} p) = f (topProfile {x, y} p') :=
    scf_step_2 hA hW hM hp' (hA.topProfile_mem hp _) hT
  have heq' : f (topProfile {y, x} p) = f (topProfile {y, x} p') := by
    rw [Set.pair_comm, heq]
  simp only [scfRelation, heq, heq', and_self]

/-- **Step 7** of the proof of Proposition 21.E.1 (MWG, pp. 810-811), and **Proposition 21.E.1**
(MWG, p. 809). With finitely many agents, at least three alternatives and domain `𝓡^I` or
`𝓟^I`, every weakly Paretian and monotonic social choice function is dictatorial. -/
theorem proposition_21_E_1 [Finite ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hA : StandardDomain A) (hW : WeaklyParetian A f) (hM : Monotonic A f) :
    DictatorialSCF A f := by
  have hF : IsSWF A (scfRelation f) := fun p hp => (scf_step_3 hA hW hM hp).1
  obtain ⟨h, hh⟩ := proposition_21_C_1 hX hA hF (scf_step_5 hA hW hM) (scf_step_6 hA hW hM)
  refine ⟨h, fun p hp y => ?_⟩
  by_contra hn
  have hs : Strict (p h) y (f p) := ⟨((hA.rational hp h).1 _ _).resolve_left hn, hn⟩
  exact (hh p hp y (f p) hs).2 (scf_step_4 hA hM hp y)

/-- **Proposition 21.E.1**, non-vacuity (MWG, p. 809). On `𝓟^I` the dictatorial social choice
function "agent `h`'s most preferred alternative" is weakly Paretian and monotonic (MWG,
p. 808; Exercise 21.E.2, second part): the hypotheses have instances and the conclusion is
attained. -/
theorem dictatorial_strict_spec {f : Profile ι X → X} {h : ι}
    (hf : IsSCFDictator (StrictProfiles ι X) f h) :
    WeaklyParetian (StrictProfiles ι X) f ∧ Monotonic (StrictProfiles ι X) f := by
  refine ⟨fun p hp x y hall hy => (hall h).2 (hy ▸ hf p hp x), fun p hp p' hp' hmain => ?_⟩
  by_contra hne
  have h1 : p' h (f p) (f p') := hmain h _ (hf p hp _)
  exact hne ((hp' h).2 _ _ (hf p' hp' _) h1)

/-- The agent-`h` choice from a nonempty finite set of alternatives: the alternative with
smallest label among `h`'s most preferred ones (Exercise 21.E.2), with `0` as a default. -/
noncomputable def smallestTopLabel {N : ℕ} [NeZero N] (h : ι) (p : Profile ι (Fin N)) :
    Fin N :=
  by classical exact
    if hne : (univ.filter fun x => ∀ y, p h x y).Nonempty then
      (univ.filter fun x => ∀ y, p h x y).min' hne else 0

/-- The smallest-label rule chooses one of agent `h`'s most preferred alternatives. -/
theorem smallestTopLabel_spec {N : ℕ} [NeZero N] (h : ι) {p : Profile ι (Fin N)}
    (hp : Rational (p h)) :
    (∀ y, p h (smallestTopLabel h p) y) ∧
      ∀ x, (∀ y, p h x y) → smallestTopLabel h p ≤ x := by
  classical
  obtain ⟨m, -, hm⟩ := rational_acyclic hp univ univ_nonempty
  have hne : (univ.filter fun x => ∀ y, p h x y).Nonempty :=
    ⟨m, by simpa using fun y => hm y (mem_univ y)⟩
  have e : smallestTopLabel h p = (univ.filter fun x => ∀ y, p h x y).min' hne := by
    unfold smallestTopLabel
    simp only [hne, ↓reduceDIte]
  rw [e]
  refine ⟨fun y => ?_, fun x hx => min'_le _ _ (by simpa using hx)⟩
  have := min'_mem _ hne
  simp only [mem_filter, mem_univ, true_and] at this
  exact this y

/-- **Exercise 21.E.2** (MWG, p. 816), first part. On `𝓡^I`, the smallest-label rule of agent
`h` is dictatorial and weakly Paretian. -/
theorem exercise_21_E_2_dictatorial {N : ℕ} [NeZero N] (h : ι) :
    IsSCFDictator (RationalProfiles ι (Fin N)) (smallestTopLabel h) h ∧
      WeaklyParetian (RationalProfiles ι (Fin N)) (smallestTopLabel h) := by
  refine ⟨fun p hp y => (smallestTopLabel_spec h (hp h)).1 y, fun p hp x y hall hy => ?_⟩
  exact (hall h).2 (hy ▸ (smallestTopLabel_spec h (hp h)).1 x)

/-- **Exercise 21.E.2** (MWG, p. 816), correction. On `𝓡^I` the smallest-label rule is not
monotonic as soon as there are two alternatives: if agent `h` has `1 ≻ 0` the rule picks `1`;
if `h` becomes indifferent between `0` and `1` (so that `1` maintains its position), it picks
`0`. -/
theorem exercise_21_E_2_not_monotonic {N : ℕ} [NeZero N] (hN : 2 ≤ N) (h : ι) :
    ¬Monotonic (RationalProfiles ι (Fin N)) (smallestTopLabel h) := by
  classical
  intro hM
  let one : Fin N := ⟨1, by omega⟩
  let u : Fin N → ℕ := fun x => if x = one then 2 else if x = 0 then 1 else 0
  let u' : Fin N → ℕ := fun x => if x = one ∨ x = 0 then 2 else 0
  have h10 : one ≠ 0 := by
    intro e
    have := congrArg Fin.val e
    simp [one] at this
  let p : Profile ι (Fin N) := fun _ => natPref u
  let p' : Profile ι (Fin N) := fun _ => natPref u'
  have hp : p ∈ RationalProfiles ι (Fin N) := fun _ => natPref_rational _
  have hp' : p' ∈ RationalProfiles ι (Fin N) := fun _ => natPref_rational _
  have hfp : smallestTopLabel h p = one := by
    have hs := (smallestTopLabel_spec h (hp h)).1 one
    change u one ≤ u (smallestTopLabel h p) at hs
    have hu1 : u one = 2 := by simp [u]
    by_contra hne
    have : u (smallestTopLabel h p) ≤ 1 := by
      simp only [u]
      split_ifs <;> simp_all
    omega
  have hfp' : smallestTopLabel h p' = 0 := by
    have hs := smallestTopLabel_spec h (hp' h)
    have h0 : ∀ y, p' h 0 y := fun y => by
      simp only [p', natPref, u']
      split_ifs <;> simp_all
    exact le_antisymm (hs.2 0 h0) (Fin.zero_le _)
  have hmain : MaintainsPosition (smallestTopLabel h p) p p' := by
    rw [hfp]
    intro i y _
    simp only [p', natPref, u']
    split_ifs <;> simp_all
  have := hM p hp p' hp' hmain
  rw [hfp, hfp'] at this
  exact h10 this.symm

/-- **Exercise 21.E.2** (MWG, p. 816), the domain `𝓟^I`. There the smallest-label rule is
dictatorial, weakly Paretian and monotonic. -/
theorem exercise_21_E_2_strict {N : ℕ} [NeZero N] (h : ι) :
    IsSCFDictator (StrictProfiles ι (Fin N)) (smallestTopLabel h) h ∧
      WeaklyParetian (StrictProfiles ι (Fin N)) (smallestTopLabel h) ∧
      Monotonic (StrictProfiles ι (Fin N)) (smallestTopLabel h) := by
  have hd : IsSCFDictator (StrictProfiles ι (Fin N)) (smallestTopLabel h) h :=
    fun p hp y => (smallestTopLabel_spec h (hp h).1).1 y
  exact ⟨hd, dictatorial_strict_spec hd⟩

/-- **Proposition 21.E.2** (MWG, p. 811). The no-incentive-to-misrepresent condition on `𝓟^I`:
no agent `h` with true preference `≿ₕ` gains by reporting any `≿'ₕ ∈ 𝓟` instead. -/
def NoIncentiveToMisrepresent [DecidableEq ι] (f : Profile ι X → X) : Prop :=
  ∀ p ∈ StrictProfiles ι X, ∀ h, ∀ r ∈ StrictPrefs X, p h (f p) (f (Function.update p h r))

/-- The single-agent step of the proof of Proposition 21.E.2 (MWG, p. 811): if the chosen
alternative maintains its position when agent `a` alone changes preferences, the choice does
not change. -/
theorem no_incentive_step [DecidableEq ι] {f : Profile ι X → X}
    (hf : NoIncentiveToMisrepresent f) {q : Profile ι X} (hq : q ∈ StrictProfiles ι X) {a : ι}
    {r : X → X → Prop} (hr : r ∈ StrictPrefs X)
    (hmain : MaintainsPosition (f q) q (Function.update q a r)) :
    f (Function.update q a r) = f q := by
  have hq' : Function.update q a r ∈ StrictProfiles ι X := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa using hr
    · simpa [Function.update_of_ne hi] using hq i
  by_contra hne
  by_cases hyx : Strict (q a) (f (Function.update q a r)) (f q)
  · exact hyx.2 (hf q hq a r hr)
  · have hxy : q a (f q) (f (Function.update q a r)) := weak_of_not_strict (hq a).1.1 hyx
    have h1 : r (f q) (f (Function.update q a r)) := by
      simpa using hmain a _ hxy
    have h2 := hf _ hq' a (q a) (hq a)
    rw [Function.update_idem, Function.update_eq_self] at h2
    simp only [Function.update_self] at h2
    exact hne ((hr.2 _ _ h2 h1))

/-- **Proposition 21.E.2** (MWG, p. 811), main step. A social choice function on `𝓟^I` with no
incentive to misrepresent is monotonic (agents' preferences are changed one at a time). -/
theorem monotonic_of_noIncentive [Finite ι] [DecidableEq ι] {f : Profile ι X → X}
    (hf : NoIncentiveToMisrepresent f) : Monotonic (StrictProfiles ι X) f := by
  have := Fintype.ofFinite ι
  intro p hp p' hp' hmain
  let q : Finset ι → Profile ι X := fun S i => if i ∈ S then p' i else p i
  have hqmem : ∀ S, q S ∈ StrictProfiles ι X := fun S i => by
    by_cases hi : i ∈ S
    · simpa [q, hi] using hp' i
    · simpa [q, hi] using hp i
  have key : ∀ S, f (q S) = f p := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert a S haS ih =>
      have hupd : q (insert a S) = Function.update (q S) a (p' a) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [q]
        · simp [q, hi]
      rw [hupd]
      rw [← ih]
      refine no_incentive_step hf (hqmem S) (hp' a) fun i y hy => ?_
      rw [ih] at hy ⊢
      by_cases hi : i = a
      · subst hi
        simp only [Function.update_self]
        have : q S i = p i := by simp [q, haS]
        rw [this] at hy
        exact hmain i y hy
      · rwa [Function.update_of_ne hi]
  have huniv : q univ = p' := by
    funext i
    simp [q]
  rw [← huniv]
  exact key univ

/-- **Proposition 21.E.2** (MWG, p. 811). With finitely many agents and at least three
alternatives, a weakly Paretian social choice function on `𝓟^I` satisfying the
no-incentive-to-misrepresent condition is dictatorial. -/
theorem proposition_21_E_2 [Finite ι] [DecidableEq ι] (hX : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {f : Profile ι X → X} (hW : WeaklyParetian (StrictProfiles ι X) f)
    (hf : NoIncentiveToMisrepresent f) : DictatorialSCF (StrictProfiles ι X) f :=
  proposition_21_E_1 hX (Or.inr rfl) hW (monotonic_of_noIncentive hf)

/-- **Proposition 21.E.2**, non-vacuity (MWG, p. 811). The dictatorial smallest-label rule of
agent `h` is weakly Paretian on `𝓟^I` and gives no agent an incentive to misrepresent. -/
theorem smallestTopLabel_noIncentive [DecidableEq ι] {N : ℕ} [NeZero N] (h : ι) :
    WeaklyParetian (StrictProfiles ι (Fin N)) (smallestTopLabel h) ∧
      NoIncentiveToMisrepresent (X := Fin N) (smallestTopLabel h) := by
  refine ⟨(exercise_21_E_2_strict h).2.1, fun p hp k r _ => ?_⟩
  by_cases hk : k = h
  · subst hk
    exact (smallestTopLabel_spec k (hp k).1).1 _
  · have : smallestTopLabel h (Function.update p k r) = smallestTopLabel h p := by
      unfold smallestTopLabel
      rw [Function.update_of_ne (Ne.symm hk)]
    rw [this]
    exact complete_refl (hp k).1.1 _

/-- With an odd number of agents and preferences in `𝓟`, a Condorcet winner is unique. -/
theorem condorcetWinner_unique [Fintype ι] {p : Profile ι X} (hp : p ∈ StrictProfiles ι X)
    (hodd : Odd (Fintype.card ι)) {x y : X} (hx : IsCondorcetWinner p x)
    (hy : IsCondorcetWinner p y) : x = y := by
  classical
  by_contra hne
  have h1 := hx y
  have h2 := hy x
  rw [majorityRel_iff] at h1 h2
  exact strict_majority_odd hp hodd hne (by omega)

/-- The Condorcet-winner social choice function (Exercise 21.E.1): a Condorcet winner when one
exists. -/
noncomputable def condorcetSCF [Fintype ι] [Nonempty X] (p : Profile ι X) : X :=
  Classical.epsilon (IsCondorcetWinner p)

/-- **Exercise 21.E.1** (MWG, p. 815). With an odd number of agents and the domain `𝓟_≥^I`, the
social choice function assigning the Condorcet winner to every profile is weakly Paretian and
monotonic. (Finiteness of `X` is not needed.) -/
theorem exercise_21_E_1 [Fintype ι] [LinearOrder X] [Nonempty X]
    (hodd : Odd (Fintype.card ι)) :
    WeaklyParetian (StrictSinglePeakedProfiles ι X) condorcetSCF ∧
      Monotonic (StrictSinglePeakedProfiles ι X) condorcetSCF := by
  classical
  have hcw : ∀ p ∈ StrictSinglePeakedProfiles ι X, IsCondorcetWinner p (condorcetSCF p) :=
    fun p hp => Classical.epsilon_spec
      (proposition_21_D_1_exists (strictSinglePeaked_subset hp))
  refine ⟨fun p hp x y hall hy => ?_, fun p hp p' hp' hmain => ?_⟩
  · have h1 := hcw p hp x
    rw [← hy, majorityRel_iff] at h1
    have e1 : (univ.filter fun i => Strict (p i) x y) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact hall i
    have e2 : (univ.filter fun i => Strict (p i) y x) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact strict_asymm (hall i)
    rw [e1, e2, card_empty, card_univ] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  · set x := condorcetSCF p
    have hsp := strictSinglePeaked_subset_strict hp'
    have hcw' : IsCondorcetWinner p' x := by
      intro y
      by_cases hxy : x = y
      · subst hxy
        rw [majorityRel_iff]
      have h1 : majorityRel p x y := hcw p hp y
      rw [majorityRel_iff] at h1 ⊢
      have s1 : (univ.filter fun i => Strict (p i) x y) ⊆
          univ.filter fun i => Strict (p' i) x y := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨mem_univ i, hmain i y hi.2.1, fun h => hxy ((hsp i).2 x y (hmain i y hi.2.1) h)⟩
      have s2 : (univ.filter fun i => Strict (p' i) y x) ⊆
          univ.filter fun i => Strict (p i) y x := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨mem_univ i, ((hp i).1.1.1 y x).resolve_right fun h => hi.2.2 (hmain i y h),
          fun h => hi.2.2 (hmain i y h)⟩
      have := card_le_card s1
      have := card_le_card s2
      omega
    exact condorcetWinner_unique hsp hodd (hcw p' hp') hcw'

/-- The parity rule over two alternatives `0, 1` (Exercise 21.E.4): `0` is socially preferred
iff an odd number of agents prefer `0` to `1`. -/
noncomputable def parityRule [Fintype ι] (p : Profile ι (Fin 2)) (a b : Fin 2) : Prop :=
  by classical exact
    a = b ∨ (a = 0 ∧ b = 1 ∧ Odd (univ.filter fun i => Strict (p i) 0 1).card) ∨
      (a = 1 ∧ b = 0 ∧ ¬Odd (univ.filter fun i => Strict (p i) 0 1).card)

/-- **Exercise 21.E.4**, two alternatives (MWG, p. 816). With three agents and `𝓐 = 𝓟^I`, the
parity rule is a Paretian, pairwise independent social welfare functional `𝓐 → 𝓟`, and no
social choice function selecting its most preferred alternative is monotonic. -/
theorem exercise_21_E_4_two :
    (∀ p ∈ StrictProfiles (Fin 3) (Fin 2), parityRule p ∈ StrictPrefs (Fin 2)) ∧
      Paretian (StrictProfiles (Fin 3) (Fin 2)) parityRule ∧
      PairwiseIndependent (StrictProfiles (Fin 3) (Fin 2)) parityRule ∧
      ∀ f : Profile (Fin 3) (Fin 2) → Fin 2,
        (∀ p ∈ StrictProfiles (Fin 3) (Fin 2), ∀ y, parityRule p (f p) y) →
          ¬Monotonic (StrictProfiles (Fin 3) (Fin 2)) f := by
  classical
  have hP : ∀ p : Profile (Fin 3) (Fin 2), parityRule p ∈ StrictPrefs (Fin 2) := by
    intro p
    unfold parityRule
    by_cases ho : Odd (univ.filter fun i => Strict (p i) 0 1).card
    · refine ⟨⟨fun a b => ?_, fun a b c => ?_⟩, fun a b => ?_⟩ <;> simp only [ho] <;>
        fin_cases a <;> fin_cases b <;> (try fin_cases c) <;> simp
    · refine ⟨⟨fun a b => ?_, fun a b c => ?_⟩, fun a b => ?_⟩ <;> simp only [ho] <;>
        fin_cases a <;> fin_cases b <;> (try fin_cases c) <;> simp
  have hcount : ∀ p p' : Profile (Fin 3) (Fin 2),
      (univ.filter fun i => Strict (p i) 0 1) = (univ.filter fun i => Strict (p' i) 0 1) →
        parityRule p = parityRule p' := by
    intro p p' h
    unfold parityRule
    rw [h]
  refine ⟨fun p _ => hP p, fun p _ a b hall => ?_, fun p _ p' _ x y hag => ?_, fun f hf hM => ?_⟩
  · have hab : a ≠ b := fun e => (hall 0).2 (e ▸ (hall 0).1)
    have hP' := hP p
    have hrel : parityRule p a b := by
      unfold parityRule
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · have e : (univ.filter fun i => Strict (p i) 0 1) = univ := by
          ext i
          rw [mem_filter]
          simpa using hall i
        rw [e]
        right; left
        exact ⟨rfl, rfl, by decide⟩
      · have e : (univ.filter fun i => Strict (p i) 0 1) = ∅ := by
          ext i
          rw [mem_filter]
          simpa using strict_asymm (hall i)
        rw [e]
        right; right
        exact ⟨rfl, rfl, by decide⟩
      · exact absurd rfl hab
    exact ⟨hrel, fun h => hab (hP'.2 a b hrel h)⟩
  · by_cases hxy : x = y
    · subst hxy
      have h1 : parityRule p x x := by unfold parityRule; exact Or.inl rfl
      have h2 : parityRule p' x x := by unfold parityRule; exact Or.inl rfl
      exact ⟨iff_of_true h1 h2, iff_of_true h1 h2⟩
    have hxy' : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by omega
    have h01 : ∀ i, (p i 0 1 ↔ p' i 0 1) ∧ (p i 1 0 ↔ p' i 1 0) := by
      rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hag
      · exact fun i => ⟨(hag i).2, (hag i).1⟩
    have e : (univ.filter fun i => Strict (p i) 0 1) = univ.filter fun i => Strict (p' i) 0 1 := by
      ext i
      rw [mem_filter, mem_filter]
      simp only [Strict, (h01 i).1, (h01 i).2]
    rw [hcount p p' e]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · let u : Fin 2 → ℕ := ![1, 0]
    let v : Fin 2 → ℕ := ![0, 1]
    let p : Profile (Fin 3) (Fin 2) := fun i => natPref (if i = 0 then u else v)
    let p' : Profile (Fin 3) (Fin 2) := fun i => natPref (if i = 2 then v else u)
    have hp : p ∈ StrictProfiles (Fin 3) (Fin 2) := fun i => by
      by_cases hi : i = 0
      · simp only [p, hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
      · simp only [p, hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
    have hp' : p' ∈ StrictProfiles (Fin 3) (Fin 2) := fun i => by
      by_cases hi : i = 2
      · simp only [p', hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
      · simp only [p', hi, ↓reduceIte]
        exact natPref_mem_strict (by decide)
    have c1 : (univ.filter fun i => Strict (p i) 0 1) = {0} := by
      ext i
      rw [mem_filter]
      fin_cases i <;> simp [p, u, v, natPref_strict_iff]
    have c2 : (univ.filter fun i => Strict (p' i) 0 1) = {0, 1} := by
      ext i
      rw [mem_filter]
      fin_cases i <;> simp [p', u, v, natPref_strict_iff]
    have hfp : f p = 0 := by
      have h := hf p hp 0
      by_contra hne
      have h1 : f p = 1 := by omega
      rw [h1] at h
      unfold parityRule at h
      rw [c1] at h
      simp at h
    have hfp' : f p' = 1 := by
      have h := hf p' hp' 1
      by_contra hne
      have h0 : f p' = 0 := by omega
      rw [h0] at h
      unfold parityRule at h
      rw [c2] at h
      rcases h with h | ⟨-, -, h⟩ | ⟨h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hmain : MaintainsPosition (f p) p p' := by
      rw [hfp]
      intro i y hy
      fin_cases i <;> fin_cases y <;> simp_all [p, p', u, v, natPref]
    have := hM p hp p' hp' hmain
    rw [hfp, hfp'] at this
    exact absurd this (by decide)

/-- The domain `𝓐 = {pA, pB}` of Exercise 21.E.4 with three agents and alternatives
`x, y, z = 0, 1, 2`: `pA` has `y ≻ x ≻ z` (agents 1, 2) and `x ≻ y ≻ z` (agent 3); `pB` has
`y ≻ x ≻ z` (agent 1) and `x ≻ y ≻ z` (agents 2, 3). -/
def e214A : Fin 3 → Fin 3 → ℕ := ![![1, 2, 0], ![1, 2, 0], ![2, 1, 0]]

/-- See `e214A`. -/
def e214B : Fin 3 → Fin 3 → ℕ := ![![1, 2, 0], ![2, 1, 0], ![2, 1, 0]]

/-- The social welfare functional of Exercise 21.E.4 on `{pA, pB}`: `x ≻ y ≻ z` at `pA`,
`y ≻ x ≻ z` at `pB` (and `x ≻ y ≻ z` elsewhere). -/
noncomputable def e214F (p : Profile (Fin 3) (Fin 3)) : Fin 3 → Fin 3 → Prop :=
  by classical exact
    if p = (fun i => natPref (e214B i)) then natPref ![1, 2, 0] else natPref ![2, 1, 0]

/-- **Exercise 21.E.4**, more than two alternatives (MWG, p. 816). On the two-profile domain
`{pA, pB} ⊆ 𝓟^I`, `e214F` is a Paretian, pairwise independent social welfare functional with
values in `𝓟`, but the induced social choice function (choose the social top) is not
monotonic: it picks `x` at `pA`, `x` maintains its position from `pA` to `pB`, and `y` is
picked at `pB`. -/
theorem exercise_21_E_4_three :
    let A : Set (Profile (Fin 3) (Fin 3)) :=
      {fun i => natPref (e214A i), fun i => natPref (e214B i)}
    A ⊆ StrictProfiles (Fin 3) (Fin 3) ∧ (∀ p ∈ A, e214F p ∈ StrictPrefs (Fin 3)) ∧
      Paretian A e214F ∧ PairwiseIndependent A e214F ∧
      ∀ f : Profile (Fin 3) (Fin 3) → Fin 3, (∀ p ∈ A, ∀ y, e214F p (f p) y) →
        ¬Monotonic A f := by
  intro A
  classical
  have hne : (fun i => natPref (e214A i)) ≠ (fun i => natPref (e214B i)) := by
    intro h
    have := congrFun (congrFun (congrFun h 1) 0) 1
    simp [natPref, e214A, e214B] at this
  have FA : e214F (fun i => natPref (e214A i)) = natPref ![2, 1, 0] := by
    unfold e214F
    simp [hne]
  have FB : e214F (fun i => natPref (e214B i)) = natPref ![1, 2, 0] := by
    unfold e214F
    simp
  have hmemA : ∀ p ∈ A, p = (fun i => natPref (e214A i)) ∨ p = (fun i => natPref (e214B i)) :=
    fun p hp => hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp i
    rcases hmemA p hp with rfl | rfl <;> exact natPref_mem_strict (by fin_cases i <;> decide)
  · intro p hp
    rcases hmemA p hp with rfl | rfl
    · rw [FA]; exact natPref_mem_strict (by decide)
    · rw [FB]; exact natPref_mem_strict (by decide)
  · intro p hp x y hall
    rcases hmemA p hp with rfl | rfl
    · simp only [natPref_strict_iff] at hall
      rw [FA, natPref_strict_iff]
      revert hall
      revert x y
      decide
    · simp only [natPref_strict_iff] at hall
      rw [FB, natPref_strict_iff]
      revert hall
      revert x y
      decide
  · intro p hp p' hp' x y hag
    rcases hmemA p hp with rfl | rfl <;> rcases hmemA p' hp' with rfl | rfl
    · exact ⟨Iff.rfl, Iff.rfl⟩
    · rw [FA, FB]
      simp only [natPref] at hag ⊢
      revert hag
      revert x y
      decide
    · rw [FA, FB]
      simp only [natPref] at hag ⊢
      revert hag
      revert x y
      decide
    · exact ⟨Iff.rfl, Iff.rfl⟩
  · intro f hf hM
    have hA : (fun i => natPref (e214A i)) ∈ A := Or.inl rfl
    have hB : (fun i => natPref (e214B i)) ∈ A := Or.inr rfl
    have tA : f (fun i => natPref (e214A i)) = 0 := by
      have h := hf _ hA 0
      rw [FA] at h
      revert h
      generalize f (fun i => natPref (e214A i)) = a
      intro h
      fin_cases a <;> simp_all [natPref]
    have tB : f (fun i => natPref (e214B i)) = 1 := by
      have h := hf _ hB 1
      rw [FB] at h
      revert h
      generalize f (fun i => natPref (e214B i)) = a
      intro h
      fin_cases a <;> simp_all [natPref]
    have hmain : MaintainsPosition (f (fun i => natPref (e214A i)))
        (fun i => natPref (e214A i)) (fun i => natPref (e214B i)) := by
      rw [tA]
      intro i y
      simp only [natPref]
      revert i y
      decide
    have := hM _ hA _ hB hmain
    rw [tA, tB] at this
    exact absurd this (by decide)

end MWG.SocialChoice
