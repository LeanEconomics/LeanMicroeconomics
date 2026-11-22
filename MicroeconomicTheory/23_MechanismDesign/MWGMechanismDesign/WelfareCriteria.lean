/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Participation
import MWGMechanismDesign.Independent
import MWGMechanismDesign.TypeDensity

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
