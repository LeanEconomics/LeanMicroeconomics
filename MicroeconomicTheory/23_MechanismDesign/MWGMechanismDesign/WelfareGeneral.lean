/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.WelfareCriteria
import MWGMechanismDesign.TypeDensity

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
