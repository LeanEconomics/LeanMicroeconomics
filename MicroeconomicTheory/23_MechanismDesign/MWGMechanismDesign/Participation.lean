/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Bayesian
import MWGMechanismDesign.Quasilinear

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
