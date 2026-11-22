/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Bayesian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

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
