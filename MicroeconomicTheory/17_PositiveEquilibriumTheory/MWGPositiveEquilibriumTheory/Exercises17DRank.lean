/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GenericRegularity

/-!
# Exercises 17.D.5 and 17.D.6: the full rank condition without aggregation (MWG p. 644)

Two consumers, two goods. The equilibrium problem is set up in the consumption variables
`x₁, x₂ ∈ ℝ²`, the price `p = (p₁, 1)` and the reciprocals `λ₁, λ₂` of the marginal utilities of
wealth, with parameters `(ω₁, ω₂) ∈ ℝ⁴`. Deleting the market-clearing equation for good 2 (Walras'
law) and the unknown `p₂` (normalization) leaves 7 equations in 7 unknowns (`focSystem`):

  `λ₁ ∇_{x₁}u₁(x₁, x₂) = p`, `λ₂ ∇u₂(x₂) = p`, `p·(x₁ - ω₁) = 0`, `p·(x₂ - ω₂) = 0`,
  `x₁₁ + x₁₂ = ω₁₁ + ω₁₂`.

The unknowns are `v = (x₁₁, x₂₁, x₁₂, x₂₂, p₁, λ₁, λ₂)`, the gradients are `g₁(x₁, x₂)` (consumer 1
may care about `x₂`: the externality of Exercise 17.D.6) and `g₂(x₂)`.

* **Exercise 17.D.5/17.D.6, full rank** (`focSystem_rank`): if the gradients are differentiable
  with `D_{x₁}g₁` and `Dg₂` nonsingular (the "appropriate differentiability conditions"; e.g. a
  nonsingular Hessian) and `λ₁, λ₂ ≠ 0`, then `D_{(v, ω)} F` has full rank 7: the `x`-directions
  reach the first-order conditions, and endowment changes reach the budget and market equations.
* **Exercise 17.D.6, generic finiteness** (`exercise_17_D_6`): for almost every `(ω₁, ω₂) ∈ ℝ⁴`
  every equilibrium is regular, hence locally isolated (`exercise_17_D_6_isolated`), and the
  equilibrium set, when compact, is finite (`exercise_17_D_6_finite`).
* Instances: log utilities (no externality, `exercise_17_D_5`) and
  `u₁ = log x₁₁ + log x₂₁ + x₁₁ x₁₂` (an externality, `exercise_17_D_6_instance`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology MeasureTheory MWG.ClassicalDemand

/-- Consumer 1's bundle `(v₀, v₁)`. -/
def focX1 (v : Fin 7 → ℝ) : Fin 2 → ℝ := ![v 0, v 1]

/-- Consumer 2's bundle `(v₂, v₃)`. -/
def focX2 (v : Fin 7 → ℝ) : Fin 2 → ℝ := ![v 2, v 3]

/-- **Exercises 17.D.5-17.D.6** (MWG, p. 644). The equilibrium equations in `(x₁, x₂, p₁, λ₁, λ₂)`
with endowments `(ω₁, ω₂)` as parameters (`p₂ = 1`, good 2's market equation deleted). -/
noncomputable def focSystem (g₁ : (Fin 2 → ℝ) × (Fin 2 → ℝ) → Fin 2 → ℝ)
    (g₂ : (Fin 2 → ℝ) → Fin 2 → ℝ) (z : (Fin 7 → ℝ) × (Fin 4 → ℝ)) : Fin 7 → ℝ :=
  ![z.1 5 * g₁ (focX1 z.1, focX2 z.1) 0 - z.1 4,
    z.1 5 * g₁ (focX1 z.1, focX2 z.1) 1 - 1,
    z.1 6 * g₂ (focX2 z.1) 0 - z.1 4,
    z.1 6 * g₂ (focX2 z.1) 1 - 1,
    z.1 4 * (z.1 0 - z.2 0) + (z.1 1 - z.2 1),
    z.1 4 * (z.1 2 - z.2 2) + (z.1 3 - z.2 3),
    z.1 0 + z.1 2 - z.2 0 - z.2 2]

variable {g₁ : (Fin 2 → ℝ) × (Fin 2 → ℝ) → Fin 2 → ℝ} {g₂ : (Fin 2 → ℝ) → Fin 2 → ℝ}

/-- Endowment changes enter only the budget and market equations, linearly. -/
theorem focSystem_shift_ω (v : Fin 7 → ℝ) (ω dω : Fin 4 → ℝ) (s : ℝ) :
    focSystem g₁ g₂ (v, ω + s • dω) = focSystem g₁ g₂ (v, ω) +
      s • ![0, 0, 0, 0, -(v 4 * dω 0 + dω 1), -(v 4 * dω 2 + dω 3), -(dω 0 + dω 2)] := by
  funext k
  fin_cases k <;> simp [focSystem] <;> ring

/-- The direction moving the bundles by `(a, b)`. -/
def focDir (a b : Fin 2 → ℝ) : Fin 7 → ℝ := ![a 0, a 1, b 0, b 1, 0, 0, 0]

theorem focX1_line (v : Fin 7 → ℝ) (a b : Fin 2 → ℝ) (s : ℝ) :
    focX1 (v + s • focDir a b) = focX1 v + s • a := by
  funext j
  fin_cases j <;> simp [focX1, focDir]

theorem focX2_line (v : Fin 7 → ℝ) (a b : Fin 2 → ℝ) (s : ℝ) :
    focX2 (v + s • focDir a b) = focX2 v + s • b := by
  funext j
  fin_cases j <;> simp [focX2, focDir]

/-- **Exercises 17.D.5-17.D.6** (MWG, p. 644), the full rank condition of the transversality
theorem. If `F = focSystem g₁ g₂` is differentiable at `(v, ω)`, the gradients have derivatives
`G₁`, `G₂` with `D_{x₁}g₁ = G₁ ∘ inl` and `G₂` invertible, and `λ₁, λ₂ ≠ 0`, then `DF(v, ω)`
(a `7 × 11` matrix) has rank 7. No aggregation into excess demand is used. -/
theorem focSystem_rank {v : Fin 7 → ℝ} {ω : Fin 4 → ℝ}
    (hd : DifferentiableAt ℝ (focSystem g₁ g₂) (v, ω))
    {G₁ : (Fin 2 → ℝ) × (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)} {G₂ : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hg₁ : HasFDerivAt g₁ G₁ (focX1 v, focX2 v)) (hg₂ : HasFDerivAt g₂ G₂ (focX2 v))
    (hinv₁ : (G₁.comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible) (hinv₂ : G₂.IsInvertible)
    (hl₁ : v 5 ≠ 0) (hl₂ : v 6 ≠ 0) :
    (fderiv ℝ (focSystem g₁ g₂) (v, ω)).range = ⊤ := by
  set D := fderiv ℝ (focSystem g₁ g₂) (v, ω)
  -- endowment directions
  have hω : ∀ dω : Fin 4 → ℝ, D (0, dω) =
      ![0, 0, 0, 0, -(v 4 * dω 0 + dω 1), -(v 4 * dω 2 + dω 3), -(dω 0 + dω 2)] := by
    intro dω
    have hline : HasDerivAt (fun s : ℝ => (v, ω + s • dω)) ((0 : Fin 7 → ℝ), dω) 0 := by
      refine (hasDerivAt_const (0 : ℝ) v).prodMk ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dω).const_add ω
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have h2 : HasDerivAt (fun s : ℝ => focSystem g₁ g₂ (v, ω + s • dω))
        ![0, 0, 0, 0, -(v 4 * dω 0 + dω 1), -(v 4 * dω 2 + dω 3), -(dω 0 + dω 2)] 0 := by
      simp only [focSystem_shift_ω]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (![0, 0, 0, 0, -(v 4 * dω 0 + dω 1), -(v 4 * dω 2 + dω 3), -(dω 0 + dω 2)] :
          Fin 7 → ℝ)).const_add (focSystem g₁ g₂ (v, ω))
    exact h1.unique h2
  -- bundle directions
  have hx : ∀ a b : Fin 2 → ℝ,
      D (focDir a b, 0) 0 = v 5 * G₁ (a, b) 0 ∧ D (focDir a b, 0) 1 = v 5 * G₁ (a, b) 1 ∧
      D (focDir a b, 0) 2 = v 6 * G₂ b 0 ∧ D (focDir a b, 0) 3 = v 6 * G₂ b 1 := by
    intro a b
    have hline : HasDerivAt (fun s : ℝ => (v + s • focDir a b, ω)) (focDir a b, (0 : Fin 4 → ℝ))
        0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const (0 : ℝ) ω)
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (focDir a b)).const_add v
    have h1 := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp))
    have hl1 : HasDerivAt (fun s : ℝ => (focX1 v + s • a, focX2 v + s • b)) (a, b) 0 := by
      refine HasDerivAt.prodMk ?_ ?_
      · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (focX1 v)
      · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add (focX2 v)
    have hG1 := hasDerivAt_pi.1 (hg₁.comp_hasDerivAt_of_eq (0 : ℝ) hl1 (by simp))
    have hl2 : HasDerivAt (fun s : ℝ => focX2 v + s • b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add (focX2 v)
    have hG2 := hasDerivAt_pi.1 (hg₂.comp_hasDerivAt_of_eq (0 : ℝ) hl2 (by simp))
    have hd5 : focDir a b 5 = 0 := rfl
    have hd4 : focDir a b 4 = 0 := rfl
    have hd6 : focDir a b 6 = 0 := rfl
    refine ⟨(h1 0).unique ?_, (h1 1).unique ?_, (h1 2).unique ?_, (h1 3).unique ?_⟩
    · have := ((hG1 0).const_mul (v 5)).sub_const (v 4)
      convert this using 2 with s
      simp [focSystem, focX1_line, focX2_line, hd5, hd4]
    · have := ((hG1 1).const_mul (v 5)).sub_const 1
      convert this using 2 with s
      simp [focSystem, focX1_line, focX2_line, hd5]
    · have := ((hG2 0).const_mul (v 6)).sub_const (v 4)
      convert this using 2 with s
      simp [focSystem, focX2_line, hd6, hd4]
    · have := ((hG2 1).const_mul (v 6)).sub_const 1
      convert this using 2 with s
      simp [focSystem, focX2_line, hd6]
  obtain ⟨e₁, he₁⟩ := hinv₁
  obtain ⟨e₂, he₂⟩ := hinv₂
  refine LinearMap.range_eq_top.2 fun T => ?_
  set b := e₂.symm ((v 6)⁻¹ • ![T 2, T 3])
  set a := e₁.symm ((v 5)⁻¹ • ![T 0, T 1] - G₁ (0, b))
  have hGa : G₁ (a, 0) = (v 5)⁻¹ • ![T 0, T 1] - G₁ (0, b) := by
    have := congrArg (fun f => f a) he₁
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] at this
    rw [← this, ContinuousLinearEquiv.apply_symm_apply]
  have hGb : G₂ b = (v 6)⁻¹ • ![T 2, T 3] := by
    have := congrArg (fun f => f b) he₂
    simp only [ContinuousLinearEquiv.coe_coe] at this
    rw [← this, ContinuousLinearEquiv.apply_symm_apply]
  have hGab : G₁ (a, b) = (v 5)⁻¹ • ![T 0, T 1] := by
    rw [show (a, b) = (a, 0) + (0, b) by simp, map_add, hGa, sub_add_cancel]
  set r := D (focDir a b, 0)
  set dω : Fin 4 → ℝ := ![-(T 6 - r 6), -(T 4 - r 4) + v 4 * (T 6 - r 6), 0, -(T 5 - r 5)]
  refine ⟨(focDir a b, dω), ?_⟩
  change D (focDir a b, dω) = T
  rw [show (focDir a b, dω) = (focDir a b, 0) + (0, dω) by simp, map_add, hω]
  obtain ⟨h0, h1, h2, h3⟩ := hx a b
  rw [hGab] at h0 h1
  rw [hGb] at h2 h3
  funext k
  fin_cases k
  · simp only [Fin.zero_eta, Pi.add_apply]
    rw [h0]
    simp [hl₁]
  · simp only [Fin.mk_one, Pi.add_apply]
    rw [h1]
    simp [hl₁]
  · simp only [Pi.add_apply]
    rw [show (⟨2, by norm_num⟩ : Fin 7) = 2 from rfl, h2]
    simp [hl₂]
  · simp only [Pi.add_apply]
    rw [show (⟨3, by norm_num⟩ : Fin 7) = 3 from rfl, h3]
    simp [hl₂]
  · simp [dω, r]
    ring
  · simp [dω, r]
  · simp [dω, r]

/-- The region of unknowns where the gradients are defined. -/
def focDomain (U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))) (U₂ : Set (Fin 2 → ℝ)) :
    Set (Fin 7 → ℝ) :=
  {v | (focX1 v, focX2 v) ∈ U₁ ∧ focX2 v ∈ U₂}

theorem contDiff_focX1 : ContDiff ℝ 1 focX1 := by
  refine contDiff_pi.2 fun j => ?_
  fin_cases j
  · exact contDiff_apply ℝ ℝ (0 : Fin 7)
  · exact contDiff_apply ℝ ℝ (1 : Fin 7)

theorem contDiff_focX2 : ContDiff ℝ 1 focX2 := by
  refine contDiff_pi.2 fun j => ?_
  fin_cases j
  · exact contDiff_apply ℝ ℝ (2 : Fin 7)
  · exact contDiff_apply ℝ ℝ (3 : Fin 7)

theorem isOpen_focDomain {U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {U₂ : Set (Fin 2 → ℝ)}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) : IsOpen (focDomain U₁ U₂) :=
  (hU₁.preimage (contDiff_focX1.continuous.prodMk contDiff_focX2.continuous)).inter
    (hU₂.preimage contDiff_focX2.continuous)

/-- With `C¹` gradients, the system is `C¹` on `focDomain × ℝ⁴`. -/
theorem contDiffOn_focSystem {U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {U₂ : Set (Fin 2 → ℝ)}
    (hg₁ : ContDiffOn ℝ 1 g₁ U₁) (hg₂ : ContDiffOn ℝ 1 g₂ U₂) :
    ContDiffOn ℝ 1 (focSystem g₁ g₂) (focDomain U₁ U₂ ×ˢ Set.univ) := by
  have hP : ContDiff ℝ 1 fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => (focX1 z.1, focX2 z.1) :=
    (contDiff_focX1.comp contDiff_fst).prodMk (contDiff_focX2.comp contDiff_fst)
  have hG₁ : ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => g₁ (focX1 z.1, focX2 z.1))
      (focDomain U₁ U₂ ×ˢ Set.univ) :=
    hg₁.comp hP.contDiffOn fun z hz => hz.1.1
  have hG₂ : ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => g₂ (focX2 z.1))
      (focDomain U₁ U₂ ×ˢ Set.univ) :=
    hg₂.comp (contDiff_focX2.comp contDiff_fst).contDiffOn fun z hz => hz.1.2
  have hv : ∀ k : Fin 7, ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => z.1 k)
      (focDomain U₁ U₂ ×ˢ Set.univ) := fun k =>
    ((contDiff_apply ℝ ℝ k).comp contDiff_fst).contDiffOn
  have hw : ∀ k : Fin 4, ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => z.2 k)
      (focDomain U₁ U₂ ×ˢ Set.univ) := fun k =>
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd).contDiffOn
  refine contDiffOn_pi.2 fun k => ?_
  fin_cases k
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) =>
      z.1 5 * g₁ (focX1 z.1, focX2 z.1) 0 - z.1 4) _
    exact ((hv 5).mul (contDiffOn_pi.1 hG₁ 0)).sub (hv 4)
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) =>
      z.1 5 * g₁ (focX1 z.1, focX2 z.1) 1 - 1) _
    exact ((hv 5).mul (contDiffOn_pi.1 hG₁ 1)).sub contDiffOn_const
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => z.1 6 * g₂ (focX2 z.1) 0 - z.1 4) _
    exact ((hv 6).mul (contDiffOn_pi.1 hG₂ 0)).sub (hv 4)
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => z.1 6 * g₂ (focX2 z.1) 1 - 1) _
    exact ((hv 6).mul (contDiffOn_pi.1 hG₂ 1)).sub contDiffOn_const
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) =>
      z.1 4 * (z.1 0 - z.2 0) + (z.1 1 - z.2 1)) _
    exact ((hv 4).mul ((hv 0).sub (hw 0))).add ((hv 1).sub (hw 1))
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) =>
      z.1 4 * (z.1 2 - z.2 2) + (z.1 3 - z.2 3)) _
    exact ((hv 4).mul ((hv 2).sub (hw 2))).add ((hv 3).sub (hw 3))
  · change ContDiffOn ℝ 1 (fun z : (Fin 7 → ℝ) × (Fin 4 → ℝ) => z.1 0 + z.1 2 - z.2 0 - z.2 2) _
    exact (((hv 0).add (hv 2)).sub (hw 0)).sub (hw 2)

/-- **Exercise 17.D.6** (MWG, p. 644), generic regularity. With an externality in consumer 1's
utility (`g₁` may depend on `x₂`), `C¹` gradients on open sets and nonsingular `D_{x₁}g₁`, `Dg₂`,
the set of endowments `(ω₁, ω₂) ∈ ℝ⁴` for which some equilibrium `v` has `D_v F(v; ω)` singular
has Lebesgue measure zero (transversality, Chapter 3 `theorem_M_E_2`, with `focSystem_rank`). -/
theorem exercise_17_D_6 {U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {U₂ : Set (Fin 2 → ℝ)}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hg₁ : ContDiffOn ℝ 1 g₁ U₁)
    (hg₂ : ContDiffOn ℝ 1 g₂ U₂)
    (hinv₁ : ∀ y ∈ U₁, ((fderiv ℝ g₁ y).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible)
    (hinv₂ : ∀ x ∈ U₂, (fderiv ℝ g₂ x).IsInvertible) :
    volume {ω : Fin 4 → ℝ | ω ∈ Set.univ ∧ ∃ v ∈ focDomain U₁ U₂,
      focSystem g₁ g₂ (v, ω) = 0 ∧ ¬ ((fderiv ℝ (focSystem g₁ g₂) (v, ω)).comp
        (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} = 0 := by
  have hA := isOpen_focDomain hU₁ hU₂
  have hf := contDiffOn_focSystem hg₁ hg₂ (U₁ := U₁) (U₂ := U₂)
  refine theorem_M_E_2 hA isOpen_univ hf fun z hz hz0 => ?_
  obtain ⟨v, ω⟩ := z
  have hd : DifferentiableAt ℝ (focSystem g₁ g₂) (v, ω) :=
    (hf.contDiffAt ((hA.prod isOpen_univ).mem_nhds hz)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ g₁ (focX1 v, focX2 v) :=
    (hg₁.contDiffAt (hU₁.mem_nhds hz.1.1)).differentiableAt one_ne_zero
  have h2 : DifferentiableAt ℝ g₂ (focX2 v) :=
    (hg₂.contDiffAt (hU₂.mem_nhds hz.1.2)).differentiableAt one_ne_zero
  have hrow1 := congrFun hz0 1
  have hrow3 := congrFun hz0 3
  simp only [focSystem] at hrow1 hrow3
  have hl₁ : v 5 ≠ 0 := by
    intro h
    simp [h] at hrow1
  have hl₂ : v 6 ≠ 0 := by
    intro h
    simp [h] at hrow3
  exact focSystem_rank hd h1.hasFDerivAt h2.hasFDerivAt (hinv₁ _ hz.1.1) (hinv₂ _ hz.1.2)
    hl₁ hl₂

/-- An invertible derivative makes a zero isolated. -/
theorem isolated_of_isInvertible {N : ℕ} {f : (Fin N → ℝ) → Fin N → ℝ} {x : Fin N → ℝ}
    {D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)} (hd : HasFDerivAt f D x) (hinv : D.IsInvertible) :
    ∃ ε > 0, ∀ y, y ≠ x → dist y x < ε → f y ≠ f x := by
  obtain ⟨e, rfl⟩ := hinv
  have hev := hd.eventually_ne (c := f x) ⟨_, e.antilipschitz⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  exact ⟨ε, hε, fun y hy hdist => hball hdist hy⟩

/-- **Exercise 17.D.6** (MWG, p. 644): for almost every `(ω₁, ω₂)`, every equilibrium of the
system is locally isolated. -/
theorem exercise_17_D_6_isolated {U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {U₂ : Set (Fin 2 → ℝ)}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hg₁ : ContDiffOn ℝ 1 g₁ U₁)
    (hg₂ : ContDiffOn ℝ 1 g₂ U₂)
    (hinv₁ : ∀ y ∈ U₁, ((fderiv ℝ g₁ y).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible)
    (hinv₂ : ∀ x ∈ U₂, (fderiv ℝ g₂ x).IsInvertible) :
    ∀ᵐ ω, ∀ v ∈ focDomain U₁ U₂, focSystem g₁ g₂ (v, ω) = 0 →
      ∃ ε > 0, ∀ v', v' ≠ v → dist v' v < ε → focSystem g₁ g₂ (v', ω) ≠ 0 := by
  have hA := isOpen_focDomain hU₁ hU₂
  have hf := contDiffOn_focSystem hg₁ hg₂ (U₁ := U₁) (U₂ := U₂)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (exercise_17_D_6 hU₁ hU₂ hg₁ hg₂ hinv₁ hinv₂)
  simp only [Set.mem_ofPred_eq, not_forall] at hω
  obtain ⟨v, hv, hv0, hno⟩ := hω
  refine ⟨trivial, v, hv, hv0, fun hinv => hno ?_⟩
  have hd : DifferentiableAt ℝ (focSystem g₁ g₂) (v, ω) :=
    (hf.contDiffAt ((hA.prod isOpen_univ).mem_nhds ⟨hv, trivial⟩)).differentiableAt one_ne_zero
  obtain ⟨ε, hε, h⟩ := isolated_of_isInvertible (fderiv_partial_left hd) hinv
  exact ⟨ε, hε, fun v' hne hdist => by rw [← hv0]; exact h v' hne hdist⟩

/-- A compact set of isolated points is finite. -/
theorem finite_of_isCompact_isolated {N : ℕ} {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hiso : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist y x < ε → y = x) : K.Finite := by
  choose! ε hε hball using hiso
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (ε x))
    fun x hx => Metric.ball_mem_nhds x (hε x hx)
  refine (t.finite_toSet).subset fun x hx => ?_
  obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (hcover hx)
  rw [hball c (htK c hct) x hx (Metric.mem_ball.1 hxc)]
  exact hct

/-- **Exercise 17.D.6** (MWG, p. 644): generically on endowments the number of equilibria is
finite, provided the equilibrium set is compact (as it is under boundary conditions on demand
like those behind Proposition 17.D.1). -/
theorem exercise_17_D_6_finite {U₁ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {U₂ : Set (Fin 2 → ℝ)}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hg₁ : ContDiffOn ℝ 1 g₁ U₁)
    (hg₂ : ContDiffOn ℝ 1 g₂ U₂)
    (hinv₁ : ∀ y ∈ U₁, ((fderiv ℝ g₁ y).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible)
    (hinv₂ : ∀ x ∈ U₂, (fderiv ℝ g₂ x).IsInvertible) :
    ∀ᵐ ω, IsCompact {v | v ∈ focDomain U₁ U₂ ∧ focSystem g₁ g₂ (v, ω) = 0} →
      {v | v ∈ focDomain U₁ U₂ ∧ focSystem g₁ g₂ (v, ω) = 0}.Finite := by
  filter_upwards [exercise_17_D_6_isolated hU₁ hU₂ hg₁ hg₂ hinv₁ hinv₂] with ω hω hK
  refine finite_of_isCompact_isolated hK fun v hv => ?_
  obtain ⟨ε, hε, h⟩ := hω v hv.1 hv.2
  refine ⟨ε, hε, fun v' hv' hdist => ?_⟩
  by_contra hne
  exact h v' hne hdist hv'.2

/-! ### Instances -/

/-- The gradient `(1/x₁, 1/x₂)` of `u(x) = log x₁ + log x₂`. -/
noncomputable def logGrad (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![1 / x 0, 1 / x 1]

theorem contDiffOn_logGrad : ContDiffOn ℝ 1 logGrad (posOrthant 2) := by
  refine contDiffOn_pi.2 fun j => ?_
  fin_cases j
  · exact contDiffOn_const.div (contDiff_apply ℝ ℝ 0).contDiffOn fun x hx => (hx 0).ne'
  · exact contDiffOn_const.div (contDiff_apply ℝ ℝ 1).contDiffOn fun x hx => (hx 1).ne'

/-- An injective linear map of `ℝ^N` is invertible. -/
theorem isInvertible_of_injective {N : ℕ} {f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)}
    (h : Function.Injective f) : f.IsInvertible := by
  rw [isInvertible_iff_det_ne_zero]
  have hu : IsUnit (f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 h)
  exact ((LinearMap.isUnit_iff_isUnit_det _).1 hu).ne_zero

/-- The Hessian of `log x₁ + log x₂` is nonsingular on `ℝ²₊₊`. -/
theorem logGrad_fderiv_isInvertible {x : Fin 2 → ℝ} (hx : x ∈ posOrthant 2) :
    (fderiv ℝ logGrad x).IsInvertible := by
  have hd : DifferentiableAt ℝ logGrad x :=
    (contDiffOn_logGrad.contDiffAt ((isOpen_posOrthant 2).mem_nhds hx)).differentiableAt
      one_ne_zero
  refine isInvertible_of_injective fun v w hvw => ?_
  rw [← sub_eq_zero, ← map_sub] at hvw
  set u := v - w
  have hline : HasDerivAt (fun s : ℝ => x + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have h1 := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp))
  have hj : ∀ j : Fin 2, u j = 0 := by
    intro j
    have hxj := (hx j).ne'
    have hl : HasDerivAt (fun s : ℝ => x j + s * u j) (u j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u j)).const_add (x j)
    have hc : HasDerivAt (fun s : ℝ => (x j + s * u j)⁻¹) (-(u j) / (x j + 0 * u j) ^ 2) 0 :=
      hl.inv (by simpa using hxj)
    have hcoord := (h1 j).unique (by
      convert hc using 2 with s
      fin_cases j <;> simp [logGrad])
    rw [hvw] at hcoord
    simp only [Pi.zero_apply] at hcoord
    have : -(u j) / x j ^ 2 = 0 := by
      have h' := hcoord.symm
      simpa using h'
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · exact absurd h (pow_ne_zero 2 hxj)
  exact sub_eq_zero.1 (funext hj)

/-- **Exercise 17.D.5** (MWG, p. 644), instance: two consumers with `uᵢ = log x₁ᵢ + log x₂ᵢ`
(no externality). The hypotheses of `exercise_17_D_6` hold, so for almost every
`(ω₁, ω₂) ∈ ℝ⁴` the system in `(x₁, x₂, p₁, λ₁, λ₂)` is regular. -/
theorem exercise_17_D_5 :
    volume {ω : Fin 4 → ℝ | ω ∈ Set.univ ∧ ∃ v ∈ focDomain (posOrthant 2 ×ˢ Set.univ)
      (posOrthant 2), focSystem (fun y => logGrad y.1) logGrad (v, ω) = 0 ∧
        ¬ ((fderiv ℝ (focSystem (fun y => logGrad y.1) logGrad) (v, ω)).comp
          (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} = 0 := by
  refine exercise_17_D_6 ((isOpen_posOrthant 2).prod isOpen_univ) (isOpen_posOrthant 2)
    (contDiffOn_logGrad.comp contDiff_fst.contDiffOn fun y hy => hy.1) contDiffOn_logGrad
    (fun y hy => ?_) fun x hx => logGrad_fderiv_isInvertible hx
  have hd : DifferentiableAt ℝ (fun y : (Fin 2 → ℝ) × (Fin 2 → ℝ) => logGrad y.1) y :=
    ((contDiffOn_logGrad.contDiffAt ((isOpen_posOrthant 2).mem_nhds hy.1)).differentiableAt
      one_ne_zero).comp y differentiableAt_fst
  have h := fderiv_partial_left (v := y.1) (q := y.2) hd
  rw [← h.fderiv]
  exact logGrad_fderiv_isInvertible hy.1

/-- The gradient in `x₁` of `u₁(x₁, x₂) = log x₁₁ + log x₂₁ + x₁₁ x₁₂` (an externality: consumer
2's consumption of good 1 raises consumer 1's marginal utility of good 1). -/
noncomputable def externalGrad (y : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Fin 2 → ℝ :=
  logGrad y.1 + ![y.2 0, 0]

/-- **Exercise 17.D.6** (MWG, p. 644), instance with an externality: the hypotheses hold for
`u₁ = log x₁₁ + log x₂₁ + x₁₁ x₁₂` and `u₂ = log x₁₂ + log x₂₂`, so for almost every endowment
vector the equilibria are regular, hence locally isolated (and finitely many when the equilibrium
set is compact). -/
theorem exercise_17_D_6_instance :
    ∀ᵐ ω, ∀ v ∈ focDomain (posOrthant 2 ×ˢ Set.univ) (posOrthant 2),
      focSystem externalGrad logGrad (v, ω) = 0 →
        ∃ ε > 0, ∀ v', v' ≠ v → dist v' v < ε → focSystem externalGrad logGrad (v', ω) ≠ 0 := by
  have hc : ContDiffOn ℝ 1 externalGrad (posOrthant 2 ×ˢ Set.univ) := by
    refine (contDiffOn_logGrad.comp contDiff_fst.contDiffOn fun y hy => hy.1).add ?_
    refine contDiff_pi.2 (fun j => ?_) |>.contDiffOn
    fin_cases j
    · change ContDiff ℝ 1 (fun y : (Fin 2 → ℝ) × (Fin 2 → ℝ) => y.2 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
    · change ContDiff ℝ 1 (fun _ : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (0 : ℝ))
      exact contDiff_const
  refine exercise_17_D_6_isolated ((isOpen_posOrthant 2).prod isOpen_univ) (isOpen_posOrthant 2)
    hc contDiffOn_logGrad (fun y hy => ?_) fun x hx => logGrad_fderiv_isInvertible hx
  have hd : DifferentiableAt ℝ externalGrad y :=
    (hc.contDiffAt (((isOpen_posOrthant 2).prod isOpen_univ).mem_nhds hy)).differentiableAt
      one_ne_zero
  have h := fderiv_partial_left (v := y.1) (q := y.2) hd
  rw [← h.fderiv]
  have heq : (fun x => externalGrad (x, y.2)) = fun x => logGrad x + ![y.2 0, 0] := rfl
  rw [heq, fderiv_add_const]
  exact logGrad_fderiv_isInvertible hy.1

end MWG.PositiveEquilibriumTheory
