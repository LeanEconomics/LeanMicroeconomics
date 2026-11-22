/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Efficiency
import MWGAdverseSelection.Constrained

/-!
# Distributional aims and direct revelation mechanisms

MWG, Section 13.B, pp. 448-450 (small type).

* `weightedWelfare` is (13.B.13); with weights `λ(θ) = N` it is aggregate surplus
  (`weightedWelfare_const`).
* `mandate_all`: when `r(θ) ≤ θ`, mandating that everyone work raises aggregate surplus above a
  competitive equilibrium in which some types with `r(θ) < θ` stay home, although the type `θ̄`
  is worse off when `E[θ] < r(θ̄)` (p. 449).
* Direct revelation mechanisms `[w(·), t(·), I(·)]`: individual rationality for the firm (13.B.14),
  budget balance (13.B.15), truth telling (13.B.16) and the authority's budget (13.B.17).
  `mechanism_17_of_14_15`, `mechanism_exists_t`: a mechanism is feasible iff `[w(·), I(·)]`
  satisfies (13.B.16) and (13.B.17); `mechanism_two_outcome`, `mechanism_scheme`: truth telling
  forces a two-outcome scheme `(w_e, 1)`, `(w_u, 0)`, the class studied above.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- **(13.B.13)** (MWG, p. 448). Social welfare as a weighted sum of worker utilities
`∫ [I(θ)θ + (1 - I(θ))r(θ)] λ(θ) dF(θ)`. -/
noncomputable def weightedWelfare (μ : Measure ℝ) (lam r I : ℝ → ℝ) : ℝ :=
  ∫ θ, (I θ * θ + (1 - I θ) * r θ) * lam θ ∂μ

/-- **(13.B.13)** (MWG, p. 448). With `λ(θ) = N` for all `θ` the welfare function is aggregate
surplus. -/
theorem weightedWelfare_const (μ : Measure ℝ) (N : ℝ) (r I : ℝ → ℝ) :
    weightedWelfare μ (fun _ => N) r I = aggSurplus μ N r I := by
  unfold weightedWelfare aggSurplus
  congr 1; ext θ; ring

/-- **Section 13.B** (MWG, pp. 448-449). If `r(θ) ≤ θ` on `[θ̲, θ̄]`, mandating that every worker
work for a firm (at wage `E[θ]`) yields strictly higher aggregate surplus than a competitive
equilibrium with wage `w*` in which, with positive probability, types with `w* < r(θ) < θ`
stay home; yet type `θ̄` is worse off when `E[θ] < r(θ̄)`. -/
theorem mandate_all {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {N : ℝ} (hN : 0 < N)
    {r : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r μ)
    (hle : ∀ θ ∈ Icc θl θh, r θ ≤ θ) (ws : ℝ)
    (hmis : 0 < μ {θ | ws < r θ ∧ r θ < θ}) :
    aggSurplus μ N r ((acceptSet r ws).indicator fun _ => 1) < aggSurplus μ N r (fun _ => 1) ∧
      (meanType μ < r θh → meanType μ < max ws (r θh)) := by
  refine ⟨?_, fun h => h.trans_le (le_max_right _ _)⟩
  have heq : aggSurplus μ N r (fun _ => 1) = aggSurplus μ N r (optEmployment r) := by
    unfold aggSurplus
    refine integral_congr_ae (hd.ae_mem.mono fun θ hθ => ?_)
    simp only [optEmployment_eq, max_eq_left (hle θ hθ)]
    ring
  rw [heq]
  refine aggSurplus_lt_opt hd hN hr hrint
    (measurable_const.indicator (measurableSet_acceptSet hr ws))
    (fun θ => by by_cases h : θ ∈ acceptSet r ws <;> simp [h]) (hmis.trans_le
    (measure_mono fun θ hθ => ?_))
  have hθ' : θ ∉ acceptSet r ws := fun h => absurd (show r θ ≤ ws from h) (not_le.2 hθ.1)
  simp only [mem_ofPred_eq, indicator_of_notMem hθ', zero_mul, sub_zero, one_mul, zero_add]
  rw [max_eq_left hθ.2.le]; exact hθ.2

/-- **(13.B.14)** (MWG, p. 449). Individual rationality for the (aggregate) firm. -/
def MechIR (μ : Measure ℝ) (t I : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (I θ * θ - t θ) ∂μ

/-- **(13.B.15)** (MWG, p. 449). Budget balance for the authority. -/
def MechBB (μ : Measure ℝ) (w t : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (t θ - w θ) ∂μ

/-- **(13.B.16)** (MWG, p. 449). Truth telling: type `θ` prefers her own outcome to the one of
any `θ̂`. -/
def MechIC (r w I : ℝ → ℝ) : Prop :=
  ∀ θ θhat, w θhat + (1 - I θhat) * r θ ≤ w θ + (1 - I θ) * r θ

/-- **(13.B.17)** (MWG, p. 449). The budget of an authority that runs the firms. -/
def MechBudget (μ : Measure ℝ) (w I : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (I θ * θ - w θ) ∂μ

/-- **Section 13.B** (MWG, p. 449). A feasible mechanism satisfies (13.B.17). -/
theorem mechanism_17_of_14_15 {μ : Measure ℝ} {w t I : ℝ → ℝ}
    (hIθ : Integrable (fun θ => I θ * θ) μ) (ht : Integrable t μ) (hw : Integrable w μ)
    (h14 : MechIR μ t I) (h15 : MechBB μ w t) : MechBudget μ w I := by
  unfold MechIR MechBB MechBudget at *
  rw [integral_sub hIθ ht] at h14
  rw [integral_sub ht hw] at h15
  rw [integral_sub hIθ hw]
  linarith

/-- **Section 13.B** (MWG, p. 450). If `[w(·), I(·)]` satisfies (13.B.17), the transfer
`t(θ) = I(θ)θ` makes `[w(·), t(·), I(·)]` satisfy (13.B.14) and (13.B.15). -/
theorem mechanism_exists_t {μ : Measure ℝ} {w I : ℝ → ℝ}
    (h17 : MechBudget μ w I) :
    MechIR μ (fun θ => I θ * θ) I ∧ MechBB μ w (fun θ => I θ * θ) := by
  refine ⟨?_, h17⟩
  unfold MechIR; simp

/-- **Section 13.B** (MWG, p. 450). Truth telling forces equal payments to types with the same
employment decision: `I(θ') = I(θ'')` implies `w(θ') = w(θ'')`. -/
theorem mechanism_two_outcome {r w I : ℝ → ℝ} (hIC : MechIC r w I) {θ₁ θ₂ : ℝ}
    (hI : I θ₁ = I θ₂) : w θ₁ = w θ₂ := by
  have h1 := hIC θ₁ θ₂
  have h2 := hIC θ₂ θ₁
  rw [hI] at h1 h2
  linarith

/-- **Section 13.B** (MWG, p. 450). A truthful mechanism with `I(θ) ∈ {0, 1}` is a choice between
two outcomes `(w_e, I = 1)` and `(w_u, I = 0)`, and each type picks a best one. -/
theorem mechanism_scheme {r w I : ℝ → ℝ} (hIC : MechIC r w I) :
    ∃ we wu, (∀ θ, I θ = 1 → w θ = we) ∧ (∀ θ, I θ = 0 → w θ = wu) ∧
      (∀ θ θ', I θ = 1 → I θ' = 0 → wu + r θ ≤ we ∧ we ≤ wu + r θ') := by
  by_cases h1 : ∃ θ, I θ = 1
  · obtain ⟨θ1, hθ1⟩ := h1
    by_cases h0 : ∃ θ, I θ = 0
    · obtain ⟨θ0, hθ0⟩ := h0
      refine ⟨w θ1, w θ0, fun θ h => mechanism_two_outcome hIC (h.trans hθ1.symm),
        fun θ h => mechanism_two_outcome hIC (h.trans hθ0.symm), fun θ θ' h h' => ?_⟩
      have e1 : w θ = w θ1 := mechanism_two_outcome hIC (h.trans hθ1.symm)
      have e0 : w θ' = w θ0 := mechanism_two_outcome hIC (h'.trans hθ0.symm)
      have a1 := hIC θ θ'
      have a2 := hIC θ' θ
      rw [h, h'] at a1 a2
      constructor <;> linarith
    · push Not at h0
      refine ⟨w θ1, 0, fun θ h => mechanism_two_outcome hIC (h.trans hθ1.symm),
        fun θ h => absurd h (h0 θ), fun θ θ' _ h' => absurd h' (h0 θ')⟩
  · push Not at h1
    by_cases h0 : ∃ θ, I θ = 0
    · obtain ⟨θ0, hθ0⟩ := h0
      exact ⟨0, w θ0, fun θ h => absurd h (h1 θ),
        fun θ h => mechanism_two_outcome hIC (h.trans hθ0.symm), fun θ _ h _ => absurd h (h1 θ)⟩
    · push Not at h0
      exact ⟨0, 0, fun θ h => absurd h (h1 θ), fun θ h => absurd h (h0 θ),
        fun θ _ h _ => absurd h (h1 θ)⟩

end MWG.AdverseSelection
