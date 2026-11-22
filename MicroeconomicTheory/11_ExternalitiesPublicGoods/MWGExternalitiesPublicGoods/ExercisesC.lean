/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Exercise 11.C.3: Ramsey taxation with a public good (MWG, p. 379)

The government chooses commodity taxes `t = (t₂, …, t_L)` (here `t : Fin n → ℝ`) and the level
`x₀` of a public good produced at cost `c(x₀)`, maximizing aggregate surplus `W(t, x₀)` subject to
budget balance `G(t, x₀) = ∑ₗ tₗ xₗ - c(x₀) = 0` (Exercise 10.E.3 with a public good). With
quasilinear utilities `x₁ᵢ + ∑ₗ φₗᵢ(xₗᵢ, x₀)`, consumers equate `∂φₗᵢ/∂xₗᵢ` to the consumer price,
so (envelope argument, as in Exercise 10.E.3, Chapter 10's `exercise_10_E_3b_marginal`)
`∂W/∂tₗ = tₗ ∂xₗ/∂tₗ` and `∂W/∂x₀ = MB + ∑ₗ tₗ ∂xₗ/∂x₀ - c'(x₀)` with `MB = ∑ᵢ∑ₗ ∂φₗᵢ/∂x₀`;
and `∂G/∂tₗ = xₗ + tₗ ∂xₗ/∂tₗ`, `∂G/∂x₀ = ∑ₗ tₗ ∂xₗ/∂x₀ - c'(x₀)`. We take these derivatives as the
data and derive the optimality conditions from Mathlib's Lagrange multiplier theorem:

* the **Ramsey conditions** `tₗ ∂xₗ/∂tₗ = λ (xₗ + tₗ ∂xₗ/∂tₗ)` (so `(1 - λ) tₗ ∂xₗ/∂tₗ = λ xₗ`, the
  inverse-elasticity rule of Exercise 10.E.3), and
* the **modified Samuelson condition** `MB = (1 - λ)(c'(x₀) - ∑ₗ tₗ ∂xₗ/∂x₀)`: the marginal benefit
  of the public good equals its marginal cost, net of the extra tax revenue it generates through
  complementarity with taxed goods, scaled by the marginal cost of public funds `1 - λ`
  (`exercise_11_C_3`). The two problems interact through `λ` and the revenue terms
  `∑ₗ tₗ ∂xₗ/∂x₀`.
-/

namespace MWG.ExternalitiesPublicGoods

/-- The linear functional `∑ₗ uₗ dtₗ + w dx₀` on `(t, x₀)`. -/
noncomputable def taxPGForm {n : ℕ} (u : Fin n → ℝ) (w : ℝ) :
    (Fin n → ℝ) × ℝ →L[ℝ] ℝ :=
  ∑ l, u l • (ContinuousLinearMap.proj l).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
    w • ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ

theorem taxPGForm_single {n : ℕ} (u : Fin n → ℝ) (w : ℝ) (l : Fin n) :
    taxPGForm u w (Pi.single l 1, 0) = u l := by
  simp [taxPGForm, Pi.single_apply]

theorem taxPGForm_snd {n : ℕ} (u : Fin n → ℝ) (w : ℝ) : taxPGForm u w (0, 1) = w := by
  simp [taxPGForm]

/-- **Exercise 11.C.3** (MWG, p. 379). At a local maximum of `W` on the budget-balance set, if
the budget constraint is qualified (its gradient is not zero), there is a multiplier `λ` with the
Ramsey conditions for every taxed good and the modified Samuelson condition for the public good. -/
theorem exercise_11_C_3 {n : ℕ} (W G : (Fin n → ℝ) × ℝ → ℝ) (v₀ : (Fin n → ℝ) × ℝ)
    (t X sX xX : Fin n → ℝ) (MB dc : ℝ)
    (hW : HasStrictFDerivAt W (taxPGForm (fun l => t l * sX l) (MB + ∑ l, t l * xX l - dc)) v₀)
    (hG : HasStrictFDerivAt G (taxPGForm (fun l => X l + t l * sX l)
      (∑ l, t l * xX l - dc)) v₀)
    (hmax : IsLocalMaxOn W {v | G v = G v₀} v₀)
    (hqual : (∃ l, X l + t l * sX l ≠ 0) ∨ ∑ l, t l * xX l - dc ≠ 0) :
    ∃ lam : ℝ, (∀ l, t l * sX l = lam * (X l + t l * sX l)) ∧
      MB + ∑ l, t l * xX l - dc = lam * (∑ l, t l * xX l - dc) ∧
      (∀ l, (1 - lam) * (t l * sX l) = lam * X l) ∧
      MB = (1 - lam) * (dc - ∑ l, t l * xX l) := by
  obtain ⟨a, b, hab, hlin⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inr hmax) hG hW
  have hcoord : ∀ l, a * (X l + t l * sX l) + b * (t l * sX l) = 0 := fun l => by
    have := congrArg (fun L => L (Pi.single l 1, 0)) hlin
    simpa [taxPGForm_single] using this
  have hsnd : a * (∑ l, t l * xX l - dc) + b * (MB + ∑ l, t l * xX l - dc) = 0 := by
    have := congrArg (fun L => L (0, 1)) hlin
    simpa [taxPGForm_snd] using this
  have hb : b ≠ 0 := by
    intro hb0
    have ha : a ≠ 0 := fun ha0 => hab (by rw [ha0, hb0]; rfl)
    rcases hqual with ⟨l, hl⟩ | h
    · have := hcoord l
      rw [hb0, zero_mul, add_zero] at this
      exact hl ((mul_eq_zero.1 this).resolve_left ha)
    · rw [hb0, zero_mul, add_zero] at hsnd
      exact h ((mul_eq_zero.1 hsnd).resolve_left ha)
  refine ⟨-a / b, fun l => ?_, ?_, fun l => ?_, ?_⟩
  · have := hcoord l; field_simp; linarith
  · field_simp; linarith
  · have := hcoord l; field_simp; linarith
  · field_simp; linarith

/-- A (degenerate) instance of the hypotheses of `exercise_11_C_3`: one taxed good with zero tax,
demand `1`, welfare locally constant, budget `G(t, x₀) = t`. -/
theorem exercise_11_C_3_instance :
    ∃ lam : ℝ, (∀ _l : Fin 1, (0 : ℝ) * 0 = lam * (1 + 0 * 0)) ∧
      (0 : ℝ) + ∑ _l : Fin 1, (0 : ℝ) * 0 - 0 = lam * (∑ _l : Fin 1, (0 : ℝ) * 0 - 0) ∧
      (∀ _l : Fin 1, (1 - lam) * ((0 : ℝ) * 0) = lam * 1) ∧
      (0 : ℝ) = (1 - lam) * (0 - ∑ _l : Fin 1, (0 : ℝ) * 0) := by
  have hG : HasStrictFDerivAt (taxPGForm (fun _ : Fin 1 => (1 : ℝ)) 0)
      (taxPGForm (fun l => (fun _ : Fin 1 => (1 : ℝ)) l + (fun _ => (0 : ℝ)) l *
        (fun _ => (0 : ℝ)) l) (∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0))
      (0 : (Fin 1 → ℝ) × ℝ) := by
    simpa using (taxPGForm (fun _ : Fin 1 => (1 : ℝ)) 0).hasStrictFDerivAt
  have hW : HasStrictFDerivAt (fun _ : (Fin 1 → ℝ) × ℝ => (0 : ℝ))
      (taxPGForm (fun l => (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l)
        (0 + ∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0))
      (0 : (Fin 1 → ℝ) × ℝ) := by
    have h0 : taxPGForm (fun l => (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l)
        (0 + ∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0) = 0 := by
      ext v <;> simp [taxPGForm]
    rw [h0]
    exact hasStrictFDerivAt_const _ _
  exact exercise_11_C_3 _ _ 0 (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 0 hW hG
    (Filter.Eventually.of_forall fun _ => le_rfl) (Or.inl ⟨0, by norm_num⟩)

end MWG.ExternalitiesPublicGoods
