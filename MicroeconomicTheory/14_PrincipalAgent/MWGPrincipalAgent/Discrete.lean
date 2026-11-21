/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Finitely many profit levels

MWG, footnote 6 (p. 481): the discrete version of the hidden-action model, with finitely many
profit levels `π₁, …, π_N`. The reference measure is the counting measure on these levels,
`∑ᵢ δ_{πᵢ}`; integrals against it are finite sums. Used for the concrete instances of
Section 14.B and for Exercise 14.B.4.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- The counting measure on the profit levels `a 0, …, a (n - 1)` (MWG, footnote 6). -/
noncomputable def dmeas {n : ℕ} (a : Fin n → ℝ) : Measure ℝ := ∑ i, Measure.dirac (a i)

/-- Every function is integrable against the counting measure on finitely many points. -/
theorem dmeas_integrable {n : ℕ} (a : Fin n → ℝ) (F : ℝ → ℝ) : Integrable F (dmeas a) :=
  integrable_finsetSum_measure.2 fun i _ => integrable_dirac (by simp)

/-- Integrals against the counting measure are finite sums. -/
theorem dmeas_integral {n : ℕ} (a : Fin n → ℝ) (F : ℝ → ℝ) :
    ∫ x, F x ∂dmeas a = ∑ i, F (a i) := by
  unfold dmeas
  rw [integral_finsetSum_measure fun i _ => integrable_dirac (by simp)]
  simp [integral_dirac]

/-- Integrals over a measurable set are sums over the points in the set. -/
theorem dmeas_setIntegral {n : ℕ} (a : Fin n → ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (F : ℝ → ℝ) : ∫ x in s, F x ∂dmeas a = ∑ i, s.indicator F (a i) := by
  rw [← integral_indicator hs, dmeas_integral]

/-- A property holding at every point holds almost everywhere for the counting measure. -/
theorem dmeas_ae {n : ℕ} (a : Fin n → ℝ) {P : ℝ → Prop} (h : ∀ i, P (a i)) :
    ∀ᵐ x ∂dmeas a, P x := by
  rw [ae_iff]
  unfold dmeas
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply, indicator_of_notMem (by simpa using h i)]

end MWG.PrincipalAgent
