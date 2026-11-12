/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.Basic

/-!
# Exercise 3.G.5(a): Hicksian composite commodities

MWG, Exercise 3.G.5(a), pp. 99-100. Goods are split into `x ∈ ℝ^A_+` and `y ∈ ℝ^B_+`, the prices
of the `y` goods move together, `q = α q₀`, and
`ũ(x, z) = max {u(x, y) : y ≥ 0, q₀·y ≤ z}` (formalized as a supremum, so that no continuity of
`u` is needed). If `(x*, y*)` solves the UMP `max u(x, y)` s.t. `p·x + q·y ≤ w`, then
`(x*, z*) = (x*, q₀·y*)` solves the composite problem `max ũ(x, z)` s.t. `p·x + α z ≤ w`, with
the same value (`exercise_3_G_5a`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice

variable {A B : ℕ}

/-- **Exercise 3.G.5** (MWG, p. 99). The composite-commodity utility
`ũ(x, z) = sup {u(x, y) : y ≥ 0, q₀·y ≤ z}`. -/
noncomputable def compositeUtility (u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ) (q0 : Fin B → ℝ)
    (x : Fin A → ℝ) (z : ℝ) : ℝ :=
  sSup ((fun y => u x y) '' {y | y ∈ nonnegOrthant B ∧ q0 ⬝ᵥ y ≤ z})

/-- **Exercise 3.G.5(a)** (MWG, p. 100). Let `q = α q₀` with `α > 0`, `q₀ ≫ 0`, and let
`(x*, y*)` solve `max u(x, y)` subject to `x ≥ 0`, `y ≥ 0`, `p·x + q·y ≤ w`. Then
`ũ(x*, q₀·y*) = u(x*, y*)`, and `(x*, q₀·y*)` solves `max ũ(x, z)` subject to `x ≥ 0`, `z ≥ 0`,
`p·x + α z ≤ w`: the consumer's actual `x` and `z = q₀·y` solve the composite problem. -/
theorem exercise_3_G_5a {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {p : Fin A → ℝ}
    {q0 : Fin B → ℝ} (hq0 : StrictlyPositive q0) {α w : ℝ} (hα : 0 < α)
    {xs : Fin A → ℝ} {ys : Fin B → ℝ}
    (hfeas : xs ∈ nonnegOrthant A ∧ ys ∈ nonnegOrthant B ∧ p ⬝ᵥ xs + (α • q0) ⬝ᵥ ys ≤ w)
    (hopt : ∀ x y, x ∈ nonnegOrthant A → y ∈ nonnegOrthant B →
      p ⬝ᵥ x + (α • q0) ⬝ᵥ y ≤ w → u x y ≤ u xs ys) :
    compositeUtility u q0 xs (q0 ⬝ᵥ ys) = u xs ys ∧
      (xs ∈ nonnegOrthant A ∧ 0 ≤ q0 ⬝ᵥ ys ∧ p ⬝ᵥ xs + α * (q0 ⬝ᵥ ys) ≤ w) ∧
      ∀ x z, x ∈ nonnegOrthant A → 0 ≤ z → p ⬝ᵥ x + α * z ≤ w →
        compositeUtility u q0 x z ≤ compositeUtility u q0 xs (q0 ⬝ᵥ ys) := by
  have hsmul : ∀ y : Fin B → ℝ, (α • q0) ⬝ᵥ y = α * (q0 ⬝ᵥ y) := fun y => by
    rw [smul_dotProduct, smul_eq_mul]
  have hz0 : 0 ≤ q0 ⬝ᵥ ys := Finset.sum_nonneg fun l _ => mul_nonneg (hq0 l).le (hfeas.2.1 l)
  -- any `(x, z)` feasible for the composite problem is dominated by `u(x*, y*)`
  have hdom : ∀ x z, x ∈ nonnegOrthant A → 0 ≤ z → p ⬝ᵥ x + α * z ≤ w →
      compositeUtility u q0 x z ≤ u xs ys := by
    intro x z hx hz hb
    have hne : ((fun y => u x y) '' {y | y ∈ nonnegOrthant B ∧ q0 ⬝ᵥ y ≤ z}).Nonempty :=
      ⟨u x 0, 0, ⟨fun _ => le_rfl, by simpa using hz⟩, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨y, ⟨hy, hyz⟩, rfl⟩
    refine hopt x y hx hy ?_
    rw [hsmul]
    nlinarith
  have hval : compositeUtility u q0 xs (q0 ⬝ᵥ ys) = u xs ys := by
    refine le_antisymm (hdom xs _ hfeas.1 hz0 (by rw [← hsmul]; exact hfeas.2.2)) ?_
    have hbdd : BddAbove ((fun y => u xs y) ''
        {y | y ∈ nonnegOrthant B ∧ q0 ⬝ᵥ y ≤ q0 ⬝ᵥ ys}) := by
      refine ⟨u xs ys, ?_⟩
      rintro _ ⟨y, ⟨hy, hyz⟩, rfl⟩
      refine hopt xs y hfeas.1 hy ?_
      rw [hsmul]
      have := hfeas.2.2
      rw [hsmul] at this
      nlinarith
    exact le_csSup hbdd ⟨ys, ⟨hfeas.2.1, le_rfl⟩, rfl⟩
  refine ⟨hval, ⟨hfeas.1, hz0, by rw [← hsmul]; exact hfeas.2.2⟩, fun x z hx hz hb => ?_⟩
  rw [hval]
  exact hdom x z hx hz hb

end MWG.ClassicalDemand
