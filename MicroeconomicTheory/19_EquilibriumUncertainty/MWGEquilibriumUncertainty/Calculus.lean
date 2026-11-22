/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.ArrowDebreu
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# First-order tools for Chapter 19

The chapter's examples and exercises use first-order conditions at interior optima. This module
proves the elementary facts they rest on, with no differentiability beyond what each statement
names.

* One-sided derivative tests: a positive derivative gives strict increase just to the right of
  the point (`eventually_lt_of_hasDerivAt_pos`); a one-sided maximum gives a nonpositive
  derivative (`hasDerivAt_nonpos_of_eventually_le`).
* The alternative for a single linear inequality: if `a·d ≤ 0` whenever `q·d ≤ 0`, then
  `a = α q` with `α ≥ 0` (`exists_nonneg_smul_of_dot_nonpos`), the Lagrange condition for one
  budget constraint.
* Directional first-order conditions for a consumer maximizing on `{x ≥ 0 : p·x ≤ w}` at an
  interior point (`foc_dir`), and the strict decrease of the derivative of a strictly concave
  function (`hasDerivAt_lt_of_strictConcaveOn`).
* Demand of a quasilinear consumer with utility `b ln x₁ + x₂` (`quasilinearLog_le`,
  `quasilinearLog_eq_iff`).
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology

variable {S L : ℕ}

/-- A positive derivative at `a` gives `g a < g t` for all `t > a` close to `a`. -/
theorem eventually_lt_of_hasDerivAt_pos {g : ℝ → ℝ} {g' a : ℝ} (hg : HasDerivAt g g' a)
    (hpos : 0 < g') : ∀ᶠ t in 𝓝[>] a, g a < g t := by
  have h1 := (hasDerivAt_iff_tendsto_slope.mp hg).eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ t in 𝓝[>] a, 0 < slope g a t := h1.filter_mono (nhdsGT_le_nhdsNE a)
  filter_upwards [h2, self_mem_nhdsWithin] with t ht hta
  rw [slope_def_field] at ht
  have hta' : 0 < t - a := sub_pos.mpr hta
  have := (div_pos_iff_of_pos_right hta').mp ht
  linarith

/-- A one-sided (right) local maximum at `a` gives a nonpositive derivative. -/
theorem hasDerivAt_nonpos_of_eventually_le {g : ℝ → ℝ} {g' a : ℝ} (hg : HasDerivAt g g' a)
    (hmax : ∀ᶠ t in 𝓝[>] a, g t ≤ g a) : g' ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨t, h1, h2⟩ := ((eventually_lt_of_hasDerivAt_pos hg h).and hmax).exists
  linarith

/-- **The alternative for one linear inequality** (the Lagrange condition behind every first-order
condition of the chapter). If `a·d ≤ 0` for every `d` with `q·d ≤ 0`, then `a = α q` for some
`α ≥ 0`. -/
theorem exists_nonneg_smul_of_dot_nonpos {n : Type*} [Fintype n] {a q : n → ℝ}
    (h : ∀ d, q ⬝ᵥ d ≤ 0 → a ⬝ᵥ d ≤ 0) : ∃ α : ℝ, 0 ≤ α ∧ a = α • q := by
  classical
  by_cases hq : q ⬝ᵥ q = 0
  · have hq0 : q = 0 := dotProduct_self_eq_zero.mp hq
    refine ⟨0, le_rfl, ?_⟩
    have ha : a ⬝ᵥ a = 0 := by
      apply le_antisymm (h a (by simp [hq0]))
      have := h (-a) (by simp [hq0])
      rw [dotProduct_neg] at this
      linarith
    rw [dotProduct_self_eq_zero.mp ha, zero_smul]
  · have hqq : 0 < q ⬝ᵥ q :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (q i)) (Ne.symm hq)
    set α := (a ⬝ᵥ q) / (q ⬝ᵥ q) with hα
    have hker : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0 := by
      intro d hd
      apply le_antisymm (h d hd.le)
      have := h (-d) (by rw [dotProduct_neg, hd, neg_zero])
      rw [dotProduct_neg] at this
      linarith
    have hα0 : 0 ≤ α := by
      have := h (-q) (by rw [dotProduct_neg]; linarith)
      rw [dotProduct_neg] at this
      exact div_nonneg (by linarith) hqq.le
    refine ⟨α, hα0, ?_⟩
    have hd : ∀ d, a ⬝ᵥ d = α * (q ⬝ᵥ d) := by
      intro d
      have h0 := hker (d - ((q ⬝ᵥ d) / (q ⬝ᵥ q)) • q) (by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hq, sub_self])
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h0
      rw [h0, hα, dotProduct_comm a q]
      field_simp
    funext k
    have := hd (Pi.single k 1)
    simpa [dotProduct_single] using this

/-- The value is linear along a ray. -/
theorem cval_add_smul (p x d : CVec S L) (t : ℝ) :
    cval p (x + t • d) = cval p x + t * cval p d := by
  simp only [cval, Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- **Directional first-order condition**. If `x*` is strictly positive and maximizes `U` on
`{x ≥ 0 : p·x ≤ w}`, then along every direction `d` with `p·d ≤ 0` the derivative of
`t ↦ U(x* + t d)` at `0` is nonpositive. -/
theorem foc_dir {U : CVec S L → ℝ} {p x : CVec S L} {w : ℝ} (hx : ∀ s l, 0 < x s l)
    (hb : cval p x ≤ w) (hmax : ∀ x', NonnegC x' → cval p x' ≤ w → U x' ≤ U x)
    {d : CVec S L} (hd : cval p d ≤ 0) {D : ℝ}
    (hD : HasDerivAt (fun t : ℝ => U (x + t • d)) D 0) :
    D ≤ 0 := by
  refine hasDerivAt_nonpos_of_eventually_le hD ?_
  have hpos : ∀ s l, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x s l + t * d s l := by
    intro s l
    have hc : Tendsto (fun t : ℝ => x s l + t * d s l) (𝓝 0) (𝓝 (x s l + 0 * d s l)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at hc
    exact (hc.eventually (lt_mem_nhds (hx s l))).filter_mono nhdsWithin_le_nhds |>.mono
      fun t ht => ht.le
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ s l, 0 ≤ x s l + t * d s l :=
    eventually_all.2 fun s => eventually_all.2 fun l => hpos s l
  filter_upwards [hall, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_smul, add_zero]
  apply hmax
  · intro s l; simpa using ht s l
  · rw [cval_add_smul]
    have : t * cval p d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt htpos) hd
    linarith

/-- The derivative of a strictly concave function is strictly decreasing (derivatives given as
`HasDerivAt` values). -/
theorem hasDerivAt_lt_of_strictConcaveOn {D : Set ℝ} {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ D u)
    {x y a b : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) (ha : HasDerivAt u a x)
    (hb : HasDerivAt u b y) : b < a :=
  (hu.lt_slope_of_hasDerivAt hx hy hxy hb).trans (hu.slope_lt_of_hasDerivAt hx hy hxy ha)

/-- The derivative of a strictly concave function determines the point. -/
theorem eq_of_hasDerivAt_eq_of_strictConcaveOn {D : Set ℝ} {u : ℝ → ℝ}
    (hu : StrictConcaveOn ℝ D u) {x y a : ℝ} (hx : x ∈ D) (hy : y ∈ D) (ha : HasDerivAt u a x)
    (hb : HasDerivAt u a y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (hasDerivAt_lt_of_strictConcaveOn hu hx hy h ha hb) (lt_irrefl a)
  · exact h
  · exact absurd (hasDerivAt_lt_of_strictConcaveOn hu hy hx h hb ha) (lt_irrefl a)

/-! ## Quasilinear logarithmic demand -/

/-- The quasilinear utility `b ln x₁ + x₂` is at most `b ln(b/p) - b + w` on the budget set
`{x₁ > 0, p x₁ + x₂ ≤ w}` (`b, p > 0`). -/
theorem quasilinearLog_le {b p w x₁ x₂ : ℝ} (hb : 0 < b) (hp : 0 < p) (hx : 0 < x₁)
    (hbud : p * x₁ + x₂ ≤ w) : b * Real.log x₁ + x₂ ≤ b * Real.log (b / p) - b + w := by
  have hr : 0 < x₁ / (b / p) := div_pos hx (div_pos hb hp)
  have hl := Real.log_le_sub_one_of_pos hr
  rw [Real.log_div hx.ne' (div_pos hb hp).ne'] at hl
  have h2 : b * (x₁ / (b / p)) = p * x₁ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hl hb.le]

/-- The maximum `b ln(b/p) - b + w` is attained exactly at `x₁ = b/p`, `x₂ = w - b`: a bundle of
the budget set attaining it has `x₁ = b/p` (and spends its whole budget). -/
theorem quasilinearLog_eq_iff {b p w x₁ x₂ : ℝ} (hb : 0 < b) (hp : 0 < p) (hx : 0 < x₁)
    (hbud : p * x₁ + x₂ ≤ w) (hge : b * Real.log (b / p) - b + w ≤ b * Real.log x₁ + x₂) :
    x₁ = b / p ∧ x₂ = w - b := by
  have hbp : 0 < b / p := div_pos hb hp
  by_contra hne
  have hx1 : x₁ = b / p := by
    by_contra h1
    have hr : 0 < x₁ / (b / p) := div_pos hx hbp
    have hr1 : x₁ / (b / p) ≠ 1 := by
      intro h; apply h1; rw [div_eq_one_iff_eq hbp.ne'] at h; exact h
    have hl : Real.log (x₁ / (b / p)) < x₁ / (b / p) - 1 := by
      have := Real.add_one_lt_exp (Real.log_ne_zero_of_pos_of_ne_one hr hr1)
      rw [Real.exp_log hr] at this; linarith
    rw [Real.log_div hx.ne' hbp.ne'] at hl
    have h2 : b * (x₁ / (b / p)) = p * x₁ := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hl hb]
  refine hne ⟨hx1, ?_⟩
  rw [hx1] at hbud hge
  have : p * (b / p) = b := by field_simp
  linarith

/-- A bundle `(b/p, w - b)` attains the maximum of `quasilinearLog_le`. -/
theorem quasilinearLog_at (b p w : ℝ) :
    b * Real.log (b / p) + (w - b) = b * Real.log (b / p) - b + w := by ring

end MWG.EquilibriumUncertainty
