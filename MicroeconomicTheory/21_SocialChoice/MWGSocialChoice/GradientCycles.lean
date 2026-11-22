/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Plane
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.LinearCombination

/-!
# Condorcet cycles near a point where the gradients span the plane

MWG, Exercises 21.D.7 and 21.D.8, p. 813.

Three agents have utilities `uᵢ` on a set `X ⊆ ℝ²` (modelled by `ℂ`) containing a neighbourhood
of the origin, differentiable at the origin with gradients `gᵢ` (MWG assumes `X` convex and
the `uᵢ` continuously differentiable; we only use differentiability at `0`). If the cone spanned
by the gradients is the whole plane then (a) there is a Condorcet cycle `x, y, z ∈ X`, and (b)
for every `x ≠ 0` there is `y ∈ X` with `‖x - y‖ < ‖x‖` preferred to the origin by two agents
(without the hint's linearity assumption).

The construction: the cone condition gives `λ ≫ 0` with `∑ λᵢ gᵢ = 0`, so the signed areas
`D(g₀, g₁)`, `D(g₁, g₂)`, `D(g₂, g₀)` are nonzero with a common sign `σ`; the directions
`d₀ = σ I (g₂ - g₁)`, `d₁ = σ I (g₀ - g₂)`, `d₂ = σ I (g₁ - g₀)` sum to zero and each makes
exactly the two agents other than `k` better off to first order.

**Correction.** In (b) the point `x` must be nonzero: for `x = 0` no `y` satisfies
`‖x - y‖ < ‖x‖`.

Exercise 21.D.8: we prove part (c) for linear utilities (a directional median agent, which for
linear utilities is the same at every point, rules out Condorcet cycles). Parts (a) (existence
of a directional median for a pointed gradient cone) and (b) (an example with a changing median
and a Condorcet cycle), and (c) for the literal notion, are in `DirectionalMedian`.
-/

namespace MWG.SocialChoice

open Finset Filter Topology

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Two of the three agents strictly prefer `a` to `b`: a strict majority. -/
def TwoAgentsPrefer (u : Fin 3 → ℂ → ℝ) (a b : ℂ) : Prop :=
  ∃ i j, i ≠ j ∧ u i b < u i a ∧ u j b < u j a

/-- First-order comparison: if `u` has gradient `g` at `0` and `⟪g, a - b⟫ > 0`, then
`u(ta) > u(tb)` for all small `t > 0`. -/
theorem eventually_gradient_lt {f : ℂ → ℝ} {g : ℂ} (hf : HasGradientAt f g 0) {a b : ℂ}
    (hab : 0 < ⟪g, a - b⟫) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f ((t : ℝ) • b) < f ((t : ℝ) • a) := by
  have hF := hf.hasFDerivAt
  have hpath : ∀ c : ℂ, HasDerivAt (fun t : ℝ => f (t • c)) ⟪g, c⟫ 0 := by
    intro c
    have hγ : HasDerivAt (fun t : ℝ => t • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const c
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hF hγ (zero_smul ℝ c).symm
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
  have hφ : HasDerivAt (fun t : ℝ => f (t • a) - f (t • b)) ⟪g, a - b⟫ 0 := by
    rw [inner_sub_right]
    exact (hpath a).sub (hpath b)
  have hslope := hasDerivAt_iff_tendsto_slope.1 hφ
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope (fun t : ℝ => f (t • a) - f (t • b)) 0 t :=
    hslope.eventually (lt_mem_nhds hab)
  have hpos' := (hpos.filter_mono (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).and
    self_mem_nhdsWithin
  filter_upwards [hpos'] with t ht
  obtain ⟨h1, h2⟩ := ht
  have h2' : (0 : ℝ) < t := h2
  rw [slope_def_field] at h1
  simp only [zero_smul, sub_self, sub_zero] at h1
  have := (div_pos_iff_of_pos_right h2').1 h1
  linarith

/-- The signed area `D(a, b) = ⟪a, I b⟫`. -/
theorem area_antisymm (a b : ℂ) : ⟪a, Complex.I * b⟫ = -⟪b, Complex.I * a⟫ := by
  rw [inner_I_mul, inner_I_mul]
  ring

/-- `D(a, a) = 0`. -/
theorem area_self (a : ℂ) : ⟪a, Complex.I * a⟫ = 0 := by
  rw [inner_I_mul]
  ring

/-- The structure of three gradients whose cone is the plane: three directions summing to
zero, each improving (to first order) exactly the two agents other than its index, and such that
every nonzero vector makes a positive inner product with one of them. -/
theorem cone_directions {g : Fin 3 → ℂ}
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) :
    ∃ d0 d1 d2 : ℂ, d0 + d1 + d2 = 0 ∧ 0 < ⟪g 1, d0⟫ ∧ 0 < ⟪g 2, d0⟫ ∧ 0 < ⟪g 0, d1⟫ ∧
      0 < ⟪g 2, d1⟫ ∧ 0 < ⟪g 0, d2⟫ ∧ 0 < ⟪g 1, d2⟫ ∧
      ∀ x : ℂ, x ≠ 0 → 0 < ⟪x, d0⟫ ∨ 0 < ⟪x, d1⟫ ∨ 0 < ⟪x, d2⟫ := by
  obtain ⟨μ, hμ, hv⟩ := hcone (-(g 0 + g 1 + g 2))
  simp only [Fin.sum_univ_three] at hv
  set l : Fin 3 → ℝ := fun i => μ i + 1
  have hl : ∀ i, 0 < l i := fun i => by simp only [l]; linarith [hμ i]
  have hsum : l 0 • g 0 + l 1 • g 1 + l 2 • g 2 = 0 := by
    simp only [l, add_smul, one_smul]
    rw [show μ 0 • g 0 + g 0 + (μ 1 • g 1 + g 1) + (μ 2 • g 2 + g 2) =
      (μ 0 • g 0 + μ 1 • g 1 + μ 2 • g 2) + (g 0 + g 1 + g 2) by abel, ← hv]
    abel
  set D : ℂ → ℂ → ℝ := fun a b => ⟪a, Complex.I * b⟫ with hD
  have Dlin : ∀ c, l 0 * D (g 0) c + l 1 * D (g 1) c + l 2 * D (g 2) c = 0 := by
    intro c
    have : D (l 0 • g 0 + l 1 • g 1 + l 2 • g 2) c = 0 := by
      rw [hsum]
      simp only [hD, inner_zero_left]
    simpa only [hD, inner_add_left, real_inner_smul_left] using this
  have Danti : ∀ a b, D a b = -D b a := area_antisymm
  have Dself : ∀ a, D a a = 0 := area_self
  set σ := D (g 0) (g 1) with hσdef
  have e0 := Dlin (g 0)
  have e1 := Dlin (g 1)
  rw [Dself, Danti (g 1) (g 0)] at e0
  rw [Dself] at e1
  have hD20 : D (g 2) (g 0) = l 1 * σ / l 2 := by
    field_simp [(hl 2).ne']
    linarith
  have hD21 : D (g 2) (g 1) = -(l 0 * σ / l 2) := by
    field_simp [(hl 2).ne']
    linarith
  have hD02 : D (g 0) (g 2) = -(l 1 * σ / l 2) := by rw [Danti, hD20]
  have hD12 : D (g 1) (g 2) = l 0 * σ / l 2 := by rw [Danti, hD21, neg_neg]
  have hD10 : D (g 1) (g 0) = -σ := by rw [Danti]
  have hσ : σ ≠ 0 := by
    intro hσ0
    have z : ∀ k i, D (g k) (g i) = 0 := by
      intro k i
      fin_cases k <;> fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Dself, hD20, hD21,
          hD02, hD12, hD10, ← hσdef, hσ0, mul_zero, zero_div, neg_zero]
    by_cases hall : ∀ k, g k = 0
    · obtain ⟨μ', -, hv'⟩ := hcone 1
      simp only [hall, smul_zero, sum_const_zero] at hv'
      exact one_ne_zero hv'
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      obtain ⟨μ', -, hv'⟩ := hcone (Complex.I * g k)
      have h1 : D (g k) (Complex.I * g k) = 0 := by
        rw [hv']
        have e : ∀ i, ⟪g k, Complex.I * (μ' i • g i)⟫ = μ' i * D (g k) (g i) := fun i => by
          rw [mul_smul_comm, inner_smul_right]
        have z' : ∀ i, ⟪g k, Complex.I * g i⟫ = 0 := fun i => z k i
        simp only [hD, Fin.sum_univ_three, mul_add, inner_add_right, e]
        rw [z' 0, z' 1, z' 2]
        ring
      have h2 : D (g k) (Complex.I * g k) = -‖g k‖ ^ 2 := by
        simp only [hD, ← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right,
          real_inner_self_eq_norm_sq]
      rw [h2] at h1
      have : ‖g k‖ = 0 := by nlinarith [norm_nonneg (g k)]
      exact hk (norm_eq_zero.1 this)
  have key : ∀ i c c' : ℂ, ⟪i, σ • (Complex.I * (c - c'))⟫ = σ * (D i c - D i c') := by
    intro i c c'
    simp only [hD, inner_smul_right, mul_sub, inner_sub_right]
  have p1 : 0 < σ * σ := mul_self_pos.2 hσ
  have pa : 0 < σ * (l 1 * σ / l 2) := by
    have : σ * (l 1 * σ / l 2) = l 1 * (σ * σ) / l 2 := by ring
    rw [this]
    exact div_pos (mul_pos (hl 1) p1) (hl 2)
  have pb : 0 < σ * (l 0 * σ / l 2) := by
    have : σ * (l 0 * σ / l 2) = l 0 * (σ * σ) / l 2 := by ring
    rw [this]
    exact div_pos (mul_pos (hl 0) p1) (hl 2)
  refine ⟨σ • (Complex.I * (g 2 - g 1)), σ • (Complex.I * (g 0 - g 2)),
    σ • (Complex.I * (g 1 - g 0)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add, ← smul_add, ← mul_add, ← mul_add]
    simp
  · rw [key, hD12, Dself]; linarith
  · rw [key, Dself, hD21]; linarith
  · rw [key, Dself, hD02]; linarith
  · rw [key, hD20, Dself]; linarith
  · rw [key, ← hσdef, Dself]; linarith
  · rw [key, Dself, hD10]; linarith
  · intro x hx
    by_contra hc
    push Not at hc
    obtain ⟨c0, c1, c2⟩ := hc
    have hsum0 : ⟪x, σ • (Complex.I * (g 2 - g 1))⟫ + ⟪x, σ • (Complex.I * (g 0 - g 2))⟫ +
        ⟪x, σ • (Complex.I * (g 1 - g 0))⟫ = 0 := by
      rw [← inner_add_right, ← inner_add_right, ← smul_add, ← smul_add, ← mul_add, ← mul_add]
      simp
    have z0 : ⟪x, σ • (Complex.I * (g 2 - g 1))⟫ = 0 := by linarith
    have z1 : ⟪x, σ • (Complex.I * (g 0 - g 2))⟫ = 0 := by linarith
    have hIx : Complex.I * x ≠ 0 := mul_ne_zero Complex.I_ne_zero hx
    have o0 : ⟪σ • (Complex.I * (g 2 - g 1)), Complex.I * (Complex.I * x)⟫ = 0 := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right, real_inner_comm, z0,
        neg_zero]
    have o1 : ⟪σ • (Complex.I * (g 0 - g 2)), Complex.I * (Complex.I * x)⟫ = 0 := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, inner_neg_right, real_inner_comm, z1,
        neg_zero]
    have hc := collinear_of_orth hIx o0 o1
    have hval : ⟪σ • (Complex.I * (g 2 - g 1)), Complex.I * (σ • (Complex.I * (g 0 - g 2)))⟫ =
        σ * σ * (D (g 2) (g 0) - D (g 2) (g 2) - D (g 1) (g 0) + D (g 1) (g 2)) := by
      simp only [hD, inner_I_mul, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
        Complex.sub_im]
      ring
    rw [hval, hD20, Dself, hD10, hD12] at hc
    have : 0 < σ * σ * (l 1 * σ / l 2 - 0 - -σ + l 0 * σ / l 2) * σ := by
      have : σ * σ * (l 1 * σ / l 2 - 0 - -σ + l 0 * σ / l 2) * σ =
          (σ * σ) * ((l 1 * (σ * σ) / l 2) + σ * σ + (l 0 * (σ * σ) / l 2)) := by ring
      rw [this]
      exact mul_pos p1 (add_pos (add_pos (div_pos (mul_pos (hl 1) p1) (hl 2)) p1)
        (div_pos (mul_pos (hl 0) p1) (hl 2)))
    rw [hc, zero_mul] at this
    exact lt_irrefl _ this

/-- **Exercise 21.D.7(a)** (MWG, p. 813). If three utilities are differentiable at the origin,
an interior point of `X`, with gradients whose cone is `ℝ²`, then there are `x, y, z ∈ X` forming
a Condorcet cycle: a strict majority prefers `x` to `y`, `y` to `z`, and `z` to `x`. -/
theorem exercise_21_D_7a {X : Set ℂ} (hX : X ∈ 𝓝 (0 : ℂ)) {u : Fin 3 → ℂ → ℝ} {g : Fin 3 → ℂ}
    (hu : ∀ i, HasGradientAt (u i) (g i) 0)
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ z ∈ X, TwoAgentsPrefer u x y ∧ TwoAgentsPrefer u y z ∧
      TwoAgentsPrefer u z x := by
  obtain ⟨d0, d1, d2, hs, a10, a20, a01, a21, a02, a12, -⟩ := cone_directions hcone
  have hy : (-d0) = d1 + d2 := by linear_combination (-1 : ℂ) * hs
  have tend : ∀ c : ℂ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (t : ℝ) • c ∈ X := fun c => by
    have : Tendsto (fun t : ℝ => t • c) (𝓝[>] 0) (𝓝 0) := by
      exact ((continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds
    exact this hX
  have i1 : 0 < ⟪g 1, (0 : ℂ) - -d0⟫ := by simpa using a10
  have i2 : 0 < ⟪g 2, (0 : ℂ) - -d0⟫ := by simpa using a20
  have j0 : 0 < ⟪g 0, -d0 - d2⟫ := by rw [hy]; simpa using a01
  have j2 : 0 < ⟪g 2, -d0 - d2⟫ := by rw [hy]; simpa using a21
  have k0 : 0 < ⟪g 0, d2 - 0⟫ := by simpa using a02
  have k1 : 0 < ⟪g 1, d2 - 0⟫ := by simpa using a12
  obtain ⟨t, ht⟩ := ((eventually_gradient_lt (hu 1) i1).and ((eventually_gradient_lt (hu 2) i2).and
    ((eventually_gradient_lt (hu 0) j0).and ((eventually_gradient_lt (hu 2) j2).and
    ((eventually_gradient_lt (hu 0) k0).and ((eventually_gradient_lt (hu 1) k1).and
    ((tend 0).and ((tend (-d0)).and (tend d2))))))))).exists
  obtain ⟨b1, b2, b3, b4, b5, b6, m1, m2, m3⟩ := ht
  refine ⟨t • 0, m1, t • (-d0), m2, t • d2, m3, ⟨1, 2, by decide, b1, b2⟩,
    ⟨0, 2, by decide, b3, b4⟩, ⟨0, 1, by decide, b5, b6⟩⟩

/-- **Exercise 21.D.7(b)** (MWG, p. 813), for `x ≠ 0` (correction: for `x = 0` no `y` has
`‖x - y‖ < ‖x‖`). Under the hypotheses of (a), for every `x ≠ 0` there is `y ∈ X` with
`‖x - y‖ < ‖x‖` that two agents prefer to the origin (the status quo). No linearity is
assumed. -/
theorem exercise_21_D_7b {X : Set ℂ} (hX : X ∈ 𝓝 (0 : ℂ)) {u : Fin 3 → ℂ → ℝ} {g : Fin 3 → ℂ}
    (hu : ∀ i, HasGradientAt (u i) (g i) 0)
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) {x : ℂ}
    (hx : x ≠ 0) : ∃ y ∈ X, ‖x - y‖ < ‖x‖ ∧ TwoAgentsPrefer u y 0 := by
  obtain ⟨d0, d1, d2, -, a10, a20, a01, a21, a02, a12, hpos⟩ := cone_directions hcone
  have tend : ∀ c : ℂ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (t : ℝ) • c ∈ X := fun c => by
    have : Tendsto (fun t : ℝ => t • c) (𝓝[>] 0) (𝓝 0) := by
      exact ((continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds
    exact this hX
  have closer : ∀ d : ℂ, 0 < ⟪x, d⟫ → ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖x - (t : ℝ) • d‖ < ‖x‖ := by
    intro d hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have hn : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hd0) 2
    filter_upwards [Ioo_mem_nhdsGT (div_pos (mul_pos two_pos hd) hn)] with t ht
    obtain ⟨h0, h1⟩ := ht
    rw [lt_div_iff₀ hn] at h1
    have e : ‖x - t • d‖ ^ 2 = ‖x‖ ^ 2 - 2 * t * ⟪x, d⟫ + t ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have : ‖x - t • d‖ ^ 2 < ‖x‖ ^ 2 := by rw [e]; nlinarith
    nlinarith [norm_nonneg (x - t • d), norm_nonneg x]
  have zero_smul' : ∀ t : ℝ, (t • (0 : ℂ)) = 0 := fun t => smul_zero t
  rcases hpos x hx with h | h | h
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d0 h).and ((eventually_gradient_lt (hu 1)
      (b := 0) (by simpa using a10)).and ((eventually_gradient_lt (hu 2) (b := 0)
      (by simpa using a20)).and (tend d0)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d0, h4, h1, 1, 2, by decide, h2, h3⟩
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d1 h).and ((eventually_gradient_lt (hu 0)
      (b := 0) (by simpa using a01)).and ((eventually_gradient_lt (hu 2) (b := 0)
      (by simpa using a21)).and (tend d1)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d1, h4, h1, 0, 2, by decide, h2, h3⟩
  · obtain ⟨t, h1, h2, h3, h4⟩ := ((closer d2 h).and ((eventually_gradient_lt (hu 0)
      (b := 0) (by simpa using a02)).and ((eventually_gradient_lt (hu 1) (b := 0)
      (by simpa using a12)).and (tend d2)))).exists
    rw [zero_smul'] at h2 h3
    exact ⟨t • d2, h4, h1, 0, 1, by decide, h2, h3⟩

/-- **Exercise 21.D.7(b)**, correction. For `x = 0` the requirement `‖x - y‖ < ‖x‖` is
impossible. -/
theorem exercise_21_D_7b_zero (y : ℂ) : ¬‖(0 : ℂ) - y‖ < ‖(0 : ℂ)‖ := by
  simp only [norm_zero, not_lt]
  exact norm_nonneg _

/-- **Exercise 21.D.8(a)** (MWG, p. 813), the property, for linear utilities `uᵢ(v) = ⟪gᵢ, v⟫`:
agent `h` is a directional median: every move having a strict majority makes `h` strictly
better off. -/
def IsDirectionalMedian (g : Fin 3 → ℂ) (h : Fin 3) : Prop :=
  ∀ d : ℂ, (∃ i j, i ≠ j ∧ 0 < ⟪g i, d⟫ ∧ 0 < ⟪g j, d⟫) → 0 < ⟪g h, d⟫

/-- **Exercise 21.D.8(c)** (MWG, p. 813), linear case. If, with linear utilities, some agent is
a directional median (necessarily the same at every point), there is no Condorcet cycle. -/
theorem exercise_21_D_8c {g : Fin 3 → ℂ} {h : Fin 3} (hh : IsDirectionalMedian g h)
    (x y z : ℂ) :
    ¬(TwoAgentsPrefer (fun i v => ⟪g i, v⟫) x y ∧ TwoAgentsPrefer (fun i v => ⟪g i, v⟫) y z ∧
      TwoAgentsPrefer (fun i v => ⟪g i, v⟫) z x) := by
  rintro ⟨⟨i1, j1, h1, a1, b1⟩, ⟨i2, j2, h2, a2, b2⟩, ⟨i3, j3, h3, a3, b3⟩⟩
  have c1 := hh (x - y) ⟨i1, j1, h1, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  have c2 := hh (y - z) ⟨i2, j2, h2, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  have c3 := hh (z - x) ⟨i3, j3, h3, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  rw [inner_sub_right] at c1 c2 c3
  linarith

/-- **Exercise 21.D.8(c)**, instance. With gradients `1, 1, I` (a pointed cone), agent `0` is a
directional median. -/
theorem exercise_21_D_8c_instance : IsDirectionalMedian ![1, 1, Complex.I] 0 := by
  rintro d ⟨i, j, hij, hi, hj⟩
  fin_cases i <;> fin_cases j <;> simp_all

end MWG.SocialChoice
