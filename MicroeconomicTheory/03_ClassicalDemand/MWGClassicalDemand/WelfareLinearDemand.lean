/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareExercises

/-!
# Welfare evaluation with linear demand systems: Exercises 3.I.7 and 3.I.8

MWG, Exercises 3.I.7 and 3.I.8 (p. 103). Three goods, good 3 the numeraire (`p₃ = 1`); the
demands for goods 1 and 2 do not depend on wealth:
`x₁ = a₁ + b₁p₁ + c₁p₂ + d₁p₁p₂`, `x₂ = a₂ + b₂p₁ + c₂p₂ + d₂p₁p₂` (Exercise 3.I.7 is the case
`d₁ = d₂ = 0`, with `(a, b, c, d, e, g) = (a₁, b₁, c₁, a₂, b₂, c₂)`).

Without wealth effects the equivalent variation is the line integral of demand (Exercise 3.I.1,
`marshallian_surplus`); `bilinEV` is that integral along the path that changes `p₁` first and
`bilinEVAlt` along the path that changes `p₂` first.

* 3.I.7(a) and 3.I.8(b): symmetry and negative semidefiniteness of the Slutsky matrix give
  `c = e`, `b ≤ 0`, `g ≤ 0`, `c² ≤ bg` (and `d₁ = d₂ = 0` in 3.I.8).
* 3.I.7(b): without symmetry the two paths differ by `c - e`; (c)-(d): `EV - (EV₁ + EV₂) = -c` and
  `DW - (DW₁ + DW₂) = -c`; (e): the deadweight loss of taxes `t` is `-(tᵀSt)/2`, minimized under the
  linearized revenue constraint `t·x⁰ = R` by `t* ∝ S⁻¹x⁰` (correction-free; the linearization is
  the book's "small" revenue).
* 3.I.8(a): quasilinear utility in good 3 gives wealth-independent demand for goods 1 and 2 (the
  converse "most general class" is OPEN); (c)-(d): the welfare measure and the computations, with
  correction D7 (the parameter values of (d) violate (b)).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology MeasureTheory

/-- `∫_P^Q (A + B s) ds = A(Q - P) + B(Q² - P²)/2`. -/
theorem integral_affine (A B P Q : ℝ) :
    ∫ s in P..Q, (A + B * s) = A * (Q - P) + B * (Q ^ 2 - P ^ 2) / 2 := by
  have h : ∫ s in P..Q, (A + B * s) = (∫ _ in P..Q, A) + ∫ s in P..Q, B * s :=
    intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_const.mul continuous_id').intervalIntegrable _ _)
  rw [h, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- The (negative) line integral of the demands `x₁ = a₁ + b₁p₁ + c₁p₂ + d₁p₁p₂`,
`x₂ = a₂ + b₂p₁ + c₂p₂ + d₂p₁p₂` from `(P₁, P₂)` to `(Q₁, Q₂)`, changing `p₁` first. -/
noncomputable def bilinEV (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ : ℝ) : ℝ :=
  -((∫ s in P₁..Q₁, (a₁ + b₁ * s + c₁ * P₂ + d₁ * s * P₂)) +
    ∫ s in P₂..Q₂, (a₂ + b₂ * Q₁ + c₂ * s + d₂ * Q₁ * s))

/-- The same line integral along the path changing `p₂` first. -/
noncomputable def bilinEVAlt (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ : ℝ) : ℝ :=
  -((∫ s in P₂..Q₂, (a₂ + b₂ * P₁ + c₂ * s + d₂ * P₁ * s)) +
    ∫ s in P₁..Q₁, (a₁ + b₁ * s + c₁ * Q₂ + d₁ * s * Q₂))

/-- Closed form of `bilinEV`. -/
theorem bilinEV_eq (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ : ℝ) :
    bilinEV a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ =
      -((a₁ + c₁ * P₂) * (Q₁ - P₁) + (b₁ + d₁ * P₂) * (Q₁ ^ 2 - P₁ ^ 2) / 2 +
        ((a₂ + b₂ * Q₁) * (Q₂ - P₂) + (c₂ + d₂ * Q₁) * (Q₂ ^ 2 - P₂ ^ 2) / 2)) := by
  have h1 : (fun s => a₁ + b₁ * s + c₁ * P₂ + d₁ * s * P₂) =
      fun s => (a₁ + c₁ * P₂) + (b₁ + d₁ * P₂) * s := by funext s; ring
  have h2 : (fun s => a₂ + b₂ * Q₁ + c₂ * s + d₂ * Q₁ * s) =
      fun s => (a₂ + b₂ * Q₁) + (c₂ + d₂ * Q₁) * s := by funext s; ring
  rw [bilinEV, h1, h2, integral_affine, integral_affine]

/-- Closed form of `bilinEVAlt`. -/
theorem bilinEVAlt_eq (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ : ℝ) :
    bilinEVAlt a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ P₁ P₂ Q₁ Q₂ =
      -((a₂ + b₂ * P₁) * (Q₂ - P₂) + (c₂ + d₂ * P₁) * (Q₂ ^ 2 - P₂ ^ 2) / 2 +
        ((a₁ + c₁ * Q₂) * (Q₁ - P₁) + (b₁ + d₁ * Q₂) * (Q₁ ^ 2 - P₁ ^ 2) / 2)) := by
  have h1 : (fun s => a₂ + b₂ * P₁ + c₂ * s + d₂ * P₁ * s) =
      fun s => (a₂ + b₂ * P₁) + (c₂ + d₂ * P₁) * s := by funext s; ring
  have h2 : (fun s => a₁ + b₁ * s + c₁ * Q₂ + d₁ * s * Q₂) =
      fun s => (a₁ + c₁ * Q₂) + (b₁ + d₁ * Q₂) * s := by funext s; ring
  rw [bilinEVAlt, h1, h2, integral_affine, integral_affine]

/-- A `2 × 2` quadratic form `b y₁² + 2c y₁y₂ + g y₂²` is nonpositive for all `y` iff
`b ≤ 0`, `g ≤ 0`, `c² ≤ bg`. -/
theorem quadForm_nonpos_iff (b c g : ℝ) :
    (∀ y₁ y₂ : ℝ, b * y₁ ^ 2 + 2 * c * y₁ * y₂ + g * y₂ ^ 2 ≤ 0) ↔
      b ≤ 0 ∧ g ≤ 0 ∧ c ^ 2 ≤ b * g := by
  constructor
  · intro h
    have hb : b ≤ 0 := by simpa using h 1 0
    have hg : g ≤ 0 := by simpa using h 0 1
    refine ⟨hb, hg, ?_⟩
    rcases hb.lt_or_eq with hb' | hb'
    · have := h c (-b)
      nlinarith
    · subst hb'
      by_contra hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc
      have := h ((1 - g) / (2 * c)) 1
      have h' : 0 * ((1 - g) / (2 * c)) ^ 2 + 2 * c * ((1 - g) / (2 * c)) * 1 + g * 1 ^ 2 = 1 := by
        field_simp
        ring
      linarith
  · rintro ⟨hb, hg, hc⟩ y₁ y₂
    rcases hb.lt_or_eq with hb' | hb'
    · have key : b * (b * y₁ ^ 2 + 2 * c * y₁ * y₂ + g * y₂ ^ 2) =
          (b * y₁ + c * y₂) ^ 2 + (b * g - c ^ 2) * y₂ ^ 2 := by ring
      have : 0 ≤ b * (b * y₁ ^ 2 + 2 * c * y₁ * y₂ + g * y₂ ^ 2) := by
        rw [key]; nlinarith [sq_nonneg (b * y₁ + c * y₂), sq_nonneg y₂]
      by_contra hpos
      rw [not_le] at hpos
      nlinarith
    · subst hb'
      have : c = 0 := by nlinarith [sq_nonneg c]
      subst this
      nlinarith [sq_nonneg y₂]

/-- With no wealth effect for good `l`, the Slutsky entries of row `l` are the price effects. -/
theorem slutsky_eq_priceEffect_of_no_wealth {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (xv : Fin L → ℝ) {l : Fin L} (h : wealthEffect D l = 0) (k : Fin L) :
    slutskyMatrix D xv l k = priceEffect D l k := by
  simp [slutskyMatrix, h]

/-- **Exercise 3.I.7(a)** (MWG, p. 103). If the Slutsky matrix of the three-good demand is
symmetric and negative semidefinite, with (no wealth effects) `s₁₁ = b`, `s₁₂ = c`, `s₂₁ = e`,
`s₂₂ = g`, then `c = e`, `b ≤ 0`, `g ≤ 0` and `c² ≤ bg`. -/
theorem exercise_3_I_7a {S : Matrix (Fin 3) (Fin 3) ℝ} (hsym : ∀ i j, S i j = S j i)
    (hnsd : NegSemidef S) {b c e g : ℝ} (hb : S 0 0 = b) (hc : S 0 1 = c) (he : S 1 0 = e)
    (hg : S 1 1 = g) : c = e ∧ b ≤ 0 ∧ g ≤ 0 ∧ c ^ 2 ≤ b * g := by
  have hce : c = e := by rw [← hc, ← he, hsym]
  refine ⟨hce, (quadForm_nonpos_iff b c g).mp fun y₁ y₂ => ?_⟩
  have := hnsd ![y₁, y₂, 0]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
  rw [hb, hc, he, hg, ← hce] at this
  nlinarith

/-- **Exercise 3.I.7(b)** (MWG, p. 103). The line integral of demand from `(1, 1)` to `(2, 2)`:
changing `p₁` first gives `-(a + 3b/2 + c + d + 2e + 3g/2)`, changing `p₂` first gives
`-(a + 3b/2 + 2c + d + e + 3g/2)`; the two differ by `c - e`, so the estimate of the equivalent
variation is path independent iff `c = e` (symmetry). -/
theorem exercise_3_I_7b (a b c d e g : ℝ) :
    bilinEV a b c 0 d e g 0 1 1 2 2 = -(a + 3 * b / 2 + c + d + 2 * e + 3 * g / 2) ∧
      bilinEVAlt a b c 0 d e g 0 1 1 2 2 = -(a + 3 * b / 2 + 2 * c + d + e + 3 * g / 2) ∧
      bilinEV a b c 0 d e g 0 1 1 2 2 - bilinEVAlt a b c 0 d e g 0 1 1 2 2 = c - e ∧
      (bilinEV a b c 0 d e g 0 1 1 2 2 = bilinEVAlt a b c 0 d e g 0 1 1 2 2 ↔ c = e) := by
  rw [bilinEV_eq, bilinEVAlt_eq]
  refine ⟨by ring, by ring, by ring, ⟨fun h => by linarith, fun h => by rw [h]; ring⟩⟩

/-- **Exercise 3.I.7(c)** (MWG, p. 103). Under symmetry (`e = c`), with `EV₁`, `EV₂`, `EV` the
variations for the moves from `(1, 1)` to `(2, 1)`, `(1, 2)`, `(2, 2)`:
`EV - (EV₁ + EV₂) = -c`, so `EV < EV₁ + EV₂` iff the goods are substitutes (`c > 0`). -/
theorem exercise_3_I_7c (a b c d g : ℝ) :
    bilinEV a b c 0 d c g 0 1 1 2 2 -
        (bilinEV a b c 0 d c g 0 1 1 2 1 + bilinEV a b c 0 d c g 0 1 1 1 2) = -c := by
  rw [bilinEV_eq, bilinEV_eq, bilinEV_eq]
  ring

/-- The deadweight loss `-T - EV` of the taxes that raise prices from `(1, 1)` to `(Q₁, Q₂)`,
with revenue `T = (Q₁ - 1)x₁(Q) + (Q₂ - 1)x₂(Q)`, for the linear demand of Exercise 3.I.7. -/
noncomputable def linDeadweight (a b c d e g Q₁ Q₂ : ℝ) : ℝ :=
  -((Q₁ - 1) * (a + b * Q₁ + c * Q₂) + (Q₂ - 1) * (d + e * Q₁ + g * Q₂)) -
    bilinEV a b c 0 d e g 0 1 1 Q₁ Q₂

/-- **Exercise 3.I.7(d)** (MWG, p. 103). Under symmetry, `DW₁ = -b/2`, `DW₂ = -g/2`,
`DW = -(b + g)/2 - c`, so `DW - (DW₁ + DW₂) = -c`. -/
theorem exercise_3_I_7d (a b c d g : ℝ) :
    linDeadweight a b c d c g 2 1 = -b / 2 ∧ linDeadweight a b c d c g 1 2 = -g / 2 ∧
      linDeadweight a b c d c g 2 2 = -(b + g) / 2 - c ∧
      linDeadweight a b c d c g 2 2 -
        (linDeadweight a b c d c g 2 1 + linDeadweight a b c d c g 1 2) = -c := by
  simp only [linDeadweight, bilinEV_eq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **Exercise 3.I.7(e)** (MWG, p. 103), the deadweight loss of taxes `(t₁, t₂)` levied at
`(1, 1)`: under symmetry it is the quadratic form `-(b t₁² + 2c t₁t₂ + g t₂²)/2`. -/
theorem exercise_3_I_7e_deadweight (a b c d g t₁ t₂ : ℝ) :
    linDeadweight a b c d c g (1 + t₁) (1 + t₂) =
      -(b * t₁ ^ 2 + 2 * c * t₁ * t₂ + g * t₂ ^ 2) / 2 := by
  simp only [linDeadweight, bilinEV_eq]
  ring

/-- **Exercise 3.I.7(e)** (MWG, p. 103), the optimal taxes. Let `S = [[b, c], [c, g]]` be
negative semidefinite (part (a)), `x⁰ = (x₁⁰, x₂⁰)` the demand at `(1, 1)`, and
`m = (g x₁⁰ - c x₂⁰, b x₂⁰ - c x₁⁰)` (`m = det(S) S⁻¹x⁰` when `S` is invertible) with
`m·x⁰ ≠ 0`. Among taxes raising the (small, so linearized) revenue `t·x⁰ = R`, the deadweight
loss is minimized by `t* = (R/(m·x⁰)) m`. -/
theorem exercise_3_I_7e {a b c d g x₁ x₂ R : ℝ} (hb : b ≤ 0) (hg : g ≤ 0)
    (hbg : c ^ 2 ≤ b * g) (hD : (g * x₁ - c * x₂) * x₁ + (b * x₂ - c * x₁) * x₂ ≠ 0) :
    let D := (g * x₁ - c * x₂) * x₁ + (b * x₂ - c * x₁) * x₂
    let s₁ := R / D * (g * x₁ - c * x₂)
    let s₂ := R / D * (b * x₂ - c * x₁)
    s₁ * x₁ + s₂ * x₂ = R ∧ ∀ t₁ t₂ : ℝ, t₁ * x₁ + t₂ * x₂ = R →
      linDeadweight a b c d c g (1 + s₁) (1 + s₂) ≤
        linDeadweight a b c d c g (1 + t₁) (1 + t₂) := by
  intro D s₁ s₂
  have hrev : s₁ * x₁ + s₂ * x₂ = R := by
    have : s₁ * x₁ + s₂ * x₂ = R / D * D := by simp only [s₁, s₂, D]; ring
    rw [this, div_mul_cancel₀ R hD]
  refine ⟨hrev, fun t₁ t₂ ht => ?_⟩
  rw [exercise_3_I_7e_deadweight, exercise_3_I_7e_deadweight]
  have hq := (quadForm_nonpos_iff b c g).mpr ⟨hb, hg, hbg⟩ (t₁ - s₁) (t₂ - s₂)
  -- the cross term vanishes: `s*ᵀ S (t - s*) = (R/D) det(S) x⁰·(t - s*) = 0`
  have hcross : (b * s₁ + c * s₂) * (t₁ - s₁) + (c * s₁ + g * s₂) * (t₂ - s₂) = 0 := by
    have h1 : b * s₁ + c * s₂ = R / D * (b * g - c ^ 2) * x₁ := by
      simp only [s₁, s₂]; ring
    have h2 : c * s₁ + g * s₂ = R / D * (b * g - c ^ 2) * x₂ := by
      simp only [s₁, s₂]; ring
    rw [h1, h2]
    have : x₁ * (t₁ - s₁) + x₂ * (t₂ - s₂) = 0 := by linarith
    linear_combination (R / D * (b * g - c ^ 2)) * this
  nlinarith

/-- **Exercise 3.I.8(a)** (MWG, p. 103), the "if" direction. If `u` is quasilinear with respect
to good `k` on the quasilinear consumption set and `p_k = 1`, then raising wealth by `c` adds `c`
units of good `k` to any demanded bundle: the demand for the other goods does not depend on
wealth. (That these are the only such utilities is OPEN.) -/
theorem exercise_3_I_8a {L : ℕ} {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    (hql : ∀ x ∈ quasilinearDomain k, ∀ c : ℝ, u (x + c • unitVec k) = u x + c)
    {p : Fin L → ℝ} (hpk : p k = 1) {w : ℝ} {y : Fin L → ℝ}
    (hy : y ∈ walrasianDemandOn (quasilinearDomain k) u p w) (c : ℝ) :
    y + c • unitVec k ∈ walrasianDemandOn (quasilinearDomain k) u p (w + c) ∧
      ∀ l, l ≠ k → (y + c • unitVec k) l = y l := by
  have hdom : ∀ x ∈ quasilinearDomain k, ∀ d : ℝ, x + d • unitVec k ∈ quasilinearDomain k := by
    intro x hx d l hl
    simp [unitVec, hl, hx l hl]
  have hpe : ∀ x d, p ⬝ᵥ (x + d • unitVec k) = p ⬝ᵥ x + d := by
    intro x d
    rw [dotProduct_add, dotProduct_smul, unitVec, dotProduct_single, hpk]
    simp
  refine ⟨⟨⟨hdom y hy.1.1 c, by rw [hpe]; linarith [hy.1.2]⟩, fun z hz => ?_⟩, fun l hl => ?_⟩
  · have hz' : z + (-c) • unitVec k ∈ budgetSetOn (quasilinearDomain k) p w :=
      ⟨hdom z hz.1 (-c), by rw [hpe]; linarith [hz.2]⟩
    have := hy.2 _ hz'
    have e1 := hql (z + (-c) • unitVec k) (hdom z hz.1 (-c)) c
    rw [show z + (-c) • unitVec k + c • unitVec k = z by module] at e1
    rw [hql y hy.1.1, e1]
    linarith
  · simp [unitVec, hl]

/-- **Exercise 3.I.8(b)** (MWG, p. 103). For the demands `x₁ = a₁ + b₁p₁ + c₁p₂ + d₁p₁p₂`,
`x₂ = a₂ + b₂p₁ + c₂p₂ + d₂p₁p₂` without wealth effects, symmetry of the substitution matrix at
all `p ≫ 0` (`∂x₁/∂p₂ = ∂x₂/∂p₁`) holds iff `d₁ = d₂ = 0` and `c₁ = b₂`; together with negative
semidefiniteness this gives `b₁ ≤ 0`, `c₂ ≤ 0`, `c₁² ≤ b₁c₂`. -/
theorem exercise_3_I_8b (b₁ c₁ d₁ b₂ c₂ d₂ : ℝ) :
    ((∀ p₁ p₂ : ℝ, 0 < p₁ → 0 < p₂ → c₁ + d₁ * p₁ = b₂ + d₂ * p₂) ↔
      d₁ = 0 ∧ d₂ = 0 ∧ c₁ = b₂) ∧
    (d₁ = 0 → d₂ = 0 → c₁ = b₂ →
      (∀ y₁ y₂ : ℝ, b₁ * y₁ ^ 2 + (c₁ + b₂) * y₁ * y₂ + c₂ * y₂ ^ 2 ≤ 0) →
      b₁ ≤ 0 ∧ c₂ ≤ 0 ∧ c₁ ^ 2 ≤ b₁ * c₂) := by
  refine ⟨⟨fun h => ?_, ?_⟩, fun _ _ hcb hq => ?_⟩
  · have h11 := h 1 1 one_pos one_pos
    have h21 := h 2 1 two_pos one_pos
    have h12 := h 1 2 one_pos two_pos
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩ p₁ p₂ _ _
    ring
  · subst hcb
    refine (quadForm_nonpos_iff b₁ c₁ c₂).mp fun y₁ y₂ => ?_
    have := hq y₁ y₂
    linarith

/-- **Exercise 3.I.8(c)** (MWG, p. 103). With `d₁ = d₂ = 0` and `c₁ = b₂`, the welfare change
from `p = (P₁, P₂)` to `p' = (Q₁, Q₂)` (the common value of `EV` and `CV` without wealth effects)
is `-[a₁(Q₁ - P₁) + b₁(Q₁² - P₁²)/2 + a₂(Q₂ - P₂) + c₂(Q₂² - P₂²)/2 + c₁(Q₁Q₂ - P₁P₂)]`,
whichever price is changed first. -/
theorem exercise_3_I_8c (a₁ b₁ c₁ a₂ c₂ P₁ P₂ Q₁ Q₂ : ℝ) :
    bilinEV a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 P₁ P₂ Q₁ Q₂ =
        -(a₁ * (Q₁ - P₁) + b₁ * (Q₁ ^ 2 - P₁ ^ 2) / 2 + a₂ * (Q₂ - P₂) +
          c₂ * (Q₂ ^ 2 - P₂ ^ 2) / 2 + c₁ * (Q₁ * Q₂ - P₁ * P₂)) ∧
      bilinEVAlt a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 P₁ P₂ Q₁ Q₂ = bilinEV a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 P₁ P₂ Q₁ Q₂ := by
  rw [bilinEV_eq, bilinEVAlt_eq]
  exact ⟨by ring, by ring⟩

/-- **Exercise 3.I.8(d)** (MWG, p. 103). With `a₁ = a₂ = 3/2`, `b₁ = c₂ = 1`, `c₁ = b₂ = 1/2`,
`d₁ = d₂ = 0` and `p = (1, 1)`: `EV₁ = -7/2` (to `(2, 1)`), `EV₂ = -7/2` (to `(1, 2)`),
`EV₃ = -15/2` (to `(2, 2)`), so `EV₃ ≠ EV₁ + EV₂`; in general `EV₃ = EV₁ + EV₂` iff `c₁ = 0`.
These parameter values violate the restriction `b₁ ≤ 0` of part (b) (correction D7). -/
theorem exercise_3_I_8d :
    bilinEV (3 / 2) 1 (1 / 2) 0 (3 / 2) (1 / 2) 1 0 1 1 2 1 = -7 / 2 ∧
      bilinEV (3 / 2) 1 (1 / 2) 0 (3 / 2) (1 / 2) 1 0 1 1 1 2 = -7 / 2 ∧
      bilinEV (3 / 2) 1 (1 / 2) 0 (3 / 2) (1 / 2) 1 0 1 1 2 2 = -15 / 2 ∧
      (∀ a₁ b₁ c₁ a₂ c₂ : ℝ, bilinEV a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 1 1 2 2 =
        bilinEV a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 1 1 2 1 + bilinEV a₁ b₁ c₁ 0 a₂ c₁ c₂ 0 1 1 1 2 ↔
          c₁ = 0) ∧
      ¬ ((1 : ℝ) ≤ 0) := by
  refine ⟨?_, ?_, ?_, fun a₁ b₁ c₁ a₂ c₂ => ?_, by norm_num⟩
  · rw [bilinEV_eq]; norm_num
  · rw [bilinEV_eq]; norm_num
  · rw [bilinEV_eq]; norm_num
  · rw [bilinEV_eq, bilinEV_eq, bilinEV_eq]
    constructor
    · intro h; linarith
    · intro h; rw [h]; ring

end MWG.ClassicalDemand
