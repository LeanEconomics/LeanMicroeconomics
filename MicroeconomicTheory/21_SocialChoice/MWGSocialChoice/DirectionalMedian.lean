/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.NonVacuity
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Directional median agents

MWG, Exercise 21.D.8, p. 813.

Three agents have utilities on `X ⊆ ℝ²` (modelled by `ℂ`) with gradients `g₀, g₁, g₂` at a
point. Agent `h` is a (first-order) *directional median* if every direction that strictly
improves two agents strictly improves `h` (`IsDirectionalMedian`, in `GradientCycles`).

(a) A directional median exists whenever the cone spanned by the gradients is pointed in MWG's
sense (contains no half-space): `exercise_21_D_8a`. In fact we prove the full dichotomy: a
directional median exists iff the cone is not the whole plane (`exercise_21_D_8a_iff`; the
spanning case is that of Exercise 21.D.7). The case analysis runs on the signs of the signed
areas `c₀ = D(g₁, g₂)`, `c₁ = D(g₂, g₀)`, `c₂ = D(g₀, g₁)`, which satisfy
`c₀ g₀ + c₁ g₁ + c₂ g₂ = 0`: if no agent is a directional median, the Binet-Cauchy identity
rules out `cᵢ = 0` and the relation rules out mixed signs, so the `cᵢ` have a common strict sign
and the gradients span the plane positively.

**Correction (reading of (a)).** Read literally ("any alternative having a strict majority
against the origin must make this agent strictly better off", a global statement about
utility levels), (a) is false even for concave utilities with a pointed gradient cone:
`exercise_21_D_8a_global_counterexample`. The statement holds for the first-order notion.

(b) Euclidean utilities `uᵢ(z) = -‖z - pᵢ‖²` with peaks `(0, 8)`, `(8, 8)`, `(4, 12)` on the
open half-plane `X = {z : z₁ < 8}` (which contains the origin): the gradient cone is pointed
at every point of `X`, the directional median is agent 2 at the origin but agent 0 at
`(-12, 7)`, and there is a Condorcet cycle in `X` (`exercise_21_D_8b`).

(c) For the literal (global) reading the conclusion holds for arbitrary utilities on any set
(`exercise_21_D_8c_global`); for the first-order notion it holds for linear utilities
(`exercise_21_D_8c`, in `GradientCycles`) but **fails** for nonlinear concave utilities:
`exercise_21_D_8c_counterexample` (`Im z - (Re z)²`, `Im z`, `Im z - (max (Re z) 0)²` on the
plane; agent 2 is a first-order directional median everywhere, the cone is pointed everywhere,
and there is a Condorcet cycle).
-/

namespace MWG.SocialChoice

open Finset

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Exercise 21.D.8** (MWG, p. 813). The cone spanned by `g₀, g₁, g₂` contains a closed
half-space `{v : ⟪v, q⟫ ≥ 0}`, `q ≠ 0`. MWG calls the cone *pointed* when this fails. -/
def ConeContainsHalfSpace (g : Fin 3 → ℂ) : Prop :=
  ∃ q : ℂ, q ≠ 0 ∧ ∀ v : ℂ, 0 ≤ ⟪v, q⟫ →
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i

/-- The relation `D(b, c) a + D(c, a) b + D(a, b) c = 0` among three plane vectors, paired
with any `d`. -/
theorem dm_three_term (a b c d : ℂ) :
    ⟪b, Complex.I * c⟫ * ⟪a, d⟫ + ⟪c, Complex.I * a⟫ * ⟪b, d⟫ + ⟪a, Complex.I * b⟫ * ⟪c, d⟫ =
      0 := by
  simp only [inner_I_mul]
  simp only [complex_inner_eq]
  ring

/-- The Binet-Cauchy identity in the plane. -/
theorem dm_binet_cauchy (a b d d' : ℂ) :
    ⟪a, d⟫ * ⟪b, d'⟫ - ⟪a, d'⟫ * ⟪b, d⟫ = ⟪a, Complex.I * b⟫ * ⟪d, Complex.I * d'⟫ := by
  simp only [inner_I_mul]
  simp only [complex_inner_eq]
  ring

/-- If `h` is not a directional median, some direction strictly improves both other agents and
does not improve `h`. -/
theorem dm_not_median {g : Fin 3 → ℂ} {h : Fin 3} (hn : ¬IsDirectionalMedian g h) :
    ∃ d : ℂ, ⟪g h, d⟫ ≤ 0 ∧ ∀ k, k ≠ h → 0 < ⟪g k, d⟫ := by
  unfold IsDirectionalMedian at hn
  push Not at hn
  obtain ⟨d, ⟨i, j, hij, hi, hj⟩, hh⟩ := hn
  refine ⟨d, hh, fun k hk => ?_⟩
  have hih : i ≠ h := by
    rintro rfl
    linarith
  have hjh : j ≠ h := by
    rintro rfl
    linarith
  have key : ∀ h i j k : Fin 3, i ≠ h → j ≠ h → i ≠ j → k ≠ h → k = i ∨ k = j := by decide
  rcases key h i j k hih hjh hij hk with rfl | rfl
  · exact hi
  · exact hj

/-- Gradients with a strictly positive linear relation `∑ lᵢ gᵢ = 0` and `D(g₀, g₁) ≠ 0` span
the plane positively. -/
theorem dm_spans_of_relation {g : Fin 3 → ℂ} {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i)
    (hsum : ∀ d : ℂ, l 0 * ⟪g 0, d⟫ + l 1 * ⟪g 1, d⟫ + l 2 * ⟪g 2, d⟫ = 0)
    (h01 : ⟪g 0, Complex.I * g 1⟫ ≠ 0) (v : ℂ) :
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  have hre : l 0 * (g 0).re + l 1 * (g 1).re + l 2 * (g 2).re = 0 := by
    have := hsum 1
    simp only [complex_inner_eq, Complex.one_re, Complex.one_im, mul_one, mul_zero,
      add_zero] at this
    exact this
  have him : l 0 * (g 0).im + l 1 * (g 1).im + l 2 * (g 2).im = 0 := by
    have := hsum Complex.I
    simp only [complex_inner_eq, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      zero_add] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c, c = ⟪g 0, Complex.I * g 1⟫ := ⟨_, rfl⟩
  rw [← hc] at h01
  obtain ⟨α, hα⟩ : ∃ α, α = ⟪v, Complex.I * g 1⟫ / c := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ⟪g 0, Complex.I * v⟫ / c := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = |α| / l 0 + |β| / l 1 := ⟨_, rfl⟩
  have e1 : α * (g 0).re + β * (g 1).re = v.re := by
    rw [hα, hβ]
    field_simp
    rw [hc]
    simp only [inner_I_mul]
    ring
  have e2 : α * (g 0).im + β * (g 1).im = v.im := by
    rw [hα, hβ]
    field_simp
    rw [hc]
    simp only [inner_I_mul]
    ring
  have t0 : |α| ≤ t * l 0 := by
    have : t * l 0 = |α| + |β| / l 1 * l 0 := by
      rw [ht]
      field_simp [(hl 0).ne']
    rw [this]
    have := div_nonneg (abs_nonneg β) (hl 1).le
    nlinarith [hl 0]
  have t1 : |β| ≤ t * l 1 := by
    have : t * l 1 = |α| / l 0 * l 1 + |β| := by
      rw [ht]
      field_simp [(hl 1).ne']
    rw [this]
    have := div_nonneg (abs_nonneg α) (hl 0).le
    nlinarith [hl 1]
  have tnn : 0 ≤ t := by
    rw [ht]
    exact add_nonneg (div_nonneg (abs_nonneg _) (hl 0).le) (div_nonneg (abs_nonneg _) (hl 1).le)
  refine ⟨![α + t * l 0, β + t * l 1, t * l 2], fun i => ?_, ?_⟩
  · fin_cases i
    · change 0 ≤ α + t * l 0
      linarith [neg_abs_le α]
    · change 0 ≤ β + t * l 1
      linarith [neg_abs_le β]
    · change 0 ≤ t * l 2
      exact mul_nonneg tnn (hl 2).le
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      linear_combination -e1 - t * hre
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      linear_combination -e2 - t * him

/-- **Exercise 21.D.8(a)** (MWG, p. 813), the case analysis on the cone. Either some agent is a
directional median, or the gradients span the whole plane positively. -/
theorem dm_median_or_spans (g : Fin 3 → ℂ) :
    (∃ h, IsDirectionalMedian g h) ∨
      ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  by_cases hm : ∃ h, IsDirectionalMedian g h
  · exact Or.inl hm
  right
  push Not at hm
  obtain ⟨d0, a00, ha0⟩ := dm_not_median (hm 0)
  obtain ⟨d1, a11, ha1⟩ := dm_not_median (hm 1)
  obtain ⟨d2, a22, ha2⟩ := dm_not_median (hm 2)
  have a10 := ha0 1 (by decide)
  have a20 := ha0 2 (by decide)
  have a01 := ha1 0 (by decide)
  have a21 := ha1 2 (by decide)
  have a02 := ha2 0 (by decide)
  have a12 := ha2 1 (by decide)
  have R0 := dm_three_term (g 0) (g 1) (g 2) d0
  have R1 := dm_three_term (g 0) (g 1) (g 2) d1
  have R2 := dm_three_term (g 0) (g 1) (g 2) d2
  have B2 := dm_binet_cauchy (g 0) (g 1) d0 d2
  have B0 := dm_binet_cauchy (g 1) (g 2) d1 d0
  have B1 := dm_binet_cauchy (g 2) (g 0) d2 d1
  have hc2 : ⟪g 0, Complex.I * g 1⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B2
    nlinarith [mul_pos a02 a10, mul_nonneg (neg_nonneg.2 a00) a12.le]
  have hc0 : ⟪g 1, Complex.I * g 2⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B0
    nlinarith [mul_pos a10 a21, mul_nonneg (neg_nonneg.2 a11) a20.le]
  have hc1 : ⟪g 2, Complex.I * g 0⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at B1
    nlinarith [mul_pos a21 a02, mul_nonneg (neg_nonneg.2 a22) a01.le]
  have hsign : (0 < ⟪g 1, Complex.I * g 2⟫ ∧ 0 < ⟪g 2, Complex.I * g 0⟫ ∧
      0 < ⟪g 0, Complex.I * g 1⟫) ∨ (⟪g 1, Complex.I * g 2⟫ < 0 ∧
      ⟪g 2, Complex.I * g 0⟫ < 0 ∧ ⟪g 0, Complex.I * g 1⟫ < 0) := by
    rcases hc0.lt_or_gt with h0 | h0 <;> rcases hc1.lt_or_gt with h1 | h1 <;>
      rcases hc2.lt_or_gt with h2 | h2
    · exact Or.inr ⟨h0, h1, h2⟩
    · linarith [mul_neg_of_neg_of_pos h0 a02, mul_neg_of_neg_of_pos h1 a12,
        mul_nonpos_of_nonneg_of_nonpos h2.le a22]
    · linarith [mul_neg_of_neg_of_pos h0 a01, mul_nonpos_of_nonneg_of_nonpos h1.le a11,
        mul_neg_of_neg_of_pos h2 a21]
    · linarith [mul_nonneg_of_nonpos_of_nonpos h0.le a00, mul_pos h1 a10, mul_pos h2 a20]
    · linarith [mul_nonpos_of_nonneg_of_nonpos h0.le a00, mul_neg_of_neg_of_pos h1 a10,
        mul_neg_of_neg_of_pos h2 a20]
    · linarith [mul_pos h0 a01, mul_nonneg_of_nonpos_of_nonpos h1.le a11, mul_pos h2 a21]
    · linarith [mul_pos h0 a02, mul_pos h1 a12, mul_nonneg_of_nonpos_of_nonpos h2.le a22]
    · exact Or.inl ⟨h0, h1, h2⟩
  rcases hsign with ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩
  · refine dm_spans_of_relation (l := ![⟪g 1, Complex.I * g 2⟫, ⟪g 2, Complex.I * g 0⟫,
      ⟪g 0, Complex.I * g 1⟫]) (fun i => ?_) (fun d => ?_) hc2
    · fin_cases i
      · exact p0
      · exact p1
      · exact p2
    · simpa using dm_three_term (g 0) (g 1) (g 2) d
  · refine dm_spans_of_relation (l := ![-⟪g 1, Complex.I * g 2⟫, -⟪g 2, Complex.I * g 0⟫,
      -⟪g 0, Complex.I * g 1⟫]) (fun i => ?_) (fun d => ?_) hc2
    · fin_cases i
      · exact neg_pos.2 p0
      · exact neg_pos.2 p1
      · exact neg_pos.2 p2
    · have := dm_three_term (g 0) (g 1) (g 2) d
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      linarith

/-- If the gradients span the plane positively, no agent is a directional median. -/
theorem dm_spans_no_median {g : Fin 3 → ℂ}
    (hcone : ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i) (h : Fin 3) :
    ¬IsDirectionalMedian g h := by
  obtain ⟨d0, d1, d2, -, a10, a20, a01, a21, a02, a12, -⟩ := cone_directions hcone
  obtain ⟨μ, hμ, hv⟩ := hcone (-(g 0 + g 1 + g 2))
  have rel : ∀ d : ℂ, (μ 0 + 1) * ⟪g 0, d⟫ + (μ 1 + 1) * ⟪g 1, d⟫ + (μ 2 + 1) * ⟪g 2, d⟫ =
      0 := by
    intro d
    have := congrArg (fun w => ⟪w, d⟫) hv
    simp only [Fin.sum_univ_three, inner_add_left, inner_neg_left, real_inner_smul_left] at this
    linarith
  have m0 := hμ 0
  have m1 := hμ 1
  have m2 := hμ 2
  intro hmed
  fin_cases h
  · have := hmed d0 ⟨1, 2, by decide, a10, a20⟩
    change 0 < ⟪g 0, d0⟫ at this
    nlinarith [rel d0, mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) a10,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) a20,
      mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) this]
  · have := hmed d1 ⟨0, 2, by decide, a01, a21⟩
    change 0 < ⟪g 1, d1⟫ at this
    nlinarith [rel d1, mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) a01,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) a21,
      mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) this]
  · have := hmed d2 ⟨0, 1, by decide, a02, a12⟩
    change 0 < ⟪g 2, d2⟫ at this
    nlinarith [rel d2, mul_pos (by linarith : (0 : ℝ) < μ 0 + 1) a02,
      mul_pos (by linarith : (0 : ℝ) < μ 1 + 1) a12,
      mul_pos (by linarith : (0 : ℝ) < μ 2 + 1) this]

/-- **Exercise 21.D.8(a)** (MWG, p. 813), sharp form. Some agent is a directional median iff the
cone spanned by the gradients is not the whole plane. -/
theorem exercise_21_D_8a_iff (g : Fin 3 → ℂ) :
    (∃ h, IsDirectionalMedian g h) ↔
      ¬∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ v = ∑ i, μ i • g i := by
  constructor
  · rintro ⟨h, hh⟩ hc
    exact dm_spans_no_median hc h hh
  · intro hn
    exact (dm_median_or_spans g).resolve_right hn

/-- **Exercise 21.D.8(a)** (MWG, p. 813). If the cone spanned by the gradients is pointed
(contains no half-space), some agent is a directional median: every direction that strictly
improves a majority strictly improves that agent. -/
theorem exercise_21_D_8a (g : Fin 3 → ℂ) (hpt : ¬ConeContainsHalfSpace g) :
    ∃ h, IsDirectionalMedian g h :=
  (dm_median_or_spans g).resolve_right fun hc => hpt ⟨1, one_ne_zero, fun v _ => hc v⟩

/-- A cone of vectors all strictly on one side of a line through the origin is pointed. -/
theorem not_coneContainsHalfSpace_of_pos (g : Fin 3 → ℂ) (p : ℂ) (hp : ∀ i, 0 < ⟪g i, p⟫) :
    ¬ConeContainsHalfSpace g := by
  rintro ⟨q, hq, hH⟩
  have hIq : ⟪Complex.I * q, q⟫ = 0 := by
    simp only [complex_inner_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hIq0 : Complex.I * q ≠ 0 := mul_ne_zero Complex.I_ne_zero hq
  have key : ∀ w : ℂ, w ≠ 0 → ⟪w, q⟫ = 0 → ⟪w, p⟫ ≤ 0 → False := by
    intro w hw hwq hwp
    obtain ⟨μ, hμ, hv⟩ := hH w hwq.ge
    have hnn : ∀ j, 0 ≤ μ j * ⟪g j, p⟫ := fun j => mul_nonneg (hμ j) (hp j).le
    have e : ⟪w, p⟫ = ∑ j, μ j * ⟪g j, p⟫ := by
      rw [hv, sum_inner]
      simp only [real_inner_smul_left]
    have hsum0 : ∑ j, μ j * ⟪g j, p⟫ = 0 :=
      le_antisymm (e ▸ hwp) (sum_nonneg fun j _ => hnn j)
    have hz : ∀ i, μ i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 hsum0 i (mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hp i).ne'
    apply hw
    rw [hv]
    simp [hz]
  rcases le_total ⟪Complex.I * q, p⟫ 0 with h | h
  · exact key _ hIq0 hIq h
  · exact key (-(Complex.I * q)) (neg_ne_zero.2 hIq0) (by rw [inner_neg_left, hIq, neg_zero])
      (by rw [inner_neg_left]; linarith)

/-- **Exercise 21.D.8(a)**, instance. The gradients `1, 1, I` span a pointed cone, and agent `0`
is a directional median. -/
theorem exercise_21_D_8a_instance :
    ¬ConeContainsHalfSpace ![1, 1, Complex.I] ∧ IsDirectionalMedian ![1, 1, Complex.I] 0 :=
  ⟨not_coneContainsHalfSpace_of_pos _ (1 + Complex.I) (by
    intro i
    fin_cases i <;> simp), exercise_21_D_8c_instance⟩

/-- **Exercise 21.D.8(a)** (MWG, p. 813), literal reading: agent `h` is a directional median at
`x` if every alternative of `X` that a strict majority prefers to `x` makes `h` strictly better
off. -/
def IsGlobalDirectionalMedian (X : Set ℂ) (u : Fin 3 → ℂ → ℝ) (x : ℂ) (h : Fin 3) : Prop :=
  ∀ y ∈ X, TwoAgentsPrefer u y x → u h x < u h y

/-- The concave utilities `Re z`, `Im z`, `Re z + Im z - 2 (Re z - Im z)²` of the counterexample
to the literal reading of Exercise 21.D.8(a). -/
def e218aUtil : Fin 3 → ℂ → ℝ :=
  ![fun z => z.re, fun z => z.im, fun z => z.re + z.im - 2 * (z.re - z.im) ^ 2]

/-- **Exercise 21.D.8(a)**, correction: the literal reading is false. The utilities `e218aUtil`
are concave, with gradients `1, I, 1 + I` at the origin spanning a pointed cone (agent 2 is a
first-order directional median), yet for every agent `h` some alternative is preferred to the
origin by a strict majority while `h` is not better off. -/
theorem exercise_21_D_8a_global_counterexample :
    (∀ i, ConcaveOn ℝ Set.univ (e218aUtil i)) ∧
      (∀ i, HasGradientAt (e218aUtil i) (![1, Complex.I, 1 + Complex.I] i) 0) ∧
      ¬ConeContainsHalfSpace ![1, Complex.I, 1 + Complex.I] ∧
      IsDirectionalMedian ![1, Complex.I, 1 + Complex.I] 2 ∧
      ∀ h, ¬IsGlobalDirectionalMedian Set.univ e218aUtil 0 h := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, fun h => ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    fin_cases i
    · simp [e218aUtil]
    · simp [e218aUtil]
    · simp only [e218aUtil, Fin.reduceFinMk, Matrix.cons_val, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg ((x.re - x.im) - (y.re - y.im)))]
  · fin_cases i
    · convert hasGradientAt_inner_const 1 using 1
      · funext z
        simp [e218aUtil]
      · rfl
    · convert hasGradientAt_inner_const Complex.I using 1
      · funext z
        simp [e218aUtil]
      · rfl
    · rw [hasGradientAt_iff_hasFDerivAt]
      have hA := (InnerProductSpace.toDual ℝ ℂ (1 + Complex.I) : ℂ →L[ℝ] ℝ).hasFDerivAt
        (x := 0)
      have hB := (InnerProductSpace.toDual ℝ ℂ (1 - Complex.I) : ℂ →L[ℝ] ℝ).hasFDerivAt
        (x := 0)
      have hC := hA.sub ((hB.mul hB).const_mul 2)
      convert hC using 1
      · funext z
        simp [e218aUtil, InnerProductSpace.toDual_apply_apply]
        ring
      · simp
  · exact not_coneContainsHalfSpace_of_pos _ (1 + Complex.I) (by
      intro i
      fin_cases i <;> rw [complex_inner_eq] <;> simp)
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  · intro hh
    fin_cases h
    · have := hh ⟨-1 / 100, 1 / 50⟩ trivial ⟨1, 2, by decide, by simp [e218aUtil],
        by simp [e218aUtil]; norm_num⟩
      simp [e218aUtil] at this
      norm_num at this
    · have := hh ⟨1 / 50, -1 / 100⟩ trivial ⟨0, 2, by decide, by simp [e218aUtil],
        by simp [e218aUtil]; norm_num⟩
      simp [e218aUtil] at this
      norm_num at this
    · have := hh ⟨1, 1 / 100⟩ trivial ⟨0, 1, by decide, by simp [e218aUtil],
        by simp [e218aUtil]⟩
      simp [e218aUtil] at this
      norm_num at this

/-- The peaks `(0, 8)`, `(8, 8)`, `(4, 12)` of the Euclidean example for Exercise 21.D.8(b). -/
def e218bPeak : Fin 3 → ℂ := ![⟨0, 8⟩, ⟨8, 8⟩, ⟨4, 12⟩]

/-- The Euclidean utilities `uᵢ(z) = -‖z - pᵢ‖²` of the example for Exercise 21.D.8(b), in
coordinates. -/
def e218bUtil (i : Fin 3) (z : ℂ) : ℝ :=
  -((z.re - (e218bPeak i).re) ^ 2 + (z.im - (e218bPeak i).im) ^ 2)

/-- Their gradients `2 (pᵢ - x)` at `x`. -/
noncomputable def e218bGrad (x : ℂ) (i : Fin 3) : ℂ := (2 : ℝ) • (e218bPeak i - x)

/-- The utilities `e218bUtil` are Euclidean: `uᵢ(z) = -‖z - pᵢ‖²`. -/
theorem e218bUtil_eq (i : Fin 3) (z : ℂ) : e218bUtil i z = -‖z - e218bPeak i‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, e218bUtil, Complex.sub_re, Complex.sub_im]
  ring

/-- The utilities `e218bUtil` are concave on the plane. -/
theorem e218bUtil_concave (i : Fin 3) : ConcaveOn ℝ Set.univ (e218bUtil i) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [e218bUtil, smul_eq_mul, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg (x.re - y.re))
    (sq_nonneg (x.im - y.im)))]

/-- `e218bUtil i` has gradient `2 (pᵢ - x)` at every `x`. -/
theorem e218bUtil_hasGradientAt (i : Fin 3) (x : ℂ) :
    HasGradientAt (e218bUtil i) (e218bGrad x i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hre := (Complex.reCLM.hasFDerivAt (x := x)).sub_const (e218bPeak i).re
  have him := (Complex.imCLM.hasFDerivAt (x := x)).sub_const (e218bPeak i).im
  have h := ((hre.mul hre).add (him.mul him)).neg
  convert h using 1
  · funext z
    simp only [e218bUtil, Pi.neg_apply, Pi.add_apply, Pi.mul_apply, Complex.reCLM_apply,
      Complex.imCLM_apply]
    ring
  · ext v
    simp [e218bGrad, InnerProductSpace.toDual_apply_apply]
    ring

/-- **Exercise 21.D.8(b)** (MWG, p. 813). Euclidean utilities with peaks `(0, 8)`, `(8, 8)`,
`(4, 12)` on the convex open half-plane `X = {z : z₁ < 8}`, which contains the origin. The
utilities are concave and differentiable; at every point of `X` the gradient cone is pointed,
so (by (a)) there is a directional median; the directional median is agent 2 (not agent 0) at
the origin and agent 0 (not agent 2) at `(-12, 7)`; and `(-7, 6)`, `0`, `(-4, 2)` form a
Condorcet cycle in `X`. -/
theorem exercise_21_D_8b :
    Convex ℝ {z : ℂ | z.im < 8} ∧ (0 : ℂ) ∈ interior {z : ℂ | z.im < 8} ∧
      (∀ i, ConcaveOn ℝ Set.univ (e218bUtil i)) ∧
      (∀ x i, HasGradientAt (e218bUtil i) (e218bGrad x i) x) ∧
      (∀ x : ℂ, x.im < 8 → ¬ConeContainsHalfSpace (e218bGrad x)) ∧
      (∀ x : ℂ, x.im < 8 → ∃ h, IsDirectionalMedian (e218bGrad x) h) ∧
      IsDirectionalMedian (e218bGrad 0) 2 ∧ ¬IsDirectionalMedian (e218bGrad 0) 0 ∧
      IsDirectionalMedian (e218bGrad ⟨-12, 7⟩) 0 ∧
      ¬IsDirectionalMedian (e218bGrad ⟨-12, 7⟩) 2 ∧
      ∃ x ∈ {z : ℂ | z.im < 8}, ∃ y ∈ {z : ℂ | z.im < 8}, ∃ z ∈ {z : ℂ | z.im < 8},
        TwoAgentsPrefer e218bUtil x y ∧ TwoAgentsPrefer e218bUtil y z ∧
          TwoAgentsPrefer e218bUtil z x := by
  have hpt : ∀ x : ℂ, x.im < 8 → ¬ConeContainsHalfSpace (e218bGrad x) := by
    intro x hx
    apply not_coneContainsHalfSpace_of_pos _ Complex.I
    intro i
    fin_cases i <;> simp [e218bGrad, e218bPeak] <;> linarith
  refine ⟨?_, ?_, e218bUtil_concave, fun x i => e218bUtil_hasGradientAt i x, hpt,
    fun x hx => exercise_21_D_8a _ (hpt x hx), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢
      rw [zero_add] at hab
      rw [hab]
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx h, mul_le_mul_of_nonneg_left hy.le hb]
  · rw [(isOpen_lt Complex.continuous_im continuous_const).interior_eq]
    simp
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all [e218bGrad, e218bPeak] <;> linarith
  · intro h
    have := h 1 ⟨1, 2, by decide, by simp [e218bGrad, e218bPeak], by
      simp [e218bGrad, e218bPeak]⟩
    simp [e218bGrad, e218bPeak] at this
  · rintro d ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all [e218bGrad, e218bPeak] <;> linarith
  · intro h
    have := h ⟨1, -4⟩ ⟨0, 1, by decide, by simp [e218bGrad, e218bPeak]; norm_num, by
      simp [e218bGrad, e218bPeak]; norm_num⟩
    simp [e218bGrad, e218bPeak] at this
    norm_num at this
  · refine ⟨⟨-7, 6⟩, by simp; norm_num, 0, by simp, ⟨-4, 2⟩, by simp; norm_num,
      ⟨0, 2, by decide, ?_, ?_⟩, ⟨1, 2, by decide, ?_, ?_⟩, ⟨0, 1, by decide, ?_, ?_⟩⟩ <;>
      simp [e218bUtil, e218bPeak] <;> norm_num

/-- **Exercise 21.D.8(c)** (MWG, p. 813), literal reading, arbitrary utilities. If the same
agent `h` is a directional median (in the literal sense of (a)) at every point of `X`, there is
no Condorcet cycle in `X`. -/
theorem exercise_21_D_8c_global {X : Set ℂ} {u : Fin 3 → ℂ → ℝ} {h : Fin 3}
    (hmed : ∀ x ∈ X, IsGlobalDirectionalMedian X u x h) {x y z : ℂ} (hx : x ∈ X) (hy : y ∈ X)
    (hz : z ∈ X) :
    ¬(TwoAgentsPrefer u x y ∧ TwoAgentsPrefer u y z ∧ TwoAgentsPrefer u z x) := by
  rintro ⟨h1, h2, h3⟩
  have a := hmed y hy x hx h1
  have b := hmed z hz y hy h2
  have c := hmed x hx z hz h3
  linarith

/-- **Exercise 21.D.8(c)**, instance. For the linear utilities with gradients `1, 1, I`, agent
`0` is a directional median in the literal sense at every point of the plane. -/
theorem exercise_21_D_8c_global_instance (x : ℂ) :
    IsGlobalDirectionalMedian Set.univ (fun i v => ⟪![1, 1, Complex.I] i, v⟫) x 0 := by
  rintro y - ⟨i, j, hij, hi, hj⟩
  have := exercise_21_D_8c_instance (y - x) ⟨i, j, hij, by rw [inner_sub_right]; linarith,
    by rw [inner_sub_right]; linarith⟩
  rw [inner_sub_right] at this
  linarith

/-- `t ↦ (max t 0)²` has derivative `2 max t 0` everywhere. -/
theorem e218c_hasDerivAt_sqPos (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have e : (fun s : ℝ => max s 0 ^ 2) =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [max_eq_right (le_of_lt (Set.mem_Iio.1 hs))]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq e
  · rw [hasDerivAt_iff_isLittleO]
    simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      mul_zero, smul_zero]
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun s => ?_)).trans_isLittleO
      (Asymptotics.isLittleO_pow_id one_lt_two)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _), one_mul]
    rcases le_total s 0 with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg s]
    · rw [max_eq_left h]
  · have e : (fun s : ℝ => max s 0 ^ 2) =ᶠ[nhds t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt (Set.mem_Ioi.1 hs))]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq e

/-- The concave utilities `Im z - (Re z)²`, `Im z`, `Im z - (max (Re z) 0)²` of the
counterexample to the first-order reading of Exercise 21.D.8(c). -/
def e218cUtil : Fin 3 → ℂ → ℝ :=
  ![fun z => z.im - z.re ^ 2, fun z => z.im, fun z => z.im - max z.re 0 ^ 2]

/-- Their gradients `(-2 Re x, 1)`, `(0, 1)`, `(-2 max (Re x) 0, 1)` at `x`. -/
noncomputable def e218cGrad (x : ℂ) : Fin 3 → ℂ :=
  ![⟨-2 * x.re, 1⟩, ⟨0, 1⟩, ⟨-2 * max x.re 0, 1⟩]

/-- **Exercise 21.D.8(c)** (MWG, p. 813), correction: false for nonlinear utilities under the
first-order notion of directional median. On `X = ℝ²` the utilities `e218cUtil` are concave and
differentiable with gradients `e218cGrad`; at every point the gradient cone is pointed and agent
2 is a directional median (its gradient equals agent 1's where `Re x ≤ 0` and agent 0's where
`Re x ≥ 0`); yet `(0, -1/4)`, `(1, 1/2)`, `(-1, 0)` form a Condorcet cycle. What survives is
the literal reading (`exercise_21_D_8c_global`) and the linear case (`exercise_21_D_8c`). -/
theorem exercise_21_D_8c_counterexample :
    (∀ i, ConcaveOn ℝ Set.univ (e218cUtil i)) ∧
      (∀ x i, HasGradientAt (e218cUtil i) (e218cGrad x i) x) ∧
      (∀ x, ¬ConeContainsHalfSpace (e218cGrad x)) ∧
      (∀ x, IsDirectionalMedian (e218cGrad x) 2) ∧
      TwoAgentsPrefer e218cUtil ⟨0, -1 / 4⟩ ⟨1, 1 / 2⟩ ∧
      TwoAgentsPrefer e218cUtil ⟨1, 1 / 2⟩ ⟨-1, 0⟩ ∧
      TwoAgentsPrefer e218cUtil ⟨-1, 0⟩ ⟨0, -1 / 4⟩ := by
  refine ⟨fun i => ?_, fun x i => ?_, fun x => ?_, fun x => ?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    fin_cases i
    · simp only [e218cUtil, Fin.zero_eta, Matrix.cons_val_zero, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      obtain rfl : b = 1 - a := by linarith
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.re - y.re))]
    · simp [e218cUtil]
    · simp only [e218cUtil, Fin.reduceFinMk, Matrix.cons_val, smul_eq_mul, Complex.add_re,
        Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      have h1 : max (a * x.re + b * y.re) 0 ≤ a * max x.re 0 + b * max y.re 0 :=
        max_le (by nlinarith [le_max_left x.re 0, le_max_left y.re 0])
          (by nlinarith [le_max_right x.re 0, le_max_right y.re 0])
      have h0 := le_max_right (a * x.re + b * y.re) 0
      obtain rfl : b = 1 - a := by linarith
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (max x.re 0 - max y.re 0)),
        mul_le_mul h1 h1 h0 (le_trans h0 h1)]
  · rw [hasGradientAt_iff_hasFDerivAt]
    fin_cases i
    · have h := (Complex.imCLM.hasFDerivAt (x := x)).sub
        ((Complex.reCLM.hasFDerivAt (x := x)).mul (Complex.reCLM.hasFDerivAt (x := x)))
      convert h using 1
      · funext z
        simp [e218cUtil]
        ring
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
        ring
    · convert Complex.imCLM.hasFDerivAt (x := x) using 1
      · funext v
        simp [e218cUtil]
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
    · have hq := e218c_hasDerivAt_sqPos (Complex.reCLM x)
      have h := (Complex.imCLM.hasFDerivAt (x := x)).sub
        (hq.comp_hasFDerivAt x (Complex.reCLM.hasFDerivAt (x := x)))
      convert h using 1
      · funext z
        simp [e218cUtil]
      · ext v
        simp [e218cGrad, InnerProductSpace.toDual_apply_apply]
        ring
  · apply not_coneContainsHalfSpace_of_pos _ Complex.I
    intro i
    fin_cases i <;> simp [e218cGrad]
  · rintro d ⟨i, j, hij, hi, hj⟩
    rcases le_total x.re 0 with hr | hr
    · have hm : max x.re 0 = 0 := max_eq_right hr
      fin_cases i <;> fin_cases j <;> simp_all [e218cGrad]
    · have hm : max x.re 0 = x.re := max_eq_left hr
      fin_cases i <;> fin_cases j <;> simp_all [e218cGrad]
  · exact ⟨0, 2, by decide, by simp [e218cUtil]; norm_num, by simp [e218cUtil]; norm_num⟩
  · exact ⟨0, 1, by decide, by simp [e218cUtil], by simp [e218cUtil]⟩
  · exact ⟨1, 2, by decide, by simp [e218cUtil]; norm_num, by simp [e218cUtil]; norm_num⟩

end MWG.SocialChoice
