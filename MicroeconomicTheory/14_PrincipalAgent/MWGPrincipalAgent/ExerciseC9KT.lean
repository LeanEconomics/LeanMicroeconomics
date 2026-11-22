/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.KuhnTucker
import MWGPrincipalAgent.ExerciseC9
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exercise 14.C.9(b): the shape of every optimal menu

MWG, Exercise 14.C.9(b), p. 510.

The program of `ExerciseC9`, in utility levels `x = u(c₁)`, `y = u(c₂)` with wealth `φ(·)`
(`φ = u⁻¹`), with all four constraints: the participation constraints of both types (reservation
levels `r_L`, `r_H`) and both self-selection constraints. The program is convex, Slater's condition
holds when `θ_L < θ_H`, so by `kt_convexlike` the Kuhn-Tucker conditions are necessary.

* `kt_foc_1d`: a point minimizing `A φ(x + s) + B s` over `s` has `A φ'(x) + B = 0`.
* `exercise_14_C_9b_necessary`: at every optimal menu (when `r_H < r_L`, as for no-insurance
  reservation levels, `c9_r_order`) the high-risk type is fully insured (`x_H = y_H`), the
  low-risk type is partially insured (`y_L < x_L`), the low-risk participation constraint and the
  high-risk self-selection constraint bind. This closes the necessity part left open by the
  sufficiency theorem `exercise_14_C_9b`.
* `exercise_14_C_9b_necessary_instance`: `u = log`, `W = 2`, `L = 3/2`, `θ_L = 1/4`, `θ_H = 1/2`,
  `λ = 8/17`: the optimal menu gives the high-risk type full insurance at wealth `1` and leaves the
  low-risk type uninsured.
-/

namespace MWG.PrincipalAgent

open Set

/-- A point minimizing `s ↦ A φ(x + s) + B s` at `s = 0`, with `φ'(x) = d`, has `A d + B = 0`. -/
theorem kt_foc_1d {φ : ℝ → ℝ} {d x A B : ℝ} (hd : HasDerivAt φ d x)
    (h : ∀ s, A * φ x ≤ A * φ (x + s) + B * s) : A * d + B = 0 := by
  have h1 : HasDerivAt (fun s => φ (x + s)) d 0 :=
    HasDerivAt.comp_const_add x 0 (by simpa using hd)
  have hd' : HasDerivAt (fun s => A * φ (x + s) + B * s) (A * d + B * 1) 0 :=
    (h1.const_mul A).add ((hasDerivAt_id' 0).const_mul B)
  have := IsLocalMin.hasDerivAt_eq_zero
    (Filter.Eventually.of_forall fun s => by simpa using h s) hd'
  linarith

/-- With no insurance as the outside option (`u(W) > u(W - L)`), the low-risk type's reservation
level exceeds the high-risk type's. -/
theorem c9_r_order {a b θL θH : ℝ} (hab : b < a) (hθ : θL < θH) :
    (1 - θH) * a + θH * b < (1 - θL) * a + θL * b := by
  nlinarith

/-- **Exercise 14.C.9(b)** (MWG, p. 510), necessity. Utility levels `(x_L, y_L)`, `(x_H, y_H)`,
`φ` convex and differentiable with `φ'` positive and strictly increasing, `0 < λ < 1`,
`0 < θ_L < θ_H < 1` and `r_H < r_L`. Every menu maximizing the insurer's expected profit subject to
both participation and both self-selection constraints gives the high-risk type full insurance
(`x_H = y_H`) and the low-risk type partial insurance (`y_L < x_L`); the low-risk participation
constraint and the high-risk self-selection constraint bind. -/
theorem exercise_14_C_9b_necessary {φ dφ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hdφ : ∀ x, HasDerivAt φ (dφ x) x) (hd : StrictMono dφ) (hdpos : ∀ x, 0 < dφ x)
    {W L θL θH lam rL rH : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hθL0 : 0 < θL) (hθ : θL < θH)
    (hθH1 : θH < 1) (hr : rH < rL) {xL yL xH yH : ℝ}
    (hIRL : rL ≤ (1 - θL) * xL + θL * yL) (hIRH : rH ≤ (1 - θH) * xH + θH * yH)
    (hICH : (1 - θH) * xL + θH * yL ≤ (1 - θH) * xH + θH * yH)
    (hICL : (1 - θL) * xH + θL * yH ≤ (1 - θL) * xL + θL * yL)
    (hopt : ∀ xL' yL' xH' yH', rL ≤ (1 - θL) * xL' + θL * yL' →
      rH ≤ (1 - θH) * xH' + θH * yH' →
      (1 - θH) * xL' + θH * yL' ≤ (1 - θH) * xH' + θH * yH' →
      (1 - θL) * xH' + θL * yH' ≤ (1 - θL) * xL' + θL * yL' →
      lam * c9Profit φ W L θL xL' yL' + (1 - lam) * c9Profit φ W L θH xH' yH' ≤
        lam * c9Profit φ W L θL xL yL + (1 - lam) * c9Profit φ W L θH xH yH) :
    xH = yH ∧ yL < xL ∧ (1 - θL) * xL + θL * yL = rL ∧
      (1 - θH) * xL + θH * yL = (1 - θH) * xH + θH * yH := by
  let J : ℝ × ℝ × ℝ × ℝ → ℝ := fun z => lam * ((1 - θL) * φ z.1 + θL * φ z.2.1) +
    (1 - lam) * ((1 - θH) * φ z.2.2.1 + θH * φ z.2.2.2)
  let G : Fin 4 → ℝ × ℝ × ℝ × ℝ → ℝ := ![
    fun z => rL - ((1 - θL) * z.1 + θL * z.2.1),
    fun z => rH - ((1 - θH) * z.2.2.1 + θH * z.2.2.2),
    fun z => (1 - θH) * z.1 + θH * z.2.1 - ((1 - θH) * z.2.2.1 + θH * z.2.2.2),
    fun z => (1 - θL) * z.2.2.1 + θL * z.2.2.2 - ((1 - θL) * z.1 + θL * z.2.1)]
  have hG0 : ∀ z, G 0 z = rL - ((1 - θL) * z.1 + θL * z.2.1) := fun z => rfl
  have hG1 : ∀ z, G 1 z = rH - ((1 - θH) * z.2.2.1 + θH * z.2.2.2) := fun z => rfl
  have hG2 : ∀ z, G 2 z = (1 - θH) * z.1 + θH * z.2.1 - ((1 - θH) * z.2.2.1 + θH * z.2.2.2) :=
    fun z => rfl
  have hG3 : ∀ z, G 3 z = (1 - θL) * z.2.2.1 + θL * z.2.2.2 - ((1 - θL) * z.1 + θL * z.2.1) :=
    fun z => rfl
  have hall : ∀ (P : Fin 4 → Prop), P 0 → P 1 → P 2 → P 3 → ∀ i, P i := by
    intro P h0 h1 h2 h3 i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hconvφ : ∀ a b t : ℝ, 0 ≤ t → t ≤ 1 → φ ((1 - t) * a + t * b) ≤ (1 - t) * φ a + t * φ b :=
    fun a b t ht0 ht1 => by
      have := hφ.2 (mem_univ a) (mem_univ b) (by linarith : 0 ≤ 1 - t) ht0 (by ring)
      simpa [smul_eq_mul] using this
  obtain ⟨a, ha, hcs, hlag⟩ := kt_convexlike J G (xL, yL, xH, yH)
    (hall _ (by rw [hG0]; linarith) (by rw [hG1]; linarith) (by rw [hG2]; linarith)
      (by rw [hG3]; linarith))
    (fun z hz => by
      have h := hopt z.1 z.2.1 z.2.2.1 z.2.2.2 (by linarith [hG0 z ▸ hz 0])
        (by linarith [hG1 z ▸ hz 1]) (by linarith [hG2 z ▸ hz 2]) (by linarith [hG3 z ▸ hz 3])
      simp only [c9Profit] at h
      simp only [J]
      nlinarith)
    (fun z0 z1 t ht0 ht1 => by
      refine ⟨((1 - t) * z0.1 + t * z1.1, (1 - t) * z0.2.1 + t * z1.2.1,
        (1 - t) * z0.2.2.1 + t * z1.2.2.1, (1 - t) * z0.2.2.2 + t * z1.2.2.2), ?_,
        hall _ ?_ ?_ ?_ ?_⟩
      · simp only [J]
        have c1 := hconvφ z0.1 z1.1 t ht0 ht1
        have c2 := hconvφ z0.2.1 z1.2.1 t ht0 ht1
        have c3 := hconvφ z0.2.2.1 z1.2.2.1 t ht0 ht1
        have c4 := hconvφ z0.2.2.2 z1.2.2.2 t ht0 ht1
        have k1 : 0 ≤ lam * (1 - θL) := mul_nonneg hl0.le (by linarith)
        have k2 : 0 ≤ lam * θL := mul_nonneg hl0.le hθL0.le
        have k3 : 0 ≤ (1 - lam) * (1 - θH) := mul_nonneg (by linarith) (by linarith)
        have k4 : 0 ≤ (1 - lam) * θH := mul_nonneg (by linarith) (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left c1 k1, mul_le_mul_of_nonneg_left c2 k2,
          mul_le_mul_of_nonneg_left c3 k3, mul_le_mul_of_nonneg_left c4 k4]
      · rw [hG0, hG0, hG0]; apply le_of_eq; ring
      · rw [hG1, hG1, hG1]; apply le_of_eq; ring
      · rw [hG2, hG2, hG2]; apply le_of_eq; ring
      · rw [hG3, hG3, hG3]; apply le_of_eq; ring)
    ⟨(|rL| + |rH| + 1, |rL| + |rH| + 1, |rL| + |rH| + 1 - (θL + θH),
      |rL| + |rH| + 1 + 2 - θL - θH), hall _
      (by rw [hG0]; linarith [le_abs_self rL, abs_nonneg rH])
      (by rw [hG1]; nlinarith [le_abs_self rH, abs_nonneg rL])
      (by rw [hG2]; nlinarith) (by rw [hG3]; nlinarith)⟩
  -- the multipliers
  have hsum : ∀ z, ∑ i, a i * G i z = a 0 * G 0 z + a 1 * G 1 z + a 2 * G 2 z + a 3 * G 3 z :=
    fun z => Fin.sum_univ_four _
  have cs0 := hcs 0
  have cs1 := hcs 1
  have cs2 := hcs 2
  have cs3 := hcs 3
  rw [hG0] at cs0
  rw [hG1] at cs1
  rw [hG2] at cs2
  rw [hG3] at cs3
  simp only at cs0 cs1 cs2 cs3
  have hlag' : ∀ z : ℝ × ℝ × ℝ × ℝ, J (xL, yL, xH, yH) ≤ J z + (a 0 * G 0 z + a 1 * G 1 z +
      a 2 * G 2 z + a 3 * G 3 z) := fun z => by rw [← hsum]; exact hlag z
  -- first-order conditions
  have F1 : lam * (1 - θL) * dφ xL + (-(a 0) * (1 - θL) + a 2 * (1 - θH) - a 3 * (1 - θL)) = 0 :=
    kt_foc_1d (hdφ xL) fun s => by
      have h := hlag' (xL + s, yL, xH, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F2 : lam * θL * dφ yL + (-(a 0) * θL + a 2 * θH - a 3 * θL) = 0 :=
    kt_foc_1d (hdφ yL) fun s => by
      have h := hlag' (xL, yL + s, xH, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F3 : (1 - lam) * (1 - θH) * dφ xH + (-(a 1) * (1 - θH) - a 2 * (1 - θH) +
      a 3 * (1 - θL)) = 0 :=
    kt_foc_1d (hdφ xH) fun s => by
      have h := hlag' (xL, yL, xH + s, yH)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have F4 : (1 - lam) * θH * dφ yH + (-(a 1) * θH - a 2 * θH + a 3 * θL) = 0 :=
    kt_foc_1d (hdφ yH) fun s => by
      have h := hlag' (xL, yL, xH, yH + s)
      simp only [J, hG0, hG1, hG2, hG3] at h
      nlinarith
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hθL1 : 0 < 1 - θL := by linarith
  have hθH0 : 0 < θH := by linarith
  have hθH1' : 0 < 1 - θH := by linarith
  have hl1' : 0 < 1 - lam := by linarith
  -- the two key combinations
  have KL : lam * θL * (1 - θL) * (dφ xL - dφ yL) = a 2 * (θH - θL) := by
    linear_combination θL * F1 - (1 - θL) * F2
  have KH : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) = -(a 3 * (θH - θL)) := by
    linear_combination θH * F3 - (1 - θH) * F4
  have pL : 0 < lam * θL * (1 - θL) := by positivity
  have pH : 0 < (1 - lam) * θH * (1 - θH) := by positivity
  -- `β_H > 0`
  have ha2pos : 0 < a 2 := by
    rcases ha2.lt_or_eq with h | h
    · exact h
    exfalso
    have hxy : xL = yL := by
      rw [← h, zero_mul] at KL
      have : dφ xL = dφ yL := by
        have := (mul_eq_zero.1 KL).resolve_left pL.ne'
        linarith
      exact hd.injective this
    have hF3 := F3
    rw [← h] at hF3
    have k : a 1 * (1 - θH) = (1 - lam) * (1 - θH) * dφ xH + a 3 * (1 - θL) := by
      linear_combination -hF3
    have k' : 0 < a 1 * (1 - θH) := by
      rw [k]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hl1' hθH1') (hdpos xH))
        (mul_nonneg ha3 hθL1.le)
    have hα1 : 0 < a 1 := (pos_iff_pos_of_mul_pos k').2 hθH1'
    have hbind : (1 - θH) * xH + θH * yH = rH := by
      have := (mul_eq_zero.1 cs1).resolve_left hα1.ne'
      linarith
    subst hxy
    have e1 : (1 - θL) * xL + θL * xL = xL := by ring
    have e2 : (1 - θH) * xL + θH * xL = xL := by ring
    linarith
  have hdL : dφ yL < dφ xL := by
    have : 0 < lam * θL * (1 - θL) * (dφ xL - dφ yL) := by
      rw [KL]; exact mul_pos ha2pos (by linarith)
    have := (pos_iff_pos_of_mul_pos this).1 pL
    linarith
  -- `β_L = 0`
  have ha3z : a 3 = 0 := by
    rcases ha3.lt_or_eq with h | h
    · exfalso
      have b2 : (1 - θH) * xL + θH * yL - ((1 - θH) * xH + θH * yH) = 0 :=
        (mul_eq_zero.1 cs2).resolve_left ha2pos.ne'
      have b3 : (1 - θL) * xH + θL * yH - ((1 - θL) * xL + θL * yL) = 0 :=
        (mul_eq_zero.1 cs3).resolve_left h.ne'
      have k1 : (θH - θL) * ((yH - yL) - (xH - xL)) = 0 := by linear_combination -b3 - b2
      have hdd : yH - yL = xH - xL := by
        have := (mul_eq_zero.1 k1).resolve_left (by linarith)
        linarith
      have hx : xH - xL = 0 := by linear_combination -b2 - θH * hdd
      have hdH : dφ xH < dφ yH := by
        have : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) < 0 := by
          rw [KH]; exact neg_lt_zero.2 (mul_pos h (by linarith))
        have := neg_of_mul_neg_right this pH.le
        linarith
      have hxe : xH = xL := by linarith
      have hye : yH = yL := by linarith
      rw [hxe, hye] at hdH
      linarith
    · exact h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha3z] at KH
    have : dφ xH = dφ yH := by
      have := (mul_eq_zero.1 (by linarith : (1 - lam) * θH * (1 - θH) * (dφ xH - dφ yH) = 0))
      rcases this with h | h
      · exact absurd h pH.ne'
      · linarith
    exact hd.injective this
  · exact hd.lt_iff_lt.1 hdL
  · have hα0 : 0 < a 0 := by
      rw [ha3z] at F1
      have k : a 0 * (1 - θL) = lam * (1 - θL) * dφ xL + a 2 * (1 - θH) := by
        linear_combination -F1
      have k' : 0 < a 0 * (1 - θL) := by
        rw [k]
        exact add_pos (mul_pos (mul_pos hl0 hθL1) (hdpos xL)) (mul_pos ha2pos hθH1')
      exact (pos_iff_pos_of_mul_pos k').2 hθL1
    have := (mul_eq_zero.1 cs0).resolve_left hα0.ne'
    linarith
  · have := (mul_eq_zero.1 cs2).resolve_left ha2pos.ne'
    linarith

/-- **Exercise 14.C.9(b), an instance of the necessity theorem** (MWG, p. 510). `u = log`
(`φ = exp`), `W = 2`, `L = 3/2`, `θ_L = 1/4`, `θ_H = 1/2`, `λ = 8/17`: the reservation levels are
`r_L = (log 2)/2` and `r_H = 0`. The menu `(x_L, y_L) = (log 2, -log 2)` (no insurance) and
`(x_H, y_H) = (0, 0)` (full insurance at wealth `1`) is optimal (sufficiency, with `α = 22/17`,
`β = 9/17`), and the necessity theorem applies to it. -/
theorem exercise_14_C_9b_necessary_instance :
    (0 : ℝ) = 0 ∧ -Real.log 2 < Real.log 2 ∧
      (1 - 1 / 4) * Real.log 2 + 1 / 4 * -Real.log 2 = Real.log 2 / 2 ∧
      (1 - 1 / 2) * Real.log 2 + 1 / 2 * -Real.log 2 = (1 - 1 / 2) * 0 + 1 / 2 * (0 : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hopt : ∀ xL' yL' xH' yH' : ℝ, Real.log 2 / 2 ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL' →
      0 ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH' →
      (1 - 1 / 2) * xL' + 1 / 2 * yL' ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH' →
      (1 - 1 / 4) * xH' + 1 / 4 * yH' ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL' →
      8 / 17 * c9Profit Real.exp 2 (3 / 2) (1 / 4) xL' yL' +
          (1 - 8 / 17) * c9Profit Real.exp 2 (3 / 2) (1 / 2) xH' yH' ≤
        8 / 17 * c9Profit Real.exp 2 (3 / 2) (1 / 4) (Real.log 2) (-Real.log 2) +
          (1 - 8 / 17) * c9Profit Real.exp 2 (3 / 2) (1 / 2) 0 0 := by
    intro xL' yL' xH' yH' h1 _ h3 _
    have e1 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, e1]; norm_num
    refine exercise_14_C_9b (φ := Real.exp) (dφ := Real.exp) convexOn_exp
      (fun x => Real.hasDerivAt_exp x) (α := 22 / 17) (β := 9 / 17) (rL := Real.log 2 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ h1 h3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [Real.exp_zero]; norm_num
    · rw [Real.exp_zero]; norm_num
    · rw [e1]; norm_num
    · rw [e2]; norm_num
    · ring
    · ring
  have hn := exercise_14_C_9b_necessary (φ := Real.exp) (dφ := Real.exp) convexOn_exp
    (fun x => Real.hasDerivAt_exp x) Real.exp_strictMono Real.exp_pos (W := 2) (L := 3 / 2)
    (lam := 8 / 17) (rH := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (by ring_nf; exact le_refl _) (by norm_num)
    (by ring_nf; exact le_refl _) (by nlinarith) hopt
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩

end MWG.PrincipalAgent
