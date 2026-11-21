/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.HiddenInfo
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Exercises 14.AA.1 and 14.AA.2

MWG, p. 510.

* `exercise_14_AA_1`: the differential form of the monotone likelihood ratio property:
  `f_e(π|e) / f(π|e)` is nondecreasing in `π` for every `e ∈ [a, b]` iff
  `f(π|e'') / f(π|e')` is nondecreasing in `π` for all `e' < e''` in `[a, b]`.
  `exercise_14_AA_1_strict` gives the strict version of "only if"; `exercise_14_AA_1_strict_false`
  shows that the strict version of "if" is false (correction).
* `exercise_14_AA_2_valid`, `exercise_14_AA_2_contract`: two outcomes; if `f(π_H|e)` is concave in
  `e`, `g` convex and `v_H ≥ v_L`, the manager's first-order condition is sufficient (the
  first-order approach is valid); the optimal contract implementing an interior `e` has
  `v_H - v_L = g'(e) / f'(π_H|e)` and a binding participation constraint.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- A point of `[a, b]` (`a < b`) is a limit of other points of `[a, b]`. -/
theorem aa_neBot {a b e : ℝ} (hab : a < b) (he : e ∈ Icc a b) : (𝓝[Icc a b \ {e}] e).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  rcases he.2.lt_or_eq with h | h
  · have hsub : Ioo e b ⊆ Icc a b \ {e} := fun x hx => ⟨⟨he.1.trans hx.1.le, hx.2.le⟩, hx.1.ne'⟩
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨le_rfl, h.le⟩)
  · have hsub : Ioo a b ⊆ Icc a b \ {e} := fun x hx => ⟨⟨hx.1.le, hx.2.le⟩, by
      rw [h]; exact hx.2.ne⟩
    exact closure_mono hsub (by rw [closure_Ioo hab.ne]; rw [h]; exact ⟨hab.le, le_rfl⟩)

/-- A function with within-derivatives on `[a, b]` (`a < b`) is monotone there iff its derivative
is nonnegative at every point of `[a, b]`. -/
theorem aa_mono_iff {G G' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ e ∈ Icc a b, HasDerivWithinAt G (G' e) (Icc a b) e) :
    MonotoneOn G (Icc a b) ↔ ∀ e ∈ Icc a b, 0 ≤ G' e := by
  constructor
  · intro hm e he
    have ht := hasDerivWithinAt_iff_tendsto_slope.1 (hd e he)
    have := aa_neBot hab he
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hy.2 with h | h
    · exact div_nonneg_of_nonpos (by linarith [hm hy.1 he h.le]) (by linarith)
    · exact div_nonneg (by linarith [hm he hy.1 h.le]) (by linarith)
  · intro hpos
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := G') (convex_Icc a b)
      (fun e he => (hd e he).continuousWithinAt) (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Icc] at he ⊢
      exact (hd e (Ioo_subset_Icc_self he)).mono Ioo_subset_Icc_self
    · rw [interior_Icc] at he
      exact hpos e (Ioo_subset_Icc_self he)

/-- For positive numbers, `A/B ≤ C/D` iff `log A - log B ≤ log C - log D`. -/
theorem aa_ratio_log {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    A / B ≤ C / D ↔ Real.log A - Real.log B ≤ Real.log C - Real.log D := by
  rw [← Real.log_div hA.ne' hB.ne', ← Real.log_div hC.ne' hD.ne',
    Real.log_le_log_iff (div_pos hA hB) (div_pos hC hD)]

/-- The derivative of `e ↦ log f(π₂|e) - log f(π₁|e)`. -/
theorem aa_G_deriv {f fe : ℝ → ℝ → ℝ} {S : Set ℝ} (hf : ∀ x e, 0 < f x e) {e : ℝ}
    (hd : ∀ x, HasDerivWithinAt (fun e => f x e) (fe x e) S e) (x₁ x₂ : ℝ) :
    HasDerivWithinAt (fun e => Real.log (f x₂ e) - Real.log (f x₁ e))
      (fe x₂ e / f x₂ e - fe x₁ e / f x₁ e) S e :=
  ((hd x₂).log (hf x₂ e).ne').sub ((hd x₁).log (hf x₁ e).ne')

/-- **Exercise 14.AA.1** (MWG, p. 510). For positive `f(π|e)` differentiable in `e ∈ [a, b]`
(`a < b`), `f_e(π|e) / f(π|e)` is nondecreasing in `π` for every `e ∈ [a, b]` iff
`f(π|e'') / f(π|e')` is nondecreasing in `π` whenever `e' < e''` in `[a, b]`. -/
theorem exercise_14_AA_1 {f fe : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ∀ x e, 0 < f x e)
    (hd : ∀ x, ∀ e ∈ Icc a b, HasDerivWithinAt (fun e => f x e) (fe x e) (Icc a b) e) :
    (∀ e ∈ Icc a b, Monotone fun x => fe x e / f x e) ↔
      ∀ e' ∈ Icc a b, ∀ e'' ∈ Icc a b, e' < e'' → Monotone fun x => f x e'' / f x e' := by
  -- both sides say: for `x₁ ≤ x₂`, `G = log f(x₂|·) - log f(x₁|·)` is monotone on `[a, b]`
  have key : ∀ x₁ x₂, MonotoneOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) ↔
      ∀ e ∈ Icc a b, 0 ≤ fe x₂ e / f x₂ e - fe x₁ e / f x₁ e :=
    fun x₁ x₂ => aa_mono_iff hab fun e he => aa_G_deriv hf (fun x => hd x e he) x₁ x₂
  constructor
  · intro h e' he' e'' he'' hlt x₁ x₂ hx
    have hm := (key x₁ x₂).2 fun e he => sub_nonneg.2 (h e he hx)
    have := hm he' he'' hlt.le
    simp only at this
    rw [aa_ratio_log (hf _ _) (hf _ _) (hf _ _) (hf _ _)]
    linarith
  · intro h e he x₁ x₂ hx
    have hm : MonotoneOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) := by
      intro e' he' e'' he'' hle
      rcases hle.lt_or_eq with hlt | heq
      · have := (aa_ratio_log (hf _ _) (hf _ _) (hf _ _) (hf _ _)).1 (h e' he' e'' he'' hlt hx)
        simp only; linarith
      · rw [heq]
    exact sub_nonneg.1 ((key x₁ x₂).1 hm e he)

/-- **Exercise 14.AA.1, strict "only if"**: if `f_e/f` is strictly increasing in `π` for every
`e ∈ [a, b]`, then `f(π|e'')/f(π|e')` is strictly increasing in `π` for `e' < e''`. -/
theorem exercise_14_AA_1_strict {f fe : ℝ → ℝ → ℝ} {a b : ℝ} (hf : ∀ x e, 0 < f x e)
    (hd : ∀ x, ∀ e ∈ Icc a b, HasDerivWithinAt (fun e => f x e) (fe x e) (Icc a b) e)
    (h : ∀ e ∈ Icc a b, StrictMono fun x => fe x e / f x e) :
    ∀ e' ∈ Icc a b, ∀ e'' ∈ Icc a b, e' < e'' → StrictMono fun x => f x e'' / f x e' := by
  intro e' he' e'' he'' hlt x₁ x₂ hx
  have hm : StrictMonoOn (fun e => Real.log (f x₂ e) - Real.log (f x₁ e)) (Icc a b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := fun e => fe x₂ e / f x₂ e - fe x₁ e / f x₁ e) (convex_Icc a b)
      (fun e he => (aa_G_deriv hf (fun x => hd x e he) x₁ x₂).continuousWithinAt)
      (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Icc] at he ⊢
      exact (aa_G_deriv hf (fun x => hd x e (Ioo_subset_Icc_self he)) x₁ x₂).mono
        Ioo_subset_Icc_self
    · rw [interior_Icc] at he
      exact sub_pos.2 (h e (Ioo_subset_Icc_self he) hx)
  have := hm he' he'' hlt
  simp only at this
  have hA := hf x₁ e''; have hB := hf x₁ e'; have hC := hf x₂ e''; have hD := hf x₂ e'
  rw [div_lt_div_iff₀ hB hD, ← Real.log_lt_log_iff (mul_pos hA hD) (mul_pos hC hB),
    Real.log_mul hA.ne' hD.ne', Real.log_mul hC.ne' hB.ne']
  linarith

/-- **Exercise 14.AA.1, the strict "if" is false** (correction). For `f(π|e) = exp(e³ π)` on
`e ∈ [-1, 1]` the ratio `f(π|e'')/f(π|e') = exp((e''³ - e'³) π)` is strictly increasing in `π` for
every `e' < e''`, but `f_e/f = 3 e² π` is constant in `π` at `e = 0`. (Multiplying `f` by any
positive normalizing factor `c(e)` changes neither property.) -/
theorem exercise_14_AA_1_strict_false :
    (∀ e' e'' : ℝ, e' < e'' →
        StrictMono fun x : ℝ => Real.exp (e'' ^ 3 * x) / Real.exp (e' ^ 3 * x)) ∧
      (∀ x e : ℝ, HasDerivAt (fun e => Real.exp (e ^ 3 * x))
        (3 * e ^ 2 * x * Real.exp (e ^ 3 * x)) e)
      ∧ ¬ StrictMono fun x : ℝ => 3 * (0 : ℝ) ^ 2 * x * Real.exp (0 ^ 3 * x) /
        Real.exp (0 ^ 3 * x) := by
  refine ⟨fun e' e'' hlt x₁ x₂ hx => ?_, fun x e => ?_, fun h => ?_⟩
  · simp only [← Real.exp_sub]
    apply Real.exp_lt_exp.2
    have : e' ^ 3 < e'' ^ 3 := Odd.strictMono_pow (by decide) hlt
    nlinarith
  · have := ((hasDerivAt_pow 3 e).mul_const x).exp
    convert this using 1
    push_cast; ring
  · have := h (show (0 : ℝ) < 1 by norm_num)
    simp at this

/-- **Exercise 14.AA.2** (MWG, p. 510), validity of the first-order approach. Two outcomes; the
manager's utility from effort `e ∈ [0, ē]` under utility levels `v_H ≥ v_L` is
`v_L + f(π_H|e)(v_H - v_L) - g(e)`. If `f(π_H|·)` is concave and `g` convex, any `e` satisfying the
first-order condition `f'(π_H|e)(v_H - v_L) = g'(e)` maximizes it. -/
theorem exercise_14_AA_2_valid {p dp g dg : ℝ → ℝ} {ebar : ℝ}
    (hp : ConcaveOn ℝ (Icc 0 ebar) p) (hg : ConvexOn ℝ (Icc 0 ebar) g)
    (hdp : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt p (dp e) (Icc 0 ebar) e)
    (hdg : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt g (dg e) (Icc 0 ebar) e)
    {vL vH : ℝ} (hv : vL ≤ vH) {e : ℝ} (he : e ∈ Icc 0 ebar) (hfoc : dp e * (vH - vL) = dg e) :
    ∀ e' ∈ Icc 0 ebar, vL + p e' * (vH - vL) - g e' ≤ vL + p e * (vH - vL) - g e := by
  intro e' he'
  have t1 := tpa_tangent_le hp he he' (hdp e he)
  have t2 := tpa_tangent_ge_convex hg he he' (hdg e he)
  have := mul_le_mul_of_nonneg_right t1 (sub_nonneg.2 hv)
  have e1 : dp e * (e' - e) * (vH - vL) = dg e * (e' - e) := by rw [← hfoc]; ring
  nlinarith

/-- **Exercise 14.AA.2** (MWG, p. 510), the optimal contract. Under the conditions of
`exercise_14_AA_2_valid`, with `f'(π_H|e) > 0`, `g'(e) ≥ 0` and wages `φ(v)` increasing in the
utility level (`φ = v⁻¹`), the cheapest utility levels implementing an interior `e ∈ (0, ē)` with
expected utility at least `ū` are `v_H - v_L = g'(e)/f'(π_H|e)` with participation binding:
every implementing pair is weakly more expensive. -/
theorem exercise_14_AA_2_contract {p dp g dg φ : ℝ → ℝ} {ebar ubar : ℝ}
    (hp : ConcaveOn ℝ (Icc 0 ebar) p) (hg : ConvexOn ℝ (Icc 0 ebar) g)
    (hdp : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt p (dp e) (Icc 0 ebar) e)
    (hdg : ∀ e ∈ Icc 0 ebar, HasDerivWithinAt g (dg e) (Icc 0 ebar) e)
    (hφ : Monotone φ) {e : ℝ} (he : e ∈ Ioo 0 ebar) (hp01 : 0 ≤ p e ∧ p e ≤ 1)
    (hdp0 : 0 < dp e) (hdg0 : 0 ≤ dg e) :
    let Δ := dg e / dp e
    let vL := ubar + g e - p e * Δ
    -- the contract implements `e` and gives exactly `ū`
    (∀ e' ∈ Icc 0 ebar, vL + p e' * Δ - g e' ≤ vL + p e * Δ - g e) ∧
      vL + p e * Δ - g e = ubar ∧
    -- every implementing pair costs at least as much
    ∀ uL uH : ℝ, (∀ e' ∈ Icc 0 ebar, uL + p e' * (uH - uL) - g e' ≤ uL + p e * (uH - uL) - g e) →
      ubar ≤ uL + p e * (uH - uL) - g e →
      p e * φ (vL + Δ) + (1 - p e) * φ vL ≤ p e * φ uH + (1 - p e) * φ uL := by
  intro Δ vL
  have hIcc : e ∈ Icc 0 ebar := Ioo_subset_Icc_self he
  have hΔ : 0 ≤ Δ := div_nonneg hdg0 hdp0.le
  have hfocΔ : dp e * Δ = dg e := by simp only [Δ]; field_simp
  refine ⟨fun e' he' => ?_, by simp only [vL]; ring, fun uL uH hIC hpart => ?_⟩
  · have := exercise_14_AA_2_valid hp hg hdp hdg (vL := vL) (vH := vL + Δ) (by linarith) hIcc
      (by rw [add_sub_cancel_left]; exact hfocΔ) e' he'
    simpa only [add_sub_cancel_left] using this
  · -- interior maximum: the first-order condition holds
    have hnhds : Icc 0 ebar ∈ 𝓝 e := Icc_mem_nhds he.1 he.2
    have hU : HasDerivAt (fun e => uL + p e * (uH - uL) - g e) (dp e * (uH - uL) - dg e) e :=
      ((((hdp e hIcc).hasDerivAt hnhds).mul_const (uH - uL)).const_add uL).sub
        ((hdg e hIcc).hasDerivAt hnhds)
    have hloc : IsLocalMax (fun e => uL + p e * (uH - uL) - g e) e :=
      Filter.mem_of_superset hnhds fun y hy => hIC y hy
    have hfoc := hloc.hasDerivAt_eq_zero hU
    have hdiff : uH - uL = Δ := by
      simp only [Δ]; field_simp; linarith
    have hLle : vL ≤ uL := by
      simp only [vL]; rw [hdiff] at hpart; linarith
    have hHle : vL + Δ ≤ uH := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (hφ hHle) hp01.1,
      mul_le_mul_of_nonneg_left (hφ hLle) (by linarith : (0:ℝ) ≤ 1 - p e)]

end MWG.PrincipalAgent
