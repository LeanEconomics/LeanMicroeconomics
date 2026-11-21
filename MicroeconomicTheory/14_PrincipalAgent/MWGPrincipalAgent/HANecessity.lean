/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.KuhnTucker
import MWGPrincipalAgent.AppendixA
import MWGPrincipalAgent.ExercisesB
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Necessity of the Kuhn-Tucker conditions in the hidden-action model

MWG, footnote 7 (p. 484), (14.B.10), Lemma 14.B.1, Exercise 14.B.2 (p. 507) and
(14.AA.2)-(14.AA.3) (p. 504).

Footnote 7 reformulates (14.B.9) as a convex program in the manager's utility levels
`v̂(π) = v(w(π))` and concludes that the Kuhn-Tucker conditions are necessary. Here this is proved
in the general model of `HiddenAction` (profits with a density with respect to an arbitrary
measure, measurable schemes with finite expected wage and utility):

* `ha_mix`: the scheme whose utility levels are the `t`-mixture of those of two schemes is
  admissible and pays at most the mixture of their wages (`v` concave): the program is
  convex-like in utility levels.
* `ha_piece_integral`, `ha_piece_adm`: changing a scheme to a constant on a measurable set.
* `ha_raise`: raising a scheme on a set of positive measure raises expected utilities strictly;
  with strict first-order stochastic dominance this gives a scheme satisfying (i) and (ii_H)
  strictly (`ha_slater`: Slater's condition).
* `ha_ae_min`: a scheme that cannot be improved by changing it to a constant on any measurable set
  minimizes the pointwise Lagrangian at almost every profit level.
* `ha_kt_general`: multipliers exist at every solution of a program with the constraints of
  (14.B.9) and any objective that is convex in utility levels (via `kt_convexlike`).
* `ha_kt_necessary`: **footnote 7**, the Kuhn-Tucker condition (14.B.10) with complementary
  slackness holds (almost everywhere) at every solution of (14.B.9) for `e = e_H`;
  `lemma_14_B_1_every`: in every solution both multipliers are positive.
* `exercise_14_B_2_necessary`: the same for a risk-averse owner.
* `foa_necessary`: **(14.AA.3)** holds at every solution of the relaxed program of the
  first-order approach (via `kt_convexlike_eq`).
* `inst_kt_necessary`, `inst_14_B_2_necessary`, `inst_foa_necessary`: proved instances.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

open Classical in
/-- Changing a function to the constant `q` on a measurable set `A`: integrability and the change
in the integral of `Ψ(π, w(π))`. -/
theorem ha_piece_integral {μ : Measure ℝ} {Ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (q : ℝ) (h1 : Integrable (fun x => Ψ x (w x)) μ)
    (h2 : Integrable (fun x => Ψ x q) μ) :
    Integrable (fun x => Ψ x (A.piecewise (fun _ => q) w x)) μ ∧
      ∫ x, Ψ x (A.piecewise (fun _ => q) w x) ∂μ - ∫ x, Ψ x (w x) ∂μ =
        ∫ x in A, (Ψ x q - Ψ x (w x)) ∂μ := by
  have heq : (fun x => Ψ x (A.piecewise (fun _ => q) w x)) =
      fun x => Ψ x (w x) + A.indicator (fun x => Ψ x q - Ψ x (w x)) x := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx]
  have hi : Integrable (fun x => A.indicator (fun x => Ψ x q - Ψ x (w x)) x) μ :=
    (h2.sub h1).indicator hA
  rw [heq]
  refine ⟨h1.add hi, ?_⟩
  rw [integral_add h1 hi, integral_indicator hA]
  ring

open Classical in
/-- A scheme changed to a constant on a measurable set is admissible. -/
theorem ha_piece_adm {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) {A : Set ℝ}
    (hA : MeasurableSet A) (q : ℝ) : M.Adm (A.piecewise (fun _ => q) w) :=
  ⟨Measurable.piecewise hA measurable_const hw.1, fun e =>
    ⟨(ha_piece_integral (Ψ := fun x c => c * M.f e x) hA q (hw.2 e).1
      ((hM.f_int e).const_mul q)).1,
     (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA q (hw.2 e).2
      ((hM.f_int e).const_mul _)).1⟩⟩

/-- **Footnote 7** (MWG, p. 484): the program is convex in utility levels. For admissible `w₀`,
`w₁` and `t ∈ [0, 1]` there is an admissible scheme `W` with
`v(W(π)) = (1 - t) v(w₀(π)) + t v(w₁(π))` at every `π`, and (as `v` is concave)
`W(π) ≤ (1 - t) w₀(π) + t w₁(π)`. -/
theorem ha_mix {M : HAModel ε} (hM : M.Standing) {w0 w1 : ℝ → ℝ} (hw0 : M.Adm w0)
    (hw1 : M.Adm w1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ W, M.Adm W ∧ (∀ x, M.v (W x) = (1 - t) * M.v (w0 x) + t * M.v (w1 x)) ∧
      ∀ x, W x ≤ (1 - t) * w0 x + t * w1 x := by
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hmono := ha_v_strictMono hM
  have hex : ∀ x, ∃ c, c ∈ Icc (min (w0 x) (w1 x)) (max (w0 x) (w1 x)) ∧
      M.v c = (1 - t) * M.v (w0 x) + t * M.v (w1 x) := by
    intro x
    have hmem : (1 - t) * M.v (w0 x) + t * M.v (w1 x) ∈
        Icc (M.v (min (w0 x) (w1 x))) (M.v (max (w0 x) (w1 x))) := by
      have a1 := hmono.monotone (min_le_left (w0 x) (w1 x))
      have a2 := hmono.monotone (min_le_right (w0 x) (w1 x))
      have a3 := hmono.monotone (le_max_left (w0 x) (w1 x))
      have a4 := hmono.monotone (le_max_right (w0 x) (w1 x))
      constructor <;> nlinarith
    exact intermediate_value_Icc min_le_max hvc.continuousOn hmem
  choose W hWI hWv using hex
  have hmixm : Measurable fun x => (1 - t) * M.v (w0 x) + t * M.v (w1 x) :=
    ((hvc.measurable.comp hw0.1).const_mul _).add ((hvc.measurable.comp hw1.1).const_mul _)
  have hWm : Measurable W := by
    refine measurable_of_Iic fun c => ?_
    have : W ⁻¹' Iic c = {x | (1 - t) * M.v (w0 x) + t * M.v (w1 x) ≤ M.v c} := by
      ext x
      change W x ≤ c ↔ (1 - t) * M.v (w0 x) + t * M.v (w1 x) ≤ M.v c
      rw [← hWv x]
      exact hmono.le_iff_le.symm
    rw [this]
    exact measurableSet_le hmixm measurable_const
  refine ⟨W, ⟨hWm, fun e => ⟨?_, ?_⟩⟩, hWv, fun x => ?_⟩
  · refine Integrable.mono' (((hw0.2 e).1.norm).add ((hw1.2 e).1.norm))
      (hWm.mul (hM.f_meas e)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hf := hM.f_pos e x
    change ‖W x * M.f e x‖ ≤ ‖w0 x * M.f e x‖ + ‖w1 x * M.f e x‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hf]
    have hb : |W x| ≤ |w0 x| + |w1 x| := by
      obtain ⟨h1, h2⟩ := hWI x
      rw [abs_le]
      constructor
      · exact le_trans (le_min (by linarith [neg_abs_le (w0 x), abs_nonneg (w1 x)])
          (by linarith [neg_abs_le (w1 x), abs_nonneg (w0 x)])) h1
      · exact h2.trans (max_le (by linarith [le_abs_self (w0 x), abs_nonneg (w1 x)])
          (by linarith [le_abs_self (w1 x), abs_nonneg (w0 x)]))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hb hf.le
  · have : (fun x => M.v (W x) * M.f e x) =
        fun x => (1 - t) * (M.v (w0 x) * M.f e x) + t * (M.v (w1 x) * M.f e x) := by
      funext x; rw [hWv x]; ring
    rw [this]
    exact ((hw0.2 e).2.const_mul _).add ((hw1.2 e).2.const_mul _)
  · have hc := hM.v_conc.2 (mem_univ (w0 x)) (mem_univ (w1 x)) (by linarith : 0 ≤ 1 - t) ht0
      (by ring)
    simp only [smul_eq_mul] at hc
    rw [← hWv x] at hc
    exact hmono.le_iff_le.1 hc

/-- Expected utilities of income are linear along the mixtures of `ha_mix`. -/
theorem ha_EV_mix {M : HAModel ε} {w0 w1 W : ℝ → ℝ} (hw0 : M.Adm w0) (hw1 : M.Adm w1) {t : ℝ}
    (hW : ∀ x, M.v (W x) = (1 - t) * M.v (w0 x) + t * M.v (w1 x)) (e : ε) :
    M.EV e W = (1 - t) * M.EV e w0 + t * M.EV e w1 := by
  unfold EV
  have : (fun x => M.v (W x) * M.f e x) =
      fun x => (1 - t) * (M.v (w0 x) * M.f e x) + t * (M.v (w1 x) * M.f e x) := by
    funext x; rw [hW x]; ring
  rw [this, integral_add ((hw0.2 e).2.const_mul _) ((hw1.2 e).2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- A set integral of a function positive on a set of positive measure is positive. -/
theorem ha_setIntegral_pos {μ : Measure ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hAμ : μ A ≠ 0)
    {k : ℝ → ℝ} (hk : IntegrableOn k A μ) (hpos : ∀ x ∈ A, 0 < k x) :
    0 < ∫ x in A, k x ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem hA fun x hx => (hpos x hx).le) hk]
  refine lt_of_lt_of_le (pos_iff_ne_zero.2 hAμ) (measure_mono fun x hx => ⟨?_, hx⟩)
  exact (hpos x hx).ne'

/-- Raising a scheme on a set `B` of positive measure. Given a weight `k` positive on `B`, there is
an admissible scheme with strictly higher expected utility of income under every effort and a
strictly higher `∫ v(w(π)) k(π) dπ`. -/
theorem ha_raise {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) {B : Set ℝ}
    (hB : MeasurableSet B) (hBν : M.ν B ≠ 0) {k : ℝ → ℝ}
    (hk : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * k x) M.ν)
    (hkpos : ∀ x ∈ B, 0 < k x) :
    ∃ w', M.Adm w' ∧ (∀ e, M.EV e w < M.EV e w') ∧
      ∫ x, M.v (w x) * k x ∂M.ν < ∫ x, M.v (w' x) * k x ∂M.ν := by
  have hU : B = ⋃ n : ℕ, B ∩ {x | w x ≤ n} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (w x)
      exact ⟨n, h, hn⟩
    · rintro ⟨n, h, -⟩
      exact h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M.ν (B ∩ {x | w x ≤ n}) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hBν (hU ▸ measure_iUnion_null hc)
  set A := B ∩ {x | w x ≤ n}
  have hA : MeasurableSet A := hB.inter (measurableSet_le hw.1 measurable_const)
  have hlt : ∀ x ∈ A, M.v (w x) < M.v ((n : ℝ) + 1) := fun x hx =>
    ha_v_strictMono hM (lt_of_le_of_lt hx.2 (by linarith))
  refine ⟨_, ha_piece_adm hM hw hA ((n : ℝ) + 1), fun e => ?_, ?_⟩
  · have h := (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA ((n : ℝ) + 1) (hw.2 e).2
      ((hM.f_int e).const_mul _)).2
    have hp : 0 < ∫ x in A, (M.v ((n : ℝ) + 1) * M.f e x - M.v (w x) * M.f e x) ∂M.ν :=
      ha_setIntegral_pos hA hn (((hM.f_int e).const_mul _).sub (hw.2 e).2).integrableOn
        fun x hx => by nlinarith [hlt x hx, hM.f_pos e x]
    unfold EV
    linarith
  · have h := (ha_piece_integral (Ψ := fun x c => M.v c * k x) hA ((n : ℝ) + 1)
      (hk w hw) (hk _ (ha_const_adm hM _))).2
    have hp : 0 < ∫ x in A, (M.v ((n : ℝ) + 1) * k x - M.v (w x) * k x) ∂M.ν :=
      ha_setIntegral_pos hA hn ((hk _ (ha_const_adm hM _)).sub (hk w hw)).integrableOn
        fun x hx => by nlinarith [hlt x hx, hkpos x hx.1]
    linarith

/-- **Slater's condition for (14.B.9)**. With strict first-order stochastic dominance, every
admissible scheme can be raised to one with strictly higher `EU(e_H)` and strictly higher
`EU(e_H) - EU(e_L)`; in particular, if (i) and (ii_H) hold, a scheme satisfying both strictly
exists. -/
theorem ha_slater {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL)
    {w : ℝ → ℝ} (hw : M.Adm w) :
    ∃ w', M.Adm w' ∧ M.EU eH w < M.EU eH w' ∧
      M.EU eH w - M.EU eL w < M.EU eH w' - M.EU eL w' := by
  have hpos : M.ν {x | M.f eL x < M.f eH x} ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂M.ν, 0 ≤ M.f eL x - M.f eH x := by
      rw [ae_iff]
      convert h0 using 2
      ext x
      simp [sub_nonneg, not_le]
    have hint : ∫ x, (M.f eL x - M.f eH x) ∂M.ν = 0 := by
      rw [integral_sub (hM.f_int eL) (hM.f_int eH), hM.f_one, hM.f_one, sub_self]
    have h0' := (integral_eq_zero_iff_of_nonneg_ae hae ((hM.f_int eL).sub (hM.f_int eH))).1 hint
    have h2 : ∀ᵐ x ∂M.ν, ¬ (M.f eH x < M.f eL x) := by
      filter_upwards [h0'] with x hx
      simp only [Pi.zero_apply] at hx
      linarith
    exact ha_fosd_set hM hfosd (by rw [ae_iff] at h2; simpa using h2)
  have hk : ∀ w', M.Adm w' →
      Integrable (fun x => M.v (w' x) * (M.f eH x - M.f eL x)) M.ν := fun w' hw' => by
    have := (hw'.2 eH).2.sub (hw'.2 eL).2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  obtain ⟨w', hw', hEV, hk'⟩ := ha_raise hM hw (measurableSet_lt (hM.f_meas eL) (hM.f_meas eH))
    hpos hk fun x hx => sub_pos.2 hx
  have hD : ∀ u, M.Adm u → ∫ x, M.v (u x) * (M.f eH x - M.f eL x) ∂M.ν = M.EV eH u - M.EV eL u :=
    fun u hu => by
      unfold EV
      rw [← integral_sub (hu.2 eH).2 (hu.2 eL).2]
      congr 1; funext x; ring
  rw [hD w hw, hD w' hw'] at hk'
  refine ⟨w', hw', ?_, ?_⟩ <;> unfold EU
  · linarith [hEV eH]
  · linarith

/-- A scheme `w` that cannot be improved, in the integral of a Lagrangian `ℓ(π, w(π))`, by changing
it to a constant on a measurable set minimizes `ℓ(π, ·)` at almost every `π`. -/
theorem ha_ae_min {μ : Measure ℝ} {ℓ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} (hc : ∀ x, Continuous (ℓ x))
    (hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) μ)
    (hA : ∀ A, MeasurableSet A → ∀ q, 0 ≤ ∫ x in A, (ℓ x q - ℓ x (w x)) ∂μ) :
    ∀ᵐ x ∂μ, ∀ c, ℓ x (w x) ≤ ℓ x c := by
  have h : ∀ q : ℚ, ∀ᵐ x ∂μ, 0 ≤ ℓ x q - ℓ x (w x) := fun q =>
    ae_nonneg_of_forall_setIntegral_nonneg (hint q) fun s hs _ => hA s hs q
  filter_upwards [ae_all_iff.2 h] with x hx c
  refine Rat.denseRange_cast.induction_on c (isClosed_le continuous_const (hc x)) fun q => ?_
  linarith [hx q]

/-- **Footnote 7** (MWG, p. 484), general form. Two effort levels with strict first-order
stochastic dominance; an objective `∫ φ(π, w(π)) dπ` that is convex in utility levels (`hφconv`).
At every `w` minimizing it subject to (i) and (ii_H) there are multipliers `γ, μ ≥ 0` with
complementary slackness such that, at almost every `π`, `w(π)` minimizes the pointwise Lagrangian
`c ↦ φ(π, c) - (γ + μ) v(c) f(π|e_H) + μ v(c) f(π|e_L)`. -/
theorem ha_kt_general {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (φ : ℝ → ℝ → ℝ)
    (hφi : ∀ w', M.Adm w' → Integrable (fun x => φ x (w' x)) M.ν)
    (hφc : ∀ x, Continuous (φ x))
    (hφconv : ∀ x a b c t, 0 ≤ t → t ≤ 1 → c ≤ (1 - t) * a + t * b →
      φ x c ≤ (1 - t) * φ x a + t * φ x b)
    {w : ℝ → ℝ} (hw : M.HAFeasible eH w)
    (hopt : ∀ w', M.HAFeasible eH w' → ∫ x, φ x (w x) ∂M.ν ≤ ∫ x, φ x (w' x) ∂M.ν) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, ∀ c, φ x (w x) - (γ + μ) * (M.v (w x) * M.f eH x) +
        μ * (M.v (w x) * M.f eL x) ≤
        φ x c - (γ + μ) * (M.v c * M.f eH x) + μ * (M.v c * M.f eL x) := by
  classical
  let X := {u : ℝ → ℝ // M.Adm u}
  let J : X → ℝ := fun u => ∫ x, φ x (u.1 x) ∂M.ν
  let G : Fin 2 → X → ℝ := ![fun u => M.ubar - M.EU eH u.1, fun u => M.EU eL u.1 - M.EU eH u.1]
  have hii := (ha_IC_two hE w).1 hw.2
  obtain ⟨lam, hlam, hcs, hlag⟩ := kt_convexlike J G ⟨w, hw.1.1⟩
    (Fin.forall_fin_two.2 ⟨by simp [G]; linarith [hw.1.2], by simp [G]; linarith⟩)
    (fun u hu => by
      have h0 := hu 0
      have h1 := hu 1
      simp only [G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
      exact hopt u.1 ⟨⟨u.2, by linarith⟩, (ha_IC_two hE u.1).2 (by linarith)⟩)
    (fun u0 u1 t ht0 ht1 => by
      obtain ⟨W, hW, hWv, hWle⟩ := ha_mix hM u0.2 u1.2 ht0 ht1
      refine ⟨⟨W, hW⟩, ?_, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · change ∫ x, φ x (W x) ∂M.ν ≤ (1 - t) * (∫ x, φ x (u0.1 x) ∂M.ν) +
          t * ∫ x, φ x (u1.1 x) ∂M.ν
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((hφi _ u0.2).const_mul _) ((hφi _ u1.2).const_mul _)]
        exact integral_mono (hφi _ hW)
          (((hφi _ u0.2).const_mul _).add ((hφi _ u1.2).const_mul _))
          fun x => hφconv x _ _ _ t ht0 ht1 (hWle x)
      · simp only [G, Matrix.cons_val_zero]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv]
        nlinarith
      · simp only [G, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv, ha_EV_mix u0.2 u1.2 hWv]
        nlinarith)
    (by
      obtain ⟨w', hw', h1, h2⟩ := ha_slater hM hfosd hw.1.1
      refine ⟨⟨w', hw'⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · simp only [G, Matrix.cons_val_zero]; linarith [hw.1.2]
      · simp only [G, Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith)
  set γ := lam 0
  set μ := lam 1
  have hcs0 : γ * (M.ubar - M.EU eH w) = 0 := hcs 0
  have hcs1 : μ * (M.EU eL w - M.EU eH w) = 0 := hcs 1
  have hlag' : ∀ u : ℝ → ℝ, M.Adm u → ∫ x, φ x (w x) ∂M.ν ≤ ∫ x, φ x (u x) ∂M.ν +
      γ * (M.ubar - M.EU eH u) + μ * (M.EU eL u - M.EU eH u) := by
    intro u hu
    have := hlag ⟨u, hu⟩
    simp only [Fin.sum_univ_two, G, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, J] at this
    linarith
  refine ⟨γ, μ, hlam 0, hlam 1, by linear_combination -hcs0, by linear_combination -hcs1, ?_⟩
  let ℓ : ℝ → ℝ → ℝ := fun x c =>
    φ x c - (γ + μ) * (M.v c * M.f eH x) + μ * (M.v c * M.f eL x)
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hVi : ∀ e q, Integrable (fun x => M.v q * M.f e x) M.ν := fun e q =>
    (hM.f_int e).const_mul _
  have hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) M.ν := by
    intro q
    exact ((((hφi _ (ha_const_adm hM q)).sub ((hVi eH q).const_mul _)).add
      ((hVi eL q).const_mul _)).sub (((hφi _ hw.1.1).sub ((hw.1.1.2 eH).2.const_mul _)).add
      ((hw.1.1.2 eL).2.const_mul _)))
  refine ha_ae_min (ℓ := ℓ) (fun x => ?_) hint fun A hA q => ?_
  · exact ((hφc x).sub (continuous_const.mul (hvc.mul continuous_const))).add
      (continuous_const.mul (hvc.mul continuous_const))
  · have hu := ha_piece_adm hM hw.1.1 hA q
    have h0 : ∫ x, φ x (A.piecewise (fun _ => q) w x) ∂M.ν - ∫ x, φ x (w x) ∂M.ν =
        ∫ x in A, (φ x q - φ x (w x)) ∂M.ν :=
      (ha_piece_integral hA q (hφi _ hw.1.1) (hφi _ (ha_const_adm hM q))).2
    have hH : M.EV eH (A.piecewise (fun _ => q) w) - M.EV eH w =
        ∫ x in A, (M.v q * M.f eH x - M.v (w x) * M.f eH x) ∂M.ν :=
      (ha_piece_integral (Ψ := fun x c => M.v c * M.f eH x) hA q (hw.1.1.2 eH).2 (hVi eH q)).2
    have hL : M.EV eL (A.piecewise (fun _ => q) w) - M.EV eL w =
        ∫ x in A, (M.v q * M.f eL x - M.v (w x) * M.f eL x) ∂M.ν :=
      (ha_piece_integral (Ψ := fun x c => M.v c * M.f eL x) hA q (hw.1.1.2 eL).2 (hVi eL q)).2
    have hl := hlag' _ hu
    have I1 : IntegrableOn (fun x => φ x q - φ x (w x)) A M.ν :=
      ((hφi _ (ha_const_adm hM q)).sub (hφi _ hw.1.1)).integrableOn
    have I2 : IntegrableOn (fun x => (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x))
        A M.ν := (((hVi eH q).sub (hw.1.1.2 eH).2).const_mul (γ + μ)).integrableOn
    have I3 : IntegrableOn (fun x => μ * (M.v q * M.f eL x - M.v (w x) * M.f eL x)) A M.ν :=
      (((hVi eL q).sub (hw.1.1.2 eL).2).const_mul μ).integrableOn
    have I12 : IntegrableOn (fun x => (φ x q - φ x (w x)) -
        (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x)) A M.ν := I1.sub I2
    have e1 : ∫ x in A, (ℓ x q - ℓ x (w x)) ∂M.ν =
        ∫ x in A, ((φ x q - φ x (w x)) -
          (γ + μ) * (M.v q * M.f eH x - M.v (w x) * M.f eH x) +
          μ * (M.v q * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν := by
      congr 1; funext x; simp only [ℓ]; ring
    rw [e1, integral_add I12 I3, integral_sub I1 I2, integral_const_mul,
      integral_const_mul, ← h0, ← hH, ← hL]
    unfold EU at hl hcs0 hcs1
    nlinarith

/-- **Footnote 7 and (14.B.10)** (MWG, p. 484): necessity of the Kuhn-Tucker conditions. Two
effort levels, `F(·|e_H)` strictly first-order stochastically dominates `F(·|e_L)`. At every
solution `w` of (14.B.9) for `e = e_H` there are multipliers `γ, μ ≥ 0` with complementary
slackness such that `1 / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π`. -/
theorem ha_kt_necessary {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) {w : ℝ → ℝ}
    (hw : M.IsHACostMin eH w) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  obtain ⟨γ, μ, hγ, hμ, h1, h2, hmin⟩ := ha_kt_general hM hE hfosd (fun x c => c * M.f eH x)
    (fun w' hw' => (hw'.2 eH).1) (fun x => continuous_id.mul continuous_const)
    (fun x a b c t _ _ hc => by nlinarith [hM.f_pos eH x]) hw.1 (fun w' hw' => hw.2 w' hw')
  refine ⟨γ, μ, hγ, hμ, h1, h2, ?_⟩
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => c * M.f eH x - (γ + μ) * (M.v c * M.f eH x) +
      μ * (M.v c * M.f eL x)) (1 * M.f eH x - (γ + μ) * (M.dv (w x) * M.f eH x) +
      μ * (M.dv (w x) * M.f eL x)) (w x) :=
    (((hasDerivAt_id' (w x)).mul_const _).sub (((hM.v_deriv _).mul_const _).const_mul _)).add
      (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos eH x
  field_simp
  linarith

/-- **Lemma 14.B.1** (MWG, p. 484), as stated: in *any* solution of (14.B.9) with `e = e_H` the
Kuhn-Tucker multipliers exist and both are positive (strict first-order stochastic dominance,
`g(e_H) > g(e_L)`, `v'` strictly decreasing). -/
theorem lemma_14_B_1_every {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (hg : M.g eL < M.g eH)
    (hda : StrictAnti M.dv) {w : ℝ → ℝ} (hw : M.IsHACostMin eH w) :
    ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  obtain ⟨γ, μ, hγ, hμ, -, -, hfoc⟩ := ha_kt_necessary hM hE hfosd hw
  obtain ⟨h1, h2⟩ := lemma_14_B_1 hM hfosd hg hda ((ha_IC_two hE w).1 hw.1.2) hγ hμ hfoc
  exact ⟨γ, μ, h1, h2, hfoc⟩

/-- **Exercise 14.B.2** (MWG, p. 507), necessity. A risk-averse owner with a concave,
nondecreasing, differentiable utility `U` of net profit (strict first-order stochastic dominance,
two efforts). At every scheme `w` maximizing the owner's expected utility
`∫ U(π - w(π)) f(π|e_H) dπ` subject to (i) and (ii_H), there are multipliers `γ, μ ≥ 0` with
complementary slackness such that
`U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π`. -/
theorem exercise_14_B_2_necessary {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) {U dU : ℝ → ℝ}
    (hU : ConcaveOn ℝ univ U) (hdU : ∀ y, HasDerivAt U (dU y) y) (hdU0 : ∀ y, 0 ≤ dU y)
    (hUi : ∀ w', M.Adm w' → Integrable (fun x => U (x - w' x) * M.f eH x) M.ν)
    {w : ℝ → ℝ} (hw : M.HAFeasible eH w)
    (hopt : ∀ w', M.HAFeasible eH w' →
      ∫ x, U (x - w' x) * M.f eH x ∂M.ν ≤ ∫ x, U (x - w x) * M.f eH x ∂M.ν) :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (M.EU eH w - M.ubar) = 0 ∧
      μ * (M.EU eH w - M.EU eL w) = 0 ∧
      ∀ᵐ x ∂M.ν, dU (x - w x) / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x) := by
  have hUm : Monotone U := monotone_of_deriv_nonneg (fun y => (hdU y).differentiableAt)
    (fun y => (hdU y).deriv ▸ hdU0 y)
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun y => (hdU y).continuousAt
  obtain ⟨γ, μ, hγ, hμ, h1, h2, hmin⟩ := ha_kt_general hM hE hfosd
    (fun x c => -(U (x - c) * M.f eH x)) (fun w' hw' => (hUi w' hw').neg)
    (fun x => ((hUc.comp (continuous_const.sub continuous_id)).mul continuous_const).neg)
    (fun x a b c t ht0 ht1 hc => by
      have hf := hM.f_pos eH x
      have hmo : U (x - ((1 - t) * a + t * b)) ≤ U (x - c) := hUm (by linarith)
      have hcv := hU.2 (mem_univ (x - a)) (mem_univ (x - b)) (by linarith : 0 ≤ 1 - t) ht0
        (by ring)
      simp only [smul_eq_mul] at hcv
      have : (1 - t) * (x - a) + t * (x - b) = x - ((1 - t) * a + t * b) := by ring
      rw [this] at hcv
      nlinarith)
    hw (fun w' hw' => by
      rw [integral_neg, integral_neg]; linarith [hopt w' hw'])
  refine ⟨γ, μ, hγ, hμ, h1, h2, ?_⟩
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => -(U (x - c) * M.f eH x) - (γ + μ) * (M.v c * M.f eH x) +
      μ * (M.v c * M.f eL x)) (-(dU (x - w x) * -1 * M.f eH x) -
      (γ + μ) * (M.dv (w x) * M.f eH x) + μ * (M.dv (w x) * M.f eL x)) (w x) :=
    ((((hdU (x - w x)).comp (w x) ((hasDerivAt_id' (w x)).const_sub x)).mul_const _).neg.sub
      (((hM.v_deriv _).mul_const _).const_mul _)).add (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos eH x
  field_simp
  linarith

/-- **(14.AA.2)-(14.AA.3)** (MWG, p. 504), necessity. The relaxed program of the first-order
approach: minimize `∫ w f(·|e)` over admissible schemes subject to participation and the
manager's first-order condition `∫ v(w(π)) f_e(π|e) dπ = g'(e)`. Suppose `f_e` is measurable, the
integrals exist, and `f_e` is positive on a set of positive measure and negative on another (as for
the derivative of a family of densities that is not constant). Then at every solution there are
`λ ≥ 0` (with complementary slackness) and `μ` such that
`1 / v'(w(π)) = λ + μ f_e(π|e)/f(π|e)` at almost every `π`. -/
theorem foa_necessary {M : HAModel ε} (hM : M.Standing) {e : ε} {fe : ℝ → ℝ} {dg : ℝ}
    (hfem : Measurable fe)
    (hfe : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * fe x) M.ν)
    (hpos : M.ν {x | 0 < fe x} ≠ 0) (hneg : M.ν {x | fe x < 0} ≠ 0)
    {w : ℝ → ℝ} (hw : M.Adm w) (hpart : M.ubar ≤ M.EU e w)
    (hfoa : ∫ x, M.v (w x) * fe x ∂M.ν = dg)
    (hopt : ∀ w', M.Adm w' → M.ubar ≤ M.EU e w' → ∫ x, M.v (w' x) * fe x ∂M.ν = dg →
      M.EW e w ≤ M.EW e w') :
    ∃ lam μ : ℝ, 0 ≤ lam ∧ lam * (M.EU e w - M.ubar) = 0 ∧
      ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = lam + μ * (fe x / M.f e x) := by
  classical
  let X := {u : ℝ → ℝ // M.Adm u}
  let J : X → ℝ := fun u => M.EW e u.1
  let G : Fin 1 → X → ℝ := fun _ u => M.ubar - M.EU e u.1
  let H : X → ℝ := fun u => ∫ x, M.v (u.1 x) * fe x ∂M.ν - dg
  obtain ⟨wp, hwp, hEVp, hHp⟩ :=
    ha_raise hM hw (measurableSet_lt measurable_const hfem) hpos hfe fun x hx => hx
  have hfe' : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * -fe x) M.ν :=
    fun w' hw' => by
      refine (hfe w' hw').neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]; ring
  obtain ⟨wm, hwm, hEVm, hHm⟩ :=
    ha_raise hM hw (measurableSet_lt hfem measurable_const) hneg (k := fun x => -fe x) hfe'
      fun x hx => neg_pos.2 hx
  simp only [mul_neg, integral_neg] at hHm
  have hmixH : ∀ u0 u1 : ℝ → ℝ, M.Adm u0 → M.Adm u1 → ∀ (W : ℝ → ℝ) (t : ℝ),
      (∀ x, M.v (W x) = (1 - t) * M.v (u0 x) + t * M.v (u1 x)) →
      ∫ x, M.v (W x) * fe x ∂M.ν =
        (1 - t) * ∫ x, M.v (u0 x) * fe x ∂M.ν + t * ∫ x, M.v (u1 x) * fe x ∂M.ν := by
    intro u0 u1 hu0 hu1 W t hW
    have : (fun x => M.v (W x) * fe x) =
        fun x => (1 - t) * (M.v (u0 x) * fe x) + t * (M.v (u1 x) * fe x) := by
      funext x; rw [hW x]; ring
    rw [this, integral_add ((hfe _ hu0).const_mul _) ((hfe _ hu1).const_mul _),
      integral_const_mul, integral_const_mul]
  obtain ⟨lam, ν0, hlam, hcs, hlag⟩ := kt_convexlike_eq J G H ⟨w, hw⟩
    (fun _ => by simp only [G]; linarith) (by simp only [H, hfoa, sub_self])
    (fun u hu hHu => hopt u.1 u.2 (by linarith [hu 0]) (by simp only [H] at hHu; linarith))
    (fun u0 u1 t ht0 ht1 => by
      obtain ⟨W, hW, hWv, hWle⟩ := ha_mix hM u0.2 u1.2 ht0 ht1
      refine ⟨⟨W, hW⟩, ?_, fun _ => ?_, ?_⟩
      · change M.EW e W ≤ (1 - t) * M.EW e u0.1 + t * M.EW e u1.1
        unfold EW
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add (((u0.2).2 e).1.const_mul _) (((u1.2).2 e).1.const_mul _)]
        refine integral_mono (hW.2 e).1 ((((u0.2).2 e).1.const_mul _).add
          (((u1.2).2 e).1.const_mul _)) fun x => ?_
        have hf := hM.f_pos e x
        have := mul_le_mul_of_nonneg_right (hWle x) hf.le
        simp only
        linarith
      · simp only [G]
        unfold EU
        rw [ha_EV_mix u0.2 u1.2 hWv]
        nlinarith
      · simp only [H]
        rw [hmixH _ _ u0.2 u1.2 W t hWv]
        ring)
    (xp := ⟨wp, hwp⟩) (xm := ⟨wm, hwm⟩)
    (fun _ => by have h := hpart; simp only [G]; unfold EU at h ⊢; linarith [hEVp e])
    (fun _ => by have h := hpart; simp only [G]; unfold EU at h ⊢; linarith [hEVm e])
    (by simp only [H]; linarith) (by simp only [H]; linarith)
  set lam0 := lam 0
  have hcs0 : lam0 * (M.ubar - M.EU e w) = 0 := hcs 0
  have hlag' : ∀ u : ℝ → ℝ, M.Adm u → M.EW e w ≤ M.EW e u +
      lam0 * (M.ubar - M.EU e u) + ν0 * (∫ x, M.v (u x) * fe x ∂M.ν - dg) := by
    intro u hu
    have := hlag ⟨u, hu⟩
    simp only [Fin.sum_univ_one, J, G, H] at this
    linarith
  refine ⟨lam0, -ν0, hlam 0, by linear_combination -hcs0, ?_⟩
  let ℓ : ℝ → ℝ → ℝ := fun x c =>
    c * M.f e x - lam0 * (M.v c * M.f e x) + ν0 * (M.v c * fe x)
  have hvc : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hVi : ∀ q, Integrable (fun x => M.v q * M.f e x) M.ν := fun q =>
    (hM.f_int e).const_mul _
  have hWi : ∀ q, Integrable (fun x => q * M.f e x) M.ν := fun q => (hM.f_int e).const_mul _
  have hint : ∀ q, Integrable (fun x => ℓ x q - ℓ x (w x)) M.ν := by
    intro q
    exact ((((hWi q).sub ((hVi q).const_mul _)).add
      ((hfe _ (ha_const_adm hM q)).const_mul _)).sub
      ((((hw.2 e).1).sub (((hw.2 e).2).const_mul _)).add ((hfe w hw).const_mul _)))
  have hmin : ∀ᵐ x ∂M.ν, ∀ c, ℓ x (w x) ≤ ℓ x c := by
    refine ha_ae_min (ℓ := ℓ) (fun x => ?_) hint fun A hA q => ?_
    · exact ((continuous_id.mul continuous_const).sub
        (continuous_const.mul (hvc.mul continuous_const))).add
        (continuous_const.mul (hvc.mul continuous_const))
    · have hu := ha_piece_adm hM hw hA q
      have h0 : M.EW e (A.piecewise (fun _ => q) w) - M.EW e w =
          ∫ x in A, (q * M.f e x - w x * M.f e x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => c * M.f e x) hA q (hw.2 e).1 (hWi q)).2
      have hV : M.EV e (A.piecewise (fun _ => q) w) - M.EV e w =
          ∫ x in A, (M.v q * M.f e x - M.v (w x) * M.f e x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => M.v c * M.f e x) hA q (hw.2 e).2 (hVi q)).2
      have hF : ∫ x, M.v (A.piecewise (fun _ => q) w x) * fe x ∂M.ν -
          ∫ x, M.v (w x) * fe x ∂M.ν = ∫ x in A, (M.v q * fe x - M.v (w x) * fe x) ∂M.ν :=
        (ha_piece_integral (Ψ := fun x c => M.v c * fe x) hA q (hfe w hw)
          (hfe _ (ha_const_adm hM q))).2
      have hl := hlag' _ hu
      have I1 : IntegrableOn (fun x => q * M.f e x - w x * M.f e x) A M.ν :=
        ((hWi q).sub (hw.2 e).1).integrableOn
      have I2 : IntegrableOn (fun x => lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x)) A M.ν :=
        (((hVi q).sub (hw.2 e).2).const_mul _).integrableOn
      have I3 : IntegrableOn (fun x => ν0 * (M.v q * fe x - M.v (w x) * fe x)) A M.ν :=
        (((hfe _ (ha_const_adm hM q)).sub (hfe w hw)).const_mul _).integrableOn
      have I12 : IntegrableOn (fun x => (q * M.f e x - w x * M.f e x) -
          lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x)) A M.ν := I1.sub I2
      have e1 : ∫ x in A, (ℓ x q - ℓ x (w x)) ∂M.ν =
          ∫ x in A, ((q * M.f e x - w x * M.f e x) -
            lam0 * (M.v q * M.f e x - M.v (w x) * M.f e x) +
            ν0 * (M.v q * fe x - M.v (w x) * fe x)) ∂M.ν := by
        congr 1; funext x; simp only [ℓ]; ring
      rw [e1, integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul,
        ← h0, ← hV, ← hF, hfoa]
      unfold EU at hl hcs0
      nlinarith
  filter_upwards [hmin] with x hx
  have hd : HasDerivAt (fun c => c * M.f e x - lam0 * (M.v c * M.f e x) +
      ν0 * (M.v c * fe x)) (1 * M.f e x - lam0 * (M.dv (w x) * M.f e x) +
      ν0 * (M.dv (w x) * fe x)) (w x) :=
    (((hasDerivAt_id' (w x)).mul_const _).sub (((hM.v_deriv _).mul_const _).const_mul _)).add
      (((hM.v_deriv _).mul_const _).const_mul _)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hx) hd
  have hdv := hM.dv_pos (w x)
  have hf := hM.f_pos e x
  field_simp
  linarith

end HAModel

/-- **Footnote 7, an instance** (MWG, p. 484). In `exA` the optimal scheme `exW` (Figure 14.B.1)
has Kuhn-Tucker multipliers, and they are positive (Lemma 14.B.1), by the necessity theorems. -/
theorem inst_kt_necessary :
    (∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (exA.EU true exW - exA.ubar) = 0 ∧
      μ * (exA.EU true exW - exA.EU false exW) = 0 ∧
      ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = γ + μ * (1 - exA.f false x / exA.f true x)) ∧
    ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
      ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = γ + μ * (1 - exA.f false x / exA.f true x) :=
  ⟨HAModel.ha_kt_necessary exA_standing exA_two (exA_fosd _ _ _ _) exA_optimal,
    HAModel.lemma_14_B_1_every exA_standing exA_two (exA_fosd _ _ _ _)
      (by norm_num [exA, exModel]) exA_dv_anti exA_optimal⟩

/-- **Exercise 14.B.2, an instance** (MWG, p. 507). In `exA`, with the owner's utility `U(y) = y`
(concave and nondecreasing), `exW` maximizes the owner's expected utility subject to (i) and
(ii_H), so the necessity theorem applies and yields the multipliers. -/
theorem inst_14_B_2_necessary :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (exA.EU true exW - exA.ubar) = 0 ∧
      μ * (exA.EU true exW - exA.EU false exW) = 0 ∧
      ∀ᵐ x ∂exA.ν, (fun _ => (1 : ℝ)) (x - exW x) / exA.dv (exW x) =
        γ + μ * (1 - exA.f false x / exA.f true x) := by
  refine HAModel.exercise_14_B_2_necessary exA_standing exA_two (exA_fosd _ _ _ _)
    (U := fun y => y) (concaveOn_id convex_univ) (fun y => hasDerivAt_id' y)
    (fun _ => zero_le_one) (fun _ _ => dmeas_integrable _ _) exA_optimal.1 fun w' hw' => ?_
  change exA.OP true w' ≤ exA.OP true exW
  rw [HAModel.ha_OP_eq exA_standing hw'.1.1, HAModel.ha_OP_eq exA_standing exW_adm]
  linarith [exA_optimal.2 w' hw']

/-- The model of the first-order-approach instance: profit levels `0, 1, 2` with
`f(·|e) = (1/4, 1/2, 1/4)`, `v(w) = -exp(-w)`, no disutility of effort and `ū = -7/12`. -/
noncomputable def exFOA : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) 0 (-7 / 12)

/-- The solution of the relaxed program in `exFOA`: `w = 0, log 2, log 3` at `π = 0, 1, 2`. -/
noncomputable def exWf (x : ℝ) : ℝ :=
  if x < 1 / 2 then 0 else if x < 3 / 2 then Real.log 2 else Real.log 3

/-- **(14.AA.3), an instance** (MWG, p. 504). In `exFOA` with `f_e(π|e) = (π - 1)/4` and
`g'(e) = 1/6`, the scheme `exWf` solves the relaxed program of the first-order approach (by
`foa_sufficient`, with `λ = 2`, `μ = 1`), and the necessity theorem applies to it. -/
theorem inst_foa_necessary :
    ∃ lam μ : ℝ, 0 ≤ lam ∧ lam * (exFOA.EU true exWf - exFOA.ubar) = 0 ∧
      ∀ᵐ x ∂exFOA.ν, 1 / exFOA.dv (exWf x) = lam + μ * ((x - 1) / 4 / exFOA.f true x) := by
  have hst : exFOA.Standing :=
    exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _
  have hadm : exFOA.Adm exWf := by
    refine ⟨?_, fun _ => ⟨dmeas_integrable _ _, dmeas_integrable _ _⟩⟩
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        measurable_const)
  have hfe : ∀ w', exFOA.Adm w' →
      Integrable (fun x => exFOA.v (w' x) * ((x - 1) / 4)) exFOA.ν :=
    fun _ _ => dmeas_integrable _ _
  have h0 : exWf 0 = 0 := by norm_num [exWf]
  have h1 : exWf 1 = Real.log 2 := by norm_num [exWf]
  have h2 : exWf 2 = Real.log 3 := by norm_num [exWf]
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e3 : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEU : exFOA.EU true exWf = -7 / 12 := by
    change (∫ x, -Real.exp (-exWf x) * exF true x ∂dmeas exPts) - (if true then (0 : ℝ) else 0)
      = -7 / 12
    rw [exA_integral, h0, h1, h2, e2, e3]
    simp only [exF]
    norm_num
  have hfoa : ∫ x, exFOA.v (exWf x) * ((x - 1) / 4) ∂exFOA.ν = 1 / 6 := by
    change ∫ x, -Real.exp (-exWf x) * ((x - 1) / 4) ∂dmeas exPts = 1 / 6
    rw [exA_integral, h0, h1, h2, e2, e3]
    norm_num
  have hfoc : ∀ᵐ x ∂exFOA.ν,
      1 / exFOA.dv (exWf x) = 2 + 1 * ((x - 1) / 4 / exFOA.f true x) := by
    refine dmeas_ae _ fun i => ?_
    change 1 / Real.exp (-exWf (exPts i)) = 2 + 1 * ((exPts i - 1) / 4 / exF true (exPts i))
    fin_cases i <;> simp only [exPts, exF] <;> norm_num [h0, h1, h2, Real.exp_neg,
      Real.exp_log]
  have hset : ∀ (P : ℝ → Prop) (i : Fin 3), MeasurableSet {x | P x} → P (exPts i) →
      exFOA.ν {x | P x} ≠ 0 := by
    intro P i hP hi h
    have hsum : exFOA.ν {x | P x} = ∑ j, Measure.dirac (exPts j) {x | P x} := by
      change (∑ j, Measure.dirac (exPts j)) {x | P x} = _
      rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hle := Finset.single_le_sum (f := fun j => Measure.dirac (exPts j) {x | P x})
      (fun j _ => zero_le) (Finset.mem_univ i)
    rw [← hsum, h, Measure.dirac_apply' _ hP, indicator_of_mem (by exact hi)] at hle
    simp at hle
  refine HAModel.foa_necessary hst (by fun_prop) hfe
    (hset _ 2 (measurableSet_lt measurable_const (by fun_prop)) (by norm_num [exPts]))
    (hset _ 0 (measurableSet_lt (by fun_prop) measurable_const) (by norm_num [exPts]))
    hadm (by rw [hEU]; exact le_refl _) hfoa fun w' hw' hp hf => ?_
  exact foa_sufficient hst hfe hadm (lam := 2) (μ := 1) (by norm_num) hfoc
    (by rw [hEU]; change (2 : ℝ) * (-7 / 12 - -7 / 12) = 0; ring) hfoa hw' hp hf

end MWG.PrincipalAgent
