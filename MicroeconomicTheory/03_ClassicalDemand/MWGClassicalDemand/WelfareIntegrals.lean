/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareBasic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Welfare evaluation: areas under Hicksian and Walrasian demand curves

MWG, Section 3.I, pp. 83-91, and in-text Exercises 3.I.1-3.I.2 and Exercise 3.I.3.

The consumer has a continuous, strictly quasiconcave utility `u` representing a locally
nonsatiated `≿` (so demands are single-valued); `xs` is the Walrasian demand function (a selection
from `x(p, w)`), and `h(p, ū) = x(p, e(p, ū))` (`hicksianOf`) is the Hicksian demand function, by
(3.E.4). Only the price of good `l` changes, along the line `t ↦ p̄` with `p̄_l` replaced by `t`.

* Along the line, `e(·, ū)` is an antiderivative of the Hicksian demand curve, which is
  nonincreasing (`expenditure_line_integral`); hence (3.I.3)-(3.I.4), the EV and CV as areas to
  the left of Hicksian demand curves.
* The area variation (3.I.8) and its comparison with EV and CV: `CV ≤ AV ≤ EV` for a normal good,
  `EV ≤ AV ≤ CV` for an inferior good (pp. 83, 89, Exercise 3.I.3), equality without wealth effects
  (the Marshallian consumer surplus).
* Example 3.I.1: the deadweight losses (3.I.5), (3.I.6) as integrals, nonnegative, and positive if
  the Hicksian demand curve is strictly decreasing.
* Exercise 3.I.1 (two prices change) and Exercise 3.I.2 (the derivative of the deadweight loss
  with respect to the tax; correction D4).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology MeasureTheory

variable {L : ℕ}

/-- The Hicksian demand function induced by a Walrasian demand function `xs`:
`h(p, ū) = x(p, e(p, ū))` (equation (3.E.4)). -/
noncomputable def hicksianOf (u : (Fin L → ℝ) → ℝ) (xs : DemandFunction L) (q : Fin L → ℝ)
    (ub : ℝ) : Fin L → ℝ :=
  xs q (expenditure u q ub)

/-- The price vector `p̄` with the price of good `l` replaced by `t`. -/
def priceLine (pb : Fin L → ℝ) (l : Fin L) (t : ℝ) : Fin L → ℝ := Function.update pb l t

/-- A price line is strictly positive at `t > 0`. -/
theorem priceLine_pos {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {t : ℝ}
    (ht : 0 < t) : StrictlyPositive (priceLine pb l t) := by
  intro k
  by_cases hk : k = l
  · subst hk; simp [priceLine, ht]
  · simp [priceLine, hk, hpb k]

/-- Price lines are ordered by the changed price. -/
theorem priceLine_mono (pb : Fin L → ℝ) (l : Fin L) {s t : ℝ} (hst : s ≤ t) :
    priceLine pb l s ≤ priceLine pb l t := by
  intro k
  by_cases hk : k = l
  · subst hk; simp [priceLine, hst]
  · simp [priceLine, hk]

/-- The derivative of the price line. -/
theorem priceLine_hasDerivAt (pb : Fin L → ℝ) (l : Fin L) (t : ℝ) :
    HasDerivAt (priceLine pb l) (Pi.single l 1) t := by
  have heq : priceLine pb l = fun s => pb + (s - pb l) • (Pi.single l 1 : Fin L → ℝ) := by
    funext s
    funext k
    by_cases hk : k = l
    · subst hk; simp [priceLine]
    · simp [priceLine, hk]
  rw [heq]
  simpa using (((hasDerivAt_id t).sub_const (pb l)).smul_const
    (Pi.single l 1 : Fin L → ℝ)).const_add pb

/-- The Hicksian demand function induced by a demand selection lies in `h(p, ū)`. -/
theorem hicksianOf_mem {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w) {q : Fin L → ℝ}
    (hq : StrictlyPositive q) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) : hicksianOf u xs q ub ∈ hicksianDemand u q ub := by
  rw [equation_3_E_4_left hrep hu hlns hq hub hne]
  exact hxs q _ hq (expenditure_nonneg u hq ub)

/-- **Section 3.I** (MWG, p. 83). Along a price line, `e(·, ū)` has derivative `h_l(·, ū)`
(Shephard's lemma), the Hicksian demand curve is nonincreasing (compensated law of demand), and
`e(p̄_{-l}, b; ū) - e(p̄_{-l}, a; ū) = ∫_a^b h_l(t, p̄_{-l}, ū) dt` for `a, b > 0`. -/
theorem expenditure_line_integral {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    (∀ t, 0 < t → HasDerivAt (fun s => expenditure u (priceLine pb l s) ub)
      (hicksianOf u xs (priceLine pb l t) ub l) t) ∧
    AntitoneOn (fun t => hicksianOf u xs (priceLine pb l t) ub l) (Set.Ioi 0) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      expenditure u (priceLine pb l b) ub - expenditure u (priceLine pb l a) ub =
        ∫ t in a..b, hicksianOf u xs (priceLine pb l t) ub l := by
  have hmem : ∀ t, 0 < t → hicksianOf u xs (priceLine pb l t) ub ∈
      hicksianDemand u (priceLine pb l t) ub :=
    fun t ht => hicksianOf_mem hrep hu hlns hxs (priceLine_pos hpb l ht) hub hne
  have hd : ∀ t, 0 < t → HasDerivAt (fun s => expenditure u (priceLine pb l s) ub)
      (hicksianOf u xs (priceLine pb l t) ub l) t := by
    intro t ht
    have h1 := shephard_lemma hu hq (priceLine_pos hpb l ht) (hmem t ht)
    have := h1.comp_hasDerivAt t (priceLine_hasDerivAt pb l t)
    rw [dualityDotCLM_apply, dotProduct_single, mul_one] at this
    exact this
  have hanti : AntitoneOn (fun t => hicksianOf u xs (priceLine pb l t) ub l) (Set.Ioi 0) := by
    intro s hs t ht hst
    have hother : ∀ k, k ≠ l → priceLine pb l t k = priceLine pb l s k := fun k hk => by
      simp [priceLine, hk]
    have := compensated_own_price u hother (hmem s hs) (hmem t ht)
    have hl : ∀ t', priceLine pb l t' l = t' := fun t' => by simp [priceLine]
    rw [hl, hl] at this
    simp only
    rcases hst.lt_or_eq with hlt | heq
    · have hpos : 0 < t - s := sub_pos.mpr hlt
      by_contra hcon
      rw [not_le] at hcon
      nlinarith
    · subst heq; exact le_rfl
  refine ⟨hd, hanti, fun a b ha hb => ?_⟩
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := fun t ht =>
    lt_of_lt_of_le (lt_min ha hb) (Set.uIcc_subset_uIcc_left ht |> fun _ => ht.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht))
    ((hanti.mono hsub).intervalIntegrable)]

/-- **Equation (3.I.3)** (MWG, p. 83). If only the price of good `l` changes, from `a₀` to `a₁`,
`EV(p⁰, p¹, w) = ∫_{a₁}^{a₀} h_l(t, p̄_{-l}, u¹) dt`. -/
theorem equation_3_I_3 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w) :
    equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w =
      ∫ t in a₁..a₀, hicksianOf u xs (priceLine pb l t)
        (indirectUtility u (priceLine pb l a₁) w) l := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  rw [← (expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw)
    (welfare_v_attainable hu hp₁ hw.le)).2.2 a₁ a₀ ha₁ ha₀,
    equation_3_I_1 hrep hu hlns hp₀ hw.le, equation_3_E_1_left hrep hu hlns hp₁ hw.le]

/-- **Equation (3.I.4)** (MWG, p. 83). If only the price of good `l` changes, from `a₀` to `a₁`,
`CV(p⁰, p¹, w) = ∫_{a₁}^{a₀} h_l(t, p̄_{-l}, u⁰) dt`. -/
theorem equation_3_I_4 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w) :
    compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w =
      ∫ t in a₁..a₀, hicksianOf u xs (priceLine pb l t)
        (indirectUtility u (priceLine pb l a₀) w) l := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  rw [← (expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw)
    (welfare_v_attainable hu hp₀ hw.le)).2.2 a₁ a₀ ha₁ ha₀,
    equation_3_I_2 hrep hu hlns hp₁ hw.le, equation_3_E_1_left hrep hu hlns hp₀ hw.le]

/-- **Equation (3.I.8)** (MWG, p. 89). The area variation measure
`AV(p⁰, p¹, w) = ∫_{a₁}^{a₀} x_l(t, p̄_{-l}, w) dt` (only the price of good `l` changes). -/
noncomputable def areaVariation (xs : DemandFunction L) (pb : Fin L → ℝ) (l : Fin L)
    (a₀ a₁ w : ℝ) : ℝ :=
  ∫ t in a₁..a₀, xs (priceLine pb l t) w l

/-- The Hicksian demand curves compared with the Walrasian one on the segment between the two
prices (MWG, pp. 83, 89, Figure 3.I.3): at a price `t` between `a₀` and `a₁`, `e(t, u⁰)` and
`e(t, u¹)` lie on opposite sides of `w`. -/
theorem welfare_expenditure_sides {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {pb : Fin L → ℝ}
    (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w t : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hw : 0 ≤ w) :
    (a₁ ≤ t → t ≤ a₀ → expenditure u (priceLine pb l t)
        (indirectUtility u (priceLine pb l a₀) w) ≤ w ∧
      w ≤ expenditure u (priceLine pb l t) (indirectUtility u (priceLine pb l a₁) w)) ∧
    (a₀ ≤ t → t ≤ a₁ → w ≤ expenditure u (priceLine pb l t)
        (indirectUtility u (priceLine pb l a₀) w) ∧
      expenditure u (priceLine pb l t) (indirectUtility u (priceLine pb l a₁) w) ≤ w) := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  have e₀ := equation_3_E_1_left hrep hu hlns hp₀ hw
  have e₁ := equation_3_E_1_left hrep hu hlns hp₁ hw
  constructor
  · intro h1 h2
    have ht : 0 < t := ha₁.trans_le h1
    exact ⟨(proposition_3_E_2_ii_prices u (priceLine_pos hpb l ht)
        (priceLine_mono pb l h2) _).trans_eq e₀,
      e₁.symm.trans_le (proposition_3_E_2_ii_prices u hp₁ (priceLine_mono pb l h1) _)⟩
  · intro h1 h2
    have ht : 0 < t := ha₀.trans_le h1
    exact ⟨e₀.symm.trans_le (proposition_3_E_2_ii_prices u hp₀ (priceLine_mono pb l h1) _),
      (proposition_3_E_2_ii_prices u (priceLine_pos hpb l ht)
        (priceLine_mono pb l h2) _).trans_eq e₁⟩

/-- **Section 3.I** (MWG, pp. 83, 89, Figure 3.I.3). If good `l` is normal (`x_l(p, ·)`
nondecreasing in wealth along the price line), then `CV ≤ AV ≤ EV`, whether the price falls or
rises; in particular `EV ≥ CV`. -/
theorem normal_good_cv_le_av_le_ev {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w)
    (hnormal : ∀ t, 0 < t → MonotoneOn (fun w' => xs (priceLine pb l t) w' l) (Set.Ici 0))
    (hint : IntervalIntegrable (fun t => xs (priceLine pb l t) w l) volume a₁ a₀) :
    compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w ≤
        areaVariation xs pb l a₀ a₁ w ∧
      areaVariation xs pb l a₀ a₁ w ≤
        equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  set u₀ := indirectUtility u (priceLine pb l a₀) w
  set u₁ := indirectUtility u (priceLine pb l a₁) w
  obtain ⟨-, hanti₀, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw) (welfare_v_attainable hu hp₀ hw.le)
  obtain ⟨-, hanti₁, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw) (welfare_v_attainable hu hp₁ hw.le)
  have hsub : Set.uIcc a₁ a₀ ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha₁ ha₀) ht.1
  have hi₀ := (hanti₀.mono hsub).intervalIntegrable (μ := volume)
  have hi₁ := (hanti₁.mono hsub).intervalIntegrable (μ := volume)
  rw [equation_3_I_4 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw,
    equation_3_I_3 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw, areaVariation]
  have sides := fun t : ℝ => welfare_expenditure_sides hrep hu hlns hpb l (t := t) ha₀ ha₁ hw.le
  rcases le_total a₁ a₀ with h | h
  · have hcmp : ∀ t ∈ Set.Icc a₁ a₀, hicksianOf u xs (priceLine pb l t) u₀ l ≤
        xs (priceLine pb l t) w l ∧
        xs (priceLine pb l t) w l ≤ hicksianOf u xs (priceLine pb l t) u₁ l := by
      intro t ht
      have htp : 0 < t := ha₁.trans_le ht.1
      obtain ⟨s₀, s₁⟩ := (sides t).1 ht.1 ht.2
      exact ⟨hnormal t htp (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          (Set.mem_Ici.mpr hw.le) s₀,
        hnormal t htp (Set.mem_Ici.mpr hw.le) (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          s₁⟩
    exact ⟨intervalIntegral.integral_mono_on h hi₀ hint fun t ht => (hcmp t ht).1,
      intervalIntegral.integral_mono_on h hint hi₁ fun t ht => (hcmp t ht).2⟩
  · have hcmp : ∀ t ∈ Set.Icc a₀ a₁, hicksianOf u xs (priceLine pb l t) u₁ l ≤
        xs (priceLine pb l t) w l ∧
        xs (priceLine pb l t) w l ≤ hicksianOf u xs (priceLine pb l t) u₀ l := by
      intro t ht
      have htp : 0 < t := ha₀.trans_le ht.1
      obtain ⟨s₀, s₁⟩ := (sides t).2 ht.1 ht.2
      exact ⟨hnormal t htp (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          (Set.mem_Ici.mpr hw.le) s₁,
        hnormal t htp (Set.mem_Ici.mpr hw.le) (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          s₀⟩
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_symm a₀,
      intervalIntegral.integral_symm a₀]
    exact ⟨neg_le_neg (intervalIntegral.integral_mono_on h hint.symm hi₀.symm
        fun t ht => (hcmp t ht).2),
      neg_le_neg (intervalIntegral.integral_mono_on h hi₁.symm hint.symm
        fun t ht => (hcmp t ht).1)⟩

/-- **Section 3.I and Exercise 3.I.3** (MWG, pp. 83, 89, 102). If good `l` is inferior
(`x_l(p, ·)` nonincreasing in wealth along the price line), then `EV ≤ AV ≤ CV`, whether the
price falls or rises; in particular `CV ≥ EV` (correction D5 for the strict inequality). -/
theorem inferior_good_ev_le_av_le_cv {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w)
    (hinf : ∀ t, 0 < t → AntitoneOn (fun w' => xs (priceLine pb l t) w' l) (Set.Ici 0))
    (hint : IntervalIntegrable (fun t => xs (priceLine pb l t) w l) volume a₁ a₀) :
    equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w ≤
        areaVariation xs pb l a₀ a₁ w ∧
      areaVariation xs pb l a₀ a₁ w ≤
        compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  set u₀ := indirectUtility u (priceLine pb l a₀) w
  set u₁ := indirectUtility u (priceLine pb l a₁) w
  obtain ⟨-, hanti₀, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw) (welfare_v_attainable hu hp₀ hw.le)
  obtain ⟨-, hanti₁, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw) (welfare_v_attainable hu hp₁ hw.le)
  have hsub : Set.uIcc a₁ a₀ ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha₁ ha₀) ht.1
  have hi₀ := (hanti₀.mono hsub).intervalIntegrable (μ := volume)
  have hi₁ := (hanti₁.mono hsub).intervalIntegrable (μ := volume)
  rw [equation_3_I_4 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw,
    equation_3_I_3 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw, areaVariation]
  have sides := fun t : ℝ => welfare_expenditure_sides hrep hu hlns hpb l (t := t) ha₀ ha₁ hw.le
  rcases le_total a₁ a₀ with h | h
  · have hcmp : ∀ t ∈ Set.Icc a₁ a₀, hicksianOf u xs (priceLine pb l t) u₁ l ≤
        xs (priceLine pb l t) w l ∧
        xs (priceLine pb l t) w l ≤ hicksianOf u xs (priceLine pb l t) u₀ l := by
      intro t ht
      have htp : 0 < t := ha₁.trans_le ht.1
      obtain ⟨s₀, s₁⟩ := (sides t).1 ht.1 ht.2
      exact ⟨hinf t htp (Set.mem_Ici.mpr hw.le) (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          s₁,
        hinf t htp (expenditure_nonneg u (priceLine_pos hpb l htp) _) (Set.mem_Ici.mpr hw.le)
          s₀⟩
    exact ⟨intervalIntegral.integral_mono_on h hi₁ hint fun t ht => (hcmp t ht).1,
      intervalIntegral.integral_mono_on h hint hi₀ fun t ht => (hcmp t ht).2⟩
  · have hcmp : ∀ t ∈ Set.Icc a₀ a₁, hicksianOf u xs (priceLine pb l t) u₀ l ≤
        xs (priceLine pb l t) w l ∧
        xs (priceLine pb l t) w l ≤ hicksianOf u xs (priceLine pb l t) u₁ l := by
      intro t ht
      have htp : 0 < t := ha₀.trans_le ht.1
      obtain ⟨s₀, s₁⟩ := (sides t).2 ht.1 ht.2
      exact ⟨hinf t htp (Set.mem_Ici.mpr hw.le) (expenditure_nonneg u (priceLine_pos hpb l htp) _)
          s₀,
        hinf t htp (expenditure_nonneg u (priceLine_pos hpb l htp) _) (Set.mem_Ici.mpr hw.le)
          s₁⟩
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_symm a₀,
      intervalIntegral.integral_symm a₀]
    exact ⟨neg_le_neg (intervalIntegral.integral_mono_on h hint.symm hi₁.symm
        fun t ht => (hcmp t ht).2),
      neg_le_neg (intervalIntegral.integral_mono_on h hi₀.symm hint.symm
        fun t ht => (hcmp t ht).1)⟩

/-- **Section 3.I** (MWG, pp. 83, 89). With no wealth effect for good `l` along the price line
(e.g. quasilinear preferences with respect to another good), `h_l(p, u⁰) = x_l(p, w) =
h_l(p, u¹)`, so `CV = AV = EV`: the change in Marshallian consumer surplus. -/
theorem marshallian_surplus {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w)
    (hnone : ∀ t, 0 < t → ∀ w', 0 ≤ w' →
      xs (priceLine pb l t) w' l = xs (priceLine pb l t) w l) :
    compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w =
        areaVariation xs pb l a₀ a₁ w ∧
      equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w =
        areaVariation xs pb l a₀ a₁ w := by
  have hsub : Set.uIcc a₁ a₀ ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha₁ ha₀) ht.1
  rw [equation_3_I_4 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw,
    equation_3_I_3 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw, areaVariation]
  constructor <;>
  exact intervalIntegral.integral_congr fun t ht =>
    hnone t (hsub ht) _ (expenditure_nonneg u (priceLine_pos hpb l (hsub ht)) _)

/-- **Example 3.I.1** (MWG, pp. 84-85), equation (3.I.5). A tax `τ ≥ 0` on good `l` raises its
price from `a` to `a + τ`, with revenue `T = τ x_l(p¹, w)`. The deadweight loss
`(-T) - EV(p⁰, p¹, w) = w - T - e(p⁰, u¹)` equals
`∫_a^{a+τ} [h_l(s, p̄_{-l}, u¹) - h_l(a + τ, p̄_{-l}, u¹)] ds`; it is nonnegative, and positive when
`τ > 0` and `h_l(·, u¹)` is strictly decreasing on `[a, a + τ]`. -/
theorem example_3_I_1_u1 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a τ w : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) (hw : 0 < w) :
    let p₀ := priceLine pb l a
    let p₁ := priceLine pb l (a + τ)
    let u₁ := indirectUtility u p₁ w
    let T := τ * xs p₁ w l
    (-T - equivalentVariation u p₀ p₁ w = w - T - expenditure u p₀ u₁) ∧
      -T - equivalentVariation u p₀ p₁ w =
        ∫ s in a..a + τ, (hicksianOf u xs (priceLine pb l s) u₁ l -
          hicksianOf u xs (priceLine pb l (a + τ)) u₁ l) ∧
      0 ≤ -T - equivalentVariation u p₀ p₁ w ∧
      (0 < τ → StrictAntiOn (fun s => hicksianOf u xs (priceLine pb l s) u₁ l)
        (Set.Icc a (a + τ)) → 0 < -T - equivalentVariation u p₀ p₁ w) := by
  intro p₀ p₁ u₁ T
  have haτ : 0 < a + τ := by linarith
  have hp₀ := priceLine_pos hpb l ha
  have hp₁ := priceLine_pos hpb l haτ
  obtain ⟨-, hanti, hint⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw) (welfare_v_attainable hu hp₁ hw.le)
  have he₁ : expenditure u p₁ u₁ = w := equation_3_E_1_left hrep hu hlns hp₁ hw.le
  have hT : T = τ * hicksianOf u xs p₁ u₁ l := by
    simp only [T, hicksianOf, he₁]
  have hsub : Set.uIcc a (a + τ) ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha haτ) ht.1
  have hi := (hanti.mono hsub).intervalIntegrable (μ := volume)
  have hEV := equation_3_I_1 hrep hu hlns hp₀ hw.le (p₁ := p₁)
  have hkey : -T - equivalentVariation u p₀ p₁ w =
      ∫ s in a..a + τ, (hicksianOf u xs (priceLine pb l s) u₁ l -
        hicksianOf u xs (priceLine pb l (a + τ)) u₁ l) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
      ← hint a (a + τ) ha haτ, hEV, hT, smul_eq_mul]
    have : expenditure u (priceLine pb l (a + τ)) u₁ = w := he₁
    rw [this]
    ring
  refine ⟨by rw [hEV]; ring, hkey, ?_, fun hτ0 hstrict => ?_⟩
  · rw [hkey]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    have := hanti (hsub (Set.Icc_subset_uIcc hs)) (hsub (Set.right_mem_uIcc)) hs.2
    linarith
  · rw [hkey]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hi.sub intervalIntegrable_const)
      _ (by linarith)
    intro s hs
    have := hstrict (Set.Ioo_subset_Icc_self hs) (Set.right_mem_Icc.mpr (by linarith)) hs.2
    linarith

/-- **Example 3.I.1** (MWG, p. 85), equation (3.I.6). The deficit of a government that
compensates the consumer to her pretax utility `u⁰`, `-CV(p⁰, p¹, w) - τ h_l(p¹, u⁰)`, equals
`∫_a^{a+τ} [h_l(s, p̄_{-l}, u⁰) - h_l(a + τ, p̄_{-l}, u⁰)] ds`; it is nonnegative, and positive when
`τ > 0` and `h_l(·, u⁰)` is strictly decreasing on `[a, a + τ]`. (The first line of (3.I.6)
prints `th₁(p¹, u)` for `th₁(p¹, u⁰)`, correction D6.) -/
theorem example_3_I_1_u0 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a τ w : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) (hw : 0 < w) :
    let p₀ := priceLine pb l a
    let p₁ := priceLine pb l (a + τ)
    let u₀ := indirectUtility u p₀ w
    (-compensatingVariation u p₀ p₁ w - τ * hicksianOf u xs p₁ u₀ l =
        ∫ s in a..a + τ, (hicksianOf u xs (priceLine pb l s) u₀ l -
          hicksianOf u xs (priceLine pb l (a + τ)) u₀ l)) ∧
      0 ≤ -compensatingVariation u p₀ p₁ w - τ * hicksianOf u xs p₁ u₀ l ∧
      (0 < τ → StrictAntiOn (fun s => hicksianOf u xs (priceLine pb l s) u₀ l)
        (Set.Icc a (a + τ)) →
          0 < -compensatingVariation u p₀ p₁ w - τ * hicksianOf u xs p₁ u₀ l) := by
  intro p₀ p₁ u₀
  have haτ : 0 < a + τ := by linarith
  have hp₀ := priceLine_pos hpb l ha
  have hp₁ := priceLine_pos hpb l haτ
  obtain ⟨-, hanti, hint⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l
    (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw) (welfare_v_attainable hu hp₀ hw.le)
  have he₀ : expenditure u p₀ u₀ = w := equation_3_E_1_left hrep hu hlns hp₀ hw.le
  have hsub : Set.uIcc a (a + τ) ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha haτ) ht.1
  have hi := (hanti.mono hsub).intervalIntegrable (μ := volume)
  have hkey : -compensatingVariation u p₀ p₁ w - τ * hicksianOf u xs p₁ u₀ l =
      ∫ s in a..a + τ, (hicksianOf u xs (priceLine pb l s) u₀ l -
        hicksianOf u xs (priceLine pb l (a + τ)) u₀ l) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
      ← hint a (a + τ) ha haτ, equation_3_I_2 hrep hu hlns hp₁ hw.le, smul_eq_mul]
    have : expenditure u (priceLine pb l a) u₀ = w := he₀
    rw [this]
    ring
  refine ⟨hkey, ?_, fun hτ0 hstrict => ?_⟩
  · rw [hkey]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    have := hanti (hsub (Set.Icc_subset_uIcc hs)) (hsub (Set.right_mem_uIcc)) hs.2
    linarith
  · rw [hkey]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hi.sub intervalIntegrable_const)
      _ (by linarith)
    intro s hs
    have := hstrict (Set.Ioo_subset_Icc_self hs) (Set.right_mem_Icc.mpr (by linarith)) hs.2
    linarith

/-- **Exercise 3.I.2** (MWG, p. 86), at a fixed utility level `ū` (exactly (3.I.6); for (3.I.5)
with `u¹` held fixed). The deadweight loss `D(τ) = ∫_a^{a+τ} [h_l(s, ū) - h_l(a + τ, ū)] ds =
e(a + τ, ū) - e(a, ū) - τ h_l(a + τ, ū)` has derivative `-τ ∂h_l/∂p_l(a + τ, ū)` wherever the
Hicksian demand curve is differentiable; it is `0` at `τ = 0`, and `> 0` for `τ > 0` iff
`∂h_l/∂p_l(a + τ, ū) < 0` (correction D4: "strictly decreasing" is not enough). -/
theorem exercise_3_I_2 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {a τ g' : ℝ} (ha : 0 < a) (haτ : 0 < a + τ)
    (hg : HasDerivAt (fun s => hicksianOf u xs (priceLine pb l s) ub l) g' (a + τ)) :
    let D := fun τ' : ℝ => expenditure u (priceLine pb l (a + τ')) ub -
      expenditure u (priceLine pb l a) ub - τ' * hicksianOf u xs (priceLine pb l (a + τ')) ub l
    HasDerivAt D (-τ * g') τ ∧ g' ≤ 0 ∧ (0 < τ → (0 < -τ * g' ↔ g' < 0)) := by
  intro D
  obtain ⟨hd, hanti, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l hub hne
  have hshift : HasDerivAt (fun τ' : ℝ => a + τ') 1 τ := by
    simpa using (hasDerivAt_id τ).const_add a
  have h1 : HasDerivAt (fun τ' => expenditure u (priceLine pb l (a + τ')) ub)
      (hicksianOf u xs (priceLine pb l (a + τ)) ub l) τ := by
    have := (hd (a + τ) haτ).comp τ hshift
    rw [mul_one] at this
    exact this
  have h2 : HasDerivAt (fun τ' => hicksianOf u xs (priceLine pb l (a + τ')) ub l) g' τ := by
    have := hg.comp τ hshift
    rw [mul_one] at this
    exact this
  have h3 := (h1.sub_const (expenditure u (priceLine pb l a) ub)).sub
    ((hasDerivAt_id' τ).mul h2)
  have hg0 : g' ≤ 0 := by
    have hlim := hg.tendsto_slope_zero_right
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have := hanti (show a + τ ∈ Set.Ioi (0 : ℝ) from haτ)
      (show a + τ + t ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith) (by linarith)
    simp only [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le) (by linarith)
  refine ⟨?_, hg0, fun hτ => ⟨fun h => ?_, fun h => by nlinarith⟩⟩
  · exact h3.congr_deriv (by ring)
  · by_contra hcon
    rw [not_lt] at hcon
    nlinarith

/-- **Exercise 3.I.1** (MWG, p. 84). If the prices of two goods `l ≠ k` change (from `p⁰` to
`p¹`, all other prices fixed), the equivalent and compensating variations are sums of integrals
under Hicksian demand curves: changing `p_l` first (with `p_k = p⁰_k`) and then `p_k` (with
`p_l = p¹_l`), `EV = ∫_{p¹_l}^{p⁰_l} h_l(·, u¹) + ∫_{p¹_k}^{p⁰_k} h_k(·, u¹)` and likewise `CV` with
`u⁰`; with no wealth effects for either good, `CV = EV`. -/
theorem exercise_3_I_1 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ p₁ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {l k : Fin L}
    (hlk : l ≠ k) (hother : ∀ j, j ≠ l → j ≠ k → p₁ j = p₀ j) {w : ℝ} (hw : 0 < w) :
    let pm := priceLine p₀ l (p₁ l)
    (∀ ub, ub = indirectUtility u p₀ w ∨ ub = indirectUtility u p₁ w →
      expenditure u p₀ ub - expenditure u p₁ ub =
        (∫ t in p₁ l..p₀ l, hicksianOf u xs (priceLine p₀ l t) ub l) +
          ∫ t in p₁ k..p₀ k, hicksianOf u xs (priceLine pm k t) ub k) ∧
    equivalentVariation u p₀ p₁ w =
      (∫ t in p₁ l..p₀ l, hicksianOf u xs (priceLine p₀ l t) (indirectUtility u p₁ w) l) +
        ∫ t in p₁ k..p₀ k, hicksianOf u xs (priceLine pm k t) (indirectUtility u p₁ w) k ∧
    compensatingVariation u p₀ p₁ w =
      (∫ t in p₁ l..p₀ l, hicksianOf u xs (priceLine p₀ l t) (indirectUtility u p₀ w) l) +
        ∫ t in p₁ k..p₀ k, hicksianOf u xs (priceLine pm k t) (indirectUtility u p₀ w) k ∧
    ((∀ q, StrictlyPositive q → ∀ w₁ w₂, 0 ≤ w₁ → 0 ≤ w₂ →
        xs q w₁ l = xs q w₂ l ∧ xs q w₁ k = xs q w₂ k) →
      compensatingVariation u p₀ p₁ w = equivalentVariation u p₀ p₁ w) := by
  intro pm
  have hpm : StrictlyPositive pm := priceLine_pos hp₀ l (hp₁ l)
  have hpm_k : pm k = p₀ k := by simp [pm, priceLine, Ne.symm hlk]
  have hend₀ : priceLine pm k (p₀ k) = pm := by
    rw [← hpm_k]; simp [priceLine]
  have hend₁ : priceLine pm k (p₁ k) = p₁ := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [priceLine]
    · by_cases hj' : j = l
      · subst hj'; simp [priceLine, pm, hj]
      · simp [priceLine, pm, hj, hj', hother j hj' hj]
  have hstart : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  have hsplit : ∀ ub, u 0 < ub → (∃ x ∈ nonnegOrthant L, ub ≤ u x) →
      expenditure u p₀ ub - expenditure u p₁ ub =
        (∫ t in p₁ l..p₀ l, hicksianOf u xs (priceLine p₀ l t) ub l) +
          ∫ t in p₁ k..p₀ k, hicksianOf u xs (priceLine pm k t) ub k := by
    intro ub hub hne
    have i1 := (expenditure_line_integral hrep hu hlns hq hxs hp₀ l hub hne).2.2 (p₁ l) (p₀ l)
      (hp₁ l) (hp₀ l)
    have i2 := (expenditure_line_integral hrep hu hlns hq hxs hpm k hub hne).2.2 (p₁ k) (p₀ k)
      (hp₁ k) (hp₀ k)
    rw [hstart] at i1
    rw [hend₀, hend₁] at i2
    rw [← i1, ← i2]
    simp only [pm]
    ring
  have hall : ∀ ub, ub = indirectUtility u p₀ w ∨ ub = indirectUtility u p₁ w →
      expenditure u p₀ ub - expenditure u p₁ ub =
        (∫ t in p₁ l..p₀ l, hicksianOf u xs (priceLine p₀ l t) ub l) +
          ∫ t in p₁ k..p₀ k, hicksianOf u xs (priceLine pm k t) ub k := by
    rintro ub (rfl | rfl)
    · exact hsplit _ (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw)
        (welfare_v_attainable hu hp₀ hw.le)
    · exact hsplit _ (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw)
        (welfare_v_attainable hu hp₁ hw.le)
  have hEV : equivalentVariation u p₀ p₁ w =
      expenditure u p₀ (indirectUtility u p₁ w) - expenditure u p₁ (indirectUtility u p₁ w) := by
    rw [equation_3_I_1 hrep hu hlns hp₀ hw.le, equation_3_E_1_left hrep hu hlns hp₁ hw.le]
  have hCV : compensatingVariation u p₀ p₁ w =
      expenditure u p₀ (indirectUtility u p₀ w) - expenditure u p₁ (indirectUtility u p₀ w) := by
    rw [equation_3_I_2 hrep hu hlns hp₁ hw.le, equation_3_E_1_left hrep hu hlns hp₀ hw.le]
  refine ⟨hall, hEV.trans (hall _ (Or.inr rfl)), hCV.trans (hall _ (Or.inl rfl)), fun hnw => ?_⟩
  rw [hCV, hEV, hall _ (Or.inl rfl), hall _ (Or.inr rfl)]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    have htp : 0 < t := lt_of_lt_of_le (lt_min (hp₁ l) (hp₀ l)) ht.1
    exact (hnw _ (priceLine_pos hp₀ l htp) _ _ (expenditure_nonneg u (priceLine_pos hp₀ l htp) _)
      (expenditure_nonneg u (priceLine_pos hp₀ l htp) _)).1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    have htp : 0 < t := lt_of_lt_of_le (lt_min (hp₁ k) (hp₀ k)) ht.1
    exact (hnw _ (priceLine_pos hpm k htp) _ _ (expenditure_nonneg u (priceLine_pos hpm k htp) _)
      (expenditure_nonneg u (priceLine_pos hpm k htp) _)).2

end MWG.ClassicalDemand
