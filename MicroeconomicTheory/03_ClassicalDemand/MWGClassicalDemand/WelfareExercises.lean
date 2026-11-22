/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Welfare evaluation: Exercises 3.I.3, 3.I.4, 3.I.5 and 3.I.10

MWG, Exercises 3.I.3-3.I.5 and 3.I.10 (pp. 102-103).

* Exercise 3.I.3: for a fall in the price of an inferior good, `CV ≥ EV`; strictly if the good is
  strictly inferior, the price falls strictly and the good is consumed. As printed ("`p¹ ≤ p⁰`,
  `CV > EV`") it fails for `p¹ = p⁰` (correction D5).
* Exercise 3.I.4: with the utility `u(x) = min(x₁ + 1, x₂)` (non-homothetic and not quasilinear),
  `p⁰ = (10, 2)`, `p^A = (1, 3/2)`, `p^B = (5, 1)`, `w = 2`, the consumer prefers `p^A`, but
  `CV(p⁰, p^A, w) < CV(p⁰, p^B, w)`.
* Exercise 3.I.5: with a quasilinear utility (numeraire price 1) on the quasilinear consumption
  set, `CV = EV` for all `(p⁰, p¹, w)`.
* Exercise 3.I.10: for the same utility, `p⁰ = (1, 1)`, `p¹ = (2, 1/2)`, `w = 3`, the consumer is
  indifferent, but the area variation computed along the path that changes `p₁` first is
  `5 log(6/5) - 2 log(3/2) > 0`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology MeasureTheory

variable {L : ℕ}

/-- **Exercise 3.I.3** (MWG, p. 102), corrected (correction D5). If only the price of good `l`
falls (`a₁ ≤ a₀`) and good `l` is inferior along the price line, then `CV ≥ EV`. If moreover
`a₁ < a₀`, good `l` is consumed at `(p⁰, w)` and strictly inferior, then `CV > EV`. -/
theorem exercise_3_I_3 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) (l : Fin L) {a₀ a₁ w : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hw : 0 < w) (hfall : a₁ ≤ a₀)
    (hinf : ∀ t, 0 < t → AntitoneOn (fun w' => xs (priceLine pb l t) w' l) (Set.Ici 0)) :
    equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w ≤
        compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w ∧
      (a₁ < a₀ → 0 < xs (priceLine pb l a₀) w l →
        (∀ t, 0 < t → StrictAntiOn (fun w' => xs (priceLine pb l t) w' l) (Set.Ici 0)) →
        equivalentVariation u (priceLine pb l a₀) (priceLine pb l a₁) w <
          compensatingVariation u (priceLine pb l a₀) (priceLine pb l a₁) w) := by
  have hp₀ := priceLine_pos hpb l ha₀
  have hp₁ := priceLine_pos hpb l ha₁
  set u₀ := indirectUtility u (priceLine pb l a₀) w
  set u₁ := indirectUtility u (priceLine pb l a₁) w
  have h0 := relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw
  have h1 := relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw
  have n0 := welfare_v_attainable hu hp₀ hw.le
  have n1 := welfare_v_attainable hu hp₁ hw.le
  obtain ⟨-, hanti₀, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l h0 n0
  obtain ⟨-, hanti₁, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hpb l h1 n1
  have hsub : Set.uIcc a₁ a₀ ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le (lt_min ha₁ ha₀) ht.1
  have hi₀ := (hanti₀.mono hsub).intervalIntegrable (μ := volume)
  have hi₁ := (hanti₁.mono hsub).intervalIntegrable (μ := volume)
  have hsides := fun t : ℝ => welfare_expenditure_sides hrep hu hlns hpb l (t := t) ha₀ ha₁ hw.le
  rw [equation_3_I_3 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw,
    equation_3_I_4 hrep hu hlns hq hxs hpb l ha₀ ha₁ hw]
  refine ⟨intervalIntegral.integral_mono_on hfall hi₁ hi₀ fun t ht => ?_,
    fun hlt hcons hstrict => ?_⟩
  · have htp : 0 < t := ha₁.trans_le ht.1
    obtain ⟨s₀, s₁⟩ := (hsides t).1 ht.1 ht.2
    exact (hinf t htp (Set.mem_Ici.mpr hw.le) (expenditure_nonneg u (priceLine_pos hpb l htp) _)
      s₁).trans (hinf t htp (expenditure_nonneg u (priceLine_pos hpb l htp) _)
      (Set.mem_Ici.mpr hw.le) s₀)
  · -- the consumer is strictly better off after the fall (Proposition 3.I.1)
    have hbetter : u₀ < u₁ := by
      apply proposition_3_I_1 hrep hu hlns hp₁ (hxs _ w hp₀ hw.le)
      have : priceLine pb l a₁ - priceLine pb l a₀ = (a₁ - a₀) • Pi.single l 1 := by
        funext k
        by_cases hk : k = l
        · subst hk; simp [priceLine]
        · simp [priceLine, hk]
      rw [this, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
      exact mul_neg_of_neg_of_pos (by linarith) hcons
    rw [← sub_pos, ← intervalIntegral.integral_sub hi₀ hi₁]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hi₀.sub hi₁) _ hlt
    intro t ht
    have htp : 0 < t := ha₁.trans ht.1
    have hqt := priceLine_pos hpb l htp
    have hlt' : expenditure u (priceLine pb l t) u₀ < expenditure u (priceLine pb l t) u₁ :=
      (welfare_e_lt_iff hu hqt h0 h1 n0 n1).mpr hbetter
    have := hstrict t htp (expenditure_nonneg u hqt _) (expenditure_nonneg u hqt _) hlt'
    simp only [hicksianOf]
    linarith

/-- **Exercise 3.I.3** (MWG, p. 102), as printed, is false (correction D5): for `p¹ = p⁰` (allowed
by `p¹ ≤ p⁰`) both variations vanish, so `CV > EV` fails for every consumer. -/
theorem exercise_3_I_3_printed_counterexample (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) :
    ¬ equivalentVariation u p p w < compensatingVariation u p p w := by
  simp [equivalentVariation, compensatingVariation]

/-- The utility `u(x) = min(x₁ + 1, x₂)` on `ℝ²` (used in Exercises 3.I.4 and 3.I.10). -/
noncomputable def shiftLeontief (x : Fin 2 → ℝ) : ℝ := min (x 0 + 1) (x 1)

/-- `min(x₁ + 1, x₂)` is continuous. -/
theorem shiftLeontief_continuous : Continuous shiftLeontief := by
  unfold shiftLeontief; fun_prop

/-- `min(x₁ + 1, x₂)` is locally nonsatiated on `ℝ²_+`. -/
theorem shiftLeontief_lns : LocallyNonsatiated (nonnegOrthant 2) (utilityPref shiftLeontief) := by
  intro x hx ε hε
  refine ⟨x + fun _ => ε / 2, fun l => by simp only [Pi.add_apply]; linarith [hx l], ?_, ?_⟩
  · rw [euclidDist_add_const, abs_of_pos (by linarith)]
    have h2 : Real.sqrt (2 : ℕ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ ε / 2)
    linarith
  · have hlt : shiftLeontief x < shiftLeontief (x + fun _ => ε / 2) := by
      simp only [shiftLeontief, Pi.add_apply]
      rcases le_total (x 0 + 1) (x 1) with h | h
      · rw [min_eq_left h, lt_min_iff]; constructor <;> linarith
      · rw [min_eq_right h, lt_min_iff]; constructor <;> linarith
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- For `ū ≥ 1` and `p ≫ 0`, the expenditure function of `min(x₁ + 1, x₂)` is
`e(p, ū) = p₁(ū - 1) + p₂ū`, attained at `(ū - 1, ū)`. -/
theorem shiftLeontief_expenditure {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {ub : ℝ}
    (hub : 1 ≤ ub) : expenditure shiftLeontief p ub = p 0 * (ub - 1) + p 1 * ub := by
  have hmem : (![ub - 1, ub] : Fin 2 → ℝ) ∈ hicksianDemand shiftLeontief p ub := by
    refine ⟨⟨fun i => by fin_cases i <;> simp <;> linarith, by simp [shiftLeontief]⟩,
      fun y hy => ?_⟩
    have h1 : ub ≤ y 0 + 1 := hy.2.trans (min_le_left _ _)
    have h2 : ub ≤ y 1 := hy.2.trans (min_le_right _ _)
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    nlinarith [hp 0, hp 1]
  rw [expenditure_eq_of_mem hmem]
  simp [dotProduct, Fin.sum_univ_two]

/-- For `p ≫ 0` and `1 ≤ ū`, the indirect utility of `min(x₁ + 1, x₂)` at wealth
`p₁(ū - 1) + p₂ū` is `ū`. -/
theorem shiftLeontief_indirect {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : 1 ≤ ub) :
    indirectUtility shiftLeontief p (p 0 * (ub - 1) + p 1 * ub) = ub := by
  rw [← shiftLeontief_expenditure hp hub]
  refine equation_3_E_1_right shiftLeontief_continuous.continuousOn hp
    (by simp [shiftLeontief]; linarith) ⟨![ub - 1, ub], ?_, by simp [shiftLeontief]⟩
  intro i; fin_cases i <;> simp <;> linarith

/-- **Exercise 3.I.4** (MWG, p. 102). Comparing compensating variations need not rank new price
vectors correctly: for `u(x) = min(x₁ + 1, x₂)`, `w = 2`, `p⁰ = (10, 2)`, `p^A = (1, 3/2)`,
`p^B = (5, 1)`, the consumer strictly prefers `p^A` (`v = 6/5 > 7/6`), but
`CV(p⁰, p^A, w) = 1/2 < 1 = CV(p⁰, p^B, w)`. -/
theorem exercise_3_I_4 :
    indirectUtility shiftLeontief ![1, 3 / 2] 2 = 6 / 5 ∧
      indirectUtility shiftLeontief ![5, 1] 2 = 7 / 6 ∧
      indirectUtility shiftLeontief ![5, 1] 2 < indirectUtility shiftLeontief ![1, 3 / 2] 2 ∧
      compensatingVariation shiftLeontief ![10, 2] ![1, 3 / 2] 2 = 1 / 2 ∧
      compensatingVariation shiftLeontief ![10, 2] ![5, 1] 2 = 1 ∧
      compensatingVariation shiftLeontief ![10, 2] ![1, 3 / 2] 2 <
        compensatingVariation shiftLeontief ![10, 2] ![5, 1] 2 := by
  have hpA : StrictlyPositive (![1, 3 / 2] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have hpB : StrictlyPositive (![5, 1] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have hp0 : StrictlyPositive (![10, 2] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have vA : indirectUtility shiftLeontief ![1, 3 / 2] 2 = 6 / 5 := by
    have := shiftLeontief_indirect hpA (ub := 6 / 5) (by norm_num)
    norm_num at this ⊢
    exact this
  have vB : indirectUtility shiftLeontief ![5, 1] 2 = 7 / 6 := by
    have := shiftLeontief_indirect hpB (ub := 7 / 6) (by norm_num)
    norm_num at this ⊢
    exact this
  have v0 : indirectUtility shiftLeontief ![10, 2] 2 = 1 := by
    have := shiftLeontief_indirect hp0 (ub := 1) le_rfl
    norm_num at this ⊢
    exact this
  have hcv : ∀ q : Fin 2 → ℝ, StrictlyPositive q →
      compensatingVariation shiftLeontief ![10, 2] q 2 = 2 - q 1 := by
    intro q hq
    rw [equation_3_I_2 (representsOn_utilityPref _ _) shiftLeontief_continuous.continuousOn
      shiftLeontief_lns hq (by norm_num), v0, shiftLeontief_expenditure hq le_rfl]
    ring
  refine ⟨vA, vB, by rw [vA, vB]; norm_num, ?_, ?_, ?_⟩
  · rw [hcv _ hpA]; norm_num
  · rw [hcv _ hpB]; norm_num
  · rw [hcv _ hpA, hcv _ hpB]; norm_num

/-- The expenditure function on a general consumption set `X`:
`inf {p·x : x ∈ X, u(x) ≥ ū}`. -/
noncomputable def expenditureOn (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ)
    (p : Fin L → ℝ) (ub : ℝ) : ℝ :=
  supportFn {x | x ∈ X ∧ ub ≤ u x} p

/-- **Exercise 3.I.5** (MWG, p. 102), the key step. For a utility quasilinear with respect to
good `k` on the quasilinear consumption set (`u(x + c e_k) = u(x) + c`) and `p_k = 1`, the
expenditure function is a translation in `ū`: `e(p, ū + c) = e(p, ū) + c`, whenever the
expenditure-minimization values at `ū` are bounded below. -/
theorem expenditureOn_quasilinear_add {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    (hql : ∀ x ∈ quasilinearDomain k, ∀ c : ℝ, u (x + c • unitVec k) = u x + c)
    {p : Fin L → ℝ} (hpk : p k = 1) (ub c : ℝ)
    (hbdd : BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ quasilinearDomain k ∧ ub ≤ u x})) :
    expenditureOn (quasilinearDomain k) u p (ub + c) =
      expenditureOn (quasilinearDomain k) u p ub + c := by
  set S := {x | x ∈ quasilinearDomain k ∧ ub ≤ u x} with hS
  set S' := {x | x ∈ quasilinearDomain k ∧ ub + c ≤ u x} with hS'
  have hdom : ∀ x ∈ quasilinearDomain k, ∀ d : ℝ, x + d • unitVec k ∈ quasilinearDomain k := by
    intro x hx d l hl
    simp [unitVec, hl, hx l hl]
  have hpe : ∀ x d, p ⬝ᵥ (x + d • unitVec k) = p ⬝ᵥ x + d := by
    intro x d
    rw [dotProduct_add, dotProduct_smul, unitVec, dotProduct_single, hpk]
    simp
  have himg : (fun x => p ⬝ᵥ x) '' S' = (fun y => y + c) '' ((fun x => p ⬝ᵥ x) '' S) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hux⟩, rfl⟩
      refine ⟨p ⬝ᵥ (x + (-c) • unitVec k), ⟨x + (-c) • unitVec k, ⟨hdom x hx (-c), ?_⟩, rfl⟩,
        by rw [hpe]; ring⟩
      rw [hql x hx]; linarith
    · rintro ⟨_, ⟨x, ⟨hx, hux⟩, rfl⟩, rfl⟩
      refine ⟨x + c • unitVec k, ⟨hdom x hx c, ?_⟩, hpe x c⟩
      rw [hql x hx]; linarith
  have hne : ((fun x => p ⬝ᵥ x) '' S).Nonempty := by
    refine ⟨_, (0 : Fin L → ℝ) + (ub - u 0) • unitVec k, ⟨hdom 0 (fun l _ => le_rfl) _, ?_⟩, rfl⟩
    rw [hql 0 (fun l _ => le_rfl)]; linarith
  have goal : sInf ((fun x => p ⬝ᵥ x) '' S') = sInf ((fun x => p ⬝ᵥ x) '' S) + c := by
    rw [himg]
    obtain ⟨m, hm⟩ := hbdd
    apply le_antisymm
    · rw [← sub_le_iff_le_add]
      apply le_csInf hne
      intro y hy
      rw [sub_le_iff_le_add]
      exact csInf_le ⟨m + c, by rintro _ ⟨z, hz, rfl⟩; linarith [hm hz]⟩ ⟨y, hy, rfl⟩
    · apply le_csInf (hne.image _)
      rintro _ ⟨y, hy, rfl⟩
      linarith [csInf_le ⟨m, hm⟩ hy]
  exact goal

/-- **Exercise 3.I.5** (MWG, p. 102). If `u` is quasilinear with respect to good `k` (on the
quasilinear consumption set, with `p_k = 1` at both price vectors), then `CV(p⁰, p¹, w) =
EV(p⁰, p¹, w)` for every `(p⁰, p¹, w)`, for the variations defined from the expenditure function
and the indirect utility on that consumption set (assuming the expenditure minimization is
bounded below at `p⁰` and `p¹`). -/
theorem exercise_3_I_5 {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    (hql : ∀ x ∈ quasilinearDomain k, ∀ c : ℝ, u (x + c • unitVec k) = u x + c)
    {p₀ p₁ : Fin L → ℝ} (hp₀ : p₀ k = 1) (hp₁ : p₁ k = 1)
    (hb₀ : ∀ ub, BddBelow ((fun x => p₀ ⬝ᵥ x) '' {x | x ∈ quasilinearDomain k ∧ ub ≤ u x}))
    (hb₁ : ∀ ub, BddBelow ((fun x => p₁ ⬝ᵥ x) '' {x | x ∈ quasilinearDomain k ∧ ub ≤ u x}))
    (w : ℝ) :
    let X := quasilinearDomain k
    let u₀ := indirectUtilityOn X u p₀ w
    let u₁ := indirectUtilityOn X u p₁ w
    expenditureOn X u p₁ u₁ - expenditureOn X u p₁ u₀ =
      expenditureOn X u p₀ u₁ - expenditureOn X u p₀ u₀ := by
  intro X u₀ u₁
  have h : ∀ q : Fin L → ℝ, q k = 1 →
      (∀ ub, BddBelow ((fun x => q ⬝ᵥ x) '' {x | x ∈ quasilinearDomain k ∧ ub ≤ u x})) →
      expenditureOn X u q u₁ - expenditureOn X u q u₀ = u₁ - u₀ := by
    intro q hq hb
    have := expenditureOn_quasilinear_add hql hq u₀ (u₁ - u₀) (hb u₀)
    rw [add_sub_cancel] at this
    rw [this]
    ring
  rw [h p₁ hp₁ hb₁, h p₀ hp₀ hb₀]

/-- The Walrasian demand of `min(x₁ + 1, x₂)` when `w ≥ p₂`:
`x = ((w - p₂)/(p₁ + p₂), (w + p₁)/(p₁ + p₂))`. -/
noncomputable def shiftLeontiefDemand (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![(w - p 1) / (p 0 + p 1), (w + p 0) / (p 0 + p 1)]

/-- For `p ≫ 0` and `w ≥ p₂`, the Walrasian demand of `min(x₁ + 1, x₂)` is the single bundle
`((w - p₂)/(p₁ + p₂), (w + p₁)/(p₁ + p₂))`. -/
theorem shiftLeontief_walrasianDemand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : p 1 ≤ w) : walrasianDemand shiftLeontief p w = {shiftLeontiefDemand p w} := by
  have hs : 0 < p 0 + p 1 := add_pos (hp 0) (hp 1)
  set v := (w + p 0) / (p 0 + p 1) with hv
  have hx0 : (w - p 1) / (p 0 + p 1) = v - 1 := by
    rw [hv]; field_simp; ring
  have hcost : p 0 * (v - 1) + p 1 * v = w := by
    rw [hv]; field_simp; ring
  have hv1 : 1 ≤ v := by rw [hv, le_div_iff₀ hs]; linarith
  have hdem : shiftLeontiefDemand p w = ![v - 1, v] := by
    simp [shiftLeontiefDemand, hx0, hv]
  -- the bound on utility in the budget set
  have hbound : ∀ y ∈ budgetSet p w, shiftLeontief y ≤ v := by
    intro y hy
    by_contra hc
    rw [not_le] at hc
    have h1 : v < y 0 + 1 := hc.trans_le (min_le_left _ _)
    have h2 : v < y 1 := hc.trans_le (min_le_right _ _)
    have := hy.2
    simp only [dotProduct, Fin.sum_univ_two] at this
    nlinarith [hp 0, hp 1]
  rw [hdem]
  ext y
  constructor
  · rintro ⟨hy, hmax⟩
    have hle := hmax ![v - 1, v] ⟨fun i => by fin_cases i <;> simp <;> linarith,
      by simp [dotProduct, Fin.sum_univ_two]; linarith⟩
    have hu : v ≤ shiftLeontief y := by simpa [shiftLeontief] using hle
    have h1 : v - 1 ≤ y 0 := by linarith [hu.trans (min_le_left _ _)]
    have h2 : v ≤ y 1 := hu.trans (min_le_right _ _)
    have hb := hy.2
    simp only [dotProduct, Fin.sum_univ_two] at hb
    have e0 : y 0 = v - 1 := by nlinarith [hp 0, hp 1]
    have e1 : y 1 = v := by nlinarith [hp 0, hp 1]
    ext i; fin_cases i <;> simp [e0, e1]
  · rintro rfl
    refine ⟨⟨fun i => by fin_cases i <;> simp <;> linarith, ?_⟩, fun y hy => ?_⟩
    · simp [dotProduct, Fin.sum_univ_two]; linarith
    · have := hbound y hy
      simpa [shiftLeontief] using this

/-- The area variation of a change of both prices of `ℝ²`, along the path that changes `p₁`
first (Exercise 3.I.1 with Walrasian demand): `∫_{p¹₁}^{p⁰₁} x₁(t, p⁰₂, w) dt +
∫_{p¹₂}^{p⁰₂} x₂(p¹₁, t, w) dt`. -/
noncomputable def areaVariationTwo (xs : DemandFunction 2) (p₀ p₁ : Fin 2 → ℝ) (w : ℝ) : ℝ :=
  (∫ t in p₁ 0..p₀ 0, xs ![t, p₀ 1] w 0) + ∫ t in p₁ 1..p₀ 1, xs ![p₁ 0, t] w 1

/-- **Exercise 3.I.10** (MWG, p. 103). The area variation measure can rank `p⁰` and `p¹`
incorrectly when two prices change. For `u(x) = min(x₁ + 1, x₂)`, `w = 3`, `p⁰ = (1, 1)`,
`p¹ = (2, 1/2)`, the consumer is indifferent (`v(p⁰, 3) = v(p¹, 3) = 2`), but the area variation
computed from her Walrasian demand along the path changing `p₁` first is
`5 log(6/5) - 2 log(3/2) > 0`, indicating a strict improvement. -/
theorem exercise_3_I_10 :
    indirectUtility shiftLeontief ![1, 1] 3 = 2 ∧ indirectUtility shiftLeontief ![2, 1 / 2] 3 = 2 ∧
      areaVariationTwo shiftLeontiefDemand ![1, 1] ![2, 1 / 2] 3 =
        5 * Real.log (6 / 5) - 2 * Real.log (3 / 2) ∧
      0 < areaVariationTwo shiftLeontiefDemand ![1, 1] ![2, 1 / 2] 3 := by
  have hp0 : StrictlyPositive (![1, 1] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have hp1 : StrictlyPositive (![2, 1 / 2] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have v0 : indirectUtility shiftLeontief ![1, 1] 3 = 2 := by
    have := shiftLeontief_indirect hp0 (ub := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have v1 : indirectUtility shiftLeontief ![2, 1 / 2] 3 = 2 := by
    have := shiftLeontief_indirect hp1 (ub := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have i1 : (∫ t in (2 : ℝ)..1, shiftLeontiefDemand ![t, 1] 3 0) = -(2 * Real.log (3 / 2)) := by
    have hcongr : Set.EqOn (fun t => shiftLeontiefDemand ![t, 1] 3 0)
        (fun t => 2 * (t + 1)⁻¹) (Set.uIcc 2 1) := by
      intro t _
      simp [shiftLeontiefDemand]
      norm_num
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun t => t⁻¹),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    have : Real.log ((1 + 1) / (2 + 1)) = -Real.log (3 / 2) := by
      rw [← Real.log_inv]; norm_num
    rw [this]
    ring
  have i2 : (∫ t in (1 / 2 : ℝ)..1, shiftLeontiefDemand ![2, t] 3 1) = 5 * Real.log (6 / 5) := by
    have hcongr : Set.EqOn (fun t => shiftLeontiefDemand ![2, t] 3 1)
        (fun t => 5 * (t + 2)⁻¹) (Set.uIcc (1 / 2) 1) := by
      intro t _
      simp [shiftLeontiefDemand]
      norm_num
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun t => t⁻¹),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have hav : areaVariationTwo shiftLeontiefDemand ![1, 1] ![2, 1 / 2] 3 =
      5 * Real.log (6 / 5) - 2 * Real.log (3 / 2) := by
    simp only [areaVariationTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [i1, i2]
    ring
  refine ⟨v0, v1, hav, ?_⟩
  have h2 : (2 : ℝ) * Real.log (3 / 2) = Real.log ((3 / 2) ^ 2) := by
    rw [Real.log_pow]; norm_num
  have h5 : (5 : ℝ) * Real.log (6 / 5) = Real.log ((6 / 5) ^ 5) := by
    rw [Real.log_pow]; norm_num
  rw [hav, sub_pos, h2, h5]
  exact Real.log_lt_log (by norm_num) (by norm_num)

end MWG.ClassicalDemand
