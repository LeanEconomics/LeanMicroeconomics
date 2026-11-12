/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityBasic

/-!
# Welfare evaluation of economic changes: money metric, EV and CV

MWG, Section 3.I, pp. 80-88, and Exercises 3.I.6, 3.I.11, 3.I.12 (pp. 102-104).

The consumer has a utility `u`, continuous on `ℝ^L_+`, representing a locally nonsatiated `≿`;
`e` and `v` are the expenditure and indirect utility functions of parts A-B, wealth is `w > 0`.

* The money metric indirect utility `e(p̄, v(p, w))` (`moneyMetric`) is an indirect utility
  function for `≿` (`moneyMetric_le_iff`) that does not depend on the representation
  (footnote 21, `footnote_3_I_21`).
* The equivalent and compensating variations (3.I.1)-(3.I.2), their indirect-utility forms
  `v(p⁰, w + EV) = u¹`, `v(p¹, w - CV) = u⁰` (footnote 22), the correct welfare ranking (p. 82),
  the comparison of several price vectors with EV and CV (p. 86, footnote 24).
* Proposition 3.I.1 (the partial-information test), the nonpositive second-order remainder of
  (3.I.7), and Proposition 3.I.2 (the reverse test for small changes; correction D3).
* Exercise 3.I.6 (compensation of several consumers), 3.I.11 (the test at `p¹`) and 3.I.12
  (changes in prices and wealth).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Section 3.I** (MWG, p. 81). The money metric indirect utility function
`(p, w) ↦ e(p̄, v(p, w))` with base prices `p̄`. -/
noncomputable def moneyMetric (u : (Fin L → ℝ) → ℝ) (pb p : Fin L → ℝ) (w : ℝ) : ℝ :=
  expenditure u pb (indirectUtility u p w)

/-- **Equation (3.I.1)** (MWG, p. 82). The equivalent variation
`EV(p⁰, p¹, w) = e(p⁰, u¹) - e(p⁰, u⁰)`, `uⁱ = v(pⁱ, w)`. -/
noncomputable def equivalentVariation (u : (Fin L → ℝ) → ℝ) (p₀ p₁ : Fin L → ℝ) (w : ℝ) : ℝ :=
  expenditure u p₀ (indirectUtility u p₁ w) - expenditure u p₀ (indirectUtility u p₀ w)

/-- **Equation (3.I.2)** (MWG, p. 82). The compensating variation
`CV(p⁰, p¹, w) = e(p¹, u¹) - e(p¹, u⁰)`. -/
noncomputable def compensatingVariation (u : (Fin L → ℝ) → ℝ) (p₀ p₁ : Fin L → ℝ) (w : ℝ) :
    ℝ :=
  expenditure u p₁ (indirectUtility u p₁ w) - expenditure u p₁ (indirectUtility u p₀ w)

/-- The utility level `v(p, w)` is attained in `ℝ^L_+` (by the demanded bundle). -/
theorem welfare_v_attainable {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    ∃ x ∈ nonnegOrthant L, indirectUtility u p w ≤ u x := by
  obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hw
  exact ⟨x, hx.1.1, (indirectUtility_eq_of_mem hx).le⟩

/-- For attainable utility levels above `u(0)`, `e(p̄, ·)` is strictly increasing:
`e(p̄, a) < e(p̄, b) ⟺ a < b` (Proposition 3.E.2(ii)). -/
theorem welfare_e_lt_iff {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) {a b : ℝ} (ha : u 0 < a) (hb : u 0 < b)
    (hna : ∃ x ∈ nonnegOrthant L, a ≤ u x) (hnb : ∃ x ∈ nonnegOrthant L, b ≤ u x) :
    expenditure u pb a < expenditure u pb b ↔ a < b := by
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd h (not_lt.mpr (proposition_3_E_2_ii_utility hu hpb hb hlt hna).le)
    · rw [heq] at h
      exact lt_irrefl _ h
  · exact fun h => proposition_3_E_2_ii_utility hu hpb ha h hnb

/-- The weak form: `e(p̄, a) ≤ e(p̄, b) ⟺ a ≤ b`. -/
theorem welfare_e_le_iff {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {pb : Fin L → ℝ} (hpb : StrictlyPositive pb) {a b : ℝ} (ha : u 0 < a) (hb : u 0 < b)
    (hna : ∃ x ∈ nonnegOrthant L, a ≤ u x) (hnb : ∃ x ∈ nonnegOrthant L, b ≤ u x) :
    expenditure u pb a ≤ expenditure u pb b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, welfare_e_lt_iff hu hpb hb ha hnb hna]

/-- **Section 3.I** (MWG, p. 81, Figure 3.I.1). The money metric is an indirect utility function
for `≿`: for `p̄, p, p' ≫ 0` and `w, w' > 0`,
`e(p̄, v(p, w)) ≤ e(p̄, v(p', w')) ⟺ v(p, w) ≤ v(p', w')`. -/
theorem moneyMetric_le_iff {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {pb p p' : Fin L → ℝ}
    (hpb : StrictlyPositive pb) (hp : StrictlyPositive p) (hp' : StrictlyPositive p') {w w' : ℝ}
    (hw : 0 < w) (hw' : 0 < w') :
    moneyMetric u pb p w ≤ moneyMetric u pb p' w' ↔
      indirectUtility u p w ≤ indirectUtility u p' w' :=
  welfare_e_le_iff hu hpb (relations_indirectUtility_gt_zero hrep hu hlns hp hw)
    (relations_indirectUtility_gt_zero hrep hu hlns hp' hw') (welfare_v_attainable hu hp hw.le)
    (welfare_v_attainable hu hp' hw'.le)

/-- **Section 3.I** (MWG, p. 81). At its base prices the money metric is wealth:
`e(p, v(p, w)) = w`. -/
theorem moneyMetric_self {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 ≤ w) : moneyMetric u p p w = w :=
  equation_3_E_1_left hrep hu hlns hp hw

/-- The expenditure function does not depend on the representation: `e_{f∘u}(p, f(ū)) =
e_u(p, ū)` for strictly increasing `f`. -/
theorem expenditure_comp {u : (Fin L → ℝ) → ℝ} {f : ℝ → ℝ} (hf : StrictMono f)
    (p : Fin L → ℝ) (ub : ℝ) : expenditure (f ∘ u) p (f ub) = expenditure u p ub := by
  have : empConstraintSet (f ∘ u) (f ub) = empConstraintSet u ub := by
    ext x
    simp [empConstraintSet, hf.le_iff_le]
  rw [expenditure, expenditure, this]

/-- **Footnote 21** (MWG, p. 81). The money metric does not depend on the indirect utility
function (equivalently, the utility function) used to construct it: for strictly increasing `f`,
the money metric of `f ∘ u` equals that of `u`. -/
theorem footnote_3_I_21 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {f : ℝ → ℝ} (hf : StrictMono f) {pb p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 ≤ w) : moneyMetric (f ∘ u) pb p w = moneyMetric u pb p w := by
  rw [moneyMetric, moneyMetric, indirectUtility_comp hf (proposition_3_D_1 hu hp hw),
    expenditure_comp hf]

/-- **Equation (3.I.1)** (MWG, p. 82). `EV(p⁰, p¹, w) = e(p⁰, u¹) - w`. -/
theorem equation_3_I_1 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hw : 0 ≤ w) :
    equivalentVariation u p₀ p₁ w = expenditure u p₀ (indirectUtility u p₁ w) - w := by
  rw [equivalentVariation, equation_3_E_1_left hrep hu hlns hp₀ hw]

/-- **Equation (3.I.2)** (MWG, p. 82). `CV(p⁰, p¹, w) = w - e(p¹, u⁰)`. -/
theorem equation_3_I_2 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₁ : StrictlyPositive p₁) {w : ℝ} (hw : 0 ≤ w) :
    compensatingVariation u p₀ p₁ w = w - expenditure u p₁ (indirectUtility u p₀ w) := by
  rw [compensatingVariation, equation_3_E_1_left hrep hu hlns hp₁ hw]

/-- **Section 3.I and footnote 22** (MWG, p. 82). The equivalent variation in indirect-utility
form: `v(p⁰, w + EV) = u¹`; conversely if `u¹ = v(p⁰, w + EV')` with `w + EV' ≥ 0`, then
`e(p⁰, u¹) = w + EV'`, so `EV' = EV`. -/
theorem footnote_3_I_22 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w : ℝ} (hw : 0 < w) :
    indirectUtility u p₀ (w + equivalentVariation u p₀ p₁ w) = indirectUtility u p₁ w ∧
      ∀ ev : ℝ, 0 ≤ w + ev → indirectUtility u p₁ w = indirectUtility u p₀ (w + ev) →
        ev = equivalentVariation u p₀ p₁ w := by
  rw [equation_3_I_1 hrep hu hlns hp₀ hw.le, add_sub_cancel]
  refine ⟨equation_3_E_1_right hu hp₀ (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw)
    (welfare_v_attainable hu hp₁ hw.le), fun ev hev h => ?_⟩
  rw [h, equation_3_E_1_left hrep hu hlns hp₀ hev]
  ring

/-- **Section 3.I** (MWG, p. 82). The compensating variation in indirect-utility form:
`v(p¹, w - CV) = u⁰`. -/
theorem cv_indirectUtility {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w : ℝ} (hw : 0 < w) :
    indirectUtility u p₁ (w - compensatingVariation u p₀ p₁ w) = indirectUtility u p₀ w := by
  rw [equation_3_I_2 hrep hu hlns hp₁ hw.le, sub_sub_cancel]
  exact equation_3_E_1_right hu hp₁ (relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw)
    (welfare_v_attainable hu hp₀ hw.le)

/-- **Section 3.I** (MWG, p. 82). EV and CV give the correct welfare ranking: the consumer is
better off under `p¹` than under `p⁰` iff `EV > 0` iff `CV > 0`. -/
theorem welfare_ranking {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w : ℝ} (hw : 0 < w) :
    (indirectUtility u p₀ w < indirectUtility u p₁ w ↔ 0 < equivalentVariation u p₀ p₁ w) ∧
      (indirectUtility u p₀ w < indirectUtility u p₁ w ↔
        0 < compensatingVariation u p₀ p₁ w) := by
  have h0 := relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw
  have h1 := relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw
  have n0 := welfare_v_attainable hu hp₀ hw.le
  have n1 := welfare_v_attainable hu hp₁ hw.le
  constructor
  · rw [equivalentVariation, sub_pos, welfare_e_lt_iff hu hp₀ h0 h1 n0 n1]
  · rw [compensatingVariation, sub_pos, welfare_e_lt_iff hu hp₁ h0 h1 n0 n1]

/-- **Section 3.I** (MWG, p. 86). With `p⁰` fixed, `EV(p⁰, ·, w)` is an indirect utility
function (a money metric one): `EV(p⁰, p¹, w) - EV(p⁰, p², w) = e(p⁰, u¹) - e(p⁰, u²)`, and `p¹`
is better than `p²` iff `EV(p⁰, p¹, w) > EV(p⁰, p², w)`. -/
theorem ev_compare {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ p₂ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) (hp₂ : StrictlyPositive p₂)
    {w : ℝ} (hw : 0 < w) :
    equivalentVariation u p₀ p₁ w - equivalentVariation u p₀ p₂ w =
        expenditure u p₀ (indirectUtility u p₁ w) - expenditure u p₀ (indirectUtility u p₂ w) ∧
      (indirectUtility u p₂ w < indirectUtility u p₁ w ↔
        equivalentVariation u p₀ p₂ w < equivalentVariation u p₀ p₁ w) := by
  refine ⟨by rw [equivalentVariation, equivalentVariation]; ring, ?_⟩
  rw [equivalentVariation, equivalentVariation, sub_lt_sub_iff_right,
    welfare_e_lt_iff hu hp₀ (relations_indirectUtility_gt_zero hrep hu hlns hp₂ hw)
      (relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw) (welfare_v_attainable hu hp₂ hw.le)
      (welfare_v_attainable hu hp₁ hw.le)]

/-- **Section 3.I** (MWG, p. 86). `CV(p⁰, p¹, w) - CV(p⁰, p², w) = e(p², u⁰) - e(p¹, u⁰)`: the
compensating variations use different base prices (see Exercise 3.I.4 for a misranking). -/
theorem cv_difference {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ p₂ : Fin L → ℝ}
    (hp₁ : StrictlyPositive p₁) (hp₂ : StrictlyPositive p₂) {w : ℝ} (hw : 0 ≤ w) :
    compensatingVariation u p₀ p₁ w - compensatingVariation u p₀ p₂ w =
      expenditure u p₂ (indirectUtility u p₀ w) - expenditure u p₁ (indirectUtility u p₀ w) := by
  rw [equation_3_I_2 hrep hu hlns hp₁ hw, equation_3_I_2 hrep hu hlns hp₂ hw]
  ring

/-- **Footnote 24** (MWG, p. 86). `p¹` and `p²` are ranked correctly by the sign of
`CV(p¹, p², w)`. -/
theorem footnote_3_I_24 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₁ p₂ : Fin L → ℝ}
    (hp₁ : StrictlyPositive p₁) (hp₂ : StrictlyPositive p₂) {w : ℝ} (hw : 0 < w) :
    indirectUtility u p₁ w < indirectUtility u p₂ w ↔ 0 < compensatingVariation u p₁ p₂ w :=
  (welfare_ranking hrep hu hlns hp₁ hp₂ hw).2

/-- **Proposition 3.I.1** (MWG, p. 87), for a preference. If `≿` is locally nonsatiated,
`x⁰ ∈ ℝ^L_+` with `p⁰·x⁰ = w` (Walras' law at `x⁰ = x(p⁰, w)`), and `(p¹ - p⁰)·x⁰ < 0`, then some
bundle affordable at `(p¹, w)` is strictly preferred to `x⁰`. -/
theorem proposition_3_I_1_pref {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ x₀ : Fin L → ℝ} {w : ℝ}
    (hx₀ : x₀ ∈ nonnegOrthant L) (hwal : p₀ ⬝ᵥ x₀ = w) (htest : (p₁ - p₀) ⬝ᵥ x₀ < 0) :
    ∃ z ∈ budgetSet p₁ w, Strict r z x₀ := by
  have : p₁ ⬝ᵥ x₀ < w := by rw [sub_dotProduct] at htest; linarith
  obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns p₁ hx₀ this
  exact ⟨z, ⟨hz, hpz.le⟩, hs⟩

/-- **Proposition 3.I.1** (MWG, p. 87). For `u` continuous on `ℝ^L_+` representing a locally
nonsatiated `≿` and `x⁰ ∈ x(p⁰, w)`: if `(p¹ - p⁰)·x⁰ < 0`, the consumer is strictly better off
under `(p¹, w)` than under `(p⁰, w)`. -/
theorem proposition_3_I_1 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ x₀ : Fin L → ℝ}
    (hp₁ : StrictlyPositive p₁) {w : ℝ} (hx₀ : x₀ ∈ walrasianDemand u p₀ w)
    (htest : (p₁ - p₀) ⬝ᵥ x₀ < 0) : indirectUtility u p₀ w < indirectUtility u p₁ w := by
  obtain ⟨z, hz, hs⟩ := proposition_3_I_1_pref hlns hx₀.1.1
    (proposition_3_D_2_ii hrep hlns hx₀) htest
  rw [indirectUtility_eq_of_mem hx₀]
  exact ((hrep.strict_iff hz.1 hx₀.1.1).mp hs).trans_le (le_indirectUtility hu hp₁ hz)

/-- **Equation (3.I.7)** (MWG, p. 87). The second-order remainder of the expansion of `e(·, u⁰)`
at `p⁰` is nonpositive (concavity): `e(p¹, u⁰) ≤ e(p⁰, u⁰) + (p¹ - p⁰)·h(p⁰, u⁰)`, and with
`h(p⁰, u⁰) = x⁰`, `e(p⁰, u⁰) = w` this is `e(p¹, u⁰) ≤ w + (p¹ - p⁰)·x⁰`. -/
theorem equation_3_I_7 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    {p₀ p₁ x₀ : Fin L → ℝ} (hp₁ : StrictlyPositive p₁) {w : ℝ}
    (hx₀ : x₀ ∈ walrasianDemand u p₀ w) :
    expenditure u p₁ (u x₀) ≤ w + (p₁ - p₀) ⬝ᵥ x₀ := by
  obtain ⟨hh, he⟩ := proposition_3_E_1_i hrep hlns hx₀
  have h1 := (expenditure_le_linear hh hp₁).1
  have hw := proposition_3_D_2_ii hrep hlns hx₀
  rw [sub_dotProduct, hw]
  linarith

/-- **Proposition 3.I.2** (MWG, p. 88), with `0 < α < ᾱ` (correction D3). Let `x⁰ ∈ x(p⁰, w)`,
`u⁰ = u(x⁰)`, and suppose `e(·, u⁰)` is differentiable at `p⁰`. If `(p¹ - p⁰)·x⁰ > 0`, there is
`ᾱ ∈ (0, 1)` such that for all `α ∈ (0, ᾱ)`, `e((1 - α)p⁰ + αp¹, u⁰) > w`, so the consumer is
strictly better off under `(p⁰, w)` than under `((1 - α)p⁰ + αp¹, w)`. -/
theorem proposition_3_I_2 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ x₀ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w : ℝ}
    (hx₀ : x₀ ∈ walrasianDemand u p₀ w) {E' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hd : HasFDerivAt (fun q => expenditure u q (u x₀)) E' p₀)
    (htest : 0 < (p₁ - p₀) ⬝ᵥ x₀) :
    ∃ αb : ℝ, 0 < αb ∧ αb < 1 ∧ ∀ α : ℝ, 0 < α → α < αb →
      w < expenditure u ((1 - α) • p₀ + α • p₁) (u x₀) ∧
        indirectUtility u ((1 - α) • p₀ + α • p₁) w < indirectUtility u p₀ w := by
  obtain ⟨hh, he⟩ := proposition_3_E_1_i hrep hlns hx₀
  -- the gradient of `e(·, u⁰)` at `p⁰` is `x⁰`
  have hgrad : E' = dualityDotCLM x₀ := by
    have hmin : IsLocalMin (fun q => q ⬝ᵥ x₀ - expenditure u q (u x₀)) p₀ := by
      filter_upwards [relations_eventually_strictlyPositive hp₀] with q hq
      have h1 := (expenditure_le_linear hh hq).1
      have h2 := (expenditure_le_linear hh hq).2
      linarith
    have := hmin.hasFDerivAt_eq_zero ((duality_hasFDerivAt_dot_left x₀ p₀).sub hd)
    exact (sub_eq_zero.mp this).symm
  set z := p₁ - p₀ with hz
  have hpath : ∀ α : ℝ, (1 - α) • p₀ + α • p₁ = p₀ + α • z := fun α => by
    rw [hz]; module
  have hg := mc_line_hasDerivAt hd z
  rw [hgrad, dualityDotCLM_apply, dotProduct_comm] at hg
  -- the slope of `g(α) = e(p⁰ + αz, u⁰)` at `0` is positive, so `g(α) > g(0) = w` for small `α`
  have hslope := hg.tendsto_slope_zero_right
  have hev : ∀ᶠ α in 𝓝[>] (0 : ℝ), 0 < α⁻¹ • (expenditure u (p₀ + α • z) (u x₀) -
      expenditure u (p₀ + (0 : ℝ) • z) (u x₀)) := by
    have := hslope.eventually (lt_mem_nhds htest)
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun α hα0 hα => ?_⟩
  have hαε : α < ε := lt_of_lt_of_le hα ((min_le_left _ _).trans (by linarith))
  have hmem := hball ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hα0]; exact hαε,
    hα0⟩
  simp only [zero_smul, add_zero] at hmem
  have hpos : 0 < expenditure u (p₀ + α • z) (u x₀) - expenditure u p₀ (u x₀) := by
    have hmem' : 0 < α⁻¹ • (expenditure u (p₀ + α • z) (u x₀) - expenditure u p₀ (u x₀)) :=
      hmem
    exact (smul_pos_iff_of_pos_left (inv_pos.mpr hα0)).mp hmem'
  rw [he] at hpos
  have hlt : w < expenditure u ((1 - α) • p₀ + α • p₁) (u x₀) := by rw [hpath]; linarith
  refine ⟨hlt, ?_⟩
  have hpα : StrictlyPositive ((1 - α) • p₀ + α • p₁) :=
    exp_convex_strictlyPositive L hp₀ hp₁ (by linarith [hα.trans_le (min_le_right _ _)])
      hα0.le (by ring)
  have hw : 0 ≤ w := by
    rw [← proposition_3_D_2_ii hrep hlns hx₀]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hp₀ l).le (hx₀.1.1 l)
  rw [indirectUtility_eq_of_mem hx₀]
  exact (lt_expenditure_iff hu hpα hw ⟨x₀, hx₀.1.1, le_rfl⟩).mp hlt

/-- **Exercise 3.I.11** (MWG, p. 103). With `x¹ ∈ x(p¹, w)` known: if `(p¹ - p⁰)·x¹ > 0`, the
consumer is worse off at `(p¹, w)` than at `(p⁰, w)`; the test is equivalently
`p⁰·(x¹ - x⁰) < 0` for `x⁰ ∈ x(p⁰, w)`; and it is the first-order approximation of `e(·, u¹)` at
`p¹`: `e(p⁰, u¹) ≤ w - (p¹ - p⁰)·x¹`. -/
theorem exercise_3_I_11 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ x₀ x₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hx₀ : x₀ ∈ walrasianDemand u p₀ w)
    (hx₁ : x₁ ∈ walrasianDemand u p₁ w) :
    (0 < (p₁ - p₀) ⬝ᵥ x₁ → indirectUtility u p₁ w < indirectUtility u p₀ w) ∧
      ((p₁ - p₀) ⬝ᵥ x₁ = -(p₀ ⬝ᵥ (x₁ - x₀))) ∧
      expenditure u p₀ (u x₁) ≤ w - (p₁ - p₀) ⬝ᵥ x₁ := by
  have hw₀ := proposition_3_D_2_ii hrep hlns hx₀
  have hw₁ := proposition_3_D_2_ii hrep hlns hx₁
  refine ⟨fun htest => ?_, ?_, ?_⟩
  · have := proposition_3_I_1 hrep hu hlns hp₀ hx₁ (by
      rw [show p₀ - p₁ = -(p₁ - p₀) by abel, neg_dotProduct]; linarith)
    exact this
  · rw [sub_dotProduct, dotProduct_sub, hw₀, hw₁]
    ring
  · have := equation_3_I_7 hrep hlns hp₀ hx₁
    rw [show p₀ - p₁ = -(p₁ - p₀) by abel, neg_dotProduct] at this
    linarith

/-- **Exercise 3.I.12** (MWG, p. 104). The equivalent variation of a change from `(p⁰, w⁰)` to
`(p¹, w¹)`: `e(p⁰, u¹) - w⁰`, `uⁱ = v(pⁱ, wⁱ)`. -/
noncomputable def equivalentVariationPW (u : (Fin L → ℝ) → ℝ) (p₀ : Fin L → ℝ) (w₀ : ℝ)
    (p₁ : Fin L → ℝ) (w₁ : ℝ) : ℝ :=
  expenditure u p₀ (indirectUtility u p₁ w₁) - expenditure u p₀ (indirectUtility u p₀ w₀)

/-- **Exercise 3.I.12** (MWG, p. 104). The compensating variation of a change from `(p⁰, w⁰)`
to `(p¹, w¹)`: `w¹ - e(p¹, u⁰)`. -/
noncomputable def compensatingVariationPW (u : (Fin L → ℝ) → ℝ) (p₀ : Fin L → ℝ) (w₀ : ℝ)
    (p₁ : Fin L → ℝ) (w₁ : ℝ) : ℝ :=
  expenditure u p₁ (indirectUtility u p₁ w₁) - expenditure u p₁ (indirectUtility u p₀ w₀)

/-- **Exercise 3.I.12** (MWG, p. 104). The extended measures: `EV = e(p⁰, u¹) - w⁰`,
`CV = w¹ - e(p¹, u⁰)`; they reduce to (3.I.1)-(3.I.2) when `w⁰ = w¹`; they rank `(p⁰, w⁰)` and
`(p¹, w¹)` correctly; and the partial-information test extends: if `p¹·x⁰ < w¹` for
`x⁰ ∈ x(p⁰, w⁰)`, the consumer is better off at `(p¹, w¹)`. -/
theorem exercise_3_I_12 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w₀ w₁ : ℝ} (hw₀ : 0 < w₀)
    (hw₁ : 0 < w₁) :
    equivalentVariationPW u p₀ w₀ p₁ w₁ = expenditure u p₀ (indirectUtility u p₁ w₁) - w₀ ∧
      compensatingVariationPW u p₀ w₀ p₁ w₁ = w₁ - expenditure u p₁ (indirectUtility u p₀ w₀) ∧
      equivalentVariationPW u p₀ w₀ p₁ w₀ = equivalentVariation u p₀ p₁ w₀ ∧
      compensatingVariationPW u p₀ w₀ p₁ w₀ = compensatingVariation u p₀ p₁ w₀ ∧
      (indirectUtility u p₀ w₀ < indirectUtility u p₁ w₁ ↔
        0 < equivalentVariationPW u p₀ w₀ p₁ w₁) ∧
      (indirectUtility u p₀ w₀ < indirectUtility u p₁ w₁ ↔
        0 < compensatingVariationPW u p₀ w₀ p₁ w₁) ∧
      ∀ x₀ ∈ walrasianDemand u p₀ w₀, p₁ ⬝ᵥ x₀ < w₁ →
        indirectUtility u p₀ w₀ < indirectUtility u p₁ w₁ := by
  have h0 := relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw₀
  have h1 := relations_indirectUtility_gt_zero hrep hu hlns hp₁ hw₁
  have n0 := welfare_v_attainable hu hp₀ hw₀.le
  have n1 := welfare_v_attainable hu hp₁ hw₁.le
  refine ⟨by rw [equivalentVariationPW, equation_3_E_1_left hrep hu hlns hp₀ hw₀.le],
    by rw [compensatingVariationPW, equation_3_E_1_left hrep hu hlns hp₁ hw₁.le], rfl, rfl,
    by rw [equivalentVariationPW, sub_pos, welfare_e_lt_iff hu hp₀ h0 h1 n0 n1],
    by rw [compensatingVariationPW, sub_pos, welfare_e_lt_iff hu hp₁ h0 h1 n0 n1],
    fun x₀ hx₀ htest => ?_⟩
  obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns p₁ hx₀.1.1 htest
  rw [indirectUtility_eq_of_mem hx₀]
  exact ((hrep.strict_iff hz hx₀.1.1).mp hs).trans_le (le_indirectUtility hu hp₁ ⟨hz, hpz.le⟩)

/-- **Exercise 3.I.6** (MWG, p. 102). With consumers `i = 1, ..., I` (utilities `uᵢ`, wealth
`wᵢ > 0`), if `∑ᵢ CVᵢ(p⁰, p¹, wᵢ) > 0`, the wealth levels `w'ᵢ = e_i(p¹, v_i(p⁰, wᵢ))` satisfy
`∑ᵢ w'ᵢ < ∑ᵢ wᵢ` and `vᵢ(p¹, w'ᵢ) = vᵢ(p⁰, wᵢ)`: everybody can be compensated. -/
theorem exercise_3_I_6 {I : ℕ} {u : Fin I → (Fin L → ℝ) → ℝ}
    {r : Fin I → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : ∀ i, RepresentsOn (nonnegOrthant L) (u i) (r i))
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant L) (r i)) {p₀ p₁ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) {w : Fin I → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : 0 < ∑ i, compensatingVariation (u i) p₀ p₁ (w i)) :
    ∃ w' : Fin I → ℝ, ∑ i, w' i < ∑ i, w i ∧
      ∀ i, indirectUtility (u i) p₁ (w' i) = indirectUtility (u i) p₀ (w i) := by
  refine ⟨fun i => w i - compensatingVariation (u i) p₀ p₁ (w i), ?_, fun i =>
    cv_indirectUtility (hrep i) (hu i) (hlns i) hp₀ hp₁ (hw i)⟩
  rw [Finset.sum_sub_distrib]
  linarith

end MWG.ClassicalDemand
