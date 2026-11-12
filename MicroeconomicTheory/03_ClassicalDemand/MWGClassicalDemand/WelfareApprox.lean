/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareTax

/-!
# Welfare evaluation: taxes, comparisons and approximations

MWG, Section 3.I, pp. 84-91.

* Example 3.I.1, small type (p. 84, Figure 3.I.5): `x(p¹, w)` lies on the budget line of
  `B_{p⁰, w - T}`.
* Two taxes raising the same revenue `T` (p. 86, Figure 3.I.6): the first is better iff its
  deadweight loss is smaller.
* Footnote 28 (p. 90): the derivatives of `EV(p¹, p⁰, w)` and `AV(p¹, p⁰, w)` with respect to
  `p¹_l` at `p⁰_l` are `x_l(p⁰, w)` (the statement for `CV` is OPEN).
* The approximation (3.I.9) (pp. 90-91): `h̃(p, u⁰) = x(p⁰, w) + S(p⁰, w)(p - p⁰)` is the
  first-order Taylor approximation of the Hicksian demand at `p⁰`, computable from the Walrasian
  demand; `h(p, u⁰) - h̃(p, u⁰) = o(‖p - p⁰‖)`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology MeasureTheory Asymptotics

variable {L : ℕ}

/-- **Example 3.I.1**, small type (MWG, p. 84, Figure 3.I.5). With a tax `τ` on good `l` and
revenue `T = τ x_l(p¹, w)`, the bundle `x(p¹, w)` lies on the budget line of `B_{p⁰, w - T}`:
`p⁰·x(p¹, w) = w - T`. -/
theorem example_3_I_1_budget_line {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (l : Fin L) {τ w : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u (priceLine p l (p l + τ)) w) :
    p ⬝ᵥ x = w - τ * x l := by
  have := proposition_3_D_2_ii hrep hlns hx
  rw [priceLine_dot] at this
  linarith

/-- **Section 3.I** (MWG, p. 86, Figure 3.I.6). If taxes leading to `p¹` and `p²` raise the same
revenue `T`, the first is better iff its deadweight loss `(-T) - EV(p⁰, p¹, w)` is smaller. -/
theorem two_taxes_compare {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p₀ p₁ p₂ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (hp₁ : StrictlyPositive p₁) (hp₂ : StrictlyPositive p₂)
    {w : ℝ} (hw : 0 < w) (T : ℝ) :
    indirectUtility u p₂ w < indirectUtility u p₁ w ↔
      -T - equivalentVariation u p₀ p₁ w < -T - equivalentVariation u p₀ p₂ w := by
  rw [(ev_compare hrep hu hlns hp₀ hp₁ hp₂ hw).2]
  constructor <;> intro h <;> linarith

/-- **Footnote 28** (MWG, p. 90), the equivalent variation. With `u` continuous, strictly
quasiconcave, representing a locally nonsatiated `≿`, and `xs` the Walrasian demand function: as a
function of the price `s` of good `l` in `p¹`, `EV(p¹, p⁰, w)` has derivative `x_l(p⁰, w)` at
`s = p⁰_l`. -/
theorem footnote_3_I_28_ev {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (l : Fin L) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun s => equivalentVariation u (priceLine p₀ l s) p₀ w) (xs p₀ w l) (p₀ l) := by
  have h0 := relations_indirectUtility_gt_zero hrep hu hlns hp₀ hw
  have n0 := welfare_v_attainable hu hp₀ hw.le
  obtain ⟨hd, -, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hp₀ l h0 n0
  have hself : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  have hval : hicksianOf u xs (priceLine p₀ l (p₀ l)) (indirectUtility u p₀ w) l = xs p₀ w l := by
    rw [hicksianOf, hself, equation_3_E_1_left hrep hu hlns hp₀ hw.le]
  have h1 := (hd (p₀ l) (hp₀ l)).sub_const w
  rw [hval] at h1
  apply h1.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (hp₀ l)] with s hs
  exact equation_3_I_1 hrep hu hlns (priceLine_pos hp₀ l hs) hw.le

/-- **Footnote 28** (MWG, p. 90), the area variation. If `t ↦ x_l(p⁰ with p_l = t, w)` is
continuous on `t > 0`, then `AV(p¹, p⁰, w) = ∫_{p⁰_l}^{p¹_l} x_l` has derivative `x_l(p⁰, w)`
with respect to `p¹_l` at `p⁰_l`. -/
theorem footnote_3_I_28_av {xs : DemandFunction L} {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀)
    (l : Fin L) {w : ℝ}
    (hc : ContinuousOn (fun t => xs (priceLine p₀ l t) w l) (Set.Ioi 0)) :
    HasDerivAt (fun s => areaVariation xs p₀ l s (p₀ l) w) (xs p₀ w l) (p₀ l) := by
  have hself : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  have hmem : p₀ l ∈ Set.Ioi (0 : ℝ) := hp₀ l
  have hint : IntervalIntegrable (fun t => xs (priceLine p₀ l t) w l) volume (p₀ l) (p₀ l) :=
    IntervalIntegrable.refl
  have := intervalIntegral.integral_hasDerivAt_right hint
    (hc.stronglyMeasurableAtFilter isOpen_Ioi _ hmem)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hmem))
  rw [hself] at this
  exact this

/-- **Equation (3.I.9)** (MWG, pp. 90-91). Let `u` be continuous on `ℝ^L_+`, representing a
locally nonsatiated, strictly convex `≿`, `xs` a demand function differentiable at `(p⁰, w)` with
derivative `Dx`, and `h(·, u⁰)` the Hicksian demand at `u⁰ = v(p⁰, w)`. Then
`h̃(p) = x(p⁰, w) + S(p⁰, w)(p - p⁰)` (computable from the Walrasian demand) is the first-order
approximation of `h(·, u⁰)` at `p⁰`: `h(p, u⁰) - h̃(p) = o(‖p - p⁰‖)`. -/
theorem equation_3_I_9 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {xs : DemandFunction L} (hxs : ∀ p w, PWDomain p w → xs p w ∈ walrasianDemand u p w)
    {p₀ : Fin L → ℝ} {w : ℝ} (hpw : PWDomain p₀ w)
    {Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry xs) Dx (p₀, w))
    {hf : (Fin L → ℝ) → (Fin L → ℝ)}
    (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q (indirectUtility u p₀ w)) :
    (fun p => hf p - (xs p₀ w + (slutskyMatrix Dx (xs p₀ w)).mulVec (p - p₀))) =o[𝓝 p₀]
      fun p => p - p₀ := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  obtain ⟨hhd, hjac⟩ := proposition_3_G_3 hrep hu hlns hsc hxs hpw hD hhf
  -- `h(p⁰, u⁰) = x(p⁰, w)`
  have hx₀ := hxs p₀ w hpw
  have hmem : xs p₀ w ∈ hicksianDemand u p₀ (indirectUtility u p₀ w) := by
    rw [indirectUtility_eq_of_mem hx₀]
    exact (proposition_3_E_1_i hrep hlns hx₀).1
  have hp0 : hf p₀ = xs p₀ w :=
    exercise_3_E_4_unique hu hq hpw.1 _ (hhf p₀ hpw.1) hmem
  have := hhd.isLittleO
  refine this.congr_left fun p => ?_
  rw [← hjac, jacobian_mulVec, hp0]
  abel

end MWG.ClassicalDemand
