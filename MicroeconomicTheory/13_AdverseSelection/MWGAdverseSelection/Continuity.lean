/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# Continuity of profits and the sign of `E[θ | r(θ) ≤ w] - w`

MWG, Section 13.B, pp. 441-444.

The book uses (p. 441) that, when `F` has a density, `E[θ | r(θ) ≤ w]` varies continuously with
`w`. We prove the form used in the proof of Proposition 13.B.1: the profit
`w ↦ ∫_{Θ(w)} (θ - w) dF` is continuous whenever `F` has no atoms and `r` is one-to-one on
`[θ̲, θ̄]` (dominated convergence: the integrand is continuous in `w` except at the type with
`r(θ) = w`). We then prove the facts about `W*` used in Section 13.B: for `w > θ̄` the profit is
negative, below `θ̲` no type with `r(θ) ≤ θ` makes a loss, and (with `r` continuous and positive
density) `μ(Θ(w)) > 0` for every `w > r(θ̲)`.
-/

namespace MWG.AdverseSelection

open MeasureTheory Filter Topology

/-- **Section 13.B** (MWG, pp. 441, 444). The profit `w ↦ ∫_{Θ(w)} (θ - w) dF` is continuous when
`F` has no atoms and `r` is measurable and one-to-one on `[θ̲, θ̄]` (in particular when it is
strictly increasing there). -/
theorem continuous_firmProfit {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hna : ∀ x, μ {x} = 0) (hr : Measurable r) (hinj : Set.InjOn r (Set.Icc θl θh)) :
    Continuous (firmProfit μ r) := by
  have := hd.prob
  have : NullSingletonClass μ := ⟨hna⟩
  rw [continuous_iff_continuousAt]
  intro w0
  refine continuousAt_of_dominated (bound := fun _ => |θl| + |θh| + |w0| + 1) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun w =>
      ((measurable_id.sub measurable_const).indicator
        (measurableSet_acceptSet hr w)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show w0 - 1 < w0 by linarith) (show w0 < w0 + 1 by linarith)]
      with w hw
    filter_upwards [hd.ae_mem] with θ hθ
    rw [Real.norm_eq_abs]
    by_cases hθw : θ ∈ acceptSet r w
    · rw [Set.indicator_of_mem hθw, abs_le]
      constructor <;> cases abs_cases θl <;> cases abs_cases θh <;> cases abs_cases w0 <;>
        linarith [hθ.1, hθ.2, hw.1, hw.2]
    · rw [Set.indicator_of_notMem hθw, abs_zero]; positivity
  · have hsub : ({θ | r θ = w0} ∩ Set.Icc θl θh).Subsingleton := fun a ha b hb =>
      hinj ha.2 hb.2 (ha.1.trans hb.1.symm)
    have hnull : μ ({θ | r θ = w0} ∩ Set.Icc θl θh) = 0 := hsub.measure_zero μ
    have hae : ∀ᵐ θ ∂μ, θ ∉ {θ | r θ = w0} ∩ Set.Icc θl θh :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hae, hd.ae_mem] with θ h1 h2
    have hne : r θ ≠ w0 := fun h => h1 ⟨h, h2⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hc : ContinuousAt (fun w : ℝ => θ - w) w0 :=
        (continuous_const.sub continuous_id).continuousAt
      refine hc.congr ?_
      filter_upwards [Ioi_mem_nhds hlt] with w hw
      have : θ ∈ acceptSet r w := show r θ ≤ w from le_of_lt hw
      rw [Set.indicator_of_mem this]
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Iio_mem_nhds hgt] with w hw
      have : θ ∉ acceptSet r w := fun h => absurd (show r θ ≤ w from h) (not_le.2 hw)
      rw [Set.indicator_of_notMem this]

/-- **Section 13.B** (MWG, p. 444). Above `θ̄` every hire makes a loss: `Π(w) < 0` once `Θ(w)`
has positive probability, and `Π(w) ≤ 0` always. -/
theorem firmProfit_nonpos_of_gt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) {w : ℝ} (hw : θh ≤ w) : firmProfit μ r w ≤ 0 := by
  rw [firmProfit_eq_setIntegral hr]
  exact setIntegral_nonpos_of_ae_restrict
    (ae_restrict_of_ae (hd.ae_mem.mono fun θ hθ => show θ - w ≤ 0 by linarith [hθ.2]))

/-- A set integral of an a.e. positive function over a set of positive measure is positive. -/
theorem setIntegral_pos_of_ae_pos {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (hpos : 0 < μ s) (hf : ∀ᵐ x ∂μ, x ∈ s → 0 < f x)
    (hint : IntegrableOn f s μ) :
    0 < ∫ x in s, f x ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · refine hpos.trans_le (measure_mono_ae ?_)
    filter_upwards [hf] with x hx hxs
    exact ⟨(hx hxs).ne', hxs⟩
  · exact (ae_restrict_iff' hs).2 (hf.mono fun x hx hxs => (hx hxs).le)

/-- **Section 13.B** (MWG, p. 444). For `w > θ̄` with `μ(Θ(w)) > 0`, `Π(w) < 0`, equivalently
`E[θ | r(θ) ≤ w] < w`. -/
theorem firmProfit_neg_of_gt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) {w : ℝ} (hw : θh < w) (hpos : 0 < μ (acceptSet r w)) :
    firmProfit μ r w < 0 := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, ← neg_pos, ← integral_neg]
  refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet hr w) hpos
    (hd.ae_mem.mono fun θ hθ _ => by linarith [hθ.2]) ?_
  exact (hd.integrable_id.sub (integrable_const w)).neg.integrableOn

end MWG.AdverseSelection
