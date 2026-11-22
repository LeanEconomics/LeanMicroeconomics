import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The labor market with unobservable productivity

MWG, Section 13.B, pp. 437-441.

Worker types `θ` are distributed according to a probability measure `μ` on `ℝ` concentrated on
`[θ̲, θ̄]` (the distribution function `F` of the book is `θ ↦ μ (Iic θ)`). A worker of type `θ`
earns `r(θ)` at home.

* `acceptSet r w` is `Θ(w) = {θ : r(θ) ≤ w}`, (13.B.2).
* `meanType μ` is `E[θ]` and `condMean μ θl θh S` is `E[θ | θ ∈ S]`.
* `IsCompEq` is **Definition 13.B.1**; `eqWages` is the set `W*` of competitive equilibrium
  wages.
* `firmProfit μ r w = ∫_{Θ(w)} (θ - w) dF`: the profit of a firm that hires every worker
  willing to work at wage `w`; `firmProfit_eq` relates it to `E[θ | Θ(w)] - w`.
* `laborDemand` is (13.B.3).
* `TypeDist` collects the standing assumptions on `F` and `HasPosDensity` the assumption that
  `F` has a density `f > 0` on `[θ̲, θ̄]` (in the form used: no atoms and positive mass on
  every nondegenerate subinterval).

Departure (conditional expectation of a null set). The book takes `E[θ | Θ*] = E[θ]` when
`Θ* = ∅`, and in Figure 13.B.2 and Example 13.B.1 uses `E[θ | Θ(w)] = θ̲` at `w = r(θ̲)`, where
`Θ(w) ∩ [θ̲, θ̄] = {θ̲}` is nonempty but has probability zero (the limit of `E[θ | r(θ) ≤ w]`
as `w ↓ r(θ̲)`, p. 441). `condMean` follows both conventions: for a null set meeting
`[θ̲, θ̄]` it is `θ̲`, for a null set missing it, `E[θ]`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **(13.B.2)** (MWG, p. 439). The set `Θ(w) = {θ : r(θ) ≤ w}` of worker types willing to accept
employment at wage `w` (a worker accepts when indifferent). -/
def acceptSet (r : ℝ → ℝ) (w : ℝ) : Set ℝ := {θ | r θ ≤ w}

/-- **Section 13.B** (MWG, p. 438). The unconditional expected productivity `E[θ]`. -/
noncomputable def meanType (μ : Measure ℝ) : ℝ := ∫ θ, θ ∂μ

open Classical in
/-- **Section 13.B** (MWG, pp. 439-441). `E[θ | θ ∈ S]`: the average over `S` when `S` has positive
probability; for a null set, `θ̲` if `S` meets `[θ̲, θ̄]` (the book's limiting value, p. 441) and
`E[θ]` otherwise (the book's convention for `Θ* = ∅`, p. 439). -/
noncomputable def condMean (μ : Measure ℝ) (θl θh : ℝ) (S : Set ℝ) : ℝ :=
  if 0 < μ S then (∫ θ in S, θ ∂μ) / (μ S).toReal
  else if (S ∩ Set.Icc θl θh).Nonempty then θl else meanType μ

/-- **Definition 13.B.1** (MWG, p. 439). A competitive equilibrium of the labor market with
unobservable productivity: a wage `w*` and a set `Θ*` of types accepting employment with
`Θ* = {θ : r(θ) ≤ w*}` (13.B.4) and `w* = E[θ | θ ∈ Θ*]` (13.B.5). -/
def IsCompEq (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) (w : ℝ) (Θs : Set ℝ) : Prop :=
  Θs = acceptSet r w ∧ w = condMean μ θl θh Θs

/-- **Section 13.B** (MWG, p. 443). The set `W*` of competitive equilibrium wages. -/
def eqWages (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Set ℝ :=
  {w | IsCompEq μ θl θh r w (acceptSet r w)}

/-- **(13.B.6)** (MWG, p. 441). `w ∈ W*` iff `w = E[θ | r(θ) ≤ w]`. -/
theorem mem_eqWages_iff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} {w : ℝ} :
    w ∈ eqWages μ θl θh r ↔ w = condMean μ θl θh (acceptSet r w) := by
  simp [eqWages, IsCompEq]

/-- **(13.B.3)** (MWG, p. 439). A price-taking constant-returns firm's demand for labor at wage
`w` when it expects average productivity `m`: none if `m < w`, any amount if `m = w`, unbounded
(every amount is dominated by a larger one) if `m > w`. We record the profit per worker. -/
def laborDemand (m w : ℝ) : Set ℝ :=
  if m < w then {0} else if m = w then Set.Ici 0 else ∅

/-- **(13.B.3)** (MWG, p. 439). With expected productivity `m > w`, hiring `z + 1` workers is
strictly more profitable than hiring `z`: the demand is infinite. -/
theorem laborDemand_unbounded {m w z : ℝ} (h : w < m) : z * (m - w) < (z + 1) * (m - w) := by
  nlinarith

/-- **(13.B.3)** (MWG, p. 439). With expected productivity `m < w`, every positive amount of labor
makes a loss, so the demand is `0`; with `m = w` every amount gives zero profit. -/
theorem laborDemand_profit {m w z : ℝ} (hz : 0 < z) :
    (m < w → z * (m - w) < 0) ∧ (m = w → z * (m - w) = 0) := by
  constructor
  · intro h; nlinarith
  · intro h; simp [h]

/-- **Section 13.B** (MWG, pp. 439, 444). The profit `∫_{Θ(w)} (θ - w) dF` of a firm offering wage
`w` and hiring every worker who accepts it (the book's `M (E[θ | r(θ) ≤ w] - w)`). -/
noncomputable def firmProfit (μ : Measure ℝ) (r : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ θ, (acceptSet r w).indicator (fun θ => θ - w) θ ∂μ

/-- **Section 13.B** (MWG, p. 438). The standing assumptions on the type distribution:
`0 ≤ θ̲ < θ̄`, `F` a probability distribution concentrated on `[θ̲, θ̄]`. -/
structure TypeDist (μ : Measure ℝ) (θl θh : ℝ) : Prop where
  nonneg : 0 ≤ θl
  lt : θl < θh
  prob : IsProbabilityMeasure μ
  supp : μ (Set.Icc θl θh)ᶜ = 0

/-- **Section 13.B** (MWG, p. 441). `F` has a density `f` with `f(θ) > 0` on `[θ̲, θ̄]`, in the
form used: no atoms and positive probability of every nondegenerate subinterval. -/
structure HasPosDensity (μ : Measure ℝ) (θl θh : ℝ) : Prop where
  noAtom : ∀ x, μ {x} = 0
  pos : ∀ a b, θl ≤ a → a < b → b ≤ θh → 0 < μ (Set.Icc a b)

/-- Almost every type lies in `[θ̲, θ̄]`. -/
theorem TypeDist.ae_mem {μ : Measure ℝ} {θl θh : ℝ} (h : TypeDist μ θl θh) :
    ∀ᵐ θ ∂μ, θ ∈ Set.Icc θl θh :=
  measure_eq_zero_iff_ae_notMem.1 h.supp |>.mono fun _ hx => by simpa using hx

/-- The type is integrable. -/
theorem TypeDist.integrable_id {μ : Measure ℝ} {θl θh : ℝ} (h : TypeDist μ θl θh) :
    Integrable (fun θ : ℝ => θ) μ := by
  have := h.prob
  refine Integrable.of_bound (C := |θl| + |θh|) measurable_id.aestronglyMeasurable ?_
  filter_upwards [h.ae_mem] with θ hθ
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> cases abs_cases θl <;> cases abs_cases θh <;> linarith [hθ.1, hθ.2]

/-- `θ̲ ≤ E[θ] ≤ θ̄`. -/
theorem TypeDist.meanType_mem {μ : Measure ℝ} {θl θh : ℝ} (h : TypeDist μ θl θh) :
    meanType μ ∈ Set.Icc θl θh := by
  have := h.prob
  constructor
  · have := integral_mono_ae (integrable_const θl) h.integrable_id
      (h.ae_mem.mono fun θ hθ => hθ.1)
    simpa [meanType] using this
  · have := integral_mono_ae h.integrable_id (integrable_const θh)
      (h.ae_mem.mono fun θ hθ => hθ.2)
    simpa [meanType] using this

/-- `Θ(w)` is measurable when `r` is. -/
theorem measurableSet_acceptSet {r : ℝ → ℝ} (hr : Measurable r) (w : ℝ) :
    MeasurableSet (acceptSet r w) :=
  measurableSet_le hr measurable_const

/-- Profit of a firm as the integral of `θ - w` over `Θ(w)`. -/
theorem firmProfit_eq_setIntegral {μ : Measure ℝ} {r : ℝ → ℝ} (hr : Measurable r) (w : ℝ) :
    firmProfit μ r w = ∫ θ in acceptSet r w, (θ - w) ∂μ :=
  integral_indicator (measurableSet_acceptSet hr w)

/-- **Section 13.B** (MWG, p. 444). `Π = M (E[θ | r(θ) ≤ w] - w)`: when `Θ(w)` has positive
probability `M`, the profit is `M` times the gap between average productivity and the wage. -/
theorem firmProfit_eq {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) {w : ℝ} (hpos : 0 < μ (acceptSet r w)) :
    firmProfit μ r w =
      (μ (acceptSet r w)).toReal * (condMean μ θl θh (acceptSet r w) - w) := by
  have := hd.prob
  have hfin : μ (acceptSet r w) ≠ ⊤ := measure_ne_top _ _
  have hM : 0 < (μ (acceptSet r w)).toReal := ENNReal.toReal_pos hpos.ne' hfin
  simp only [condMean, hpos, ↓reduceIte]
  rw [firmProfit_eq_setIntegral hr,
    integral_sub hd.integrable_id.integrableOn (integrable_const w).integrableOn,
    setIntegral_const, smul_eq_mul, Measure.real, mul_sub, mul_div_cancel₀ _ hM.ne']

/-- **Section 13.B** (MWG, pp. 439-441). For `w` with `0 < μ(Θ(w))`, `w` is a competitive
equilibrium wage iff the firm's profit at `w` is zero. -/
theorem mem_eqWages_iff_profit {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (hd : TypeDist μ θl θh) (hr : Measurable r) {w : ℝ} (hpos : 0 < μ (acceptSet r w)) :
    w ∈ eqWages μ θl θh r ↔ firmProfit μ r w = 0 := by
  have := hd.prob
  have hM : 0 < (μ (acceptSet r w)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [mem_eqWages_iff, firmProfit_eq hd hr hpos, mul_eq_zero, sub_eq_zero]
  constructor
  · intro h; exact Or.inr h.symm
  · rintro (h | h)
    · exact absurd h hM.ne'
    · exact h.symm

/-- A null `Θ(w)` gives zero profit. -/
theorem firmProfit_of_null {μ : Measure ℝ} {r : ℝ → ℝ} (hr : Measurable r) {w : ℝ}
    (h0 : μ (acceptSet r w) = 0) : firmProfit μ r w = 0 := by
  rw [firmProfit_eq_setIntegral hr, Measure.restrict_eq_zero.2 h0, integral_zero_measure]

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The adverse selection model with increasing `r`

MWG, Section 13.B, pp. 441-444.

From p. 441 on, MWG assume `r(θ) ≤ θ` on `[θ̲, θ̄]`, `r` strictly increasing and `F` with a
positive density. Here we collect what this gives for `Θ(w) = {θ : r(θ) ≤ w}` and for the set `W*`
of competitive equilibrium wages:

* below `r(θ̲)` nobody accepts employment and no wage is an equilibrium wage (footnote 7);
* at `w = r(θ̲)` only the null set `{θ̲}` accepts, and `r(θ̲) ∈ W*` iff `r(θ̲) = θ̲`
  (Figure 13.B.2);
* if `r` is also continuous, `Θ(w)` has positive probability for every `w > r(θ̲)`, and then
  `w ∈ W*` iff the firm's profit `Π(w) = ∫_{Θ(w)} (θ - w) dF` is zero;
* `exists_isGreatest_eqWages`: `W*` is nonempty and has a largest element (the book's
  `w* = Max W*`, p. 443).
-/

namespace MWG.AdverseSelection

open MeasureTheory Filter Topology

/-- Only the part of `Θ(w)` in `[θ̲, θ̄]` matters for probabilities. -/
theorem measure_acceptSet_inter {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (S : Set ℝ) :
    μ (S ∩ Set.Icc θl θh) = μ S := by
  refine measure_congr ?_
  filter_upwards [hd.ae_mem] with θ hθ
  simp only [Set.mem_inter_iff, eq_iff_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hθ⟩⟩

/-- If `S` contains `[θ̲, θ̄]` then `E[θ | θ ∈ S] = E[θ]`. -/
theorem condMean_of_superset {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S : Set ℝ}
    (hS : Set.Icc θl θh ⊆ S) : condMean μ θl θh S = meanType μ := by
  have := hd.prob
  have hSae : ∀ᵐ θ ∂μ, θ ∈ S := hd.ae_mem.mono fun _ h => hS h
  have h1 : μ S = 1 := by
    rw [← measure_acceptSet_inter hd, Set.inter_eq_right.2 hS]
    have : μ (Set.Icc θl θh) = μ Set.univ := measure_congr (by
      filter_upwards [hd.ae_mem] with θ hθ; simp [hθ])
    rw [this, measure_univ]
  have hint : ∫ θ in S, θ ∂μ = ∫ θ, θ ∂μ :=
    setIntegral_eq_integral_of_ae_compl_eq_zero (hSae.mono fun _ h hc => absurd h hc)
  simp only [condMean, h1, zero_lt_one, ↓reduceIte, hint, ENNReal.toReal_one, div_one,
    meanType]

/-- A wage at which (almost) every hired type has `θ < w` makes a strict loss. -/
theorem firmProfit_neg_of_ae_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) {w : ℝ} (hpos : 0 < μ (acceptSet r w))
    (hlt : ∀ᵐ θ ∂μ, θ ∈ acceptSet r w → θ < w) : firmProfit μ r w < 0 := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, ← neg_pos, ← integral_neg]
  refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet hr w) hpos
    (hlt.mono fun θ hθ hm => by linarith [hθ hm]) ?_
  exact (hd.integrable_id.sub (integrable_const w)).neg.integrableOn

/-- **Footnote 7** (MWG, p. 441). Below `r(θ̲)` no type in `[θ̲, θ̄]` accepts employment. -/
theorem acceptSet_inter_eq_empty {θl θh : ℝ} {r : ℝ → ℝ} (hmono : MonotoneOn r (Set.Icc θl θh))
    {w : ℝ} (hw : w < r θl) : acceptSet r w ∩ Set.Icc θl θh = ∅ := by
  ext θ
  simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro h hθ
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hθ.1.trans hθ.2⟩
  linarith [hmono hl hθ hθ.1]

/-- **Figure 13.B.2** (MWG, pp. 441-442). At `w = r(θ̲)` only the type `θ̲` accepts. -/
theorem acceptSet_inter_eq_singleton {θl θh : ℝ} {r : ℝ → ℝ} (hlt : θl < θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) : acceptSet r (r θl) ∩ Set.Icc θl θh = {θl} := by
  ext θ
  simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hθ⟩
    have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hlt.le⟩
    by_contra hne
    have := hmono hl hθ (lt_of_le_of_ne hθ.1 (Ne.symm hne))
    linarith
  · rintro rfl; exact ⟨le_rfl, le_rfl, hlt.le⟩

/-- **Section 13.B** (MWG, p. 441). With `r` continuous and positive density, every wage above
`r(θ̲)` attracts a set of workers of positive probability. -/
theorem measure_acceptSet_pos {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hden : HasPosDensity μ θl θh) (hcont : ContinuousOn r (Set.Icc θl θh)) {w : ℝ}
    (hw : r θl < w) : 0 < μ (acceptSet r w) := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hev : ∀ᶠ θ in 𝓝[≥] θl, r θ < w := by
    have := (hcont θl hl).eventually (Iio_mem_nhds hw)
    rwa [nhdsWithin_Icc_eq_nhdsGE hd.lt] at this
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  set v := min u θh
  have hv : θl < v := lt_min hu hd.lt
  refine (hden.pos θl v le_rfl hv (min_le_right _ _)).trans_le (measure_mono ?_)
  intro θ hθ
  exact le_of_lt (show r θ < w from hsub ⟨hθ.1, hθ.2.trans (min_le_left _ _)⟩)

/-- **Footnote 7** (MWG, p. 441). No wage below `r(θ̲)` is a competitive equilibrium wage. -/
theorem not_mem_eqWages_of_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : MonotoneOn r (Set.Icc θl θh)) (hrθ : ∀ θ ∈ Set.Icc θl θh, r θ ≤ θ) {w : ℝ}
    (hw : w < r θl) : w ∉ eqWages μ θl θh r := by
  rw [mem_eqWages_iff]
  have hempty := acceptSet_inter_eq_empty hmono hw
  have h0 : μ (acceptSet r w) = 0 := by
    rw [← measure_acceptSet_inter hd, hempty, measure_empty]
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hempty, Set.not_nonempty_empty]
  intro h
  linarith [hd.meanType_mem.1, hrθ θl hl]

/-- **Figure 13.B.2** (MWG, p. 442). `r(θ̲) ∈ W*` iff `r(θ̲) = θ̲`. -/
theorem mem_eqWages_rl_iff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) (hden : HasPosDensity μ θl θh) :
    r θl ∈ eqWages μ θl θh r ↔ r θl = θl := by
  rw [mem_eqWages_iff]
  have hs := acceptSet_inter_eq_singleton hd.lt hmono
  have h0 : μ (acceptSet r (r θl)) = 0 := by
    rw [← measure_acceptSet_inter hd, hs, hden.noAtom]
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hs, Set.singleton_nonempty]

/-- At `w = r(θ̲)` the firm's profit is zero. -/
theorem firmProfit_rl {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) (hden : HasPosDensity μ θl θh) (hr : Measurable r) :
    firmProfit μ r (r θl) = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd, acceptSet_inter_eq_singleton hd.lt hmono, hden.noAtom]

/-- Below `r(θ̲)` the firm's profit is zero. -/
theorem firmProfit_of_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : MonotoneOn r (Set.Icc θl θh)) (hr : Measurable r) {w : ℝ} (hw : w < r θl) :
    firmProfit μ r w = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd, acceptSet_inter_eq_empty hmono hw, measure_empty]

/-- **Section 13.B** (MWG, p. 444). A firm offering `w = 0` never makes a loss: `Π(0) ≥ 0`
(types are nonnegative). -/
theorem firmProfit_zero_nonneg {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) : 0 ≤ firmProfit μ r 0 := by
  rw [firmProfit_eq_setIntegral hr]
  exact setIntegral_nonneg_of_ae_restrict
    (ae_restrict_of_ae (hd.ae_mem.mono fun θ hθ =>
      show (0 : ℝ) ≤ θ - 0 by linarith [hd.nonneg, hθ.1]))

/-- The regular adverse selection model of p. 441, plus continuity of `r`: `F` has a positive
density on `[θ̲, θ̄]`, `r` is measurable, continuous and strictly increasing there, and
`r(θ) ≤ θ`. -/
structure RegularModel (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Prop where
  dist : TypeDist μ θl θh
  dens : HasPosDensity μ θl θh
  meas : Measurable r
  mono : StrictMonoOn r (Set.Icc θl θh)
  cont : ContinuousOn r (Set.Icc θl θh)
  le : ∀ θ ∈ Set.Icc θl θh, r θ ≤ θ

/-- The profit is continuous in the regular model. -/
theorem RegularModel.continuous {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : Continuous (firmProfit μ r) :=
  continuous_firmProfit h.dist h.dens.noAtom h.meas h.mono.injOn

/-- In the regular model, `w > r(θ̲)` is an equilibrium wage iff `Π(w) = 0`. -/
theorem RegularModel.mem_eqWages_iff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w : ℝ} (hw : r θl < w) :
    w ∈ eqWages μ θl θh r ↔ firmProfit μ r w = 0 :=
  mem_eqWages_iff_profit h.dist h.meas (measure_acceptSet_pos h.dist h.dens h.cont hw)

/-- **Section 13.B** (MWG, p. 444). If `w*` is the largest equilibrium wage then
`E[θ | r(θ) ≤ w] < w`, i.e. `Π(w) < 0`, for every `w > w*` (the book's continuity argument,
via the intermediate value theorem). -/
theorem RegularModel.firmProfit_neg_of_gt_max {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) {w : ℝ}
    (hw : ws < w) : firmProfit μ r w < 0 := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hws : r θl ≤ ws := by
    by_contra hlt
    exact not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le (not_le.1 hlt) hmax.1
  have hrw : r θl < w := hws.trans_lt hw
  have hne : firmProfit μ r w ≠ 0 := by
    intro h0
    exact absurd (hmax.2 ((h.mem_eqWages_iff hrw).2 h0)) (not_le.2 hw)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact hneg
  · exfalso
    set b := max w θh + 1
    have hwb : w ≤ b := by simp only [b]; linarith [le_max_left w θh]
    have hbθ : θh < b := by simp only [b]; linarith [le_max_right w θh]
    have hb : firmProfit μ r b < 0 :=
      firmProfit_neg_of_gt h.dist h.meas hbθ
        (measure_acceptSet_pos h.dist h.dens h.cont (hrw.trans_le hwb))
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hwb h.continuous.continuousOn
      ⟨hb.le, hpos.le⟩
    have hcm : c ∈ eqWages μ θl θh r :=
      (h.mem_eqWages_iff (hrw.trans_le hc.1)).2 hc0
    exact absurd (hmax.2 hcm) (not_le.2 (hw.trans_le hc.1))

/-- Between `r(θ̲)` and `θ̲` every hire is profitable. -/
theorem RegularModel.firmProfit_pos_of_lt_θl {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w : ℝ} (hw1 : r θl < w) (hw2 : w < θl) :
    0 < firmProfit μ r w := by
  have := h.dist.prob
  rw [firmProfit_eq_setIntegral h.meas]
  refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet h.meas w)
    (measure_acceptSet_pos h.dist h.dens h.cont hw1)
    (h.dist.ae_mem.mono fun θ hθ _ => by linarith [hθ.1]) ?_
  exact (h.dist.integrable_id.sub (integrable_const w)).integrableOn

/-- **Section 13.B** (MWG, p. 443). In the regular model the set `W*` of competitive equilibrium
wages is nonempty and has a largest element `w* = Max W*`. -/
theorem RegularModel.exists_isGreatest_eqWages {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : ∃ ws, IsGreatest (eqWages μ θl θh r) ws := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hrl := h.le θl hl
  set b := θh + 1
  have hbθ : θh < b := by simp only [b]; linarith
  -- the zero set of the profit between `a` and `b`
  have key : ∀ a, r θl ≤ a → a ≤ b → (a = r θl → r θl = θl) →
      (∃ w ∈ Set.Icc a b, firmProfit μ r w = 0) →
      (∀ w ∈ eqWages μ θl θh r, w < a → r θl = θl ∧ w = r θl ∧ a = r θl) →
      ∃ ws, IsGreatest (eqWages μ θl θh r) ws := by
    intro a ha hab haeq hne hlow
    have hcpt : IsCompact {w | w ∈ Set.Icc a b ∧ firmProfit μ r w = 0} :=
      isCompact_Icc.inter_right (isClosed_eq h.continuous continuous_const)
    obtain ⟨c, ⟨hc, hc0⟩, hcmax⟩ := hcpt.exists_isGreatest hne
    refine ⟨c, ?_, ?_⟩
    · rcases eq_or_lt_of_le (ha.trans hc.1) with heq | hlt
      · rw [← heq]; exact (mem_eqWages_rl_iff h.dist h.mono h.dens).2 (haeq (le_antisymm
          (heq ▸ hc.1) ha) )
      · exact (h.mem_eqWages_iff hlt).2 hc0
    · intro w hw
      by_cases hwa : w < a
      · obtain ⟨_, -, ha'⟩ := hlow w hw hwa
        linarith [hc.1]
      · have hwr : r θl ≤ w := ha.trans (not_lt.1 hwa)
        rcases eq_or_lt_of_le hwr with heq | hlt
        · linarith [hc.1, ha, heq]
        · have h0 := (h.mem_eqWages_iff hlt).1 hw
          have hwb : w ≤ b := by
            by_contra hgt
            exact absurd h0 (firmProfit_neg_of_gt h.dist h.meas (hbθ.trans (not_le.1 hgt))
              (measure_acceptSet_pos h.dist h.dens h.cont hlt)).ne
          exact hcmax ⟨⟨not_lt.1 hwa, hwb⟩, h0⟩
  have hb : firmProfit μ r b < 0 :=
    firmProfit_neg_of_gt h.dist h.meas hbθ
      (measure_acceptSet_pos h.dist h.dens h.cont (by linarith [h.dist.lt]))
  rcases eq_or_lt_of_le hrl with heq | hlt
  · refine key (r θl) le_rfl (by linarith [h.dist.lt]) (fun _ => heq)
      ⟨r θl, ⟨le_rfl, by linarith [h.dist.lt]⟩,
      firmProfit_rl h.dist h.mono h.dens h.meas⟩ ?_
    intro w hw hwa
    exact absurd hw (not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le hwa)
  · set a := (r θl + θl) / 2
    have ha1 : r θl < a := by simp only [a]; linarith
    have ha2 : a < θl := by simp only [a]; linarith
    have hpa := h.firmProfit_pos_of_lt_θl ha1 ha2
    have hab : a ≤ b := by linarith [h.dist.lt]
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab h.continuous.continuousOn ⟨hb.le, hpa.le⟩
    refine key a ha1.le hab (fun h' => absurd h' ha1.ne') ⟨c, hc, hc0⟩ ?_
    intro w hw hwa
    exfalso
    rcases lt_trichotomy w (r θl) with h1 | h1 | h1
    · exact not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le h1 hw
    · rw [h1] at hw
      exact hlt.ne ((mem_eqWages_rl_iff h.dist h.mono h.dens).1 hw)
    · have h0 := (h.mem_eqWages_iff h1).1 hw
      exact (h.firmProfit_pos_of_lt_θl h1 (hwa.trans ha2)).ne' h0

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Monotonicity of `E[θ | r(θ) ≤ w]`

MWG, Section 13.B, p. 441: "It is increasing in the level `w` for wages between `r(θ̲)` and
`r(θ̄)`".

* `condMean_mono_of_sep`, `condMean_lt_of_sep`: enlarging a set by points lying (strictly)
  above all its points raises (strictly) the conditional mean.
* `condMean_acceptSet_mono`: for `r` nondecreasing on `[θ̲, θ̄]`, `w ↦ E[θ | r(θ) ≤ w]` is
  nondecreasing on `[r(θ̲), ∞)` (no density or continuity needed).
* `RegularModel.condMean_acceptSet_strictMono`: in the model of p. 441 (with `r` continuous,
  correction 2) it is strictly increasing on `[r(θ̲), r(θ̄)]`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- Every conditional mean is at least `θ̲`. -/
theorem condMean_ge {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (S : Set ℝ) :
    θl ≤ condMean μ θl θh S := by
  have := hd.prob
  unfold condMean
  split_ifs with hpos hne
  · have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    rw [le_div_iff₀ ha]
    have hle : ∫ θ in S, θl ∂μ ≤ ∫ θ in S, θ ∂μ :=
      integral_mono_ae (integrable_const θl).integrableOn hd.integrable_id.integrableOn
        (ae_restrict_of_ae (hd.ae_mem.mono fun θ hθ => hθ.1))
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hle
    linarith
  · exact le_rfl
  · exact hd.meanType_mem.1

/-- Adding to a set `S` of positive probability points that lie above all points of `S` (within
`[θ̲, θ̄]`) does not lower the conditional mean. -/
theorem condMean_mono_of_sep {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S S' : Set ℝ}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hsub : S ⊆ S') (hpos : 0 < μ S)
    (hsep : ∀ θ ∈ S ∩ Set.Icc θl θh, ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, θ ≤ θ') :
    condMean μ θl θh S ≤ condMean μ θl θh S' := by
  have := hd.prob
  have hpos' : 0 < μ S' := hpos.trans_le (measure_mono hsub)
  have hD : MeasurableSet (S' \ S) := hS'.diff hS
  have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hb : 0 ≤ (μ (S' \ S)).toReal := ENNReal.toReal_nonneg
  have hmeas : (μ S').toReal = (μ S).toReal + (μ (S' \ S)).toReal := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    rw [measure_union Set.disjoint_sdiff_right hD,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hint : ∫ θ in S', θ ∂μ = (∫ θ in S, θ ∂μ) + ∫ θ in S' \ S, θ ∂μ := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right hD hd.integrable_id.integrableOn
      hd.integrable_id.integrableOn
  set m := (∫ θ in S, θ ∂μ) / (μ S).toReal with hmdef
  have hm : ∫ θ in S, θ ∂μ = m * (μ S).toReal := by rw [hmdef, div_mul_cancel₀ _ ha.ne']
  have h1 : ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, m ≤ θ' := by
    intro θ' hθ'
    have hle : ∫ θ in S, θ ∂μ ≤ ∫ θ in S, θ' ∂μ :=
      integral_mono_ae hd.integrable_id.integrableOn (integrable_const θ').integrableOn
        ((ae_restrict_iff' hS).2 (hd.ae_mem.mono fun θ hθ hθS => hsep θ ⟨hθS, hθ⟩ θ' hθ'))
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hle
    rw [hmdef, div_le_iff₀ ha]
    linarith
  have h2 : ∫ θ in S' \ S, m ∂μ ≤ ∫ θ in S' \ S, θ ∂μ :=
    integral_mono_ae (integrable_const m).integrableOn hd.integrable_id.integrableOn
      ((ae_restrict_iff' hD).2 (hd.ae_mem.mono fun θ hθ hθD => h1 θ ⟨hθD, hθ⟩))
  rw [setIntegral_const, smul_eq_mul, Measure.real] at h2
  have hcS : condMean μ θl θh S = m := by simp only [condMean, hpos, ↓reduceIte, hmdef]
  have hcS' : condMean μ θl θh S' = (∫ θ in S', θ ∂μ) / (μ S').toReal := by
    simp only [condMean, hpos', ↓reduceIte]
  rw [hcS, hcS', le_div_iff₀ (by rw [hmeas]; linarith), hint, hmeas]
  nlinarith

/-- The strict version: if the added points lie strictly above all points of `S` and have
positive probability, the conditional mean rises strictly. -/
theorem condMean_lt_of_sep {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S S' : Set ℝ}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hsub : S ⊆ S') (hpos : 0 < μ S)
    (hposD : 0 < μ (S' \ S))
    (hsep : ∀ θ ∈ S ∩ Set.Icc θl θh, ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, θ < θ') :
    condMean μ θl θh S < condMean μ θl θh S' := by
  have := hd.prob
  have hpos' : 0 < μ S' := hpos.trans_le (measure_mono hsub)
  have hD : MeasurableSet (S' \ S) := hS'.diff hS
  have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hb : 0 < (μ (S' \ S)).toReal := ENNReal.toReal_pos hposD.ne' (measure_ne_top _ _)
  have hmeas : (μ S').toReal = (μ S).toReal + (μ (S' \ S)).toReal := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    rw [measure_union Set.disjoint_sdiff_right hD,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hint : ∫ θ in S', θ ∂μ = (∫ θ in S, θ ∂μ) + ∫ θ in S' \ S, θ ∂μ := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right hD hd.integrable_id.integrableOn
      hd.integrable_id.integrableOn
  set m := (∫ θ in S, θ ∂μ) / (μ S).toReal with hmdef
  have hm : ∫ θ in S, θ ∂μ = m * (μ S).toReal := by rw [hmdef, div_mul_cancel₀ _ ha.ne']
  have h1 : ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, m < θ' := by
    intro θ' hθ'
    have hlt : 0 < ∫ θ in S, (θ' - θ) ∂μ :=
      setIntegral_pos_of_ae_pos hS hpos
        (hd.ae_mem.mono fun θ hθ hθS => sub_pos.2 (hsep θ ⟨hθS, hθ⟩ θ' hθ'))
        ((integrable_const θ').sub hd.integrable_id).integrableOn
    rw [integral_sub (integrable_const θ').integrableOn hd.integrable_id.integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    rw [hmdef, div_lt_iff₀ ha]
    linarith
  have h2 : 0 < ∫ θ in S' \ S, (θ - m) ∂μ :=
    setIntegral_pos_of_ae_pos hD hposD
      (hd.ae_mem.mono fun θ hθ hθD => sub_pos.2 (h1 θ ⟨hθD, hθ⟩))
      (hd.integrable_id.sub (integrable_const m)).integrableOn
  rw [integral_sub hd.integrable_id.integrableOn (integrable_const m).integrableOn,
    setIntegral_const, smul_eq_mul, Measure.real] at h2
  have hcS : condMean μ θl θh S = m := by simp only [condMean, hpos, ↓reduceIte, hmdef]
  have hcS' : condMean μ θl θh S' = (∫ θ in S', θ ∂μ) / (μ S').toReal := by
    simp only [condMean, hpos', ↓reduceIte]
  rw [hcS, hcS', lt_div_iff₀ (by rw [hmeas]; linarith), hint, hmeas]
  nlinarith

/-- **Section 13.B** (MWG, p. 441). For `r` nondecreasing on `[θ̲, θ̄]`, `E[θ | r(θ) ≤ w]` is
nondecreasing in `w ≥ r(θ̲)`. Neither a density nor continuity of `r` is needed. -/
theorem condMean_acceptSet_mono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (hd : TypeDist μ θl θh) (hr : Measurable r) (hmono : MonotoneOn r (Set.Icc θl θh))
    {w w' : ℝ} (hw : r θl ≤ w) (hww : w ≤ w') :
    condMean μ θl θh (acceptSet r w) ≤ condMean μ θl θh (acceptSet r w') := by
  rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
  · have hne : (acceptSet r w ∩ Set.Icc θl θh).Nonempty := ⟨θl, hw, le_rfl, hd.lt.le⟩
    have hc : condMean μ θl θh (acceptSet r w) = θl := by
      simp only [condMean, h0, lt_irrefl, ↓reduceIte, hne]
    rw [hc]
    exact condMean_ge hd _
  · refine condMean_mono_of_sep hd (measurableSet_acceptSet hr w)
      (measurableSet_acceptSet hr w') (fun θ hθ => le_trans hθ hww) hpos ?_
    rintro θ ⟨hθ, hθI⟩ θ' ⟨⟨_, hθ'⟩, hθ'I⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hθ' (le_trans (hmono hθ'I hθI hlt.le) hθ)

/-- **Section 13.B** (MWG, p. 441). In the model of p. 441 (`r` strictly increasing and, as in
correction 2, continuous; positive density), `E[θ | r(θ) ≤ w]` is strictly increasing in `w`
on `[r(θ̲), r(θ̄)]`. -/
theorem RegularModel.condMean_acceptSet_strictMono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w w' : ℝ} (hw : r θl ≤ w) (hww : w < w')
    (hw' : w' ≤ r θh) :
    condMean μ θl θh (acceptSet r w) < condMean μ θl θh (acceptSet r w') := by
  have hd := h.dist
  have := hd.prob
  have hI : Set.Icc (r θl) (r θh) ⊆ r '' Set.Icc θl θh :=
    intermediate_value_Icc hd.lt.le h.cont
  obtain ⟨θ1, hθ1I, hθ1⟩ := hI ⟨hw, hww.le.trans hw'⟩
  obtain ⟨θ2, hθ2I, hθ2⟩ := hI ⟨hw.trans hww.le, hw'⟩
  have h12 : θ1 < θ2 := by
    by_contra hle
    rw [not_lt] at hle
    have := h.mono.monotoneOn hθ2I hθ1I hle
    linarith
  set c := (θ1 + θ2) / 2 with hc
  have hsubD : Set.Icc c θ2 ⊆ acceptSet r w' \ acceptSet r w := by
    intro θ hθ
    have hθI : θ ∈ Set.Icc θl θh := ⟨by linarith [hθ1I.1, hθ.1, hc], hθ.2.trans hθ2I.2⟩
    refine ⟨?_, ?_⟩
    · change r θ ≤ w'
      rw [← hθ2]; exact h.mono.monotoneOn hθI hθ2I hθ.2
    · change ¬ r θ ≤ w
      rw [← hθ1, not_le]; exact h.mono hθ1I hθI (by linarith [hθ.1, hc])
  have hposD : 0 < μ (acceptSet r w' \ acceptSet r w) :=
    (h.dens.pos c θ2 (by linarith [hθ1I.1, hc]) (by linarith [hc]) hθ2I.2).trans_le
      (measure_mono hsubD)
  have hS' : MeasurableSet (acceptSet r w') := measurableSet_acceptSet h.meas w'
  rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
  · have hne : (acceptSet r w ∩ Set.Icc θl θh).Nonempty := ⟨θl, hw, le_rfl, hd.lt.le⟩
    have hc : condMean μ θl θh (acceptSet r w) = θl := by
      simp only [condMean, h0, lt_irrefl, ↓reduceIte, hne]
    rw [hc]
    have hpos' : 0 < μ (acceptSet r w') := hposD.trans_le (measure_mono Set.sdiff_subset)
    have hae : ∀ᵐ θ ∂μ, θ ≠ θl := by
      rw [ae_iff]; simpa using h.dens.noAtom θl
    have hlt : 0 < ∫ θ in acceptSet r w', (θ - θl) ∂μ :=
      setIntegral_pos_of_ae_pos hS' hpos'
        ((hd.ae_mem.and hae).mono fun θ hθ _ => sub_pos.2 (lt_of_le_of_ne hθ.1.1 hθ.2.symm))
        (hd.integrable_id.sub (integrable_const θl)).integrableOn
    rw [integral_sub hd.integrable_id.integrableOn (integrable_const θl).integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    have ha : 0 < (μ (acceptSet r w')).toReal := ENNReal.toReal_pos hpos'.ne' (measure_ne_top _ _)
    simp only [condMean, hpos', ↓reduceIte]
    rw [lt_div_iff₀ ha]
    linarith
  · refine condMean_lt_of_sep hd (measurableSet_acceptSet h.meas w) hS'
      (fun θ hθ => le_trans hθ hww.le) hpos hposD ?_
    rintro θ ⟨hθ, hθI⟩ θ' ⟨⟨_, hθ'⟩, hθ'I⟩
    by_contra hle
    rw [not_lt] at hle
    exact hθ' (le_trans (h.mono.monotoneOn hθ'I hθI hle) hθ)

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two firms simultaneously announcing wages

MWG, Sections 13.B (pp. 443-445) and 13.C (p. 452).

In stage 1 two firms announce wages; in stage 2 each worker accepts a highest wage if it is at
least her reservation value, choosing between tied firms with equal probability (MWG, p. 443,
footnote 12). A firm whose wage is the strictly highest earns the profit `P(w)` of hiring every
worker who accepts `w`; with a tie each firm earns `P(w)/2`; a firm with the lower wage earns
nothing. Given this (optimal) behaviour of the workers, the pure strategy SPNE are the pure Nash
equilibria of the firms' wage game `wageGame P`, a normal form game of Chapter 8
(`MWG.NoncooperativeGames.NormalForm`, `MWG.SimultaneousMoveGames.IsNashEquilibrium`).

* `isNash_wageGame_iff`: the Nash condition firm by firm.
* `wageGame_unique`: if `P` is right-continuous, `P(0) ≥ 0`, `P(w*) = 0`, `P < 0` above `w*` and
  `P > 0` just below `w*`, the unique pure equilibrium is `(w*, w*)` (the argument of
  Proposition 13.B.1(i), and the Bertrand argument of Section 13.C, p. 452).
* `wageGame_flat`: if `P = 0` up to `w*` and `P < 0` above, the pure equilibria are exactly the
  profiles with both wages at most `w*` (the argument of Proposition 13.B.1(ii)).
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Filter Topology

/-- **Section 13.B** (MWG, p. 443). A firm's share of the profit `P` of its wage `own` when the
other firm offers `other`: all of it when `own` is strictly higher, half with a tie, none when
`own` is lower. -/
noncomputable def wageShare (own other P : ℝ) : ℝ :=
  if other < own then P else if own = other then P / 2 else 0

/-- **Section 13.B** (MWG, p. 443). The firms' stage-1 wage game: firm `i` announces `w i` and
earns its share of `P (w i)`. -/
noncomputable def wageGame (P : ℝ → ℝ) : NormalForm (Fin 2) (fun _ => ℝ) where
  payoff i w := wageShare (w i) (w (1 - i)) (P (w i))

/-- Firm `own`'s wage is a best reply to `other`. -/
def WageBestReply (P : ℝ → ℝ) (own other : ℝ) : Prop :=
  ∀ t, wageShare t other (P t) ≤ wageShare own other (P own)

/-- **Section 13.B** (MWG, p. 443). The Nash condition of the wage game, firm by firm. -/
theorem isNash_wageGame_iff (P : ℝ → ℝ) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔
      WageBestReply P (w 0) (w 1) ∧ WageBestReply P (w 1) (w 0) := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have := h 0 t
      simpa [wageGame, Function.update] using this
    · have := h 1 t
      simpa [wageGame, Function.update] using this
  · rintro ⟨h0, h1⟩ i t
    fin_cases i
    · simpa [wageGame, Function.update] using h0 t
    · simpa [wageGame, Function.update] using h1 t

/-- A share of a nonnegative profit is nonnegative. -/
theorem wageShare_nonneg {own other P : ℝ} (h : 0 ≤ P) : 0 ≤ wageShare own other P := by
  unfold wageShare; split_ifs <;> linarith

theorem wageShare_of_gt {own other P : ℝ} (h : other < own) : wageShare own other P = P := by
  simp [wageShare, h]

theorem wageShare_of_eq {own P : ℝ} : wageShare own own P = P / 2 := by
  simp [wageShare]

theorem wageShare_of_lt {own other P : ℝ} (h : own < other) : wageShare own other P = 0 := by
  simp [wageShare, not_lt.2 h.le, h.ne]

/-- With a safe wage earning `P(0) ≥ 0`, a best reply earns at least `0`. -/
theorem WageBestReply.nonneg {P : ℝ → ℝ} {own other : ℝ} (h : WageBestReply P own other)
    (h0 : 0 ≤ P 0) : 0 ≤ wageShare own other (P own) :=
  (wageShare_nonneg h0).trans (h 0)

/-- **Proposition 13.B.1**, proof (MWG, p. 444). The weakly lower-wage firm can capture the whole
market by raising its wage slightly: at a best reply with `own ≤ other`, `P(other) ≤ 0`. Only
right-continuity of `P` is used. -/
theorem WageBestReply.profit_nonpos {P : ℝ → ℝ} (hP : ∀ x, ContinuousWithinAt P (Set.Ici x) x)
    {own other : ℝ} (h : WageBestReply P own other) (hle : own ≤ other) : P other ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hev : ∀ᶠ x in 𝓝[≥] other, P other / 2 < P x :=
    (hP other).eventually (lt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  have hx : P other / 2 < P u := hsub ⟨hu.le, le_rfl⟩
  have hdev := h u
  rw [wageShare_of_gt hu] at hdev
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, wageShare_of_eq] at hdev; linarith
  · rw [wageShare_of_lt hlt] at hdev; linarith

/-- **Proposition 13.B.1(i)**, the argument (MWG, p. 444); also the Bertrand argument of
Section 13.C (p. 452). Let `P` be continuous with `P(0) ≥ 0`, `P(w*) = 0`, `P(w) < 0` for
`w > w*` and `P(w) > 0` for `w ∈ (w* - ε, w*)`. Then `(w*, w*)` is the unique pure Nash
equilibrium of the wage game. -/
theorem wageGame_unique {P : ℝ → ℝ} (hP : ∀ x, ContinuousWithinAt P (Set.Ici x) x)
    (h0 : 0 ≤ P 0) {ws ε : ℝ}
    (hε : 0 < ε) (hws : P ws = 0) (habove : ∀ w, ws < w → P w < 0)
    (hbelow : ∀ w, ws - ε < w → w < ws → 0 < P w) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 = ws ∧ w 1 = ws := by
  rw [isNash_wageGame_iff]
  -- a profitable deviation just below `w*` and above any `x < w*`
  have hdev : ∀ x, x < ws → ∃ t, x < t ∧ 0 < P t := by
    intro x hx
    refine ⟨(max x (ws - ε) + ws) / 2, ?_, hbelow _ ?_ ?_⟩
    · have := le_max_left x (ws - ε); linarith
    · have := le_max_right x (ws - ε); linarith
    · have : max x (ws - ε) < ws := max_lt hx (by linarith)
      linarith
  -- the core argument for a pair with `own ≤ other`
  have core : ∀ a b, a ≤ b → WageBestReply P a b → WageBestReply P b a → a = ws ∧ b = ws := by
    intro a b hab ha hb
    have hPb : P b ≤ 0 := ha.profit_nonpos hP hab
    have hub := hb.nonneg h0
    have hPb0 : P b = 0 := by
      rcases eq_or_lt_of_le hab with heq | hlt
      · rw [heq, wageShare_of_eq] at hub; linarith
      · rw [wageShare_of_gt hlt] at hub; linarith
    have hbws : ws ≤ b := by
      by_contra hlt
      obtain ⟨t, hbt, ht⟩ := hdev b (not_le.1 hlt)
      have := ha t
      rw [wageShare_of_gt hbt] at this
      rcases eq_or_lt_of_le hab with heq | hlt'
      · rw [heq, wageShare_of_eq, hPb0] at this; linarith
      · rw [wageShare_of_lt hlt'] at this; linarith
    have hbws' : b = ws := by
      by_contra hne
      exact absurd hPb0 (habove b (lt_of_le_of_ne hbws (Ne.symm hne))).ne
    refine ⟨?_, hbws'⟩
    by_contra hne
    have halt : a < ws := lt_of_le_of_ne (hbws' ▸ hab) hne
    obtain ⟨t, hat, ht⟩ := hdev a halt
    have := hb t
    rw [wageShare_of_gt hat, wageShare_of_gt (hbws' ▸ halt), hPb0] at this
    linarith
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total (w 0) (w 1) with hle | hle
    · exact core _ _ hle h1 h2
    · exact (core _ _ hle h2 h1).symm
  · rintro ⟨e0, e1⟩
    have br : WageBestReply P ws ws := by
      intro t
      rw [wageShare_of_eq, hws, zero_div]
      rcases lt_trichotomy t ws with ht | ht | ht
      · rw [wageShare_of_lt ht]
      · rw [ht, wageShare_of_eq, hws, zero_div]
      · rw [wageShare_of_gt ht]; exact (habove t ht).le
    rw [e0, e1]
    exact ⟨br, br⟩

/-- **Proposition 13.B.1(ii)**, the argument (MWG, pp. 444-445). If `P(w) = 0` for `w ≤ w*` and
`P(w) < 0` for `w > w*`, the pure Nash equilibria of the wage game are exactly the profiles with
both wages at most `w*`. -/
theorem wageGame_flat {P : ℝ → ℝ} {ws : ℝ} (hflat : ∀ w, w ≤ ws → P w = 0)
    (habove : ∀ w, ws < w → P w < 0) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 ≤ ws ∧ w 1 ≤ ws := by
  rw [isNash_wageGame_iff]
  have hshare : ∀ t o, t ≤ ws → wageShare t o (P t) = 0 := by
    intro t o ht
    rw [hflat t ht]; unfold wageShare; split_ifs <;> simp
  have hneg : ∀ a b, b ≤ a → ws < a → wageShare a b (P a) < 0 := by
    intro a b hba ha
    rcases eq_or_lt_of_le hba with heq | hlt
    · rw [heq, wageShare_of_eq]; linarith [habove a ha]
    · rw [wageShare_of_gt hlt]; exact habove a ha
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    rcases le_total (w 0) (w 1) with hle | hle
    · have hw1 : ws < w 1 := hcon.elim (fun h => h.trans_le hle) id
      have := h2 ws
      rw [hshare ws _ le_rfl] at this
      linarith [hneg _ _ hle hw1]
    · have hw0 : ws < w 0 := hcon.elim id (fun h => h.trans_le hle)
      have := h1 ws
      rw [hshare ws _ le_rfl] at this
      linarith [hneg _ _ hle hw0]
  · rintro ⟨h0, h1⟩
    have br : ∀ a b, a ≤ ws → b ≤ ws → WageBestReply P a b := by
      intro a b ha hb t
      rw [hshare a b ha]
      by_cases ht : t ≤ ws
      · rw [hshare t b ht]
      · exact (hneg t b (hb.trans (not_le.1 ht).le) (not_le.1 ht)).le
    exact ⟨br _ _ h0 h1, br _ _ h1 h0⟩

/-- **Section 13.C** (MWG, p. 459, small type). If `P(w) = 0` for `w < w̄` and `P(w) < 0` for
`w ≥ w̄`, the pure Nash equilibria of the wage game are the profiles with both wages below
`w̄`. -/
theorem wageGame_flat_open {P : ℝ → ℝ} {ws : ℝ} (hflat : ∀ w, w < ws → P w = 0)
    (habove : ∀ w, ws ≤ w → P w < 0) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 < ws ∧ w 1 < ws := by
  rw [isNash_wageGame_iff]
  have hshare : ∀ t o, t < ws → wageShare t o (P t) = 0 := by
    intro t o ht
    rw [hflat t ht]; unfold wageShare; split_ifs <;> simp
  have hneg : ∀ a b, b ≤ a → ws ≤ a → wageShare a b (P a) < 0 := by
    intro a b hba ha
    rcases eq_or_lt_of_le hba with heq | hlt
    · rw [heq, wageShare_of_eq]; linarith [habove a ha]
    · rw [wageShare_of_gt hlt]; exact habove a ha
  have hlow : ws - 1 < ws := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    rw [not_and_or, not_lt, not_lt] at hcon
    rcases le_total (w 0) (w 1) with hle | hle
    · have hw1 : ws ≤ w 1 := hcon.elim (fun h => h.trans hle) id
      have := h2 (ws - 1)
      rw [hshare _ _ hlow] at this
      linarith [hneg _ _ hle hw1]
    · have hw0 : ws ≤ w 0 := hcon.elim id (fun h => h.trans hle)
      have := h1 (ws - 1)
      rw [hshare _ _ hlow] at this
      linarith [hneg _ _ hle hw0]
  · rintro ⟨h0, h1⟩
    have br : ∀ a b, a < ws → b < ws → WageBestReply P a b := by
      intro a b ha hb t
      rw [hshare a b ha]
      by_cases ht : t < ws
      · rw [hshare t b ht]
      · exact (hneg t b (hb.le.trans (not_lt.1 ht)) (not_lt.1 ht)).le
    exact ⟨br _ _ h0 h1, br _ _ h1 h0⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The game-theoretic approach: Proposition 13.B.1

MWG, Section 13.B, pp. 443-445.

Two firms announce wages; workers then accept a highest wage if it is at least `r(θ)` (and are
indifferent otherwise only on ties, footnote 12). `worker_best` records that this is optimal for
the workers, so the pure SPNE are the pure Nash equilibria of `wageGame (firmProfit μ r)`.

* `proposition_13_B_1_i`: if `w* = Max W* > r(θ̲)` and `E[θ | r(θ) ≤ w'] > w'` just below `w*`,
  the unique pure SPNE has both firms offering `w*`; then exactly the types in `Θ(w*)` are
  employed and each earns `w*` (`proposition_13_B_1_i_outcome`).
* `proposition_13_B_1_ii`: if `w* = r(θ̲)`, the pure SPNE are exactly the wage pairs with both
  wages at most `w*`; there are several (`proposition_13_B_1_ii_multiple`) and in each firms earn
  zero and a worker of type `θ` earns `r(θ)`, as in the highest-wage competitive equilibrium.

Departure (correction 2). The proposition assumes only that `r` is strictly increasing. We add
that `r` is continuous on `[θ̲, θ̄]` (part of `RegularModel`): the proof's deviation to a wage just
below `w*` is profitable only if it attracts workers of positive probability. Without continuity
part (i) is false: `counterexample_13_B_1_i` (types uniform on `[1, 2]`, `r(1) = 0` and
`r(θ) = θ` for `θ > 1`) satisfies every printed hypothesis with `W* = {1}`, yet `(1/2, 1/2)` is
also a pure SPNE.
-/

namespace MWG.AdverseSelection

open MeasureTheory MWG.SimultaneousMoveGames

/-- **Section 13.B** (MWG, p. 444). In stage 2 a worker of type `θ` facing wages `w₀, w₁` earns at
most `max (max w₀ w₁) (r θ)`, which she attains by accepting a highest wage when it is at least
`r(θ)` and staying home otherwise. -/
theorem worker_best (rθ w₀ w₁ : ℝ) :
    (w₀ ≤ max (max w₀ w₁) rθ ∧ w₁ ≤ max (max w₀ w₁) rθ ∧ rθ ≤ max (max w₀ w₁) rθ) ∧
      (rθ ≤ max w₀ w₁ → max (max w₀ w₁) rθ = max w₀ w₁) ∧
      (max w₀ w₁ < rθ → max (max w₀ w₁) rθ = rθ) := by
  refine ⟨⟨?_, ?_, le_max_right _ _⟩, fun h => max_eq_left h, fun h => max_eq_right h.le⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)

/-- **Proposition 13.B.1(i)** (MWG, pp. 443-444). In the adverse selection model (with `r`
continuous, see correction 2), let `w* = Max W* > r(θ̲)` and suppose `E[θ | r(θ) ≤ w'] > w'` for
`w' ∈ (w* - ε, w*)`. Then the unique pure strategy SPNE has both firms offering `w*`. -/
theorem proposition_13_B_1_i {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : RegularModel μ θl θh r)
    {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) (hws : r θl < ws) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ w', ws - ε < w' → w' < ws → w' < condMean μ θl θh (acceptSet r w'))
    (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) w ↔ w 0 = ws ∧ w 1 = ws := by
  have := h.dist.prob
  refine wageGame_unique (fun x => h.continuous.continuousAt.continuousWithinAt)
    (firmProfit_zero_nonneg h.dist h.meas)
    (ε := min ε (ws - r θl)) (lt_min hε (by linarith)) ((h.mem_eqWages_iff hws).1 hmax.1)
    (fun w hw => h.firmProfit_neg_of_gt_max hmax hw) ?_ w
  intro w' h1 h2
  have h1' : ws - ε < w' := lt_of_le_of_lt (by linarith [min_le_left ε (ws - r θl)]) h1
  have hr' : r θl < w' := lt_of_le_of_lt (by linarith [min_le_right ε (ws - r θl)]) h1
  have hpos := measure_acceptSet_pos h.dist h.dens h.cont hr'
  rw [firmProfit_eq h.dist h.meas hpos]
  exact mul_pos (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))
    (sub_pos.2 (hgap w' h1' h2))

/-- **Proposition 13.B.1(i)** (MWG, pp. 443-444), the outcome: in the SPNE employed workers
receive `w*` and a worker of type `θ` accepts employment iff `θ ∈ Θ(w*)`. -/
theorem proposition_13_B_1_i_outcome {r : ℝ → ℝ} {ws : ℝ} (w : Fin 2 → ℝ)
    (hw : w 0 = ws ∧ w 1 = ws) (θ : ℝ) :
    max (w 0) (w 1) = ws ∧ (r θ ≤ max (w 0) (w 1) ↔ θ ∈ acceptSet r ws) := by
  rw [hw.1, hw.2, max_self]
  exact ⟨rfl, Iff.rfl⟩

/-- **Proposition 13.B.1(ii)** (MWG, pp. 444-445). In the adverse selection model, if
`w* = Max W* = r(θ̲)`, the pure strategy SPNE are exactly the wage pairs `(w₁, w₂)` with
`wⱼ ≤ w*`. -/
theorem proposition_13_B_1_ii {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) w ↔ w 0 ≤ ws ∧ w 1 ≤ ws := by
  refine wageGame_flat (fun t ht => ?_) (fun t ht => h.firmProfit_neg_of_gt_max hmax ht) w
  rcases eq_or_lt_of_le (hws ▸ ht) with heq | hlt
  · rw [heq]; exact firmProfit_rl h.dist h.mono h.dens h.meas
  · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt

/-- **Proposition 13.B.1(ii)** (MWG, p. 444). There are multiple pure SPNEs. -/
theorem proposition_13_B_1_ii_multiple {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) ![ws, ws] ∧
      IsNashEquilibrium (wageGame (firmProfit μ r)) ![ws - 1, ws] ∧
      (![ws, ws] : Fin 2 → ℝ) ≠ ![ws - 1, ws] := by
  refine ⟨(proposition_13_B_1_ii h hmax hws _).2 (by simp),
    (proposition_13_B_1_ii h hmax hws _).2 (by simp), fun he => ?_⟩
  have := congrFun he 0
  simp at this
  linarith

/-- **Proposition 13.B.1(ii)** (MWG, p. 445). In every pure SPNE both firms earn zero and a
worker of type `θ ∈ [θ̲, θ̄]` earns `r(θ)`, exactly her payoff in the competitive equilibrium
with wage `w*`. -/
theorem proposition_13_B_1_ii_payoffs {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) (w : Fin 2 → ℝ)
    (hne : IsNashEquilibrium (wageGame (firmProfit μ r)) w) :
    (∀ i, (wageGame (firmProfit μ r)).payoff i w = 0) ∧
      ∀ θ ∈ Set.Icc θl θh, max (max (w 0) (w 1)) (r θ) = r θ ∧ max ws (r θ) = r θ := by
  obtain ⟨h0, h1⟩ := (proposition_13_B_1_ii h hmax hws w).1 hne
  have hP : ∀ t, t ≤ ws → firmProfit μ r t = 0 := fun t ht => by
    rcases eq_or_lt_of_le (hws ▸ ht) with heq | hlt
    · rw [heq]; exact firmProfit_rl h.dist h.mono h.dens h.meas
    · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt
  refine ⟨fun i => ?_, fun θ hθ => ?_⟩
  · have hi : w i ≤ ws := by fin_cases i <;> simpa
    simp only [wageGame, hP _ hi]
    unfold wageShare; split_ifs <;> simp
  · have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
    have hrθ : ws ≤ r θ := hws ▸ h.mono.monotoneOn hl hθ hθ.1
    exact ⟨max_eq_right ((max_le h0 h1).trans hrθ), max_eq_right hrθ⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Uniformly distributed types

MWG, Section 13.B, p. 442 (Example 13.B.1) and the concrete instances of this chapter.

`unifMeas a b` is the uniform distribution on `[a, b]`. We prove that it satisfies the standing
assumptions (`TypeDist`, `HasPosDensity`) and compute `F(c)` and `∫_{θ ≤ c} θ dF` for
`a ≤ c ≤ b`.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- The uniform distribution on `[a, b]`. -/
noncomputable def unifMeas (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

theorem unifMeas_apply {a b : ℝ} (hab : a < b) {S : Set ℝ} (hS : MeasurableSet S) :
    unifMeas a b S = ENNReal.ofReal ((volume (S ∩ Icc a b)).toReal / (b - a)) := by
  have hfin : volume (S ∩ Icc a b) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (by simp [Real.volume_Icc])
  rw [unifMeas, Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul,
    ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_toReal hfin, div_eq_mul_inv, mul_comm]

theorem unifMeas_isProb {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (unifMeas a b) := by
  constructor
  rw [unifMeas_apply hab MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), div_self (by linarith), ENNReal.ofReal_one]

theorem unifMeas_compl {a b : ℝ} (hab : a < b) : unifMeas a b (Icc a b)ᶜ = 0 := by
  rw [unifMeas_apply hab measurableSet_Icc.compl, compl_inter_self, measure_empty,
    ENNReal.toReal_zero, zero_div, ENNReal.ofReal_zero]

theorem Iic_inter_Icc_of_le {a b c : ℝ} (hcb : c ≤ b) : Iic c ∩ Icc a b = Icc a c := by
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hcb⟩

/-- The uniform distribution on `[a, b]`, `0 ≤ a < b`, satisfies the standing assumptions. -/
theorem unifMeas_typeDist {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : TypeDist (unifMeas a b) a b where
  nonneg := ha
  lt := hab
  prob := unifMeas_isProb hab
  supp := unifMeas_compl hab

/-- The uniform distribution has a positive density. -/
theorem unifMeas_density {a b : ℝ} (hab : a < b) : HasPosDensity (unifMeas a b) a b where
  noAtom x := by
    rw [unifMeas_apply hab (measurableSet_singleton x)]
    have : volume ({x} ∩ Icc a b) = 0 := measure_mono_null inter_subset_left (by simp)
    rw [this]; simp
  pos c d hc hcd hd := by
    rw [unifMeas_apply hab measurableSet_Icc, Icc_inter_Icc, max_eq_left hc, min_eq_left hd,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    exact ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))

/-- `F(c) = (c - a)/(b - a)` for the uniform distribution. -/
theorem unifMeas_Iic {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    unifMeas a b (Iic c) = ENNReal.ofReal ((c - a) / (b - a)) := by
  rw [unifMeas_apply hab measurableSet_Iic, Iic_inter_Icc_of_le hcb, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

/-- `∫_{θ ≤ c} θ dF = (c² - a²) / (2 (b - a))` for the uniform distribution. -/
theorem unifMeas_setIntegral_Iic {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ θ in Iic c, θ ∂(unifMeas a b) = (c ^ 2 - a ^ 2) / (2 * (b - a)) := by
  rw [unifMeas, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict
    measurableSet_Iic, Iic_inter_Icc_of_le hcb, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hac, integral_id, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  field_simp

/-- `E[θ] = (a + b)/2` for the uniform distribution. -/
theorem unifMeas_mean {a b : ℝ} (hab : a < b) : meanType (unifMeas a b) = (a + b) / 2 := by
  have h := unifMeas_setIntegral_Iic hab hab.le le_rfl
  have hfull : ∫ θ in Iic b, θ ∂(unifMeas a b) = ∫ θ, θ ∂(unifMeas a b) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    have hs : ∀ᵐ θ ∂(unifMeas a b), θ ∈ Icc a b :=
      measure_eq_zero_iff_ae_notMem.1 (unifMeas_compl hab) |>.mono fun _ hx => by simpa using hx
    filter_upwards [hs] with θ hθ hθc
    exact absurd hθ.2 hθc
  rw [meanType, ← hfull, h]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Market unraveling: Example 13.B.1, and the counterexample to Proposition 13.B.1(i)

MWG, Section 13.B, pp. 442-445.

* `example_13_B_1`: with `r(θ) = αθ` (`0 < α < 1`) and `θ` uniform on `[0, 2]`,
  `E[θ | r(θ) ≤ w] = w/(2α)` for `0 < w ≤ 2α`; for `α > 1/2`, `E[θ | r(θ) ≤ 0] = 0` and
  `E[θ | r(θ) ≤ w] < w` for every `w > 0`, so `W* = {0}`: complete market failure (Figure 13.B.2).
  Akerlof's case `α = 2/3` (footnote 10) is `example_13_B_1_akerlof`. Proposition 13.B.1(ii)
  applies (`example_13_B_1_spne`).
* `example_13_B_1_lowα`: for `α < 1/2`, `W* = {0, 1}` with `Max W* = 1 > r(θ̲)`, an instance of
  Proposition 13.B.1(i) (`proposition_13_B_1_i_instance`).
* `counterexample_13_B_1_i` (correction 2): Proposition 13.B.1(i) fails when `r` is strictly
  increasing but discontinuous.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set MWG.SimultaneousMoveGames

/-- **Example 13.B.1** (MWG, p. 442). The home-production function `r(θ) = αθ`. -/
def akerlofR (α : ℝ) : ℝ → ℝ := fun θ => α * θ

theorem acceptSet_akerlofR {α : ℝ} (hα : 0 < α) (w : ℝ) :
    acceptSet (akerlofR α) w = Iic (w / α) := by
  ext θ
  simp only [acceptSet, akerlofR, mem_ofPred_eq, mem_Iic, le_div_iff₀ hα]
  rw [mul_comm]

/-- **Example 13.B.1** (MWG, p. 442). The model with `r(θ) = αθ`, `0 < α < 1`, and `θ` uniform on
`[0, 2]` satisfies the assumptions of p. 441. -/
theorem akerlof_regular {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    RegularModel (unifMeas 0 2) 0 2 (akerlofR α) where
  dist := unifMeas_typeDist le_rfl two_pos
  dens := unifMeas_density two_pos
  meas := measurable_const.mul measurable_id
  mono := fun a _ b _ hab => mul_lt_mul_of_pos_left hab hα
  cont := (continuous_const.mul continuous_id).continuousOn
  le := fun θ hθ => by simp only [akerlofR]; nlinarith [hθ.1]

/-- **Example 13.B.1** (MWG, p. 442). `E[θ | r(θ) ≤ w] = w/(2α)` for `0 < w ≤ 2α`. -/
theorem example_13_B_1 {α w : ℝ} (hα : 0 < α) (hw : 0 < w) (hw2 : w ≤ 2 * α) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) = w / (2 * α) := by
  have hc0 : 0 ≤ w / α := (div_pos hw hα).le
  have hc2 : w / α ≤ 2 := (div_le_iff₀ hα).2 (by linarith)
  have hcpos : 0 < w / α := div_pos hw hα
  rw [acceptSet_akerlofR hα]
  have hμ := unifMeas_Iic (a := 0) (b := 2) two_pos hc0 hc2
  have hpos : 0 < unifMeas 0 2 (Iic (w / α)) := by
    rw [hμ]; exact ENNReal.ofReal_pos.2 (by positivity)
  simp only [condMean, hpos, ↓reduceIte]
  rw [unifMeas_setIntegral_Iic two_pos hc0 hc2, hμ, ENNReal.toReal_ofReal (by positivity)]
  have hw0 : w ≠ 0 := hw.ne'
  field_simp
  rw [div_eq_iff (by simpa using hw0)]
  ring

/-- **Example 13.B.1** (MWG, p. 442). `E[θ | r(θ) ≤ 0] = 0`. -/
theorem example_13_B_1_zero {α : ℝ} (hα : 0 < α) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) 0) = 0 := by
  rw [acceptSet_akerlofR hα, zero_div]
  have h0 : unifMeas 0 2 (Iic 0) = 0 := by
    rw [unifMeas_Iic two_pos le_rfl zero_le_two]; simp
  have hne : (Iic (0 : ℝ) ∩ Icc 0 2).Nonempty := ⟨0, by simp⟩
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne]

/-- **Example 13.B.1** (MWG, p. 442). Above `2α` every type accepts, so
`E[θ | r(θ) ≤ w] = E[θ] = 1`. -/
theorem example_13_B_1_high {α w : ℝ} (hα : 0 < α) (hw : 2 * α ≤ w) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) = 1 := by
  rw [condMean_of_superset (unifMeas_typeDist le_rfl two_pos), unifMeas_mean two_pos]
  · norm_num
  · intro θ hθ
    simp only [acceptSet, akerlofR, mem_ofPred_eq]
    nlinarith [hθ.1, hθ.2]

/-- **Example 13.B.1** (MWG, p. 442). For `α > 1/2`, `E[θ | r(θ) ≤ w] < w` for all `w > 0`. -/
theorem example_13_B_1_lt {α w : ℝ} (hα : 1 / 2 < α) (hw : 0 < w) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) < w := by
  have hα0 : 0 < α := by linarith
  rcases le_or_gt w (2 * α) with h | h
  · rw [example_13_B_1 hα0 hw h, div_lt_iff₀ (by linarith)]
    nlinarith
  · rw [example_13_B_1_high hα0 h.le]; linarith

/-- **Example 13.B.1, Figure 13.B.2** (MWG, p. 442). For `1/2 < α < 1` the only competitive
equilibrium wage is `w* = θ̲ = 0`: the market unravels completely. -/
theorem example_13_B_1_unravel {α : ℝ} (hα : 1 / 2 < α) :
    eqWages (unifMeas 0 2) 0 2 (akerlofR α) = {0} := by
  have hα0 : 0 < α := by linarith
  ext w
  rw [mem_eqWages_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases lt_trichotomy w 0 with hw | hw | hw
    · have hne : ¬ (acceptSet (akerlofR α) w ∩ Icc 0 2).Nonempty := by
        rintro ⟨θ, h1, h2⟩
        simp only [acceptSet, akerlofR, mem_ofPred_eq] at h1
        nlinarith [h2.1]
      have h0 : unifMeas 0 2 (acceptSet (akerlofR α) w) = 0 := by
        rw [← measure_acceptSet_inter (unifMeas_typeDist le_rfl two_pos),
          not_nonempty_iff_eq_empty.1 hne, measure_empty]
      simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne, unifMeas_mean two_pos] at h
      linarith
    · exact hw
    · exact absurd h (example_13_B_1_lt hα hw).ne'
  · rintro rfl; exact (example_13_B_1_zero hα0).symm

/-- **Footnote 10** (MWG, p. 442). Akerlof's case `α = 2/3`. -/
theorem example_13_B_1_akerlof : eqWages (unifMeas 0 2) 0 2 (akerlofR (2 / 3)) = {0} :=
  example_13_B_1_unravel (by norm_num)

/-- **Example 13.B.1 with Proposition 13.B.1(ii)** (MWG, pp. 442-445). For `1/2 < α < 1` the
pure SPNE of the wage game are exactly the pairs of wages `≤ 0`. -/
theorem example_13_B_1_spne {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit (unifMeas 0 2) (akerlofR α))) w ↔
      w 0 ≤ 0 ∧ w 1 ≤ 0 := by
  refine proposition_13_B_1_ii (akerlof_regular (by linarith) hα1) ?_ (by simp [akerlofR]) w
  rw [example_13_B_1_unravel hα]
  exact ⟨rfl, fun x hx => le_of_eq hx⟩

/-- **Example 13.B.1, `α < 1/2`** (MWG, pp. 442-443). Then `W* = {0, 1}`. -/
theorem example_13_B_1_lowα {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) :
    eqWages (unifMeas 0 2) 0 2 (akerlofR α) = {0, 1} := by
  ext w
  rw [mem_eqWages_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases lt_trichotomy w 0 with hw | hw | hw
    · exfalso
      have hne : ¬ (acceptSet (akerlofR α) w ∩ Icc 0 2).Nonempty := by
        rintro ⟨θ, h1, h2⟩
        simp only [acceptSet, akerlofR, mem_ofPred_eq] at h1
        nlinarith [h2.1]
      have h0 : unifMeas 0 2 (acceptSet (akerlofR α) w) = 0 := by
        rw [← measure_acceptSet_inter (unifMeas_typeDist le_rfl two_pos),
          not_nonempty_iff_eq_empty.1 hne, measure_empty]
      simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne, unifMeas_mean two_pos] at h
      linarith
    · exact Or.inl hw
    · right
      rcases le_or_gt w (2 * α) with h2 | h2
      · rw [example_13_B_1 hα hw h2] at h
        exfalso
        have : w * (2 * α) = w := by field_simp at h; linarith
        nlinarith
      · rw [example_13_B_1_high hα h2.le] at h; exact h
  · rintro (rfl | rfl)
    · exact (example_13_B_1_zero hα).symm
    · exact (example_13_B_1_high hα (by linarith)).symm

/-- **Proposition 13.B.1(i), an instance** (MWG, pp. 442-444). With `r(θ) = αθ`, `0 < α < 1/2`,
and `θ` uniform on `[0, 2]`, `w* = 1` and the unique pure SPNE has both firms offering `1`. -/
theorem proposition_13_B_1_i_instance {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit (unifMeas 0 2) (akerlofR α))) w ↔
      w 0 = 1 ∧ w 1 = 1 := by
  refine proposition_13_B_1_i (akerlof_regular hα (by linarith)) ?_ (by simp [akerlofR])
    one_pos ?_ w
  · rw [example_13_B_1_lowα hα hα2]
    refine ⟨by simp, fun x hx => ?_⟩
    rcases hx with rfl | rfl <;> norm_num
  · intro w' h1 h2
    have hw' : 0 < w' := by linarith
    rcases le_or_gt w' (2 * α) with h | h
    · rw [example_13_B_1 hα hw' h, lt_div_iff₀ (by linarith)]
      nlinarith
    · rw [example_13_B_1_high hα h.le]; exact h2

end MWG.AdverseSelection

namespace MWG.AdverseSelection

open MeasureTheory Set MWG.SimultaneousMoveGames

/-- Correction 2: a strictly increasing, discontinuous home-production function on `[1, 2]`:
`r(θ) = 0` for `θ ≤ 1` and `r(θ) = θ` for `θ > 1`. -/
noncomputable def jumpR : ℝ → ℝ := fun θ => if θ ≤ 1 then 0 else θ

theorem jumpR_inter_subset {w : ℝ} (hw : w ≤ 1) : acceptSet jumpR w ∩ Icc 1 2 ⊆ {1} := by
  rintro θ ⟨h1, h2⟩
  simp only [acceptSet, jumpR, mem_ofPred_eq] at h1
  split_ifs at h1 with h
  · exact le_antisymm h h2.1
  · exact absurd (h1.trans hw) h

theorem jumpR_null {w : ℝ} (hw : w ≤ 1) : unifMeas 1 2 (acceptSet jumpR w) = 0 := by
  rw [← measure_acceptSet_inter (unifMeas_typeDist zero_le_one one_lt_two)]
  exact measure_mono_null (jumpR_inter_subset hw) ((unifMeas_density one_lt_two).noAtom 1)

theorem jumpR_meas : Measurable jumpR :=
  Measurable.ite measurableSet_Iic measurable_const measurable_id

theorem jumpR_profit_neg {w : ℝ} (hw : 1 < w) : firmProfit (unifMeas 1 2) jumpR w < 0 := by
  have hd := unifMeas_typeDist zero_le_one one_lt_two
  have hden := unifMeas_density one_lt_two
  have hpos : 0 < unifMeas 1 2 (acceptSet jumpR w) := by
    refine (hden.pos 1 (min w 2) le_rfl (lt_min hw one_lt_two) (min_le_right _ _)).trans_le
      (measure_mono fun θ hθ => ?_)
    simp only [acceptSet, jumpR, mem_ofPred_eq]
    split_ifs
    · linarith
    · exact hθ.2.trans (min_le_left _ _)
  refine firmProfit_neg_of_ae_lt hd jumpR_meas hpos ?_
  have hne : ∀ᵐ θ ∂(unifMeas 1 2), θ ≠ w := by
    have : unifMeas 1 2 {w} = 0 := hden.noAtom w
    exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun _ h => h
  filter_upwards [hd.ae_mem, hne] with θ hθ hθw hm
  simp only [acceptSet, jumpR, mem_ofPred_eq] at hm
  split_ifs at hm with h
  · linarith
  · exact lt_of_le_of_ne hm hθw

/-- **Proposition 13.B.1(i) is false without continuity of `r`** (correction 2; MWG,
pp. 443-444). Types uniform on `[1, 2]` (positive density), `r = jumpR` strictly increasing with
`r(θ) ≤ θ`, `W* = {1}` so `w* = 1 > r(θ̲) = 0`, and `E[θ | r(θ) ≤ w'] > w'` on `(0, 1)`. Yet
both firms offering `1/2` is a pure SPNE, so the SPNE is not unique and need not pay `w*`. -/
theorem counterexample_13_B_1_i :
    TypeDist (unifMeas 1 2) 1 2 ∧ HasPosDensity (unifMeas 1 2) 1 2 ∧ Measurable jumpR ∧
      StrictMonoOn jumpR (Icc 1 2) ∧ (∀ θ ∈ Icc (1 : ℝ) 2, jumpR θ ≤ θ) ∧
      IsGreatest (eqWages (unifMeas 1 2) 1 2 jumpR) 1 ∧ jumpR 1 < 1 ∧
      (∀ w', 1 - 1 < w' → w' < 1 → w' < condMean (unifMeas 1 2) 1 2 (acceptSet jumpR w')) ∧
      IsNashEquilibrium (wageGame (firmProfit (unifMeas 1 2) jumpR)) ![1 / 2, 1 / 2] ∧
      ¬ ((![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 = 1) := by
  have hd := unifMeas_typeDist zero_le_one one_lt_two
  -- below `1` only the null type `1` accepts
  have hcm : ∀ w, 0 ≤ w → w ≤ 1 → condMean (unifMeas 1 2) 1 2 (acceptSet jumpR w) = 1 := by
    intro w h0 h1
    have hne : (acceptSet jumpR w ∩ Icc 1 2).Nonempty :=
      ⟨1, by simp [acceptSet, jumpR, h0], by norm_num⟩
    simp only [condMean, jumpR_null h1, lt_self_iff_false, ↓reduceIte, hne]
  refine ⟨hd, unifMeas_density one_lt_two, jumpR_meas, ?_, ?_, ⟨?_, ?_⟩, by norm_num [jumpR],
    ?_, ?_, by norm_num⟩
  · intro a ha b hb hab
    simp only [jumpR]
    split_ifs with h1 h2 h2 <;> linarith [hb.1, ha.1]
  · intro θ hθ
    simp only [jumpR]; split_ifs <;> linarith [hθ.1]
  · rw [mem_eqWages_iff, hcm 1 zero_le_one le_rfl]
  · intro w hw
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < unifMeas 1 2 (acceptSet jumpR w) := by
      by_contra h0
      have h0' : unifMeas 1 2 (acceptSet jumpR w) = 0 := le_antisymm (not_lt.1 h0) bot_le
      exact (jumpR_profit_neg hlt).ne (firmProfit_of_null jumpR_meas h0')
    exact (jumpR_profit_neg hlt).ne ((mem_eqWages_iff_profit hd jumpR_meas hpos).1 hw)
  · intro w' h1 h2
    rw [hcm w' (by linarith) h2.le]; exact h2
  · refine (wageGame_flat (ws := 1) (fun t ht => firmProfit_of_null jumpR_meas (jumpR_null ht))
      (fun t ht => jumpR_profit_neg ht) _).2 ?_
    norm_num

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Full information, Pareto optimality and the case `r(θ) = r`

MWG, Section 13.B, pp. 438-440 and 442-443.

* `typeMarketClears`, `typeMarket_clears_iff`: with observable types the market for type-`θ`
  labor clears at `w*(θ) = θ` (employment iff `r(θ) ≤ θ`) or at a wage `w ∈ (θ, r(θ))` with no
  trade (footnote 4).
* `aggSurplus` is (13.B.1); `aggSurplus_le_opt`: it is maximized by employing exactly the types
  with `r(θ) ≤ θ` (p. 438), so the full-information competitive outcome is Pareto optimal.
* Constant `r` (p. 440): `eqWages_const`: `W* = {E[θ]}`; all workers are employed if
  `E[θ] ≥ r`, none otherwise; `const_inefficient_*`: with `F` atomless and `F(r) ∈ (0, 1)` the
  equilibrium is not Pareto optimal.
* Correction 1: `const_atom_counterexample`: with an atom at `r` the claim fails (types `1` and
  `2` with probability `1/2` each, `r = 1`).
* `pareto_ranked` (p. 443): higher-wage equilibria Pareto dominate lower-wage ones.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- **Section 13.B, footnote 4** (MWG, p. 438). With observable types, the market for type-`θ`
labor (demand (13.B.3) with known productivity `θ`, supply one worker if `w ≥ r(θ)`) clears at
wage `w` when either `w = θ`, or `w > θ` and no worker supplies labor (`w < r(θ)`). -/
def typeMarketClears (θ rθ w : ℝ) : Prop := w = θ ∨ (θ < w ∧ w < rθ)

/-- **Section 13.B, footnote 4** (MWG, p. 438). A wage `w` clears the type-`θ` market iff some
labor demand in (13.B.3) (with `μ = θ`) equals the supply: if `w < θ` demand is infinite; if
`w > θ` demand is zero, so supply must be zero. Hence `w*(θ) = θ` is the competitive wage, and
types with `r(θ) > θ` may also face any wage in `(θ, r(θ))`. -/
theorem typeMarket_clears_iff (θ rθ w : ℝ) :
    typeMarketClears θ rθ w ↔
      ((rθ ≤ w → (1 : ℝ) ∈ laborDemand θ w) ∧ (w < rθ → (0 : ℝ) ∈ laborDemand θ w)) := by
  unfold typeMarketClears laborDemand
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · simp
    · refine ⟨fun h => absurd (h.trans_lt h2) (lt_irrefl _), fun _ => ?_⟩
      simp [h1]
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy θ w with h | h | h
    · by_cases hr : rθ ≤ w
      · have := h1 hr; simp [h] at this
      · exact Or.inr ⟨h, not_le.1 hr⟩
    · exact Or.inl h.symm
    · by_cases hr : rθ ≤ w
      · have := h1 hr; simp [not_lt.2 h.le, h.ne'] at this
      · have := h2 (not_le.1 hr); simp [not_lt.2 h.le, h.ne'] at this

/-- **Section 13.B** (MWG, p. 438). At the full-information competitive wage `w*(θ) = θ` the
type-`θ` market clears, and the type is employed iff `r(θ) ≤ θ`. -/
theorem fullInfo_eq (θ rθ : ℝ) :
    typeMarketClears θ rθ θ ∧ (rθ ≤ θ ↔ θ ∈ acceptSet (fun _ => rθ) θ) :=
  ⟨Or.inl rfl, Iff.rfl⟩

/-- **(13.B.1)** (MWG, p. 438). Aggregate surplus `∫ N[I(θ)θ + (1 - I(θ))r(θ)] dF(θ)` of the
employment rule `I` (with `I(θ) ∈ {0, 1}`). -/
noncomputable def aggSurplus (μ : Measure ℝ) (N : ℝ) (r I : ℝ → ℝ) : ℝ :=
  ∫ θ, N * (I θ * θ + (1 - I θ) * r θ) ∂μ

/-- **Section 13.B** (MWG, p. 438). The efficient employment rule: `I(θ) = 1` iff `r(θ) ≤ θ`. -/
noncomputable def optEmployment (r : ℝ → ℝ) : ℝ → ℝ :=
  {θ | r θ ≤ θ}.indicator (fun _ => 1)

theorem optEmployment_eq (r : ℝ → ℝ) (θ : ℝ) :
    optEmployment r θ * θ + (1 - optEmployment r θ) * r θ = max θ (r θ) := by
  by_cases h : r θ ≤ θ
  · simp [optEmployment, h]
  · simp [optEmployment, h, max_eq_right (not_le.1 h).le]

/-- Pointwise, every employment decision gives at most `max θ (r θ)`. -/
theorem employment_le (r : ℝ → ℝ) {I : ℝ → ℝ} (hI : ∀ θ, I θ = 0 ∨ I θ = 1) (θ : ℝ) :
    I θ * θ + (1 - I θ) * r θ ≤ max θ (r θ) := by
  rcases hI θ with h | h <;> simp [h]

/-- The surplus integrand of an employment rule is integrable. -/
theorem integrable_employment {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r I : ℝ → ℝ}
    (hr : Measurable r) (hrint : Integrable r μ) (hIm : Measurable I)
    (hI : ∀ θ, I θ = 0 ∨ I θ = 1) : Integrable (fun θ => I θ * θ + (1 - I θ) * r θ) μ := by
  refine Integrable.mono' (hd.integrable_id.abs.add hrint.abs) ?_ ?_
  · exact ((hIm.mul measurable_id).add ((measurable_const.sub hIm).mul hr)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun θ => by
      rcases hI θ with h | h <;> simp [h, Real.norm_eq_abs]

/-- **(13.B.1)** (MWG, p. 438). Aggregate surplus is maximized by employing exactly the types with
`r(θ) ≤ θ`: the full-information competitive outcome is Pareto optimal. -/
theorem aggSurplus_le_opt {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {N : ℝ}
    (hN : 0 ≤ N) {r I : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r μ)
    (hIm : Measurable I) (hI : ∀ θ, I θ = 0 ∨ I θ = 1) :
    aggSurplus μ N r I ≤ aggSurplus μ N r (optEmployment r) := by
  unfold aggSurplus
  simp only [optEmployment_eq]
  refine integral_mono ?_ ((hd.integrable_id.sup hrint).const_mul N) fun θ =>
      mul_le_mul_of_nonneg_left (employment_le r hI θ) hN
  exact (integrable_employment hd hr hrint hIm hI).const_mul N

/-- **(13.B.1)** (MWG, p. 438). The surplus loss of an employment rule is strict when, with
positive probability, it misallocates a type (`I(θ)θ + (1 - I(θ))r(θ) < max(θ, r(θ))`). -/
theorem aggSurplus_lt_opt {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {N : ℝ}
    (hN : 0 < N) {r I : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r μ) (hIm : Measurable I)
    (hI : ∀ θ, I θ = 0 ∨ I θ = 1)
    (hmis : 0 < μ {θ | I θ * θ + (1 - I θ) * r θ < max θ (r θ)}) :
    aggSurplus μ N r I < aggSurplus μ N r (optEmployment r) := by
  unfold aggSurplus
  simp only [optEmployment_eq]
  have hmax : Integrable (fun θ => max θ (r θ)) μ := hd.integrable_id.sup hrint
  rw [← sub_pos, ← integral_sub (hmax.const_mul N)
    ((integrable_employment hd hr hrint hIm hI).const_mul N)]
  have hint : Integrable (fun θ => N * max θ (r θ) - N * (I θ * θ + (1 - I θ) * r θ)) μ :=
    (hmax.const_mul N).sub ((integrable_employment hd hr hrint hIm hI).const_mul N)
  rw [integral_pos_iff_support_of_nonneg_ae _ hint]
  · refine hmis.trans_le (measure_mono fun θ hθ => ?_)
    simp only [Function.mem_support, mem_ofPred_eq] at hθ ⊢
    nlinarith
  · exact Filter.Eventually.of_forall fun θ => by
      simp only [Pi.zero_apply]
      nlinarith [employment_le r hI θ]

/-- **Section 13.B** (MWG, p. 440). With `r(θ) = r` for all `θ`, `E[θ | θ ∈ Θ(w)] = E[θ]` for
every `w`: `Θ(w)` is everything (`w ≥ r`) or nothing (`w < r`). -/
theorem condMean_const {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (c w : ℝ) :
    condMean μ θl θh (acceptSet (fun _ => c) w) = meanType μ := by
  by_cases h : c ≤ w
  · exact condMean_of_superset hd fun θ _ => h
  · have he : acceptSet (fun _ : ℝ => c) w = ∅ := by
      ext θ; simp [acceptSet, not_le.1 h]
    simp [condMean, he]

/-- **Section 13.B** (MWG, p. 440). With `r(θ) = r`, the unique competitive equilibrium wage is
`w* = E[θ]`. -/
theorem eqWages_const {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (c : ℝ) :
    eqWages μ θl θh (fun _ => c) = {meanType μ} := by
  ext w; simp [mem_eqWages_iff, condMean_const hd]

/-- **Section 13.B** (MWG, p. 440). With `r(θ) = r`: if `E[θ] ≥ r` all workers accept
employment, otherwise none do. -/
theorem acceptSet_const (c m : ℝ) :
    (c ≤ m → acceptSet (fun _ => c) m = univ) ∧ (m < c → acceptSet (fun _ => c) m = ∅) :=
  ⟨fun h => by ext; simp [acceptSet, h], fun h => by ext; simp [acceptSet, h]⟩

/-- **Section 13.B** (MWG, p. 440). With `r(θ) = r`, `F` atomless and `F(r) ∈ (0, 1)`, the
competitive equilibrium is not Pareto optimal: if `E[θ] ≥ r` too many workers are employed (all,
including those with `θ < r`), otherwise too few (none, though some have `θ > r`). -/
theorem const_inefficient {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (hna : ∀ x, μ {x} = 0) {N c : ℝ} (hN : 0 < N) (hF0 : 0 < μ (Iic c)) (hF1 : μ (Iic c) < 1) :
    aggSurplus μ N (fun _ => c) ((acceptSet (fun _ => c) (meanType μ)).indicator fun _ => 1) <
      aggSurplus μ N (fun _ => c) (optEmployment fun _ => c) := by
  have := hd.prob
  refine aggSurplus_lt_opt hd hN measurable_const (integrable_const c)
    (measurable_const.indicator (measurableSet_acceptSet measurable_const _))
    (fun θ => by by_cases h : θ ∈ acceptSet (fun _ => c) (meanType μ) <;> simp [h]) ?_
  by_cases hc : c ≤ meanType μ
  · rw [(acceptSet_const c _).1 hc]
    have hIio : μ (Iic c) ≤ μ (Iio c) := by
      calc μ (Iic c) ≤ μ (Iio c ∪ {c}) := measure_mono (by rw [Iio_union_right])
        _ ≤ μ (Iio c) + μ {c} := measure_union_le _ _
        _ = μ (Iio c) := by rw [hna, add_zero]
    refine (hF0.trans_le hIio).trans_le (measure_mono fun θ hθ => ?_)
    simp only [mem_Iio] at hθ
    simp [hθ]
  · rw [(acceptSet_const c _).2 (not_le.1 hc)]
    have hIoi : 0 < μ (Ioi c) := by
      rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
      exact tsub_pos_of_lt hF1
    refine hIoi.trans_le (measure_mono fun θ hθ => ?_)
    simp only [mem_Ioi] at hθ
    simp [hθ]

/-- Correction 1: two equally likely types, `θ = 1` and `θ = 2`. -/
noncomputable def atomMeas : Measure ℝ :=
  (2⁻¹ : ENNReal) • Measure.dirac 1 + (2⁻¹ : ENNReal) • Measure.dirac 2

theorem integral_atomMeas (f : ℝ → ℝ) : ∫ θ, f θ ∂atomMeas = (f 1 + f 2) / 2 := by
  rw [atomMeas, integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem atomMeas_typeDist : TypeDist atomMeas 1 2 where
  nonneg := zero_le_one
  lt := one_lt_two
  prob := ⟨by simp [atomMeas, ENNReal.inv_two_add_inv_two]⟩
  supp := by simp [atomMeas]

/-- **Correction 1** (MWG, p. 440). The claim that with `r(θ) = r` and `F(r) ∈ (0, 1)` the
competitive equilibrium is not Pareto optimal needs `F` atomless. With types `1` and `2` equally
likely and `r = 1`: `F(r) = 1/2`, `W* = {E[θ]} = {3/2}`, every worker is employed, and this
outcome maximizes aggregate surplus. -/
theorem const_atom_counterexample (N : ℝ) :
    atomMeas (Iic 1) = 2⁻¹ ∧ eqWages atomMeas 1 2 (fun _ => 1) = {3 / 2} ∧
      acceptSet (fun _ => (1 : ℝ)) (3 / 2) = univ ∧
      aggSurplus atomMeas N (fun _ => 1) ((acceptSet (fun _ => (1 : ℝ)) (3 / 2)).indicator
        fun _ => 1) = aggSurplus atomMeas N (fun _ => 1) (optEmployment fun _ => 1) := by
  have hmean : meanType atomMeas = 3 / 2 := by
    rw [meanType, integral_atomMeas]; norm_num
  have hacc : acceptSet (fun _ => (1 : ℝ)) (3 / 2) = univ := (acceptSet_const 1 _).1 (by norm_num)
  refine ⟨?_, by rw [eqWages_const atomMeas_typeDist, hmean], hacc, ?_⟩
  · simp [atomMeas]
  · rw [hacc]
    unfold aggSurplus
    simp only [optEmployment_eq, indicator_univ, integral_atomMeas]
    norm_num

/-- **Section 13.B** (MWG, p. 443). Competitive equilibria are Pareto ranked: firms earn zero in
every equilibrium, and a worker of type `θ` earns `max(w, r(θ))`, which is weakly higher at a
higher wage, strictly for the types employed at the higher wage. -/
theorem pareto_ranked {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {w : ℝ} (hw : w ∈ eqWages μ θl θh r) {w₁ w₂ : ℝ} (h : w₁ < w₂) :
    (0 < μ (acceptSet r w) → firmProfit μ r w = 0) ∧
      ∀ θ, max w₁ (r θ) ≤ max w₂ (r θ) ∧ (r θ < w₂ → max w₁ (r θ) < max w₂ (r θ)) := by
  refine ⟨fun hpos => (mem_eqWages_iff_profit hd hr hpos).1 hw, fun θ => ⟨?_, fun hθ => ?_⟩⟩
  · exact max_le_max h.le le_rfl
  · rw [max_eq_left hθ.le]; exact max_lt h hθ

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Constrained Pareto optimality: Proposition 13.B.2

MWG, Section 13.B, pp. 445-448.

A central authority that cannot observe types runs the firms, pays `w_e` to those who accept
employment and `w_u` to those who do not, and must balance its budget. Type `θ` accepts iff
`w_u + r(θ) ≤ w_e`, i.e. iff `θ ∈ Θ(w_e - w_u)`, and then earns `max(w_e, w_u + r(θ))`.

* `BudgetOK` is the budget constraint (13.B.8), written as `≤` (footnote 15 shows a surplus is
  never optimal: `footnote_15`). `budget_wu_le`: it says exactly that `w_u` is at most the profit
  of a firm paying `w_e - w_u`.
* `IsParetoImprovement`, `IsConstrainedPO`: the definitions of p. 445.
* `proposition_13_B_2`: in the model of p. 441 (with `r` continuous) the highest-wage
  competitive equilibrium is a constrained Pareto optimum. The proof does not use `r(θ) ≤ θ`, so
  it also proves **Exercise 13.B.10** (`exercise_13_B_10`).
* `scheme_13_B_9`, `scheme_13_B_10`, ...: the scheme `(w_u(θ̂), w_e(θ̂))` of (13.B.7)-(13.B.12)
  and its value at `θ̂ = θ*`.
* `highest_wage_implementable` (p. 446): the authority can implement the highest-wage
  equilibrium with `w_e = w*`, `w_u = 0`; so a Pareto-dominated equilibrium is not a constrained
  Pareto optimum (`dominated_not_constrainedPO`).
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- The model of p. 441 without `r(θ) ≤ θ` (as in Exercise 13.B.10): positive density, `r`
measurable, strictly increasing and continuous on `[θ̲, θ̄]`. -/
structure MonoModel (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Prop where
  dist : TypeDist μ θl θh
  dens : HasPosDensity μ θl θh
  meas : Measurable r
  mono : StrictMonoOn r (Icc θl θh)
  cont : ContinuousOn r (Icc θl θh)

/-- The model of p. 441 is a `MonoModel`. -/
theorem RegularModel.toMono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : MonoModel μ θl θh r :=
  ⟨h.dist, h.dens, h.meas, h.mono, h.cont⟩

/-- **(13.B.8)** (MWG, p. 447). The authority's budget: paying `w_e` to the employed set
`E = Θ(w_e - w_u)` and `w_u` to the others costs at most the output `∫_E θ dF`. -/
def BudgetOK (μ : Measure ℝ) (r : ℝ → ℝ) (we wu : ℝ) : Prop :=
  we * μ.real (acceptSet r (we - wu)) + wu * (1 - μ.real (acceptSet r (we - wu))) ≤
    ∫ θ in acceptSet r (we - wu), θ ∂μ

/-- **Section 13.B** (MWG, pp. 445-446). The intervention `(w_e, w_u)` Pareto improves on the
competitive equilibrium with wage `w*`: no worker type is worse off and some type is better
off (firms' owners earn zero in both). -/
def IsParetoImprovement (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  (∀ θ ∈ Icc θl θh, max ws (r θ) ≤ max we (wu + r θ)) ∧
    ∃ θ ∈ Icc θl θh, max ws (r θ) < max we (wu + r θ)

/-- **Section 13.B** (MWG, pp. 445-446). The competitive equilibrium with wage `w*` is a
constrained Pareto optimum: no budget-feasible intervention Pareto improves on it. -/
def IsConstrainedPO (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) (ws : ℝ) : Prop :=
  ∀ we wu, BudgetOK μ r we wu → ¬ IsParetoImprovement θl θh r ws we wu

/-- The budget constraint says that `w_u` is at most the profit of a firm paying
`w_e - w_u`. -/
theorem budget_wu_le {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {we wu : ℝ} (hb : BudgetOK μ r we wu) :
    wu ≤ firmProfit μ r (we - wu) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  unfold BudgetOK at hb
  nlinarith

/-- **Footnote 15** (MWG, p. 447). If `(w_e, w_u)` leaves a budget surplus, raising both by
`ε` keeps the employed set, stays feasible for small `ε`, and makes every worker better off. -/
theorem footnote_15 {μ : Measure ℝ} {r : ℝ → ℝ} {we wu ε : ℝ} (hε : 0 < ε)
    (hsur : we * μ.real (acceptSet r (we - wu)) + wu * (1 - μ.real (acceptSet r (we - wu))) + ε ≤
      ∫ θ in acceptSet r (we - wu), θ ∂μ) :
    BudgetOK μ r (we + ε) (wu + ε) ∧ ∀ x, max we (wu + x) < max (we + ε) (wu + ε + x) := by
  have hd : we + ε - (wu + ε) = we - wu := by ring
  refine ⟨?_, fun x => ?_⟩
  · unfold BudgetOK; rw [hd]; nlinarith
  · rw [show wu + ε + x = (wu + x) + ε by ring, max_add_add_right]; linarith

/-- The worker's payoff under an intervention: `max(w_e, w_u + r) = w_u + max(w_e - w_u, r)`. -/
theorem scheme_payoff (we wu x : ℝ) : max we (wu + x) = wu + max (we - wu) x := by
  rw [← max_add_add_left]; congr 1; ring

/-- In the `MonoModel`, above the largest equilibrium wage the profit is negative wherever
`Θ(w)` has positive probability. -/
theorem MonoModel.firmProfit_neg_of_gt_max {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) {w : ℝ}
    (hw : ws < w) (hpos : 0 < μ (acceptSet r w)) : firmProfit μ r w < 0 := by
  have hcont := continuous_firmProfit h.dist h.dens.noAtom h.meas h.mono.injOn
  have hne : firmProfit μ r w ≠ 0 := fun h0 =>
    absurd (hmax.2 ((mem_eqWages_iff_profit h.dist h.meas hpos).2 h0)) (not_le.2 hw)
  rcases lt_or_gt_of_ne hne with hneg | hp
  · exact hneg
  · exfalso
    set b := max w θh + 1
    have hwb : w ≤ b := by simp only [b]; linarith [le_max_left w θh]
    have hbθ : θh < b := by simp only [b]; linarith [le_max_right w θh]
    have hmono : ∀ c, w ≤ c → 0 < μ (acceptSet r c) := fun c hc =>
      hpos.trans_le (measure_mono fun θ hθ => le_trans hθ hc)
    have hb := firmProfit_neg_of_gt h.dist h.meas hbθ (hmono b hwb)
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hwb hcont.continuousOn ⟨hb.le, hp.le⟩
    have hcm := (mem_eqWages_iff_profit h.dist h.meas (hmono c hc.1)).2 hc0
    exact absurd (hmax.2 hcm) (not_le.2 (hw.trans_le hc.1))

/-- **Proposition 13.B.2**, proof (MWG, pp. 447-448), the case `θ̂ < θ*`. If the authority
employs fewer types than the equilibrium with wage `w*` (cutoff wage `d` with
`r(θ̲) ≤ d < w*` and `d < r(θ̄)`), then `w_e ≤ w_u + d ≤ Π(d) + d < w*`: the type `θ̲` is worse
off. This is `E[θ | θ ≤ θ̂] < E[θ | θ ≤ θ*]`. -/
theorem MonoModel.profit_add_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws d : ℝ} (hws : ws ∈ eqWages μ θl θh r) (hd1 : r θl ≤ d)
    (hd2 : d < ws) (hd3 : d < r θh) : firmProfit μ r d + d < ws := by
  have := h.dist.prob
  have hl : θl ∈ Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hh : θh ∈ Icc θl θh := ⟨h.dist.lt.le, le_rfl⟩
  -- the type `a` with `r(a) = d`
  obtain ⟨a, ha, hra⟩ := intermediate_value_Icc h.dist.lt.le h.cont ⟨hd1, hd3.le⟩
  have hah : a < θh := by
    rcases eq_or_lt_of_le ha.2 with he | hlt
    · rw [he] at hra; exact absurd hra hd3.ne'
    · exact hlt
  have hiff : ∀ θ ∈ Icc θl θh, r θ ≤ d ↔ θ ≤ a := fun θ hθ => by
    rw [← hra]; exact h.mono.le_iff_le hθ ha
  set E := acceptSet r d
  set E' := acceptSet r ws
  set D := E' \ E
  have hEm := measurableSet_acceptSet h.meas d
  have hE'm := measurableSet_acceptSet h.meas ws
  have hsub : E ⊆ E' := fun θ hθ => le_trans hθ hd2.le
  have hE'pos : 0 < μ E' := measure_acceptSet_pos h.dist h.dens h.cont (hd1.trans_lt hd2)
  have hP : firmProfit μ r ws = 0 := (mem_eqWages_iff_profit h.dist h.meas hE'pos).1 hws
  have hint := h.dist.integrable_id
  -- integrals and measures
  have hIE' : ∫ θ in E', θ ∂μ = ws * μ.real E' := by
    have := hP
    rw [firmProfit_eq_setIntegral h.meas, integral_sub hint.integrableOn
      (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul] at this
    linarith
  have hunion : E' = E ∪ D := (union_sdiff_cancel hsub).symm
  have hdisj : Disjoint E D := disjoint_sdiff_right
  have hDm : MeasurableSet D := hE'm.diff hEm
  have hIsplit : ∫ θ in E', θ ∂μ = ∫ θ in E, θ ∂μ + ∫ θ in D, θ ∂μ := by
    rw [hunion]; exact setIntegral_union hdisj hDm hint.integrableOn hint.integrableOn
  have hMsplit : μ.real E' = μ.real E + μ.real D := by
    rw [hunion]; exact measureReal_union hdisj hDm
  have hEa : ∫ θ in E, θ ∂μ ≤ a * μ.real E := by
    have := setIntegral_mono_on_ae hint.integrableOn (integrable_const a).integrableOn hEm
      (h.dist.ae_mem.mono fun θ hθ hθE => (hiff θ hθ).1 hθE)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hDa : a * μ.real D ≤ ∫ θ in D, θ ∂μ := by
    have := setIntegral_mono_on_ae (integrable_const a).integrableOn hint.integrableOn hDm
      (h.dist.ae_mem.mono fun θ hθ hθD => by
        by_contra hlt
        exact hθD.2 ((hiff θ hθ).2 (not_le.1 hlt).le))
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hE0 := measureReal_nonneg (μ := μ) (s := E)
  have hD0 := measureReal_nonneg (μ := μ) (s := D)
  -- `E[θ | E] ≤ w*`
  have hclaim : ∫ θ in E, θ ∂μ ≤ ws * μ.real E := by
    by_contra hcon
    rw [not_le] at hcon
    have hEpos : 0 < μ.real E := by
      rcases eq_or_lt_of_le hE0 with he | hlt
      · rw [← he] at hcon hEa; linarith
      · exact hlt
    have hwa : ws < a := lt_of_mul_lt_mul_right (hcon.trans_le hEa) hE0
    have hsplit' : ws * μ.real E' = ws * μ.real E + ws * μ.real D := by rw [hMsplit]; ring
    have hDlt : ∫ θ in D, θ ∂μ < ws * μ.real D := by linarith
    rcases eq_or_lt_of_le hD0 with he | hDpos
    · rw [← he] at hDlt hDa; linarith
    · have : a * μ.real D < ws * μ.real D := hDa.trans_lt hDlt
      linarith [lt_of_mul_lt_mul_right this hD0]
  -- some types are not employed at `d`
  have hEl1 : μ.real E < 1 := by
    have hIoi : 0 < μ (Ioi a) := by
      refine (h.dens.pos ((a + θh) / 2) θh (by linarith [ha.1]) (by linarith) le_rfl).trans_le
        (measure_mono fun θ hθ => ?_)
      exact show a < θ by linarith [hθ.1]
    have hEle : μ E ≤ μ (Iic a) := measure_mono_ae (h.dist.ae_mem.mono fun θ hθ hθE =>
      show θ ≤ a from (hiff θ hθ).1 hθE)
    have hsum : μ (Iic a) + μ (Ioi a) = 1 := by
      rw [← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    have hlt1 : μ E < 1 := by
      calc μ E ≤ μ (Iic a) := hEle
        _ < μ (Iic a) + μ (Ioi a) := ENNReal.lt_add_right (measure_ne_top _ _) hIoi.ne'
        _ = 1 := hsum
    rw [Measure.real]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hlt1 |>.trans_eq
      ENNReal.toReal_one
  rw [firmProfit_eq_setIntegral h.meas, integral_sub hint.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  nlinarith

/-- When every type in `[θ̲, θ̄]` accepts `w`, the profit is `E[θ] - w`. -/
theorem firmProfit_of_full {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {w : ℝ} (hfull : Icc θl θh ⊆ acceptSet r w) :
    firmProfit μ r w = meanType μ - w := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, setIntegral_eq_integral_of_ae_compl_eq_zero
    (hd.ae_mem.mono fun θ hθ hc => absurd (hfull hθ) hc), integral_sub hd.integrable_id
    (integrable_const w), integral_const, meanType]
  simp

/-- If every type accepts `E[θ]`, then `E[θ]` is a competitive equilibrium wage (full
employment). -/
theorem mean_mem_eqWages {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hfull : Icc θl θh ⊆ acceptSet r (meanType μ)) : meanType μ ∈ eqWages μ θl θh r := by
  rw [mem_eqWages_iff, condMean_of_superset hd hfull]

/-- **Proposition 13.B.2** in the generality of **Exercise 13.B.10** (MWG, pp. 447-448, 474).
In the model with positive density and `r` strictly increasing and continuous (`r(θ) ≤ θ` is not
needed), the highest-wage competitive equilibrium is a constrained Pareto optimum. -/
theorem MonoModel.isConstrainedPO {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws := by
  have := h.dist.prob
  intro we wu hb ⟨hall, θ0, hθ0, hstrict⟩
  have hl : θl ∈ Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hh : θh ∈ Icc θl θh := ⟨h.dist.lt.le, le_rfl⟩
  have hwu := budget_wu_le h.dist h.meas hb
  have hTl := hall θl hl
  have hTh := hall θh hh
  rw [scheme_payoff] at hTl hTh hstrict
  set d := we - wu with hd
  have hr0l : r θl ≤ r θ0 := h.mono.monotoneOn hl hθ0 hθ0.1
  have hr0h : r θ0 ≤ r θh := h.mono.monotoneOn hθ0 hh hθ0.2
  have hfullOf : ∀ x, r θh ≤ x → Icc θl θh ⊆ acceptSet r x := fun x hx θ hθ =>
    (h.mono.monotoneOn hθ hh hθ.2).trans hx
  rcases lt_trichotomy d ws with hdlt | hdeq | hdgt
  · by_cases hd1 : d < r θl
    · have hP := firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hd1
      rw [max_eq_right hd1.le] at hTl
      have : wu = 0 := le_antisymm (hP ▸ hwu) (by linarith [le_max_right ws (r θl)])
      linarith [max_le_max hdlt.le (le_refl (r θ0))]
    · rw [not_lt] at hd1
      rw [max_eq_left hd1] at hTl
      by_cases hd3 : d < r θh
      · have := h.profit_add_lt hmax.1 hd1 hdlt hd3
        linarith [le_max_left ws (r θl)]
      · rw [not_lt] at hd3
        have hP := firmProfit_of_full h.dist h.meas (hfullOf d hd3)
        have hE : ws ≤ meanType μ := by linarith [le_max_left ws (r θl)]
        have hEm : meanType μ ≤ ws :=
          hmax.2 (mean_mem_eqWages h.dist (hfullOf _ (by linarith)))
        rw [max_eq_left (hr0h.trans hd3)] at hstrict
        linarith [le_max_left ws (r θ0)]
  · have hP : firmProfit μ r ws ≤ 0 := by
      by_cases hpos : 0 < μ (acceptSet r ws)
      · exact ((mem_eqWages_iff_profit h.dist h.meas hpos).1 hmax.1).le
      · exact (firmProfit_of_null h.meas (le_antisymm (not_lt.1 hpos) bot_le)).le
    rw [hdeq] at hwu hstrict
    linarith
  · by_cases hdl : d ≤ r θl
    · have hP : firmProfit μ r d = 0 := by
        rcases eq_or_lt_of_le hdl with he | hlt
        · rw [he]; exact firmProfit_rl h.dist h.mono h.dens h.meas
        · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt
      rw [max_eq_right (hdl.trans hr0l)] at hstrict
      linarith [le_max_right ws (r θ0)]
    · rw [not_le] at hdl
      have hneg := h.firmProfit_neg_of_gt_max hmax hdgt
        (measure_acceptSet_pos h.dist h.dens h.cont hdl)
      by_cases hdh : d ≤ r θh
      · rw [max_eq_right hdh] at hTh
        linarith [le_max_right ws (r θh)]
      · rw [not_le] at hdh
        have hP := firmProfit_of_full h.dist h.meas (hfullOf d hdh.le)
        rw [max_eq_left hdh.le] at hTh
        have hEm : meanType μ ≤ ws :=
          hmax.2 (mean_mem_eqWages h.dist (hfullOf _ (by linarith [le_max_right ws (r θh)])))
        rw [max_eq_left (hr0h.trans hdh.le)] at hstrict
        linarith [le_max_left ws (r θ0)]

/-- **Proposition 13.B.2** (MWG, p. 447). In the adverse selection model (`r` strictly
increasing, here also continuous, `r(θ) ≤ θ`, positive density) the highest-wage competitive
equilibrium is a constrained Pareto optimum. -/
theorem proposition_13_B_2 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws :=
  h.toMono.isConstrainedPO hmax

/-- **Exercise 13.B.10** (MWG, p. 474). Proposition 13.B.2 continues to hold when `r(θ) > θ` for
some `θ`. -/
theorem exercise_13_B_10 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws :=
  h.isConstrainedPO hmax

/-- **(13.B.9)** (MWG, p. 447). The unemployment benefit that employs exactly the types
`θ ≤ θ̂` with a balanced budget: `w_u(θ̂) = ∫_{θ̲}^{θ̂} θ f(θ) dθ - r(θ̂) F(θ̂)`. -/
noncomputable def schemeWu (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) : ℝ :=
  (∫ θ in Iic θhat, θ ∂μ) - r θhat * μ.real (Iic θhat)

/-- **(13.B.10)** (MWG, p. 447). The employment wage
`w_e(θ̂) = ∫_{θ̲}^{θ̂} θ f(θ) dθ + r(θ̂)(1 - F(θ̂))`. -/
noncomputable def schemeWe (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) : ℝ :=
  (∫ θ in Iic θhat, θ ∂μ) + r θhat * (1 - μ.real (Iic θhat))

/-- **(13.B.7)-(13.B.10)** (MWG, p. 447). `(w_e(θ̂), w_u(θ̂))` satisfies the indifference
condition (13.B.7) `w_u + r(θ̂) = w_e` and the budget (13.B.8), and is the only pair doing so. -/
theorem scheme_13_B_7_8 (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) :
    schemeWu μ r θhat + r θhat = schemeWe μ r θhat ∧
      schemeWe μ r θhat * μ.real (Iic θhat) + schemeWu μ r θhat * (1 - μ.real (Iic θhat)) =
        ∫ θ in Iic θhat, θ ∂μ ∧
      ∀ we wu, wu + r θhat = we →
        we * μ.real (Iic θhat) + wu * (1 - μ.real (Iic θhat)) = ∫ θ in Iic θhat, θ ∂μ →
        wu = schemeWu μ r θhat ∧ we = schemeWe μ r θhat := by
  refine ⟨by unfold schemeWu schemeWe; ring, by unfold schemeWu schemeWe; ring,
    fun we wu h7 h8 => ?_⟩
  subst h7
  unfold schemeWu schemeWe
  constructor <;> linarith

/-- **(13.B.11)-(13.B.12)** (MWG, p. 447). With `F(θ̂) > 0`,
`w_u(θ̂) = F(θ̂)(E[θ | θ ≤ θ̂] - r(θ̂))` and `w_e(θ̂) = F(θ̂)(E[θ | θ ≤ θ̂] - r(θ̂)) + r(θ̂)`. -/
theorem scheme_13_B_11_12 (μ : Measure ℝ) (r : ℝ → ℝ) {θhat : ℝ}
    (hF : 0 < μ.real (Iic θhat)) :
    schemeWu μ r θhat = μ.real (Iic θhat) *
        ((∫ θ in Iic θhat, θ ∂μ) / μ.real (Iic θhat) - r θhat) ∧
      schemeWe μ r θhat = μ.real (Iic θhat) *
        ((∫ θ in Iic θhat, θ ∂μ) / μ.real (Iic θhat) - r θhat) + r θhat := by
  unfold schemeWu schemeWe
  constructor
  · field_simp
  · field_simp; ring

/-- **Proposition 13.B.2**, proof (MWG, p. 447). At the highest type `θ*` employed in the
highest-wage equilibrium, `r(θ*) = E[θ | θ ≤ θ*]`, so `w_u(θ*) = 0` and `w_e(θ*) = r(θ*)`: the
scheme reproduces the equilibrium. -/
theorem scheme_at_θstar (μ : Measure ℝ) (r : ℝ → ℝ) {θs : ℝ} (hF : 0 < μ.real (Iic θs))
    (heq : r θs = (∫ θ in Iic θs, θ ∂μ) / μ.real (Iic θs)) :
    schemeWu μ r θs = 0 ∧ schemeWe μ r θs = r θs := by
  obtain ⟨h1, h2⟩ := scheme_13_B_11_12 μ r hF
  rw [h1, h2, ← heq]; simp

/-- **Section 13.B** (MWG, p. 446). The authority can implement any competitive equilibrium
(in particular the highest-wage one) by setting `w_e = w*`, `w_u = 0`: the budget balances
since `w* = E[θ | r(θ) ≤ w*]`, and every type gets her equilibrium payoff. -/
theorem highest_wage_implementable {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) {ws : ℝ} (hws : ws ∈ eqWages μ θl θh r)
    (hpos : 0 < μ (acceptSet r ws)) :
    BudgetOK μ r ws 0 ∧ ∀ θ, max ws (0 + r θ) = max ws (r θ) := by
  have := hd.prob
  refine ⟨?_, fun θ => by rw [zero_add]⟩
  have hP := (mem_eqWages_iff_profit hd hr hpos).1 hws
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul] at hP
  unfold BudgetOK
  rw [sub_zero]
  linarith

/-- **Section 13.B** (MWG, p. 446). A competitive equilibrium Pareto dominated by another one
(with positive employment, and some type employed at the higher wage) is not a constrained
Pareto optimum. -/
theorem dominated_not_constrainedPO {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) {w₁ w₂ : ℝ} (hw₂ : w₂ ∈ eqWages μ θl θh r)
    (hpos : 0 < μ (acceptSet r w₂)) (hlt : w₁ < w₂) (hemp : ∃ θ ∈ Icc θl θh, r θ < w₂) :
    ¬ IsConstrainedPO μ θl θh r w₁ := by
  intro hcpo
  obtain ⟨hb, hpay⟩ := highest_wage_implementable hd hr hw₂ hpos
  refine hcpo w₂ 0 hb ⟨fun θ _ => ?_, ?_⟩
  · rw [hpay]; exact max_le_max hlt.le le_rfl
  · obtain ⟨θ, hθ, hrθ⟩ := hemp
    refine ⟨θ, hθ, ?_⟩
    rw [hpay, max_eq_left hrθ.le]
    exact max_lt hlt hrθ

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Distributional aims and direct revelation mechanisms

MWG, Section 13.B, pp. 448-450 (small type).

* `weightedWelfare` is (13.B.13); with weights `λ(θ) = N` it is aggregate surplus
  (`weightedWelfare_const`).
* `mandate_all`: when `r(θ) ≤ θ`, mandating that everyone work raises aggregate surplus above a
  competitive equilibrium in which some types with `r(θ) < θ` stay home, although the type `θ̄`
  is worse off when `E[θ] < r(θ̄)` (p. 449).
* Direct revelation mechanisms `[w(·), t(·), I(·)]`: individual rationality for the firm (13.B.14),
  budget balance (13.B.15), truth telling (13.B.16) and the authority's budget (13.B.17).
  `mechanism_17_of_14_15`, `mechanism_exists_t`: a mechanism is feasible iff `[w(·), I(·)]`
  satisfies (13.B.16) and (13.B.17); `mechanism_two_outcome`, `mechanism_scheme`: truth telling
  forces a two-outcome scheme `(w_e, 1)`, `(w_u, 0)`, the class studied above.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- **(13.B.13)** (MWG, p. 448). Social welfare as a weighted sum of worker utilities
`∫ [I(θ)θ + (1 - I(θ))r(θ)] λ(θ) dF(θ)`. -/
noncomputable def weightedWelfare (μ : Measure ℝ) (lam r I : ℝ → ℝ) : ℝ :=
  ∫ θ, (I θ * θ + (1 - I θ) * r θ) * lam θ ∂μ

/-- **(13.B.13)** (MWG, p. 448). With `λ(θ) = N` for all `θ` the welfare function is aggregate
surplus. -/
theorem weightedWelfare_const (μ : Measure ℝ) (N : ℝ) (r I : ℝ → ℝ) :
    weightedWelfare μ (fun _ => N) r I = aggSurplus μ N r I := by
  unfold weightedWelfare aggSurplus
  congr 1; ext θ; ring

/-- **Section 13.B** (MWG, pp. 448-449). If `r(θ) ≤ θ` on `[θ̲, θ̄]`, mandating that every worker
work for a firm (at wage `E[θ]`) yields strictly higher aggregate surplus than a competitive
equilibrium with wage `w*` in which, with positive probability, types with `w* < r(θ) < θ`
stay home; yet type `θ̄` is worse off when `E[θ] < r(θ̄)`. -/
theorem mandate_all {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {N : ℝ} (hN : 0 < N)
    {r : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r μ)
    (hle : ∀ θ ∈ Icc θl θh, r θ ≤ θ) (ws : ℝ)
    (hmis : 0 < μ {θ | ws < r θ ∧ r θ < θ}) :
    aggSurplus μ N r ((acceptSet r ws).indicator fun _ => 1) < aggSurplus μ N r (fun _ => 1) ∧
      (meanType μ < r θh → meanType μ < max ws (r θh)) := by
  refine ⟨?_, fun h => h.trans_le (le_max_right _ _)⟩
  have heq : aggSurplus μ N r (fun _ => 1) = aggSurplus μ N r (optEmployment r) := by
    unfold aggSurplus
    refine integral_congr_ae (hd.ae_mem.mono fun θ hθ => ?_)
    simp only [optEmployment_eq, max_eq_left (hle θ hθ)]
    ring
  rw [heq]
  refine aggSurplus_lt_opt hd hN hr hrint
    (measurable_const.indicator (measurableSet_acceptSet hr ws))
    (fun θ => by by_cases h : θ ∈ acceptSet r ws <;> simp [h]) (hmis.trans_le
    (measure_mono fun θ hθ => ?_))
  have hθ' : θ ∉ acceptSet r ws := fun h => absurd (show r θ ≤ ws from h) (not_le.2 hθ.1)
  simp only [mem_ofPred_eq, indicator_of_notMem hθ', zero_mul, sub_zero, one_mul, zero_add]
  rw [max_eq_left hθ.2.le]; exact hθ.2

/-- **(13.B.14)** (MWG, p. 449). Individual rationality for the (aggregate) firm. -/
def MechIR (μ : Measure ℝ) (t I : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (I θ * θ - t θ) ∂μ

/-- **(13.B.15)** (MWG, p. 449). Budget balance for the authority. -/
def MechBB (μ : Measure ℝ) (w t : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (t θ - w θ) ∂μ

/-- **(13.B.16)** (MWG, p. 449). Truth telling: type `θ` prefers her own outcome to the one of
any `θ̂`. -/
def MechIC (r w I : ℝ → ℝ) : Prop :=
  ∀ θ θhat, w θhat + (1 - I θhat) * r θ ≤ w θ + (1 - I θ) * r θ

/-- **(13.B.17)** (MWG, p. 449). The budget of an authority that runs the firms. -/
def MechBudget (μ : Measure ℝ) (w I : ℝ → ℝ) : Prop := 0 ≤ ∫ θ, (I θ * θ - w θ) ∂μ

/-- **Section 13.B** (MWG, p. 449). A feasible mechanism satisfies (13.B.17). -/
theorem mechanism_17_of_14_15 {μ : Measure ℝ} {w t I : ℝ → ℝ}
    (hIθ : Integrable (fun θ => I θ * θ) μ) (ht : Integrable t μ) (hw : Integrable w μ)
    (h14 : MechIR μ t I) (h15 : MechBB μ w t) : MechBudget μ w I := by
  unfold MechIR MechBB MechBudget at *
  rw [integral_sub hIθ ht] at h14
  rw [integral_sub ht hw] at h15
  rw [integral_sub hIθ hw]
  linarith

/-- **Section 13.B** (MWG, p. 450). If `[w(·), I(·)]` satisfies (13.B.17), the transfer
`t(θ) = I(θ)θ` makes `[w(·), t(·), I(·)]` satisfy (13.B.14) and (13.B.15). -/
theorem mechanism_exists_t {μ : Measure ℝ} {w I : ℝ → ℝ}
    (h17 : MechBudget μ w I) :
    MechIR μ (fun θ => I θ * θ) I ∧ MechBB μ w (fun θ => I θ * θ) := by
  refine ⟨?_, h17⟩
  unfold MechIR; simp

/-- **Section 13.B** (MWG, p. 450). Truth telling forces equal payments to types with the same
employment decision: `I(θ') = I(θ'')` implies `w(θ') = w(θ'')`. -/
theorem mechanism_two_outcome {r w I : ℝ → ℝ} (hIC : MechIC r w I) {θ₁ θ₂ : ℝ}
    (hI : I θ₁ = I θ₂) : w θ₁ = w θ₂ := by
  have h1 := hIC θ₁ θ₂
  have h2 := hIC θ₂ θ₁
  rw [hI] at h1 h2
  linarith

/-- **Section 13.B** (MWG, p. 450). A truthful mechanism with `I(θ) ∈ {0, 1}` is a choice between
two outcomes `(w_e, I = 1)` and `(w_u, I = 0)`, and each type picks a best one. -/
theorem mechanism_scheme {r w I : ℝ → ℝ} (hIC : MechIC r w I) :
    ∃ we wu, (∀ θ, I θ = 1 → w θ = we) ∧ (∀ θ, I θ = 0 → w θ = wu) ∧
      (∀ θ θ', I θ = 1 → I θ' = 0 → wu + r θ ≤ we ∧ we ≤ wu + r θ') := by
  by_cases h1 : ∃ θ, I θ = 1
  · obtain ⟨θ1, hθ1⟩ := h1
    by_cases h0 : ∃ θ, I θ = 0
    · obtain ⟨θ0, hθ0⟩ := h0
      refine ⟨w θ1, w θ0, fun θ h => mechanism_two_outcome hIC (h.trans hθ1.symm),
        fun θ h => mechanism_two_outcome hIC (h.trans hθ0.symm), fun θ θ' h h' => ?_⟩
      have e1 : w θ = w θ1 := mechanism_two_outcome hIC (h.trans hθ1.symm)
      have e0 : w θ' = w θ0 := mechanism_two_outcome hIC (h'.trans hθ0.symm)
      have a1 := hIC θ θ'
      have a2 := hIC θ' θ
      rw [h, h'] at a1 a2
      constructor <;> linarith
    · push Not at h0
      refine ⟨w θ1, 0, fun θ h => mechanism_two_outcome hIC (h.trans hθ1.symm),
        fun θ h => absurd h (h0 θ), fun θ θ' _ h' => absurd h' (h0 θ')⟩
  · push Not at h1
    by_cases h0 : ∃ θ, I θ = 0
    · obtain ⟨θ0, hθ0⟩ := h0
      exact ⟨0, w θ0, fun θ h => absurd h (h1 θ),
        fun θ h => mechanism_two_outcome hIC (h.trans hθ0.symm), fun θ _ h _ => absurd h (h1 θ)⟩
    · push Not at h0
      exact ⟨0, 0, fun θ h => absurd h (h1 θ), fun θ h => absurd h (h0 θ),
        fun θ _ h _ => absurd h (h1 θ)⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The education signaling model

MWG, Section 13.C, pp. 450-453.

Two types `θ_L < θ_H` (`true` is the high type), `λ = Prob(θ = θ_H) ∈ (0, 1)`, home earnings
`r` (the main text has `r = 0`, the small type on p. 459 has `r ∈ (θ_L, θ_H)`; we allow any
`0 ≤ r < θ_H`), and education cost `c(e, θ)`. A worker of type `θ` choosing `e` and earning `w`
gets `w - c(e, θ)`.

Assumptions (`SigModel.Valid`). From the book's assumptions on `c` we use: `c(0, θ) = 0`,
`c(·, θ)` strictly increasing on `e ≥ 0` (`c_e > 0`), and the single-crossing property in the
integrated form `c(e', θ_H) - c(e, θ_H) < c(e', θ_L) - c(e, θ_L)` for `0 ≤ e < e'` (implied by
`c_{eθ} < 0`). `c_θ < 0` then follows
(`c_lt_of_pos`). Convexity (`c_ee > 0`) is not needed.

The game (Figure 13.C.1): nature draws the type, the worker chooses `e ≥ 0`, two firms see `e`
and simultaneously offer wages, the worker accepts a highest offer if it is at least `r`.
Education is a continuous choice, so the game is not one of the finite extensive forms of
Chapter 9; we use the book's equivalent definition of a pure strategy perfect Bayesian
equilibrium (p. 452, conditions (i)-(iii)), with condition (iii) a Nash equilibrium of the
Chapter 8 wage game `wageGame` (`IsPBE`).

* `bertrand_wage`: in the wage game after `e` with belief `μ(e)`, every Nash equilibrium gives
  the worker `max(μ(e)θ_H + (1 - μ(e))θ_L, r)` (p. 452: both firms offer the expected
  productivity when it is at least `r`).
* `pbe_iff`: a PBE is the same as an education strategy and beliefs satisfying Bayes' rule on
  the path such that each type's education is optimal against the wage schedule
  `w(e) = μ(e)θ_H + (1 - μ(e))θ_L`.
-/

namespace MWG.AdverseSelection

open Set MWG.SimultaneousMoveGames

/-- **Section 13.C** (MWG, p. 450). The two-type signaling model: types `θ_L`, `θ_H`, the
probability `λ` of `θ_H`, home earnings `r` and the education cost `c(e, θ)`. -/
structure SigModel where
  θL : ℝ
  θH : ℝ
  lam : ℝ
  r : ℝ
  c : ℝ → ℝ → ℝ

namespace SigModel

/-- The productivity of type `b` (`true` = high). -/
def θ (M : SigModel) (b : Bool) : ℝ := if b then M.θH else M.θL

/-- `E[θ] = λθ_H + (1 - λ)θ_L`. -/
def Eθ (M : SigModel) : ℝ := M.lam * M.θH + (1 - M.lam) * M.θL

/-- Expected productivity `μθ_H + (1 - μ)θ_L` when the firms' belief that the worker is of high
ability is `μ`. -/
def expProd (M : SigModel) (m : ℝ) : ℝ := m * M.θH + (1 - m) * M.θL

/-- **Section 13.C** (MWG, p. 450). The assumptions on the model. -/
structure Valid (M : SigModel) : Prop where
  θL_pos : 0 < M.θL
  lt : M.θL < M.θH
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  r_nonneg : 0 ≤ M.r
  r_lt : M.r < M.θH
  c_zero : ∀ θ, M.c 0 θ = 0
  c_mono : ∀ b, StrictMonoOn (fun e => M.c e (M.θ b)) (Ici 0)
  c_cont : ∀ b, ContinuousOn (fun e => M.c e (M.θ b)) (Ici 0)
  sc : ∀ e e', 0 ≤ e → e < e' → M.c e' M.θH - M.c e M.θH < M.c e' M.θL - M.c e M.θL

/-- A firm's profit from offering `w` after education `e` when the expected productivity is
`p`: the worker accepts iff `w ≥ r`. -/
noncomputable def offerProfit (M : SigModel) (p : ℝ) (w : ℝ) : ℝ := if M.r ≤ w then p - w else 0

/-- **Section 13.C** (MWG, p. 451). The worker's payoff when she is of type `b`, chooses `e` and
faces the offers `w`: she accepts a highest offer if it is at least `r`. -/
def workerPay (M : SigModel) (b : Bool) (w : Fin 2 → ℝ) (e : ℝ) : ℝ :=
  max (max (w 0) (w 1)) M.r - M.c e (M.θ b)

/-- **Section 13.C** (MWG, p. 452). Beliefs derived from the worker's strategy by Bayes' rule
on the equilibrium path: after the high type's education the belief is `1` if the types
separate and `λ` if they pool; after the low type's education it is `0` if they separate. -/
def BayesOnPath (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Prop :=
  (eS false ≠ eS true → μ (eS true) = 1 ∧ μ (eS false) = 0) ∧
    (eS false = eS true → μ (eS true) = M.lam)

/-- **Section 13.C** (MWG, p. 452). A pure strategy perfect Bayesian equilibrium of the
education signaling game: education choices `e*(θ) ≥ 0`, beliefs `μ(e) ∈ [0, 1]` and wage
offers `w_j(e)` such that (i) each type's education choice is optimal given the firms'
strategies, (ii) beliefs follow Bayes' rule on the path, (iii) after every `e` the offers are a
Nash equilibrium of the firms' wage game with expected productivity `μ(e)θ_H + (1 - μ(e))θ_L`. -/
def IsPBE (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) (wO : ℝ → Fin 2 → ℝ) : Prop :=
  (∀ b, 0 ≤ eS b) ∧ (∀ e, 0 ≤ μ e ∧ μ e ≤ 1) ∧
    (∀ b e, 0 ≤ e → M.workerPay b (wO e) e ≤ M.workerPay b (wO (eS b)) (eS b)) ∧
    M.BayesOnPath eS μ ∧
    ∀ e, 0 ≤ e → IsNashEquilibrium (wageGame (M.offerProfit (M.expProd (μ e)))) (wO e)

/-- A separating equilibrium: the two types choose different education levels. -/
def Separating (eS : Bool → ℝ) : Prop := eS false ≠ eS true

/-- A pooling equilibrium: the two types choose the same education level. -/
def Pooling (eS : Bool → ℝ) : Prop := eS false = eS true

variable {M : SigModel}

theorem θ_true (M : SigModel) : M.θ true = M.θH := rfl
theorem θ_false (M : SigModel) : M.θ false = M.θL := rfl

/-- Expected productivity lies in `[θ_L, θ_H]`. -/
theorem Valid.expProd_mem (hM : M.Valid) {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    M.θL ≤ M.expProd m ∧ M.expProd m ≤ M.θH := by
  unfold expProd
  constructor <;> nlinarith [hM.lt]

theorem expProd_one (M : SigModel) : M.expProd 1 = M.θH := by simp [expProd]
theorem expProd_zero (M : SigModel) : M.expProd 0 = M.θL := by simp [expProd]
theorem expProd_lam (M : SigModel) : M.expProd M.lam = M.Eθ := by simp [expProd, Eθ]

/-- `θ_L < E[θ] < θ_H`. -/
theorem Valid.Eθ_mem (hM : M.Valid) : M.θL < M.Eθ ∧ M.Eθ < M.θH := by
  unfold Eθ
  constructor <;> nlinarith [hM.lt, hM.lam_pos, hM.lam_lt]

/-- `c(e, θ_H) < c(e, θ_L)` for `e > 0` (`c_θ < 0`). -/
theorem Valid.c_lt_of_pos (hM : M.Valid) {e : ℝ} (he : 0 < e) : M.c e M.θH < M.c e M.θL := by
  have := hM.sc 0 e le_rfl he
  rw [hM.c_zero, hM.c_zero] at this
  linarith

/-- `c(e, θ_H) ≤ c(e, θ_L)` for `e ≥ 0`. -/
theorem Valid.c_le (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) : M.c e M.θH ≤ M.c e M.θL := by
  rcases eq_or_lt_of_le he with h | h
  · rw [← h, hM.c_zero, hM.c_zero]
  · exact (hM.c_lt_of_pos h).le

/-- `c(e, θ) ≥ 0` for `e ≥ 0`, and `> 0` for `e > 0`. -/
theorem Valid.c_pos (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 < e) : 0 < M.c e (M.θ b) := by
  have := hM.c_mono b (le_refl (0 : ℝ)) he.le he
  simp only [hM.c_zero] at this
  exact this

theorem Valid.c_nonneg (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 ≤ e) : 0 ≤ M.c e (M.θ b) := by
  rcases eq_or_lt_of_le he with h | h
  · rw [← h, hM.c_zero]
  · exact (hM.c_pos b h).le

/-- The firm's profit in the wage game is right-continuous. -/
theorem offerProfit_rc (M : SigModel) (p x : ℝ) :
    ContinuousWithinAt (M.offerProfit p) (Ici x) x := by
  by_cases hx : M.r ≤ x
  · have hc : ContinuousWithinAt (fun y : ℝ => p - y) (Ici x) x :=
      (continuous_const.sub continuous_id).continuousWithinAt
    refine hc.congr (fun y hy => ?_) ?_
    · simp [offerProfit, hx.trans hy]
    · simp [offerProfit, hx]
  · have hc : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici x) x := continuousWithinAt_const
    refine hc.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.1 hx))] with y hy
      simp [offerProfit, not_le.2 (show y < M.r from hy)]
    · simp [offerProfit, hx]

/-- **Section 13.C** (MWG, p. 452). The Nash equilibria of the wage game after education `e`
with expected productivity `p ≥ 0`: if `p > r` both firms offer exactly `p` (Bertrand); if
`p = r`, any offers `≤ r`; if `p < r`, any offers `< r` (no worker accepts). -/
theorem bertrand_iff (M : SigModel) {p : ℝ} (hp : 0 ≤ p) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (M.offerProfit p)) w ↔
      (M.r < p → w 0 = p ∧ w 1 = p) ∧ (M.r = p → w 0 ≤ p ∧ w 1 ≤ p) ∧
        (p < M.r → w 0 < M.r ∧ w 1 < M.r) := by
  rcases lt_trichotomy M.r p with hlt | heq | hgt
  · rw [wageGame_unique (M.offerProfit_rc p) (by unfold offerProfit; split_ifs <;> linarith)
      (ws := p) (ε := p - M.r) (by linarith) (by simp [offerProfit, hlt.le])
      (fun w hw => by simp [offerProfit, hlt.le.trans hw.le]; linarith)
      (fun w h1 h2 => by simp [offerProfit, show M.r ≤ w by linarith]; linarith) w]
    simp [hlt, hlt.ne, not_lt.2 hlt.le]
  · rw [wageGame_flat (ws := M.r) (fun t ht => by
      unfold offerProfit; split_ifs with h
      · rw [← heq, le_antisymm ht h, sub_self]
      · rfl) (fun t ht => by simp [offerProfit, ht.le]; linarith) w]
    simp [heq]
  · rw [wageGame_flat_open (ws := M.r) (fun t ht => by simp [offerProfit, not_le.2 ht])
      (fun t ht => by simp [offerProfit, ht]; linarith) w]
    simp [hgt, hgt.ne', not_lt.2 hgt.le]

/-- **Section 13.C** (MWG, p. 452). In every Nash equilibrium of the wage game with expected
productivity `p ≥ 0` the worker ends up with `max(p, r)`. -/
theorem bertrand_wage (M : SigModel) {p : ℝ} (hp : 0 ≤ p) (w : Fin 2 → ℝ)
    (hne : IsNashEquilibrium (wageGame (M.offerProfit p)) w) :
    max (max (w 0) (w 1)) M.r = max p M.r := by
  obtain ⟨h1, h2, h3⟩ := (M.bertrand_iff hp w).1 hne
  rcases lt_trichotomy M.r p with hlt | heq | hgt
  · rw [(h1 hlt).1, (h1 hlt).2, max_self]
  · rw [max_eq_right (max_le ((h2 heq).1.trans heq.ge) ((h2 heq).2.trans heq.ge)), heq,
      max_self]
  · rw [max_eq_right (max_le (h3 hgt).1.le (h3 hgt).2.le), max_eq_right hgt.le]

/-- **Section 13.C** (MWG, p. 452). The wage game always has a pure Nash equilibrium: both
firms offer `p` if `p ≥ r`, and `r - 1` otherwise. -/
noncomputable def bertrandOffer (M : SigModel) (p : ℝ) : Fin 2 → ℝ :=
  fun _ => if M.r ≤ p then p else M.r - 1

theorem bertrandOffer_nash (M : SigModel) {p : ℝ} (hp : 0 ≤ p) :
    IsNashEquilibrium (wageGame (M.offerProfit p)) (M.bertrandOffer p) := by
  rw [M.bertrand_iff hp]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [bertrandOffer, h.le]
  · simp [bertrandOffer, h.le]
  · simp [bertrandOffer, not_le.2 h]

theorem bertrandOffer_max (M : SigModel) (p : ℝ) :
    max (max (M.bertrandOffer p 0) (M.bertrandOffer p 1)) M.r = max p M.r := by
  unfold bertrandOffer
  split_ifs with h
  · simp [max_eq_left h]
  · simp [max_eq_right (not_le.1 h).le]

/-- The worker's payoff from education `e` against the equilibrium wage schedule
`w(e) = μ(e)θ_H + (1 - μ(e))θ_L` (she works at home if `w(e) < r`). -/
def redPay (M : SigModel) (μ : ℝ → ℝ) (b : Bool) (e : ℝ) : ℝ :=
  max (M.expProd (μ e)) M.r - M.c e (M.θ b)

/-- **Section 13.C** (MWG, pp. 452-453). The reduced form of a PBE: education choices `≥ 0`,
beliefs in `[0, 1]` derived by Bayes' rule on the path, and each type's education optimal
against the wage schedule `w(e) = μ(e)θ_H + (1 - μ(e))θ_L`. -/
def IsPBERed (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Prop :=
  (∀ b, 0 ≤ eS b) ∧ (∀ e, 0 ≤ μ e ∧ μ e ≤ 1) ∧
    (∀ b e, 0 ≤ e → M.redPay μ b e ≤ M.redPay μ b (eS b)) ∧ M.BayesOnPath eS μ

/-- **Section 13.C** (MWG, p. 452). A PBE gives the worker `w(e) = max(μ(e)θ_H + (1-μ(e))θ_L, r)`
after every education level, so its strategies and beliefs form a reduced-form PBE. -/
theorem Valid.isPBERed_of_isPBE (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    {wO : ℝ → Fin 2 → ℝ} (h : M.IsPBE eS μ wO) : M.IsPBERed eS μ := by
  obtain ⟨h0, hμ, hopt, hB, hNE⟩ := h
  have hw : ∀ e, 0 ≤ e → max (max (wO e 0) (wO e 1)) M.r = max (M.expProd (μ e)) M.r :=
    fun e he => M.bertrand_wage (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)
      _ (hNE e he)
  refine ⟨h0, hμ, fun b e he => ?_, hB⟩
  have := hopt b e he
  unfold workerPay at this
  rw [hw e he, hw _ (h0 b)] at this
  exact this

/-- **Section 13.C** (MWG, p. 452). Conversely, a reduced-form PBE with the Bertrand offers
`bertrandOffer` is a PBE. -/
theorem Valid.isPBE_of_isPBERed (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) : M.IsPBE eS μ (fun e => M.bertrandOffer (M.expProd (μ e))) := by
  obtain ⟨h0, hμ, hopt, hB⟩ := h
  refine ⟨h0, hμ, fun b e he => ?_, hB, fun e _ => M.bertrandOffer_nash
    (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)⟩
  unfold workerPay
  rw [bertrandOffer_max, bertrandOffer_max]
  exact hopt b e he

/-- **Section 13.C** (MWG, p. 452). Strategies and beliefs are part of a PBE iff they form a
reduced-form PBE. -/
theorem Valid.exists_isPBE_iff (hM : M.Valid) (eS : Bool → ℝ) (μ : ℝ → ℝ) :
    (∃ wO, M.IsPBE eS μ wO) ↔ M.IsPBERed eS μ :=
  ⟨fun ⟨_, h⟩ => hM.isPBERed_of_isPBE h, fun h => ⟨_, hM.isPBE_of_isPBERed h⟩⟩

/-- **Section 13.C** (MWG, p. 453). In any PBE the wage after every education level lies in
`[θ_L, θ_H]`. -/
theorem Valid.wage_mem (hM : M.Valid) {μ : ℝ → ℝ} (hμ : ∀ e, 0 ≤ μ e ∧ μ e ≤ 1) (e : ℝ) :
    M.θL ≤ M.expProd (μ e) ∧ M.expProd (μ e) ≤ M.θH :=
  hM.expProd_mem (hμ e).1 (hμ e).2

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Separating and pooling equilibria of the signaling model

MWG, Section 13.C, pp. 453-458 and the small type on pp. 459-460.

All results are stated for home earnings `0 ≤ r < θ_H`; the main text is `r = 0`, where
`max(θ_L, r) = θ_L`, and the small type on p. 459 is `θ_L < r < θ_H`.

* `lemma_13_C_1`, `lemma_13_C_2`: in a separating PBE each type is paid her productivity and the
  low type gets no education.
* `separating_iff`: `(e*(θ_L), e*(θ_H)) = (0, e)` is a separating PBE outcome iff
  `θ_H - c(e, θ_L) ≤ max(θ_L, r) ≤ θ_H - c(e, θ_H)`; for `r = 0` this is `ẽ ≤ e ≤ e₁`
  (`separating_interval`, Figures 13.C.5-13.C.7), with the beliefs of Figure 13.C.6/13.C.7.
* `pooling_iff`: a pooling PBE at `e` exists iff `max(θ_L, r) ≤ max(E[θ], r) - c(e, θ_L)`; for
  `r = 0` this is `e ≤ e'` (Figures 13.C.9-13.C.10).
* Welfare: `separating_pareto_ranked`, `separating_vs_nosignal`, `high_type_worse_as_lam_to_one`
  (Figure 13.C.8), `pooling_dominated`.
* Refinement (pp. 457-458): `refined_separating`: with `μ(e) = 1` for `e > ẽ` the only separating
  education level of the high type is `ẽ`.
* Small type, `r ∈ (θ_L, θ_H)` with `E[θ] < r` (p. 459, Figure 13.C.12): `smalltype_pooling`,
  `smalltype_separating`, `smalltype_pareto`.
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

variable {M : SigModel}

/-- **Lemma 13.C.1** (MWG, p. 453). In any separating PBE the high type is paid `θ_H` and the
low type `θ_L` (in general, each ends up with `max(θ, r)`). -/
theorem lemma_13_C_1 (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} {wO : ℝ → Fin 2 → ℝ}
    (h : M.IsPBE eS μ wO) (hsep : Separating eS) :
    max (max (wO (eS true) 0) (wO (eS true) 1)) M.r = M.θH ∧
      max (max (wO (eS false) 0) (wO (eS false) 1)) M.r = max M.θL M.r := by
  obtain ⟨h0, hμ, -, hB, hNE⟩ := h
  obtain ⟨h1, h2⟩ := hB.1 hsep
  have hw : ∀ e, 0 ≤ e → max (max (wO e 0) (wO e 1)) M.r = max (M.expProd (μ e)) M.r :=
    fun e he => M.bertrand_wage (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)
      _ (hNE e he)
  rw [hw _ (h0 true), hw _ (h0 false), h1, h2, expProd_one, expProd_zero,
    max_eq_left hM.r_lt.le]
  exact ⟨rfl, rfl⟩

/-- **Lemma 13.C.1** (MWG, p. 453), with `r = 0`: the wages are exactly `θ_H` and `θ_L`. -/
theorem lemma_13_C_1_r0 (hM : M.Valid) (hr : M.r = 0) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    {wO : ℝ → Fin 2 → ℝ} (h : M.IsPBE eS μ wO) (hsep : Separating eS) :
    max (max (wO (eS true) 0) (wO (eS true) 1)) M.r = M.θH ∧
      max (max (wO (eS false) 0) (wO (eS false) 1)) M.r = M.θL := by
  have := lemma_13_C_1 hM h hsep
  rw [hr, max_eq_left hM.θL_pos.le] at this
  rw [hr]; exact this

/-- The low type's payoff in any PBE is at least `max(θ_L, r)` (she can choose `e = 0`). -/
theorem Valid.low_payoff (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ) :
    max M.θL M.r ≤ M.redPay μ false (eS false) := by
  have := h.2.2.1 false 0 le_rfl
  unfold redPay at this ⊢
  rw [hM.c_zero, sub_zero] at this
  exact (max_le_max (hM.wage_mem h.2.1 0).1 le_rfl).trans this

/-- **Lemma 13.C.2** (MWG, p. 454). In any separating PBE the low type chooses `e = 0`. -/
theorem lemma_13_C_2 (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hsep : Separating eS) : eS false = 0 := by
  have hlow := hM.low_payoff h
  obtain ⟨-, h2⟩ := h.2.2.2.1 hsep
  unfold redPay at hlow
  rw [h2, expProd_zero] at hlow
  have hc : M.c (eS false) (M.θ false) ≤ 0 := by linarith
  by_contra hne
  have hpos := hM.c_pos false (lt_of_le_of_ne (h.1 false) (Ne.symm hne))
  linarith

/-- The separating beliefs of Figure 13.C.6/13.C.7: high ability iff `e ≥ e_H`. -/
noncomputable def sepBelief (eH : ℝ) : ℝ → ℝ := fun x => if eH ≤ x then 1 else 0

/-- The low type's no-mimicking condition forces `e > 0`, so `(0, e)` separates. -/
theorem separating_sep (hM : M.Valid) {e : ℝ} (he : 0 ≤ e)
    (hL : M.θH - M.c e M.θL ≤ max M.θL M.r) : Separating fun b : Bool => if b then e else 0 := by
  have hepos : 0 < e := by
    by_contra hle
    have he0 : e = 0 := le_antisymm (not_lt.1 hle) he
    rw [he0, hM.c_zero, sub_zero] at hL
    exact absurd hL (not_le.2 (max_lt hM.lt hM.r_lt))
  simp [Separating, hepos.ne]

/-- **Section 13.C** (MWG, pp. 454-455, Figures 13.C.6-13.C.7). Under the conditions of
`separating_iff`, the beliefs `μ(x) = 1` iff `x ≥ e` support `(0, e)` as a separating PBE. -/
theorem separating_sepBelief (hM : M.Valid) {e : ℝ} (he : 0 ≤ e)
    (hL : M.θH - M.c e M.θL ≤ max M.θL M.r) (hH : max M.θL M.r ≤ M.θH - M.c e M.θH) :
    M.IsPBERed (fun b => if b then e else 0) (sepBelief e) := by
  have hepos : 0 < e := by
    by_contra hle
    have he0 : e = 0 := le_antisymm (not_lt.1 hle) he
    rw [he0, hM.c_zero, sub_zero] at hL
    exact absurd hL (not_le.2 (max_lt hM.lt hM.r_lt))
  have hsep : Separating fun b : Bool => if b then e else 0 := by
    simp [Separating, hepos.ne]
  refine ⟨fun b => by cases b <;> simp [he], fun x => ?_, fun b x hx => ?_,
    ⟨fun _ => ?_, fun h => absurd h hsep⟩⟩
  · unfold sepBelief; split_ifs <;> norm_num
  · have hθH : max M.θH M.r = M.θH := max_eq_left hM.r_lt.le
    cases b
    · simp only [redPay, sepBelief, Bool.false_eq_true, ite_false, not_le.2 hepos, θ_false,
        hM.c_zero, sub_zero, expProd_zero]
      split_ifs with hex
      · rw [expProd_one, hθH]
        have := (hM.c_mono false).monotoneOn he hx hex
        simp only [θ_false] at this
        linarith
      · rw [expProd_zero]
        have := hM.c_nonneg false hx
        simp only [θ_false] at this
        linarith
    · simp only [redPay, sepBelief, ite_true, le_refl, expProd_one, hθH, θ_true]
      split_ifs with hex
      · rw [expProd_one, hθH]
        have := (hM.c_mono true).monotoneOn he hx hex
        simp only [θ_true] at this
        linarith
      · rw [expProd_zero]
        have := hM.c_nonneg true hx
        simp only [θ_true] at this
        linarith
  · simp [sepBelief, not_le.2 hepos]

/-- **Section 13.C** (MWG, pp. 454-455). `(0, e)` is the outcome of a separating PBE iff
`θ_H - c(e, θ_L) ≤ max(θ_L, r) ≤ θ_H - c(e, θ_H)`: the low type does not want to mimic the high
type, and the high type does not prefer to be taken for a low type. -/
theorem separating_iff (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      M.θH - M.c e M.θL ≤ max M.θL M.r ∧ max M.θL M.r ≤ M.θH - M.c e M.θH := by
  constructor
  · rintro ⟨μ, h, hsep⟩
    obtain ⟨h1, h2⟩ := h.2.2.2.1 hsep
    simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
    have hL := h.2.2.1 false e he
    have hH := h.2.2.1 true 0 le_rfl
    simp only [redPay, h1, h2, expProd_one, expProd_zero, ite_true, Bool.false_eq_true,
      ite_false, θ_true, θ_false, hM.c_zero, sub_zero, max_eq_left hM.r_lt.le] at hL hH
    exact ⟨hL, hH⟩
  · rintro ⟨hL, hH⟩
    exact ⟨sepBelief e, separating_sepBelief hM he hL hH, separating_sep hM he hL⟩

/-- **Section 13.C** (MWG, pp. 454-455, Figures 13.C.5-13.C.7). With `r = 0`, let `ẽ` solve
`c(ẽ, θ_L) = θ_H - θ_L` and `e₁` solve `θ_H - c(e₁, θ_H) = θ_L`. Then `(0, e)` is a separating PBE
outcome iff `ẽ ≤ e ≤ e₁`. -/
theorem separating_interval (hM : M.Valid) (hr : M.r = 0) {et e1 e : ℝ} (het : 0 ≤ et)
    (he1 : 0 ≤ e1) (he : 0 ≤ e) (hcet : M.c et M.θL = M.θH - M.θL)
    (hce1 : M.θH - M.c e1 M.θH = M.θL) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      et ≤ e ∧ e ≤ e1 := by
  rw [separating_iff hM he, hr, max_eq_left hM.θL_pos.le]
  have hL := (hM.c_mono false).le_iff_le het he
  have hH := (hM.c_mono true).le_iff_le he he1
  simp only [θ_false, θ_true] at hL hH
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hL.1 (by linarith), hH.1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [hL.2 h1], by linarith [hH.2 h2]⟩

/-- The pooling beliefs: `λ` at the pooling level, low ability elsewhere (Figure 13.C.10). -/
noncomputable def poolBelief (M : SigModel) (ep : ℝ) : ℝ → ℝ :=
  fun x => if x = ep then M.lam else 0

/-- **Section 13.C** (MWG, pp. 456-457). Both types choosing `e` is a pooling PBE outcome iff the
low type prefers `(max(E[θ], r), e)` to `(max(θ_L, r), 0)`. -/
theorem pooling_iff (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun _ => e) μ) ↔ max M.θL M.r ≤ max M.Eθ M.r - M.c e M.θL := by
  constructor
  · rintro ⟨μ, h⟩
    have hlow := hM.low_payoff h
    have hB := h.2.2.2.2 rfl
    simp only [redPay, hB, expProd_lam, θ_false] at hlow
    exact hlow
  · intro hL
    refine ⟨M.poolBelief e, fun _ => he, fun x => ?_, fun b x hx => ?_,
      ⟨fun h => absurd rfl h, fun _ => by simp [poolBelief]⟩⟩
    · unfold poolBelief; split_ifs
      · exact ⟨hM.lam_pos.le, hM.lam_lt.le⟩
      · norm_num
    · have hpay : M.redPay (M.poolBelief e) b e = max M.Eθ M.r - M.c e (M.θ b) := by
        simp [redPay, poolBelief, expProd_lam]
      rw [hpay]
      by_cases hxe : x = e
      · rw [hxe, hpay]
      · simp only [redPay, poolBelief, hxe, ite_false, expProd_zero]
        have hc := hM.c_nonneg b hx
        cases b
        · simp only [θ_false] at hc ⊢; linarith
        · simp only [θ_true] at hc ⊢; linarith [hM.c_le he]

/-- **Section 13.C** (MWG, p. 457, Figure 13.C.9). With `r = 0`, if `c(e', θ_L) = E[θ] - θ_L`,
pooling at `e` is a PBE outcome iff `e ≤ e'`. -/
theorem pooling_interval (hM : M.Valid) (hr : M.r = 0) {ep e : ℝ} (hep : 0 ≤ ep) (he : 0 ≤ e)
    (hcep : M.c ep M.θL = M.Eθ - M.θL) : (∃ μ, M.IsPBERed (fun _ => e) μ) ↔ e ≤ ep := by
  rw [pooling_iff hM he, hr, max_eq_left hM.θL_pos.le,
    max_eq_left (hM.θL_pos.trans hM.Eθ_mem.1).le]
  have hL := (hM.c_mono false).le_iff_le he hep
  simp only [θ_false] at hL
  constructor
  · intro h; exact hL.1 (by linarith)
  · intro h; linarith [hL.2 h]

/-- **Section 13.C** (MWG, p. 455). Separating equilibria are Pareto ranked: firms earn zero
and the low type gets `max(θ_L, r)` in all of them, while the high type is strictly better off
with less education. -/
theorem separating_pareto_ranked (hM : M.Valid) {e e' : ℝ} (he : 0 ≤ e) (hlt : e < e') :
    M.θH - M.c e' M.θH < M.θH - M.c e M.θH := by
  have := hM.c_mono true he (he.trans hlt.le) hlt
  simp only [θ_true] at this
  linarith

/-- **Section 13.C** (MWG, p. 455). In a separating PBE the low type gets `max(θ_L, r)` and the
high type `θ_H - c(e*(θ_H), θ_H)`. -/
theorem separating_payoffs (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hsep : Separating eS) :
    M.redPay μ false (eS false) = max M.θL M.r ∧
      M.redPay μ true (eS true) = M.θH - M.c (eS true) M.θH := by
  obtain ⟨h1, h2⟩ := h.2.2.2.1 hsep
  have h0 := lemma_13_C_2 hM h hsep
  refine ⟨?_, ?_⟩
  · rw [h0] at h2 ⊢
    simp only [redPay, h2, expProd_zero, hM.c_zero, sub_zero]
  · simp only [redPay, h1, expProd_one, max_eq_left hM.r_lt.le, θ_true]

/-- **Section 13.C** (MWG, p. 456, Figure 13.C.8). With `r = 0`, compared with the outcome
without signaling (everybody paid `E[θ]`, no education), the low type is strictly worse off in
any separating PBE, and the high type is better off iff `θ_H - c(e*(θ_H), θ_H) ≥ E[θ]`. -/
theorem separating_vs_nosignal (hM : M.Valid) (hr : M.r = 0) :
    max M.θL M.r < M.Eθ ∧ ∀ e, (M.Eθ ≤ M.θH - M.c e M.θH ↔ M.Eθ ≤ M.θH - M.c e M.θH) := by
  rw [hr, max_eq_left hM.θL_pos.le]
  exact ⟨hM.Eθ_mem.1, fun _ => Iff.rfl⟩

/-- **Section 13.C** (MWG, p. 456, Figure 13.C.8(b)). For any positive education level `e`, if
the fraction `λ` of high-ability workers is close enough to `1`, the high type is worse off at
`(θ_H, e)` than at `(E[θ], 0)`: separating equilibria do not depend on `λ`, but `E[θ] → θ_H`. -/
theorem high_type_worse_as_lam_to_one (hM : M.Valid) {e : ℝ} (he : 0 < e) :
    ∃ l0 < 1, ∀ l, l0 < l → l < 1 → M.θH - M.c e M.θH < l * M.θH + (1 - l) * M.θL := by
  have hc : 0 < M.c e M.θH := by
    have := hM.c_pos true he; simpa only [θ_true] using this
  have hgap : 0 < M.θH - M.θL := by linarith [hM.lt]
  refine ⟨1 - M.c e M.θH / (M.θH - M.θL), by linarith [div_pos hc hgap], fun l hl _ => ?_⟩
  have : (1 - l) * (M.θH - M.θL) < M.c e M.θH := by
    have h' : 1 - l < M.c e M.θH / (M.θH - M.θL) := by linarith
    calc (1 - l) * (M.θH - M.θL) < M.c e M.θH / (M.θH - M.θL) * (M.θH - M.θL) :=
          mul_lt_mul_of_pos_right h' hgap
      _ = M.c e M.θH := div_mul_cancel₀ _ hgap.ne'
  nlinarith

/-- **Section 13.C** (MWG, p. 457). Pooling at `e = 0` gives each type `max(E[θ], r)`, exactly
the outcome without signaling, and weakly (for `e > 0` strictly) Pareto dominates pooling at
`e`. -/
theorem pooling_dominated (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 < e) :
    M.redPay (M.poolBelief e) b e < M.redPay (M.poolBelief 0) b 0 ∧
      M.redPay (M.poolBelief 0) b 0 = max M.Eθ M.r := by
  have hpay : ∀ x, M.redPay (M.poolBelief x) b x = max M.Eθ M.r - M.c x (M.θ b) := fun x => by
    simp [redPay, poolBelief, expProd_lam]
  rw [hpay, hpay, hM.c_zero, sub_zero]
  exact ⟨by linarith [hM.c_pos b he], rfl⟩

/-- **Section 13.C** (MWG, pp. 457-458). Above `ẽ` (where `θ_H - c(ẽ, θ_L) = max(θ_L, r)`) the low
type is worse off than at `e = 0` whatever the firms believe: the highest possible wage is
`θ_H`. -/
theorem low_never_above (hM : M.Valid) {et x : ℝ} (het : 0 ≤ et)
    (hcet : M.θH - M.c et M.θL = max M.θL M.r) (hx : et < x) :
    M.θH - M.c x M.θL < max M.θL M.r := by
  have := hM.c_mono false het (het.trans hx.le) hx
  simp only [θ_false] at this
  linarith

/-- **Section 13.C** (MWG, p. 458). If beliefs are reasonable in the sense that `μ(e) = 1` for
every `e > ẽ`, the only separating PBE has the high type choosing `ẽ`. -/
theorem refined_separating (hM : M.Valid) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.θH - M.c et M.θL = max M.θL M.r) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) (hsep : Separating eS) (hμ : ∀ x, et < x → μ x = 1) :
    eS true = et := by
  have h0 := lemma_13_C_2 hM h hsep
  have hpay := separating_payoffs hM h hsep
  obtain ⟨μ', hμ'⟩ : ∃ μ', M.IsPBERed (fun b => if b then eS true else 0) μ' ∧
      Separating fun b => if b then eS true else 0 := by
    refine ⟨μ, ?_, ?_⟩
    · have : (fun b : Bool => if b then eS true else 0) = eS := by
        funext b; cases b <;> simp [h0]
      rw [this]; exact h
    · simpa [Separating, ← h0] using hsep
  have hcond := (separating_iff hM (h.1 true)).1 ⟨μ', hμ'⟩
  have hge : et ≤ eS true := by
    have hL := (hM.c_mono false).le_iff_le het (h.1 true)
    simp only [θ_false] at hL
    exact hL.1 (by linarith [hcond.1])
  by_contra hne
  have hgt : et < eS true := lt_of_le_of_ne hge (Ne.symm hne)
  set x := (et + eS true) / 2
  have hx1 : et < x := by simp only [x]; linarith
  have hx2 : x < eS true := by simp only [x]; linarith
  have hdev := h.2.2.1 true x (het.trans hx1.le)
  rw [hpay.2] at hdev
  simp only [redPay, hμ x hx1, expProd_one, max_eq_left hM.r_lt.le, θ_true] at hdev
  have := hM.c_mono true (het.trans hx1.le) (h.1 true) hx2
  simp only [θ_true] at this
  linarith

/-- **Appendix 13.A** (MWG, p. 470). If `μ(e) = 1` for every `e > ẽ`, then in any pooling PBE the
high type gets at least `θ_H - c(ẽ, θ_H)` (she could deviate to just above `ẽ`); hence when the
high type prefers `(θ_H, ẽ)` to `(max(E[θ], r), 0)` no pooling PBE has such beliefs. -/
theorem pooling_eliminated (hM : M.Valid) {et : ℝ} (het : 0 ≤ et) {e : ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed (fun _ => e) μ) (hμ : ∀ x, et < x → μ x = 1) :
    M.θH - M.c et M.θH ≤ M.redPay μ true e := by
  by_contra hlt
  rw [not_le] at hlt
  have hc : ContinuousWithinAt (fun x => M.c x (M.θ true)) (Ioi et) et :=
    ((hM.c_cont true) et het).mono (fun x hx => het.trans (le_of_lt hx))
  have hev : ∀ᶠ x in nhdsWithin et (Ioi et), M.c x M.θH < M.θH - M.redPay μ true e :=
    hc.eventually (gt_mem_nhds (by simp only [θ_true]; linarith))
  obtain ⟨x, hx, hxe⟩ := (hev.and self_mem_nhdsWithin).exists
  have hdev := h.2.2.1 true x (het.trans (le_of_lt hxe))
  simp only [redPay, hμ x hxe, expProd_one, max_eq_left hM.r_lt.le, θ_true] at hdev
  simp only [redPay, θ_true] at hx
  linarith

/-- **Section 13.C, small type** (MWG, p. 459). With `θ_L < r < θ_H` and `E[θ] < r`, every
pooling PBE has both types choosing `e = 0` and staying at home. -/
theorem smalltype_pooling (hM : M.Valid) (hr1 : M.θL < M.r) (hEr : M.Eθ < M.r) {e : ℝ}
    (he : 0 ≤ e) (h : ∃ μ, M.IsPBERed (fun _ => e) μ) : e = 0 ∧ M.Eθ < M.r := by
  have := (pooling_iff hM he).1 h
  rw [max_eq_right hr1.le, max_eq_right hEr.le] at this
  refine ⟨?_, hEr⟩
  by_contra hne
  have := hM.c_pos false (lt_of_le_of_ne he (Ne.symm hne))
  simp only [θ_false] at this
  linarith

/-- **Section 13.C, small type** (MWG, pp. 459-460, Figure 13.C.12). With `θ_L < r < θ_H`, `(0, e)`
is a separating PBE outcome iff `θ_H - c(e, θ_L) ≤ r ≤ θ_H - c(e, θ_H)`, i.e. `e ∈ [ẽ, e₂]`. -/
theorem smalltype_separating (hM : M.Valid) (hr1 : M.θL < M.r) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      M.θH - M.c e M.θL ≤ M.r ∧ M.r ≤ M.θH - M.c e M.θH := by
  rw [separating_iff hM he, max_eq_right hr1.le]

/-- **Section 13.C, small type** (MWG, pp. 459-460). With `θ_L < r < θ_H` and `E[θ] < r`, in every
PBE each type gets at least `r`, her payoff without signaling (where nobody is employed), and the
low type gets exactly `r`; in a separating PBE with `θ_H - c(e*(θ_H), θ_H) > r` the high type is
strictly better off. -/
theorem smalltype_pareto (hM : M.Valid) (hr1 : M.θL < M.r) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) :
    M.r ≤ M.redPay μ false (eS false) ∧ M.r ≤ M.redPay μ true (eS true) := by
  have hlow := hM.low_payoff h
  rw [max_eq_right hr1.le] at hlow
  refine ⟨hlow, ?_⟩
  have := h.2.2.1 true 0 le_rfl
  simp only [redPay, hM.c_zero, sub_zero] at this ⊢
  exact (le_max_right _ _).trans this

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Second-best intervention: cross-subsidization (Exercise 13.C.3)

MWG, Section 13.C, pp. 458-459, Figure 13.C.11 and Exercise 13.C.3.

`crossModel`: `θ_L = 1`, `θ_H = 2`, `λ = 1/3`, `r = 0`, and `c(e, θ) = (2 - θ)e + (θ - 1)e²/(1 + e)`
(so `c(e, θ_L) = e`, `c(e, θ_H) = e²/(1 + e)`; `c_θ < 0`, `c_{eθ} = -(1 + e)⁻² < 0`).

* `crossModel_valid`: it satisfies the assumptions, giving concrete instances of the separating
  and pooling characterizations (`crossModel_separating`, `crossModel_pooling`).
* `exercise_13_C_3`: in the best separating equilibrium (`(θ_L, 0)`, `(θ_H, ẽ = 1)`) banning
  signaling (everybody gets `(E[θ], 0) = (4/3, 0)`) makes the high type worse off, while the
  cross-subsidizing wage schedule `ŵ_L = 11/10` for `e < 71/100`, `ŵ_H = 9/5` for `e ≥ 71/100`
  makes both types strictly better off, with firms breaking even on average.

Departure. With linear indifference curves for both types (the exercise's hint, e.g.
`c(e, θ) = e/θ`) a cross-subsidy that improves on the best separating equilibrium exists exactly
when banning does, because all payoffs are linear in the subsidy; the example therefore keeps
the low type's curve linear and makes the high type's strictly convex (`c_{ee} > 0` fails for
the low type; the chapter's results do not use it).
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

/-- **Exercise 13.C.3** (MWG, p. 459). The model of the example. -/
noncomputable def crossModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 3
  r := 0
  c := fun e θ => (2 - θ) * e + (θ - 1) * (e ^ 2 / (1 + e))

theorem crossModel_cL (e : ℝ) : crossModel.c e crossModel.θL = e := by
  simp [crossModel]; ring

theorem crossModel_cH (e : ℝ) : crossModel.c e crossModel.θH = e ^ 2 / (1 + e) := by
  simp [crossModel]; norm_num

theorem crossModel_cH_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 / (1 + a) < b ^ 2 / (1 + b) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (sub_pos.2 hab) (by nlinarith : 0 < a + b + a * b)]

/-- **Exercise 13.C.3** (MWG, p. 459). The example satisfies the assumptions of Section 13.C. -/
theorem crossModel_valid : crossModel.Valid where
  θL_pos := by norm_num [crossModel]
  lt := by norm_num [crossModel]
  lam_pos := by norm_num [crossModel]
  lam_lt := by norm_num [crossModel]
  r_nonneg := by norm_num [crossModel]
  r_lt := by norm_num [crossModel]
  c_zero := fun θ => by simp [crossModel]
  c_mono := fun b => by
    cases b
    · intro a _ b _ hab; simp only [θ_false, crossModel_cL]; exact hab
    · intro a ha b _ hab; simp only [θ_true, crossModel_cH]; exact crossModel_cH_lt ha hab
  c_cont := fun b => by
    cases b
    · simp only [θ_false, crossModel_cL]; exact continuousOn_id
    · simp only [θ_true, crossModel_cH]
      exact ((continuous_pow 2).continuousOn).div (continuous_const.add continuous_id).continuousOn
        fun x hx => by have : (0 : ℝ) ≤ x := hx; positivity
  sc := fun e e' he hlt => by
    rw [crossModel_cH, crossModel_cH, crossModel_cL, crossModel_cL]
    have hne' : (1 + e') ≠ 0 := by linarith
    have hne : (1 + e) ≠ 0 := by linarith
    have h1 : e' - e' ^ 2 / (1 + e') = e' / (1 + e') := by field_simp; ring
    have h2 : e - e ^ 2 / (1 + e) = e / (1 + e) := by field_simp; ring
    have : e / (1 + e) < e' / (1 + e') := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith

/-- **Section 13.C** (MWG, pp. 454-455), an instance: in `crossModel` the best separating
equilibrium `(e*(θ_L), e*(θ_H)) = (0, ẽ) = (0, 1)` is a PBE. -/
theorem crossModel_separating :
    ∃ μ wO, crossModel.IsPBE (fun b => if b then 1 else 0) μ wO ∧
      Separating fun b : Bool => if b then (1 : ℝ) else 0 := by
  have h := (separating_iff crossModel_valid (e := 1) zero_le_one).2 (by
    rw [crossModel_cL, crossModel_cH]; simp [crossModel]; norm_num)
  obtain ⟨μ, hμ, hsep⟩ := h
  exact ⟨μ, _, crossModel_valid.isPBE_of_isPBERed hμ, hsep⟩

/-- **Section 13.C** (MWG, pp. 456-457), an instance: pooling at `e = 0` is a PBE outcome. -/
theorem crossModel_pooling : ∃ μ, crossModel.IsPBERed (fun _ => 0) μ := by
  refine (pooling_iff crossModel_valid le_rfl).2 ?_
  simp [crossModel, Eθ]; norm_num

/-- **Exercise 13.C.3** (MWG, p. 459), the cross-subsidizing wage schedule of Figure 13.C.11. -/
noncomputable def crossWage (e : ℝ) : ℝ := if 71 / 100 ≤ e then 9 / 5 else 11 / 10

/-- **Exercise 13.C.3** (MWG, p. 459). In `crossModel`:
(1) banning signaling (everyone at `(E[θ], 0)`) leaves the high type strictly worse off than in
the best separating equilibrium, so it is not a Pareto improvement;
(2) under the mandated schedule `crossWage` the low type optimally chooses `e = 0` and the high
type `e = 71/100`; both are strictly better off than in the best separating equilibrium
(`θ_L` and `θ_H - c(1, θ_H) = 3/2`), and firms break even on average (they lose on low types
and gain on high types). -/
theorem exercise_13_C_3 :
    crossModel.Eθ < crossModel.θH - crossModel.c 1 crossModel.θH ∧
      (∀ e, 0 ≤ e → crossWage e - crossModel.c e crossModel.θL ≤
        crossWage 0 - crossModel.c 0 crossModel.θL) ∧
      (∀ e, 0 ≤ e → crossWage e - crossModel.c e crossModel.θH ≤
        crossWage (71 / 100) - crossModel.c (71 / 100) crossModel.θH) ∧
      (1 - crossModel.lam) * (crossModel.θL - crossWage 0) +
        crossModel.lam * (crossModel.θH - crossWage (71 / 100)) = 0 ∧
      crossModel.θL < crossWage 0 - crossModel.c 0 crossModel.θL ∧
      crossModel.θH - crossModel.c 1 crossModel.θH <
        crossWage (71 / 100) - crossModel.c (71 / 100) crossModel.θH ∧
      crossModel.θL - crossWage 0 < 0 ∧ 0 < crossModel.θH - crossWage (71 / 100) := by
  simp only [crossModel_cL, crossModel_cH]
  refine ⟨by simp [crossModel, Eθ]; norm_num, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold crossWage; split_ifs with h <;> norm_num <;> linarith
  · have hv : (71 / 100 : ℝ) ^ 2 / (1 + 71 / 100) = 5041 / 17100 := by norm_num
    have hw : crossWage (71 / 100) = 9 / 5 := by simp [crossWage]
    rw [hv, hw]
    unfold crossWage
    split_ifs with h
    · have hm : (71 / 100 : ℝ) ^ 2 / (1 + 71 / 100) ≤ e ^ 2 / (1 + e) := by
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h']
        · exact (crossModel_cH_lt (by norm_num) h').le
      rw [hv] at hm
      norm_num
      linarith
    · have : 0 ≤ e ^ 2 / (1 + e) := by positivity
      norm_num
      linarith
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Reasonable-beliefs refinements in signaling games

MWG, Appendix A to Chapter 13, pp. 467-472.

A signaling game (`SignalingGame`): player 1 has a type `θ` in a finite set `Θ` with prior
`f(θ) > 0` and chooses `a ∈ A`; the other players `j ∈ J` see `a` and choose `s_j ∈ S_j`
simultaneously. After `a`, given a belief `μ` on `Θ`, the responders play the normal form game
`responseGame G a μ` of Chapter 8 (expected payoffs).

* `IsPBE` is the perfect Bayesian equilibrium of p. 468 (pure strategies, conditions (i)-(iii)).
* `DominatedFor` is (13.AA.1) (and, relative to a set of responses, (13.AA.2)); `typesUndominated`
  is `Θ(a)`; `eqResponses G T a` is `S*(Θ̂, a)`; `typesUndominatedStar` is `Θ*(a)`;
  `EqDominated` is (13.AA.3) and `typesNotEqDominated` is `Θ**(a)`; `ReasonableBeliefs`;
  `ViolatesIC` is the intuitive criterion (13.AA.4).
* `eqDominated_of_dominated` (p. 471): an action dominated in the sense of (13.AA.2) is
  equilibrium dominated.
* `passesIC_of_reasonable` (p. 471): a PBE with reasonable beliefs (relative to `Θ**`) passes
  the intuitive criterion.
* `two_types_singleton`, `two_types_reasonable` (p. 472): with two types, when equilibrium
  domination eliminates a type there is only one admissible belief, and a PBE passing the
  intuitive criterion stays a PBE when that belief is imposed.
* `example_13_AA_1` (p. 472): with three types a PBE can pass the intuitive criterion although no
  PBE with the same outcome has reasonable beliefs.

Departures. "`Min_{s'} u₁(a', s', θ) > Max_s u₁(a, s, θ)`" is read as "every payoff from `a'`
exceeds every payoff from `a`" (equivalent when the minimum and maximum exist, as the book
presupposes). In (13.AA.4), when `Θ**(a) = ∅` we use all beliefs (`S*(Θ, a)`), matching the
convention for reasonable beliefs ("for all `a` with `Θ**(a) ≠ ∅`").
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset

/-- **Appendix A** (MWG, p. 467). A signaling game: payoffs `u₁(a, s, θ)` of player 1 and
`u_j(a, s, θ)` of the responders `j ∈ J`. -/
structure SignalingGame (Θ A J : Type*) (S : J → Type*) where
  u1 : A → ((j : J) → S j) → Θ → ℝ
  u : J → A → ((j : J) → S j) → Θ → ℝ

namespace SignalingGame

variable {Θ A J : Type*} {S : J → Type*} [Fintype Θ] [DecidableEq J]

/-- A belief on `Θ` concentrated on `T`. -/
def IsBeliefOn (T : Set Θ) (μ : Θ → ℝ) : Prop :=
  (∀ θ, 0 ≤ μ θ) ∧ ∑ θ, μ θ = 1 ∧ ∀ θ, 0 < μ θ → θ ∈ T

/-- **Appendix A** (MWG, p. 468). The responders' simultaneous-move game after `a` when the
probability of type `θ` is `μ(θ)`. -/
def responseGame (G : SignalingGame Θ A J S) (a : A) (μ : Θ → ℝ) : NormalForm J S where
  payoff j s := ∑ θ, μ θ * G.u j a s θ

open Classical in
/-- **Appendix A** (MWG, p. 468). A pure strategy perfect Bayesian equilibrium: (i) each type's
action is optimal, (ii) beliefs are derived by Bayes' rule on the path, (iii) after every `a`
the responses are a Nash equilibrium of the response game given the belief `μ(·|a)`. -/
def IsPBE (G : SignalingGame Θ A J S) (f : Θ → ℝ) (aS : Θ → A) (sS : A → (j : J) → S j)
    (μ : A → Θ → ℝ) : Prop :=
  (∀ θ a, G.u1 a (sS a) θ ≤ G.u1 (aS θ) (sS (aS θ)) θ) ∧
    (∀ a θ, (∃ θ', aS θ' = a) →
      μ a θ * ∑ θ' ∈ univ.filter (fun θ' => aS θ' = a), f θ' = if aS θ = a then f θ else 0) ∧
    ∀ a, IsBeliefOn Set.univ (μ a) ∧ IsNashEquilibrium (G.responseGame a (μ a)) (sS a)

/-- **(13.AA.1)-(13.AA.2)** (MWG, pp. 468-469). Action `a` is strictly dominated for type `θ`
relative to response sets `R a`: some `a'` does better against every response in `R a'` than
`a` does against any response in `R a`. With `R = univ` this is (13.AA.1). -/
def DominatedFor (G : SignalingGame Θ A J S) (R : A → Set ((j : J) → S j)) (a : A) (θ : Θ) :
    Prop :=
  ∃ a', ∀ s ∈ R a, ∀ s' ∈ R a', G.u1 a s θ < G.u1 a' s' θ

/-- **Appendix A** (MWG, p. 468). `Θ(a)`: the types for which `a` is not strictly dominated in the
sense of (13.AA.1). -/
def typesUndominated (G : SignalingGame Θ A J S) (a : A) : Set Θ :=
  {θ | ¬ G.DominatedFor (fun _ => Set.univ) a θ}

/-- **Appendix A** (MWG, p. 469). `S*(Θ̂, a)`: the equilibrium responses to `a` for some belief
concentrated on `Θ̂`. -/
def eqResponses (G : SignalingGame Θ A J S) (T : Set Θ) (a : A) : Set ((j : J) → S j) :=
  {s | ∃ μ, IsBeliefOn T μ ∧ IsNashEquilibrium (G.responseGame a μ) s}

/-- **Appendix A** (MWG, p. 469). `Θ*(a)`: types for which `a` is not dominated in the sense of
(13.AA.2). -/
def typesUndominatedStar (G : SignalingGame Θ A J S) (a : A) : Set Θ :=
  {θ | ¬ G.DominatedFor (G.eqResponses Set.univ) a θ}

/-- **(13.AA.3)** (MWG, p. 471). Action `a` is equilibrium dominated for `θ` in a PBE with
equilibrium payoffs `uS`: every equilibrium response to `a` gives `θ` less than `uS θ`. -/
def EqDominated (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) (θ : Θ) : Prop :=
  ∀ s ∈ G.eqResponses Set.univ a, G.u1 a s θ < uS θ

/-- **Appendix A** (MWG, p. 471). `Θ**(a)`. -/
def typesNotEqDominated (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) : Set Θ :=
  {θ | ¬ G.EqDominated uS a θ}

/-- **Appendix A** (MWG, pp. 468-471). Beliefs are reasonable relative to `T`: whenever `T a` is
nonempty, `μ(θ | a) > 0` only for `θ ∈ T a`. -/
def ReasonableBeliefs (T : A → Set Θ) (μ : A → Θ → ℝ) : Prop :=
  ∀ a, (T a).Nonempty → ∀ θ, 0 < μ a θ → θ ∈ T a

/-- The equilibrium payoff `u₁*(θ)` of type `θ`. -/
def eqPayoff (G : SignalingGame Θ A J S) (aS : Θ → A) (sS : A → (j : J) → S j) (θ : Θ) : ℝ :=
  G.u1 (aS θ) (sS (aS θ)) θ

open Classical in
/-- The set of types used by the intuitive criterion at `a`: `Θ**(a)`, or all types if it is
empty. -/
noncomputable def icTypes (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) : Set Θ :=
  if (G.typesNotEqDominated uS a).Nonempty then G.typesNotEqDominated uS a else Set.univ

/-- **(13.AA.4)** (MWG, p. 471). A PBE with equilibrium payoffs `uS` violates the intuitive
criterion if some type `θ` has a deviation `a` that gives her more than `uS θ` against every
equilibrium response to beliefs concentrated on `Θ**(a)`. -/
def ViolatesIC (G : SignalingGame Θ A J S) (uS : Θ → ℝ) : Prop :=
  ∃ θ a, ∀ s ∈ G.eqResponses (G.icTypes uS a) a, uS θ < G.u1 a s θ

/-- In a PBE the response to every action is an equilibrium response. -/
theorem IsPBE.mem_eqResponses {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) (a : A) :
    sS a ∈ G.eqResponses Set.univ a :=
  ⟨μ a, (h.2.2 a).1, (h.2.2 a).2⟩

/-- **Appendix A** (MWG, p. 471). In a PBE, an action that is strictly dominated for `θ` in the
sense of (13.AA.2) is equilibrium dominated for `θ`: `Θ**(a) ⊆ Θ*(a)`. -/
theorem eqDominated_of_dominated {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) {a : A} {θ : Θ}
    (hd : G.DominatedFor (G.eqResponses Set.univ) a θ) :
    G.EqDominated (G.eqPayoff aS sS) a θ := by
  obtain ⟨a', ha'⟩ := hd
  intro s hs
  exact (ha' s hs (sS a') (h.mem_eqResponses a')).trans_le (h.1 θ a')

/-- **Appendix A** (MWG, p. 471). `Θ**(a) ⊆ Θ*(a)`. -/
theorem typesNotEqDominated_subset {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) (a : A) :
    G.typesNotEqDominated (G.eqPayoff aS sS) a ⊆ G.typesUndominatedStar a :=
  fun _ hθ hd => hθ (eqDominated_of_dominated h hd)

/-- **Appendix A** (MWG, p. 471). A PBE whose beliefs are reasonable relative to `Θ**` passes the
intuitive criterion. -/
theorem passesIC_of_reasonable {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ)
    (hr : ReasonableBeliefs (G.typesNotEqDominated (G.eqPayoff aS sS)) μ) :
    ¬ G.ViolatesIC (G.eqPayoff aS sS) := by
  rintro ⟨θ, a, hv⟩
  have hmem : sS a ∈ G.eqResponses (G.icTypes (G.eqPayoff aS sS) a) a := by
    refine ⟨μ a, ⟨(h.2.2 a).1.1, (h.2.2 a).1.2.1, fun θ' hθ' => ?_⟩, (h.2.2 a).2⟩
    unfold icTypes
    split_ifs with hne
    · exact hr a hne θ' hθ'
    · trivial
  exact absurd (h.1 θ a) (not_le.2 (hv _ hmem))

/-- **Appendix A** (MWG, p. 472). With two types, a belief concentrated on a single type is the
point mass on it: when equilibrium domination eliminates one type there is only one admissible
belief. -/
theorem two_types_singleton {μ : Bool → ℝ} {b : Bool} (h : IsBeliefOn {b} μ) :
    μ b = 1 ∧ μ (!b) = 0 := by
  obtain ⟨h0, h1, hs⟩ := h
  have hnb : μ (!b) = 0 := by
    by_contra hne
    have := hs (!b) (lt_of_le_of_ne (h0 _) (Ne.symm hne))
    cases b <;> simp at this
  refine ⟨?_, hnb⟩
  rw [Fintype.sum_bool] at h1
  cases b <;> simp_all

/-- **Appendix A** (MWG, p. 472). With two types, if a PBE passes the intuitive criterion and
equilibrium domination at an off-path action `a` eliminates all but type `b`
(`Θ**(a) = {b}`), then imposing the only admissible belief (`b` for sure) together with a
suitable equilibrium response keeps it a PBE with the same outcome: the intuitive criterion and
reasonable beliefs make the same predictions. -/
theorem two_types_reasonable {A J : Type*} {S : J → Type*} [DecidableEq J] [DecidableEq A]
    {G : SignalingGame Bool A J S} {f : Bool → ℝ} {aS : Bool → A} {sS : A → (j : J) → S j}
    {μ : A → Bool → ℝ} (h : G.IsPBE f aS sS μ) (hIC : ¬ G.ViolatesIC (G.eqPayoff aS sS))
    {a : A} (hoff : ∀ θ, aS θ ≠ a) {b : Bool}
    (hb : G.typesNotEqDominated (G.eqPayoff aS sS) a = {b}) :
    ∃ s ν, IsBeliefOn {b} ν ∧
      G.IsPBE f aS (Function.update sS a s) (Function.update μ a ν) := by
  have hic : G.icTypes (G.eqPayoff aS sS) a = {b} := by
    simp [icTypes, hb]
  unfold ViolatesIC at hIC
  push Not at hIC
  obtain ⟨s, hs, hsb⟩ := hIC b a
  rw [hic] at hs
  obtain ⟨ν, hν, hne⟩ := hs
  have hsame : ∀ θ, Function.update sS a s (aS θ) = sS (aS θ) := fun θ =>
    Function.update_of_ne (hoff θ) _ _
  refine ⟨s, ν, hν, ⟨fun θ a' => ?_, fun a' θ ha' => ?_, fun a' => ?_⟩⟩
  · rw [hsame]
    by_cases ha : a' = a
    · subst ha
      rw [Function.update_self]
      by_cases hθ : θ = b
      · subst hθ; exact hsb
      · have hθd : θ ∉ G.typesNotEqDominated (G.eqPayoff aS sS) a' := by
          rw [hb]; exact hθ
        simp only [typesNotEqDominated, Set.mem_ofPred_eq, not_not] at hθd
        refine (hθd s ⟨ν, ⟨hν.1, hν.2.1, fun _ _ => trivial⟩, hne⟩).le
    · rw [Function.update_of_ne ha]; exact h.1 θ a'
  · have ha : a' ≠ a := by
      rintro rfl; obtain ⟨θ', h'⟩ := ha'; exact hoff θ' h'
    rw [Function.update_of_ne ha]; exact h.2.1 a' θ ha'
  · by_cases ha : a' = a
    · subst ha
      rw [Function.update_self, Function.update_self]
      exact ⟨⟨hν.1, hν.2.1, fun _ _ => trivial⟩, hne⟩
    · rw [Function.update_of_ne ha, Function.update_of_ne ha]; exact h.2.2 a'

end SignalingGame

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Example 13.AA.1: the intuitive criterion versus reasonable beliefs with three types

MWG, Appendix A, pp. 471-472.

Three types `θ₁, θ₂, θ₃` (`Fin 3`), equally likely; player 1 chooses `false` (the equilibrium
action) or `true` (the deviation `â`); one responder chooses `s ∈ ℝ` with payoff
`-(s - g(θ))²`, `g = (-2, 1, 0)`, so after `â` her unique best response to a belief `μ` is
`s = μ(θ₂) - 2μ(θ₁)`. Player 1 gets `0` from `false`; from `â`, type `θ₁` gets `-1`, type `θ₂`
gets `1` if `s ≥ 1/4` (else `-1`) and type `θ₃` gets `1` if `0 ≤ s ≤ 3/4` (else `-1`). For
beliefs concentrated on `{θ₂, θ₃}`, `s = μ(θ₂|â)`: type `θ₂` strictly prefers to deviate iff
`μ(θ₂|â) ≥ 1/4` and type `θ₃` iff `μ(θ₂|â) ≤ 3/4`, as in the book.

* `example_13_AA_1_pbe`: everybody choosing `false`, with belief `θ₁` after `â`, is a PBE;
* `example_13_AA_1_eqdom`: `Θ**(â) = {θ₂, θ₃}`;
* `example_13_AA_1_ic`: this PBE passes the intuitive criterion;
* `example_13_AA_1_no_reasonable`: no PBE with this outcome has reasonable beliefs.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- The responder's target `g(θ)`. -/
def exG : Fin 3 → ℝ := ![-2, 1, 0]

/-- **Example 13.AA.1** (MWG, p. 472). The signaling game. -/
noncomputable def exGame : SignalingGame (Fin 3) Bool Unit (fun _ => ℝ) where
  u1 a s θ := if a then
      (if θ = 0 then -1 else if θ = 1 then (if 1 / 4 ≤ s () then 1 else -1)
        else (if 0 ≤ s () ∧ s () ≤ 3 / 4 then 1 else -1))
    else 0
  u _ _ s θ := -(s () - exG θ) ^ 2

/-- The uniform prior. -/
noncomputable def exPrior : Fin 3 → ℝ := fun _ => 1 / 3

/-- The responder's expected payoff is `-(s - m)²` plus a constant, `m = Σ μ(θ) g(θ)`. -/
theorem exGame_payoff (a : Bool) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    (exGame.responseGame a μ).payoff () s =
      -(s () - ∑ θ, μ θ * exG θ) ^ 2 + ((∑ θ, μ θ * exG θ) ^ 2 - ∑ θ, μ θ * exG θ ^ 2) := by
  simp only [SignalingGame.responseGame, exGame, Fin.sum_univ_three] at hμ ⊢
  have : μ 2 = 1 - μ 0 - μ 1 := by linarith
  rw [this]; ring

/-- After any action, the responder's unique equilibrium response to `μ` is `Σ μ(θ) g(θ)`. -/
theorem exGame_nash_iff (a : Bool) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    IsNashEquilibrium (exGame.responseGame a μ) s ↔ s () = ∑ θ, μ θ * exG θ := by
  constructor
  · intro h
    have := h () (∑ θ, μ θ * exG θ)
    rw [exGame_payoff a μ hμ, exGame_payoff a μ hμ, Function.update_self, sub_self] at this
    nlinarith [sq_nonneg (s () - ∑ θ, μ θ * exG θ)]
  · intro h i t
    rw [exGame_payoff a μ hμ, exGame_payoff a μ hμ, h]
    nlinarith [sq_nonneg (Function.update s i t () - ∑ θ, μ θ * exG θ)]

/-- The point mass on `θ`. -/
def pointMass (θ : Fin 3) : Fin 3 → ℝ := fun θ' => if θ' = θ then 1 else 0

theorem pointMass_belief (θ : Fin 3) (T : Set (Fin 3)) (hθ : θ ∈ T) :
    IsBeliefOn T (pointMass θ) := by
  refine ⟨fun θ' => by unfold pointMass; split_ifs <;> norm_num, ?_, fun θ' h => ?_⟩
  · simp [pointMass]
  · unfold pointMass at h; split_ifs at h with he
    · rw [he]; exact hθ
    · norm_num at h

theorem pointMass_resp (θ : Fin 3) : ∑ θ', pointMass θ θ' * exG θ' = exG θ := by
  simp [pointMass]

/-- The equilibrium responses to `â` for beliefs concentrated on `T`. -/
theorem exGame_eqResponses (T : Set (Fin 3)) (a : Bool) (s : Unit → ℝ) :
    s ∈ exGame.eqResponses T a ↔ ∃ μ, IsBeliefOn T μ ∧ s () = ∑ θ, μ θ * exG θ := by
  constructor
  · rintro ⟨μ, hμ, hne⟩; exact ⟨μ, hμ, (exGame_nash_iff a μ hμ.2.1 s).1 hne⟩
  · rintro ⟨μ, hμ, hs⟩; exact ⟨μ, hμ, (exGame_nash_iff a μ hμ.2.1 s).2 hs⟩

/-- **Example 13.AA.1** (MWG, p. 472). With equilibrium payoffs `0`, `â` is equilibrium dominated
for `θ₁` only: `Θ**(â) = {θ₂, θ₃}`. -/
theorem example_13_AA_1_eqdom :
    exGame.typesNotEqDominated (fun _ => 0) true = {1, 2} := by
  ext θ
  simp only [SignalingGame.typesNotEqDominated, SignalingGame.EqDominated, Set.mem_ofPred_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases θ
  · simp only [exGame]; norm_num
  · simp only [exGame]
    norm_num
    refine ⟨fun _ => 1, (exGame_eqResponses _ _ _).2 ⟨pointMass 1, pointMass_belief 1 _ trivial,
      by rw [pointMass_resp]; simp [exG]⟩, by norm_num⟩
  · simp only [exGame]
    norm_num
    refine ⟨fun _ => 0, (exGame_eqResponses _ _ _).2 ⟨pointMass 2, pointMass_belief 2 _ trivial,
      by rw [pointMass_resp]; simp [exG]⟩, by norm_num⟩

/-- The responses of the PBE: `-2` after `â` (belief `θ₁`), `-1/3` after `false` (prior). -/
noncomputable def exResp (a : Bool) : Unit → ℝ := if a then fun _ => -2 else fun _ => -1 / 3

/-- The beliefs of the PBE. -/
noncomputable def exBelief (a : Bool) : Fin 3 → ℝ := if a then pointMass 0 else exPrior

theorem exPrior_belief : IsBeliefOn Set.univ exPrior :=
  ⟨fun _ => by norm_num [exPrior], by simp [exPrior],
    fun _ _ => trivial⟩

/-- The equilibrium payoffs are `0` whenever everybody plays `false`. -/
theorem exGame_eqPayoff (sS : Bool → Unit → ℝ) :
    exGame.eqPayoff (fun _ => false) sS = fun _ => 0 := by
  funext θ; simp [SignalingGame.eqPayoff, exGame]

/-- **Example 13.AA.1** (MWG, p. 472). All types choosing `false`, with belief `θ₁` after `â`, is
a PBE. -/
theorem example_13_AA_1_pbe : exGame.IsPBE exPrior (fun _ => false) exResp exBelief := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ?_⟩
  · cases a
    · exact le_rfl
    · fin_cases θ <;> simp [exGame, exResp] <;> norm_num
  · obtain ⟨_, h⟩ := ha
    subst h
    simp [exBelief, exPrior]
  · cases a
    · refine ⟨exPrior_belief, (exGame_nash_iff _ _ exPrior_belief.2.1 _).2 ?_⟩
      simp [exResp, exPrior, exG, Fin.sum_univ_three]; norm_num
    · refine ⟨pointMass_belief 0 _ trivial,
        (exGame_nash_iff _ _ (pointMass_belief 0 Set.univ trivial).2.1 _).2 ?_⟩
      simp only [exResp, ite_true]
      rw [pointMass_resp]; simp [exG]

/-- **Example 13.AA.1** (MWG, p. 472). This PBE does not violate the intuitive criterion: for
every type and deviation some equilibrium response to beliefs on `Θ**(â) = {θ₂, θ₃}` leaves the
type no better off. -/
theorem example_13_AA_1_ic :
    ¬ exGame.ViolatesIC (exGame.eqPayoff (fun _ => false) exResp) := by
  rw [exGame_eqPayoff]
  rintro ⟨θ, a, hv⟩
  have hict : exGame.icTypes (fun _ => 0) true = {1, 2} := by
    simp [icTypes, example_13_AA_1_eqdom]
  have hresp0 : (fun _ => -1 / 3 : Unit → ℝ) ∈ exGame.eqResponses Set.univ false :=
    (exGame_eqResponses _ _ _).2 ⟨exPrior, exPrior_belief, by
      simp [exPrior, exG, Fin.sum_univ_three]; norm_num⟩
  have hict0 : exGame.icTypes (fun _ => 0) false = Set.univ := by
    have : exGame.typesNotEqDominated (fun _ => 0) false = Set.univ := by
      ext θ
      simp only [typesNotEqDominated, EqDominated, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro hall
      have := hall _ hresp0
      simp [exGame] at this
    simp [icTypes, this]
  cases a
  · rw [hict0] at hv
    have := hv _ hresp0
    simp [exGame] at this
  · rw [hict] at hv
    fin_cases θ
    · have := hv (fun _ => 1) ((exGame_eqResponses _ _ _).2 ⟨pointMass 1,
        pointMass_belief 1 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this
    · have := hv (fun _ => 0) ((exGame_eqResponses _ _ _).2 ⟨pointMass 2,
        pointMass_belief 2 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this
    · have := hv (fun _ => 1) ((exGame_eqResponses _ _ _).2 ⟨pointMass 1,
        pointMass_belief 1 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this

/-- **Example 13.AA.1** (MWG, p. 472). No PBE in which every type chooses `false` has beliefs that
are reasonable relative to `Θ**`: after `â`, either `θ₂` or `θ₃` would deviate. -/
theorem example_13_AA_1_no_reasonable (sS : Bool → Unit → ℝ) (μ : Bool → Fin 3 → ℝ)
    (h : exGame.IsPBE exPrior (fun _ => false) sS μ)
    (hr : ReasonableBeliefs (exGame.typesNotEqDominated (exGame.eqPayoff (fun _ => false) sS))
      μ) : False := by
  rw [exGame_eqPayoff] at hr
  have hr' := hr true (by rw [example_13_AA_1_eqdom]; exact ⟨1, by simp⟩)
  rw [example_13_AA_1_eqdom] at hr'
  obtain ⟨⟨h0, h1, -⟩, hne⟩ := h.2.2 true
  have hμ0 : μ true 0 = 0 := by
    by_contra hne0
    have := hr' 0 (lt_of_le_of_ne (h0 0) (Ne.symm hne0))
    simp at this
  have hs := (exGame_nash_iff true _ h1 _).1 hne
  simp only [Fin.sum_univ_three, exG, hμ0] at hs h1
  norm_num at hs
  have hμ1 : μ true 1 ≤ 1 := by linarith [h0 2]
  have hdev1 := h.1 1 true
  have hdev2 := h.1 2 true
  have e1 : exGame.u1 true (sS true) 1 = if 1 / 4 ≤ μ true 1 then 1 else -1 := by
    simp [exGame, hs]
  have e2 : exGame.u1 true (sS true) 2 =
      if 0 ≤ μ true 1 ∧ μ true 1 ≤ 3 / 4 then 1 else -1 := by
    simp [exGame, hs]
  have z1 : exGame.u1 false (sS false) 1 = 0 := by simp [exGame]
  have z2 : exGame.u1 false (sS false) 2 = 0 := by simp [exGame]
  rw [e1, z1] at hdev1
  rw [e2, z2] at hdev2
  by_cases hq : 1 / 4 ≤ μ true 1
  · simp only [hq, ↓reduceIte] at hdev1; norm_num at hdev1
  · have : 0 ≤ μ true 1 ∧ μ true 1 ≤ 3 / 4 := ⟨h0 1, by linarith⟩
    simp only [this, and_self, ↓reduceIte] at hdev2; norm_num at hdev2

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two types: the intuitive criterion and reasonable beliefs, an instance

MWG, Appendix A, p. 472.

A concrete two-type signaling game satisfying the hypotheses of `two_types_reasonable`. Types
`false` (low) and `true` (high), equally likely; player 1 chooses `false` (the equilibrium
action) or `true` (the deviation); one responder chooses `s ∈ ℝ` with payoff `-(s - g(θ))²`,
`g(θ_L) = 0`, `g(θ_H) = 1`, so her unique best response to a belief `μ` is `s = μ(θ_H)`. Player 1
gets `0` from `false`; from `true` the low type gets `-1` and the high type `s - 1`.

* `twoTypes_instance`: pooling on `false` with the belief "low type" after `true` (response
  `0`) is a PBE; it passes the intuitive criterion; `Θ**(true) = {θ_H}`; its off-path belief is
  not reasonable; and `two_types_reasonable` turns it into a PBE with the reasonable belief and
  the same outcome.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- The responder's target `g(θ)`. -/
def twoG (θ : Bool) : ℝ := if θ then 1 else 0

/-- **Appendix A** (MWG, p. 472). A two-type signaling game. -/
noncomputable def twoGame : SignalingGame Bool Bool Unit (fun _ => ℝ) where
  u1 a s θ := if a then (if θ then s () - 1 else -1) else 0
  u _ _ s θ := -(s () - twoG θ) ^ 2

/-- The responder's expected payoff is `-(s - μ(θ_H))²` plus a constant. -/
theorem twoGame_payoff (a : Bool) (μ : Bool → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    (twoGame.responseGame a μ).payoff () s = -(s () - μ true) ^ 2 + (μ true ^ 2 - μ true) := by
  simp only [SignalingGame.responseGame, twoGame, Fintype.sum_bool, twoG] at hμ ⊢
  simp only [Bool.false_eq_true, ↓reduceIte]
  have : μ false = 1 - μ true := by linarith
  rw [this]; ring

/-- The responder's unique equilibrium response to `μ` is `μ(θ_H)`. -/
theorem twoGame_nash_iff (a : Bool) (μ : Bool → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    IsNashEquilibrium (twoGame.responseGame a μ) s ↔ s () = μ true := by
  constructor
  · intro h
    have := h () (μ true)
    rw [twoGame_payoff a μ hμ, twoGame_payoff a μ hμ, Function.update_self, sub_self] at this
    nlinarith [sq_nonneg (s () - μ true)]
  · intro h i t
    rw [twoGame_payoff a μ hμ, twoGame_payoff a μ hμ, h]
    nlinarith [sq_nonneg (Function.update s i t () - μ true)]

/-- The point mass on `b`. -/
def boolPoint (b : Bool) : Bool → ℝ := fun θ => if θ = b then 1 else 0

theorem boolPoint_belief (b : Bool) (T : Set Bool) (hb : b ∈ T) : IsBeliefOn T (boolPoint b) := by
  refine ⟨fun θ => by unfold boolPoint; split_ifs <;> norm_num, ?_, fun θ h => ?_⟩
  · cases b <;> simp [boolPoint]
  · unfold boolPoint at h; split_ifs at h with he
    · rw [he]; exact hb
    · norm_num at h

/-- The response `s = 1` to the belief "high type" is an equilibrium response, for beliefs
concentrated on any `T ∋ θ_H`. -/
theorem twoGame_one_mem (T : Set Bool) (hT : true ∈ T) (a : Bool) :
    (fun _ => (1 : ℝ)) ∈ twoGame.eqResponses T a :=
  ⟨boolPoint true, boolPoint_belief true T hT,
    (twoGame_nash_iff a _ (boolPoint_belief true T hT).2.1 _).2 (by simp [boolPoint])⟩

/-- The responses of the PBE: `0` after `true` (belief: low type), `1/2` after `false`. -/
noncomputable def twoResp (a : Bool) : Unit → ℝ := if a then fun _ => 0 else fun _ => 1 / 2

/-- The beliefs of the PBE. -/
noncomputable def twoBelief (a : Bool) : Bool → ℝ := if a then boolPoint false else fun _ => 1 / 2

/-- **Appendix A** (MWG, p. 472). Two types: an instance of the hypotheses of
`two_types_reasonable`, and its conclusion. -/
theorem twoTypes_instance :
    twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false) twoResp twoBelief ∧
      ¬ twoGame.ViolatesIC (twoGame.eqPayoff (fun _ => false) twoResp) ∧
      twoGame.typesNotEqDominated (twoGame.eqPayoff (fun _ => false) twoResp) true = {true} ∧
      ¬ ReasonableBeliefs (twoGame.typesNotEqDominated
        (twoGame.eqPayoff (fun _ => false) twoResp)) twoBelief ∧
      ∃ s ν, IsBeliefOn {true} ν ∧ twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false)
        (Function.update twoResp true s) (Function.update twoBelief true ν) := by
  have hpay : twoGame.eqPayoff (fun _ => false) twoResp = fun _ => 0 := by
    funext θ; simp [SignalingGame.eqPayoff, twoGame]
  have hhalf : IsBeliefOn Set.univ (fun _ : Bool => (1 : ℝ) / 2) :=
    ⟨fun _ => by norm_num, by norm_num, fun _ _ => trivial⟩
  have hpbe : twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false) twoResp twoBelief := by
    refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ?_⟩
    · cases a <;> cases θ <;> simp [twoGame, twoResp]
    · obtain ⟨θ', hθ'⟩ := ha
      subst hθ'
      simp [twoBelief]
    · cases a
      · refine ⟨hhalf, (twoGame_nash_iff false _ hhalf.2.1 _).2 ?_⟩
        simp [twoResp]
      · have hb := boolPoint_belief false Set.univ trivial
        refine ⟨hb, (twoGame_nash_iff true _ hb.2.1 _).2 ?_⟩
        simp [twoResp, boolPoint]
  have hnd : ∀ a, true ∈ twoGame.typesNotEqDominated (fun _ => 0) a := by
    intro a hdom
    have := hdom _ (twoGame_one_mem Set.univ trivial a)
    cases a <;> simp [twoGame] at this
  have heq : twoGame.typesNotEqDominated (twoGame.eqPayoff (fun _ => false) twoResp) true =
      {true} := by
    rw [hpay]
    ext θ
    cases θ
    · simp only [Set.mem_singleton_iff, Bool.false_eq_true, iff_false]
      intro hnot
      apply hnot
      intro s _
      simp [twoGame]
    · simp only [Set.mem_singleton_iff, iff_true]
      exact hnd true
  have hIC : ¬ twoGame.ViolatesIC (twoGame.eqPayoff (fun _ => false) twoResp) := by
    rw [hpay]
    rintro ⟨θ, a, hv⟩
    have hmem : true ∈ twoGame.icTypes (fun _ => 0) a := by
      unfold icTypes
      split_ifs
      · exact hnd a
      · trivial
    have := hv _ (twoGame_one_mem _ hmem a)
    cases a <;> cases θ <;> norm_num [twoGame] at this
  have hoff : ∀ θ : Bool, (fun _ : Bool => false) θ ≠ true := fun _ => Bool.false_ne_true
  refine ⟨hpbe, hIC, heq, fun hr => ?_, two_types_reasonable hpbe hIC hoff heq⟩
  have := hr true (by rw [heq]; exact ⟨true, rfl⟩) false (by simp [twoBelief, boolPoint])
  rw [heq] at this
  exact Bool.false_ne_true this

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Refinements in the education signaling model

MWG, Appendix A, pp. 468-471 (and p. 458).

In the education game the firms' equilibrium responses to education `e` under a belief `m` that
the worker is of high ability are the Bertrand wages `mθ_H + (1 - m)θ_L` (`bertrand_wage`), so
`S*(Θ, e) = [θ_L, θ_H]` (`education_Sstar`). We specialize the definitions of Appendix A
(`MWGAdverseSelection.Refinements`) to this game, with beliefs described by `m ∈ [0, 1]`:

* `EqDomEd`: (13.AA.3); `notEqDomEd`: `Θ**(e)`; `ViolatesICEd`: (13.AA.4).
* `education_Theta_all` (p. 469): (13.AA.1) eliminates nothing.
* `education_IC_unique` (p. 471): with `r = 0` (and `c(·, θ_L)` unbounded, so that the
  relevant indifference curves cross), every PBE that passes the intuitive criterion is the best
  separating equilibrium `(0, ẽ)`; `education_IC_exists`: the best separating equilibrium (with
  the beliefs of Figure 13.C.7) passes it. The intuitive criterion thus selects the Riley
  outcome.
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

variable {M : SigModel}

/-- **Appendix A** (MWG, p. 469). `S*(Θ, e) = [θ_L, θ_H]`: the Bertrand wage for some belief. -/
theorem education_Sstar (hM : M.Valid) : M.expProd '' Icc 0 1 = Icc M.θL M.θH := by
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩; exact hM.expProd_mem hm.1 hm.2
  · rintro ⟨h1, h2⟩
    have hgap : 0 < M.θH - M.θL := by linarith [hM.lt]
    refine ⟨(w - M.θL) / (M.θH - M.θL), ⟨div_nonneg (by linarith) hgap.le,
      (div_le_one hgap).2 (by linarith)⟩, ?_⟩
    unfold expProd; field_simp; ring

/-- **Appendix A** (MWG, p. 469). (13.AA.1) eliminates nothing in the education game: for any
type and any two education levels, a sufficiently higher wage after `e` makes `e` at least as
good as `e'`. -/
theorem education_Theta_all (M : SigModel) (b : Bool) (e e' w' : ℝ) :
    ∃ w, w' - M.c e' (M.θ b) ≤ w - M.c e (M.θ b) :=
  ⟨w' - M.c e' (M.θ b) + M.c e (M.θ b), by ring_nf; rfl⟩

/-- **(13.AA.3)** (MWG, p. 471) in the education game: `e` is equilibrium dominated for type `b`
with equilibrium payoffs `uS` if every equilibrium response gives `b` less. -/
def EqDomEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) (b : Bool) : Prop :=
  ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r - M.c e (M.θ b) < uS b

/-- `Θ**(e)` in the education game. -/
def notEqDomEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) : Set Bool := {b | ¬ M.EqDomEd uS e b}

/-- A belief `m` (probability of `θ_H`) concentrated on `T`. -/
def AdmissibleOn (T : Set Bool) (m : ℝ) : Prop :=
  m ∈ Icc (0 : ℝ) 1 ∧ (0 < m → true ∈ T) ∧ (m < 1 → false ∈ T)

open Classical in
/-- `Θ**(e)`, or all types if it is empty. -/
noncomputable def icSetEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) : Set Bool :=
  if (M.notEqDomEd uS e).Nonempty then M.notEqDomEd uS e else univ

/-- **(13.AA.4)** (MWG, p. 471) in the education game. -/
def ViolatesICEd (M : SigModel) (uS : Bool → ℝ) : Prop :=
  ∃ b e, 0 ≤ e ∧ ∀ m, AdmissibleOn (M.icSetEd uS e) m →
    uS b < max (M.expProd m) M.r - M.c e (M.θ b)

/-- Equilibrium payoffs of a reduced-form PBE. -/
def eqPay (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Bool → ℝ := fun b => M.redPay μ b (eS b)

/-- If `Θ**(e) = {θ_H}` and the high type gains from being recognized, the IC is violated. -/
theorem violates_of_high (hM : M.Valid) {uS : Bool → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hL : M.EqDomEd uS e false) (hH : uS true < M.θH - M.c e M.θH) : M.ViolatesICEd uS := by
  have hHnd : true ∈ M.notEqDomEd uS e := fun h =>
    absurd (h 1 ⟨zero_le_one, le_rfl⟩) (by
      rw [expProd_one, max_eq_left hM.r_lt.le, θ_true]; exact not_lt.2 hH.le)
  have hset : M.icSetEd uS e = {true} := by
    have hns : M.notEqDomEd uS e = {true} := by
      ext b; cases b
      · simp only [mem_singleton_iff, Bool.false_eq_true, iff_false]
        exact fun h => h hL
      · simp only [mem_singleton_iff, iff_true]; exact hHnd
    simp [icSetEd, hns]
  refine ⟨true, e, he, fun m hm => ?_⟩
  rw [hset] at hm
  have hm1 : m = 1 := by
    by_contra hne
    have := hm.2.2 (lt_of_le_of_ne hm.1.2 hne)
    simp at this
  rw [hm1, expProd_one, max_eq_left hM.r_lt.le, θ_true]; exact hH

/-- **Appendix A** (MWG, p. 471). With `r = 0`, every PBE that passes the intuitive criterion is
the best separating equilibrium: the low type chooses `0`, the high type `ẽ`. (We assume
`c(·, θ_L)` unbounded, so that the low type's indifference curves reach `θ_H`.) -/
theorem education_IC_unique (hM : M.Valid) (hr : M.r = 0)
    (hunb : ∀ K, ∃ e, 0 ≤ e ∧ K ≤ M.c e M.θL) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.c et M.θL = M.θH - M.θL) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hIC : ¬ M.ViolatesICEd (M.eqPay eS μ)) :
    Separating eS ∧ eS false = 0 ∧ eS true = et := by
  have hθL0 : max M.θL M.r = M.θL := by rw [hr]; exact max_eq_left hM.θL_pos.le
  have hEr : max M.Eθ M.r = M.Eθ := by rw [hr]; exact max_eq_left (hM.θL_pos.trans
    hM.Eθ_mem.1).le
  have hmax : ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r ≤ M.θH := fun m hm =>
    max_le (hM.expProd_mem hm.1 hm.2).2 hM.r_lt.le
  by_cases hsep : Separating eS
  · have h0 := lemma_13_C_2 hM h hsep
    have hpay := separating_payoffs hM h hsep
    refine ⟨hsep, h0, ?_⟩
    obtain ⟨-, hcond⟩ : True ∧ M.θH - M.c (eS true) M.θL ≤ M.θL := by
      have hsepf : Separating fun b : Bool => if b then eS true else 0 := by
        simpa [Separating, ← h0] using hsep
      have hfun : (fun b : Bool => if b then eS true else 0) = eS := by
        funext b; cases b <;> simp [h0]
      have := ((separating_iff hM (h.1 true)).1 ⟨μ, hfun ▸ h, hsepf⟩).1
      rw [hθL0] at this
      exact ⟨trivial, this⟩
    have hge : et ≤ eS true := by
      have hL := (hM.c_mono false).le_iff_le het (h.1 true)
      simp only [θ_false] at hL
      exact hL.1 (by linarith)
    by_contra hne
    have hgt : et < eS true := lt_of_le_of_ne hge (Ne.symm hne)
    set x := (et + eS true) / 2
    have hx1 : et < x := by simp only [x]; linarith
    have hx2 : x < eS true := by simp only [x]; linarith
    refine hIC (violates_of_high hM (het.trans hx1.le) (fun m hm => ?_) ?_)
    · simp only [eqPay, hpay.1, hθL0, θ_false]
      have := low_never_above hM het (by rw [hθL0]; linarith) hx1
      rw [hθL0] at this
      linarith [hmax m hm]
    · simp only [eqPay, hpay.2]
      have := hM.c_mono true (het.trans hx1.le) (h.1 true) hx2
      simp only [θ_true] at this
      linarith
  · exfalso
    have hpool : Pooling eS := not_not.1 hsep
    obtain ⟨ep, hepd⟩ : ∃ ep, eS true = ep := ⟨_, rfl⟩
    have hμp : μ ep = M.lam := hepd ▸ h.2.2.2.2 hpool
    have hpayp : ∀ b, M.eqPay eS μ b = M.Eθ - M.c ep (M.θ b) := by
      intro b
      have hb : eS b = ep := by
        cases b with
        | false => rw [hpool, hepd]
        | true => exact hepd
      simp only [eqPay, redPay, hb, hμp, expProd_lam, hEr]
    set D := M.θH - M.Eθ
    have hD : 0 < D := by simp only [D]; linarith [hM.Eθ_mem.2]
    have hep : 0 ≤ ep := hepd ▸ h.1 true
    obtain ⟨E, hE0, hE⟩ := hunb (M.c ep M.θL + D)
    have hEep : ep < E := by
      by_contra hle
      have := (hM.c_mono false).monotoneOn hE0 hep (not_lt.1 hle)
      simp only [θ_false] at this
      linarith
    have hcontL : ContinuousOn (fun x => M.c x M.θL) (Icc ep E) :=
      (hM.c_cont false).mono fun x hx => hep.trans hx.1
    obtain ⟨eL, heL, heLv⟩ := intermediate_value_Icc hEep.le hcontL
      ⟨by linarith, hE⟩
    have heL0 : ep < eL := by
      rcases eq_or_lt_of_le heL.1 with he | he
      · rw [← he] at heLv; linarith
      · exact he
    have hsc := hM.sc ep eL hep heL0
    have hcH : ContinuousWithinAt (fun x => M.c x (M.θ true)) (Ioi eL) eL :=
      ((hM.c_cont true) eL (hep.trans heL0.le)).mono fun x hx =>
        (hep.trans heL0.le).trans (le_of_lt hx)
    have hev : ∀ᶠ x in nhdsWithin eL (Ioi eL), M.c x M.θH < M.c ep M.θH + D :=
      hcH.eventually (gt_mem_nhds (by simp only [θ_true]; linarith))
    obtain ⟨x, hx, hxe⟩ := (hev.and self_mem_nhdsWithin).exists
    have hx0 : 0 ≤ x := (hep.trans heL0.le).trans (le_of_lt hxe)
    have hLx : M.c ep M.θL + D < M.c x M.θL := by
      have := hM.c_mono false (hep.trans heL0.le) hx0 hxe
      simp only [θ_false] at this; linarith
    refine hIC (violates_of_high hM hx0 (fun m hm => ?_) ?_)
    · rw [hpayp]; simp only [θ_false, D] at hLx ⊢; linarith [hmax m hm]
    · rw [hpayp]; simp only [θ_true, D] at hx ⊢; linarith

/-- **Appendix A** (MWG, p. 471). With `r = 0`, the best separating equilibrium `(0, ẽ)` with the
beliefs of Figure 13.C.6 (`μ(e) = 1` iff `e ≥ ẽ`) is a PBE that passes the intuitive
criterion. -/
theorem education_IC_exists (hM : M.Valid) (hr : M.r = 0) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.c et M.θL = M.θH - M.θL) :
    M.IsPBERed (fun b => if b then et else 0) (sepBelief et) ∧
      ¬ M.ViolatesICEd (M.eqPay (fun b => if b then et else 0) (sepBelief et)) := by
  have hθL0 : max M.θL M.r = M.θL := by rw [hr]; exact max_eq_left hM.θL_pos.le
  have hcH : M.c et M.θH ≤ M.θH - M.θL := hcet ▸ hM.c_le het
  have hcond : M.θH - M.c et M.θL ≤ max M.θL M.r ∧ max M.θL M.r ≤ M.θH - M.c et M.θH := by
    rw [hθL0]; constructor <;> linarith
  have hpbe := separating_sepBelief hM het hcond.1 hcond.2
  have hsep := separating_sep hM het hcond.1
  refine ⟨hpbe, ?_⟩
  have hpay := separating_payoffs hM hpbe hsep
  simp only [ite_true, Bool.false_eq_true, ite_false] at hpay
  have huL : M.eqPay (fun b => if b then et else 0) (sepBelief et) false = M.θL := by
    simp only [eqPay, Bool.false_eq_true, ite_false]; rw [hpay.1, hθL0]
  have huH : M.eqPay (fun b => if b then et else 0) (sepBelief et) true =
      M.θH - M.c et M.θH := by
    simp only [eqPay, ite_true]; exact hpay.2
  set uS := M.eqPay (fun b => if b then et else 0) (sepBelief et)
  have hmax : ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r ≤ M.θH := fun m hm =>
    max_le (hM.expProd_mem hm.1 hm.2).2 hM.r_lt.le
  rintro ⟨b, e, he, hv⟩
  -- an admissible belief always exists
  have hadm : ∀ T : Set Bool, T.Nonempty → ∃ m, AdmissibleOn T m := by
    rintro T ⟨b', hb'⟩
    cases b'
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => absurd h (lt_irrefl _), fun _ => hb'⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, fun _ => hb', fun h => absurd h (lt_irrefl _)⟩
  have hne : (M.icSetEd uS e).Nonempty := by
    unfold icSetEd; split_ifs with h
    exacts [h, ⟨true, trivial⟩]
  rcases le_or_gt et e with hle | hlt
  · obtain ⟨m, hm⟩ := hadm _ hne
    have := hv m hm
    have hcm := (hM.c_mono b).monotoneOn het he hle
    cases b
    · simp only [θ_false, huL] at this hcm; linarith [hmax m hm.1]
    · simp only [θ_true, huH] at this hcm; linarith [hmax m hm.1]
  · -- the low type is not equilibrium dominated below `ẽ`
    have hLnd : false ∈ M.notEqDomEd uS e := by
      intro hd
      have := hd 1 ⟨zero_le_one, le_rfl⟩
      rw [expProd_one, max_eq_left hM.r_lt.le, huL, θ_false] at this
      have hc := hM.c_mono false he het hlt
      simp only [θ_false] at hc
      linarith
    have hset : false ∈ M.icSetEd uS e := by
      simp only [icSetEd, show (M.notEqDomEd uS e).Nonempty from ⟨false, hLnd⟩, ↓reduceIte]
      exact hLnd
    have := hv 0 ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd h (lt_irrefl _), fun _ => hset⟩
    rw [expProd_zero, hθL0] at this
    have hc := hM.c_nonneg b he
    cases b
    · simp only [θ_false, huL] at this hc; linarith
    · simp only [θ_true, huH] at this hc; linarith

/-- **Appendix A** (MWG, p. 471), an instance: in the model `crossModel` of Exercise 13.C.3
(`ẽ = 1`), the PBEs passing the intuitive criterion are exactly those with outcome `(0, 1)`. -/
theorem education_IC_instance :
    (crossModel.IsPBERed (fun b => if b then 1 else 0) (sepBelief 1) ∧
      ¬ crossModel.ViolatesICEd (crossModel.eqPay (fun b => if b then 1 else 0) (sepBelief 1))) ∧
    ∀ eS μ, crossModel.IsPBERed eS μ → ¬ crossModel.ViolatesICEd (crossModel.eqPay eS μ) →
      eS false = 0 ∧ eS true = 1 := by
  have hr : crossModel.r = 0 := rfl
  have hc : crossModel.c 1 crossModel.θL = crossModel.θH - crossModel.θL := by
    rw [crossModel_cL]; norm_num [crossModel]
  refine ⟨education_IC_exists crossModel_valid hr zero_le_one hc, fun eS μ h hIC => ?_⟩
  have := education_IC_unique crossModel_valid hr (fun K => ⟨max K 0, le_max_right _ _, by
    rw [crossModel_cL]; exact le_max_left _ _⟩) zero_le_one hc h hIC
  exact ⟨this.2.1, this.2.2⟩

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The screening model

MWG, Section 13.D, pp. 460-465.

Same types, prior and cost function as in Section 13.C (a `SigModel` with `r = 0`); the task
level `t ≥ 0` plays the role of education. A contract is a pair `(w, t)`. In stage 1 two firms
announce finite sets of contracts (`ValidMenu`); in stage 2 each worker type chooses a contract
from the union of the menus (`Chooses`): one maximizing `w - c(t, θ)`, the lower task level among
equally good ones, accepting when indifferent between it and staying home (utility `0`); a firm
gets the worker if it offers her chosen contract, half the time if both do (`share`). Given this
stage-2 behaviour, the pure SPNE are the pairs of menus that are best replies to each other
(`IsScreenEq`, the Nash condition of Definition 8.D.1 written out).

* `chooses_unique`, `exists_chooses`: the worker's choice is well defined.
* `proposition_13_D_1` (observable types): type `θ` accepts `(θ, 0)` and firms earn zero.
* `lemma_13_D_1`-`lemma_13_D_5`, `proposition_13_D_2` (unobservable types, in module `ScreeningEq`):
  zero profits, no pooling equilibrium, `(θ_L, 0)` and `(θ_H, t̂_H)` with
  `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
-/

namespace MWG.AdverseSelection

namespace SigModel

/-- A worker's utility from contract `k = (w, t)`. -/
def util (M : SigModel) (θ : ℝ) (k : ℝ × ℝ) : ℝ := k.1 - M.c k.2 θ

/-- **Section 13.D** (MWG, p. 461). A menu: a finite set of contracts with task levels `t ≥ 0`. -/
def ValidMenu (A : Finset (ℝ × ℝ)) : Prop := ∀ k ∈ A, 0 ≤ k.2

/-- **Section 13.D** (MWG, p. 461). Type `θ` chooses contract `k` from the offered set `U`: `k`
maximizes utility, has the lowest task level among the best contracts, and is accepted
(utility at least `0`, the value of not working). -/
def Chooses (M : SigModel) (θ : ℝ) (U : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : Prop :=
  k ∈ U ∧ 0 ≤ M.util θ k ∧ (∀ k' ∈ U, M.util θ k' ≤ M.util θ k) ∧
    ∀ k' ∈ U, M.util θ k' = M.util θ k → k.2 ≤ k'.2

/-- **Section 13.D** (MWG, p. 461). The share of a worker choosing `k` that goes to the firm
offering `own` when the other offers `other`. -/
noncomputable def share (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : ℝ :=
  if k ∈ own then (if k ∈ other then 1 / 2 else 1) else 0

open Classical in
/-- The firm's expected profit from a worker of type `θ`. -/
noncomputable def typeProfit (M : SigModel) (θ : ℝ) (own other : Finset (ℝ × ℝ)) : ℝ :=
  if h : ∃ k, M.Chooses θ (own ∪ other) k then share own other h.choose * (θ - h.choose.1)
  else 0

/-- **Section 13.D** (MWG, p. 461). A firm's expected profit. -/
noncomputable def screenProfit (M : SigModel) (own other : Finset (ℝ × ℝ)) : ℝ :=
  (1 - M.lam) * M.typeProfit M.θL own other + M.lam * M.typeProfit M.θH own other

/-- **Section 13.D** (MWG, p. 461). A pure strategy SPNE of the screening game. -/
def IsScreenEq (M : SigModel) (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  ValidMenu A₁ ∧ ValidMenu A₂ ∧ (∀ B, ValidMenu B → M.screenProfit B A₂ ≤ M.screenProfit A₁ A₂) ∧
    ∀ B, ValidMenu B → M.screenProfit B A₁ ≤ M.screenProfit A₂ A₁

variable {M : SigModel}

/-- The worker's choice is unique. -/
theorem chooses_unique {θ : ℝ} {U : Finset (ℝ × ℝ)} {k k' : ℝ × ℝ} (h : M.Chooses θ U k)
    (h' : M.Chooses θ U k') : k = k' := by
  have hu : M.util θ k = M.util θ k' := le_antisymm (h'.2.2.1 k h.1) (h.2.2.1 k' h'.1)
  have ht : k.2 = k'.2 := le_antisymm (h.2.2.2 k' h'.1 hu.symm) (h'.2.2.2 k h.1 hu)
  have hw : k.1 = k'.1 := by unfold util at hu; rw [ht] at hu; linarith
  exact Prod.ext hw ht

/-- If some offered contract gives utility at least `0`, the worker chooses a contract. -/
theorem exists_chooses (θ : ℝ) {U : Finset (ℝ × ℝ)} (h : ∃ k ∈ U, 0 ≤ M.util θ k) :
    ∃ k, M.Chooses θ U k := by
  obtain ⟨k0, hk0, hu0⟩ := h
  obtain ⟨k1, hk1, hmax⟩ := U.exists_max_image (M.util θ) ⟨k0, hk0⟩
  set V := U.filter (fun k => M.util θ k = M.util θ k1)
  obtain ⟨k, hk, hmin⟩ := V.exists_min_image (fun k => k.2) ⟨k1, by simp [V, hk1]⟩
  simp only [V, Finset.mem_filter] at hk
  refine ⟨k, hk.1, by rw [hk.2]; exact hu0.trans (hmax k0 hk0), fun k' hk' => ?_,
    fun k' hk' he => hmin k' (by simp [V, hk', he.trans hk.2])⟩
  rw [hk.2]; exact hmax k' hk'

/-- The firm's profit from type `θ` when `θ` chooses `k`. -/
theorem typeProfit_of_chooses {θ : ℝ} {own other : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : M.Chooses θ (own ∪ other) k) :
    M.typeProfit θ own other = share own other k * (θ - k.1) := by
  have hex : ∃ k, M.Chooses θ (own ∪ other) k := ⟨k, h⟩
  rw [typeProfit, dite_eq_left_of_eq_true (eq_true hex), chooses_unique hex.choose_spec h]

/-- The profit from type `θ` is `0` if she does not work. -/
theorem typeProfit_of_not {θ : ℝ} {own other : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, M.Chooses θ (own ∪ other) k) : M.typeProfit θ own other = 0 := by
  rw [typeProfit, dite_eq_right_of_eq_false (eq_false h)]

/-- The firms' shares of a chosen contract add up to `1`. -/
theorem share_add {own other : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ own ∪ other) :
    share own other k + share other own k = 1 := by
  rcases Finset.mem_union.1 hk with h | h <;> unfold share <;> split_ifs <;> norm_num

theorem share_nonneg (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : 0 ≤ share own other k := by
  unfold share; split_ifs <;> norm_num

theorem share_le_one (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : share own other k ≤ 1 := by
  unfold share; split_ifs <;> norm_num

/-- A firm offering nothing earns nothing. -/
theorem screenProfit_empty (other : Finset (ℝ × ℝ)) : M.screenProfit ∅ other = 0 := by
  have : ∀ θ, M.typeProfit θ ∅ other = 0 := by
    intro θ
    by_cases h : ∃ k, M.Chooses θ (∅ ∪ other) k
    · obtain ⟨k, hk⟩ := h
      rw [typeProfit_of_chooses hk]; simp [share]
    · exact typeProfit_of_not h
  simp [screenProfit, this]

/-- A contract that type `θ` strictly prefers to everything else on offer, with utility
`≥ 0`, is her choice. -/
theorem chooses_of_strict {θ : ℝ} {U : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ U)
    (h0 : 0 ≤ M.util θ k) (hs : ∀ k' ∈ U, k' ≠ k → M.util θ k' < M.util θ k) :
    M.Chooses θ U k := by
  refine ⟨hk, h0, fun k' hk' => ?_, fun k' hk' he => ?_⟩
  · by_cases h : k' = k
    · rw [h]
    · exact (hs k' hk' h).le
  · by_cases h : k' = k
    · rw [h]
    · exact absurd he (hs k' hk' h).ne

/-- A firm offering nothing earns nothing from any type. -/
theorem typeProfit_empty (θ : ℝ) (other : Finset (ℝ × ℝ)) : M.typeProfit θ ∅ other = 0 := by
  by_cases h : ∃ k, M.Chooses θ (∅ ∪ other) k
  · obtain ⟨k, hk⟩ := h
    rw [typeProfit_of_chooses hk]; simp [share]
  · exact typeProfit_of_not h

/-- A deviation `B` containing a contract `k` that type `θ` strictly prefers to everything else
on offer captures type `θ`: the deviator's profit from her is `θ - w`. -/
theorem typeProfit_capture {θ : ℝ} {other B : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ B)
    (h0 : 0 ≤ M.util θ k) (hs : ∀ k' ∈ other, M.util θ k' < M.util θ k)
    (hB : ∀ k' ∈ B, k' ≠ k → M.util θ k' < M.util θ k) :
    M.typeProfit θ B other = θ - k.1 := by
  have hch : M.Chooses θ (B ∪ other) k := by
    refine chooses_of_strict (Finset.mem_union_left _ hk) h0 fun k' hk' hne => ?_
    rcases Finset.mem_union.1 hk' with h | h
    · exact hB k' h hne
    · exact hs k' h
  have hno : k ∉ other := fun h => lt_irrefl _ (hs k h)
  rw [typeProfit_of_chooses hch]
  simp [share, hk, hno]

/-- The two firms' profits from type `θ` add up to `θ - w` of her chosen contract. -/
theorem typeProfit_add {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : M.Chooses θ (A₁ ∪ A₂) k) :
    M.typeProfit θ A₁ A₂ + M.typeProfit θ A₂ A₁ = θ - k.1 := by
  have h' : M.Chooses θ (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_chooses h, typeProfit_of_chooses h', ← add_mul, share_add h.1, one_mul]

/-- **Section 13.D** (MWG, p. 461). With observable types, the competition for type `θ` workers
alone: a pure SPNE of the game in which firms offer menus to type `θ`. -/
def IsTypeEq (M : SigModel) (θ : ℝ) (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  ValidMenu A₁ ∧ ValidMenu A₂ ∧ (∀ B, ValidMenu B → M.typeProfit θ B A₂ ≤ M.typeProfit θ A₁ A₂) ∧
    ∀ B, ValidMenu B → M.typeProfit θ B A₁ ≤ M.typeProfit θ A₂ A₁

theorem IsTypeEq.symm {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsTypeEq θ A₁ A₂) :
    M.IsTypeEq θ A₂ A₁ := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- **Proposition 13.D.1** (MWG, p. 461). With observable types, in any SPNE a type-`θ` worker
accepts the contract `(θ, 0)` and both firms earn zero profits. -/
theorem proposition_13_D_1 (hM : M.Valid) (b : Bool) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsTypeEq (M.θ b) A₁ A₂) :
    M.Chooses (M.θ b) (A₁ ∪ A₂) (M.θ b, 0) ∧ M.typeProfit (M.θ b) A₁ A₂ = 0 ∧
      M.typeProfit (M.θ b) A₂ A₁ = 0 := by
  set θ := M.θ b
  have hθ : 0 < θ := by
    cases b
    · exact hM.θL_pos
    · exact hM.θL_pos.trans hM.lt
  have hval1 : ValidMenu A₁ := h.1
  have hval2 : ValidMenu A₂ := h.2.1
  have hnn1 : 0 ≤ M.typeProfit θ A₁ A₂ := by
    have := h.2.2.1 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    rwa [typeProfit_empty] at this
  have hnn2 : 0 ≤ M.typeProfit θ A₂ A₁ := by
    have := h.2.2.2 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    rwa [typeProfit_empty] at this
  have hvs : ∀ w t, 0 ≤ t → ValidMenu {(w, t)} := fun w t ht k hk => by
    rw [Finset.mem_singleton] at hk; rw [hk]; exact ht
  have hsing : ∀ k k' : ℝ × ℝ, k' ∈ ({k} : Finset (ℝ × ℝ)) → k' ≠ k →
      M.util θ k' < M.util θ k := fun k k' hk' hne =>
    absurd (Finset.mem_singleton.1 hk') hne
  -- some contract is chosen
  obtain ⟨k, hk⟩ : ∃ k, M.Chooses θ (A₁ ∪ A₂) k := by
    by_contra hno
    have hneg : ∀ k' ∈ A₂, M.util θ k' < M.util θ (θ / 2, 0) := by
      intro k' hk'
      by_contra hle
      exact hno (exists_chooses θ ⟨k', Finset.mem_union_right _ hk', by
        simp only [util, hM.c_zero] at hle ⊢; linarith⟩)
    have hcap := typeProfit_capture (M := M) (other := A₂) (Finset.mem_singleton_self _)
      (by simp only [util, hM.c_zero]; linarith) hneg (hsing _)
    have := h.2.2.1 {(θ / 2, 0)} (hvs _ _ le_rfl)
    rw [hcap, typeProfit_of_not hno] at this
    linarith
  have hsum := typeProfit_add hk
  -- undercutting: a firm with at most half the market gains by raising the wage slightly
  have hundercut : ∀ own other, M.IsTypeEq θ own other → M.Chooses θ (own ∪ other) k →
      share own other k ≤ 1 / 2 → θ - k.1 ≤ 0 := by
    intro own other he hkc hsh
    by_contra hpos
    rw [not_le] at hpos
    set ε := (θ - k.1) / 4
    have hε : 0 < ε := by simp only [ε]; linarith
    have hval : 0 ≤ k.2 := by
      rcases Finset.mem_union.1 hkc.1 with h' | h'
      · exact he.1 k h'
      · exact he.2.1 k h'
    have hbetter : ∀ k' ∈ other, M.util θ k' < M.util θ (k.1 + ε, k.2) := fun k' hk' => by
      have := hkc.2.2.1 k' (Finset.mem_union_right _ hk')
      simp only [util] at this ⊢; linarith
    have hcap := typeProfit_capture (M := M) (Finset.mem_singleton_self (k.1 + ε, k.2))
      (by have := hkc.2.1; simp only [util] at this ⊢; linarith) hbetter (hsing _)
    have := he.2.2.1 {(k.1 + ε, k.2)} (hvs _ _ hval)
    rw [hcap, typeProfit_of_chooses hkc] at this
    simp only at this
    have hhalf : share own other k * (θ - k.1) ≤ 1 / 2 * (θ - k.1) :=
      mul_le_mul_of_nonneg_right hsh hpos.le
    simp only [ε] at this
    linarith
  have hPi : θ - k.1 ≤ 0 := by
    have hsa := share_add (own := A₁) (other := A₂) hk.1
    by_cases h1 : share A₁ A₂ k ≤ 1 / 2
    · exact hundercut A₁ A₂ h hk h1
    · have h2 : share A₂ A₁ k ≤ 1 / 2 := by linarith
      exact hundercut A₂ A₁ h.symm (by rwa [Finset.union_comm]) h2
  have hw : k.1 = θ := by linarith
  have hP1 : M.typeProfit θ A₁ A₂ = 0 := by linarith
  have hP2 : M.typeProfit θ A₂ A₁ = 0 := by linarith
  refine ⟨?_, hP1, hP2⟩
  -- the task level is zero
  have ht : k.2 = 0 := by
    have hval : 0 ≤ k.2 := by
      rcases Finset.mem_union.1 hk.1 with h' | h'
      · exact hval1 k h'
      · exact hval2 k h'
    by_contra hne
    have htpos : 0 < k.2 := lt_of_le_of_ne hval (Ne.symm hne)
    have hc : 0 < M.c k.2 θ := hM.c_pos b htpos
    set δ := min (M.c k.2 θ) θ / 2
    have hδ : 0 < δ := by simp only [δ]; exact half_pos (lt_min hc hθ)
    have hδc : δ < M.c k.2 θ := by
      simp only [δ]; linarith [min_le_left (M.c k.2 θ) θ]
    have hδθ : δ < θ := by simp only [δ]; linarith [min_le_right (M.c k.2 θ) θ]
    have hbetter : ∀ k' ∈ A₂, M.util θ k' < M.util θ (θ - δ, 0) := fun k' hk' => by
      have := hk.2.2.1 k' (Finset.mem_union_right _ hk')
      simp only [util, hM.c_zero] at this ⊢; rw [hw] at this; linarith
    have hcap := typeProfit_capture (M := M) (Finset.mem_singleton_self (θ - δ, 0))
      (by simp only [util, hM.c_zero]; linarith) hbetter (hsing _)
    have := h.2.2.1 {(θ - δ, 0)} (hvs _ _ le_rfl)
    rw [hcap, hP1] at this
    simp only at this
    linarith
  have hkeq : k = (θ, 0) := Prod.ext hw ht
  rwa [hkeq] at hk

/-- **Proposition 13.D.1** (MWG, p. 461), existence: both firms offering only `(θ, 0)` is an
SPNE of the observable-types game. -/
theorem proposition_13_D_1_exists (hM : M.Valid) (b : Bool) :
    M.IsTypeEq (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} := by
  have hθ : 0 < M.θ b := by
    cases b
    · exact hM.θL_pos
    · exact hM.θL_pos.trans hM.lt
  have hv : ValidMenu {(M.θ b, 0)} := fun k hk => by rw [Finset.mem_singleton.1 hk]
  have hzero : M.typeProfit (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} = 0 := by
    have hch : M.Chooses (M.θ b) ({(M.θ b, 0)} ∪ {(M.θ b, 0)}) (M.θ b, 0) := by
      refine chooses_of_strict (by simp) (by simp only [util, hM.c_zero, sub_zero]; exact hθ.le) ?_
      intro k' hk' hne
      rw [Finset.union_self, Finset.mem_singleton] at hk'
      exact absurd hk' hne
    rw [typeProfit_of_chooses hch]; simp
  have hdev : ∀ B, ValidMenu B →
      M.typeProfit (M.θ b) B {(M.θ b, 0)} ≤ M.typeProfit (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} := by
    intro B hB
    rw [hzero]
    by_cases hex : ∃ k, M.Chooses (M.θ b) (B ∪ {(M.θ b, 0)}) k
    · obtain ⟨k, hk⟩ := hex
      rw [typeProfit_of_chooses hk]
      have hge := hk.2.2.1 (M.θ b, 0) (by simp)
      simp only [util, hM.c_zero, sub_zero] at hge
      have hk2 : 0 ≤ k.2 := by
        rcases Finset.mem_union.1 hk.1 with h' | h'
        · exact hB k h'
        · rw [Finset.mem_singleton.1 h']
      have hc := hM.c_nonneg b hk2
      exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
    · rw [typeProfit_of_not hex]
  exact ⟨hv, hv, hdev, hdev⟩

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equilibria of the screening game with unobservable types

MWG, Section 13.D, pp. 462-466.

Throughout, `(A₁, A₂)` is a pure SPNE; `kL`, `kH` are the contracts chosen by the low and high
types. Both types accept some contract in every SPNE (p. 462, `IsScreenEq.exists_bothEmployed`),
so `BothEmployed` only names the chosen contracts.

* `lemma_13_D_1`: both firms earn zero profits.
* `lemma_13_D_2`: no pooling equilibrium exists.
* `lemma_13_D_3`: in a separating equilibrium `w_L = θ_L` and `w_H = θ_H`.
* `lemma_13_D_4`: the low type accepts `(θ_L, 0)`.
* `lemma_13_D_5`: the high type accepts `(θ_H, t̂_H)`, `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
* `proposition_13_D_2`: the two together.
* `no_eq_of_pooling_deviation`, `no_eq_of_pair_deviation` (pp. 465-466, Figures 13.D.7(b) and
  13.D.8): an SPNE cannot exist if a single pooling contract, or a pair of contracts, attracts the
  workers away from the Proposition 13.D.2 contracts at a profit; instances
  `nonexistence_pooling_instance` and `nonexistence_pair_instance`.
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- Both types accept a contract in the SPNE. -/
def BothEmployed (M : SigModel) (A₁ A₂ : Finset (ℝ × ℝ)) (kL kH : ℝ × ℝ) : Prop :=
  M.Chooses M.θL (A₁ ∪ A₂) kL ∧ M.Chooses M.θH (A₁ ∪ A₂) kH

theorem IsScreenEq.symm {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    M.IsScreenEq A₂ A₁ := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem BothEmployed.symm {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.BothEmployed A₁ A₂ kL kH) : M.BothEmployed A₂ A₁ kL kH := by
  unfold BothEmployed; rwa [Finset.union_comm]

/-- Equilibrium profits are nonnegative (a firm can offer nothing). -/
theorem IsScreenEq.nonneg {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    0 ≤ M.screenProfit A₁ A₂ := by
  have := h.2.2.1 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
  rwa [screenProfit_empty] at this

/-- The firms' profits add up to the total `(1 - λ)(θ_L - w_L) + λ(θ_H - w_H)`. -/
theorem screenProfit_add {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.BothEmployed A₁ A₂ kL kH) :
    M.screenProfit A₁ A₂ + M.screenProfit A₂ A₁ =
      (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1) := by
  have h1 := typeProfit_add h.1
  have h2 := typeProfit_add h.2
  unfold screenProfit
  rw [← h1, ← h2]; ring

/-- Chosen contracts in a valid pair of menus have `t ≥ 0`. -/
theorem chosen_valid {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} (h1 : ValidMenu A₁) (h2 : ValidMenu A₂)
    {k : ℝ × ℝ} (hk : M.Chooses θ (A₁ ∪ A₂) k) : 0 ≤ k.2 := by
  rcases Finset.mem_union.1 hk.1 with h | h
  · exact h1 k h
  · exact h2 k h

/-- A deviation `{k̃}` that type `θ_H` strictly prefers to every contract of the other firm while
type `θ_L` strictly prefers one of them to `k̃` earns `λ(θ_H - w̃)`. -/
theorem screenProfit_capture_high {other : Finset (ℝ × ℝ)} {k k0 : ℝ × ℝ} (hk0 : k0 ∈ other)
    (hL : M.util M.θL k < M.util M.θL k0) (h0 : 0 ≤ M.util M.θH k)
    (hH : ∀ k' ∈ other, M.util M.θH k' < M.util M.θH k) :
    M.screenProfit {k} other = M.lam * (M.θH - k.1) := by
  have hcapH := typeProfit_capture (M := M) (Finset.mem_singleton_self k) h0 hH
    (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
  have hL0 : M.typeProfit M.θL {k} other = 0 := by
    by_cases hex : ∃ k', M.Chooses M.θL ({k} ∪ other) k'
    · obtain ⟨k', hk'⟩ := hex
      have hne : k' ≠ k := by
        rintro rfl
        exact absurd (hk'.2.2.1 k0 (Finset.mem_union_right _ hk0)) (not_le.2 hL)
      rw [typeProfit_of_chooses hk']
      simp [share, hne]
    · exact typeProfit_of_not hex
  simp [screenProfit, hcapH, hL0]

/-- A deviation `{k̃}` that type `θ_L` strictly prefers to every contract of the other firm, with
`w̃ < θ_L`, is profitable. -/
theorem screenProfit_capture_low_pos (hM : M.Valid) {other : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h0 : 0 ≤ M.util M.θL k) (hL : ∀ k' ∈ other, M.util M.θL k' < M.util M.θL k)
    (hw : k.1 < M.θL) : 0 < M.screenProfit {k} other := by
  have hcapL := typeProfit_capture (M := M) (Finset.mem_singleton_self k) h0 hL
    (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
  have hH0 : 0 ≤ M.typeProfit M.θH {k} other := by
    by_cases hex : ∃ k', M.Chooses M.θH ({k} ∪ other) k'
    · obtain ⟨k', hk'⟩ := hex
      rw [typeProfit_of_chooses hk']
      by_cases hk'k : k' = k
      · subst hk'k
        exact mul_nonneg (share_nonneg _ _ _) (by linarith [hM.lt])
      · simp [share, hk'k]
    · exact (typeProfit_of_not hex).ge
  unfold screenProfit
  rw [hcapL]
  have := hM.lam_lt
  have := hM.lam_pos
  nlinarith

/-- **Section 13.D** (MWG, p. 462). In any SPNE both types accept some contract ("it is not
difficult to see"). If the high type works nowhere, neither does the low type and the contract
`(θ_L/2, 0)` is profitable; if only the low type is idle, a firm gains by raising the high
type's contract by a small `ε` and adding `(ε/2, 0)`. -/
theorem IsScreenEq.exists_bothEmployed (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsScreenEq A₁ A₂) : ∃ kL kH, M.BothEmployed A₁ A₂ kL kH := by
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hneg : ∀ θ, (¬ ∃ k, M.Chooses θ (A₁ ∪ A₂) k) → ∀ k ∈ A₁ ∪ A₂, M.util θ k < 0 := by
    intro θ hno k hk
    by_contra hle
    exact hno (exists_chooses θ ⟨k, hk, not_lt.1 hle⟩)
  have hu0 : ∀ θ w, M.util θ (w, 0) = w := fun θ w => by simp [util, hM.c_zero]
  -- the high type works
  obtain ⟨kH, hkH⟩ : ∃ kH, M.Chooses M.θH (A₁ ∪ A₂) kH := by
    by_contra hnoH
    have hnH := hneg _ hnoH
    have hnL : ∀ k ∈ A₁ ∪ A₂, M.util M.θL k < 0 := fun k hk => by
      have h1 := hnH k hk
      have h2 := hM.c_le (hval k hk)
      simp only [util] at h1 ⊢
      linarith
    have hnoL : ¬ ∃ k, M.Chooses M.θL (A₁ ∪ A₂) k := fun ⟨k, hk⟩ =>
      absurd hk.2.1 (not_le.2 (hnL k hk.1))
    have hp0 : M.screenProfit A₁ A₂ = 0 := by
      simp [screenProfit, typeProfit_of_not hnoL, typeProfit_of_not hnoH]
    have hcap : ∀ θ, (∀ k' ∈ A₁ ∪ A₂, M.util θ k' < 0) →
        M.typeProfit θ {(M.θL / 2, 0)} A₂ = θ - M.θL / 2 := by
      intro θ hn
      have := typeProfit_capture (M := M) (θ := θ) (other := A₂)
        (Finset.mem_singleton_self (M.θL / 2, (0 : ℝ))) (by rw [hu0]; linarith)
        (fun k' hk' => (hn k' (Finset.mem_union_right _ hk')).trans (by rw [hu0]; linarith))
        (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
      simpa using this
    have hd := h.2.2.1 {(M.θL / 2, 0)} (fun k' hk' => by rw [Finset.mem_singleton.1 hk'])
    rw [hp0] at hd
    simp only [screenProfit, hcap _ hnL, hcap _ hnH] at hd
    nlinarith [mul_pos (sub_pos.2 hlam1) hθL, mul_pos hlam0 (by linarith : 0 < M.θH - M.θL / 2)]
  -- the low type works
  obtain ⟨kL, hkL⟩ : ∃ kL, M.Chooses M.θL (A₁ ∪ A₂) kL := by
    by_contra hnoL
    have hnL := hneg _ hnoL
    have hLkH : M.util M.θL kH < 0 := hnL kH hkH.1
    set ε := min (-(M.util M.θL kH) / 2) ((1 - M.lam) * M.θL / 2) with hεdef
    have hεa : ε ≤ -(M.util M.θL kH) / 2 := min_le_left _ _
    have hεb : ε ≤ (1 - M.lam) * M.θL / 2 := min_le_right _ _
    have hε : 0 < ε := lt_min (by linarith) (by nlinarith)
    have hutil : ∀ θ, M.util θ (kH.1 + ε, kH.2) = M.util θ kH + ε := fun θ => by
      simp only [util]; ring
    have hpH : M.typeProfit M.θH {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ = M.θH - (kH.1 + ε) := by
      refine typeProfit_capture (θ := M.θH) (other := A₂)
        (B := {(ε / 2, 0), (kH.1 + ε, kH.2)}) (k := (kH.1 + ε, kH.2)) (by simp)
        (by rw [hutil]; linarith [hkH.2.1])
        (fun k' hk' => by rw [hutil]; linarith [hkH.2.2.1 k' (Finset.mem_union_right _ hk')])
        (fun k' hk' hne' => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      rcases hk' with hk' | hk'
      · rw [hk', hu0, hutil]; linarith [hkH.2.1]
      · exact absurd hk' hne'
    have hpL : M.typeProfit M.θL {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ = M.θL - ε / 2 := by
      refine typeProfit_capture (θ := M.θL) (other := A₂)
        (B := {(ε / 2, 0), (kH.1 + ε, kH.2)}) (k := (ε / 2, 0)) (by simp)
        (by rw [hu0]; linarith)
        (fun k' hk' => by rw [hu0]; linarith [hnL k' (Finset.mem_union_right _ hk')])
        (fun k' hk' hne' => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      rcases hk' with hk' | hk'
      · exact absurd hk' hne'
      · rw [hk', hu0, hutil]; linarith
    have hnoL' : ¬ ∃ k, M.Chooses M.θL (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
    have htot : M.screenProfit A₁ A₂ + M.screenProfit A₂ A₁ = M.lam * (M.θH - kH.1) := by
      have := typeProfit_add hkH
      unfold screenProfit
      rw [typeProfit_of_not hnoL, typeProfit_of_not hnoL', ← this]
      ring
    have h2nn := h.symm.nonneg
    have hB : ValidMenu {(ε / 2, 0), (kH.1 + ε, kH.2)} := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk <;> rw [hk]
      exact hval kH hkH.1
    have hd := h.2.2.1 _ hB
    have hdev : M.screenProfit {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ =
        (1 - M.lam) * (M.θL - ε / 2) + M.lam * (M.θH - (kH.1 + ε)) := by
      unfold screenProfit; rw [hpH, hpL]
    rw [hdev] at hd
    nlinarith [mul_le_mul_of_nonneg_left hεb (by linarith : (0 : ℝ) ≤ 1 + M.lam),
      mul_pos (mul_pos (sub_pos.2 hlam1) hθL) (by linarith : (0 : ℝ) < 3 - M.lam)]
  exact ⟨kL, kH, hkL, hkH⟩

/-- Lemma 13.D.1 for given chosen contracts `kL`, `kH`. -/
theorem zero_profits_of_employed {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) :
    M.screenProfit A₁ A₂ = 0 ∧ M.screenProfit A₂ A₁ = 0 := by
  have hsum := screenProfit_add he
  have hn1 := h.nonneg
  have hn2 := h.symm.nonneg
  -- raising both chosen contracts' wages by `ε` captures everybody
  have hdev : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kH →
      ∀ ε, 0 < ε → (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1) - ε ≤
        M.screenProfit own other := by
    intro own other heq hem ε hε
    set kL' : ℝ × ℝ := (kL.1 + ε, kL.2)
    set kH' : ℝ × ℝ := (kH.1 + ε, kH.2)
    set B : Finset (ℝ × ℝ) := {kL', kH'}
    have hB : ValidMenu B := by
      intro k hk
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk <;> rw [hk]
      · change 0 ≤ kL.2; exact chosen_valid heq.1 heq.2.1 hem.1
      · change 0 ≤ kH.2; exact chosen_valid heq.1 heq.2.1 hem.2
    have hutil : ∀ θ k, M.util θ (k.1 + ε, k.2) = M.util θ k + ε := fun θ k => by
      simp only [util]; ring
    -- type `θ` with chosen contract `k` chooses `k + ε`
    have hcap : ∀ θ k k2, M.Chooses θ (own ∪ other) k → k2 ∈ own ∪ other →
        M.typeProfit θ {(k.1 + ε, k.2), (k2.1 + ε, k2.2)} other = θ - (k.1 + ε) := by
      intro θ k k2 hk hk2
      have hch : M.Chooses θ ({(k.1 + ε, k.2), (k2.1 + ε, k2.2)} ∪ other) (k.1 + ε, k.2) := by
        refine ⟨by simp, by rw [hutil]; linarith [hk.2.1], fun k' hk' => ?_, fun k' hk' hu => ?_⟩
        · rw [hutil]
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with (rfl | rfl) | h'
          · rw [hutil]
          · rw [hutil]; linarith [hk.2.2.1 k2 hk2]
          · linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
        · rw [hutil] at hu
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with (rfl | rfl) | h'
          · exact le_rfl
          · rw [hutil] at hu
            exact hk.2.2.2 k2 hk2 (by linarith)
          · exfalso
            linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
      have hno : (k.1 + ε, k.2) ∉ other := fun hm => by
        have := hk.2.2.1 _ (Finset.mem_union_right _ hm)
        rw [hutil] at this; linarith
      rw [typeProfit_of_chooses hch]
      simp [share, hno]
    have hpL := hcap M.θL kL kH hem.1 hem.2.1
    have hpH := hcap M.θH kH kL hem.2 hem.1.1
    rw [Finset.pair_comm] at hpH
    have := heq.2.2.1 B hB
    simp only [screenProfit, B, kL', kH', hpL, hpH] at this ⊢
    linarith
  set tot := (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1)
  have htot : tot ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    rcases le_total (M.screenProfit A₁ A₂) (M.screenProfit A₂ A₁) with hle | hle
    · have := hdev A₁ A₂ h he (tot / 4) (by linarith)
      linarith
    · have := hdev A₂ A₁ h.symm he.symm (tot / 4) (by linarith)
      linarith
  constructor <;> linarith

/-- **Lemma 13.D.1** (MWG, pp. 462-463). In any SPNE both firms earn zero profits. (The book
assumes both types accept a contract; `IsScreenEq.exists_bothEmployed` proves it.) -/
theorem lemma_13_D_1 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    M.screenProfit A₁ A₂ = 0 ∧ M.screenProfit A₂ A₁ = 0 := by
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  exact zero_profits_of_employed h he

/-- A contract `k̃` near `k` that the high type strictly prefers and the low type strictly
dislikes, with wage below `w + gap` (single crossing). -/
theorem exists_high_dev (hM : M.Valid) {k : ℝ × ℝ} (hk : 0 ≤ k.2) {gap : ℝ} (hgap : 0 < gap) :
    ∃ k' : ℝ × ℝ, 0 ≤ k'.2 ∧ M.util M.θH k < M.util M.θH k' ∧ M.util M.θL k' < M.util M.θL k ∧
      k'.1 < k.1 + gap := by
  have hc : ContinuousWithinAt (fun x => M.c x (M.θ false)) (Set.Ioi k.2) k.2 :=
    ((hM.c_cont false) k.2 hk).mono fun x hx => hk.trans (le_of_lt hx)
  have hev : ∀ᶠ x in nhdsWithin k.2 (Set.Ioi k.2), M.c x M.θL < M.c k.2 M.θL + gap :=
    hc.eventually (gt_mem_nhds (by simp only [θ_false]; linarith))
  obtain ⟨x, hx, hxk⟩ := (hev.and self_mem_nhdsWithin).exists
  have hsc := hM.sc k.2 x hk hxk
  have hL := hM.c_mono false hk (hk.trans (le_of_lt hxk)) hxk
  simp only [θ_false] at hL
  set Δ := ((M.c x M.θL - M.c k.2 M.θL) + (M.c x M.θH - M.c k.2 M.θH)) / 2
  refine ⟨(k.1 + Δ, x), hk.trans (le_of_lt hxk), ?_, ?_, ?_⟩
  · simp only [util, Δ]; linarith
  · simp only [util, Δ]; linarith
  · simp only [Δ]; linarith

/-- **Lemma 13.D.2** (MWG, p. 463). No pooling equilibrium exists. -/
theorem lemma_13_D_2 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) : kL ≠ kH := by
  intro hpool
  subst hpool
  obtain ⟨h1, h2⟩ := zero_profits_of_employed h he
  have hsum := screenProfit_add he
  rw [h1, h2] at hsum
  have hp1 : kL.1 = M.Eθ := by unfold Eθ; linarith
  have hgap : 0 < M.θH - M.Eθ := by linarith [hM.Eθ_mem.2]
  obtain ⟨k', hk'0, hH, hL, hw⟩ :=
    exists_high_dev hM (chosen_valid h.1 h.2.1 he.1) hgap
  -- the firm not offering the pooling contract deviates
  have key : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kL →
      M.screenProfit own other = 0 → kL ∈ other → False := by
    intro own other heq hem hz hmem
    have hprof := screenProfit_capture_high (M := M) hmem hL
      (hem.2.2.1.trans hH.le) (fun k'' hk'' =>
        lt_of_le_of_lt (hem.2.2.2.1 k'' (Finset.mem_union_right _ hk'')) hH)
    have := heq.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hk'0)
    rw [hprof, hz] at this
    nlinarith [hM.lam_pos]
  rcases Finset.mem_union.1 he.1.1 with hm | hm
  · exact key A₂ A₁ h.symm he.symm h2 hm
  · exact key A₁ A₂ h he h1 hm

/-- In equilibrium no single-contract deviation captures the low type at a wage below `θ_L`. -/
theorem no_low_capture (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) {k : ℝ × ℝ} (hk : 0 ≤ k.2)
    (hu : M.util M.θL kL < M.util M.θL k) (hw : k.1 < M.θL) : False := by
  have h1 := (zero_profits_of_employed h he).1
  have hpos := screenProfit_capture_low_pos hM (other := A₂) (k := k)
    (he.1.2.1.trans hu.le) (fun k' hk' => lt_of_le_of_lt
      (he.1.2.2.1 k' (Finset.mem_union_right _ hk')) hu) hw
  have := h.2.2.1 {k} (fun k' hk' => by rw [Finset.mem_singleton.1 hk']; exact hk)
  linarith

/-- **Lemma 13.D.3** (MWG, pp. 463-464). In a separating equilibrium the contracts make zero
profits: `w_L = θ_L` and `w_H = θ_H`. -/
theorem lemma_13_D_3 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) :
    kL.1 = M.θL ∧ kH.1 = M.θH := by
  obtain ⟨h1, h2⟩ := zero_profits_of_employed h he
  have hsum := screenProfit_add he
  rw [h1, h2] at hsum
  have hLv := chosen_valid h.1 h.2.1 he.1
  have hHv := chosen_valid h.1 h.2.1 he.2
  have hwL : M.θL ≤ kL.1 := by
    by_contra hlt
    rw [not_le] at hlt
    refine no_low_capture hM h he (k := ((kL.1 + M.θL) / 2, kL.2)) hLv ?_ (by simp; linarith)
    simp only [util]; linarith
  have hwH : M.θH ≤ kH.1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hHv (sub_pos.2 hlt)
    have hLk : M.util M.θL k' < M.util M.θL kL := hL.trans_le (he.1.2.2.1 kH he.2.1)
    have key : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kH →
        M.screenProfit own other = 0 → kL ∈ other → False := by
      intro own other heq hem hz hmem
      have hprof := screenProfit_capture_high (M := M) hmem hLk (hem.2.2.1.trans hH.le)
        (fun k'' hk'' => lt_of_le_of_lt (hem.2.2.2.1 k'' (Finset.mem_union_right _ hk'')) hH)
      have := heq.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hk'0)
      rw [hprof, hz] at this
      nlinarith [hM.lam_pos]
    rcases Finset.mem_union.1 he.1.1 with hm | hm
    · exact key A₂ A₁ h.symm he.symm h2 hm
    · exact key A₁ A₂ h he h1 hm
  have := hM.lam_pos
  have := hM.lam_lt
  constructor <;> nlinarith

/-- **Lemma 13.D.4** (MWG, p. 464). The low type accepts `(θ_L, 0)`. -/
theorem lemma_13_D_4 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) : kL = (M.θL, 0) := by
  have hw := (lemma_13_D_3 hM h he).1
  have hLv := chosen_valid h.1 h.2.1 he.1
  refine Prod.ext hw ?_
  by_contra hne
  have htpos : 0 < kL.2 := lt_of_le_of_ne hLv (Ne.symm hne)
  have hc : 0 < M.c kL.2 M.θL := by have := hM.c_pos false htpos; simpa only [θ_false] using this
  set w := M.θL - min (M.c kL.2 M.θL) M.θL / 2
  have hm1 := min_le_left (M.c kL.2 M.θL) M.θL
  have hm0 : 0 < min (M.c kL.2 M.θL) M.θL := lt_min hc hM.θL_pos
  refine no_low_capture hM h he (k := (w, 0)) le_rfl ?_ (by simp only [w]; linarith)
  simp only [util, hM.c_zero, sub_zero, w, hw]
  linarith

/-- **Lemma 13.D.5** (MWG, pp. 464-465). The high type accepts `(θ_H, t̂_H)` where
`θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`. -/
theorem lemma_13_D_5 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) : kH = (M.θH, th) := by
  have hwH := (lemma_13_D_3 hM h he).2
  have hkL := lemma_13_D_4 hM h he
  have hHv := chosen_valid h.1 h.2.1 he.2
  rw [hM.c_zero, sub_zero] at hcth
  have hLmono := (hM.c_mono false).le_iff_le hth hHv
  simp only [θ_false] at hLmono
  have hge : th ≤ kH.2 := by
    have := he.1.2.2.1 kH he.2.1
    simp only [util, hkL, hM.c_zero, sub_zero, hwH] at this
    exact hLmono.1 (by linarith)
  refine Prod.ext hwH ?_
  by_contra hne
  have hgt : th < kH.2 := lt_of_le_of_ne hge (Ne.symm hne)
  set t' := (th + kH.2) / 2
  have ht1 : th < t' := by simp only [t']; linarith
  have ht2 : t' < kH.2 := by simp only [t']; linarith
  have hcH := hM.c_mono true (hth.trans ht1.le) hHv ht2
  have hcL := hM.c_mono false hth (hth.trans ht1.le) ht1
  simp only [θ_true, θ_false] at hcH hcL
  set η := (M.c kH.2 M.θH - M.c t' M.θH) / 2
  have hη : 0 < η := by simp only [η]; linarith
  set k' : ℝ × ℝ := (M.θH - η, t')
  have hk'L : M.util M.θL k' < M.util M.θL kL := by
    simp only [util, k', hkL, hM.c_zero, sub_zero]; linarith
  have hk'H : M.util M.θH kH < M.util M.θH k' := by
    simp only [util, k', hwH]; simp only [η]; linarith
  have h1 := (zero_profits_of_employed h he).1
  have hB : ValidMenu (A₁ ∪ {k'}) := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · rw [Finset.mem_singleton.1 hk]; exact hth.trans ht1.le
  -- the low type still chooses `kL`
  have hchL : M.Chooses M.θL ((A₁ ∪ {k'}) ∪ A₂) kL := by
    have hmem : kL ∈ (A₁ ∪ {k'}) ∪ A₂ := by
      rcases Finset.mem_union.1 he.1.1 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ hm
    refine ⟨hmem, he.1.2.1, fun k hk => ?_, fun k hk hu => ?_⟩
    · rcases Finset.mem_union.1 hk with hk | hk
      · rcases Finset.mem_union.1 hk with hk | hk
        · exact he.1.2.2.1 k (Finset.mem_union_left _ hk)
        · rw [Finset.mem_singleton.1 hk]; exact hk'L.le
      · exact he.1.2.2.1 k (Finset.mem_union_right _ hk)
    · rcases Finset.mem_union.1 hk with hk | hk
      · rcases Finset.mem_union.1 hk with hk | hk
        · exact he.1.2.2.2 k (Finset.mem_union_left _ hk) hu
        · rw [Finset.mem_singleton.1 hk] at hu; exact absurd hu hk'L.ne
      · exact he.1.2.2.2 k (Finset.mem_union_right _ hk) hu
  have hpL : M.typeProfit M.θL (A₁ ∪ {k'}) A₂ = 0 := by
    rw [typeProfit_of_chooses hchL, hkL]; simp
  have hpH : M.typeProfit M.θH (A₁ ∪ {k'}) A₂ = M.θH - k'.1 := by
    refine typeProfit_capture (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      (he.2.2.1.trans hk'H.le) (fun k hk => lt_of_le_of_lt
        (he.2.2.2.1 k (Finset.mem_union_right _ hk)) hk'H) fun k hk hne => ?_
    rcases Finset.mem_union.1 hk with hk | hk
    · exact lt_of_le_of_lt (he.2.2.2.1 k (Finset.mem_union_left _ hk)) hk'H
    · exact absurd (Finset.mem_singleton.1 hk) hne
  have := h.2.2.1 _ hB
  rw [h1] at this
  simp only [screenProfit, hpL, hpH, k'] at this
  nlinarith [hM.lam_pos]

/-- **Proposition 13.D.2** (MWG, p. 465). In any SPNE of the screening game the low type
accepts `(θ_L, 0)` and the high type `(θ_H, t̂_H)`, where `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
(Both types work by `IsScreenEq.exists_bothEmployed`.) -/
theorem proposition_13_D_2 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsScreenEq A₁ A₂) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) :
    M.Chooses M.θL (A₁ ∪ A₂) (M.θL, 0) ∧ M.Chooses M.θH (A₁ ∪ A₂) (M.θH, th) := by
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  have h1 := lemma_13_D_4 hM h he
  have h2 := lemma_13_D_5 hM h he hth hcth
  exact ⟨h1 ▸ he.1, h2 ▸ he.2⟩

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.8). If a pair of contracts `(q_L, q_H)` that
each type strictly prefers (to the other one and to her Proposition 13.D.2 contract) yields a
positive profit, no SPNE exists. A single pooling contract is the case
`q_L = q_H` (Figure 13.D.7(b), `no_eq_of_pooling_deviation`). -/
theorem no_eq_of_pair_deviation (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) {qL qH : ℝ × ℝ} (hqL : 0 ≤ qL.2)
    (hqH : 0 ≤ qH.2) (hLL : M.θL < M.util M.θL qL) (hLH : M.util M.θL qH ≤ M.util M.θL qL)
    (hHH : M.θH - M.c th M.θH < M.util M.θH qH) (hHL : M.util M.θH qL ≤ M.util M.θH qH)
    (htie : M.util M.θL qH = M.util M.θL qL → qL.2 ≤ qH.2)
    (htie' : M.util M.θH qL = M.util M.θH qH → qH.2 ≤ qL.2)
    (hprof : 0 < (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)) :
    ¬ ∃ A₁ A₂, M.IsScreenEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  have hkL := lemma_13_D_4 hM h he
  have hkH := lemma_13_D_5 hM h he hth hcth
  have h1 := (zero_profits_of_employed h he).1
  have huL : ∀ k ∈ A₂, M.util M.θL k < M.util M.θL qL := fun k hk => by
    have := he.1.2.2.1 k (Finset.mem_union_right _ hk)
    have hu0 : M.util M.θL (M.θL, 0) = M.θL := by simp [util, hM.c_zero]
    rw [hkL, hu0] at this; linarith
  have huH : ∀ k ∈ A₂, M.util M.θH k < M.util M.θH qH := fun k hk => by
    have := he.2.2.2.1 k (Finset.mem_union_right _ hk)
    have hu0 : M.util M.θH (M.θH, th) = M.θH - M.c th M.θH := rfl
    rw [hkH, hu0] at this; linarith
  -- each type chooses her contract of the pair
  have hcL : M.Chooses M.θL ({qL, qH} ∪ A₂) qL := by
    refine ⟨by simp, by linarith [hM.θL_pos], fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact le_rfl
      · exact hLH
      · exact (huL k hk).le
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact le_rfl
      · exact htie hu
      · exact absurd hu (huL k hk).ne
  have hcH : M.Chooses M.θH ({qL, qH} ∪ A₂) qH := by
    have h0 : 0 ≤ M.θH - M.c th M.θH := by
      have := hM.c_le hth
      have hc' := hcth
      rw [hM.c_zero, sub_zero] at hc'
      linarith [hM.θL_pos]
    refine ⟨by simp, by linarith, fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact hHL
      · exact le_rfl
      · exact (huH k hk).le
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact htie' hu
      · exact le_rfl
      · exact absurd hu (huH k hk).ne
  have hnL : qL ∉ A₂ := fun hm => lt_irrefl _ (huL qL hm)
  have hnH : qH ∉ A₂ := fun hm => lt_irrefl _ (huH qH hm)
  have hpL : M.typeProfit M.θL {qL, qH} A₂ = M.θL - qL.1 := by
    rw [typeProfit_of_chooses hcL]; simp [share, hnL]
  have hpH : M.typeProfit M.θH {qL, qH} A₂ = M.θH - qH.1 := by
    rw [typeProfit_of_chooses hcH]; simp [share, hnH]
  have hB : ValidMenu {qL, qH} := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have := h.2.2.1 _ hB
  rw [h1] at this
  simp only [screenProfit, hpL, hpH] at this
  linarith

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(b)). If a pooling contract `(w̃, t̃)` with
`w̃ < E[θ]` gives both types more than their Proposition 13.D.2 contracts, no SPNE exists. -/
theorem no_eq_of_pooling_deviation (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) {p : ℝ × ℝ} (hp : 0 ≤ p.2)
    (hL : M.θL < M.util M.θL p) (hH : M.θH - M.c th M.θH < M.util M.θH p) (hw : p.1 < M.Eθ) :
    ¬ ∃ A₁ A₂, M.IsScreenEq A₁ A₂ :=
  no_eq_of_pair_deviation hM hth hcth hp hp hL le_rfl hH le_rfl (fun _ => le_rfl)
    (fun _ => le_rfl) (by unfold Eθ at hw; nlinarith)

/-- The model of Exercise 13.C.3 with `λ = l`. -/
noncomputable def screenModel (l : ℝ) : SigModel := { crossModel with lam := l }

theorem screenModel_valid {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : (screenModel l).Valid where
  θL_pos := crossModel_valid.θL_pos
  lt := crossModel_valid.lt
  lam_pos := h0
  lam_lt := h1
  r_nonneg := crossModel_valid.r_nonneg
  r_lt := crossModel_valid.r_lt
  c_zero := crossModel_valid.c_zero
  c_mono := crossModel_valid.c_mono
  c_cont := crossModel_valid.c_cont
  sc := crossModel_valid.sc

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(b)), an instance: with `θ_L = 1`, `θ_H = 2`,
`c(t, θ_L) = t`, `c(t, θ_H) = t²/(1 + t)` (`t̂_H = 1`) and `λ = 3/4`, the pooling contract
`(8/5, 0)` breaks the separating contracts: no SPNE exists. -/
theorem nonexistence_pooling_instance :
    ¬ ∃ A₁ A₂, (screenModel (3 / 4)).IsScreenEq A₁ A₂ := by
  have hv := screenModel_valid (l := 3 / 4) (by norm_num) (by norm_num)
  refine no_eq_of_pooling_deviation hv (th := 1) zero_le_one ?_ (p := (8 / 5, 0)) le_rfl ?_ ?_ ?_
  all_goals simp [screenModel, crossModel, util, Eθ]
  all_goals norm_num

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.8), an instance: with the same costs and
`λ = 2/5` no single pooling contract breaks the separating contracts (`E[θ] = 7/5` is below the
high type's utility `3/2`), but the pair `(11/10, 0)`, `(46/25, 3/4)` does: no SPNE exists. -/
theorem nonexistence_pair_instance :
    (screenModel (2 / 5)).Eθ < (screenModel (2 / 5)).θH - (screenModel (2 / 5)).c 1
      (screenModel (2 / 5)).θH ∧
    ¬ ∃ A₁ A₂, (screenModel (2 / 5)).IsScreenEq A₁ A₂ := by
  have hv := screenModel_valid (l := 2 / 5) (by norm_num) (by norm_num)
  refine ⟨by simp [screenModel, crossModel, Eθ]; norm_num, ?_⟩
  refine no_eq_of_pair_deviation hv (th := 1) zero_le_one ?_ (qL := (11 / 10, 0))
    (qH := (46 / 25, 3 / 4)) le_rfl (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [screenModel, crossModel, util]
  all_goals norm_num

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence and welfare of screening equilibria

MWG, Section 13.D, pp. 465-466, Figure 13.D.7(a) and footnote 25.

* `isScreenEq_sepMenu`: an existence criterion. If no contract `(w, t)` with `w < θ_H` that the
  high type likes at least as much as `(θ_H, t̂_H)` can be paired with a low-type contract on the
  low type's indifference curve through it at a positive profit (`NoProfitableDeviation`), both
  firms offering `{(θ_L, 0), (θ_H, t̂_H)}` is an SPNE. Instances: `figure_13_D_7a`
  (`screenModel (1/5)`, the costs of Exercise 13.C.3), and the linear model `linModel`.
* Welfare (p. 466): `screening_low_worse`, `screening_inefficient` (the high type's task is
  wasteful), `screening_high_better` (when an SPNE exists the high type gets at least `E[θ]`),
  `screening_no_strict_improvement` (when an SPNE exists, no incentive compatible allocation
  gives both types strictly more at a positive profit).
* Footnote 25 and a correction: `footnote_25_counterexample`. In `linModel` an SPNE exists, the
  high type gets exactly `E[θ]` (not strictly more), and the pooling allocation `(3/2, 0)` is a
  constrained Pareto improvement: the equilibrium is not a constrained Pareto optimum.
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- **Section 13.D** (MWG, p. 465). The menu `{(θ_L, 0), (θ_H, t̂_H)}` of Proposition 13.D.2. -/
noncomputable def sepMenu (M : SigModel) (th : ℝ) : Finset (ℝ × ℝ) := {(M.θL, 0), (M.θH, th)}

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.7(a)). No deviation breaks the separating
contracts: for every contract `(w, t)` with `w < θ_H` that the high type weakly prefers to
`(θ_H, t̂_H)`, pairing it with the low type's indifferent wage at `t = 0` loses money. -/
def NoProfitableDeviation (M : SigModel) (th : ℝ) : Prop :=
  ∀ w t, 0 ≤ t → M.θH - M.c th M.θH ≤ w - M.c t M.θH → w < M.θH →
    (1 - M.lam) * (M.θL - w + M.c t M.θL) + M.lam * (M.θH - w) ≤ 0

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(a)). The existence criterion: under
`NoProfitableDeviation`, both firms offering `{(θ_L, 0), (θ_H, t̂_H)}` is a pure SPNE. -/
theorem isScreenEq_sepMenu (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (hN : M.NoProfitableDeviation th) :
    M.IsScreenEq (M.sepMenu th) (M.sepMenu th) := by
  rw [hM.c_zero, sub_zero] at hcth
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  set A := M.sepMenu th with hA
  have hcL : ∀ t, 0 ≤ t → 0 ≤ M.c t M.θL := fun t ht => by
    have := hM.c_nonneg false ht; simpa only [θ_false] using this
  have hthpos : 0 < th := by
    rcases eq_or_lt_of_le hth with h0 | h0
    · rw [← h0, hM.c_zero] at hcth; linarith
    · exact h0
  have hcHL := hM.c_lt_of_pos hthpos
  have hAval : ValidMenu A := by
    intro k hk
    simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> rw [hk]
    exact hth
  have hAL : ∀ k ∈ A, M.util M.θL k = M.θL := by
    intro k hk
    simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> rw [hk] <;> simp only [util, hM.c_zero] <;> linarith
  have huH : M.util M.θH (M.θH, th) = M.θH - M.c th M.θH := rfl
  have hHgt : M.θL < M.θH - M.c th M.θH := by linarith
  have hmemL : (M.θL, (0 : ℝ)) ∈ A := by simp [hA, sepMenu]
  have hmemH : (M.θH, th) ∈ A := by simp [hA, sepMenu]
  have hu0 : ∀ θ w, M.util θ (w, 0) = w := fun θ w => by simp [util, hM.c_zero]
  -- the equilibrium profit is zero
  have hzero : M.screenProfit A A = 0 := by
    have hchL : M.Chooses M.θL (A ∪ A) (M.θL, 0) := by
      rw [Finset.union_self]
      refine ⟨hmemL, by rw [hu0]; exact hθL.le, fun k hk => by rw [hAL k hk, hu0],
        fun k hk _ => hAval k hk⟩
    have hchH : M.Chooses M.θH (A ∪ A) (M.θH, th) := by
      rw [Finset.union_self]
      refine chooses_of_strict hmemH (by rw [huH]; linarith) fun k hk hne => ?_
      simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk
      · rw [hk, hu0, huH]; exact hHgt
      · exact absurd hk hne
    unfold screenProfit
    rw [typeProfit_of_chooses hchL, typeProfit_of_chooses hchH]
    simp
  refine ⟨hAval, hAval, fun B hB => ?_, fun B hB => ?_⟩ <;> rw [hzero] <;>
  · have hval : ∀ k ∈ B ∪ A, 0 ≤ k.2 := fun k hk => by
      rcases Finset.mem_union.1 hk with hk | hk
      · exact hB k hk
      · exact hAval k hk
    -- the low type yields no profit
    have hπL : M.typeProfit M.θL B A ≤ 0 := by
      by_cases hex : ∃ k, M.Chooses M.θL (B ∪ A) k
      · obtain ⟨k, hk⟩ := hex
        rw [typeProfit_of_chooses hk]
        have hge := hk.2.2.1 _ (Finset.mem_union_right _ hmemL)
        rw [hu0] at hge
        have := hcL _ (hval k hk.1)
        simp only [util] at hge
        exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
      · rw [typeProfit_of_not hex]
    by_cases hexH : ∃ k, M.Chooses M.θH (B ∪ A) k
    · obtain ⟨kH, hkH⟩ := hexH
      have hπH : M.typeProfit M.θH B A = share B A kH * (M.θH - kH.1) :=
        typeProfit_of_chooses hkH
      rcases le_or_gt M.θH kH.1 with hw | hw
      · have : M.typeProfit M.θH B A ≤ 0 := by
          rw [hπH]; exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
        unfold screenProfit; nlinarith
      · have hgeH := hkH.2.2.1 _ (Finset.mem_union_right _ hmemH)
        rw [huH] at hgeH
        have hkv := hval kH hkH.1
        have hdev := hN kH.1 kH.2 hkv hgeH hw
        -- the high type's contract has a lower task level, so the low type likes it more
        have hlt : kH.2 < th := by
          by_contra hle
          rw [not_lt] at hle
          have hm := (hM.c_mono true).le_iff_le hth hkv
          simp only [θ_true] at hm
          have := hm.2 hle
          simp only [util] at hgeH
          linarith
        have hsc := hM.sc kH.2 th hkv hlt
        have hLkH : M.θL < M.util M.θL kH := by
          simp only [util] at hgeH ⊢; linarith
        obtain ⟨kL, hkL⟩ := exists_chooses (M := M) M.θL ⟨kH, hkH.1, by linarith⟩
        have hkLu := hkL.2.2.1 kH hkH.1
        have hkLA : kL ∉ A := fun hm => by rw [hAL kL hm] at hkLu; linarith
        have hkLB : kL ∈ B := by
          rcases Finset.mem_union.1 hkL.1 with hm | hm
          · exact hm
          · exact absurd hm hkLA
        have hπL' : M.typeProfit M.θL B A = M.θL - kL.1 := by
          rw [typeProfit_of_chooses hkL]; simp [share, hkLB, hkLA]
        have hcLk := hcL _ (hval kL hkL.1)
        have hshH : share B A kH * (M.θH - kH.1) ≤ M.θH - kH.1 := by
          have := share_le_one B A kH
          nlinarith
        simp only [util] at hkLu
        unfold screenProfit
        rw [hπL', hπH]
        nlinarith
    · unfold screenProfit
      rw [typeProfit_of_not hexH]
      nlinarith

/-- **Section 13.D** (MWG, p. 466). The low type is worse off with screening (`θ_L`) than
without it (`E[θ]`). -/
theorem screening_low_worse (hM : M.Valid) : M.θL < M.Eθ := hM.Eθ_mem.1

/-- **Section 13.D** (MWG, p. 466). Screening equilibria are Pareto inefficient: the high type
performs the unproductive task `t̂_H > 0` and would be strictly better off at `(θ_H, 0)`. -/
theorem screening_inefficient (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) :
    0 < th ∧ M.θH - M.c th M.θH < M.θH := by
  rw [hM.c_zero, sub_zero] at hcth
  have hthpos : 0 < th := by
    rcases eq_or_lt_of_le hth with h0 | h0
    · rw [← h0, hM.c_zero] at hcth; linarith [hM.lt]
    · exact h0
  refine ⟨hthpos, ?_⟩
  have := hM.c_pos true hthpos
  simp only [θ_true] at this
  linarith

/-- **Section 13.D** (MWG, p. 466). When an SPNE exists the high type is at least as well off as
without screening: `E[θ] ≤ θ_H - c(t̂_H, θ_H)` (otherwise a pooling contract breaks the
separating contracts). The inequality can be an equality (`footnote_25_counterexample`). -/
theorem screening_high_better (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (h : ∃ A₁ A₂, M.IsScreenEq A₁ A₂) :
    M.Eθ ≤ M.θH - M.c th M.θH := by
  by_contra hlt
  rw [not_le] at hlt
  have hL := hM.Eθ_mem.1
  set m := max M.θL (M.θH - M.c th M.θH)
  have hm1 := le_max_left M.θL (M.θH - M.c th M.θH)
  have hm2 := le_max_right M.θL (M.θH - M.c th M.θH)
  have hmE : m < M.Eθ := max_lt hL hlt
  refine no_eq_of_pooling_deviation hM hth hcth (p := ((m + M.Eθ) / 2, 0)) le_rfl ?_ ?_ ?_ h
  all_goals simp only [util, hM.c_zero, sub_zero]
  all_goals linarith

/-- **Section 13.D** (MWG, p. 466, footnote 25). An allocation `(q_L, q_H)` a central authority
that cannot observe types can implement: nonnegative task levels, incentive compatibility, and
a nonnegative expected profit (budget). -/
def ScreenFeasible (M : SigModel) (qL qH : ℝ × ℝ) : Prop :=
  0 ≤ qL.2 ∧ 0 ≤ qH.2 ∧ M.util M.θL qH ≤ M.util M.θL qL ∧ M.util M.θH qL ≤ M.util M.θH qH ∧
    0 ≤ (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)

/-- **Section 13.D** (MWG, p. 466). Constrained optimality of screening equilibria, in the form
that holds: if an SPNE exists, no incentive compatible allocation gives both types strictly
more than their Proposition 13.D.2 contracts at a strictly positive expected profit. (The
book's unqualified claim fails, `footnote_25_counterexample`.) -/
theorem screening_no_strict_improvement (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (h : ∃ A₁ A₂, M.IsScreenEq A₁ A₂)
    {qL qH : ℝ × ℝ} (hq : M.ScreenFeasible qL qH) (hLL : M.θL < M.util M.θL qL)
    (hHH : M.θH - M.c th M.θH < M.util M.θH qH)
    (hprof : 0 < (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)) : False := by
  obtain ⟨hqL, hqH, hLH, hHL, -⟩ := hq
  obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hqH hprof
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  refine no_eq_of_pair_deviation hM hth hcth (qL := qL) (qH := k') hqL hk'0 hLL
    (hL.le.trans hLH) (hHH.trans hH) (hHL.trans hH.le)
    (fun he => absurd he (ne_of_lt (hL.trans_le hLH))) (fun he => absurd he
      (ne_of_lt (lt_of_le_of_lt hHL hH))) ?_ h
  nlinarith [mul_lt_mul_of_pos_left hw hlam0]

/-- **Section 13.D**. A linear screening model: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`,
`c(t, θ) = (3 - θ)t/2` (so `c(t, θ_L) = t`, `c(t, θ_H) = t/2`). -/
noncomputable def linModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun e θ => (3 - θ) * e / 2

theorem linModel_cL (e : ℝ) : linModel.c e linModel.θL = e := by
  simp only [linModel]; ring

theorem linModel_cH (e : ℝ) : linModel.c e linModel.θH = e / 2 := by
  simp only [linModel]; ring

theorem linModel_valid : linModel.Valid where
  θL_pos := by norm_num [linModel]
  lt := by norm_num [linModel]
  lam_pos := by norm_num [linModel]
  lam_lt := by norm_num [linModel]
  r_nonneg := by norm_num [linModel]
  r_lt := by norm_num [linModel]
  c_zero := fun θ => by simp [linModel]
  c_mono := fun b => by
    cases b
    · intro a _ b _ hab; simp only [θ_false, linModel_cL]; exact hab
    · intro a _ b _ hab; simp only [θ_true, linModel_cH]; linarith
  c_cont := fun b => by
    cases b
    · simp only [θ_false, linModel_cL]; exact continuousOn_id
    · simp only [θ_true, linModel_cH]; exact (continuous_id.div_const 2).continuousOn
  sc := fun e e' _ hlt => by
    rw [linModel_cH, linModel_cH, linModel_cL, linModel_cL]; linarith

/-- **Section 13.D** (MWG, p. 466, footnote 25), counterexample. In `linModel` (`t̂_H = 1`) both
firms offering `{(1, 0), (2, 1)}` is an SPNE; the high type's equilibrium utility `3/2` equals
`E[θ]`; and the pooling allocation `(3/2, 0)` is feasible for a central authority, gives the low
type `3/2 > 1` and the high type `3/2`: a constrained Pareto improvement. -/
theorem footnote_25_counterexample :
    linModel.IsScreenEq (linModel.sepMenu 1) (linModel.sepMenu 1) ∧
      linModel.θH - linModel.c 1 linModel.θH = linModel.Eθ ∧
      linModel.ScreenFeasible (3 / 2, 0) (3 / 2, 0) ∧
      linModel.θL < linModel.util linModel.θL (3 / 2, 0) ∧
      linModel.util linModel.θH (3 / 2, 0) = linModel.θH - linModel.c 1 linModel.θH := by
  have hv := linModel_valid
  refine ⟨isScreenEq_sepMenu hv zero_le_one ?_ ?_, ?_, ?_, ?_, ?_⟩
  · rw [linModel_cL, hv.c_zero]; norm_num [linModel]
  · intro w t _ hge _
    rw [linModel_cH, linModel_cH] at hge
    rw [linModel_cL]
    simp only [linModel] at hge ⊢
    linarith
  · rw [linModel_cH]; norm_num [linModel, Eθ]
  · refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩; norm_num [linModel]
  · simp only [util, hv.c_zero]; norm_num [linModel]
  · simp only [util, hv.c_zero, linModel_cH]; norm_num [linModel]

theorem screenModel_cL (l e : ℝ) : (screenModel l).c e (screenModel l).θL = e := crossModel_cL e

theorem screenModel_cH (l e : ℝ) :
    (screenModel l).c e (screenModel l).θH = e ^ 2 / (1 + e) := crossModel_cH e

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(a)), an instance: with the costs of
`screenModel` (`c(t, θ_L) = t`, `c(t, θ_H) = t²/(1 + t)`, `t̂_H = 1`) and `λ = 1/5`, both firms
offering `{(1, 0), (2, 1)}` is an SPNE, so the hypotheses of Lemmas 13.D.1-13.D.5 and
Proposition 13.D.2 are satisfiable; the high type strictly gains from screening (`3/2 > 6/5`). -/
theorem figure_13_D_7a :
    (screenModel (1 / 5)).IsScreenEq ((screenModel (1 / 5)).sepMenu 1)
      ((screenModel (1 / 5)).sepMenu 1) ∧
      (screenModel (1 / 5)).Eθ < (screenModel (1 / 5)).θH -
        (screenModel (1 / 5)).c 1 (screenModel (1 / 5)).θH := by
  have hv := screenModel_valid (l := 1 / 5) (by norm_num) (by norm_num)
  refine ⟨isScreenEq_sepMenu hv zero_le_one ?_ ?_, ?_⟩
  · rw [screenModel_cL, hv.c_zero]; norm_num [screenModel, crossModel]
  · intro w t ht hge hw
    rw [screenModel_cH, screenModel_cH] at hge
    rw [screenModel_cL]
    simp only [screenModel, crossModel] at hge hw ⊢
    set g := t ^ 2 / (1 + t) with hg
    have hgt : g * (1 + t) = t ^ 2 := by rw [hg]; field_simp
    have ht1 : t < 1 := by nlinarith
    have hkey : 4 * t / 5 - 3 / 10 ≤ g := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : (0 : ℝ) < 1 + t),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (0 : ℝ) ≤ 3 - 2 * t)]
    norm_num at hge ⊢
    linarith
  · rw [screenModel_cH]; norm_num [screenModel, crossModel, Eθ]

/-- **Proposition 13.D.2** (MWG, p. 465), the instance: in the SPNE of `figure_13_D_7a` the low
type takes `(1, 0)` and the high type `(2, 1)`, and both firms earn zero. -/
theorem proposition_13_D_2_instance :
    (screenModel (1 / 5)).Chooses (screenModel (1 / 5)).θL
        ((screenModel (1 / 5)).sepMenu 1 ∪ (screenModel (1 / 5)).sepMenu 1) (1, 0) ∧
      (screenModel (1 / 5)).Chooses (screenModel (1 / 5)).θH
        ((screenModel (1 / 5)).sepMenu 1 ∪ (screenModel (1 / 5)).sepMenu 1) (2, 1) ∧
      (screenModel (1 / 5)).screenProfit ((screenModel (1 / 5)).sepMenu 1)
        ((screenModel (1 / 5)).sepMenu 1) = 0 := by
  have hv := screenModel_valid (l := 1 / 5) (by norm_num) (by norm_num)
  have hcth : (screenModel (1 / 5)).θH - (screenModel (1 / 5)).c 1 (screenModel (1 / 5)).θL =
      (screenModel (1 / 5)).θL - (screenModel (1 / 5)).c 0 (screenModel (1 / 5)).θL := by
    rw [screenModel_cL, hv.c_zero]; norm_num [screenModel, crossModel]
  have h := proposition_13_D_2 hv figure_13_D_7a.1 zero_le_one hcth
  exact ⟨h.1, h.2, (lemma_13_D_1 hv figure_13_D_7a.1).1⟩

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# End-of-chapter exercises

MWG, Chapter 13 exercises, pp. 473-476.

* `exercise_13_B_4`: the no-trade theorem: if trade at price `p` requires both parties to be
  strictly better off given their private signals, trade has probability zero (finite
  probability space).
* `exercise_13_B_5a`-`exercise_13_B_5d`: `r(θ) = r` with the belief `E[θ | Θ = ∅] = θ̲`:
  the equilibrium wages, Pareto ranking, SPNE of the wage game, constrained optimality.
* `exercise_13_C_5a`, `exercise_13_C_5b`: the consumer buys iff `λv_H + (1 - λ)v_L ≥ p`; no
  separating PBE with advertising exists.
* `exercise_13_C_6a`: the pooling loan rate `R = (1 + r)/(λp_G + (1 - λ)p_B)` and its comparative
  statics; good projects may go unfinanced.
-/

namespace MWG.AdverseSelection

open Finset

/-- Fiberwise positivity: if every fiber of `Yf` with positive mass has a positive weighted sum
of `g`, and `A` has positive mass, the weighted sum of `g` over `A` is positive. -/
theorem sum_pos_of_fibers {Ω Y : Type*} [DecidableEq Y] (P g : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (A : Finset Ω) (Yf : Ω → Y)
    (hg : ∀ y, 0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω →
      0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω * g ω)
    (hA : 0 < ∑ ω ∈ A, P ω) : 0 < ∑ ω ∈ A, P ω * g ω := by
  rw [← sum_fiberwise_of_maps_to (g := Yf) (t := A.image Yf)
    (fun ω hω => mem_image_of_mem _ hω)]
  have hnn : ∀ y ∈ A.image Yf, 0 ≤ ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω * g ω := by
    intro y _
    rcases eq_or_lt_of_le (sum_nonneg (fun ω _ => hP ω) :
      0 ≤ ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω) with h0 | hpos
    · have hz : ∀ ω ∈ A.filter (fun ω => Yf ω = y), P ω = 0 :=
        (sum_eq_zero_iff_of_nonneg (fun ω _ => hP ω)).1 h0.symm
      rw [sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]]
    · exact (hg y hpos).le
  obtain ⟨y, hy, hpos⟩ : ∃ y ∈ A.image Yf, 0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω := by
    by_contra hno
    push Not at hno
    have : ∑ ω ∈ A, P ω ≤ 0 := by
      rw [← sum_fiberwise_of_maps_to (g := Yf) (t := A.image Yf)
        (fun ω hω => mem_image_of_mem _ hω)]
      exact sum_nonpos hno
    linarith
  exact lt_of_lt_of_le (hg y hpos) (single_le_sum hnn hy)

/-- **Exercise 13.B.4** (MWG, p. 473). The no-trade theorem. On a finite probability space
(`P ≥ 0`) the asset is worth `V`, Ms. 1 observes `Y₁`, individual 2 observes `Y₂`, and each says
"trade" according to her signal (`T₁`, `T₂`); trade at price `p` happens when both do. If every
signal of Ms. 1 that leads to trade with positive probability makes her expected gain
`p - V` from trading strictly positive, and likewise for 2 with gain `V - p`, then trade has
probability zero. -/
theorem exercise_13_B_4 {Ω Y₁ Y₂ : Type*} [Fintype Ω] [DecidableEq Y₁] [DecidableEq Y₂]
    (P V : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (Y1 : Ω → Y₁) (Y2 : Ω → Y₂) (T1 : Y₁ → Bool)
    (T2 : Y₂ → Bool) (p : ℝ)
    (h1 : ∀ y, 0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y), P ω →
      0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y), P ω * (p - V ω))
    (h2 : ∀ y, 0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y), P ω →
      0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y), P ω * (V ω - p)) :
    ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω)), P ω = 0 := by
  set A := univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω))
  have hf1 : ∀ y, A.filter (fun ω => Y1 ω = y) =
      univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y) := by
    intro y; ext ω; simp [A, and_assoc]
  have hf2 : ∀ y, A.filter (fun ω => Y2 ω = y) =
      univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y) := by
    intro y; ext ω; simp [A, and_assoc]
  by_contra hne
  have hA : 0 < ∑ ω ∈ A, P ω := lt_of_le_of_ne (sum_nonneg fun ω _ => hP ω) (Ne.symm hne)
  have s1 := sum_pos_of_fibers P (fun ω => p - V ω) hP A Y1
    (fun y hy => by rw [hf1] at hy ⊢; exact h1 y hy) hA
  have s2 := sum_pos_of_fibers P (fun ω => V ω - p) hP A Y2
    (fun y hy => by rw [hf2] at hy ⊢; exact h2 y hy) hA
  have : ∑ ω ∈ A, P ω * (p - V ω) + ∑ ω ∈ A, P ω * (V ω - p) = 0 := by
    rw [← sum_add_distrib]; exact sum_eq_zero fun ω _ => by ring
  linarith

/-- **Exercise 13.C.5(a)** (MWG, p. 475). A risk-neutral consumer who cannot observe quality buys
at price `p` iff her expected valuation is at least `p`. -/
theorem exercise_13_C_5a (lam vH vL p : ℝ) :
    (p ≤ lam * vH + (1 - lam) * vL ↔ 0 ≤ lam * (vH - p) + (1 - lam) * (vL - p)) := by
  constructor <;> intro h <;> linarith

/-- **Exercise 13.C.5(b)** (MWG, p. 475). With `v_H > p > v_L > c_H > c_L`, there is no separating
PBE in which the two qualities choose different advertising levels `A_H ≠ A_L`: in such an
equilibrium the consumer buys only after `A_H` (she believes the quality is low after `A_L` and
`p > v_L`), so the low-quality firm must prefer not selling to mimicking
(`-A_L ≥ p - c_L - A_H`), and the high-quality firm must prefer selling
(`p - c_H - A_H ≥ -A_L`), which requires `c_H ≤ c_L`. -/
theorem exercise_13_C_5b {p cH cL : ℝ} (hc : cL < cH) :
    ¬ ∃ AH AL : ℝ, 0 ≤ AH ∧ 0 ≤ AL ∧ p - cL - AH ≤ -AL ∧ -AL ≤ p - cH - AH := by
  rintro ⟨AH, AL, -, -, hL, hH⟩
  linarith

/-- **Exercise 13.C.6(a)** (MWG, p. 475). Banks break even at `R(λp_G + (1 - λ)p_B) = 1 + r`
when both types borrow; entrepreneurs borrow iff `R ≤ Π`. So all projects are financed at
`R = (1 + r)/p̄` if `p̄Π ≥ 1 + r` and none otherwise, `p̄ = λp_G + (1 - λ)p_B`. `R` falls when
`p_G` or `λ` rise and rises with `r`; when `p̄Π < 1 + r < p_GΠ` no project is financed
although good projects are worth financing. -/
theorem exercise_13_C_6a {pG pB lam r Pf : ℝ} (hB : 0 < pB) (hBG : pB < pG) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hr : 0 ≤ r) :
    let pbar := lam * pG + (1 - lam) * pB
    0 < pbar ∧ (1 + r) / pbar * pbar = 1 + r ∧
      ((1 + r) / pbar ≤ Pf ↔ 1 + r ≤ pbar * Pf) ∧
      (∀ pG', pG < pG' → (1 + r) / (lam * pG' + (1 - lam) * pB) < (1 + r) / pbar) ∧
      (∀ lam', lam < lam' → (1 + r) / (lam' * pG + (1 - lam') * pB) < (1 + r) / pbar) ∧
      (∀ r', r < r' → (1 + r) / pbar < (1 + r') / pbar) := by
  intro pbar
  have hp : 0 < pbar := by simp only [pbar]; nlinarith
  refine ⟨hp, div_mul_cancel₀ _ hp.ne', ?_, fun pG' h => ?_, fun lam' h => ?_, fun r' h => ?_⟩
  · rw [div_le_iff₀ hp, mul_comm]
  · exact div_lt_div_of_pos_left (by linarith) hp (by simp only [pbar]; nlinarith)
  · exact div_lt_div_of_pos_left (by linarith) hp (by simp only [pbar]; nlinarith)
  · exact div_lt_div_of_pos_right (by linarith) hp

/-- **Exercise 13.B.5** (MWG, p. 473). With `r(θ) = r` and the belief `E[θ | Θ = ∅] = θ̲`, a wage
`w` is a competitive equilibrium wage iff `w = E[θ]` when `w ≥ r` and `w = θ̲` when `w < r`. -/
def eqWagesB5 (m θl r : ℝ) : Set ℝ := {w | (r ≤ w → w = m) ∧ (w < r → w = θl)}

/-- **Exercise 13.B.5(a)** (MWG, p. 473). If `E[θ] ≥ r > θ̲` there are two equilibria,
`w* = E[θ]` (everybody employed) and `w* = θ̲` (nobody); if `θ̲ ≥ r` the only one is `E[θ]`; if
`r > E[θ]` the only one is `θ̲`. -/
theorem exercise_13_B_5a {m θl r : ℝ} (hθm : θl ≤ m) :
    (r ≤ m → θl < r → eqWagesB5 m θl r = {m, θl}) ∧ (r ≤ θl → eqWagesB5 m θl r = {m}) ∧
      (m < r → eqWagesB5 m θl r = {θl}) := by
  refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩ <;> ext w <;>
    simp only [eqWagesB5, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · exact Or.inl (ha hw)
      · exact Or.inr (hb hw)
    · rintro (rfl | rfl)
      · exact ⟨fun _ => rfl, fun hw => absurd h1 (not_le.2 hw)⟩
      · exact ⟨fun hw => absurd hw (not_le.2 h2), fun _ => rfl⟩
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · exact ha hw
      · have := hb hw; linarith
    · rintro rfl; exact ⟨fun _ => rfl, fun hw => by linarith⟩
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · have := ha hw; linarith
      · exact hb hw
    · rintro rfl; exact ⟨fun hw => by linarith, fun _ => rfl⟩

/-- **Exercise 13.B.5(b)** (MWG, p. 473). If `E[θ] > r` the full-employment equilibrium Pareto
dominates the no-employment one: firms earn zero in both, and every worker earns
`E[θ] > r` instead of `r`. -/
theorem exercise_13_B_5b {m θl r : ℝ} (hm : r < m) (hθl : θl < r) :
    max θl r < max m r ∧ max m r = m := by
  rw [max_eq_right hθl.le, max_eq_left hm.le]; exact ⟨hm, rfl⟩

/-- **Exercise 13.B.5(c)** (MWG, p. 473). The SPNE of the two-firm wage game when every type
accepts any wage `≥ r` (profit `E[θ] - w` for the firm with the highest wage): if `E[θ] > r`,
both firms offer `E[θ]` (the full-employment equilibrium); if `E[θ] = r`, any wages `≤ r`; if
`E[θ] < r`, any wages `< r` (nobody is employed). -/
theorem exercise_13_B_5c {m r : ℝ} (hm : 0 ≤ m) (w : Fin 2 → ℝ) :
    MWG.SimultaneousMoveGames.IsNashEquilibrium
        (wageGame (({ θL := 0, θH := 0, lam := 0, r := r, c := fun _ _ => 0 } :
          SigModel).offerProfit m)) w ↔
      (r < m → w 0 = m ∧ w 1 = m) ∧ (r = m → w 0 ≤ m ∧ w 1 ≤ m) ∧
        (m < r → w 0 < r ∧ w 1 < r) :=
  SigModel.bertrand_iff _ hm w

/-- **Exercise 13.B.5(d)** (MWG, p. 473). With `r(θ) = r`, the highest-wage competitive
equilibrium (`E[θ]` if `E[θ] ≥ r`, otherwise `θ̲` with nobody employed) is a constrained Pareto
optimum. -/
theorem exercise_13_B_5d {μ : MeasureTheory.Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (r : ℝ) :
    IsConstrainedPO μ θl θh (fun _ => r) (if r ≤ meanType μ then meanType μ else θl) := by
  have := hd.prob
  intro we wu hb ⟨_, θ0, _, hstrict⟩
  simp only at hstrict
  have hl : θl ≤ meanType μ := hd.meanType_mem.1
  have heqpay : max r (meanType μ) ≤ max (if r ≤ meanType μ then meanType μ else θl) r := by
    split_ifs with h
    · rw [max_comm]
    · rw [max_eq_left (not_le.1 h).le]; exact le_max_right _ _
  unfold BudgetOK at hb
  by_cases hd' : r ≤ we - wu
  · have huniv : acceptSet (fun _ => r) (we - wu) = Set.univ := by
      ext θ; simp [acceptSet, hd']
    rw [huniv, MeasureTheory.Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one,
      MeasureTheory.setIntegral_univ] at hb
    have hwe : we ≤ meanType μ := by unfold meanType; linarith
    have : max we (wu + r) = we := max_eq_left (by linarith)
    rw [this] at hstrict
    linarith [le_max_right r (meanType μ)]
  · have hemp : acceptSet (fun _ => r) (we - wu) = ∅ := by
      ext θ; simp [acceptSet, not_le.1 hd']
    rw [hemp] at hb
    simp at hb
    have : max we (wu + r) = wu + r := max_eq_right (by linarith [not_le.1 hd'])
    rw [this] at hstrict
    linarith [le_max_left r (meanType μ),
      le_max_right (if r ≤ meanType μ then meanType μ else θl) r]

/-- **Proposition 13.B.2**, an instance (MWG, p. 447): with `r(θ) = θ/4` and `θ` uniform on
`[0, 2]`, `W* = {0, 1}` and the highest-wage equilibrium `w* = 1` is a constrained Pareto
optimum, while the Pareto-dominated equilibrium `w* = 0` is not. -/
theorem proposition_13_B_2_instance :
    IsConstrainedPO (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) 1 ∧
      ¬ IsConstrainedPO (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) 0 := by
  have hreg := akerlof_regular (α := 1 / 4) (by norm_num) (by norm_num)
  have hW := example_13_B_1_lowα (α := 1 / 4) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) := by rw [hW]; simp
  refine ⟨proposition_13_B_2 hreg ⟨h1, fun x hx => ?_⟩, ?_⟩
  · rw [hW] at hx; rcases hx with rfl | rfl <;> norm_num
  · refine dominated_not_constrainedPO hreg.dist hreg.meas h1
      (measure_acceptSet_pos hreg.dist hreg.dens hreg.cont (by simp [akerlofR])) one_pos
      ⟨0, ⟨le_rfl, zero_le_two⟩, by simp [akerlofR]⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.C.4: signaling with a continuum of types

MWG, Exercise 13.C.4, p. 475. Types are distributed on `[θ̲, θ̄]` (`0 < θ̲`) with a positive
density; education costs `c(e, θ) = e²/θ`; `r = 0`. The exercise asks for "the (unique)
perfect Bayesian equilibrium".

As in Section 13.C the competing firms pay the expected productivity under their beliefs
(`bertrand_wage`), so a PBE is described by the education strategy `e*(θ)` and the wage
schedule `w(e)`, the mean of the firms' belief after `e` (`IsPBEC4`): every wage lies in
`[θ̲, θ̄]` (off the path any such mean is the mean of some belief), each type's education is
optimal, and on the path the wage is the conditional mean of the types choosing `e`, or, when
these have probability zero, the mean of a belief concentrated on them.

* `exercise_13_C_4_separating`: `e*(θ) = √((θ² - θ̲²)/2)` with `w(e) = min(√(2e² + θ̲²), θ̄)` is
  a separating PBE.
* `exercise_13_C_4_pooling`: everybody choosing `e = 0`, paid `E[θ]`, with wage `θ̲` after any
  `e > 0`, is also a PBE. The PBE is not unique (`exercise_13_C_4_not_unique`, instance
  `exercise_13_C_4_instance` with types uniform on `[1, 2]`).
* Corrected statement, `exercise_13_C_4_unique_separating`: every separating PBE (`e*`
  injective) has `e*(θ) = √((θ² - θ̲²)/2)` and wage `θ` for type `θ`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.C.4** (MWG, p. 475). A pure strategy PBE of the continuum-of-types signaling
game with cost `e²/θ`, in reduced form: the education strategy `eS` and the wage schedule `w`
(the mean of the firms' belief). -/
def IsPBEC4 (μ : Measure ℝ) (θl θh : ℝ) (eS w : ℝ → ℝ) : Prop :=
  (∀ θ ∈ Set.Icc θl θh, 0 ≤ eS θ) ∧ (∀ e, 0 ≤ e → θl ≤ w e ∧ w e ≤ θh) ∧
    (∀ θ ∈ Set.Icc θl θh, ∀ e, 0 ≤ e → w e - e ^ 2 / θ ≤ w (eS θ) - eS θ ^ 2 / θ) ∧
    ∀ e, (∃ θ ∈ Set.Icc θl θh, eS θ = e) →
      (0 < μ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e} →
        w e = condMean μ θl θh {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e}) ∧
      (μ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e} = 0 →
        ∃ θ₁ ∈ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e}, ∃ θ₂ ∈ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e},
          θ₁ ≤ w e ∧ w e ≤ θ₂)

/-- **Exercise 13.C.4**. The separating education strategy `√((θ² - θ̲²)/2)`. -/
noncomputable def sepEduc (θl : ℝ) (θ : ℝ) : ℝ := Real.sqrt ((θ ^ 2 - θl ^ 2) / 2)

/-- **Exercise 13.C.4**. The separating wage schedule `min(√(2e² + θ̲²), θ̄)`. -/
noncomputable def sepWage (θl θh : ℝ) (e : ℝ) : ℝ := min (Real.sqrt (2 * e ^ 2 + θl ^ 2)) θh

theorem sepEduc_sq {θl θ : ℝ} (h0 : 0 ≤ θl) (h : θl ≤ θ) :
    sepEduc θl θ ^ 2 = (θ ^ 2 - θl ^ 2) / 2 :=
  Real.sq_sqrt (by nlinarith)

theorem sepWage_sepEduc {θl θh θ : ℝ} (h0 : 0 ≤ θl) (h : θ ∈ Set.Icc θl θh) :
    sepWage θl θh (sepEduc θl θ) = θ := by
  unfold sepWage
  rw [sepEduc_sq h0 h.1, show 2 * ((θ ^ 2 - θl ^ 2) / 2) + θl ^ 2 = θ ^ 2 by ring,
    Real.sqrt_sq (h0.trans h.1)]
  exact min_eq_left h.2

theorem sepEduc_injOn {θl θh : ℝ} (h0 : 0 ≤ θl) : Set.InjOn (sepEduc θl) (Set.Icc θl θh) := by
  intro θ hθ θ' hθ' he
  have h1 := sepEduc_sq h0 hθ.1
  have h2 := sepEduc_sq h0 hθ'.1
  rw [he] at h1
  nlinarith [hθ.1, hθ'.1]

/-- **Exercise 13.C.4** (MWG, p. 475). The separating PBE. -/
theorem exercise_13_C_4_separating {μ : Measure ℝ} {θl θh : ℝ} (hden : HasPosDensity μ θl θh)
    (hθl : 0 < θl) (hlt : θl < θh) :
    IsPBEC4 μ θl θh (sepEduc θl) (sepWage θl θh) := by
  refine ⟨fun θ _ => Real.sqrt_nonneg _, fun e _ => ⟨?_, min_le_right _ _⟩, ?_, ?_⟩
  · refine le_min ?_ hlt.le
    calc θl = Real.sqrt (θl ^ 2) := (Real.sqrt_sq hθl.le).symm
      _ ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg e])
  · intro θ hθ e he
    have hθ0 : 0 < θ := hθl.trans_le hθ.1
    rw [sepWage_sepEduc hθl.le hθ, sepEduc_sq hθl.le hθ.1]
    set v := sepWage θl θh e
    have hv2 : v ^ 2 ≤ 2 * e ^ 2 + θl ^ 2 := by
      have hv0 : 0 ≤ v := le_min (Real.sqrt_nonneg _) (hθl.le.trans hlt.le)
      have hvs : v ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) := min_le_left _ _
      calc v ^ 2 ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) ^ 2 := pow_le_pow_left₀ hv0 hvs 2
        _ = 2 * e ^ 2 + θl ^ 2 := Real.sq_sqrt (by positivity)
    have hkey : v - e ^ 2 / θ ≤ θ - (θ ^ 2 - θl ^ 2) / 2 / θ := by
      rw [← sub_nonneg]
      have : θ - (θ ^ 2 - θl ^ 2) / 2 / θ - (v - e ^ 2 / θ) =
          ((θ - v) ^ 2 + (2 * e ^ 2 + θl ^ 2 - v ^ 2)) / (2 * θ) := by
        field_simp; ring
      rw [this]
      exact div_nonneg (by nlinarith [sq_nonneg (θ - v)]) (by linarith)
    exact hkey
  · rintro e ⟨θ0, hθ0, rfl⟩
    have hP : {θ | θ ∈ Set.Icc θl θh ∧ sepEduc θl θ = sepEduc θl θ0} = {θ0} := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hθ, he⟩; exact sepEduc_injOn hθl.le hθ hθ0 he
      · rintro rfl; exact ⟨hθ0, rfl⟩
    rw [hP, hden.noAtom θ0]
    refine ⟨fun h => absurd h (lt_irrefl _), fun _ => ⟨θ0, rfl, θ0, rfl, ?_⟩⟩
    rw [sepWage_sepEduc hθl.le hθ0]
    exact ⟨le_rfl, le_rfl⟩

/-- **Exercise 13.C.4**. The pooling wage schedule: `E[θ]` at `e = 0`, `θ̲` after any `e ≠ 0`. -/
noncomputable def poolWage (μ : Measure ℝ) (θl : ℝ) (e : ℝ) : ℝ := if e = 0 then meanType μ else θl

/-- **Exercise 13.C.4** (MWG, p. 475). Everybody choosing `e = 0` is also a PBE: firms pay
`E[θ]` at `e = 0` and believe any `e > 0` comes from type `θ̲`. -/
theorem exercise_13_C_4_pooling {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (hθl : 0 < θl) : IsPBEC4 μ θl θh (fun _ => 0) (poolWage μ θl) := by
  have hm := hd.meanType_mem
  refine ⟨fun _ _ => le_rfl, fun e _ => ?_, fun θ hθ e he => ?_, ?_⟩
  · unfold poolWage; split_ifs
    · exact hm
    · exact ⟨le_rfl, hd.lt.le⟩
  · have hθ0 : 0 < θ := hθl.trans_le hθ.1
    simp only [poolWage, ↓reduceIte]
    split_ifs with he0
    · subst he0; simp
    · have : 0 ≤ e ^ 2 / θ := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
      linarith [hm.1]
  · rintro e ⟨θ0, hθ0, rfl⟩
    have hP : {θ | θ ∈ Set.Icc θl θh ∧ (fun _ : ℝ => (0 : ℝ)) θ = (fun _ : ℝ => (0 : ℝ)) θ0} =
        Set.Icc θl θh := by
      ext θ; simp
    rw [hP]
    refine ⟨fun _ => ?_, fun _ => ⟨θl, ⟨le_rfl, hd.lt.le⟩, θh, ⟨hd.lt.le, le_rfl⟩, ?_⟩⟩
    · simp only [poolWage, ↓reduceIte]
      exact (condMean_of_superset hd subset_rfl).symm
    · simp only [poolWage, ↓reduceIte]; exact hm

/-- **Exercise 13.C.4** (MWG, p. 475). The PBE is not unique: the separating and the pooling
PBE differ (the highest type's education). -/
theorem exercise_13_C_4_not_unique {θl θh : ℝ} (hθl : 0 < θl) (hlt : θl < θh) :
    sepEduc θl θh ≠ 0 := by
  intro h
  have := sepEduc_sq hθl.le hlt.le
  rw [h] at this
  nlinarith

/-- A function on `[a, b]` with `|f x - f y| ≤ (x - y)²` is constant. -/
theorem eq_of_sq_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ (x - y) ^ 2) : f b = f a := by
  have key : ∀ n : ℕ, 0 < n → |f b - f a| ≤ (b - a) ^ 2 / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (b - a) / n with hhdef
    have hh : 0 ≤ h := div_nonneg (by linarith) hn'.le
    have hnh : (n : ℝ) * h = b - a := by rw [hhdef]; field_simp
    have ind : ∀ k : ℕ, k ≤ n → |f (a + k * h) - f a| ≤ k * h ^ 2 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
        have ih' := ih (Nat.le_of_succ_le hk)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hmem1 : a + ((k : ℝ) + 1) * h ∈ Set.Icc a b :=
          ⟨by nlinarith, by nlinarith⟩
        have hmem2 : a + (k : ℝ) * h ∈ Set.Icc a b := ⟨by nlinarith, by nlinarith⟩
        have hstep := hf _ hmem1 _ hmem2
        rw [show a + ((k : ℝ) + 1) * h - (a + k * h) = h by ring] at hstep
        push_cast
        calc |f (a + ((k : ℝ) + 1) * h) - f a|
            ≤ |f (a + ((k : ℝ) + 1) * h) - f (a + k * h)| + |f (a + k * h) - f a| :=
              abs_sub_le _ _ _
          _ ≤ h ^ 2 + k * h ^ 2 := add_le_add hstep ih'
          _ = ((k : ℝ) + 1) * h ^ 2 := by ring
    have := ind n le_rfl
    rw [hnh, show a + (b - a) = b by ring] at this
    calc |f b - f a| ≤ n * h ^ 2 := this
      _ = (b - a) ^ 2 / n := by rw [hhdef]; field_simp
  by_contra hne
  have hd : 0 < |f b - f a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) ^ 2 / |f b - f a|)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have h1 := key n (by exact_mod_cast hn0)
  rw [div_lt_iff₀ hd] at hn
  rw [le_div_iff₀ hn0] at h1
  linarith

/-- **Exercise 13.C.4** (MWG, p. 475), corrected statement: every separating PBE (`e*` one-to-one
on `[θ̲, θ̄]`) has `e*(θ) = √((θ² - θ̲²)/2)`, and type `θ` is paid `θ`. -/
theorem exercise_13_C_4_unique_separating {μ : Measure ℝ} {θl θh : ℝ}
    (hden : HasPosDensity μ θl θh) (hθl : 0 < θl) {eS w : ℝ → ℝ} (h : IsPBEC4 μ θl θh eS w)
    (hinj : Set.InjOn eS (Set.Icc θl θh)) :
    ∀ θ ∈ Set.Icc θl θh, eS θ = sepEduc θl θ ∧ w (eS θ) = θ := by
  obtain ⟨hpos, hw, hic, hbayes⟩ := h
  -- each type is paid her productivity
  have hpay : ∀ θ ∈ Set.Icc θl θh, w (eS θ) = θ := by
    intro θ hθ
    have hP : {θ' | θ' ∈ Set.Icc θl θh ∧ eS θ' = eS θ} = {θ} := by
      ext θ'
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hθ', he⟩; exact hinj hθ' hθ he
      · rintro rfl; exact ⟨hθ, rfl⟩
    obtain ⟨θ₁, h₁, θ₂, h₂, hle1, hle2⟩ := (hbayes (eS θ) ⟨θ, hθ, rfl⟩).2
      (by rw [hP]; exact hden.noAtom θ)
    rw [hP] at h₁ h₂
    rw [Set.mem_singleton_iff] at h₁ h₂
    subst h₁ h₂
    exact le_antisymm hle2 hle1
  -- incentive compatibility in terms of `E(θ) = e*(θ)²`
  have hIC : ∀ θ ∈ Set.Icc θl θh, ∀ θ' ∈ Set.Icc θl θh,
      eS θ ^ 2 - eS θ' ^ 2 ≤ θ * (θ - θ') := by
    intro θ hθ θ' hθ'
    have hθ0 : 0 < θ := hθl.trans_le hθ.1
    have := hic θ hθ (eS θ') (hpos θ' hθ')
    rw [hpay θ hθ, hpay θ' hθ'] at this
    have h1 : eS θ' ^ 2 / θ * θ = eS θ' ^ 2 := div_mul_cancel₀ _ hθ0.ne'
    have h2 : eS θ ^ 2 / θ * θ = eS θ ^ 2 := div_mul_cancel₀ _ hθ0.ne'
    nlinarith
  -- `D(θ) = E(θ) - θ²/2` is constant
  set D : ℝ → ℝ := fun θ => eS θ ^ 2 - θ ^ 2 / 2 with hD
  have hDb : ∀ x ∈ Set.Icc θl θh, ∀ y ∈ Set.Icc θl θh, |D x - D y| ≤ (x - y) ^ 2 := by
    intro x hx y hy
    have h1 := hIC x hx y hy
    have h2 := hIC y hy x hx
    rw [abs_le]
    simp only [hD]
    constructor <;> nlinarith [sq_nonneg (x - y)]
  -- the lowest type does not signal
  have hlow : eS θl = 0 := by
    have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, (hw 0 le_rfl).1.trans (hw 0 le_rfl).2⟩
    have := hic θl hl 0 le_rfl
    rw [hpay θl hl] at this
    have hw0 := (hw 0 le_rfl).1
    have hq : 0 ≤ eS θl ^ 2 / θl := by positivity
    have hz : eS θl ^ 2 / θl ≤ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
        sub_zero] at this
      linarith
    have : eS θl ^ 2 = 0 := by
      have := le_antisymm hz hq
      rwa [div_eq_zero_iff, or_iff_left hθl.ne'] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  intro θ hθ
  refine ⟨?_, hpay θ hθ⟩
  have hc : D θ = D θl := eq_of_sq_bound hθ.1 fun x hx y hy =>
    hDb x ⟨hx.1, hx.2.trans hθ.2⟩ y ⟨hy.1, hy.2.trans hθ.2⟩
  simp only [hD, hlow] at hc
  have hsq : eS θ ^ 2 = (θ ^ 2 - θl ^ 2) / 2 := by linarith
  unfold sepEduc
  rw [← hsq, Real.sqrt_sq (hpos θ hθ)]

/-- **Exercise 13.C.4**, an instance: with types uniform on `[1, 2]` both the separating and the
pooling PBE exist, so "the (unique) PBE" is false. -/
theorem exercise_13_C_4_instance :
    IsPBEC4 (unifMeas 1 2) 1 2 (sepEduc 1) (sepWage 1 2) ∧
      IsPBEC4 (unifMeas 1 2) 1 2 (fun _ => 0) (poolWage (unifMeas 1 2) 1) ∧
      sepEduc 1 2 ≠ 0 :=
  ⟨exercise_13_C_4_separating (unifMeas_density (by norm_num)) one_pos (by norm_num),
    exercise_13_C_4_pooling (unifMeas_typeDist zero_le_one (by norm_num)) one_pos,
    exercise_13_C_4_not_unique one_pos (by norm_num)⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 13.B.1-13.B.3

MWG, Section 13.B, end-of-chapter exercises, p. 473.

* **Exercise 13.B.1** (the diagram in `θ̂`). In the model with positive density and `r`
  continuous and strictly increasing (`MonoModel`, no `r(θ) ≤ θ` needed):
  `exercise_13_B_1` describes the whole set `W*`: an equilibrium wage is either a no-employment
  wage `w = E[θ] < r(θ̲)`, or `w = r(θ̲) = θ̲` (Figure 13.B.2), or `w = r(θ̂)` for a marginal type
  `θ̂ ∈ (θ̲, θ̄)` with `r(θ̂) = E[θ | θ ≤ θ̂]` (a crossing of the two curves of the diagram;
  then `Θ* ∩ [θ̲, θ̄] = [θ̲, θ̂]`), or the all-employed wage `w = E[θ] ≥ r(θ̄)`.
  `exercise_13_B_1_full`: an all-employed equilibrium exists iff `r(θ̄) ≤ E[θ]`.
  `exercise_13_B_1_po`: the Pareto optimal allocation employs `{θ : r(θ) ≤ θ}` (the types where
  the curve `r(θ̂)` lies below the 45-degree line `θ̂`).
  Departure: the book allows `r` "otherwise quite arbitrary". The reading of crossings as
  equilibria needs `Θ(r(θ̂)) ∩ [θ̲, θ̄] = [θ̲, θ̂]` (`exercise_13_B_1_cutoff`, valid for any
  measurable `r`), which holds for increasing `r`; `exercise_13_B_1_nonmono` shows a crossing that
  is not an equilibrium for the continuous decreasing `r(θ) = 1 - θ`.
* **Exercise 13.B.2** (`exercise_13_B_2`): with `r(θ) < θ` below `θ̂` and `r(θ) > θ` above, every
  competitive equilibrium has aggregate surplus strictly below the optimum.
* **Exercise 13.B.3** (positive selection, `AntiModel`): (a) `exercise_13_B_3a`; (b)
  `exercise_13_B_3b` (as printed, `r(θ) > θ` for all `θ`: the unique equilibrium has no
  employment and is efficient; `exercise_13_B_3b_lt` proves the reverse reading `r(θ) < θ`:
  the unique equilibrium employs everybody and is efficient); (c) `exercise_13_B_3c` (with
  `θ̂ ∈ (θ̲, θ̄)`): every equilibrium
  with positive employment employs every type the optimum employs and, with positive probability,
  types that should not work. `exercise_13_B_3c_counterexample`: with `θ̂ = θ̲` the claim fails.
-/

namespace MWG.AdverseSelection

open MeasureTheory Filter Topology

/-- Two sets with the same trace on `[θ̲, θ̄]` are almost everywhere equal. -/
theorem exB_ae_eq_of_inter {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S T : Set ℝ}
    (h : S ∩ Set.Icc θl θh = T ∩ Set.Icc θl θh) : S =ᵐ[μ] T := by
  refine ae_eq_set.2 ⟨measure_mono_null (t := (Set.Icc θl θh)ᶜ) (fun θ hθ hθI => ?_) hd.supp,
    measure_mono_null (t := (Set.Icc θl θh)ᶜ) (fun θ hθ hθI => ?_) hd.supp⟩
  · exact hθ.2 (h ▸ ⟨hθ.1, hθI⟩ : θ ∈ T ∩ Set.Icc θl θh).1
  · exact hθ.2 (h.symm ▸ ⟨hθ.1, hθI⟩ : θ ∈ S ∩ Set.Icc θl θh).1

/-- `E[θ | θ ∈ S]` only depends on `S ∩ [θ̲, θ̄]`. -/
theorem exB_condMean_congr {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S T : Set ℝ}
    (h : S ∩ Set.Icc θl θh = T ∩ Set.Icc θl θh) :
    condMean μ θl θh S = condMean μ θl θh T := by
  have hST := exB_ae_eq_of_inter hd h
  unfold condMean
  rw [measure_congr hST, setIntegral_congr_set hST, h]

/-- The conditional mean of the empty set is `E[θ]` (the book's convention, p. 439). -/
theorem exB_condMean_empty (μ : Measure ℝ) (θl θh : ℝ) :
    condMean μ θl θh ∅ = meanType μ := by
  simp [condMean]

/-- A conditional mean over a set of types all at least `c` is at least `c`. -/
theorem exB_le_condMean {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S : Set ℝ}
    (hS : MeasurableSet S) (hpos : 0 < μ S) {c : ℝ} (hc : ∀ θ ∈ S, c ≤ θ) :
    c ≤ condMean μ θl θh S := by
  have := hd.prob
  have hM : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  simp only [condMean, hpos, ↓reduceIte]
  rw [le_div_iff₀ hM]
  have h := setIntegral_mono_on (integrable_const c).integrableOn hd.integrable_id.integrableOn
    hS hc
  rw [setIntegral_const, smul_eq_mul, Measure.real] at h
  linarith [mul_comm c (μ S).toReal]

/-- A continuous function that is positive to the left of `x` and negative to the right vanishes
at `x`. -/
theorem exB_eq_zero_of_cross {f : ℝ → ℝ} {a x b : ℝ} (hax : a < x) (hxb : x < b)
    (hf : ContinuousAt f x) (hl : ∀ y ∈ Set.Ioo a x, 0 < f y)
    (hr : ∀ y ∈ Set.Ioo x b, f y < 0) : f x = 0 := by
  have h1 : 0 ≤ f x := by
    have ht : Tendsto f (𝓝[<] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hax] with y hy using (hl y hy).le
  have h2 : f x ≤ 0 := by
    have ht : Tendsto f (𝓝[>] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hxb] with y hy using (hr y hy).le
  linarith

/-- Near a point where `r < w`, `r < w`. -/
theorem exB_lt_near {r : ℝ → ℝ} {x w : ℝ} (hc : ContinuousAt r x) (h : r x < w) :
    ∃ δ > 0, ∀ y, |y - x| < δ → r y < w := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds h))
  exact ⟨δ, hδ, fun y hy => hball (by rwa [Real.dist_eq])⟩

/-- Near a point where `r > w`, `r > w`. -/
theorem exB_gt_near {r : ℝ → ℝ} {x w : ℝ} (hc : ContinuousAt r x) (h : w < r x) :
    ∃ δ > 0, ∀ y, |y - x| < δ → w < r y := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (lt_mem_nhds h))
  exact ⟨δ, hδ, fun y hy => hball (by rwa [Real.dist_eq])⟩

/-- A function continuous on `[θ̲, θ̄]` is integrable. -/
theorem exB_integrable {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) (hc : ContinuousOn r (Set.Icc θl θh)) : Integrable r μ := by
  have := hd.prob
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine Integrable.of_bound (C := C) hr.aestronglyMeasurable ?_
  filter_upwards [hd.ae_mem] with θ hθ using hC θ hθ

/-- **Exercise 13.B.1** (MWG, p. 473). For any `r` (measurable or not), if the types in
`[θ̲, θ̄]` accepting the wage `r(θ̂)` are exactly `[θ̲, θ̂]`, then `r(θ̂)` is a competitive
equilibrium wage iff `r(θ̂) = E[θ | θ ≤ θ̂]`: a crossing of the curves `r(θ̂)` and
`E[θ | θ ≤ θ̂]` of the diagram. -/
theorem exercise_13_B_1_cutoff {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} {θhat : ℝ} (hθ : θhat ≤ θh)
    (hcut : acceptSet r (r θhat) ∩ Set.Icc θl θh = Set.Icc θl θhat) :
    r θhat ∈ eqWages μ θl θh r ↔ r θhat = condMean μ θl θh (Set.Iic θhat) := by
  rw [mem_eqWages_iff, exB_condMean_congr hd (hcut.trans (Iic_inter_Icc_of_le hθ).symm)]

/-- In the `MonoModel`, the types accepting `r(θ̂)` are `[θ̲, θ̂]`. -/
theorem MonoModel.acceptSet_cutoff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {θhat : ℝ} (hθ : θhat ∈ Set.Icc θl θh) :
    acceptSet r (r θhat) ∩ Set.Icc θl θh = Set.Icc θl θhat := by
  ext θ
  simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, (h.mono.le_iff_le ⟨h2, h3⟩ hθ).1 h1⟩
  · rintro ⟨h2, h3⟩
    exact ⟨(h.mono.le_iff_le ⟨h2, h3.trans hθ.2⟩ hθ).2 h3, h2, h3.trans hθ.2⟩

/-- **Exercise 13.B.1** (MWG, p. 473). In the model with positive density and `r` continuous
and strictly increasing (`r(θ) ≤ θ` is not needed), the competitive equilibrium wages are
exactly: a no-employment wage `w = E[θ] < r(θ̲)` (nobody in `[θ̲, θ̄]` accepts, with the book's
convention `E[θ | ∅] = E[θ]`); `w = r(θ̲)` when `r(θ̲) = θ̲` (Figure 13.B.2); `w = r(θ̂)` for a
marginal type `θ̂ ∈ (θ̲, θ̄)` at which `r(θ̂) = E[θ | θ ≤ θ̂]` (a crossing in the diagram); or
the all-employed wage `w = E[θ] ≥ r(θ̄)`. -/
theorem exercise_13_B_1 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : MonoModel μ θl θh r)
    (w : ℝ) :
    w ∈ eqWages μ θl θh r ↔
      (w < r θl ∧ w = meanType μ) ∨ (w = r θl ∧ r θl = θl) ∨
        (∃ θhat ∈ Set.Ioo θl θh, w = r θhat ∧ r θhat = condMean μ θl θh (Set.Iic θhat)) ∨
          (r θh ≤ w ∧ w = meanType μ) := by
  have hd := h.dist
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have hlow : ∀ v, v < r θl → condMean μ θl θh (acceptSet r v) = meanType μ := fun v hv => by
    rw [exB_condMean_congr hd (T := ∅) (by
      rw [acceptSet_inter_eq_empty h.mono.monotoneOn hv, Set.empty_inter]),
      exB_condMean_empty]
  have hfull : ∀ v, r θh ≤ v → Set.Icc θl θh ⊆ acceptSet r v := fun v hv θ hθ =>
    (h.mono.monotoneOn hθ hh hθ.2).trans hv
  have hrlh : r θl < r θh := h.mono hl hh hd.lt
  constructor
  · intro hw
    rcases lt_trichotomy w (r θl) with hlt | heq | hgt
    · exact Or.inl ⟨hlt, (mem_eqWages_iff.1 hw).trans (hlow w hlt)⟩
    · refine Or.inr (Or.inl ⟨heq, ?_⟩)
      rw [heq] at hw
      exact (mem_eqWages_rl_iff hd h.mono h.dens).1 hw
    · rcases lt_or_ge w (r θh) with hwh | hwh
      · obtain ⟨θhat, hθI, hθw⟩ := intermediate_value_Icc hd.lt.le h.cont ⟨hgt.le, hwh.le⟩
        have hθl : θl < θhat := lt_of_le_of_ne hθI.1 (by rintro rfl; exact hgt.ne' hθw.symm)
        have hθh : θhat < θh := lt_of_le_of_ne hθI.2 (by rintro rfl; exact hwh.ne hθw.symm)
        refine Or.inr (Or.inr (Or.inl ⟨θhat, ⟨hθl, hθh⟩, hθw.symm, ?_⟩))
        rw [← exercise_13_B_1_cutoff hd hθI.2 (h.acceptSet_cutoff hθI), hθw]
        exact hw
      · exact Or.inr (Or.inr (Or.inr ⟨hwh, (mem_eqWages_iff.1 hw).trans
          (condMean_of_superset hd (hfull w hwh))⟩))
  · rintro (⟨hlt, hwE⟩ | ⟨heq, hrl⟩ | ⟨θhat, hθ, hwθ, hcross⟩ | ⟨hwh, hwE⟩)
    · exact mem_eqWages_iff.2 (hwE.trans (hlow w hlt).symm)
    · rw [heq]; exact (mem_eqWages_rl_iff hd h.mono h.dens).2 hrl
    · rw [hwθ]
      exact (exercise_13_B_1_cutoff hd hθ.2.le
        (h.acceptSet_cutoff ⟨hθ.1.le, hθ.2.le⟩)).2 hcross
    · exact mem_eqWages_iff.2 (hwE.trans (condMean_of_superset hd (hfull w hwh)).symm)

/-- **Exercise 13.B.1** (MWG, p. 473). In the `MonoModel`, a competitive equilibrium in which
every type in `[θ̲, θ̄]` is employed exists iff `r(θ̄) ≤ E[θ]`; its wage is then `E[θ]`. -/
theorem exercise_13_B_1_full {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) :
    ((∃ w ∈ eqWages μ θl θh r, Set.Icc θl θh ⊆ acceptSet r w) ↔ r θh ≤ meanType μ) ∧
      ∀ w ∈ eqWages μ θl θh r, Set.Icc θl θh ⊆ acceptSet r w → w = meanType μ := by
  have hd := h.dist
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have huniq : ∀ w ∈ eqWages μ θl θh r, Set.Icc θl θh ⊆ acceptSet r w → w = meanType μ :=
    fun w hw hsub => (mem_eqWages_iff.1 hw).trans (condMean_of_superset hd hsub)
  refine ⟨⟨fun ⟨w, hw, hsub⟩ => ?_, fun hE => ⟨meanType μ, mean_mem_eqWages hd ?_, ?_⟩⟩, huniq⟩
  · have := hsub hh
    rw [← huniq w hw hsub]
    exact this
  all_goals exact fun θ hθ => (h.mono.monotoneOn hθ hh hθ.2).trans hE

/-- **Exercise 13.B.1** (MWG, pp. 438, 473). The Pareto optimal allocation employs exactly the
types with `r(θ) ≤ θ`, i.e. those at which the curve `r(θ̂)` lies on or below the 45-degree line
`θ̂`: this employment rule maximizes aggregate surplus (13.B.1). -/
theorem exercise_13_B_1_po {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {N : ℝ}
    (hN : 0 ≤ N) {r I : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r μ)
    (hIm : Measurable I) (hI : ∀ θ, I θ = 0 ∨ I θ = 1) :
    optEmployment r = {θ | r θ ≤ θ}.indicator (fun _ => 1) ∧
      aggSurplus μ N r I ≤ aggSurplus μ N r (optEmployment r) :=
  ⟨rfl, aggSurplus_le_opt hd hN hr hrint hIm hI⟩

/-- **Exercise 13.B.1, departure** (MWG, p. 473). For a non-monotone `r` a crossing of the two
curves need not be an equilibrium: with types uniform on `[0, 2]` and the continuous
`r(θ) = 1 - θ`, at `θ̂ = 2/3` we have `r(θ̂) = 1/3 = E[θ | θ ≤ θ̂]`, but `1/3` is not an
equilibrium wage (the types accepting it are `θ ≥ 2/3`). -/
theorem exercise_13_B_1_nonmono :
    (1 / 3 : ℝ) = 1 - 2 / 3 ∧
      (1 / 3 : ℝ) = condMean (unifMeas 0 2) 0 2 (Set.Iic (2 / 3)) ∧
      (1 / 3 : ℝ) ∉ eqWages (unifMeas 0 2) 0 2 (fun θ => 1 - θ) := by
  have hd : TypeDist (unifMeas 0 2) 0 2 := unifMeas_typeDist le_rfl two_pos
  have := hd.prob
  refine ⟨by norm_num, ?_, ?_⟩
  · have hF := unifMeas_Iic (a := 0) (b := 2) (c := 2 / 3) two_pos (by norm_num) (by norm_num)
    have hI := unifMeas_setIntegral_Iic (a := 0) (b := 2) (c := 2 / 3) two_pos (by norm_num)
      (by norm_num)
    have hpos : 0 < unifMeas 0 2 (Set.Iic (2 / 3)) := by rw [hF]; norm_num
    simp only [condMean, hpos, ↓reduceIte]
    rw [hI, hF, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  · intro hw
    rw [mem_eqWages_iff] at hw
    have hset : acceptSet (fun θ : ℝ => 1 - θ) (1 / 3) = Set.Ici (2 / 3) := by
      ext θ; simp only [acceptSet, Set.mem_ofPred_eq, Set.mem_Ici]
      constructor <;> intro <;> linarith
    have hpos : 0 < unifMeas 0 2 (Set.Ici (2 / 3)) :=
      ((unifMeas_density two_pos).pos (2 / 3) 2 (by norm_num) (by norm_num) le_rfl).trans_le
        (measure_mono Set.Icc_subset_Ici_self)
    have := exB_le_condMean hd measurableSet_Ici hpos (c := 2 / 3) fun θ hθ => hθ
    rw [hset] at hw
    linarith

/-- **Exercise 13.B.2** (MWG, p. 473). Let `r` be continuous and strictly increasing, `F` with a
positive density, and `θ̂ ∈ (θ̲, θ̄)` with `r(θ) > θ` for `θ > θ̂` and `r(θ) < θ` for `θ < θ̂`
(within `[θ̲, θ̄]`). Then every competitive equilibrium is Pareto inefficient: the aggregate
surplus (13.B.1) of its employment rule `Θ*` is strictly below the optimum. -/
theorem exercise_13_B_2 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : MonoModel μ θl θh r)
    {θhat : ℝ} (hθ : θhat ∈ Set.Ioo θl θh) (hgt : ∀ θ ∈ Set.Icc θl θh, θhat < θ → θ < r θ)
    (hlt : ∀ θ ∈ Set.Icc θl θh, θ < θhat → r θ < θ) {N : ℝ} (hN : 0 < N) {w : ℝ}
    (hw : w ∈ eqWages μ θl θh r) :
    aggSurplus μ N r ((acceptSet r w).indicator fun _ => 1) <
      aggSurplus μ N r (optEmployment r) := by
  have hd := h.dist
  have := hd.prob
  have hθI : θhat ∈ Set.Icc θl θh := ⟨hθ.1.le, hθ.2.le⟩
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hca : ContinuousAt r θhat := h.cont.continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  have hfix : r θhat = θhat := by
    have := exB_eq_zero_of_cross (f := fun θ => θ - r θ) hθ.1 hθ.2
      (continuousAt_id.sub hca)
      (fun y hy => by linarith [hlt y ⟨hy.1.le, hy.2.le.trans hθ.2.le⟩ hy.2])
      (fun y hy => by linarith [hgt y ⟨hθ.1.le.trans hy.1.le, hy.2.le⟩ hy.1])
    linarith
  set I : ℝ → ℝ := (acceptSet r w).indicator fun _ => 1 with hIdef
  have hI01 : ∀ θ, I θ = 0 ∨ I θ = 1 := fun θ => by
    by_cases hm : θ ∈ acceptSet r w
    · exact Or.inr (Set.indicator_of_mem hm _)
    · exact Or.inl (Set.indicator_of_notMem hm _)
  refine aggSurplus_lt_opt hd hN h.meas (exB_integrable hd h.meas h.cont)
    (measurable_const.indicator (measurableSet_acceptSet h.meas w)) hI01 ?_
  rcases lt_trichotomy w θhat with hwl | hwe | hwg
  · -- too little employment: types just below `θ̂` stay home although `θ > r(θ)`
    obtain ⟨δ, hδ, hnear⟩ := exB_gt_near hca (hfix.symm ▸ hwl : w < r θhat)
    set a := max θl (θhat - δ / 2)
    have ha : a < θhat := max_lt hθ.1 (by linarith)
    refine (h.dens.pos a ((a + θhat) / 2) (le_max_left _ _) (by linarith)
      (by linarith [hθ.2])).trans_le (measure_mono fun y hy => ?_)
    have hyI : y ∈ Set.Icc θl θh :=
      ⟨(le_max_left _ _).trans hy.1, by linarith [hy.2, hθ.2]⟩
    have hyθ : y < θhat := by linarith [hy.2]
    have hry := hlt y hyI hyθ
    have hwy : w < r y := hnear y (by
      rw [abs_lt]; constructor <;> linarith [hy.1, le_max_right θl (θhat - δ / 2), hy.2])
    have hIy : I y = 0 := Set.indicator_of_notMem (s := acceptSet r w)
      (fun hm : y ∈ acceptSet r w => absurd (show r y ≤ w from hm) (not_le.2 hwy)) _
    simp only [Set.mem_ofPred_eq, hIy, zero_mul, sub_zero, one_mul, zero_add,
      max_eq_left hry.le]
    exact hry
  · -- the marginal type is `θ̂` itself: then the firm loses money
    exfalso
    have hrl : r θl < w := hwe ▸ hfix ▸ h.mono hl hθI hθ.1
    have hpos := measure_acceptSet_pos hd h.dens h.cont hrl
    have h0 := (mem_eqWages_iff_profit hd h.meas hpos).1 hw
    have hneg : firmProfit μ r w < 0 := by
      refine firmProfit_neg_of_ae_lt hd h.meas hpos ?_
      filter_upwards [hd.ae_mem, measure_eq_zero_iff_ae_notMem.1 (h.dens.noAtom θhat)]
        with θ hθI' hne hacc
      have hle : θ ≤ θhat := (h.mono.le_iff_le hθI' hθI).1 (by rw [hfix, ← hwe]; exact hacc)
      exact hwe ▸ lt_of_le_of_ne hle hne
    linarith
  · -- too much employment: types just above `θ̂` work although `r(θ) > θ`
    obtain ⟨δ, hδ, hnear⟩ := exB_lt_near hca (hfix.symm ▸ hwg : r θhat < w)
    set b := min θh (θhat + δ / 2)
    have hb : θhat < b := lt_min hθ.2 (by linarith)
    refine (h.dens.pos ((θhat + b) / 2) b (by linarith [hθ.1]) (by linarith)
      (min_le_left _ _)).trans_le (measure_mono fun y hy => ?_)
    have hyI : y ∈ Set.Icc θl θh :=
      ⟨by linarith [hy.1, hθ.1], hy.2.trans (min_le_left _ _)⟩
    have hyθ : θhat < y := by linarith [hy.1]
    have hry := hgt y hyI hyθ
    have hwy : r y < w := hnear y (by
      rw [abs_lt]; constructor <;> linarith [hy.2, min_le_right θh (θhat + δ / 2), hy.1])
    have hIy : I y = 1 := Set.indicator_of_mem (s := acceptSet r w)
      (show y ∈ acceptSet r w from hwy.le) _
    simp only [Set.mem_ofPred_eq, hIy, one_mul, sub_self, zero_mul, add_zero,
      max_eq_right hry.le]
    exact hry

/-- The uniform distribution: `E[θ | θ ≤ c] = (a + c)/2` for `a < c ≤ b`. -/
theorem exB_unif_condMean_Iic {a b c : ℝ} (hab : a < b) (hac : a < c) (hcb : c ≤ b)
    (θl θh : ℝ) : condMean (unifMeas a b) θl θh (Set.Iic c) = (a + c) / 2 := by
  have hF := unifMeas_Iic hab hac.le hcb
  have hI := unifMeas_setIntegral_Iic hab hac.le hcb
  have hpos : 0 < unifMeas a b (Set.Iic c) := by
    rw [hF]; exact ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))
  simp only [condMean, hpos, ↓reduceIte]
  rw [hI, hF, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
  have h1 : b - a ≠ 0 := by linarith
  have h2 : c - a ≠ 0 := by linarith
  field_simp
  ring

/-- **Exercise 13.B.2**, instance (MWG, p. 473). Types uniform on `[1, 3]`, `r(θ) = 2θ - 2`
(`θ̂ = 2`): `w* = 4/3` (marginal type `5/3`) is a competitive equilibrium wage, and it is
inefficient. -/
theorem exercise_13_B_2_instance :
    (4 / 3 : ℝ) ∈ eqWages (unifMeas 1 3) 1 3 (fun θ => 2 * θ - 2) ∧
      aggSurplus (unifMeas 1 3) 1 (fun θ => 2 * θ - 2)
          ((acceptSet (fun θ => 2 * θ - 2) (4 / 3)).indicator fun _ => 1) <
        aggSurplus (unifMeas 1 3) 1 (fun θ => 2 * θ - 2) (optEmployment fun θ => 2 * θ - 2) := by
  have hM : MonoModel (unifMeas 1 3) 1 3 (fun θ => 2 * θ - 2) :=
    ⟨unifMeas_typeDist zero_le_one (by norm_num), unifMeas_density (by norm_num),
      (measurable_id.const_mul 2).sub_const 2, fun a _ b _ hab => by linarith,
      by fun_prop⟩
  have hw : (4 / 3 : ℝ) ∈ eqWages (unifMeas 1 3) 1 3 (fun θ => 2 * θ - 2) := by
    rw [mem_eqWages_iff]
    have hset : acceptSet (fun θ : ℝ => 2 * θ - 2) (4 / 3) = Set.Iic (5 / 3) := by
      ext θ; simp only [acceptSet, Set.mem_ofPred_eq, Set.mem_Iic]
      constructor <;> intro <;> linarith
    rw [hset, exB_unif_condMean_Iic (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  exact ⟨hw, exercise_13_B_2 hM (θhat := 2) ⟨by norm_num, by norm_num⟩
    (fun θ _ h => by linarith) (fun θ _ h => by linarith) one_pos hw⟩

/-- **Exercise 13.B.3** (MWG, p. 473). The positive selection model: positive density, `r`
measurable, continuous and strictly decreasing on `[θ̲, θ̄]`. -/
structure AntiModel (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Prop where
  dist : TypeDist μ θl θh
  dens : HasPosDensity μ θl θh
  meas : Measurable r
  anti : StrictAntiOn r (Set.Icc θl θh)
  cont : ContinuousOn r (Set.Icc θl θh)

/-- **Exercise 13.B.3(a)** (MWG, p. 473). With `r` strictly decreasing, at any wage the set of
types accepting employment is an upper set of `[θ̲, θ̄]` (the more capable workers work), and a
more capable worker has a strictly worse home option. -/
theorem exercise_13_B_3a {θl θh : ℝ} {r : ℝ → ℝ} (hanti : StrictAntiOn r (Set.Icc θl θh))
    (w : ℝ) {θ θ' : ℝ} (hθ : θ ∈ Set.Icc θl θh) (hθ' : θ' ∈ Set.Icc θl θh) (hle : θ ≤ θ') :
    (θ ∈ acceptSet r w → θ' ∈ acceptSet r w) ∧ (θ < θ' → r θ' < r θ) :=
  ⟨fun hacc => (hanti.antitoneOn hθ hθ' hle).trans hacc, fun hlt => hanti hθ hθ' hlt⟩

/-- **Exercise 13.B.3(b)** (MWG, p. 473), as printed: if `r(θ) > θ` for every type, the
competitive equilibrium is unique, `w* = E[θ]` with no type in `[θ̲, θ̄]` employed, and it is
Pareto efficient (its aggregate surplus is the optimum). -/
theorem exercise_13_B_3b {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : AntiModel μ θl θh r)
    (hgt : ∀ θ ∈ Set.Icc θl θh, θ < r θ) (N : ℝ) :
    eqWages μ θl θh r = {meanType μ} ∧
      acceptSet r (meanType μ) ∩ Set.Icc θl θh = ∅ ∧
      aggSurplus μ N r ((acceptSet r (meanType μ)).indicator fun _ => 1) =
        aggSurplus μ N r (optEmployment r) := by
  have hd := h.dist
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have hempty : acceptSet r (meanType μ) ∩ Set.Icc θl θh = ∅ := by
    ext θ
    simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hle hθ
    have h1 := h.anti.antitoneOn hθ hh hθ.2
    linarith [hgt θh hh, hd.meanType_mem.2]
  refine ⟨?_, hempty, ?_⟩
  · ext w
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hw
      rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
      · have hw' := mem_eqWages_iff.1 hw
        simp only [condMean, h0, lt_self_iff_false, ↓reduceIte] at hw'
        split_ifs at hw' with hne
        · obtain ⟨θ, hacc, hθ⟩ := hne
          have : r θ ≤ w := hacc
          linarith [hgt θ hθ, hθ.1]
        · exact hw'
      · have h0 := (mem_eqWages_iff_profit hd h.meas hpos).1 hw
        have hneg : firmProfit μ r w < 0 := by
          refine firmProfit_neg_of_ae_lt hd h.meas hpos ?_
          filter_upwards [hd.ae_mem] with θ hθ hacc
          exact (hgt θ hθ).trans_le hacc
        linarith
    · rintro rfl
      rw [mem_eqWages_iff, exB_condMean_congr hd (T := ∅) (by rw [hempty, Set.empty_inter]),
        exB_condMean_empty]
  · unfold aggSurplus
    refine integral_congr_ae ?_
    filter_upwards [hd.ae_mem] with θ hθ
    have h1 : θ ∉ acceptSet r (meanType μ) := fun hm =>
      (Set.eq_empty_iff_forall_notMem.1 hempty θ) ⟨hm, hθ⟩
    have h2 : θ ∉ {θ | r θ ≤ θ} := fun hm => absurd (hgt θ hθ) (not_lt.2 hm)
    simp only [Set.indicator_of_notMem h1, optEmployment, Set.indicator_of_notMem h2]

/-- In the positive selection model every wage above `r(θ̄)` attracts a set of types of positive
probability. -/
theorem AntiModel.measure_acceptSet_pos {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : AntiModel μ θl θh r) {w : ℝ} (hw : r θh < w) : 0 < μ (acceptSet r w) := by
  have hd := h.dist
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((h.cont θh hh).eventually (gt_mem_nhds hw))
  set a := max θl (θh - ε / 2)
  have ha : a < θh := max_lt hd.lt (by linarith)
  refine (h.dens.pos a θh (le_max_left _ _) ha le_rfl).trans_le (measure_mono fun y hy => ?_)
  have hyI : y ∈ Set.Icc θl θh := ⟨(le_max_left _ _).trans hy.1, hy.2⟩
  have hdist : Dist.dist y θh < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2, le_max_right θl (θh - ε / 2)]
  have hlt : r y < w := hball ⟨Metric.mem_ball.2 hdist, hyI⟩
  exact hlt.le

/-- **Exercise 13.B.3(b)** (MWG, p. 473), the reverse inequality (a possible intended reading):
if `r(θ) < θ` for every type, the competitive equilibrium is unique, `w* = E[θ]` with every
type employed, and it is Pareto efficient. -/
theorem exercise_13_B_3b_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : AntiModel μ θl θh r)
    (hlt : ∀ θ ∈ Set.Icc θl θh, r θ < θ) (N : ℝ) :
    eqWages μ θl θh r = {meanType μ} ∧ Set.Icc θl θh ⊆ acceptSet r (meanType μ) ∧
      aggSurplus μ N r ((acceptSet r (meanType μ)).indicator fun _ => 1) =
        aggSurplus μ N r (optEmployment r) := by
  have hd := h.dist
  have := hd.prob
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have hrl := hlt θl hl
  have hrhl : r θh < r θl := h.anti hl hh hd.lt
  have hrle : ∀ θ ∈ Set.Icc θl θh, r θ ≤ r θl := fun θ hθ => h.anti.antitoneOn hl hθ hθ.1
  have hfullOf : ∀ w, r θl ≤ w → Set.Icc θl θh ⊆ acceptSet r w := fun w hw θ hθ =>
    (hrle θ hθ).trans hw
  have hEm := hd.meanType_mem
  have hfull : Set.Icc θl θh ⊆ acceptSet r (meanType μ) := hfullOf _ (by linarith [hEm.1])
  refine ⟨?_, hfull, ?_⟩
  · ext w
    simp only [Set.mem_singleton_iff]
    refine ⟨fun hw => ?_, fun hw => hw ▸ mean_mem_eqWages hd hfull⟩
    rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
    · exfalso
      have hw' := mem_eqWages_iff.1 hw
      simp only [condMean, h0, lt_self_iff_false, ↓reduceIte] at hw'
      have hgt : r θh < w := by
        split_ifs at hw' with hne
        · linarith
        · linarith [hEm.1]
      exact (h.measure_acceptSet_pos hgt).ne' h0
    · by_cases hwl : r θl ≤ w
      · exact (mem_eqWages_iff.1 hw).trans (condMean_of_superset hd (hfullOf w hwl))
      · exfalso
        rw [not_le] at hwl
        have hP0 := (mem_eqWages_iff_profit hd h.meas hpos).1 hw
        have hrhw : r θh ≤ w := by
          by_contra hc
          rw [not_le] at hc
          refine hpos.ne' (measure_mono_null (t := (Set.Icc θl θh)ᶜ) (fun θ hθ hθI => ?_)
            hd.supp)
          have : r θ ≤ w := hθ
          linarith [h.anti.antitoneOn hθI hh hθI.2]
        obtain ⟨θt, hθt, hrt⟩ := intermediate_value_Icc' hd.lt.le h.cont ⟨hrhw, hwl.le⟩
        have hpos' : 0 < firmProfit μ r w := by
          rw [firmProfit_eq_setIntegral h.meas]
          refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet h.meas w) hpos
            (hd.ae_mem.mono fun θ hθ hacc => ?_)
            (hd.integrable_id.sub (integrable_const w)).integrableOn
          have hacc' : r θ ≤ r θt := hrt ▸ hacc
          have hθθ : θt ≤ θ := not_lt.1 fun hc => absurd hacc' (not_le.2 (h.anti hθ hθt hc))
          linarith [hlt θt hθt]
        linarith
  · unfold aggSurplus
    refine integral_congr_ae ?_
    filter_upwards [hd.ae_mem] with θ hθ
    have h2 : θ ∈ {θ | r θ ≤ θ} := (hlt θ hθ).le
    simp only [Set.indicator_of_mem (hfull hθ), optEmployment, Set.indicator_of_mem h2]

/-- **Exercise 13.B.3(c)** (MWG, p. 473). Positive selection with `θ̂ ∈ (θ̲, θ̄)`, `r(θ) < θ` for
`θ > θ̂` and `r(θ) > θ` for `θ < θ̂`. Every competitive equilibrium with positive employment has
too much employment: it employs every type the Pareto optimum employs (`r(θ) ≤ θ`) and, with
positive probability, types with `r(θ) > θ`. -/
theorem exercise_13_B_3c {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : AntiModel μ θl θh r)
    {θhat : ℝ} (hθ : θhat ∈ Set.Ioo θl θh) (hlt : ∀ θ ∈ Set.Icc θl θh, θhat < θ → r θ < θ)
    (hgt : ∀ θ ∈ Set.Icc θl θh, θ < θhat → θ < r θ) {w : ℝ} (hw : w ∈ eqWages μ θl θh r)
    (hpos : 0 < μ (acceptSet r w)) :
    {θ | θ ∈ Set.Icc θl θh ∧ r θ ≤ θ} ⊆ acceptSet r w ∧
      0 < μ (acceptSet r w ∩ {θ | θ < r θ}) := by
  have hd := h.dist
  have := hd.prob
  have hθI : θhat ∈ Set.Icc θl θh := ⟨hθ.1.le, hθ.2.le⟩
  have hca : ContinuousAt r θhat := h.cont.continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  have hfix : r θhat = θhat := by
    have := exB_eq_zero_of_cross (f := fun θ => r θ - θ) hθ.1 hθ.2
      (hca.sub continuousAt_id)
      (fun y hy => by linarith [hgt y ⟨hy.1.le, hy.2.le.trans hθ.2.le⟩ hy.2])
      (fun y hy => by linarith [hlt y ⟨hθ.1.le.trans hy.1.le, hy.2.le⟩ hy.1])
    linarith
  have h0 := (mem_eqWages_iff_profit hd h.meas hpos).1 hw
  -- a strictly positive profit contradicts equilibrium
  have hnotpos : ¬ ∀ᵐ θ ∂μ, θ ∈ acceptSet r w → w < θ := fun hae => by
    have : 0 < firmProfit μ r w := by
      rw [firmProfit_eq_setIntegral h.meas]
      exact setIntegral_pos_of_ae_pos (measurableSet_acceptSet h.meas w) hpos
        (hae.mono fun θ hθ hm => sub_pos.2 (hθ hm))
        (hd.integrable_id.sub (integrable_const w)).integrableOn
    linarith
  have hwθ : θhat ≤ w := by
    by_contra hcon
    rw [not_le] at hcon
    refine hnotpos (hd.ae_mem.mono fun θ hθ hacc => ?_)
    by_contra hθw
    rw [not_lt] at hθw
    have hθθ : θ ≤ θhat := hθw.trans hcon.le
    have : r θhat ≤ r θ := h.anti.antitoneOn hθ hθI hθθ
    have hacc' : r θ ≤ w := hacc
    linarith
  refine ⟨fun θ ⟨hθ, hrθ⟩ => ?_, ?_⟩
  · have hθθ : θhat ≤ θ := by
      by_contra hc; exact absurd hrθ (not_le.2 (hgt θ hθ (not_le.1 hc)))
    exact (h.anti.antitoneOn hθI hθ hθθ).trans (by rw [hfix]; exact hwθ)
  · rcases eq_or_lt_of_le hwθ with hwe | hwg
    · exfalso
      refine hnotpos ?_
      filter_upwards [hd.ae_mem, measure_eq_zero_iff_ae_notMem.1 (h.dens.noAtom θhat)]
        with θ hθ hne hacc
      have hacc' : r θ ≤ r θhat := by rw [hfix, hwe]; exact hacc
      have hle : θhat ≤ θ := not_lt.1 fun hlt => absurd hacc' (not_le.2 (h.anti hθ hθI hlt))
      exact hwe ▸ lt_of_le_of_ne hle (Ne.symm hne)
    · obtain ⟨δ, hδ, hnear⟩ := exB_lt_near hca (hfix.symm ▸ hwg : r θhat < w)
      set a := max θl (θhat - δ / 2)
      have ha : a < θhat := max_lt hθ.1 (by linarith)
      refine (h.dens.pos a ((a + θhat) / 2) (le_max_left _ _) (by linarith)
        (by linarith [hθ.2])).trans_le (measure_mono fun y hy => ?_)
      have hyI : y ∈ Set.Icc θl θh :=
        ⟨(le_max_left _ _).trans hy.1, by linarith [hy.2, hθ.2]⟩
      have hyθ : y < θhat := by linarith [hy.2]
      refine ⟨(hnear y ?_).le, hgt y hyI hyθ⟩
      rw [abs_lt]; constructor <;> linarith [hy.1, le_max_right θl (θhat - δ / 2), hy.2]

/-- **Exercise 13.B.3(b)**, instance (MWG, p. 473). Types uniform on `[0, 1]`,
`r(θ) = 3 - θ > θ`. -/
theorem exercise_13_B_3b_instance :
    AntiModel (unifMeas 0 1) 0 1 (fun θ => 3 - θ) ∧
      eqWages (unifMeas 0 1) 0 1 (fun θ => 3 - θ) = {1 / 2} := by
  have hA : AntiModel (unifMeas 0 1) 0 1 (fun θ => 3 - θ) :=
    ⟨unifMeas_typeDist le_rfl one_pos, unifMeas_density one_pos,
      measurable_const.sub measurable_id, fun a _ b _ hab => by linarith, by fun_prop⟩
  refine ⟨hA, ?_⟩
  rw [(exercise_13_B_3b hA (fun θ hθ => by linarith [hθ.2]) 1).1, unifMeas_mean one_pos]
  norm_num

/-- **Exercise 13.B.3(b)**, instance of the reverse reading (MWG, p. 473). Types uniform on
`[1, 2]`, `r(θ) = (2 - θ)/2 < θ`: the unique equilibrium wage is `E[θ] = 3/2`. -/
theorem exercise_13_B_3b_lt_instance :
    AntiModel (unifMeas 1 2) 1 2 (fun θ => (2 - θ) / 2) ∧
      eqWages (unifMeas 1 2) 1 2 (fun θ => (2 - θ) / 2) = {3 / 2} := by
  have hA : AntiModel (unifMeas 1 2) 1 2 (fun θ => (2 - θ) / 2) :=
    ⟨unifMeas_typeDist zero_le_one one_lt_two, unifMeas_density one_lt_two,
      (measurable_const.sub measurable_id).div_const 2, fun a _ b _ hab => by linarith,
      by fun_prop⟩
  refine ⟨hA, ?_⟩
  rw [(exercise_13_B_3b_lt hA (fun θ hθ => by linarith [hθ.1]) 1).1, unifMeas_mean one_lt_two]
  norm_num

/-- **Exercise 13.B.3(c)**, instance (MWG, p. 473). Types uniform on `[0, 2]`,
`r(θ) = 1 - θ/2` (`θ̂ = 2/3`): `w* = E[θ] = 1` is an equilibrium with every type employed, too
many relative to the optimum, which employs only `θ ≥ 2/3`. -/
theorem exercise_13_B_3c_instance :
    (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (fun θ => 1 - θ / 2) ∧
      0 < unifMeas 0 2 (acceptSet (fun θ => 1 - θ / 2) 1 ∩ {θ | θ < 1 - θ / 2}) := by
  have hA : AntiModel (unifMeas 0 2) 0 2 (fun θ => 1 - θ / 2) :=
    ⟨unifMeas_typeDist le_rfl two_pos, unifMeas_density two_pos,
      measurable_const.sub (measurable_id.div_const 2), fun a _ b _ hab => by linarith,
      by fun_prop⟩
  have hsub : Set.Icc (0 : ℝ) 2 ⊆ acceptSet (fun θ => 1 - θ / 2) 1 := fun θ hθ => by
    change 1 - θ / 2 ≤ 1; linarith [hθ.1]
  have hw : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (fun θ => 1 - θ / 2) := by
    have := mean_mem_eqWages (unifMeas_typeDist le_rfl two_pos)
      (r := fun θ => 1 - θ / 2) (by rw [unifMeas_mean two_pos]; norm_num; exact hsub)
    rwa [unifMeas_mean two_pos, show ((0 : ℝ) + 2) / 2 = 1 by norm_num] at this
  have hpos : 0 < unifMeas 0 2 (acceptSet (fun θ => 1 - θ / 2) 1) :=
    ((unifMeas_density two_pos).pos 0 2 le_rfl two_pos le_rfl).trans_le (measure_mono hsub)
  exact ⟨hw, (exercise_13_B_3c hA (θhat := 2 / 3) ⟨by norm_num, by norm_num⟩
    (fun θ _ h => by linarith) (fun θ _ h => by linarith) hw hpos).2⟩

/-- **Exercise 13.B.3(c), counterexample** (MWG, p. 473). The claim needs `θ̂ > θ̲`. Types
uniform on `[1, 2]`, `r(θ) = 2 - θ`: `r(θ) < θ` for `θ > θ̂ = 1 = θ̲` (and `r(θ) > θ` for
`θ < θ̂` vacuously in `[1, 2]`). The equilibrium `w* = 3/2` employs everybody, which is exactly the
Pareto optimal allocation: no type with `r(θ) > θ` is employed. -/
theorem exercise_13_B_3c_counterexample :
    AntiModel (unifMeas 1 2) 1 2 (fun θ => 2 - θ) ∧
      (∀ θ ∈ Set.Icc (1 : ℝ) 2, 1 < θ → 2 - θ < θ) ∧
      (∀ θ ∈ Set.Icc (1 : ℝ) 2, θ < 1 → θ < 2 - θ) ∧
      (3 / 2 : ℝ) ∈ eqWages (unifMeas 1 2) 1 2 (fun θ => 2 - θ) ∧
      0 < unifMeas 1 2 (acceptSet (fun θ => 2 - θ) (3 / 2)) ∧
      unifMeas 1 2 (acceptSet (fun θ => 2 - θ) (3 / 2) ∩ {θ | θ < 2 - θ}) = 0 := by
  have hd : TypeDist (unifMeas 1 2) 1 2 := unifMeas_typeDist zero_le_one one_lt_two
  have hsub : Set.Icc (1 : ℝ) 2 ⊆ acceptSet (fun θ => 2 - θ) (3 / 2) := fun θ hθ => by
    change 2 - θ ≤ 3 / 2; linarith [hθ.1]
  refine ⟨⟨hd, unifMeas_density one_lt_two, measurable_const.sub measurable_id,
    fun a _ b _ hab => by linarith, by fun_prop⟩, fun θ _ h => by linarith,
    fun θ hθ h => absurd hθ.1 (not_le.2 h), ?_, ?_, ?_⟩
  · have := mean_mem_eqWages hd (r := fun θ => 2 - θ) (by
      rw [unifMeas_mean one_lt_two]; norm_num; exact hsub)
    rwa [unifMeas_mean one_lt_two, show ((1 : ℝ) + 2) / 2 = 3 / 2 by norm_num] at this
  · exact ((unifMeas_density one_lt_two).pos 1 2 le_rfl one_lt_two le_rfl).trans_le
      (measure_mono hsub)
  · refine measure_mono_null (t := (Set.Icc (1 : ℝ) 2)ᶜ) (fun θ hθ hθI => ?_)
      hd.supp
    have : θ < 2 - θ := hθ.2
    linarith [hθI.1]

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.B.7: Pareto-improving interventions

MWG, Section 13.B, Exercise 13.B.7, p. 474, in the setting of `Constrained.lean` (pp. 445-447):
the authority pays `w_e` to the employed and `w_u` to the unemployed, the types in
`Θ(w_e - w_u)` work, the budget is `BudgetOK` and Pareto improvement is `IsParetoImprovement`
relative to the competitive equilibrium with wage `w*`.

* `ReducesEmployment`, `IncreasesEmployment`: the set of types in `[θ̲, θ̄]` employed under the
  intervention is a strict subset (superset) of the equilibrium set `Θ(w*) ∩ [θ̲, θ̄]`.
* `budgetOK_iff`: the budget says exactly `w_u ≤ Π(w_e - w_u)`.
* `exercise_13_B_7_reduce`: a Pareto-improving intervention reducing employment exists iff one of
  the form `(w*, ŵ_u)`, `ŵ_u > 0`, does (no assumption on `r` beyond measurability).
* `exercise_13_B_7_increase`: a Pareto-improving intervention increasing employment exists iff one
  of the form `(ŵ_e, 0)`, `ŵ_e > w*`, does. Departure: this needs the level sets
  `{θ : r(θ) = c}` to be null (true in the model of Section 13.B, `MonoModel.levelNull`).
* `exercise_13_B_7_proposition_13_B_2`: the "simple proof" of Proposition 13.B.2 (in the
  generality of Exercise 13.B.10): at the highest-wage equilibrium an intervention reducing
  employment fails because `E[θ | θ ≤ θ̂] < w*`, one increasing employment fails because firms
  lose money above `w*`, and one keeping employment cannot balance the budget.
* `exercise_13_B_7_instance`: in Example 13.B.1 with `α = 1/4` (`W* = {0, 1}`), at the low
  equilibrium `w* = 0` both sides of `exercise_13_B_7_increase` hold with `ŵ_e = 1`. (An
  instance of `exercise_13_B_7_reduce` is `exercise_13_B_9`.)
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.7** (MWG, p. 474). The intervention `(w_e, w_u)` reduces employment relative
to the equilibrium with wage `w*`: the types in `[θ̲, θ̄]` that work under it are a strict subset
of those working in the equilibrium. -/
def ReducesEmployment (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  acceptSet r (we - wu) ∩ Set.Icc θl θh ⊂ acceptSet r ws ∩ Set.Icc θl θh

/-- **Exercise 13.B.7** (MWG, p. 474). The intervention `(w_e, w_u)` increases employment relative
to the equilibrium with wage `w*`. -/
def IncreasesEmployment (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  acceptSet r ws ∩ Set.Icc θl θh ⊂ acceptSet r (we - wu) ∩ Set.Icc θl θh

/-- **(13.B.8)** (MWG, p. 447). The budget constraint says exactly that `w_u` is at most the
profit of a firm paying `w_e - w_u`. -/
theorem budgetOK_iff {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {we wu : ℝ} :
    BudgetOK μ r we wu ↔ wu ≤ firmProfit μ r (we - wu) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  unfold BudgetOK
  constructor <;> intro hb <;> nlinarith

/-- A reducing intervention leaves home a type that worked in the equilibrium. -/
theorem exB7_reduces_exists {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu : ℝ}
    (h : ReducesEmployment θl θh r ws we wu) :
    ∃ θ ∈ Set.Icc θl θh, we - wu < r θ ∧ r θ ≤ ws := by
  obtain ⟨θ, ⟨hθw, hθI⟩, hθn⟩ := Set.exists_of_ssubset h
  exact ⟨θ, hθI, not_le.1 fun hle => hθn ⟨hle, hθI⟩, hθw⟩

/-- A type that worked in the equilibrium but not under `(w_e, w_u)` makes it reducing. -/
theorem exB7_reduces_of {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu θ : ℝ} (hθ : θ ∈ Set.Icc θl θh)
    (h1 : we - wu < r θ) (h2 : r θ ≤ ws) : ReducesEmployment θl θh r ws we wu :=
  ssubset_of_subset_not_subset (fun _ hθ' => ⟨le_trans hθ'.1 (h1.trans_le h2).le, hθ'.2⟩)
    fun hsub => absurd (hsub ⟨h2, hθ⟩).1 (not_le.2 h1)

/-- An increasing intervention employs a type that stayed home in the equilibrium. -/
theorem exB7_increases_exists {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu : ℝ}
    (h : IncreasesEmployment θl θh r ws we wu) :
    ∃ θ ∈ Set.Icc θl θh, ws < r θ ∧ r θ ≤ we - wu := by
  obtain ⟨θ, ⟨hθw, hθI⟩, hθn⟩ := Set.exists_of_ssubset h
  exact ⟨θ, hθI, not_le.1 fun hle => hθn ⟨hle, hθI⟩, hθw⟩

/-- A type that works under `(w_e, w_u)` but not in the equilibrium makes it increasing. -/
theorem exB7_increases_of {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu θ : ℝ} (hθ : θ ∈ Set.Icc θl θh)
    (h1 : ws < r θ) (h2 : r θ ≤ we - wu) : IncreasesEmployment θl θh r ws we wu :=
  ssubset_of_subset_not_subset (fun _ hθ' => ⟨le_trans hθ'.1 (h1.trans_le h2).le, hθ'.2⟩)
    fun hsub => absurd (hsub ⟨h2, hθ⟩).1 (not_le.2 h1)

/-- A worker employed under `(w_e, w_u)` gets `w_e`. -/
theorem exB7_pay_emp {we wu x : ℝ} (h : x ≤ we - wu) : max we (wu + x) = we :=
  max_eq_left (by linarith)

/-- A worker at home under `(w_e, w_u)` gets `w_u + r(θ)`. -/
theorem exB7_pay_unemp {we wu x : ℝ} (h : we - wu < x) : max we (wu + x) = wu + x :=
  max_eq_right (by linarith)

/-- If no type in `[θ̲, θ̄]` accepts `w`, a firm paying `w` earns nothing. -/
theorem exB7_profit_of_empty {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {w : ℝ} (h : ∀ θ ∈ Set.Icc θl θh, w < r θ) : firmProfit μ r w = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd]
  convert measure_empty (μ := μ)
  exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => absurd hθ.1 (not_le.2 (h θ hθ.2))

/-- **Exercise 13.B.7** (MWG, p. 474). There is a budget-feasible Pareto-improving intervention
that reduces employment iff there is one of the form `(w*, ŵ_u)` with `ŵ_u > 0`. (Only
measurability of `r` is used; `w*` need not even be an equilibrium wage.) -/
theorem exercise_13_B_7_reduce {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) (ws : ℝ) :
    (∃ we wu, BudgetOK μ r we wu ∧ IsParetoImprovement θl θh r ws we wu ∧
      ReducesEmployment θl θh r ws we wu) ↔
    ∃ wu', 0 < wu' ∧ BudgetOK μ r ws wu' ∧ IsParetoImprovement θl θh r ws ws wu' ∧
      ReducesEmployment θl θh r ws ws wu' := by
  constructor
  · rintro ⟨we, wu, hb, ⟨hall, θ1, hθ1, hstrict⟩, hred⟩
    obtain ⟨θ0, hθ0, h01, h02⟩ := exB7_reduces_exists hred
    have hwu := (budgetOK_iff hd hr).1 hb
    have hdws : we - wu < ws := h01.trans_le h02
    have hwe : ws ≤ we := by
      by_cases hex : ∃ θ ∈ Set.Icc θl θh, r θ ≤ we - wu
      · obtain ⟨θ, hθ, hle⟩ := hex
        have := hall θ hθ
        rw [exB7_pay_emp hle] at this
        exact (le_max_left _ _).trans this
      · push Not at hex
        rw [exB7_profit_of_empty hd hr hex] at hwu
        have := hstrict
        rw [exB7_pay_unemp (hex θ1 hθ1)] at this
        linarith [le_max_right ws (r θ1)]
    refine ⟨ws - (we - wu), by linarith, ?_, ⟨fun θ _ => ?_, θ0, hθ0, ?_⟩, ?_⟩
    · rw [budgetOK_iff hd hr, sub_sub_cancel]
      linarith
    · exact max_le_max le_rfl (by linarith)
    · rw [max_eq_left h02]
      exact lt_max_of_lt_right (by linarith)
    · unfold ReducesEmployment
      rw [sub_sub_cancel]
      exact hred
  · rintro ⟨wu', -, hb, hpi, hred⟩
    exact ⟨ws, wu', hb, hpi, hred⟩

/-- In the model of Section 13.B (`MonoModel`), the level sets of `r` are null. -/
theorem MonoModel.levelNull {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : MonoModel μ θl θh r)
    (c : ℝ) : μ {θ | r θ = c} = 0 := by
  rw [← measure_acceptSet_inter h.dist]
  by_cases hex : ∃ θ0 ∈ Set.Icc θl θh, r θ0 = c
  · obtain ⟨θ0, hθ0, hc⟩ := hex
    refine measure_mono_null (t := {θ0}) (fun θ hθ => ?_) (h.dens.noAtom θ0)
    exact h.mono.injOn hθ.2 hθ0 (hθ.1.trans hc.symm)
  · push Not at hex
    convert measure_empty (μ := μ)
    exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => hex θ hθ.2 hθ.1

/-- **Exercise 13.B.7** (MWG, p. 474). There is a budget-feasible Pareto-improving intervention
that increases employment iff there is one of the form `(ŵ_e, 0)` with `ŵ_e > w*`. We assume
that the level sets `{θ : r(θ) = c}` are null (true in the model of Section 13.B,
`MonoModel.levelNull`). -/
theorem exercise_13_B_7_increase {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) (hlev : ∀ c, μ {θ | r θ = c} = 0) (ws : ℝ) :
    (∃ we wu, BudgetOK μ r we wu ∧ IsParetoImprovement θl θh r ws we wu ∧
      IncreasesEmployment θl θh r ws we wu) ↔
    ∃ we', ws < we' ∧ BudgetOK μ r we' 0 ∧ IsParetoImprovement θl θh r ws we' 0 ∧
      IncreasesEmployment θl θh r ws we' 0 := by
  have := hd.prob
  constructor
  · rintro ⟨we, wu, hb, ⟨hall, θ1, hθ1, hstrict⟩, hinc⟩
    obtain ⟨θ0, hθ0, h01, h02⟩ := exB7_increases_exists hinc
    have hwu := (budgetOK_iff hd hr).1 hb
    have hwsd : ws < we - wu := h01.trans_le h02
    by_cases hA : ∃ θ ∈ Set.Icc θl θh, we - wu < r θ
    · obtain ⟨θ2, hθ2, hd2⟩ := hA
      have hwu0 : 0 ≤ wu := by
        have := hall θ2 hθ2
        rw [exB7_pay_unemp hd2, max_eq_right (hwsd.trans hd2).le] at this
        linarith
      rcases eq_or_lt_of_le hwu0 with h0 | hpos
      · subst h0
        exact ⟨we, by linarith, hb, ⟨hall, θ1, hθ1, hstrict⟩, hinc⟩
      · -- some type in `[θ̲, θ̄]` has `r(θ) < w_e - w_u`
        have hP : 0 < firmProfit μ r (we - wu) := hpos.trans_le hwu
        have hmeas : 0 < μ (acceptSet r (we - wu)) := by
          by_contra h0
          rw [not_lt, nonpos_iff_eq_zero] at h0
          rw [firmProfit_of_null hr h0] at hP
          exact lt_irrefl _ hP
        have hex : ∃ θ ∈ Set.Icc θl θh, r θ < we - wu := by
          by_contra hno
          push Not at hno
          refine hmeas.ne' (measure_mono_null (t := {θ | r θ = we - wu} ∪ (Set.Icc θl θh)ᶜ)
            (fun θ hθ => ?_) (measure_union_null (hlev _) hd.supp))
          by_cases hθI : θ ∈ Set.Icc θl θh
          · exact Or.inl (le_antisymm hθ (hno θ hθI))
          · exact Or.inr hθI
        obtain ⟨θ3, hθ3, hr3⟩ := hex
        refine ⟨we - wu, hwsd, ?_, ⟨fun θ _ => ?_, θ3, hθ3, ?_⟩, ?_⟩
        · rw [budgetOK_iff hd hr, sub_zero]; exact hP.le
        · rw [zero_add]; exact max_le_max hwsd.le le_rfl
        · rw [zero_add, max_eq_left hr3.le]; exact max_lt hwsd hr3
        · exact exB7_increases_of hθ0 h01 (by rw [sub_zero]; exact h02)
    · -- everybody works under the intervention
      push Not at hA
      have hfull : Set.Icc θl θh ⊆ acceptSet r (we - wu) := fun θ hθ => hA θ hθ
      rw [firmProfit_of_full hd hr hfull] at hwu
      have hpay : ∀ θ ∈ Set.Icc θl θh, max we (wu + r θ) = we := fun θ hθ =>
        exB7_pay_emp (hA θ hθ)
      have hle : ∀ θ ∈ Set.Icc θl θh, r θ ≤ we := fun θ hθ =>
        (le_max_right ws (r θ)).trans ((hall θ hθ).trans (hpay θ hθ).le)
      have hwswe : ws < we := by
        have := hstrict; rw [hpay θ1 hθ1] at this; exact (le_max_left _ _).trans_lt this
      have hfull' : Set.Icc θl θh ⊆ acceptSet r (we - 0) := fun θ hθ => by
        rw [sub_zero]; exact hle θ hθ
      refine ⟨we, hwswe, ?_, ⟨fun θ hθ => ?_, θ1, hθ1, ?_⟩, ?_⟩
      · rw [budgetOK_iff hd hr, firmProfit_of_full hd hr hfull']; linarith
      · rw [zero_add, max_eq_left (hle θ hθ)]; exact (hall θ hθ).trans (hpay θ hθ).le
      · rw [zero_add, max_eq_left (hle θ1 hθ1)]
        exact hstrict.trans_le (hpay θ1 hθ1).le
      · exact exB7_increases_of hθ0 h01 (by rw [sub_zero]; exact hle θ0 hθ0)
  · rintro ⟨we', -, hb, hpi, hinc⟩
    exact ⟨we', 0, hb, hpi, hinc⟩

/-- Under `(w_e, w_u)` with the same employed types as at `w`, the profit at `w_e - w_u` is
`Π(w) + F(Θ(w)) (w - (w_e - w_u))`. -/
theorem exB7_profit_congr {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {d w : ℝ}
    (hE : acceptSet r d ∩ Set.Icc θl θh = acceptSet r w ∩ Set.Icc θl θh) :
    firmProfit μ r d = firmProfit μ r w + μ.real (acceptSet r w) * (w - d) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, firmProfit_eq_setIntegral hr,
    setIntegral_congr_set (exB_ae_eq_of_inter hd hE)]
  have h : ∫ θ in acceptSet r w, (θ - d) ∂μ =
      ∫ θ in acceptSet r w, ((θ - w) + (w - d)) ∂μ := by
    congr 1; funext θ; ring
  rw [h, integral_add (f := fun θ => θ - w) (g := fun _ => w - d)
    (hd.integrable_id.sub (integrable_const w)).integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]

/-- In the `MonoModel`, if some type does not accept `c`, a positive mass does not. -/
theorem MonoModel.measureReal_acceptSet_lt_one {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {c θ : ℝ} (hθ : θ ∈ Set.Icc θl θh) (hc : c < r θ) :
    μ.real (acceptSet r c) < 1 := by
  have hd := h.dist
  have := hd.prob
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have hch : c < r θh := hc.trans_le (h.mono.monotoneOn hθ hh hθ.2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((h.cont θh hh).eventually (lt_mem_nhds hch))
  set a := max θl (θh - ε / 2)
  have ha : a < θh := max_lt hd.lt (by linarith)
  have hpos : 0 < μ (Set.Icc a θh) := h.dens.pos a θh (le_max_left _ _) ha le_rfl
  have hsub : Set.Icc a θh ⊆ (acceptSet r c)ᶜ := fun y hy hacc => by
    have hyI : y ∈ Set.Icc θl θh := ⟨(le_max_left _ _).trans hy.1, hy.2⟩
    have hdist : Dist.dist y θh < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, le_max_right θl (θh - ε / 2)]
    have hlt : c < r y := hball ⟨Metric.mem_ball.2 hdist, hyI⟩
    exact absurd (hacc : r y ≤ c) (not_le.2 hlt)
  have hlt : μ (acceptSet r c) < 1 := by
    have h1 := prob_compl_eq_one_sub (μ := μ) (measurableSet_acceptSet h.meas c)
    have h2 : 0 < μ (acceptSet r c)ᶜ := hpos.trans_le (measure_mono hsub)
    rw [h1] at h2
    exact tsub_pos_iff_lt.1 h2
  rw [Measure.real]
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hlt |>.trans_eq
    ENNReal.toReal_one

/-- **Exercise 13.B.7** (MWG, p. 474): the "simple proof" of **Proposition 13.B.2**, in the
generality of Exercise 13.B.10 (`r(θ) ≤ θ` not needed). At the highest-wage competitive
equilibrium no budget-feasible intervention is a Pareto improvement: by
`exercise_13_B_7_reduce` a reducing one would give one of the form `(w*, ŵ_u)`, impossible since
`E[θ | θ ≤ θ̂] < w*`; by `exercise_13_B_7_increase` an increasing one would give one of the
form `(ŵ_e, 0)`, impossible since firms lose money above `w*`; and one keeping the employed
set cannot pay anybody more. -/
theorem exercise_13_B_7_proposition_13_B_2 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws := by
  have hd := h.dist
  have := hd.prob
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  intro we wu hb hpi
  have hP0 : firmProfit μ r ws = 0 := by
    rcases eq_zero_or_pos (μ (acceptSet r ws)) with h0 | hpos
    · exact firmProfit_of_null h.meas h0
    · exact (mem_eqWages_iff_profit hd h.meas hpos).1 hmax.1
  by_cases hred : ReducesEmployment θl θh r ws we wu
  · obtain ⟨wu', hwu', hb', -, hred'⟩ :=
      (exercise_13_B_7_reduce hd h.meas ws).1 ⟨we, wu, hb, hpi, hred⟩
    obtain ⟨θ0, hθ0, h1, h2⟩ := exB7_reduces_exists hred'
    have hP := (budgetOK_iff hd h.meas).1 hb'
    by_cases hdl : ws - wu' < r θl
    · rw [firmProfit_of_lt hd h.mono.monotoneOn h.meas hdl] at hP
      linarith
    · have := h.profit_add_lt hmax.1 (not_lt.1 hdl) (by linarith)
        (h1.trans_le (h.mono.monotoneOn hθ0 hh hθ0.2))
      linarith
  by_cases hinc : IncreasesEmployment θl θh r ws we wu
  · obtain ⟨we', hwe', hb', ⟨-, θ1, hθ1, hs⟩, -⟩ :=
      (exercise_13_B_7_increase hd h.meas h.levelNull ws).1 ⟨we, wu, hb, hpi, hinc⟩
    have hP := (budgetOK_iff hd h.meas).1 hb'
    rw [sub_zero] at hP
    rw [zero_add] at hs
    have hrl : r θl < we' := by
      by_contra hc
      rw [not_lt] at hc
      rw [max_eq_right (hc.trans (h.mono.monotoneOn hl hθ1 hθ1.1))] at hs
      exact absurd hs (not_lt.2 (le_max_right _ _))
    have hneg := h.firmProfit_neg_of_gt_max hmax hwe'
      (measure_acceptSet_pos hd h.dens h.cont hrl)
    linarith
  -- the employed set is unchanged
  obtain ⟨hall, θ1, hθ1, hstrict⟩ := hpi
  have hE : acceptSet r (we - wu) ∩ Set.Icc θl θh = acceptSet r ws ∩ Set.Icc θl θh := by
    rcases le_or_gt (we - wu) ws with hle | hgt
    · have hsub : acceptSet r (we - wu) ∩ Set.Icc θl θh ⊆ acceptSet r ws ∩ Set.Icc θl θh :=
        fun θ hθ => ⟨le_trans hθ.1 hle, hθ.2⟩
      rcases hsub.eq_or_ssubset with heq | hss
      · exact heq
      · exact absurd hss hred
    · have hsub : acceptSet r ws ∩ Set.Icc θl θh ⊆ acceptSet r (we - wu) ∩ Set.Icc θl θh :=
        fun θ hθ => ⟨le_trans hθ.1 hgt.le, hθ.2⟩
      rcases hsub.eq_or_ssubset with heq | hss
      · exact heq.symm
      · exact absurd hss hinc
  have hwu := (budgetOK_iff hd h.meas).1 hb
  rw [exB7_profit_congr hd h.meas hE, hP0, zero_add] at hwu
  set p := μ.real (acceptSet r ws) with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [hp, Measure.real]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq ENNReal.toReal_one
  -- employed types (in both) get `w_e`, the others `w_u + r(θ)`
  have hemp : ∀ θ ∈ Set.Icc θl θh, r θ ≤ ws → r θ ≤ we - wu := fun θ hθ hle => by
    have hm : θ ∈ acceptSet r (we - wu) ∩ Set.Icc θl θh := by rw [hE]; exact ⟨hle, hθ⟩
    exact hm.1
  have hun : ∀ θ ∈ Set.Icc θl θh, ws < r θ → we - wu < r θ := fun θ hθ hlt => by
    refine not_le.1 fun hle => ?_
    have hm : θ ∈ acceptSet r ws ∩ Set.Icc θl θh := by rw [← hE]; exact ⟨hle, hθ⟩
    exact absurd (hm.1 : r θ ≤ ws) (not_le.2 hlt)
  have hwe : ∀ θ ∈ Set.Icc θl θh, r θ ≤ ws → ws ≤ we := fun θ hθ hle => by
    have := hall θ hθ
    rw [exB7_pay_emp (hemp θ hθ hle), max_eq_left hle] at this
    exact this
  have hwu0 : ∀ θ ∈ Set.Icc θl θh, ws < r θ → 0 ≤ wu := fun θ hθ hlt => by
    have := hall θ hθ
    rw [exB7_pay_unemp (hun θ hθ hlt), max_eq_right hlt.le] at this
    linarith
  have hst : (r θ1 ≤ ws ∧ ws < we) ∨ (ws < r θ1 ∧ 0 < wu) := by
    rcases le_or_gt (r θ1) ws with hle | hlt
    · have := hstrict
      rw [exB7_pay_emp (hemp θ1 hθ1 hle), max_eq_left hle] at this
      exact Or.inl ⟨hle, this⟩
    · have := hstrict
      rw [exB7_pay_unemp (hun θ1 hθ1 hlt), max_eq_right hlt.le] at this
      exact Or.inr ⟨hlt, by linarith⟩
  by_cases hU : ∃ θ ∈ Set.Icc θl θh, ws < r θ
  · obtain ⟨θu, hθu, hu⟩ := hU
    have hwupos := hwu0 θu hθu hu
    have hplt : p < 1 := h.measureReal_acceptSet_lt_one hθu hu
    by_cases hEm : ∃ θ ∈ Set.Icc θl θh, r θ ≤ ws
    · obtain ⟨θe, hθe, he⟩ := hEm
      have hwege := hwe θe hθe he
      have hwu_zero : wu = 0 := by nlinarith
      rcases hst with ⟨hle1, hlt1⟩ | ⟨-, hlt1⟩
      · -- then `p = 0`, so nobody works at `w_e - w_u > w*`: impossible
        have hpz : p = 0 := by nlinarith
        have hgt : r θl < we - wu := by
          rw [hwu_zero, sub_zero]
          exact ((h.mono.monotoneOn hl hθ1 hθ1.1).trans hle1).trans_lt hlt1
        have hposd := measure_acceptSet_pos hd h.dens h.cont hgt
        have hmeq : μ (acceptSet r (we - wu)) = μ (acceptSet r ws) :=
          measure_congr (exB_ae_eq_of_inter hd hE)
        have : 0 < p := by
          rw [hp, Measure.real, ← hmeq]
          exact ENNReal.toReal_pos hposd.ne' (measure_ne_top _ _)
        linarith
      · linarith
    · push Not at hEm
      have hpz : p = 0 := by
        rw [hp, Measure.real, ← measure_acceptSet_inter hd]
        convert ENNReal.toReal_zero
        convert measure_empty (μ := μ)
        exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => absurd hθ.1 (not_le.2 (hEm θ hθ.2))
      rcases hst with ⟨hle1, -⟩ | ⟨-, hlt1⟩
      · exact absurd hle1 (not_le.2 (hEm θ1 hθ1))
      · rw [hpz] at hwu; linarith
  · push Not at hU
    have hpo : p = 1 := by
      have hI1 : μ (Set.Icc θl θh) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).1 hd.supp
      rw [hp, Measure.real, ← measure_acceptSet_inter hd,
        Set.inter_eq_right.2 (show Set.Icc θl θh ⊆ acceptSet r ws from fun θ hθ => hU θ hθ),
        hI1, ENNReal.toReal_one]
    rcases hst with ⟨-, hlt1⟩ | ⟨hlt1, -⟩
    · rw [hpo] at hwu; linarith
    · exact absurd hlt1 (not_lt.2 (hU θ1 hθ1))

/-- **Exercise 13.B.7**, instance (MWG, pp. 442, 474). Example 13.B.1 with `α = 1/4`: at the
dominated equilibrium `w* = 0` the intervention `(1, 0)` increases employment and is a
budget-feasible Pareto improvement, so both sides of `exercise_13_B_7_increase` hold. -/
theorem exercise_13_B_7_instance :
    (∃ we wu, BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we wu ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we wu ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we wu) ∧
    ∃ we', 0 < we' ∧ BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we' 0 ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we' 0 ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we' 0 := by
  have hR := akerlof_regular (α := 1 / 4) (by norm_num) (by norm_num)
  have hW := example_13_B_1_lowα (α := 1 / 4) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) := by
    rw [hW]; exact Or.inr rfl
  have hpos : 0 < unifMeas 0 2 (acceptSet (akerlofR (1 / 4)) 1) :=
    measure_acceptSet_pos hR.dist hR.dens hR.cont (by simp only [akerlofR]; norm_num)
  have hrhs : ∃ we', 0 < we' ∧ BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we' 0 ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we' 0 ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we' 0 := by
    refine ⟨1, one_pos, (highest_wage_implementable hR.dist hR.meas h1 hpos).1,
      ⟨fun θ _ => max_le_max zero_le_one (by rw [zero_add]), 0, ⟨le_rfl, zero_le_two⟩, ?_⟩,
      exB7_increases_of (θ := 1) ⟨zero_le_one, one_le_two⟩ (by simp only [akerlofR]; norm_num)
        (by simp only [akerlofR]; norm_num)⟩
    simp only [akerlofR]; norm_num
  refine ⟨?_, hrhs⟩
  obtain ⟨we', -, hb, hpi, hinc⟩ := hrhs
  exact ⟨we', 0, hb, hpi, hinc⟩

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.B.8: interventions based on observable purchases of `x`

MWG, Section 13.B, Exercise 13.B.8, p. 474. Home production uses a good `x`; a type-`θ` worker at
home buys `x(θ)`, which the authority observes. An intervention is an employment wage `w_e` and
an unemployment benefit `b(x)` depending on the observed purchase: type `θ` works iff
`r(θ) + b(x(θ)) ≤ w_e` and then gets `w_e`, otherwise `r(θ) + b(x(θ))`. The authority runs the
firms: its net revenue from type `θ` is `θ - w_e` if employed and `-b(x(θ))` otherwise
(`xNetRev`), and its budget (`XBudgetOK`) requires this to be integrable with nonnegative mean.
`IsXParetoImprovement` asks that no type in `[θ̲, θ̄]` loses and that a set of types of positive
probability gains: since `x` can single out one type, a gain for a null set of types costs
nothing and would make the notion trivial.

* `xBudgetOK_const_iff`: a constant benefit `b ≡ w_u` is the scheme `(w_e, w_u)` of
  `Constrained.lean`.
* Correction, `exercise_13_B_8_false`: in the model of Section 13.B (`RegularModel`: `r` strictly
  increasing and continuous, `r(θ) ≤ θ`, positive density), at the highest-wage equilibrium NO
  intervention of this kind (for any observable `x` and any benefit schedule `b`) is a Pareto
  improvement. So the printed claim is false in that model.
* `exercise_13_B_8`: what is true. If `x` is injective on `[θ̲, θ̄]` (e.g. strictly increasing)
  and, at an equilibrium with wage `w*` (for instance the highest-wage one), a positive mass of
  employed types is more productive at home (`r(θ) > θ`, the setting of Exercise 13.B.10), the
  benefit `b(x(θ)) = w* - θ` for exactly those types is a budget-neutral Pareto improvement.
  `exercise_13_B_8_instance`: here the highest-wage equilibrium is a constrained Pareto optimum
  for `(w_e, w_u)` schemes (Exercise 13.B.10), yet observing `x` allows a Pareto improvement.
* `exercise_13_B_8_const_x`: with `x` constant (weakly increasing is not enough) no such
  improvement exists at the highest-wage equilibrium.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.8** (MWG, p. 474). The authority's net revenue from a type-`θ` worker under
the intervention `(w_e, b)`: `θ - w_e` if she works, `-b(x(θ))` if she stays home. -/
noncomputable def xNetRev (r x : ℝ → ℝ) (we : ℝ) (b : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if r θ + b (x θ) ≤ we then θ - we else -b (x θ)

/-- **Exercise 13.B.8** (MWG, p. 474). The budget of the intervention `(w_e, b)`: the net
revenue is integrable and its mean is nonnegative. -/
def XBudgetOK (μ : Measure ℝ) (r x : ℝ → ℝ) (we : ℝ) (b : ℝ → ℝ) : Prop :=
  Integrable (xNetRev r x we b) μ ∧ 0 ≤ ∫ θ, xNetRev r x we b θ ∂μ

/-- **Exercise 13.B.8** (MWG, p. 474). The intervention `(w_e, b)` Pareto improves on the
competitive equilibrium with wage `w*`: no type in `[θ̲, θ̄]` is worse off and a set of types of
positive probability is strictly better off. -/
def IsXParetoImprovement (μ : Measure ℝ) (θl θh : ℝ) (r x : ℝ → ℝ) (ws we : ℝ)
    (b : ℝ → ℝ) : Prop :=
  (∀ θ ∈ Set.Icc θl θh, max ws (r θ) ≤ max we (r θ + b (x θ))) ∧
    0 < μ {θ | max ws (r θ) < max we (r θ + b (x θ))}

/-- With a constant benefit `w_u` the net revenue is the profit integrand at `w_e - w_u`
minus `w_u`. -/
theorem xNetRev_const (r x : ℝ → ℝ) (we wu : ℝ) :
    xNetRev r x we (fun _ => wu) = fun θ =>
      (acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu := by
  funext θ
  unfold xNetRev
  by_cases hθ : r θ ≤ we - wu
  · rw [Set.indicator_of_mem (show θ ∈ acceptSet r (we - wu) from hθ)]
    split_ifs with h1
    · ring
    · exact absurd (by linarith : r θ + wu ≤ we) h1
  · rw [Set.indicator_of_notMem (show θ ∉ acceptSet r (we - wu) from hθ)]
    split_ifs with h1
    · exact absurd (by linarith : r θ ≤ we - wu) hθ
    · ring

/-- **Exercise 13.B.8** (MWG, p. 474). A constant benefit `b ≡ w_u` is the scheme `(w_e, w_u)` of
p. 446: the budgets coincide. -/
theorem xBudgetOK_const_iff {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) (x : ℝ → ℝ) (we wu : ℝ) :
    XBudgetOK μ r x we (fun _ => wu) ↔ BudgetOK μ r we wu := by
  have := hd.prob
  have hi1 : Integrable ((acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu))) μ :=
    (hd.integrable_id.sub (integrable_const _)).indicator (measurableSet_acceptSet hr _)
  have hint : Integrable (fun θ =>
      (acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu) μ :=
    hi1.sub (integrable_const wu)
  have hI : ∫ θ, ((acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu) ∂μ =
      firmProfit μ r (we - wu) - wu := by
    rw [integral_sub hi1 (integrable_const wu), integral_const, smul_eq_mul, probReal_univ,
      one_mul]
    rfl
  rw [XBudgetOK, xNetRev_const, budgetOK_iff hd hr]
  beta_reduce
  rw [hI]
  exact ⟨fun h => by linarith [h.2], fun h => ⟨hint, by linarith⟩⟩

/-- If `f ≤ g` almost everywhere and `f < g` on a set of positive measure, `∫ f < ∫ g`. -/
theorem exB8_integral_lt {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hle : ∀ᵐ θ ∂μ, f θ ≤ g θ) (hlt : 0 < μ {θ | f θ < g θ}) :
    ∫ θ, f θ ∂μ < ∫ θ, g θ ∂μ := by
  rw [← sub_pos, ← integral_sub hg hf]
  refine (integral_pos_iff_support_of_nonneg_ae (f := fun θ => g θ - f θ)
    (hle.mono fun θ h => sub_nonneg.2 h) (hg.sub hf)).2
    (hlt.trans_le (measure_mono fun θ hθ => ?_))
  exact sub_ne_zero.2 (ne_of_gt (hθ : f θ < g θ))

/-- **Exercise 13.B.8, correction** (MWG, p. 474). In the adverse selection model of Section 13.B
(positive density, `r` strictly increasing and continuous, `r(θ) ≤ θ`), at the highest-wage
competitive equilibrium no intervention `(w_e, b)` with a benefit depending on observed purchases
`x(θ)` is a budget-feasible Pareto improvement, whatever the function `x` (increasing or not)
and the schedule `b`. The printed claim is therefore false in this model. -/
theorem exercise_13_B_8_false {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (x b : ℝ → ℝ) (we : ℝ) :
    ¬ (XBudgetOK μ r x we b ∧ IsXParetoImprovement μ θl θh r x ws we b) := by
  rintro ⟨⟨hint, hbud⟩, hall, hS⟩
  have hd := h.dist
  have := hd.prob
  set S := {θ | max ws (r θ) < max we (r θ + b (x θ))} with hSdef
  have hSI : 0 < μ (S ∩ Set.Icc θl θh) := by rwa [measure_acceptSet_inter hd]
  rcases le_or_gt we ws with hwe | hwe
  · -- `w_e ≤ w*`: the net revenue is at most the equilibrium profit integrand
    have hP0 : firmProfit μ r ws = 0 := by
      rcases eq_zero_or_pos (μ (acceptSet r ws)) with h0 | hpos
      · exact firmProfit_of_null h.meas h0
      · exact (mem_eqWages_iff_profit hd h.meas hpos).1 hmax.1
    set g := (acceptSet r ws).indicator (fun θ => θ - ws) with hgdef
    have hg : Integrable g μ :=
      (hd.integrable_id.sub (integrable_const ws)).indicator (measurableSet_acceptSet h.meas ws)
    have hpt : ∀ θ ∈ Set.Icc θl θh,
        xNetRev r x we b θ ≤ g θ ∧ (θ ∈ S → xNetRev r x we b θ < g θ) := by
      intro θ hθ
      have hP := hall θ hθ
      unfold xNetRev
      split_ifs with hemp
      · rw [max_eq_left hemp] at hP
        have hrθ : r θ ≤ ws := (le_max_right _ _).trans (hP.trans hwe)
        have hgθ : g θ = θ - ws := Set.indicator_of_mem (show θ ∈ acceptSet r ws from hrθ) _
        refine ⟨by rw [hgθ]; linarith [(le_max_left ws (r θ)).trans hP], fun hθS => ?_⟩
        have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
        rw [max_eq_left hemp] at hs
        linarith [le_max_left ws (r θ)]
      · rw [not_le] at hemp
        rw [max_eq_right hemp.le] at hP
        by_cases hacc : r θ ≤ ws
        · have hgθ : g θ = θ - ws := Set.indicator_of_mem (show θ ∈ acceptSet r ws from hacc) _
          rw [max_eq_left hacc] at hP
          have hrle := h.le θ hθ
          refine ⟨by rw [hgθ]; linarith, fun hθS => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_left hacc] at hs
          rw [hgθ]; linarith
        · rw [not_le] at hacc
          have hgθ : g θ = 0 :=
            Set.indicator_of_notMem (show θ ∉ acceptSet r ws from not_le.2 hacc) _
          rw [max_eq_right hacc.le] at hP
          refine ⟨by rw [hgθ]; linarith, fun hθS => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_right hacc.le] at hs
          rw [hgθ]; linarith
    have hlt := exB8_integral_lt hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
      (hSI.trans_le (measure_mono fun θ hθ => (hpt θ hθ.2).2 hθ.1))
    have hg0 : ∫ θ, g θ ∂μ = 0 := hP0
    linarith
  · -- `w_e > w*`: the net revenue is at most the profit integrand at `w_e`
    set g := (acceptSet r we).indicator (fun θ => θ - we) with hgdef
    have hg : Integrable g μ :=
      (hd.integrable_id.sub (integrable_const we)).indicator (measurableSet_acceptSet h.meas we)
    have hpt : ∀ θ ∈ Set.Icc θl θh, xNetRev r x we b θ ≤ g θ ∧
        (θ ∈ S → θ ∉ acceptSet r we → xNetRev r x we b θ < g θ) := by
      intro θ hθ
      have hP := hall θ hθ
      unfold xNetRev
      split_ifs with hemp
      · rw [max_eq_left hemp] at hP
        have hrθ : r θ ≤ we := (le_max_right _ _).trans hP
        have hm : θ ∈ acceptSet r we := hrθ
        exact ⟨(Set.indicator_of_mem hm (fun θ => θ - we)).ge, fun _ hn => absurd hm hn⟩
      · rw [not_le] at hemp
        rw [max_eq_right hemp.le] at hP
        by_cases hacc : r θ ≤ we
        · have hgθ : g θ = θ - we := Set.indicator_of_mem (show θ ∈ acceptSet r we from hacc) _
          have hrle := h.le θ hθ
          exact ⟨by rw [hgθ]; linarith, fun _ hn => absurd hacc hn⟩
        · rw [not_le] at hacc
          have hgθ : g θ = 0 :=
            Set.indicator_of_notMem (show θ ∉ acceptSet r we from not_le.2 hacc) _
          rw [max_eq_right (hwe.trans hacc).le] at hP
          refine ⟨by rw [hgθ]; linarith, fun hθS _ => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_right (hwe.trans hacc).le] at hs
          rw [hgθ]; linarith
    have hle : ∫ θ, xNetRev r x we b θ ∂μ ≤ ∫ θ, g θ ∂μ :=
      integral_mono_ae hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
    have hgP : ∫ θ, g θ ∂μ = firmProfit μ r we := rfl
    rcases eq_zero_or_pos (μ (acceptSet r we)) with h0 | hpos
    · rw [hgP, firmProfit_of_null h.meas h0] at hle
      have hD : 0 < μ ((S ∩ Set.Icc θl θh) \ acceptSet r we) := by
        rwa [measure_sdiff_null h0]
      have hlt := exB8_integral_lt hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
        (hD.trans_le (measure_mono fun θ hθ => (hpt θ hθ.1.2).2 hθ.1.1 hθ.2))
      rw [hgP, firmProfit_of_null h.meas h0] at hlt
      linarith
    · have hneg := h.toMono.firmProfit_neg_of_gt_max hmax hwe hpos
      linarith

/-- **Exercise 13.B.8** (MWG, p. 474), corrected. Let `x` be injective on `[θ̲, θ̄]` (e.g.
strictly increasing), so that the purchases of a worker at home reveal her type, and let `w*` be
a competitive equilibrium wage (for instance the highest one) at which a positive mass of
employed types is more productive at home (`r(θ) > θ`). Then the benefit `b(x(θ)) = w* - θ` for
exactly these types (and `0` otherwise), with `w_e = w*`, is a budget-feasible Pareto
improvement: the types sent home gain `r(θ) - θ > 0`, nobody else is affected, and the benefit
paid equals the net output `θ - w*` the authority no longer gets. -/
theorem exercise_13_B_8 {μ : Measure ℝ} {θl θh : ℝ} {r x : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) (hx : Set.InjOn x (Set.Icc θl θh)) {ws : ℝ}
    (hws : ws ∈ eqWages μ θl θh r) (hmis : 0 < μ (acceptSet r ws ∩ {θ | θ < r θ})) :
    ∃ b : ℝ → ℝ, XBudgetOK μ r x ws b ∧ IsXParetoImprovement μ θl θh r x ws ws b := by
  classical
  have := hd.prob
  set Q := acceptSet r ws ∩ {θ | θ < r θ} ∩ Set.Icc θl θh with hQ
  have hQsub : Q ⊆ Set.Icc θl θh := Set.inter_subset_right
  set b : ℝ → ℝ := fun y =>
    if y ∈ x '' Q then ws - Function.invFunOn x (Set.Icc θl θh) y else 0 with hbdef
  have hb : ∀ θ ∈ Set.Icc θl θh, b (x θ) = Q.indicator (fun θ => ws - θ) θ := by
    intro θ hθ
    by_cases hθQ : θ ∈ Q
    · simp only [hbdef, Set.mem_image_of_mem x hθQ, ↓reduceIte, hx.leftInvOn_invFunOn hθ,
        Set.indicator_of_mem hθQ]
    · have hn : x θ ∉ x '' Q := fun hm => hθQ ((hx.mem_image_iff hQsub hθ).1 hm)
      simp only [hbdef, hn, ↓reduceIte, Set.indicator_of_notMem hθQ]
  have hpos : 0 < μ (acceptSet r ws) := hmis.trans_le (measure_mono Set.inter_subset_left)
  have hP0 : firmProfit μ r ws = 0 := (mem_eqWages_iff_profit hd hr hpos).1 hws
  set g := (acceptSet r ws).indicator (fun θ => θ - ws) with hgdef
  have hg : Integrable g μ :=
    (hd.integrable_id.sub (integrable_const ws)).indicator (measurableSet_acceptSet hr ws)
  have hnet : ∀ θ ∈ Set.Icc θl θh, xNetRev r x ws b θ = g θ := by
    intro θ hθ
    unfold xNetRev
    rw [hb θ hθ]
    by_cases hθQ : θ ∈ Q
    · have hacc : θ ∈ acceptSet r ws := hθQ.1.1
      have hlt : θ < r θ := hθQ.1.2
      rw [Set.indicator_of_mem hθQ, hgdef, Set.indicator_of_mem hacc]
      split_ifs with h1
      · exact absurd h1 (by linarith)
      · ring
    · rw [Set.indicator_of_notMem hθQ, add_zero]
      by_cases hacc : r θ ≤ ws
      · rw [hgdef, Set.indicator_of_mem (show θ ∈ acceptSet r ws from hacc)]
        split_ifs; rfl
      · rw [hgdef, Set.indicator_of_notMem (show θ ∉ acceptSet r ws from hacc)]
        split_ifs; simp
  have hae : g =ᵐ[μ] xNetRev r x ws b := hd.ae_mem.mono fun θ hθ => (hnet θ hθ).symm
  refine ⟨b, ⟨hg.congr hae, ?_⟩, fun θ hθ => ?_, ?_⟩
  · rw [← integral_congr_ae hae]
    exact hP0.ge
  · rw [hb θ hθ]
    by_cases hθQ : θ ∈ Q
    · rw [Set.indicator_of_mem hθQ, max_eq_left (hθQ.1.1 : r θ ≤ ws)]
      exact le_max_left _ _
    · rw [Set.indicator_of_notMem hθQ, add_zero]
  · refine (by rwa [hQ, measure_acceptSet_inter hd] : 0 < μ Q).trans_le
      (measure_mono fun θ hθQ => ?_)
    have hθ := hQsub hθQ
    have hlt : θ < r θ := hθQ.1.2
    have hs : max ws (r θ) < max ws (r θ + b (x θ)) := by
      rw [hb θ hθ, Set.indicator_of_mem hθQ, max_eq_left (hθQ.1.1 : r θ ≤ ws)]
      exact lt_max_of_lt_right (by linarith)
    exact hs

/-- **Exercise 13.B.8** (MWG, p. 474). An `x` that does not separate types does not help: if
`x` is constant, then at the highest-wage equilibrium of the `MonoModel` no intervention
`(w_e, b)` is a budget-feasible Pareto improvement (Proposition 13.B.2, Exercise 13.B.10). -/
theorem exercise_13_B_8_const_x {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    {x : ℝ → ℝ} {c : ℝ} (hx : ∀ θ, x θ = c) (we : ℝ) (b : ℝ → ℝ) :
    ¬ (XBudgetOK μ r x we b ∧ IsXParetoImprovement μ θl θh r x ws we b) := by
  rintro ⟨hB, hall, hS⟩
  have hfun : xNetRev r x we b = xNetRev r x we (fun _ => b c) := by
    funext θ; simp only [xNetRev, hx]
  have hB' : BudgetOK μ r we (b c) := by
    rw [← xBudgetOK_const_iff h.dist h.meas x, XBudgetOK, ← hfun]
    exact hB
  have hSI : 0 < μ ({θ | max ws (r θ) < max we (r θ + b (x θ))} ∩ Set.Icc θl θh) := by
    rwa [measure_acceptSet_inter h.dist]
  obtain ⟨θ1, hθ1S, hθ1⟩ := MeasureTheory.nonempty_of_measure_ne_zero hSI.ne'
  refine h.isConstrainedPO hmax we (b c) hB' ⟨fun θ hθ => ?_, θ1, hθ1, ?_⟩
  · have := hall θ hθ
    rwa [hx, add_comm] at this
  · have : max ws (r θ1) < max we (r θ1 + b (x θ1)) := hθ1S
    rwa [hx, add_comm] at this

/-- **Exercise 13.B.8**, instance (MWG, p. 474). Types uniform on `[0, 2]`, `r(θ) = θ/4 + 1/4`
(strictly increasing, `r(θ) > θ` for `θ < 1/3`), purchases `x(θ) = θ`. The highest equilibrium
wage is `w* = E[θ] = 1` (everybody works); it is a constrained Pareto optimum for the schemes
`(w_e, w_u)` of p. 446, but the authority observing `x` can Pareto improve on it. -/
theorem exercise_13_B_8_instance :
    IsGreatest (eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4) 1 ∧
      IsConstrainedPO (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) 1 ∧
      ∃ b : ℝ → ℝ, XBudgetOK (unifMeas 0 2) (fun θ => θ / 4 + 1 / 4) id 1 b ∧
        IsXParetoImprovement (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) id 1 1 b := by
  have hd : TypeDist (unifMeas 0 2) 0 2 := unifMeas_typeDist le_rfl two_pos
  have hM : MonoModel (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) :=
    ⟨hd, unifMeas_density two_pos, (measurable_id.div_const 4).add_const _,
      fun a _ b _ hab => by linarith, by fun_prop⟩
  have hE : meanType (unifMeas 0 2) = 1 := by rw [unifMeas_mean two_pos]; norm_num
  have hsub : ∀ w, 3 / 4 ≤ w → Set.Icc (0 : ℝ) 2 ⊆ acceptSet (fun θ => θ / 4 + 1 / 4) w :=
    fun w hw θ hθ => by change θ / 4 + 1 / 4 ≤ w; linarith [hθ.2]
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4 := by
    have := mean_mem_eqWages hd (hE ▸ hsub 1 (by norm_num))
    rwa [hE] at this
  have hmax : IsGreatest (eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4) 1 := by
    refine ⟨h1, fun w hw => ?_⟩
    by_contra hw1
    rw [not_le] at hw1
    rw [mem_eqWages_iff, condMean_of_superset hd (hsub w (by linarith)), hE] at hw
    linarith
  refine ⟨hmax, hM.isConstrainedPO hmax, exercise_13_B_8 hd hM.meas (Set.injOn_id _) h1 ?_⟩
  refine ((unifMeas_density two_pos).pos 0 (1 / 4) le_rfl (by norm_num)
    (by norm_num)).trans_le (measure_mono fun θ hθ => ⟨?_, ?_⟩)
  · change θ / 4 + 1 / 4 ≤ 1; linarith [hθ.2]
  · change θ < θ / 4 + 1 / 4; linarith [hθ.2]

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.B.9: positive selection with two types

MWG, Section 13.B, Exercise 13.B.9, p. 474. Two types `θ_H > θ_L ≥ 0`, `Prob(θ = θ_H) = λ`
(`twoPt λ θ_L θ_H`), `r` strictly decreasing. Interventions, budget, Pareto improvement and
constrained Pareto optimality are those of `Constrained.lean`. (`IsParetoImprovement` quantifies
over all of `[θ_L, θ_H]`; the intermediate types have probability zero, and with `r` decreasing
the results below do not depend on them.)

* `exercise_13_B_9_exact`: a full-employment equilibrium (`r(θ_L) ≤ E[θ]`, wage `E[θ]`) is a
  constrained Pareto optimum iff `r(θ_L) ≤ θ_L`. The proof of the hard direction goes through
  Exercise 13.B.7: a Pareto improvement must reduce employment, hence there is one of the form
  `(E[θ], ŵ_u)`, and the budget then gives `ŵ_u ≤ E[θ] - θ_L`. Under the exercise's assumption
  `r(θ_L) > θ_L` the full-employment equilibrium is therefore never constrained optimal.
* `exercise_13_B_9`: the hint's case `E[θ] = r(θ_L)` (types `1`, `3`, `λ = 1/2`,
  `r(θ) = (5 - θ)/2`): the highest-wage equilibrium `w* = 2` is not a constrained Pareto
  optimum; a small unemployment benefit (`ŵ_u = 1/2`) Pareto improves on it.
* `exercise_13_B_9_cpo_instance`: an instance of the other side (`r(θ_L) = θ_L`).
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.9** (MWG, p. 474). The two-type distribution: `θ_H` with probability `λ`,
`θ_L` with probability `1 - λ`. -/
noncomputable def twoPt (lam θL θH : ℝ) : Measure ℝ :=
  ENNReal.ofReal lam • Measure.dirac θH + ENNReal.ofReal (1 - lam) • Measure.dirac θL

/-- Integrals against the two-type distribution. -/
theorem integral_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (f : ℝ → ℝ) :
    ∫ θ, f θ ∂twoPt lam θL θH = lam * f θH + (1 - lam) * f θL := by
  rw [twoPt, integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (sub_nonneg.2 h1), smul_eq_mul]

/-- The two-type distribution satisfies the standing assumptions. -/
theorem twoPt_typeDist {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hL : 0 ≤ θL)
    (hLH : θL < θH) : TypeDist (twoPt lam θL θH) θL θH where
  nonneg := hL
  lt := hLH
  prob := ⟨by
    simp only [twoPt, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]
    simp⟩
  supp := by
    simp only [twoPt, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
      Measure.dirac_apply' _ measurableSet_Icc.compl]
    simp [hLH.le]

/-- `E[θ] = λ θ_H + (1 - λ) θ_L`. -/
theorem meanType_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    meanType (twoPt lam θL θH) = lam * θH + (1 - lam) * θL :=
  integral_twoPt h0 h1 _

/-- The profit of a firm paying `w` in the two-type model. -/
theorem firmProfit_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : ℝ → ℝ) (w : ℝ) :
    firmProfit (twoPt lam θL θH) r w =
      lam * (acceptSet r w).indicator (fun θ => θ - w) θH +
        (1 - lam) * (acceptSet r w).indicator (fun θ => θ - w) θL :=
  integral_twoPt h0 h1 _

/-- **Exercise 13.B.9** (MWG, p. 474), the exact condition (via Exercise 13.B.7). In the
two-type positive selection model (`r` strictly decreasing), if `r(θ_L) ≤ E[θ]` then
`w* = E[θ]` is a competitive equilibrium wage with full employment, and it is a constrained
Pareto optimum iff `r(θ_L) ≤ θ_L`. -/
theorem exercise_13_B_9_exact {lam θL θH : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hL : 0 ≤ θL)
    (hLH : θL < θH) {r : ℝ → ℝ} (hr : Measurable r) (hanti : StrictAntiOn r (Set.Icc θL θH))
    (hfull : r θL ≤ meanType (twoPt lam θL θH)) :
    meanType (twoPt lam θL θH) ∈ eqWages (twoPt lam θL θH) θL θH r ∧
      (IsConstrainedPO (twoPt lam θL θH) θL θH r (meanType (twoPt lam θL θH)) ↔
        r θL ≤ θL) := by
  have hd := twoPt_typeDist hl0.le hl1.le hL hLH
  have hE := meanType_twoPt (θL := θL) (θH := θH) hl0.le hl1.le
  set E := meanType (twoPt lam θL θH)
  have hLi : θL ∈ Set.Icc θL θH := ⟨le_rfl, hLH.le⟩
  have hHi : θH ∈ Set.Icc θL θH := ⟨hLH.le, le_rfl⟩
  have hrHL : r θH < r θL := hanti hLi hHi hLH
  have hrle : ∀ θ ∈ Set.Icc θL θH, r θ ≤ r θL := fun θ hθ => hanti.antitoneOn hLi hθ hθ.1
  have hIccE : Set.Icc θL θH ⊆ acceptSet r E := fun θ hθ => (hrle θ hθ).trans hfull
  refine ⟨mean_mem_eqWages hd hIccE, ⟨fun hcpo => ?_, fun hLle => ?_⟩⟩
  · -- if `r(θ_L) > θ_L`, a small unemployment benefit Pareto improves
    by_contra hgt
    rw [not_le] at hgt
    set u := min (E - θL) (E - r θH) with hu
    have hu1 : E - r θL < u := lt_min (by linarith) (by linarith)
    have hu2 : u ≤ E - θL := min_le_left _ _
    have hu3 : u ≤ E - r θH := min_le_right _ _
    have hH : θH ∈ acceptSet r (E - u) := by change r θH ≤ E - u; linarith
    have hLn : θL ∉ acceptSet r (E - u) := fun h => by
      have : r θL ≤ E - u := h
      linarith
    refine hcpo E u ?_ ⟨fun θ _ => max_le_max le_rfl (by linarith), θL, hLi, ?_⟩
    · rw [budgetOK_iff hd hr, firmProfit_twoPt hl0.le hl1.le,
        Set.indicator_of_mem hH, Set.indicator_of_notMem hLn, mul_zero, add_zero]
      have h1 : 0 < 1 - lam := by linarith
      nlinarith
    · rw [max_eq_left hfull]
      exact lt_max_of_lt_right (by linarith)
  · intro we wu hb hpi
    by_cases hfI : Set.Icc θL θH ⊆ acceptSet r (we - wu)
    · -- everybody works: nobody can be paid more than `E[θ]`
      have hwu := (budgetOK_iff hd hr).1 hb
      rw [firmProfit_of_full hd hr hfI] at hwu
      obtain ⟨-, θ1, hθ1, hs⟩ := hpi
      rw [exB7_pay_emp (hfI hθ1)] at hs
      linarith [le_max_left E (r θ1)]
    · -- the intervention reduces employment: use Exercise 13.B.7
      rw [Set.not_subset] at hfI
      obtain ⟨θ0, hθ0, hθ0n⟩ := hfI
      have hred : ReducesEmployment θL θH r E we wu :=
        exB7_reduces_of hθ0 (not_le.1 hθ0n) ((hrle θ0 hθ0).trans hfull)
      obtain ⟨u, hu0, hb', ⟨-, θ1, hθ1, hs⟩, hred'⟩ :=
        (exercise_13_B_7_reduce hd hr E).1 ⟨we, wu, hb, hpi, hred⟩
      obtain ⟨θ2, hθ2, h21, -⟩ := exB7_reduces_exists hred'
      have hLn : θL ∉ acceptSet r (E - u) := fun h => by
        have : r θL ≤ E - u := h
        linarith [hrle θ2 hθ2]
      have hP := (budgetOK_iff hd hr).1 hb'
      rw [firmProfit_twoPt hl0.le hl1.le, Set.indicator_of_notMem hLn, mul_zero,
        add_zero] at hP
      have hu : u ≤ E - θL := by
        by_cases hH : θH ∈ acceptSet r (E - u)
        · rw [Set.indicator_of_mem hH] at hP
          have h1 : 0 < 1 - lam := by linarith
          nlinarith
        · rw [Set.indicator_of_notMem hH, mul_zero] at hP
          linarith
      have h1 : u + r θ1 ≤ E := by linarith [hrle θ1 hθ1]
      rw [max_eq_left h1] at hs
      exact absurd hs (not_lt.2 (le_max_left _ _))

/-- **Exercise 13.B.9** (MWG, p. 474). The highest-wage competitive equilibrium need not be a
constrained Pareto optimum. Types `θ_L = 1`, `θ_H = 3`, `λ = 1/2`, `r(θ) = (5 - θ)/2`
(strictly decreasing, `r(θ_H) = 1 < θ_H`, `r(θ_L) = 2 > θ_L`, and `E[θ] = 2 = r(θ_L)` as in the
hint): `w* = 2` is the highest equilibrium wage, and the intervention `(w*, ŵ_u) = (2, 1/2)`
(a small unemployment benefit, which sends `θ_L` home) is budget-feasible and Pareto
improving. -/
theorem exercise_13_B_9 :
    StrictAntiOn (fun θ : ℝ => (5 - θ) / 2) (Set.Icc 1 3) ∧
      (5 - 3) / 2 < (3 : ℝ) ∧ (1 : ℝ) < (5 - 1) / 2 ∧
      meanType (twoPt (1 / 2) 1 3) = (5 - 1) / 2 ∧
      IsGreatest (eqWages (twoPt (1 / 2) 1 3) 1 3 fun θ => (5 - θ) / 2) 2 ∧
      BudgetOK (twoPt (1 / 2) 1 3) (fun θ => (5 - θ) / 2) 2 (1 / 2) ∧
      IsParetoImprovement 1 3 (fun θ => (5 - θ) / 2) 2 2 (1 / 2) ∧
      ¬ IsConstrainedPO (twoPt (1 / 2) 1 3) 1 3 (fun θ => (5 - θ) / 2) 2 := by
  have hanti : StrictAntiOn (fun θ : ℝ => (5 - θ) / 2) (Set.Icc 1 3) :=
    fun a _ b _ hab => by simp only; linarith
  have hmeas : Measurable fun θ : ℝ => (5 - θ) / 2 :=
    (measurable_const.sub measurable_id).div_const 2
  have hd := twoPt_typeDist (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num) (by norm_num)
    zero_le_one (by norm_num)
  have hE : meanType (twoPt (1 / 2) 1 3) = 2 := by
    rw [meanType_twoPt (by norm_num) (by norm_num)]; norm_num
  have hex := exercise_13_B_9_exact (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) hmeas hanti (by rw [hE]; norm_num)
  rw [hE] at hex
  have hH : (3 : ℝ) ∈ acceptSet (fun θ : ℝ => (5 - θ) / 2) (2 - 1 / 2) := by
    change (5 - 3) / 2 ≤ (2 : ℝ) - 1 / 2; norm_num
  have hLn : (1 : ℝ) ∉ acceptSet (fun θ : ℝ => (5 - θ) / 2) (2 - 1 / 2) := fun h => by
    have : (5 - 1) / 2 ≤ (2 : ℝ) - 1 / 2 := h
    norm_num at this
  refine ⟨hanti, by norm_num, by norm_num, by rw [hE]; norm_num, ⟨hex.1, fun w hw => ?_⟩, ?_,
    ⟨fun θ _ => max_le_max le_rfl (by linarith), 1, ⟨le_rfl, by norm_num⟩, by norm_num⟩,
    fun h => absurd (hex.2.1 h) (by norm_num)⟩
  · by_contra hw2
    rw [not_le] at hw2
    have hsub : Set.Icc (1 : ℝ) 3 ⊆ acceptSet (fun θ : ℝ => (5 - θ) / 2) w := fun θ hθ => by
      change (5 - θ) / 2 ≤ w; linarith [hθ.1]
    rw [mem_eqWages_iff, condMean_of_superset hd hsub, hE] at hw
    linarith
  · rw [budgetOK_iff hd hmeas, firmProfit_twoPt (by norm_num) (by norm_num),
      Set.indicator_of_mem hH, Set.indicator_of_notMem hLn]
    norm_num

/-- **Exercise 13.B.9**, instance of the other side of the exact condition (MWG, p. 474). Types
`1`, `3` equally likely, `r(θ) = (3 - θ)/2` (`r(θ_L) = θ_L = 1`): the full-employment
equilibrium `w* = 2` is a constrained Pareto optimum. -/
theorem exercise_13_B_9_cpo_instance :
    IsConstrainedPO (twoPt (1 / 2) 1 3) 1 3 (fun θ => (3 - θ) / 2) 2 := by
  have hanti : StrictAntiOn (fun θ : ℝ => (3 - θ) / 2) (Set.Icc 1 3) :=
    fun a _ b _ hab => by simp only; linarith
  have hE : meanType (twoPt (1 / 2) 1 3) = 2 := by
    rw [meanType_twoPt (by norm_num) (by norm_num)]; norm_num
  have hex := exercise_13_B_9_exact (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) ((measurable_const.sub measurable_id).div_const 2)
    hanti (by rw [hE]; norm_num)
  rw [hE] at hex
  exact hex.2.2 (by norm_num)

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.B.6: Wilson's model with heterogeneous firms

MWG, Exercise 13.B.6, p. 474 (based on Wilson 1980).

Firms differ in productivity: in a firm of type `γ` a worker of type `θ` produces `γθ`; each
firm wants at most one worker; firm types have a density `g > 0` on `[0, ∞)` (`FirmDensity`,
which also assumes `g` continuous, as part (b) allows: "all relevant functions are
differentiable"). The `N` firms are a continuum of mass `N` (so that aggregate demand is the
number `N ∫ g` of firms that want to hire, as in the book's formula).

* (a) `exercise_13_B_6a`: firm `γ` hires iff `γμ ≥ w` (`wil_hire_best`), so
  `z(w, μ) = N ∫_{w/μ}^∞ g(γ) dγ = N (1 - ∫_0^{w/μ} g)`.
* (b) `exercise_13_B_6b`: `z*(w) = z(w, μ(w))` has derivative
  `N g(w/μ) (wμ' - μ)/μ²` at `w̃`, positive iff the elasticity `w̃ μ'(w̃)/μ(w̃)` exceeds `1` (and
  negative iff it is below `1`). "Strictly increasing at `w̃`" is read as `z*'(w̃) > 0`.
* (c) `exercise_13_B_6c`: with `μ(w) = E[θ | r(θ) ≤ w]` and supply `s(w) = F(Θ(w))`, if
  `w₁ < w₂` are competitive equilibria (`z*(wᵢ) = s(wᵢ)`) then `μ(w₁) ≤ μ(w₂)`,
  `w₂/μ(w₂) ≤ w₁/μ(w₁)`, every firm's profit `max(γμ - w, 0)` and every worker's payoff
  `max(w, r(θ))` is weakly higher at `w₂`, and strictly higher for every worker with
  `r(θ) < w₂` (a set containing `θ̲`): the highest-wage equilibrium Pareto dominates.
* (d) The game (`WilsonEconomy.offerPay`, `WilsonEconomy.IsSPNE`): firms simultaneously offer
  wages (or stay out), workers accept the highest offer that is at least `r(θ)`, with random
  rationing among applicants. At a market-clearing common wage `w`, a firm that deviates to
  `w' > w` is the unique highest bidder and hires a random applicant from `Θ(w')` (expected
  productivity `μ(w')`), earning `γμ(w') - w'`; a firm offering `w' < w` finds no applicant
  (every type accepting `w'` is employed at `w`). `exercise_13_B_6d_i`: an SPNE wage is the
  highest competitive equilibrium wage. `exercise_13_B_6d_ii_necessary`: the book's condition
  `z*(w) ≤ z*(w*)` for `w > w*` is necessary.

Correction. The converse in (ii) is false: high-`γ` firms, which value quality more, deviate
to a higher wage whenever it raises `μ`, whatever happens to `z*`
(`exercise_13_B_6d_ii_counterexample`). The correct statement
(`exercise_13_B_6d_ii_corrected`): a competitive equilibrium `w*` is an SPNE iff
`μ(w) ≤ μ(w*)` for all `w > w*`; this holds, in particular, when `w* ≥ r(θ̄)`
(`exercise_13_B_6d_ii_full_employment`).

Added regularity (`WilsonEconomy.Valid`): `θ̲ > 0` (so `μ > 0`), `r` monotone on `[θ̲, θ̄]` and
`r(θ̲) ≥ 0` (so equilibrium wages are nonnegative).
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.6** (MWG, p. 474). The firm types have a continuous density `g` with
`g(γ) > 0` for `γ ∈ [0, ∞)`. -/
structure FirmDensity (g : ℝ → ℝ) : Prop where
  cont : Continuous g
  pos : ∀ γ, 0 ≤ γ → 0 < g γ
  integrable : IntegrableOn g (Set.Ici 0)
  total : ∫ γ in Set.Ici 0, g γ = 1

/-- **Exercise 13.B.6(a)** (MWG, p. 474). The firm types that hire at wage `w` when the average
productivity of the workers is `m`: `γm ≥ w`. -/
def wilHireSet (w m : ℝ) : Set ℝ := {γ | 0 ≤ γ ∧ w ≤ γ * m}

/-- **Exercise 13.B.6(a)** (MWG, p. 474). The aggregate demand for labor `z(w, m)`: the mass of
firms that hire. -/
noncomputable def wilDemand (N : ℝ) (g : ℝ → ℝ) (w m : ℝ) : ℝ := N * ∫ γ in wilHireSet w m, g γ

/-- The tail `∫_x^∞ g`. -/
noncomputable def wilTail (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ γ in Set.Ici x, g γ

/-- **Exercise 13.B.6(a)** (MWG, p. 474). A firm of type `γ` hiring one worker of average
productivity `m` at wage `w` earns `γm - w`: hiring is a best choice iff `w ≤ γm`, not hiring
iff `γm ≤ w`. -/
theorem wil_hire_best (γ m w : ℝ) :
    ((0 : ℝ) * (γ * m - w) ≤ 1 * (γ * m - w) ↔ w ≤ γ * m) ∧
      ((1 : ℝ) * (γ * m - w) ≤ 0 * (γ * m - w) ↔ γ * m ≤ w) := by
  constructor <;> constructor <;> intro h <;> linarith

theorem wilHireSet_eq {w m : ℝ} (hm : 0 < m) (hw : 0 ≤ w) : wilHireSet w m = Set.Ici (w / m) := by
  ext γ
  simp only [wilHireSet, Set.mem_ofPred_eq, Set.mem_Ici, div_le_iff₀ hm]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    by_contra hγ
    rw [not_le] at hγ
    nlinarith

theorem measurableSet_wilHireSet (w m : ℝ) : MeasurableSet (wilHireSet w m) :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_const (measurable_id.mul_const m))

theorem wilTail_split {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    wilTail g x = (∫ γ in x..y, g γ) + wilTail g y := by
  have hI : IntegrableOn g (Set.Ici x) := hg.integrable.mono_set (Set.Ici_subset_Ici.2 hx)
  unfold wilTail
  rw [← Set.Ico_union_Ici_eq_Ici hxy,
    setIntegral_union (s := Set.Ico x y) (t := Set.Ici y)
      (Set.disjoint_left.2 fun t ht ht' => not_le.2 ht.2 ht') measurableSet_Ici
      (hI.mono_set Set.Ico_subset_Ici_self) (hI.mono_set (Set.Ici_subset_Ici.2 hxy)),
    intervalIntegral.integral_of_le hxy, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

theorem wilTail_lt {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    wilTail g y < wilTail g x := by
  rw [wilTail_split hg hx hxy.le]
  have := intervalIntegral.intervalIntegral_pos_of_pos_on (hg.cont.intervalIntegrable x y)
    (fun t ht => hg.pos t (hx.trans ht.1.le)) hxy
  linarith

theorem wilTail_anti {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    wilTail g y ≤ wilTail g x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (wilTail_lt hg hx h).le

theorem wilTail_nonneg {g : ℝ → ℝ} (hg : FirmDensity g) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ wilTail g x :=
  setIntegral_nonneg measurableSet_Ici fun γ hγ => (hg.pos γ (hx.trans hγ)).le

theorem wilTail_pos {g : ℝ → ℝ} (hg : FirmDensity g) {x : ℝ} (hx : 0 ≤ x) : 0 < wilTail g x :=
  (wilTail_nonneg hg (by linarith)).trans_lt (wilTail_lt hg hx (lt_add_one x))

/-- **Exercise 13.B.6(a)** (MWG, p. 474). For `μ > 0` and `w ≥ 0` the aggregate demand for labor
is `z(w, μ) = N ∫_{w/μ}^∞ g(γ) dγ = N (1 - ∫_0^{w/μ} g(γ) dγ)`. -/
theorem exercise_13_B_6a {N : ℝ} {g : ℝ → ℝ} (hg : FirmDensity g) {w m : ℝ} (hm : 0 < m)
    (hw : 0 ≤ w) :
    wilDemand N g w m = N * ∫ γ in Set.Ici (w / m), g γ ∧
      wilDemand N g w m = N * (1 - ∫ γ in (0 : ℝ)..(w / m), g γ) := by
  have h1 : wilDemand N g w m = N * wilTail g (w / m) := by
    rw [wilDemand, wilHireSet_eq hm hw]; rfl
  refine ⟨h1, ?_⟩
  have h2 := wilTail_split hg le_rfl (div_nonneg hw hm.le)
  rw [wilTail, hg.total] at h2
  rw [h1]
  congr 1
  linarith

/-- **Exercise 13.B.6(b)** (MWG, p. 474). If `μ(·)` is differentiable at `w̃ > 0` with
`μ(w̃) > 0`, then `z*(w) = z(w, μ(w))` has derivative `N g(w̃/μ) (w̃μ' - μ)/μ²` at `w̃`; it is
positive iff the elasticity `w̃μ'/μ` of `μ` exceeds `1`, and negative iff it is below `1`. -/
theorem exercise_13_B_6b {N : ℝ} {g μf : ℝ → ℝ} (hg : FirmDensity g) (hN : 0 < N) {w μ' : ℝ}
    (hw : 0 < w) (hμ : 0 < μf w) (hd : HasDerivAt μf μ' w) :
    HasDerivAt (fun x => wilDemand N g x (μf x))
        (N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2)) w ∧
      (0 < N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2) ↔ 1 < w * μ' / μf w) ∧
      (N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2) < 0 ↔ w * μ' / μf w < 1) := by
  have hev : (fun x => N * (1 - ∫ γ in (0 : ℝ)..(x / μf x), g γ)) =ᶠ[nhds w]
      fun x => wilDemand N g x (μf x) := by
    filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hμ), lt_mem_nhds hw] with x hx hx'
    exact ((exercise_13_B_6a hg hx hx'.le).2).symm
  have hq : HasDerivAt (fun x => x / μf x) ((1 * μf w - w * μ') / μf w ^ 2) w :=
    (hasDerivAt_id' w).div hd hμ.ne'
  have hG := (hg.cont.integral_hasStrictDerivAt 0 (w / μf w)).hasDerivAt.comp w hq
  have hz := (hG.const_sub 1).const_mul N
  have hgp : 0 < N * g (w / μf w) := mul_pos hN (hg.pos _ (div_nonneg hw.le hμ.le))
  have hsq : 0 < μf w ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (hz.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    field_simp
    ring
  · rw [one_lt_div hμ, mul_pos_iff_of_pos_left hgp, div_pos_iff_of_pos_right hsq, sub_pos]
  · rw [div_lt_one hμ]
    constructor
    · intro h
      by_contra hle
      rw [not_lt] at hle
      have : 0 ≤ (w * μ' - μf w) / μf w ^ 2 := div_nonneg (by linarith) hsq.le
      nlinarith
    · intro h
      have : (w * μ' - μf w) / μf w ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) hsq
      nlinarith

/-- **Exercise 13.B.6** (MWG, p. 474). The economy: `N` firms with type density `g`, the worker
type distribution `F` on `[θ̲, θ̄]` and home production `r`. -/
structure WilsonEconomy where
  N : ℝ
  g : ℝ → ℝ
  F : Measure ℝ
  θl : ℝ
  θh : ℝ
  r : ℝ → ℝ

namespace WilsonEconomy

/-- **Exercise 13.B.6(b)** (MWG, p. 474). `μ(w) = E[θ | r(θ) ≤ w]`. -/
noncomputable def mu (E : WilsonEconomy) (w : ℝ) : ℝ := condMean E.F E.θl E.θh (acceptSet E.r w)

/-- **Exercise 13.B.6(b)** (MWG, p. 474). The aggregate demand function `z*(w) = z(w, μ(w))`. -/
noncomputable def zstar (E : WilsonEconomy) (w : ℝ) : ℝ := wilDemand E.N E.g w (E.mu w)

/-- **Exercise 13.B.6(c)** (MWG, p. 474). The aggregate supply `s(w) = F(r⁻¹(w))`, the
probability of `Θ(w) = {θ : r(θ) ≤ w}`. -/
noncomputable def supply (E : WilsonEconomy) (w : ℝ) : ℝ := (E.F (acceptSet E.r w)).toReal

/-- **Exercise 13.B.6(c)** (MWG, p. 474). A competitive equilibrium wage: `z*(w*) = s(w*)`. -/
def IsCE (E : WilsonEconomy) (w : ℝ) : Prop := E.zstar w = E.supply w

/-- **Exercise 13.B.6** (MWG, p. 474). The assumptions: `g` a firm density, `N > 0`, `F` a type
distribution, and (added) `θ̲ > 0`, `r` measurable and monotone on `[θ̲, θ̄]` with
`r(θ̲) ≥ 0`. -/
structure Valid (E : WilsonEconomy) : Prop where
  firms : FirmDensity E.g
  N_pos : 0 < E.N
  dist : TypeDist E.F E.θl E.θh
  θl_pos : 0 < E.θl
  meas : Measurable E.r
  mono : MonotoneOn E.r (Set.Icc E.θl E.θh)
  r_nonneg : 0 ≤ E.r E.θl

variable {E : WilsonEconomy}

theorem Valid.mu_pos (hE : E.Valid) (w : ℝ) : 0 < E.mu w :=
  hE.θl_pos.trans_le (condMean_ge hE.dist _)

theorem Valid.zstar_eq (hE : E.Valid) {w : ℝ} (hw : 0 ≤ w) :
    E.zstar w = E.N * wilTail E.g (w / E.mu w) := by
  rw [zstar, wilDemand, wilHireSet_eq (hE.mu_pos w) hw]; rfl

/-- The demand for labor is always positive. -/
theorem Valid.zstar_pos (hE : E.Valid) (w : ℝ) : 0 < E.zstar w := by
  have hm := hE.mu_pos w
  set c := max (w / E.mu w) 0
  have hsub : Set.Ici c ⊆ wilHireSet w (E.mu w) := fun γ hγ =>
    ⟨(le_max_right _ _).trans hγ, (div_le_iff₀ hm).1 ((le_max_left _ _).trans hγ)⟩
  have hI : IntegrableOn E.g (wilHireSet w (E.mu w)) :=
    hE.firms.integrable.mono_set fun γ hγ => hγ.1
  have hle := setIntegral_mono_set hI
    ((ae_restrict_iff' (measurableSet_wilHireSet _ _)).2
      (Filter.Eventually.of_forall fun γ hγ => (hE.firms.pos γ hγ.1).le))
    hsub.eventuallyLE
  have hpos : 0 < wilTail E.g c := wilTail_pos hE.firms (le_max_right _ _)
  unfold wilTail at hpos
  exact mul_pos hE.N_pos (hpos.trans_le hle)

/-- In a competitive equilibrium `w* ≥ r(θ̲)`: some types in `[θ̲, θ̄]` accept `w*`. -/
theorem Valid.ce_ge (hE : E.Valid) {w : ℝ} (h : E.IsCE w) : E.r E.θl ≤ w := by
  have hs : 0 < E.supply w := h ▸ hE.zstar_pos w
  have hpos : E.F (acceptSet E.r w) ≠ 0 := fun h0 => by simp [supply, h0] at hs
  obtain ⟨θ, hθA, hθI⟩ : (acceptSet E.r w ∩ Set.Icc E.θl E.θh).Nonempty := by
    by_contra hne
    exact hpos (measure_mono_null (fun θ hθ hθI => hne ⟨θ, hθ, hθI⟩) hE.dist.supp)
  exact (hE.mono ⟨le_rfl, hE.dist.lt.le⟩ hθI hθI.1).trans hθA

theorem Valid.ce_nonneg (hE : E.Valid) {w : ℝ} (h : E.IsCE w) : 0 ≤ w :=
  hE.r_nonneg.trans (hE.ce_ge h)

theorem Valid.supply_mono (hE : E.Valid) {w w' : ℝ} (hww : w ≤ w') :
    E.supply w ≤ E.supply w' := by
  have := hE.dist.prob
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun θ hθ => le_trans hθ hww)

/-- **Exercise 13.B.6(c)** (MWG, p. 474). If `w₁ < w₂` are competitive equilibrium wages, then
`μ(w₁) ≤ μ(w₂)` and `w₂/μ(w₂) ≤ w₁/μ(w₁)`; every firm's profit `max(γμ - w, 0)` and every
worker's payoff `max(w, r(θ))` is at least as high at `w₂`, and strictly higher for each worker
with `r(θ) < w₂`, in particular for `θ̲`. So the highest-wage equilibrium Pareto dominates. -/
theorem exercise_13_B_6c (hE : E.Valid) {w₁ w₂ : ℝ} (h₁ : E.IsCE w₁) (h₂ : E.IsCE w₂)
    (hlt : w₁ < w₂) :
    E.mu w₁ ≤ E.mu w₂ ∧ w₂ / E.mu w₂ ≤ w₁ / E.mu w₁ ∧
      (∀ γ, max (γ * E.mu w₁ - w₁) 0 ≤ max (γ * E.mu w₂ - w₂) 0) ∧
      (∀ θ, max w₁ (E.r θ) ≤ max w₂ (E.r θ)) ∧
      (∀ θ, E.r θ < w₂ → max w₁ (E.r θ) < max w₂ (E.r θ)) ∧ E.r E.θl < w₂ := by
  have hw₁ := hE.ce_ge h₁
  have hw₁0 := hE.ce_nonneg h₁
  have hw₂0 : 0 ≤ w₂ := by linarith
  have hm₁ := hE.mu_pos w₁
  have hm₂ := hE.mu_pos w₂
  have hmu : E.mu w₁ ≤ E.mu w₂ :=
    condMean_acceptSet_mono hE.dist hE.meas hE.mono hw₁ hlt.le
  have hratio : w₂ / E.mu w₂ ≤ w₁ / E.mu w₁ := by
    by_contra hgt
    rw [not_le] at hgt
    have hT := wilTail_lt hE.firms (div_nonneg hw₁0 hm₁.le) hgt
    have hz : E.zstar w₂ < E.zstar w₁ := by
      rw [hE.zstar_eq hw₁0, hE.zstar_eq hw₂0]
      exact mul_lt_mul_of_pos_left hT hE.N_pos
    have hs := hE.supply_mono hlt.le
    rw [h₁, h₂] at hz
    linarith
  refine ⟨hmu, hratio, fun γ => ?_, fun θ => max_le_max hlt.le le_rfl,
    fun θ hθ => ?_, lt_of_le_of_lt hw₁ hlt⟩
  · rcases le_or_gt (γ * E.mu w₁ - w₁) 0 with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h.le]
      refine le_max_of_le_left ?_
      set a₁ := w₁ / E.mu w₁
      set a₂ := w₂ / E.mu w₂
      have e₁ : w₁ = a₁ * E.mu w₁ := by rw [div_mul_cancel₀ _ hm₁.ne']
      have e₂ : w₂ = a₂ * E.mu w₂ := by rw [div_mul_cancel₀ _ hm₂.ne']
      have hγ : a₁ ≤ γ := by
        by_contra hγ
        rw [not_le] at hγ
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hratio hm₂.le,
        mul_le_mul_of_nonneg_right hmu (sub_nonneg.2 hγ)]
  · rw [max_eq_left hθ.le]
    exact max_lt hlt hθ

/-- **Exercise 13.B.6(d)** (MWG, p. 474). The payoff of a firm of type `γ` that offers `w'` when
the other firms hire at the common market-clearing wage `w`: as the unique highest bidder
(`w' > w`) it hires a random applicant from `Θ(w')`; at `w' = w` it hires a random worker from
`Θ(w)`; below `w` no worker applies. Staying out gives `0`. -/
noncomputable def offerPay (E : WilsonEconomy) (γ w w' : ℝ) : ℝ :=
  if w < w' then γ * E.mu w' - w' else if w' = w then γ * E.mu w - w else 0

/-- **Exercise 13.B.6(d)** (MWG, p. 474). A (pure, common-wage) SPNE outcome of the wage-offer
game: the market clears at `w` (the firms with `γμ(w) ≥ w` hire, earning `max(γμ(w) - w, 0)`,
and all workers in `Θ(w)` are employed), and no firm gains by offering any other wage. Workers'
behaviour (accepting a highest offer that is at least `r(θ)`) is optimal by `worker_best`. -/
def IsSPNE (E : WilsonEconomy) (w : ℝ) : Prop :=
  E.IsCE w ∧ ∀ γ, 0 ≤ γ → ∀ w', E.offerPay γ w w' ≤ max (γ * E.mu w - w) 0

/-- If a higher wage `w'` attracts a better pool, a firm with a high enough `γ` gains by
offering it. -/
theorem Valid.deviation_of_mu_lt (hE : E.Valid) {w w' : ℝ} (hw : 0 ≤ w) (hww : w < w')
    (hμ : E.mu w < E.mu w') : ∃ γ, 0 ≤ γ ∧ max (γ * E.mu w - w) 0 < γ * E.mu w' - w' := by
  have hm' := hE.mu_pos w'
  set A := (w' - w) / (E.mu w' - E.mu w)
  set B := w' / E.mu w'
  have hA : 0 ≤ A := div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ B := div_nonneg (by linarith) hm'.le
  have eA : A * (E.mu w' - E.mu w) = w' - w := div_mul_cancel₀ _ (by linarith)
  have eB : B * E.mu w' = w' := div_mul_cancel₀ _ hm'.ne'
  refine ⟨A + B + 1, by linarith, max_lt ?_ ?_⟩
  · nlinarith [mul_nonneg hA hm'.le]
  · nlinarith [mul_nonneg hB (by linarith : (0 : ℝ) ≤ E.mu w' - E.mu w)]

/-- **Exercise 13.B.6(d)(i)** (MWG, p. 474). Only the highest-wage competitive equilibrium can
be an SPNE outcome: an SPNE wage is a competitive equilibrium wage at least as high as every
other one. -/
theorem exercise_13_B_6d_i (hE : E.Valid) {w : ℝ} (hw : E.IsSPNE w) :
    IsGreatest {x | E.IsCE x} w := by
  refine ⟨hw.1, fun w' hw' => ?_⟩
  by_contra hlt
  rw [Set.mem_ofPred_eq, not_le] at *
  obtain ⟨hmu, hratio, -⟩ := exercise_13_B_6c hE hw.1 hw' hlt
  have hw0 := hE.ce_nonneg hw.1
  rcases eq_or_lt_of_le hmu with heq | hμlt
  · rw [← heq] at hratio
    have := (div_le_div_iff_of_pos_right (hE.mu_pos w)).1 hratio
    linarith
  · obtain ⟨γ, hγ, hdev⟩ := hE.deviation_of_mu_lt hw0 hlt hμlt
    have := hw.2 γ hγ w'
    simp only [offerPay, hlt, ↓reduceIte] at this
    linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), the true direction: if `w*` is an SPNE outcome then
`z*(w) ≤ z*(w*)` for all `w > w*` (otherwise a firm with `w/μ(w) < γ < w*/μ(w*)`, idle at `w*`,
profits from offering `w`). -/
theorem exercise_13_B_6d_ii_necessary (hE : E.Valid) {ws : ℝ} (h : E.IsSPNE ws) {w : ℝ}
    (hw : ws < w) : E.zstar w ≤ E.zstar ws := by
  by_contra hgt
  rw [not_le] at hgt
  have hws0 := hE.ce_nonneg h.1
  have hw0 : 0 ≤ w := by linarith
  have hm := hE.mu_pos w
  have hms := hE.mu_pos ws
  have hr : w / E.mu w < ws / E.mu ws := by
    by_contra hle
    rw [not_lt] at hle
    have hT := wilTail_anti hE.firms (div_nonneg hws0 hms.le) hle
    rw [hE.zstar_eq hw0, hE.zstar_eq hws0] at hgt
    nlinarith [hE.N_pos]
  set γ := (w / E.mu w + ws / E.mu ws) / 2
  have hγ0 : 0 ≤ γ := by
    have := div_nonneg hw0 hm.le
    have := div_nonneg hws0 hms.le
    positivity
  have h1 : 0 < γ * E.mu w - w := by
    have : w / E.mu w < γ := by simp only [γ]; linarith
    rw [div_lt_iff₀ hm] at this
    linarith
  have h2 : γ * E.mu ws - ws < 0 := by
    have : γ < ws / E.mu ws := by simp only [γ]; linarith
    rw [lt_div_iff₀ hms] at this
    linarith
  have := h.2 γ hγ0 w
  simp only [offerPay, hw, ↓reduceIte] at this
  rw [max_eq_right h2.le] at this
  linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), corrected statement: a competitive equilibrium wage
`w*` is an SPNE outcome iff no higher wage attracts a better pool: `μ(w) ≤ μ(w*)` for all
`w > w*`. -/
theorem exercise_13_B_6d_ii_corrected (hE : E.Valid) {ws : ℝ} (hce : E.IsCE ws) :
    E.IsSPNE ws ↔ ∀ w, ws < w → E.mu w ≤ E.mu ws := by
  have hws0 := hE.ce_nonneg hce
  constructor
  · intro h w hw
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨γ, hγ, hdev⟩ := hE.deviation_of_mu_lt hws0 hw hlt
    have := h.2 γ hγ w
    simp only [offerPay, hw, ↓reduceIte] at this
    linarith
  · intro hmu
    refine ⟨hce, fun γ hγ w' => ?_⟩
    unfold offerPay
    split_ifs with h1 h2
    · have := mul_le_mul_of_nonneg_left (hmu w' h1) hγ
      exact le_max_of_le_left (by linarith)
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474): a competitive equilibrium at which every type works
(`w* ≥ r(θ̄)`) is an SPNE outcome. -/
theorem exercise_13_B_6d_ii_full_employment (hE : E.Valid) {ws : ℝ} (hce : E.IsCE ws)
    (hfull : E.r E.θh ≤ ws) : E.IsSPNE ws := by
  have hall : ∀ w, ws ≤ w → E.mu w = meanType E.F := fun w hw =>
    condMean_of_superset hE.dist fun θ hθ =>
      ((hE.mono hθ ⟨hE.dist.lt.le, le_rfl⟩ hθ.2).trans hfull).trans hw
  refine (exercise_13_B_6d_ii_corrected hE hce).2 fun w hw => ?_
  rw [hall w hw.le, hall ws le_rfl]

end WilsonEconomy

/-! ### Concrete instances -/

/-- The exponential density `g(γ) = e^{-γ}`. -/
theorem expDensity : FirmDensity fun γ => Real.exp (-γ) where
  cont := Real.continuous_exp.comp continuous_neg
  pos γ _ := Real.exp_pos _
  integrable := (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi 0)
  total := by rw [integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi_zero]

theorem wilTail_exp (x : ℝ) : wilTail (fun γ => Real.exp (-γ)) x = Real.exp (-x) := by
  rw [wilTail, integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]

/-- Home production `r(θ) = 0` for `θ ≤ 3/2` and `R` above. -/
noncomputable def stepR (R : ℝ) (θ : ℝ) : ℝ := if θ ≤ 3 / 2 then 0 else R

/-- **Exercise 13.B.6**, the economy of the instances: types uniform on `[1, 2]`, home
production `stepR R`, firm density `e^{-γ}`, mass `N` of firms. -/
noncomputable def stepEconomy (N R : ℝ) : WilsonEconomy where
  N := N
  g := fun γ => Real.exp (-γ)
  F := unifMeas 1 2
  θl := 1
  θh := 2
  r := stepR R

theorem stepEconomy_valid {N R : ℝ} (hN : 0 < N) (hR : 0 ≤ R) : (stepEconomy N R).Valid where
  firms := expDensity
  N_pos := hN
  dist := unifMeas_typeDist zero_le_one one_lt_two
  θl_pos := one_pos
  meas := Measurable.ite measurableSet_Iic measurable_const measurable_const
  mono := by
    intro a _ b _ hab
    change stepR R a ≤ stepR R b
    unfold stepR
    split_ifs with h1 h2 <;> first | exact le_rfl | exact hR | linarith
  r_nonneg := by
    change (0 : ℝ) ≤ stepR R 1
    unfold stepR
    norm_num

theorem stepR_accept_low {R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    acceptSet (stepR R) w = Set.Iic (3 / 2) := by
  ext θ
  by_cases h : θ ≤ 3 / 2
  · simp [acceptSet, stepR, h, hw]
  · simp [acceptSet, stepR, h, not_le.2 hwR]

theorem stepR_accept_high {R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    acceptSet (stepR R) w = Set.univ := by
  ext θ
  by_cases h : θ ≤ 3 / 2 <;> simp [acceptSet, stepR, h, hw, hRw]

theorem stepEconomy_mu_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).mu w = 5 / 4 := by
  change condMean (unifMeas 1 2) 1 2 (acceptSet (stepR R) w) = 5 / 4
  rw [stepR_accept_low hw hwR, exB_unif_condMean_Iic one_lt_two (by norm_num) (by norm_num)]
  norm_num

theorem stepEconomy_mu_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).mu w = 3 / 2 := by
  change condMean (unifMeas 1 2) 1 2 (acceptSet (stepR R) w) = 3 / 2
  rw [stepR_accept_high hw hRw, condMean_of_superset (unifMeas_typeDist zero_le_one one_lt_two)
    (Set.subset_univ _), unifMeas_mean one_lt_two]
  norm_num

theorem stepEconomy_supply_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).supply w = 1 / 2 := by
  change (unifMeas 1 2 (acceptSet (stepR R) w)).toReal = 1 / 2
  rw [stepR_accept_low hw hwR, unifMeas_Iic one_lt_two (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem stepEconomy_supply_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).supply w = 1 := by
  have := unifMeas_isProb (a := 1) (b := 2) one_lt_two
  change (unifMeas 1 2 (acceptSet (stepR R) w)).toReal = 1
  rw [stepR_accept_high hw hRw, measure_univ, ENNReal.toReal_one]

theorem stepEconomy_zstar_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).zstar w = N * Real.exp (-(4 / 5 * w)) := by
  rw [WilsonEconomy.zstar, stepEconomy_mu_low hw hwR, wilDemand, wilHireSet_eq (by norm_num) hw]
  change N * wilTail (fun γ => Real.exp (-γ)) (w / (5 / 4)) = _
  rw [wilTail_exp]
  congr 2
  ring

theorem stepEconomy_zstar_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).zstar w = N * Real.exp (-(2 / 3 * w)) := by
  rw [WilsonEconomy.zstar, stepEconomy_mu_high hw hRw, wilDemand,
    wilHireSet_eq (by norm_num) hw]
  change N * wilTail (fun γ => Real.exp (-γ)) (w / (3 / 2)) = _
  rw [wilTail_exp]
  congr 2
  ring

theorem exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log two_pos, one_div]

theorem log_two_bounds : 0 < Real.log 2 ∧ Real.log 2 < 6 / 5 :=
  ⟨Real.log_pos one_lt_two, (Real.log_le_sub_one_of_pos two_pos).trans_lt (by norm_num)⟩

/-- **Exercise 13.B.6(b)**, instances (MWG, p. 474). In `stepEconomy (e⁶) 9`, `μ` is constant
(`5/4`) near `w̃ = 1`: elasticity `0 < 1`, and `z*` is decreasing there. With `μ(w) = w²`
(elasticity `2 > 1`) and `g(γ) = e^{-γ}`, `z*` is increasing at `w̃ = 1`. -/
theorem exercise_13_B_6b_instance :
    HasDerivAt (fun x => wilDemand (Real.exp 6) (fun γ => Real.exp (-γ)) x
        ((stepEconomy (Real.exp 6) 9).mu x))
      (Real.exp 6 * Real.exp (-(1 / (5 / 4))) * ((1 * 0 - 5 / 4) / (5 / 4) ^ 2)) 1 ∧
      Real.exp 6 * Real.exp (-(1 / (5 / 4))) * ((1 * 0 - 5 / 4) / (5 / 4) ^ 2) < 0 ∧
      HasDerivAt (fun x => wilDemand 1 (fun γ => Real.exp (-γ)) x (x ^ 2))
        (1 * Real.exp (-(1 / 1 ^ 2)) * ((1 * 2 - 1 ^ 2) / (1 ^ 2) ^ 2)) 1 ∧
      0 < 1 * Real.exp (-(1 / 1 ^ 2)) * ((1 * 2 - 1 ^ 2) / (1 ^ 2) ^ 2) := by
  have hμ1 : (stepEconomy (Real.exp 6) 9).mu 1 = 5 / 4 :=
    stepEconomy_mu_low zero_le_one (by norm_num)
  have hd : HasDerivAt (stepEconomy (Real.exp 6) 9).mu 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (5 / 4 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (zero_lt_one : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 9)]
      with x hx
    exact stepEconomy_mu_low hx.1.le hx.2
  have h1 := exercise_13_B_6b expDensity (Real.exp_pos 6) one_pos (by rw [hμ1]; norm_num) hd
  rw [hμ1] at h1
  have hd2 : HasDerivAt (fun x : ℝ => x ^ 2) 2 1 := by
    simpa using hasDerivAt_pow 2 (1 : ℝ)
  have h2 := exercise_13_B_6b expDensity one_pos one_pos (by norm_num) hd2
  refine ⟨h1.1, h1.2.2.2 (by norm_num), h2.1, h2.2.1.2 (by norm_num)⟩

/-- **Exercise 13.B.6(c)-(d)(i)**, instance (MWG, p. 474). In `stepEconomy (e⁶) 9` there are two
competitive equilibrium wages, `w₁ = 15/2 + (5/4) log 2` (only the types `θ ≤ 3/2` work) and
`w₂ = 9` (everybody works), and `9` is the highest; `9` Pareto dominates `w₁`, `9` is an SPNE
outcome and `w₁` is not. -/
theorem exercise_13_B_6_instance :
    (stepEconomy (Real.exp 6) 9).Valid ∧
      (stepEconomy (Real.exp 6) 9).IsCE (15 / 2 + 5 / 4 * Real.log 2) ∧
      (stepEconomy (Real.exp 6) 9).IsCE 9 ∧
      IsGreatest {x | (stepEconomy (Real.exp 6) 9).IsCE x} 9 ∧
      (stepEconomy (Real.exp 6) 9).mu (15 / 2 + 5 / 4 * Real.log 2) <
        (stepEconomy (Real.exp 6) 9).mu 9 ∧
      (stepEconomy (Real.exp 6) 9).IsSPNE 9 ∧
      ¬ (stepEconomy (Real.exp 6) 9).IsSPNE (15 / 2 + 5 / 4 * Real.log 2) := by
  have hE := stepEconomy_valid (Real.exp_pos 6) (by norm_num : (0 : ℝ) ≤ 9)
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  have hw0 : 0 ≤ 15 / 2 + 5 / 4 * Real.log 2 := by linarith
  have hw9 : 15 / 2 + 5 / 4 * Real.log 2 < 9 := by linarith
  have hce1 : (stepEconomy (Real.exp 6) 9).IsCE (15 / 2 + 5 / 4 * Real.log 2) := by
    rw [WilsonEconomy.IsCE, stepEconomy_zstar_low hw0 hw9, stepEconomy_supply_low hw0 hw9,
      ← Real.exp_add, ← exp_neg_log_two]
    congr 1
    ring
  have hce9 : (stepEconomy (Real.exp 6) 9).IsCE 9 := by
    rw [WilsonEconomy.IsCE, stepEconomy_zstar_high (by norm_num) le_rfl,
      stepEconomy_supply_high (by norm_num) le_rfl, ← Real.exp_add]
    norm_num
  have hgr : IsGreatest {x | (stepEconomy (Real.exp 6) 9).IsCE x} 9 := by
    refine ⟨hce9, fun w hw => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h := hw
    rw [Set.mem_ofPred_eq, WilsonEconomy.IsCE, stepEconomy_zstar_high (by linarith) hlt.le,
      stepEconomy_supply_high (by linarith) hlt.le, ← Real.exp_add] at h
    have : Real.exp (6 + -(2 / 3 * w)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hspne : (stepEconomy (Real.exp 6) 9).IsSPNE 9 :=
    WilsonEconomy.exercise_13_B_6d_ii_full_employment hE hce9 (by
      change stepR 9 2 ≤ 9
      unfold stepR
      norm_num)
  refine ⟨hE, hce1, hce9, hgr, ?_, hspne, fun h => ?_⟩
  · rw [stepEconomy_mu_low hw0 hw9, stepEconomy_mu_high (by norm_num) le_rfl]
    norm_num
  · have := (WilsonEconomy.exercise_13_B_6d_i hE h).2 hce9
    linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), counterexample to the "if" direction. In
`stepEconomy 1 3` the unique (hence highest) competitive equilibrium wage is
`w* = (5/4) log 2` and `z*(w) ≤ z*(w*)` for all `w > w*`, yet `w*` is not an SPNE outcome: at
`w = 3` the pool improves (`μ` rises from `5/4` to `3/2`), and firms with high `γ` deviate. -/
theorem exercise_13_B_6d_ii_counterexample :
    (stepEconomy 1 3).Valid ∧ IsGreatest {x | (stepEconomy 1 3).IsCE x} (5 / 4 * Real.log 2) ∧
      (∀ w, 5 / 4 * Real.log 2 < w →
        (stepEconomy 1 3).zstar w ≤ (stepEconomy 1 3).zstar (5 / 4 * Real.log 2)) ∧
      ¬ (stepEconomy 1 3).IsSPNE (5 / 4 * Real.log 2) := by
  have hE := stepEconomy_valid one_pos (by norm_num : (0 : ℝ) ≤ 3)
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  have hw0 : 0 ≤ 5 / 4 * Real.log 2 := by linarith
  have hw3 : 5 / 4 * Real.log 2 < 3 := by linarith
  have hzs : (stepEconomy 1 3).zstar (5 / 4 * Real.log 2) = 1 / 2 := by
    rw [stepEconomy_zstar_low hw0 hw3, one_mul, ← exp_neg_log_two]
    congr 1
    ring
  have hce : (stepEconomy 1 3).IsCE (5 / 4 * Real.log 2) := by
    rw [WilsonEconomy.IsCE, hzs, stepEconomy_supply_low hw0 hw3]
  have he2 : Real.exp (-2) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp 2
    rw [one_div]
    exact inv_anti₀ two_pos (by linarith)
  refine ⟨hE, ⟨hce, fun w hw => ?_⟩, fun w hw => ?_, fun h => ?_⟩
  · have hw0' := hE.ce_nonneg hw
    rw [Set.mem_ofPred_eq, WilsonEconomy.IsCE] at hw
    rcases lt_or_ge w 3 with h3 | h3
    · rw [stepEconomy_zstar_low hw0' h3, stepEconomy_supply_low hw0' h3, one_mul,
        ← exp_neg_log_two] at hw
      have := Real.exp_injective hw
      linarith
    · rw [stepEconomy_zstar_high hw0' h3, stepEconomy_supply_high hw0' h3, one_mul] at hw
      have : Real.exp (-(2 / 3 * w)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      rw [Real.exp_zero] at this
      linarith
  · rw [hzs]
    rcases lt_or_ge w 3 with h3 | h3
    · rw [stepEconomy_zstar_low (by linarith) h3, one_mul, ← exp_neg_log_two]
      exact Real.exp_le_exp.2 (by linarith)
    · rw [stepEconomy_zstar_high (by linarith) h3, one_mul]
      exact (Real.exp_le_exp.2 (by linarith)).trans he2
  · have := (WilsonEconomy.exercise_13_B_6d_ii_corrected hE hce).1 h 3 hw3
    rw [stepEconomy_mu_high (by norm_num) le_rfl, stepEconomy_mu_low hw0 hw3] at this
    norm_num at this

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.C.1: a costless test with a continuum of types

MWG, Exercise 13.C.1, p. 474. Nature draws the worker's type from a continuous distribution on
`[θ̲, θ̄]`; the worker chooses whether to take a costless test that reveals her type; two
firms then bid for her (`r = 0`, as in Section 13.C).

As in Section 13.C (`bertrand_wage`) the competing firms pay the expected productivity under
their beliefs, so an equilibrium is described in reduced form (`IsTestEq`, the pattern of
`IsPBEC4`) by the test strategy `τ(θ)` and the wage `w_N` offered to a worker who did not take
the test: a tested worker is paid her type `θ`; `w_N ∈ [θ̲, θ̄]` (the mean of some belief); each
type's choice is optimal; and if the non-testers have positive probability, `w_N` is their
conditional mean.

* `exercise_13_C_1`: in every equilibrium `w_N = θ̲` (so firms offer no more than `θ̲` to a
  worker not taking the test) and every type `θ > θ̲` takes the test (strictly prefers to).
* `exercise_13_C_1_instance`: with types uniform on `[1, 2]`, both "everybody tests" and
  "everybody but `θ̲` tests" are equilibria: `θ̲` is indifferent, so "all worker types submit"
  holds for all types but `θ̲`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.C.1** (MWG, p. 474). The types in `[θ̲, θ̄]` that do not take the test. -/
def testNonTakers (θl θh : ℝ) (τ : ℝ → Bool) : Set ℝ := {θ | θ ∈ Set.Icc θl θh ∧ τ θ = false}

/-- **Exercise 13.C.1** (MWG, p. 474). The reduced form of an SPNE of the testing game: the test
strategy `τ` (`true` = take the test) and the wage `w_N` paid after no test. -/
def IsTestEq (μ : Measure ℝ) (θl θh : ℝ) (τ : ℝ → Bool) (wN : ℝ) : Prop :=
  (θl ≤ wN ∧ wN ≤ θh) ∧ (∀ θ ∈ Set.Icc θl θh, τ θ = true → wN ≤ θ) ∧
    (∀ θ ∈ Set.Icc θl θh, τ θ = false → θ ≤ wN) ∧
    (0 < μ (testNonTakers θl θh τ) → wN = condMean μ θl θh (testNonTakers θl θh τ))

/-- **Exercise 13.C.1** (MWG, p. 474). In any equilibrium of the testing game firms pay `θ̲` to a
worker who does not take the test, and every type above `θ̲` takes it. -/
theorem exercise_13_C_1 {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (hden : HasPosDensity μ θl θh) {τ : ℝ → Bool} {wN : ℝ} (h : IsTestEq μ θl θh τ wN) :
    wN = θl ∧ ∀ θ, θl < θ → θ ≤ θh → τ θ = true ∧ wN < θ := by
  have := hd.prob
  obtain ⟨⟨hw1, hw2⟩, htest, hno, hbayes⟩ := h
  set A := testNonTakers θl θh τ with hAdef
  have hsub : Set.Ico θl wN ⊆ A := fun θ hθ => by
    refine ⟨⟨hθ.1, hθ.2.le.trans hw2⟩, ?_⟩
    cases hτ : τ θ
    · rfl
    · exact absurd (htest θ ⟨hθ.1, hθ.2.le.trans hw2⟩ hτ) (not_le.2 hθ.2)
  have hAeq : A = Set.Ico θl wN ∪ (A ∩ {wN}) := by
    ext θ
    constructor
    · intro hθ
      rcases eq_or_lt_of_le (hno θ hθ.1 hθ.2) with he | hlt
      · exact Or.inr ⟨hθ, he⟩
      · exact Or.inl ⟨hθ.1.1, hlt⟩
    · rintro (hθ | hθ)
      · exact hsub hθ
      · exact hθ.1
  have hAm : MeasurableSet A := by
    rw [hAeq]
    exact measurableSet_Ico.union
      (Set.subsingleton_singleton.anti Set.inter_subset_right).measurableSet
  have hA0 : μ A = 0 := by
    by_contra hne
    have hpos : 0 < μ A := pos_iff_ne_zero.2 hne
    have hw := hbayes hpos
    have hae : ∀ᵐ θ ∂μ, θ ≠ wN := by
      rw [ae_iff]; simpa using hden.noAtom wN
    have hlt : 0 < ∫ θ in A, (wN - θ) ∂μ :=
      setIntegral_pos_of_ae_pos hAm hpos
        (hae.mono fun θ hθ hθA => sub_pos.2 (lt_of_le_of_ne (hno θ hθA.1 hθA.2) hθ))
        ((integrable_const wN).sub hd.integrable_id).integrableOn
    rw [integral_sub (integrable_const wN).integrableOn hd.integrable_id.integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    have ha : 0 < (μ A).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    simp only [condMean, hpos, ↓reduceIte] at hw
    rw [eq_div_iff ha.ne'] at hw
    nlinarith
  have hwl : wN ≤ θl := by
    by_contra hlt
    rw [not_le] at hlt
    have hp := hden.pos θl ((θl + wN) / 2) le_rfl (by linarith) (by linarith)
    have h0 : μ (Set.Icc θl ((θl + wN) / 2)) = 0 :=
      measure_mono_null (fun θ hθ => hsub ⟨hθ.1, by linarith [hθ.2]⟩) hA0
    rw [h0] at hp
    exact lt_irrefl _ hp
  have heq : wN = θl := le_antisymm hwl hw1
  refine ⟨heq, fun θ h1 h2 => ⟨?_, by linarith⟩⟩
  cases hτ : τ θ
  · have := hno θ ⟨h1.le, h2⟩ hτ
    linarith
  · rfl

/-- **Exercise 13.C.1**, instance (MWG, p. 474). With types uniform on `[1, 2]` and `w_N = 1`,
"every type takes the test" and "every type but `θ̲ = 1` takes the test" are both equilibria. -/
theorem exercise_13_C_1_instance :
    IsTestEq (unifMeas 1 2) 1 2 (fun _ => true) 1 ∧
      IsTestEq (unifMeas 1 2) 1 2 (fun θ => decide (1 < θ)) 1 := by
  refine ⟨⟨⟨le_rfl, by norm_num⟩, fun θ hθ _ => hθ.1, fun θ _ h => absurd h (by simp),
    fun h => ?_⟩, ⟨⟨le_rfl, by norm_num⟩, fun θ hθ _ => hθ.1, fun θ _ h => ?_, fun h => ?_⟩⟩
  · have : testNonTakers 1 2 (fun _ => true) = ∅ := by
      ext θ; simp [testNonTakers]
    rw [this, measure_empty] at h
    exact absurd h (lt_irrefl _)
  · simpa using h
  · have hsub : testNonTakers 1 2 (fun θ => decide (1 < θ)) ⊆ {1} := by
      intro θ hθ
      simp only [testNonTakers, Set.mem_ofPred_eq, decide_eq_false_iff_not, not_lt] at hθ
      exact le_antisymm hθ.2 hθ.1.1
    have h0 := measure_mono_null hsub ((unifMeas_density one_lt_two).noAtom 1)
    rw [h0] at h
    exact absurd h (lt_irrefl _)

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.C.2: productive education

MWG, Exercise 13.C.2, p. 475. The two-type signaling model of Section 13.C (`SigModel`,
`SigModel.Valid`) with `r(θ_L) = r(θ_H) = 0`, but a worker of type `θ` with education `e`
produces `θ(1 + μe)`, `μ > 0`.

The game is that of Section 13.C with the firms' expected productivity after `e` now
`(μ(e)θ_H + (1 - μ(e))θ_L)(1 + μe)` (`SigModel.prodWage`; here the belief is called `bel` and
`μ` is the productivity parameter). `SigModel.IsPBEProd` is the PBE with the Chapter 8 wage game
after every `e`; `SigModel.exists_isPBEProd_iff` reduces it, by `bertrand_wage`, to
`SigModel.IsPBEProdRed` (wage = expected productivity).

The full information outcome: type `θ` chooses `e` to maximise `θ(1 + μe) - c(e, θ)`
(`SigModel.fullPay`, `SigModel.IsFullInfoChoice`).

* `exercise_13_C_2_separating`: `(e_L, e_H)`, `e_L ≠ e_H`, is a separating PBE iff `e_L` is the
  low type's full information choice, the low type does not want to mimic
  (`θ_H(1 + μe_H) - c(e_H, θ_L) ≤` its full information payoff), and the high type prefers
  `e_H` to being taken for a low type at any `e`.
* `exercise_13_C_2_full_info`: if the high type's full information choice already deters
  mimicking, the full information outcome is a separating PBE.
* `exercise_13_C_2_distorted`: otherwise the high type is strictly worse off in every
  separating PBE than under full information.
* `exercise_13_C_2_pooling`: pooling at `e_p` is a PBE iff for both types
  `E[θ](1 + μe_p) - c(e_p, θ) ≥ θ_L(1 + μe) - c(e, θ)` for all `e ≥ 0`; in it the low type does
  at least as well as under full information (`exercise_13_C_2_pooling_low`).
* `exercise_13_C_2_instance`: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`, `μ = 1`, `c(e, θ) = e²/θ`: full
  information `e = 1/2, 2`; the full information outcome is not a PBE, `(1/2, 3)` is a
  separating PBE with the high type strictly worse off, and pooling at `1/2` is a PBE.
-/

namespace MWG.AdverseSelection

open MWG.SimultaneousMoveGames

namespace SigModel

/-- **Exercise 13.C.2** (MWG, p. 475). Expected productivity `(bθ_H + (1 - b)θ_L)(1 + μe)` of a
worker with education `e` believed to be of high ability with probability `b`. -/
def prodWage (M : SigModel) (μ b e : ℝ) : ℝ := M.expProd b * (1 + μ * e)

/-- **Exercise 13.C.2** (MWG, p. 475). A type's payoff from `e` against the wage schedule
`prodWage μ (bel e) e`. -/
def prodPay (M : SigModel) (μ : ℝ) (bel : ℝ → ℝ) (t : Bool) (e : ℝ) : ℝ :=
  M.prodWage μ (bel e) e - M.c e (M.θ t)

/-- **Exercise 13.C.2** (MWG, p. 475). A pure strategy PBE of the productive education game:
education choices, beliefs, and after every `e` a Nash equilibrium of the firms' wage game with
expected productivity `prodWage μ (bel e) e`. -/
def IsPBEProd (M : SigModel) (μ : ℝ) (eS : Bool → ℝ) (bel : ℝ → ℝ) (wO : ℝ → Fin 2 → ℝ) :
    Prop :=
  (∀ t, 0 ≤ eS t) ∧ (∀ e, 0 ≤ bel e ∧ bel e ≤ 1) ∧
    (∀ t e, 0 ≤ e → M.workerPay t (wO e) e ≤ M.workerPay t (wO (eS t)) (eS t)) ∧
    M.BayesOnPath eS bel ∧
    ∀ e, 0 ≤ e → IsNashEquilibrium (wageGame (M.offerProfit (M.prodWage μ (bel e) e))) (wO e)

/-- **Exercise 13.C.2** (MWG, p. 475). The reduced form: the wage is the expected productivity. -/
def IsPBEProdRed (M : SigModel) (μ : ℝ) (eS : Bool → ℝ) (bel : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ eS t) ∧ (∀ e, 0 ≤ bel e ∧ bel e ≤ 1) ∧
    (∀ t e, 0 ≤ e → M.prodPay μ bel t e ≤ M.prodPay μ bel t (eS t)) ∧ M.BayesOnPath eS bel

/-- **Exercise 13.C.2** (MWG, p. 475). The full information payoff `θ(1 + μe) - c(e, θ)`. -/
def fullPay (M : SigModel) (μ : ℝ) (t : Bool) (e : ℝ) : ℝ := M.θ t * (1 + μ * e) - M.c e (M.θ t)

/-- **Exercise 13.C.2** (MWG, p. 475). `e` is a full information choice of type `t`. -/
def IsFullInfoChoice (M : SigModel) (μ : ℝ) (t : Bool) (e : ℝ) : Prop :=
  0 ≤ e ∧ ∀ e', 0 ≤ e' → M.fullPay μ t e' ≤ M.fullPay μ t e

variable {M : SigModel}

theorem Valid.prodWage_nonneg (hM : M.Valid) {μ b e : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (he : 0 ≤ e) : 0 ≤ M.prodWage μ b e :=
  mul_nonneg (hM.θL_pos.le.trans (hM.expProd_mem hb hb1).1) (by nlinarith)

/-- The wage after `e` is at least `θ_L(1 + μe)`. -/
theorem Valid.prodWage_ge (hM : M.Valid) {μ b e : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (he : 0 ≤ e) : M.θL * (1 + μ * e) ≤ M.prodWage μ b e :=
  mul_le_mul_of_nonneg_right (hM.expProd_mem hb hb1).1 (by nlinarith)

/-- **Exercise 13.C.2** (MWG, p. 475). With `r = 0`, strategies and beliefs are part of a PBE iff
they form a reduced-form PBE. -/
theorem Valid.exists_isPBEProd_iff (hM : M.Valid) (hr : M.r = 0) {μ : ℝ} (hμ : 0 < μ)
    (eS : Bool → ℝ) (bel : ℝ → ℝ) :
    (∃ wO, M.IsPBEProd μ eS bel wO) ↔ M.IsPBEProdRed μ eS bel := by
  constructor
  · rintro ⟨wO, h0, hb, hopt, hB, hNE⟩
    have hw : ∀ e, 0 ≤ e →
        max (max (wO e 0) (wO e 1)) M.r = M.prodWage μ (bel e) e := fun e he => by
      rw [M.bertrand_wage (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he) _ (hNE e he), hr,
        max_eq_left (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)]
    refine ⟨h0, hb, fun t e he => ?_, hB⟩
    have := hopt t e he
    unfold workerPay at this
    rw [hw e he, hw _ (h0 t)] at this
    exact this
  · rintro ⟨h0, hb, hopt, hB⟩
    have hw : ∀ e, 0 ≤ e → max (max (M.bertrandOffer (M.prodWage μ (bel e) e) 0)
        (M.bertrandOffer (M.prodWage μ (bel e) e) 1)) M.r = M.prodWage μ (bel e) e :=
      fun e he => by
        rw [bertrandOffer_max, hr, max_eq_left (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)]
    refine ⟨fun e => M.bertrandOffer (M.prodWage μ (bel e) e), h0, hb, fun t e he => ?_, hB,
      fun e he => M.bertrandOffer_nash (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)⟩
    unfold workerPay
    rw [hw e he, hw _ (h0 t)]
    exact hopt t e he

/-- **Exercise 13.C.2** (MWG, p. 475). Separating PBE: `(e_L, e_H)` with `e_L ≠ e_H` is the
outcome of a PBE iff (i) `e_L` is the low type's full information choice, (ii) the low type does
not gain by mimicking, `θ_H(1 + μe_H) - c(e_H, θ_L) ≤ θ_L(1 + μe_L) - c(e_L, θ_L)`, and (iii)
`θ_L(1 + μe) - c(e, θ_H) ≤ θ_H(1 + μe_H) - c(e_H, θ_H)` for every `e ≥ 0`. -/
theorem exercise_13_C_2_separating (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH : ℝ}
    (hL : 0 ≤ eL) (hH : 0 ≤ eH) (hne : eL ≠ eH) :
    (∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel) ↔
      M.IsFullInfoChoice μ false eL ∧
        M.θH * (1 + μ * eH) - M.c eH M.θL ≤ M.fullPay μ false eL ∧
        ∀ e, 0 ≤ e → M.θL * (1 + μ * e) - M.c e M.θH ≤ M.fullPay μ true eH := by
  constructor
  · rintro ⟨bel, -, hb, hopt, hB⟩
    obtain ⟨h1, h0⟩ := hB.1 (by simpa using hne)
    simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h0 hopt
    have hlow : M.prodPay μ bel false eL = M.fullPay μ false eL := by
      simp [prodPay, fullPay, prodWage, h0, expProd_zero, θ_false]
    have hhigh : M.prodPay μ bel true eH = M.fullPay μ true eH := by
      simp [prodPay, fullPay, prodWage, h1, expProd_one, θ_true]
    refine ⟨⟨hL, fun e he => ?_⟩, ?_, fun e he => ?_⟩
    · have := hopt false e he
      have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
      simp only [Bool.false_eq_true, ite_false] at this
      rw [hlow] at this
      unfold prodPay at this
      unfold fullPay at this ⊢
      rw [θ_false] at this ⊢
      linarith
    · have := hopt false eH hH
      simp only [Bool.false_eq_true, ite_false] at this
      rw [hlow] at this
      simpa [prodPay, prodWage, h1, expProd_one, θ_false] using this
    · have := hopt true e he
      have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
      simp only [ite_true] at this
      rw [hhigh] at this
      unfold prodPay at this
      rw [θ_true] at this
      linarith
  · rintro ⟨⟨-, hfi⟩, hmim, hhi⟩
    refine ⟨fun x => if x = eH then 1 else 0, ?_, fun x => ?_, fun t e he => ?_, ?_, ?_⟩
    · intro t; cases t <;> simpa
    · dsimp only
      split_ifs <;> norm_num
    · cases t
      · simp only [Bool.false_eq_true, ite_false]
        by_cases heH : e = eH
        · subst heH
          simpa [prodPay, prodWage, hne, expProd_one, expProd_zero, θ_false, fullPay] using hmim
        · have := hfi e he
          simpa [prodPay, prodWage, heH, hne, expProd_zero, θ_false, fullPay] using this
      · simp only [ite_true]
        by_cases heH : e = eH
        · rw [heH]
        · have := hhi e he
          simpa [prodPay, prodWage, heH, expProd_zero, expProd_one, θ_true, fullPay] using this
    · intro hsep
      simp only [ite_true, Bool.false_eq_true, ite_false, hne, and_self]
    · intro hpool
      simp only [ite_true, Bool.false_eq_true, ite_false] at hpool
      exact absurd hpool hne

/-- **Exercise 13.C.2** (MWG, p. 475). If the full information choices `e_L**`, `e_H**` are such
that the low type does not want to mimic `e_H**`, the full information outcome is a separating
PBE outcome. -/
theorem exercise_13_C_2_full_info (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH : ℝ}
    (hL : M.IsFullInfoChoice μ false eL) (hH : M.IsFullInfoChoice μ true eH)
    (hmim : M.θH * (1 + μ * eH) - M.c eH M.θL ≤ M.fullPay μ false eL) :
    eL ≠ eH ∧ ∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel := by
  have hne : eL ≠ eH := by
    rintro rfl
    unfold fullPay at hmim
    rw [θ_false] at hmim
    have : 0 < 1 + μ * eL := by nlinarith [hL.1]
    nlinarith [hM.lt]
  refine ⟨hne, (exercise_13_C_2_separating hM hμ hL.1 hH.1 hne).2 ⟨hL, hmim, fun e he => ?_⟩⟩
  have := hH.2 e he
  unfold fullPay at this ⊢
  rw [θ_true] at this ⊢
  have : M.θL * (1 + μ * e) ≤ M.θH * (1 + μ * e) :=
    mul_le_mul_of_nonneg_right hM.lt.le (by nlinarith)
  linarith

/-- **Exercise 13.C.2** (MWG, p. 475). If no full information choice of the high type deters the
low type from mimicking, the high type is strictly worse off in every separating PBE than under
full information (the low type gets exactly its full information payoff,
`exercise_13_C_2_separating`). -/
theorem exercise_13_C_2_distorted (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH eHs : ℝ}
    (hL : 0 ≤ eL) (hH : 0 ≤ eH) (hne : eL ≠ eH)
    (hpbe : ∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel)
    (hHs : M.IsFullInfoChoice μ true eHs)
    (hno : ∀ e, M.IsFullInfoChoice μ true e →
      M.fullPay μ false eL < M.θH * (1 + μ * e) - M.c e M.θL) :
    M.fullPay μ true eH < M.fullPay μ true eHs := by
  obtain ⟨-, hmim, -⟩ := (exercise_13_C_2_separating hM hμ hL hH hne).1 hpbe
  rcases eq_or_lt_of_le (hHs.2 eH hH) with heq | hlt
  · have hfi : M.IsFullInfoChoice μ true eH :=
      ⟨hH, fun e' he' => heq ▸ hHs.2 e' he'⟩
    exact absurd hmim (not_le.2 (hno eH hfi))
  · exact hlt

/-- **Exercise 13.C.2** (MWG, p. 475). Pooling PBE: both types choosing `e_p` is a PBE outcome iff
for each type `E[θ](1 + μe_p) - c(e_p, θ) ≥ θ_L(1 + μe) - c(e, θ)` for all `e ≥ 0`. -/
theorem exercise_13_C_2_pooling (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {ep : ℝ} (hp : 0 ≤ ep) :
    (∃ bel, M.IsPBEProdRed μ (fun _ => ep) bel) ↔
      ∀ t e, 0 ≤ e → M.θL * (1 + μ * e) - M.c e (M.θ t) ≤
        M.Eθ * (1 + μ * ep) - M.c ep (M.θ t) := by
  constructor
  · rintro ⟨bel, -, hb, hopt, hB⟩ t e he
    have hlam := hB.2 rfl
    have := hopt t e he
    have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
    unfold prodPay at this
    rw [show M.prodWage μ (bel ep) ep = M.Eθ * (1 + μ * ep) by
      rw [prodWage, hlam, expProd_lam]] at this
    linarith
  · intro h
    refine ⟨fun x => if x = ep then M.lam else 0, fun _ => hp, fun x => ?_, fun t e he => ?_,
      ⟨fun hs => absurd rfl hs, fun _ => by simp⟩⟩
    · dsimp only
      split_ifs
      · exact ⟨hM.lam_pos.le, hM.lam_lt.le⟩
      · norm_num
    · have hep : M.prodPay μ (fun x => if x = ep then M.lam else 0) t ep =
          M.Eθ * (1 + μ * ep) - M.c ep (M.θ t) := by
        simp [prodPay, prodWage, expProd_lam]
      rw [hep]
      by_cases he' : e = ep
      · subst he'; rw [hep]
      · have := h t e he
        simpa [prodPay, prodWage, he', expProd_zero] using this

/-- **Exercise 13.C.2** (MWG, p. 475). In a pooling PBE the low type does at least as well as
under full information. -/
theorem exercise_13_C_2_pooling_low (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {ep : ℝ} (hp : 0 ≤ ep)
    (h : ∃ bel, M.IsPBEProdRed μ (fun _ => ep) bel) (e : ℝ) (he : 0 ≤ e) :
    M.fullPay μ false e ≤ M.Eθ * (1 + μ * ep) - M.c ep M.θL := by
  have := (exercise_13_C_2_pooling hM hμ hp).1 h false e he
  simpa [fullPay, θ_false] using this

/-- **Exercise 13.C.2**, the instance: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`, `r = 0`,
`c(e, θ) = e²/θ`. -/
noncomputable def prodSigModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun e θ => e ^ 2 / θ

theorem prodSigModel_valid : prodSigModel.Valid where
  θL_pos := one_pos
  lt := one_lt_two
  lam_pos := by norm_num [prodSigModel]
  lam_lt := by norm_num [prodSigModel]
  r_nonneg := le_rfl
  r_lt := two_pos
  c_zero θ := by simp [prodSigModel]
  c_mono b := by
    have hθ : 0 < prodSigModel.θ b := by
      cases b <;> norm_num [θ, prodSigModel]
    intro x hx y hy hxy
    change x ^ 2 / prodSigModel.θ b < y ^ 2 / prodSigModel.θ b
    exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hxy hx two_ne_zero) hθ
  c_cont b := (continuous_pow 2).continuousOn.div_const _
  sc e e' he hee' := by
    change e' ^ 2 / 2 - e ^ 2 / 2 < e' ^ 2 / 1 - e ^ 2 / 1
    nlinarith

/-- **Exercise 13.C.2**, instance (MWG, p. 475). With `μ = 1`: the full information choices are
`e_L** = 1/2` and `e_H** = 2` (`e_H** = 2` is the only one); the full information outcome is not
a PBE (the low type would mimic `e = 2`); `(1/2, 3)` is a separating PBE outcome, in which the
high type earns `7/2 < 4`, its full information payoff; pooling at `e = 1/2` is a PBE outcome. -/
theorem exercise_13_C_2_instance :
    prodSigModel.IsFullInfoChoice 1 false (1 / 2) ∧ prodSigModel.IsFullInfoChoice 1 true 2 ∧
      (∀ e, prodSigModel.IsFullInfoChoice 1 true e → e = 2) ∧
      ¬ (∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 2 else 1 / 2) bel) ∧
      (∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 3 else 1 / 2) bel) ∧
      prodSigModel.fullPay 1 true 3 < prodSigModel.fullPay 1 true 2 ∧
      (∃ bel, prodSigModel.IsPBEProdRed 1 (fun _ => 1 / 2) bel) ∧
      (∃ bel wO, prodSigModel.IsPBEProd 1 (fun _ => 1 / 2) bel wO) := by
  have hM := prodSigModel_valid
  have hfL : prodSigModel.IsFullInfoChoice 1 false (1 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
    nlinarith [sq_nonneg (e - 1 / 2)]⟩
  have hfH : prodSigModel.IsFullInfoChoice 1 true 2 := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel, ite_true]
    nlinarith [sq_nonneg (e - 2)]⟩
  have huniq : ∀ e, prodSigModel.IsFullInfoChoice 1 true e → e = 2 := by
    intro e he
    have := he.2 2 (by norm_num)
    simp only [fullPay, θ, prodSigModel, ite_true] at this
    nlinarith [sq_nonneg (e - 2)]
  have hsep : ∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 3 else 1 / 2) bel := by
    refine (exercise_13_C_2_separating hM one_pos (by norm_num) (by norm_num)
      (by norm_num)).2 ⟨hfL, ?_, fun e he => ?_⟩
    · simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
      norm_num
    · simp only [fullPay, θ, prodSigModel, ite_true]
      nlinarith [sq_nonneg (e - 1)]
  have hpool : ∃ bel, prodSigModel.IsPBEProdRed 1 (fun _ => 1 / 2) bel := by
    refine (exercise_13_C_2_pooling hM one_pos (by norm_num)).2 fun t e he => ?_
    simp only [Eθ, prodSigModel]
    cases t
    · simp only [θ, Bool.false_eq_true, ite_false]
      nlinarith [sq_nonneg (e - 1 / 2)]
    · simp only [θ, ite_true]
      nlinarith [sq_nonneg (e - 1)]
  obtain ⟨bel, hbel⟩ := hpool
  refine ⟨hfL, hfH, huniq, fun h => ?_, hsep, ?_, ⟨bel, hbel⟩,
    ⟨bel, (hM.exists_isPBEProd_iff rfl one_pos _ _).2 hbel⟩⟩
  · obtain ⟨-, hmim, -⟩ :=
      (exercise_13_C_2_separating hM one_pos (by norm_num) (by norm_num) (by norm_num)).1 h
    simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false] at hmim
    norm_num at hmim
  · exact exercise_13_C_2_distorted hM one_pos (by norm_num) (by norm_num) (by norm_num) hsep hfH
      fun e he => by
        rw [huniq e he]
        simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
        norm_num

/-- **Exercise 13.C.2**, a second instance: `θ_L = 1`, `θ_H = 3`, `λ = 1/2`, `c(e, θ) = e²/θ`. -/
noncomputable def prodSigModel3 : SigModel where
  θL := 1
  θH := 3
  lam := 1 / 2
  r := 0
  c := fun e θ => e ^ 2 / θ

theorem prodSigModel3_valid : prodSigModel3.Valid where
  θL_pos := one_pos
  lt := by norm_num [prodSigModel3]
  lam_pos := by norm_num [prodSigModel3]
  lam_lt := by norm_num [prodSigModel3]
  r_nonneg := le_rfl
  r_lt := by norm_num [prodSigModel3]
  c_zero θ := by simp [prodSigModel3]
  c_mono b := by
    have hθ : 0 < prodSigModel3.θ b := by
      cases b <;> norm_num [θ, prodSigModel3]
    intro x hx y hy hxy
    change x ^ 2 / prodSigModel3.θ b < y ^ 2 / prodSigModel3.θ b
    exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hxy hx two_ne_zero) hθ
  c_cont b := (continuous_pow 2).continuousOn.div_const _
  sc e e' he hee' := by
    change e' ^ 2 / 3 - e ^ 2 / 3 < e' ^ 2 / 1 - e ^ 2 / 1
    nlinarith

/-- **Exercise 13.C.2**, instance of `exercise_13_C_2_full_info` (MWG, p. 475). With `θ_H = 3`
and `μ = 1` the full information choices are `1/2` and `9/2`, and the low type does not want to
mimic `9/2`: the full information outcome is a separating PBE outcome. -/
theorem exercise_13_C_2_full_info_instance :
    prodSigModel3.IsFullInfoChoice 1 false (1 / 2) ∧ prodSigModel3.IsFullInfoChoice 1 true (9 / 2) ∧
      ∃ bel, prodSigModel3.IsPBEProdRed 1 (fun t => if t then 9 / 2 else 1 / 2) bel := by
  have hfL : prodSigModel3.IsFullInfoChoice 1 false (1 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel3, Bool.false_eq_true, ite_false]
    nlinarith [sq_nonneg (e - 1 / 2)]⟩
  have hfH : prodSigModel3.IsFullInfoChoice 1 true (9 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel3, ite_true]
    nlinarith [sq_nonneg (e - 9 / 2)]⟩
  refine ⟨hfL, hfH, (exercise_13_C_2_full_info prodSigModel3_valid one_pos hfL hfH ?_).2⟩
  simp only [fullPay, θ, prodSigModel3, Bool.false_eq_true, ite_false]
  norm_num

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.C.6(b): self-financing as a signal

MWG, Exercise 13.C.6(b), pp. 475-476. Projects cost `1`; a good (bad) project yields `Π` with
probability `p_G` (`p_B`) and `0` otherwise; a fraction `λ` is good; banks borrow at `r`; the
entrepreneur can contribute `x ∈ [0, 1]` of the outlay at effective cost `(1 + ρ)x`, `ρ > r`;
`p_GΠ - (1 + r) > 0 > p_BΠ - (1 + r)` (`LoanModel.Valid`). A loan of `1 - x` specifies the
repayment `R`, paid when the project succeeds.

* (i) `LoanModel.entPay`: the payoff `p_t(Π - R) - (1 + ρ)x` of type `t` going ahead
  (`0` otherwise); `exercise_13_C_6b_i` evaluates it at the zero-profit repayments.
* The game (entrepreneur offers `x`, banks offer `R`, entrepreneur accepts or not), in reduced
  form (`LoanModel.IsLoanPBE`): after `x` with belief `b` = Prob(good), Bertrand competition
  drives the banks to the zero-profit repayment `R = (1 + r)(1 - x)/(bp_G + (1 - b)p_B)`
  (`LoanModel.repay`, `exercise_13_C_6b_bank_zero_profit`); type `t` then goes ahead iff its
  payoff is nonnegative (`LoanModel.gamePay`); beliefs follow Bayes' rule on the path.
* (ii) `exercise_13_C_6b_ii_separating`: `(x_G, x_B)`, `x_G ≠ x_B`, is a separating PBE outcome
  iff `x_G ≥ x*`, `x* = p_B(p_GΠ - (1 + r))/(p_G(1 + ρ) - p_B(1 + r)) ∈ (0, 1)`. The best one
  (`exercise_13_C_6b_ii_best`) has `x_G = x*`: the bad type and the banks get `0` in every
  separating PBE, and the good type's payoff `p_GΠ - (1 + r) - (ρ - r)x_G` falls with `x_G`.
  Comparative statics of `x*` (`exercise_13_C_6b_ii_statics`): strictly increasing in `p_B`,
  `p_G` and `Π`, strictly decreasing in `r` (and in `ρ`), independent of `λ`.
* (iii) `exercise_13_C_6b_iii`: compared with the pooling equilibrium of (a) (all financed at
  `R = (1 + r)/p̄` if `p̄Π ≥ 1 + r`, none otherwise), the bad type is weakly worse off (strictly
  if loans are made in (a)); the good type is strictly better off if (a) has no lending, and
  otherwise better off iff `(ρ - r)x* < (1 + r)(p_G/p̄ - 1)`; both cases occur
  (`exercise_13_C_6b_iii_instance`).
-/

namespace MWG.AdverseSelection

/-- **Exercise 13.C.6** (MWG, p. 475). The loan market: success probabilities `p_G`, `p_B`,
fraction `λ` of good projects, profit `Π`, the banks' rate `r`, the entrepreneur's rate `ρ`. -/
structure LoanModel where
  pG : ℝ
  pB : ℝ
  lam : ℝ
  Pf : ℝ
  r : ℝ
  rho : ℝ

namespace LoanModel

/-- **Exercise 13.C.6** (MWG, p. 475). The assumptions. -/
structure Valid (L : LoanModel) : Prop where
  pB_pos : 0 < L.pB
  lt : L.pB < L.pG
  pG_le : L.pG ≤ 1
  lam_pos : 0 < L.lam
  lam_lt : L.lam < 1
  r_nonneg : 0 ≤ L.r
  rho_gt : L.r < L.rho
  good : 1 + L.r < L.pG * L.Pf
  bad : L.pB * L.Pf < 1 + L.r

/-- The success probability of type `t` (`true` = good). -/
def p (L : LoanModel) (t : Bool) : ℝ := if t then L.pG else L.pB

/-- The average success probability `bp_G + (1 - b)p_B` under the belief `b`. -/
def pbar (L : LoanModel) (b : ℝ) : ℝ := b * L.pG + (1 - b) * L.pB

/-- **Exercise 13.C.6(b)(i)** (MWG, p. 475). The payoff `p_t(Π - R) - (1 + ρ)x` of an
entrepreneur of type `t` who contributes `x` and goes ahead with repayment `R`. -/
def entPay (L : LoanModel) (t : Bool) (R x : ℝ) : ℝ := L.p t * (L.Pf - R) - (1 + L.rho) * x

/-- **Exercise 13.C.6(b)** (MWG, p. 475). The zero-profit repayment on a loan of `1 - x` under
the belief `b`. -/
noncomputable def repay (L : LoanModel) (x b : ℝ) : ℝ := (1 + L.r) * (1 - x) / L.pbar b

/-- **Exercise 13.C.6(b)** (MWG, p. 475). The entrepreneur's payoff in the game after offering
`x` when the banks hold belief `b`: she goes ahead iff that is profitable. -/
noncomputable def gamePay (L : LoanModel) (t : Bool) (x b : ℝ) : ℝ :=
  max (L.entPay t (L.repay x b) x) 0

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). A pure strategy PBE (reduced form): contributions
`x_t ∈ [0, 1]`, beliefs in `[0, 1]` given by Bayes' rule on the path, and each type's offer
optimal given the banks' zero-profit responses. -/
def IsLoanPBE (L : LoanModel) (xS : Bool → ℝ) (bel : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ xS t ∧ xS t ≤ 1) ∧ (∀ x, 0 ≤ bel x ∧ bel x ≤ 1) ∧
    (∀ t x, 0 ≤ x → x ≤ 1 → L.gamePay t x (bel x) ≤ L.gamePay t (xS t) (bel (xS t))) ∧
    (xS false ≠ xS true → bel (xS true) = 1 ∧ bel (xS false) = 0) ∧
    (xS false = xS true → bel (xS true) = L.lam)

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). The good type's minimal separating contribution
`x* = p_B(p_GΠ - (1 + r))/(p_G(1 + ρ) - p_B(1 + r))`. -/
noncomputable def xStar (L : LoanModel) : ℝ :=
  L.pB * (L.pG * L.Pf - (1 + L.r)) / (L.pG * (1 + L.rho) - L.pB * (1 + L.r))

variable {L : LoanModel}

theorem Valid.den_pos (hL : L.Valid) : 0 < L.pG * (1 + L.rho) - L.pB * (1 + L.r) := by
  have := hL.r_nonneg
  have := hL.rho_gt
  nlinarith [hL.lt, hL.pB_pos]

theorem Valid.pbar_pos (hL : L.Valid) {b : ℝ} (hb : 0 ≤ b) : 0 < L.pbar b := by
  unfold pbar; nlinarith [hL.lt, hL.pB_pos]

/-- **Exercise 13.C.6(b)** (MWG, p. 475). At the repayment `repay x b` a bank lending `1 - x`
breaks even under the belief `b`. -/
theorem exercise_13_C_6b_bank_zero_profit (hL : L.Valid) {x b : ℝ} (hb : 0 ≤ b) :
    L.pbar b * L.repay x b - (1 + L.r) * (1 - x) = 0 := by
  rw [repay, mul_div_cancel₀ _ (hL.pbar_pos hb).ne', sub_self]

/-- **Exercise 13.C.6(b)(i)** (MWG, p. 475). The payoffs at the zero-profit repayments: a good
type identified as good gets `p_GΠ - (1 + r) - (ρ - r)x`; a bad type identified as bad gets
`p_BΠ - (1 + r) - (ρ - r)x < 0`; a bad type taken for good gets
`p_BΠ - (p_B/p_G)(1 + r)(1 - x) - (1 + ρ)x`; a good type taken for bad gets
`p_GΠ - (p_G/p_B)(1 + r)(1 - x) - (1 + ρ)x`. -/
theorem exercise_13_C_6b_i (hL : L.Valid) (x : ℝ) (hx : 0 ≤ x) :
    L.entPay true (L.repay x 1) x = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * x ∧
      L.entPay false (L.repay x 0) x = L.pB * L.Pf - (1 + L.r) - (L.rho - L.r) * x ∧
      L.entPay false (L.repay x 0) x < 0 ∧
      L.entPay false (L.repay x 1) x =
        L.pB * L.Pf - L.pB / L.pG * ((1 + L.r) * (1 - x)) - (1 + L.rho) * x ∧
      L.entPay true (L.repay x 0) x =
        L.pG * L.Pf - L.pG / L.pB * ((1 + L.r) * (1 - x)) - (1 + L.rho) * x := by
  have hG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hB := hL.pB_pos
  have h1 : L.pbar 1 = L.pG := by simp [pbar]
  have h0 : L.pbar 0 = L.pB := by simp [pbar]
  simp only [entPay, repay, h1, h0, p, ite_true, Bool.false_eq_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp
    nlinarith [hL.bad, hL.rho_gt]
  · field_simp
  · field_simp

/-- The bad type's payoff from being taken for good is `≤ 0` iff `x ≥ x*`. -/
theorem Valid.bad_mimic_iff (hL : L.Valid) (x : ℝ) :
    L.entPay false (L.repay x 1) x ≤ 0 ↔ L.xStar ≤ x := by
  have hG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hD := hL.den_pos
  have h1 : L.pbar 1 = L.pG := by simp [pbar]
  simp only [entPay, repay, h1, p, Bool.false_eq_true, ite_false, xStar]
  rw [div_le_iff₀ hD]
  have e : L.pB * (L.Pf - (1 + L.r) * (1 - x) / L.pG) - (1 + L.rho) * x =
      (L.pB * (L.pG * L.Pf - (1 + L.r)) - x * (L.pG * (1 + L.rho) - L.pB * (1 + L.r))) /
        L.pG := by
    field_simp; ring
  rw [e, div_le_iff₀ hG, zero_mul, sub_nonpos]

/-- `0 < x* < 1`. -/
theorem Valid.xStar_mem (hL : L.Valid) : 0 < L.xStar ∧ L.xStar < 1 := by
  have hD := hL.den_pos
  have hB := hL.pB_pos
  unfold xStar
  refine ⟨div_pos (mul_pos hB (by linarith [hL.good])) hD, (div_lt_one hD).2 ?_⟩
  nlinarith [hL.bad, hL.rho_gt, hL.lt]

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). Separating PBE: `(x_G, x_B)` with `x_G ≠ x_B` in
`[0, 1]` is the outcome of a PBE iff `x* ≤ x_G`. -/
theorem exercise_13_C_6b_ii_separating (hL : L.Valid) {xG xB : ℝ} (hG0 : 0 ≤ xG) (hG1 : xG ≤ 1)
    (hB0 : 0 ≤ xB) (hB1 : xB ≤ 1) (hne : xB ≠ xG) :
    (∃ bel, L.IsLoanPBE (fun t => if t then xG else xB) bel) ↔ L.xStar ≤ xG := by
  have hpG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hbad0 : ∀ x, 0 ≤ x → L.gamePay false x 0 = 0 := fun x hx =>
    max_eq_right ((exercise_13_C_6b_i hL x hx).2.2.1).le
  constructor
  · rintro ⟨bel, -, -, hopt, hB, -⟩
    obtain ⟨h1, h0⟩ := hB (by simpa using hne)
    have := hopt false xG hG0 hG1
    simp only [Bool.false_eq_true, ite_false] at this h0
    simp only [ite_true] at h1
    rw [h1, h0, hbad0 xB hB0, gamePay, max_le_iff] at this
    exact (hL.bad_mimic_iff xG).1 this.1
  · intro hx
    refine ⟨fun x => if x = xG then 1 else 0, fun t => ?_, fun x => ?_, fun t x hx0 hx1 => ?_,
      fun _ => ?_, fun h => absurd h (by simpa using hne)⟩
    · cases t
      · exact ⟨hB0, hB1⟩
      · exact ⟨hG0, hG1⟩
    · dsimp only
      split_ifs <;> norm_num
    · cases t
      · simp only [Bool.false_eq_true, hne, ↓reduceIte]
        rw [hbad0 xB hB0]
        by_cases hxG : x = xG
        · simp only [hxG, ↓reduceIte, gamePay]
          exact max_le ((hL.bad_mimic_iff xG).2 hx) le_rfl
        · simp only [hxG, ↓reduceIte]
          rw [hbad0 x hx0]
      · simp only [↓reduceIte]
        by_cases hxG : x = xG
        · simp [hxG]
        · simp only [hxG, ↓reduceIte, gamePay]
          rw [(exercise_13_C_6b_i hL x hx0).2.2.2.2, (exercise_13_C_6b_i hL xG hG0).1]
          have hq0 : 0 ≤ L.pG / L.pB := (div_pos hpG hL.pB_pos).le
          have hpB := hL.pB_pos.ne'
          have hk : L.pG / L.pB * ((1 + L.r) * (1 - x)) - (1 - x) * (L.pG * L.Pf) =
              (1 - x) * (L.pG / L.pB) * ((1 + L.r) - L.pB * L.Pf) := by
            field_simp
          have hk0 : 0 ≤ (1 - x) * (L.pG / L.pB) * ((1 + L.r) - L.pB * L.Pf) :=
            mul_nonneg (mul_nonneg (sub_nonneg.2 hx1) hq0) (sub_nonneg.2 hL.bad.le)
          have hVge : L.pG * L.Pf - (1 + L.rho) ≤
              L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * xG := by nlinarith [hL.rho_gt]
          refine max_le ?_ (le_max_right _ _)
          rcases le_or_gt 0 (L.pG * L.Pf - (1 + L.rho)) with h | h
          · exact le_max_of_le_left (by nlinarith)
          · exact le_max_of_le_right (by nlinarith)
    · simp only [Bool.false_eq_true, hne, ↓reduceIte, and_self]

/-- The good type's payoff when identified, `p_GΠ - (1 + r) - (ρ - r)x`, at `x*`:
`(p_GΠ - (1 + r))(1 + ρ)(p_G - p_B)/(p_G(1 + ρ) - p_B(1 + r)) > 0`. -/
theorem Valid.goodPay_xStar (hL : L.Valid) :
    L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar =
        (L.pG * L.Pf - (1 + L.r)) * (1 + L.rho) * (L.pG - L.pB) /
          (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) ∧
      0 < L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
  have hD := hL.den_pos
  have e : L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar =
      (L.pG * L.Pf - (1 + L.r)) * (1 + L.rho) * (L.pG - L.pB) /
        (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) := by
    have hxs : L.xStar * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * (L.pG * L.Pf - (1 + L.r)) := div_mul_cancel₀ _ hD.ne'
    rw [eq_div_iff hD.ne']
    linear_combination (-(L.rho - L.r)) * hxs
  refine ⟨e, ?_⟩
  rw [e]
  have := hL.r_nonneg
  have := hL.rho_gt
  exact div_pos (mul_pos (mul_pos (by linarith [hL.good]) (by linarith))
    (by linarith [hL.lt])) hD

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). The best separating PBE: `x_G = x*` (with
`x_B = 0`) is a separating PBE outcome; in it the good type earns
`p_GΠ - (1 + r) - (ρ - r)x* > 0`, and in every separating PBE the bad type earns `0` and the
good type at most this (the banks earn zero by `exercise_13_C_6b_bank_zero_profit`). -/
theorem exercise_13_C_6b_ii_best (hL : L.Valid) :
    (∃ bel, L.IsLoanPBE (fun t => if t then L.xStar else 0) bel) ∧
      L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar ∧
      0 < L.gamePay true L.xStar 1 ∧
      ∀ xG xB bel, L.IsLoanPBE (fun t => if t then xG else xB) bel → xB ≠ xG →
        L.gamePay true xG (bel xG) ≤ L.gamePay true L.xStar 1 ∧
          L.gamePay false xB (bel xB) = 0 := by
  obtain ⟨hx0, hx1⟩ := hL.xStar_mem
  obtain ⟨-, hVpos⟩ := hL.goodPay_xStar
  have hV : L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
    rw [gamePay, (exercise_13_C_6b_i hL _ hx0.le).1, max_eq_left hVpos.le]
  refine ⟨(exercise_13_C_6b_ii_separating hL hx0.le hx1.le le_rfl zero_le_one hx0.ne).2 le_rfl,
    hV, hV ▸ hVpos, fun xG xB bel h hne => ?_⟩
  have hxs := h
  obtain ⟨hmem, -, -, hB, -⟩ := h
  obtain ⟨h1, h0⟩ := hB (by simpa using hne)
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h0
  have hG := hmem true
  have hBm := hmem false
  simp only [ite_true, Bool.false_eq_true, ite_false] at hG hBm
  have hge := (exercise_13_C_6b_ii_separating hL hG.1 hG.2 hBm.1 hBm.2 hne).1 ⟨bel, hxs⟩
  refine ⟨?_, ?_⟩
  · rw [h1, hV, gamePay, (exercise_13_C_6b_i hL _ hG.1).1]
    refine max_le ?_ hVpos.le
    nlinarith [hL.rho_gt]
  · rw [h0, gamePay]
    exact max_eq_right ((exercise_13_C_6b_i hL xB hBm.1).2.2.1).le

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). Comparative statics of the good type's
contribution `x*` (between valid parameter values): it rises with `p_B`, `p_G` and `Π`, falls
with `r` and `ρ`, and does not depend on `λ`. -/
theorem exercise_13_C_6b_ii_statics (hL : L.Valid) :
    (∀ pB', ({ L with pB := pB' } : LoanModel).Valid → L.pB < pB' →
      L.xStar < ({ L with pB := pB' } : LoanModel).xStar) ∧
    (∀ pG', ({ L with pG := pG' } : LoanModel).Valid → L.pG < pG' →
      L.xStar < ({ L with pG := pG' } : LoanModel).xStar) ∧
    (∀ Pf', ({ L with Pf := Pf' } : LoanModel).Valid → L.Pf < Pf' →
      L.xStar < ({ L with Pf := Pf' } : LoanModel).xStar) ∧
    (∀ r', ({ L with r := r' } : LoanModel).Valid → L.r < r' →
      ({ L with r := r' } : LoanModel).xStar < L.xStar) ∧
    (∀ rho', ({ L with rho := rho' } : LoanModel).Valid → L.rho < rho' →
      ({ L with rho := rho' } : LoanModel).xStar < L.xStar) ∧
    (∀ lam', ({ L with lam := lam' } : LoanModel).xStar = L.xStar) := by
  have hD := hL.den_pos
  have hB := hL.pB_pos
  have hA : 0 < L.pG * L.Pf - (1 + L.r) := by linarith [hL.good]
  have hc : L.pB * L.Pf < 1 + L.rho := by linarith [hL.bad, hL.rho_gt]
  have hr0 := hL.r_nonneg
  refine ⟨fun pB' hV h => ?_, fun pG' hV h => ?_, fun Pf' hV h => ?_, fun r' hV h => ?_,
    fun rho' hV h => ?_, fun _ => rfl⟩
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD hD']
    have e : pB' * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) -
        L.pB * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - pB' * (1 + L.r)) =
        (pB' - L.pB) * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho)) := by ring
    have : 0 < (pB' - L.pB) * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho)) :=
      mul_pos (mul_pos (by linarith) hA) (mul_pos (hB.trans hL.lt) (by linarith [hL.rho_gt]))
    linarith
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD hD']
    have e : L.pB * (pG' * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) -
        L.pB * (L.pG * L.Pf - (1 + L.r)) * (pG' * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * (1 + L.r) * (pG' - L.pG) * (1 + L.rho - L.pB * L.Pf) := by ring
    have : 0 < L.pB * (1 + L.r) * (pG' - L.pG) * (1 + L.rho - L.pB * L.Pf) :=
      mul_pos (mul_pos (mul_pos hB (by linarith)) (by linarith)) (by linarith)
    linarith
  · simp only [xStar]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left
      (by nlinarith [hB.trans hL.lt]) hB) hD
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD' hD]
    have e : L.pB * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + r')) -
        L.pB * (L.pG * L.Pf - (1 + r')) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * L.pG * (r' - L.r) * (1 + L.rho - L.pB * L.Pf) := by ring
    have : 0 < L.pB * L.pG * (r' - L.r) * (1 + L.rho - L.pB * L.Pf) :=
      mul_pos (mul_pos (mul_pos hB (hB.trans hL.lt)) (by linarith)) (by linarith)
    linarith
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    exact div_lt_div_of_pos_left (mul_pos hB hA) hD
      (by nlinarith [hB.trans hL.lt])

/-- **Exercise 13.C.6(a)** (MWG, p. 475), payoffs: in the pooling equilibrium of (a) all projects
are financed at `R = (1 + r)/p̄` if `p̄Π ≥ 1 + r` (`p̄ = λp_G + (1 - λ)p_B`), and type `t` earns
`p_t(Π - R)`; otherwise nothing is financed. -/
noncomputable def poolPay (L : LoanModel) (t : Bool) : ℝ :=
  if 1 + L.r ≤ L.pbar L.lam * L.Pf then L.p t * (L.Pf - (1 + L.r) / L.pbar L.lam) else 0

/-- **Exercise 13.C.6(b)(iii)** (MWG, p. 476). Compared with the equilibrium of (a): the bad type
(who earns `0` in the separating PBE) is weakly worse off, strictly when loans are made in (a);
the good type is strictly better off if (a) has no lending, and otherwise better off iff
`(ρ - r)x* < (1 + r)(p_G/p̄ - 1)`. -/
theorem exercise_13_C_6b_iii (hL : L.Valid) :
    0 ≤ L.poolPay false ∧ (1 + L.r < L.pbar L.lam * L.Pf → 0 < L.poolPay false) ∧
      (L.pbar L.lam * L.Pf < 1 + L.r → L.poolPay true < L.gamePay true L.xStar 1) ∧
      (1 + L.r ≤ L.pbar L.lam * L.Pf →
        (L.poolPay true < L.gamePay true L.xStar 1 ↔
          (L.rho - L.r) * L.xStar < (1 + L.r) * (L.pG / L.pbar L.lam - 1))) := by
  have hp := hL.pbar_pos hL.lam_pos.le
  have hB := hL.pB_pos
  obtain ⟨hx0, -⟩ := hL.xStar_mem
  obtain ⟨-, hVpos⟩ := hL.goodPay_xStar
  have hV : L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
    rw [gamePay, (exercise_13_C_6b_i hL _ hx0.le).1, max_eq_left hVpos.le]
  have hR : 1 + L.r ≤ L.pbar L.lam * L.Pf → 0 ≤ L.Pf - (1 + L.r) / L.pbar L.lam :=
    fun h => sub_nonneg.2 ((div_le_iff₀ hp).2 (by linarith))
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold poolPay
    split_ifs with h
    · exact mul_nonneg hB.le (hR h)
    · exact le_rfl
  · simp only [poolPay, h.le, ↓reduceIte, p, Bool.false_eq_true]
    exact mul_pos hB (sub_pos.2 ((div_lt_iff₀ hp).2 (by linarith)))
  · simp only [poolPay, not_le.2 h, ↓reduceIte]
    rw [hV]
    exact hVpos
  · simp only [poolPay, h, ↓reduceIte, p]
    rw [hV]
    have e : L.pG * (L.Pf - (1 + L.r) / L.pbar L.lam) =
        L.pG * L.Pf - (1 + L.r) - (1 + L.r) * (L.pG / L.pbar L.lam - 1) := by
      field_simp
      ring
    rw [e]
    constructor <;> intro h' <;> linarith

/-- **Exercise 13.C.6(b)**, the instances: `p_G = 1`, `p_B = 1/2`, `Π = 3/2`, `r = 0`, `ρ = 1`, and
`λ = 1/4` or `λ = 9/10`. -/
noncomputable def loanModel (lam : ℝ) : LoanModel where
  pG := 1
  pB := 1 / 2
  lam := lam
  Pf := 3 / 2
  r := 0
  rho := 1

theorem loanModel_valid {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : (loanModel lam).Valid where
  pB_pos := by norm_num [loanModel]
  lt := by norm_num [loanModel]
  pG_le := by norm_num [loanModel]
  lam_pos := h0
  lam_lt := h1
  r_nonneg := le_rfl
  rho_gt := by norm_num [loanModel]
  good := by norm_num [loanModel]
  bad := by norm_num [loanModel]

/-- **Exercise 13.C.6(b)(ii)-(iii)**, instances (MWG, pp. 475-476). Here `x* = 1/6` and the good
type earns `1/3` in the best separating PBE, whatever `λ`. With `λ = 1/4` nothing is financed in
(a) and the good type is better off separating; with `λ = 9/10` all projects are financed in
(a), the good type earns `17/38 > 1/3` there and the bad type `17/76 > 0`. -/
theorem exercise_13_C_6b_iii_instance :
    (loanModel (1 / 4)).xStar = 1 / 6 ∧ (loanModel (1 / 4)).gamePay true (1 / 6) 1 = 1 / 3 ∧
      (loanModel (9 / 10)).gamePay true (1 / 6) 1 = 1 / 3 ∧
      (loanModel (1 / 4)).poolPay true = 0 ∧ (loanModel (1 / 4)).poolPay false = 0 ∧
      (loanModel (9 / 10)).poolPay true = 17 / 38 ∧ (loanModel (9 / 10)).poolPay false = 17 / 76 ∧
      (loanModel (1 / 4)).poolPay true < (loanModel (1 / 4)).gamePay true (1 / 6) 1 ∧
      (loanModel (9 / 10)).gamePay true (1 / 6) 1 < (loanModel (9 / 10)).poolPay true := by
  have hg : ∀ lam : ℝ, (loanModel lam).gamePay true (1 / 6) 1 = 1 / 3 := fun lam => by
    simp only [gamePay, entPay, repay, pbar, p, loanModel, ite_true]
    norm_num
  have hpl : (loanModel (1 / 4)).poolPay true = 0 ∧ (loanModel (1 / 4)).poolPay false = 0 := by
    simp only [poolPay, pbar, loanModel]
    norm_num
  have hph : (loanModel (9 / 10)).poolPay true = 17 / 38 ∧
      (loanModel (9 / 10)).poolPay false = 17 / 76 := by
    simp only [poolPay, pbar, p, loanModel]
    norm_num
  refine ⟨by simp only [xStar, loanModel]; norm_num, hg _, hg _, hpl.1, hpl.2, hph.1, hph.2,
    ?_, ?_⟩
  · rw [hpl.1, hg]; norm_num
  · rw [hph.1, hg]; norm_num

/-- **Exercise 13.C.6(b)(ii)**, instance of `exercise_13_C_6b_ii_statics` (MWG, p. 475): the base
model `p_G = 4/5`, `p_B = 2/5`, `λ = 1/2`, `Π = 2`, `r = 0`, `ρ = 1` and each single-parameter
change used there (`p_B = 9/20`, `p_G = 9/10`, `Π = 9/4`, `r = 1/10`, `ρ = 2`) are valid. -/
theorem exercise_13_C_6b_ii_statics_instance :
    let L0 : LoanModel := ⟨4 / 5, 2 / 5, 1 / 2, 2, 0, 1⟩
    L0.Valid ∧ ({ L0 with pB := 9 / 20 } : LoanModel).Valid ∧
      ({ L0 with pG := 9 / 10 } : LoanModel).Valid ∧ ({ L0 with Pf := 9 / 4 } : LoanModel).Valid ∧
      ({ L0 with r := 1 / 10 } : LoanModel).Valid ∧ ({ L0 with rho := 2 } : LoanModel).Valid := by
  intro L0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0],
      by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0]⟩

end LoanModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A general two-type screening game

MWG, Section 13.D, pp. 460-465, and Exercises 13.D.1-13.D.3 (p. 476).

The screening game of Section 13.D with a general space of contracts `k ∈ ℝ × ℝ`: type `b`
(`true` with probability `λ`, `false` with probability `1 - λ`) gets utility `U b k` from
contract `k`, and the firm that employs (or insures) her gets `P b k`. Two firms announce finite
menus of admissible contracts (`Menu`); each type chooses from the union of the menus
(`Chooses`): a utility maximizing contract with the lowest tie-breaking key `key k` among the
best ones, accepted iff its utility is at least the reservation utility `ρ b` (otherwise she
takes her outside option, which yields no profit). A firm gets a type if it offers her chosen
contract, half of the time if both firms offer it (`SigModel.share`). `IsEq` is the pure SPNE
(the Nash condition of Definition 8.D.1 given the stage-2 choices), as in `SigModel.IsScreenEq`.

The model of Section 13.D is the case `U b (w, t) = w - c(t, θ_b)`, `P b (w, t) = θ_b - w`,
`key (w, t) = t`; Exercises 13.D.1-13.D.3 are other cases.

* `IsEq.zero`: Lemma 13.D.1 in this generality. If raising every contract's utility uniformly
  (`sw δ`) keeps contracts admissible and tie-breaking keys, and changes profits continuously,
  then in every SPNE both firms earn zero profits.
* `typeProfit_capture`, `no_capture_of_other`, `typeProfit_nonneg_of`: profits of deviations.
-/

namespace MWG.AdverseSelection

/-- **Section 13.D** (MWG, pp. 460-461). A two-type screening game: utilities `U`, profits `P`,
reservation utilities `ρ`, the tie-breaking key, the probability `λ` of type `true`, and the
admissible contracts. -/
structure ScrGame where
  U : Bool → ℝ × ℝ → ℝ
  P : Bool → ℝ × ℝ → ℝ
  ρ : Bool → ℝ
  key : ℝ × ℝ → ℝ
  lam : ℝ
  adm : ℝ × ℝ → Prop

namespace ScrGame

variable (G : ScrGame)

/-- A menu: a finite set of admissible contracts. -/
def Menu (A : Finset (ℝ × ℝ)) : Prop := ∀ k ∈ A, G.adm k

/-- **Section 13.D** (MWG, p. 461). Type `b` chooses contract `k` from the offered set `V`. -/
def Chooses (b : Bool) (V : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : Prop :=
  k ∈ V ∧ G.ρ b ≤ G.U b k ∧ (∀ k' ∈ V, G.U b k' ≤ G.U b k) ∧
    ∀ k' ∈ V, G.U b k' = G.U b k → G.key k ≤ G.key k'

/-- Contracts are identified by any type's utility and the tie-breaking key. -/
def Inj : Prop := ∀ b k k', G.U b k = G.U b k' → G.key k = G.key k' → k = k'

open Classical in
/-- The firm's expected profit from a worker of type `b`. -/
noncomputable def typeProfit (b : Bool) (own other : Finset (ℝ × ℝ)) : ℝ :=
  if h : ∃ k, G.Chooses b (own ∪ other) k then
    SigModel.share own other h.choose * G.P b h.choose else 0

/-- **Section 13.D** (MWG, p. 461). A firm's expected profit. -/
noncomputable def profit (own other : Finset (ℝ × ℝ)) : ℝ :=
  (1 - G.lam) * G.typeProfit false own other + G.lam * G.typeProfit true own other

/-- **Section 13.D** (MWG, p. 461). A pure strategy SPNE of the screening game. -/
def IsEq (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  G.Menu A₁ ∧ G.Menu A₂ ∧ (∀ B, G.Menu B → G.profit B A₂ ≤ G.profit A₁ A₂) ∧
    ∀ B, G.Menu B → G.profit B A₁ ≤ G.profit A₂ A₁

variable {G}

theorem chooses_unique (hI : G.Inj) {b : Bool} {V : Finset (ℝ × ℝ)} {k k' : ℝ × ℝ}
    (h : G.Chooses b V k) (h' : G.Chooses b V k') : k = k' := by
  have hu : G.U b k = G.U b k' := le_antisymm (h'.2.2.1 k h.1) (h.2.2.1 k' h'.1)
  exact hI b k k' hu (le_antisymm (h.2.2.2 k' h'.1 hu.symm) (h'.2.2.2 k h.1 hu))

theorem exists_chooses (b : Bool) {V : Finset (ℝ × ℝ)} (h : ∃ k ∈ V, G.ρ b ≤ G.U b k) :
    ∃ k, G.Chooses b V k := by
  obtain ⟨k0, hk0, hu0⟩ := h
  obtain ⟨k1, hk1, hmax⟩ := V.exists_max_image (G.U b) ⟨k0, hk0⟩
  set W := V.filter (fun k => G.U b k = G.U b k1)
  obtain ⟨k, hk, hmin⟩ := W.exists_min_image G.key ⟨k1, by simp [W, hk1]⟩
  simp only [W, Finset.mem_filter] at hk
  refine ⟨k, hk.1, by rw [hk.2]; exact hu0.trans (hmax k0 hk0), fun k' hk' => ?_,
    fun k' hk' he => hmin k' (by simp [W, hk', he.trans hk.2])⟩
  rw [hk.2]; exact hmax k' hk'

theorem chooses_of_strict {b : Bool} {V : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ V)
    (h0 : G.ρ b ≤ G.U b k) (hs : ∀ k' ∈ V, k' ≠ k → G.U b k' < G.U b k) :
    G.Chooses b V k := by
  refine ⟨hk, h0, fun k' hk' => ?_, fun k' hk' he => ?_⟩
  · by_cases h : k' = k
    · rw [h]
    · exact (hs k' hk' h).le
  · by_cases h : k' = k
    · rw [h]
    · exact absurd he (hs k' hk' h).ne

theorem typeProfit_of_chooses (hI : G.Inj) {b : Bool} {own other : Finset (ℝ × ℝ)}
    {k : ℝ × ℝ} (h : G.Chooses b (own ∪ other) k) :
    G.typeProfit b own other = SigModel.share own other k * G.P b k := by
  have hex : ∃ k, G.Chooses b (own ∪ other) k := ⟨k, h⟩
  rw [typeProfit, dite_eq_left_of_eq_true (eq_true hex), chooses_unique hI hex.choose_spec h]

theorem typeProfit_of_not {b : Bool} {own other : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, G.Chooses b (own ∪ other) k) : G.typeProfit b own other = 0 := by
  rw [typeProfit, dite_eq_right_of_eq_false (eq_false h)]

/-- The firms' profits from type `b` add up to the profit on her chosen contract. -/
theorem typeProfit_add (hI : G.Inj) {b : Bool} {A₁ A₂ : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : G.Chooses b (A₁ ∪ A₂) k) :
    G.typeProfit b A₁ A₂ + G.typeProfit b A₂ A₁ = G.P b k := by
  have h' : G.Chooses b (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_chooses hI h, typeProfit_of_chooses hI h', ← add_mul,
    SigModel.share_add h.1, one_mul]

theorem typeProfit_add_not {b : Bool} {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, G.Chooses b (A₁ ∪ A₂) k) :
    G.typeProfit b A₁ A₂ + G.typeProfit b A₂ A₁ = 0 := by
  have h' : ¬ ∃ k, G.Chooses b (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_not h, typeProfit_of_not h', add_zero]

theorem typeProfit_empty (hI : G.Inj) (b : Bool) (other : Finset (ℝ × ℝ)) :
    G.typeProfit b ∅ other = 0 := by
  by_cases h : ∃ k, G.Chooses b (∅ ∪ other) k
  · obtain ⟨k, hk⟩ := h
    rw [typeProfit_of_chooses hI hk]; simp [SigModel.share]
  · exact typeProfit_of_not h

theorem profit_empty (hI : G.Inj) (other : Finset (ℝ × ℝ)) : G.profit ∅ other = 0 := by
  simp [profit, typeProfit_empty hI]

theorem IsEq.symm {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) : G.IsEq A₂ A₁ :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem menu_empty : G.Menu ∅ := fun _ h => absurd h (Finset.notMem_empty _)

/-- Equilibrium profits are nonnegative (a firm can offer nothing). -/
theorem IsEq.nonneg (hI : G.Inj) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) :
    0 ≤ G.profit A₁ A₂ := by
  have := h.2.2.1 ∅ menu_empty
  rwa [profit_empty hI] at this

/-- A deviation `B` containing a contract `k` that type `b` strictly prefers to everything else
on offer, with utility at least `ρ b`, gets `P b k` from her. -/
theorem typeProfit_capture (hI : G.Inj) {b : Bool} {other B : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (hk : k ∈ B) (h0 : G.ρ b ≤ G.U b k) (hs : ∀ k' ∈ other, G.U b k' < G.U b k)
    (hB : ∀ k' ∈ B, k' ≠ k → G.U b k' < G.U b k) :
    G.typeProfit b B other = G.P b k := by
  have hch : G.Chooses b (B ∪ other) k := by
    refine chooses_of_strict (Finset.mem_union_left _ hk) h0 fun k' hk' hne => ?_
    rcases Finset.mem_union.1 hk' with h | h
    · exact hB k' h hne
    · exact hs k' h
  have hno : k ∉ other := fun h => lt_irrefl _ (hs k h)
  rw [typeProfit_of_chooses hI hch]
  simp [SigModel.share, hk, hno]

/-- A single-contract deviation `{k}` gets nothing from type `b` if some contract of the other
firm gives `b` strictly more than `k`. -/
theorem no_capture_of_other (hI : G.Inj) {b : Bool} {other : Finset (ℝ × ℝ)} {k k0 : ℝ × ℝ}
    (hk0 : k0 ∈ other) (h : G.U b k < G.U b k0) : G.typeProfit b {k} other = 0 := by
  by_cases hex : ∃ k', G.Chooses b ({k} ∪ other) k'
  · obtain ⟨k', hk'⟩ := hex
    have hne : k' ≠ k := by
      rintro rfl
      exact absurd (hk'.2.2.1 k0 (Finset.mem_union_right _ hk0)) (not_le.2 h)
    rw [typeProfit_of_chooses hI hk']
    simp [SigModel.share, hne]
  · exact typeProfit_of_not hex

/-- A deviation whose contracts all make a nonnegative profit on type `b` earns a nonnegative
profit from her. -/
theorem typeProfit_nonneg_of (hI : G.Inj) {b : Bool} {other B : Finset (ℝ × ℝ)}
    (hB : ∀ k ∈ B, 0 ≤ G.P b k) : 0 ≤ G.typeProfit b B other := by
  by_cases hex : ∃ k', G.Chooses b (B ∪ other) k'
  · obtain ⟨k', hk'⟩ := hex
    rw [typeProfit_of_chooses hI hk']
    by_cases hm : k' ∈ B
    · exact mul_nonneg (SigModel.share_nonneg _ _ _) (hB k' hm)
    · simp [SigModel.share, hm]
  · exact (typeProfit_of_not hex).ge

/-- The firms' profits add up to the expected profit on the chosen contracts. -/
theorem profit_add (A₁ A₂ : Finset (ℝ × ℝ)) :
    G.profit A₁ A₂ + G.profit A₂ A₁ =
      (1 - G.lam) * (G.typeProfit false A₁ A₂ + G.typeProfit false A₂ A₁) +
        G.lam * (G.typeProfit true A₁ A₂ + G.typeProfit true A₂ A₁) := by
  unfold profit; ring

/-- A uniform positive margin below finitely many strict inequalities. -/
theorem exists_gap {X : Type*} (S : Finset X) (f : X → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ S, δ < f x := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨1, one_pos, fun x hx => by simp [hS] at hx⟩
  · obtain ⟨x0, hx0, hmin⟩ := S.exists_min_image f hS
    exact ⟨f x0 / 2, half_pos (hf x0 hx0), fun x hx => by linarith [hmin x hx, hf x0 hx0]⟩

/-- The Bertrand deviation for one type: offering every contract on the market, sweetened by a
small `δ`, keeps (up to `η`) the profit both firms together make on type `b`. -/
theorem dev_type (hI : G.Inj) (sw : ℝ → ℝ × ℝ → ℝ × ℝ)
    (hswU : ∀ δ b k, G.U b (sw δ k) = G.U b k + δ) (hswkey : ∀ δ k, G.key (sw δ k) = G.key k)
    (hswP : ∀ b k η, 0 < η → ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → G.P b k - η < G.P b (sw δ k))
    (b : Bool) (own other : Finset (ℝ × ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      G.typeProfit b own other + G.typeProfit b other own - η ≤
        G.typeProfit b ((own ∪ other).image (sw δ)) other := by
  by_cases hex : ∃ k, G.Chooses b (own ∪ other) k
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨δ₀, hδ₀, hP⟩ := hswP b k η hη
    refine ⟨δ₀, hδ₀, fun δ hδ hδle => ?_⟩
    rw [typeProfit_add hI hk]
    set B := (own ∪ other).image (sw δ)
    have hch : G.Chooses b (B ∪ other) (sw δ k) := by
      refine ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk.1), ?_, fun k' hk' => ?_,
        fun k' hk' hu => ?_⟩
      · rw [hswU]; linarith [hk.2.1]
      · rcases Finset.mem_union.1 hk' with h' | h'
        · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
          rw [hswU, hswU]; linarith [hk.2.2.1 k'' hk'']
        · rw [hswU]; linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
      · rcases Finset.mem_union.1 hk' with h' | h'
        · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
          rw [hswU, hswU] at hu
          rw [hswkey, hswkey]
          exact hk.2.2.2 k'' hk'' (by linarith)
        · rw [hswU] at hu
          linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
    have hno : sw δ k ∉ other := fun hm => by
      have := hk.2.2.1 _ (Finset.mem_union_right _ hm)
      rw [hswU] at this; linarith
    have hmem : sw δ k ∈ B := Finset.mem_image_of_mem _ hk.1
    rw [typeProfit_of_chooses hI hch]
    simp only [SigModel.share, hmem, hno, ↓reduceIte, one_mul]
    linarith [hP δ hδ hδle]
  · have hlt : ∀ k ∈ own ∪ other, G.U b k < G.ρ b := fun k hk => by
      by_contra hle
      exact hex (exists_chooses b ⟨k, hk, not_lt.1 hle⟩)
    obtain ⟨δ₀, hδ₀, hgap⟩ := exists_gap (own ∪ other) (fun k => G.ρ b - G.U b k)
      (fun k hk => by have := hlt k hk; linarith)
    refine ⟨δ₀, hδ₀, fun δ hδ hδle => ?_⟩
    rw [typeProfit_add_not hex]
    have hno : ¬ ∃ k, G.Chooses b ((own ∪ other).image (sw δ) ∪ other) k := by
      rintro ⟨k, hk⟩
      rcases Finset.mem_union.1 hk.1 with h' | h'
      · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
        have := hk.2.1
        rw [hswU] at this
        have := hgap k'' hk''
        linarith
      · linarith [hk.2.1, hlt k (Finset.mem_union_right _ h')]
    rw [typeProfit_of_not hno]
    linarith

/-- **Lemma 13.D.1** (MWG, pp. 462-463), for a general screening game. If contracts can be
sweetened uniformly (`sw δ` raises every type's utility by `δ`, keeps admissibility and the
tie-breaking key, and changes each profit continuously), both firms earn zero profits in every
SPNE. -/
theorem IsEq.zero (hI : G.Inj) (hl0 : 0 ≤ G.lam) (hl1 : G.lam ≤ 1)
    (sw : ℝ → ℝ × ℝ → ℝ × ℝ) (hswA : ∀ δ k, 0 < δ → G.adm k → G.adm (sw δ k))
    (hswU : ∀ δ b k, G.U b (sw δ k) = G.U b k + δ) (hswkey : ∀ δ k, G.key (sw δ k) = G.key k)
    (hswP : ∀ b k η, 0 < η → ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → G.P b k - η < G.P b (sw δ k))
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) :
    G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0 := by
  set T := G.profit A₁ A₂ + G.profit A₂ A₁ with hT
  have key : ∀ own other, G.IsEq own other → ∀ η, 0 < η →
      G.profit own other + G.profit other own - η ≤ G.profit own other := by
    intro own other he η hη
    obtain ⟨δf, hδf, hf⟩ := dev_type hI sw hswU hswkey hswP false own other hη
    obtain ⟨δt, hδt, ht⟩ := dev_type hI sw hswU hswkey hswP true own other hη
    set δ := min δf δt
    have hδ : 0 < δ := lt_min hδf hδt
    have hB : G.Menu ((own ∪ other).image (sw δ)) := by
      intro k hk
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hk
      rcases Finset.mem_union.1 hk' with h' | h'
      · exact hswA δ k' hδ (he.1 k' h')
      · exact hswA δ k' hδ (he.2.1 k' h')
    have hdev := he.2.2.1 _ hB
    have h1 := hf δ hδ (min_le_left _ _)
    have h2 := ht δ hδ (min_le_right _ _)
    rw [profit_add]
    unfold profit at hdev ⊢
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hl1), mul_le_mul_of_nonneg_left h2 hl0]
  have hle : ∀ own other, G.IsEq own other →
      G.profit own other + G.profit other own ≤ G.profit own other := by
    intro own other he
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have := key own other he (η / 2) (half_pos hη)
    linarith
  have h1 := hle A₁ A₂ h
  have h2 := hle A₂ A₁ h.symm
  have n1 := h.nonneg hI
  have n2 := h.symm.nonneg hI
  constructor <;> linarith

/-- A profitable single-contract deviation is impossible in an SPNE with zero profits: the
deviation `{k'}` attracts type `true` (who strictly prefers it to her chosen contract) at a
positive profit, while type `false` strictly prefers her chosen contract `kL`. -/
theorem IsEq.dev_true (hI : G.Inj) (hl : 0 < G.lam) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0) {kL kH k' : ℝ × ℝ}
    (hkL : G.Chooses false (A₁ ∪ A₂) kL) (hkH : G.Chooses true (A₁ ∪ A₂) kH) (hadm : G.adm k')
    (hH : G.U true kH < G.U true k') (hL : G.U false k' < G.U false kL)
    (hP : 0 < G.P true k') : False := by
  have key : ∀ own other, G.IsEq own other → G.profit own other = 0 →
      (∀ k ∈ other, G.U true k ≤ G.U true kH) → kL ∈ other → False := by
    intro own other he hz' hle hmem
    have hc := typeProfit_capture hI (b := true) (other := other) (Finset.mem_singleton_self k')
      (hkH.2.1.trans hH.le) (fun k hk => (hle k hk).trans_lt hH)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have h0 := no_capture_of_other hI (b := false) (k := k') hmem hL
    have := he.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
    rw [hz'] at this
    simp only [profit, hc, h0] at this
    nlinarith
  rcases Finset.mem_union.1 hkL.1 with hm | hm
  · exact key A₂ A₁ h.symm hz.2
      (fun k hk => hkH.2.2.1 k (Finset.mem_union_left _ hk)) hm
  · exact key A₁ A₂ h hz.1 (fun k hk => hkH.2.2.1 k (Finset.mem_union_right _ hk)) hm

/-- A variant of `IsEq.dev_true`: the deviation `{k'}` gives type `true` strictly more than every
offered contract and at least `ρ true`, makes a positive profit on her, and type `false` strictly
prefers her chosen contract `kL`. -/
theorem IsEq.dev_true' (hI : G.Inj) (hl : 0 < G.lam) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0) {kL k' : ℝ × ℝ}
    (hkL : G.Chooses false (A₁ ∪ A₂) kL) (hadm : G.adm k') (h0 : G.ρ true ≤ G.U true k')
    (hs : ∀ k ∈ A₁ ∪ A₂, G.U true k < G.U true k') (hL : G.U false k' < G.U false kL)
    (hP : 0 < G.P true k') : False := by
  have key : ∀ own other, G.IsEq own other → G.profit own other = 0 →
      other ⊆ A₁ ∪ A₂ → kL ∈ other → False := by
    intro own other he hz' hsub hmem
    have hc := typeProfit_capture hI (b := true) (other := other) (Finset.mem_singleton_self k')
      h0 (fun k hk => hs k (hsub hk)) (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have h0' := no_capture_of_other hI (b := false) (k := k') hmem hL
    have := he.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
    rw [hz'] at this
    simp only [profit, hc, h0'] at this
    nlinarith
  rcases Finset.mem_union.1 hkL.1 with hm | hm
  · exact key A₂ A₁ h.symm hz.2 Finset.subset_union_left hm
  · exact key A₁ A₂ h hz.1 Finset.subset_union_right hm

/-- A single contract `k'` that type `false` strictly prefers to everything firm 2 offers, at a
positive profit on her and a nonnegative profit on type `true`, is a profitable deviation for
firm 1 when its equilibrium profit is zero. -/
theorem IsEq.dev_false (hI : G.Inj) (hl1 : G.lam < 1) (hl0 : 0 ≤ G.lam)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ}
    (hadm : G.adm k') (h0 : G.ρ false ≤ G.U false k') (hs : ∀ k ∈ A₂, G.U false k < G.U false k')
    (hP : 0 < G.P false k') (hPt : 0 ≤ G.P true k') : False := by
  have hc := typeProfit_capture hI (b := false) (other := A₂) (Finset.mem_singleton_self k') h0
    hs (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have ht := typeProfit_nonneg_of hI (b := true) (other := A₂) (B := {k'})
    (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hPt)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  nlinarith [mul_nonneg hl0 ht]

/-- The analogue of `IsEq.dev_false` for type `true`. -/
theorem IsEq.dev_true_pos (hI : G.Inj) (hl0 : 0 < G.lam) (hl1 : G.lam ≤ 1)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ}
    (hadm : G.adm k') (h0 : G.ρ true ≤ G.U true k') (hs : ∀ k ∈ A₂, G.U true k < G.U true k')
    (hP : 0 < G.P true k') (hPf : 0 ≤ G.P false k') : False := by
  have hc := typeProfit_capture hI (b := true) (other := A₂) (Finset.mem_singleton_self k') h0
    hs (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have hf := typeProfit_nonneg_of hI (b := false) (other := A₂) (B := {k'})
    (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hPf)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  nlinarith [mul_nonneg (sub_nonneg.2 hl1) hf]

/-- A single contract that both types strictly prefer to everything firm 2 offers, with a
positive expected profit, is a profitable deviation for firm 1 when its profit is zero. -/
theorem IsEq.dev_both (hI : G.Inj) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ} (hadm : G.adm k') (h0 : ∀ b, G.ρ b ≤ G.U b k')
    (hs : ∀ b, ∀ k ∈ A₂, G.U b k < G.U b k')
    (hP : 0 < (1 - G.lam) * G.P false k' + G.lam * G.P true k') : False := by
  have hc : ∀ b, G.typeProfit b {k'} A₂ = G.P b k' := fun b =>
    typeProfit_capture hI (Finset.mem_singleton_self k') (h0 b) (hs b)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  linarith

end ScrGame

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.D.1: screening with productive tasks

MWG, Exercise 13.D.1, p. 476 (the model of Section 13.D, pp. 460-465).

A type `θ` worker produces `θ(1 + μt)` at task level `t`, `μ > 0`. Contracts `(w, t)`, utility
`w - c(t, θ)`, home earnings `0`, the book's tie-breaking rules; the game is the
`ScrGame` `prodGame M μ` (`P b (w, t) = θ_b(1 + μt) - w`). Write `S_θ(t) = θ(1 + μt) - c(t, θ)`
for the surplus (`surplus`).

* `exercise_13_D_1` (the analogue of Proposition 13.D.2): in every SPNE both types work, both
  firms earn zero, no contract earns or loses money (`w_θ = θ(1 + μt_θ)`), the low type's task
  maximizes `S_L` (her full-information contract), the low type does not strictly prefer the high
  type's contract, the high type's task maximizes `S_H` among the tasks whose zero-profit contract
  the low type strictly dislikes, and there is no pooling.
* Observable types (the analogue of Proposition 13.D.1): `exercise_13_D_1_observable`,
  `exercise_13_D_1_observable_exists`: type `θ` gets `(θ(1 + μt), t)` with `t` maximizing `S_θ`.
* Comparison: `exercise_13_D_1_compare`. The low type gets her full-information utility; the high
  type at most hers, exactly hers when her full-information contract does not attract the low
  type, and strictly less when every full-information contract of hers does.
* Existence: `prod_isEq` (an existence criterion). Instances: `quadModel` with `μ = 4`
  (`c(t, θ) = t²/θ`): the full-information contracts `(9, 2)`, `(66, 8)` are the unique SPNE
  outcome (`exercise_13_D_1_fullinfo`); `linModel` with `μ = 1/8`: the unique SPNE outcome is
  `(1, 0)`, `(7/3, 4/3)`, the high type's task is distorted upward from `0` and she is worse off
  than with observable types (`exercise_13_D_1_distorted`); with `λ = 9/10` instead no SPNE exists
  (`exercise_13_D_1_nonexistence`).

Departure: the results hold for `μ ≥ 0` (`μ = 0` is Proposition 13.D.2).
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- **Exercise 13.D.1** (MWG, p. 476). The screening game with productive tasks: type `θ`
produces `θ(1 + μt)`. -/
noncomputable def prodGame (M : SigModel) (μ : ℝ) : ScrGame where
  U b k := M.util (M.θ b) k
  P b k := M.θ b * (1 + μ * k.2) - k.1
  ρ _ := 0
  key k := k.2
  lam := M.lam
  adm k := 0 ≤ k.2

/-- The surplus `S_θ(t) = θ(1 + μt) - c(t, θ)` of type `θ` at task level `t`. -/
def surplus (M : SigModel) (μ : ℝ) (b : Bool) (t : ℝ) : ℝ := M.θ b * (1 + μ * t) - M.c t (M.θ b)

theorem prodGame_inj (M : SigModel) (μ : ℝ) : (M.prodGame μ).Inj := by
  intro b k k' hu hk
  simp only [prodGame, util] at hu hk
  exact Prod.ext (by rw [hk] at hu; linarith) hk

/-- Profit = surplus - utility. -/
theorem prodGame_P (M : SigModel) (μ : ℝ) (b : Bool) (k : ℝ × ℝ) :
    (M.prodGame μ).P b k = M.surplus μ b k.2 - (M.prodGame μ).U b k := by
  simp only [prodGame, surplus, util]; ring

/-- **Lemma 13.D.1** for productive tasks: zero profits in every SPNE. -/
theorem prodGame_zero (hM : M.Valid) {μ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) :
    (M.prodGame μ).profit A₁ A₂ = 0 ∧ (M.prodGame μ).profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (prodGame_inj M μ) hM.lam_pos.le hM.lam_lt.le
    (fun δ k => (k.1 + δ, k.2)) (fun _ _ _ hk => hk) (fun δ b k => ?_) (fun _ _ => rfl)
    (fun b k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => ?_⟩) h
  · simp only [prodGame, util]; ring
  · simp only [prodGame]; linarith

theorem θ_pos (hM : M.Valid) (b : Bool) : 0 < M.θ b := by
  cases b
  · exact hM.θL_pos
  · exact hM.θL_pos.trans hM.lt

/-- **Exercise 13.D.1** (MWG, p. 476). The SPNE of the screening game with productive tasks:
both types work; the low type takes `(θ_L(1 + μt_L), t_L)` with `t_L` maximizing her surplus
(her full-information contract); the high type takes `(θ_H(1 + μt_H), t_H)`, which the low type
does not strictly prefer, with `t_H` maximizing the high type's surplus among the tasks whose
zero-profit contract the low type strictly dislikes; no pooling; both firms earn zero. -/
theorem exercise_13_D_1 (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) :
    ∃ kL kH, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
      (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH ∧ 0 ≤ kL.2 ∧ 0 ≤ kH.2 ∧
      kL.1 = M.θL * (1 + μ * kL.2) ∧ kH.1 = M.θH * (1 + μ * kH.2) ∧
      (∀ t, 0 ≤ t → M.surplus μ false t ≤ M.surplus μ false kL.2) ∧
      M.util M.θL kH ≤ M.util M.θL kL ∧
      (∀ t, 0 ≤ t → M.θH * (1 + μ * t) - M.c t M.θL < M.util M.θL kL →
        M.surplus μ true t ≤ M.surplus μ true kH.2) ∧
      kL ≠ kH ∧ (M.prodGame μ).profit A₁ A₂ = 0 ∧ (M.prodGame μ).profit A₂ A₁ = 0 := by
  have hI := prodGame_inj M μ
  have hz := prodGame_zero hM h
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hUf : ∀ k, (M.prodGame μ).U false k = k.1 - M.c k.2 M.θL := fun _ => rfl
  have hUt : ∀ k, (M.prodGame μ).U true k = k.1 - M.c k.2 M.θH := fun _ => rfl
  have hPf : ∀ k, (M.prodGame μ).P false k = M.θL * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hPt : ∀ k, (M.prodGame μ).P true k = M.θH * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hSf : ∀ t, M.surplus μ false t = M.θL * (1 + μ * t) - M.c t M.θL := fun _ => rfl
  have hSt : ∀ t, M.surplus μ true t = M.θH * (1 + μ * t) - M.c t M.θH := fun _ => rfl
  have hρ : ∀ b, (M.prodGame μ).ρ b = 0 := fun _ => rfl
  -- a contract on the low type's zero-profit line, slightly cheaper, that the low type prefers
  have devL : ∀ t ε, 0 ≤ t → 0 < ε → 0 ≤ M.surplus μ false t - ε →
      (∀ k ∈ A₁ ∪ A₂, (M.prodGame μ).U false k < M.surplus μ false t - ε) → False := by
    intro t ε ht hε h0 hlt
    have hμt : 0 ≤ μ * t := mul_nonneg hμ ht
    refine ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (M.θL * (1 + μ * t) - ε, t)) ht
      ?_ (fun k hk => ?_) ?_ ?_
    · rw [hρ, hUf]; rw [hSf] at h0; linarith
    · have := hlt k (Finset.mem_union_right _ hk)
      simp only [hUf, hSf] at this ⊢; linarith
    · rw [hPf]; linarith
    · rw [hPt]; nlinarith
  -- the low type works
  obtain ⟨kL, hkL⟩ : ∃ kL, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL := by
    by_contra hno
    refine devL 0 (M.θL / 2) le_rfl (by linarith) ?_ fun k hk => ?_
    · rw [hSf, hM.c_zero]; linarith
    · rw [hSf, hM.c_zero]
      by_contra hle
      exact hno (ScrGame.exists_chooses false ⟨k, hk, by rw [hρ]; linarith⟩)
  have hLv := hval kL hkL.1
  -- the low type gets at least her maximal surplus
  have hLeff : ∀ t, 0 ≤ t → M.surplus μ false t ≤ (M.prodGame μ).U false kL := by
    intro t ht
    by_contra hlt
    rw [not_le] at hlt
    have h0 := hkL.2.1
    rw [hρ] at h0
    refine devL t ((M.surplus μ false t - (M.prodGame μ).U false kL) / 2) ht (by linarith)
      (by linarith)
      fun k hk => ?_
    have := hkL.2.2.1 k hk
    linarith
  -- the high type works
  obtain ⟨kH, hkH⟩ : ∃ kH, (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH := by
    refine ScrGame.exists_chooses true ⟨kL, hkL.1, ?_⟩
    have h0 := hkL.2.1
    rw [hρ, hUf] at h0
    rw [hρ, hUt]
    linarith [hM.c_le hLv]
  have hHv := hval kH hkH.1
  -- no profit on the high type
  have hPH : (M.prodGame μ).P true kH ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hHv hpos
    have hHL : M.util M.θL k' < M.util M.θL kL := hL.trans_le (hkL.2.2.1 kH hkH.1)
    have ht : kH.2 < k'.2 := by
      by_contra hle
      rw [not_lt] at hle
      simp only [util] at hH hL
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [he] at hH hL; linarith
      · have := hM.sc k'.2 kH.2 hk'0 hlt
        linarith
    refine ScrGame.IsEq.dev_true hI hl0 h hz hkL hkH hk'0 hH hHL ?_
    rw [hPt]; rw [hPt] at hpos hw
    have : M.θH * (1 + μ * kH.2) ≤ M.θH * (1 + μ * k'.2) := by
      have := mul_le_mul_of_nonneg_left ht.le hμ
      nlinarith
    linarith
  have hPL : (M.prodGame μ).P false kL ≤ 0 := by
    rw [prodGame_P]; linarith [hLeff kL.2 hLv]
  -- both contracts break even
  have htot := ScrGame.profit_add (G := (M.prodGame μ)) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hkL, ScrGame.typeProfit_add hI hkH] at htot
  have hlam : (M.prodGame μ).lam = M.lam := rfl
  rw [hlam] at htot
  have hPL0 : (M.prodGame μ).P false kL = 0 := by nlinarith
  have hPH0 : (M.prodGame μ).P true kH = 0 := by nlinarith
  rw [hPf] at hPL0
  rw [hPt] at hPH0
  have hwL : kL.1 = M.θL * (1 + μ * kL.2) := by linarith
  have hwH : kH.1 = M.θH * (1 + μ * kH.2) := by linarith
  refine ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, fun t ht => ?_, hkL.2.2.1 kH hkH.1,
    fun t ht hcon => ?_, fun he => ?_, hz.1, hz.2⟩
  · have := hLeff t ht
    rw [hUf, hwL] at this
    rw [hSf, hSf]; rw [hSf] at this; linarith
  · by_contra hlt
    rw [not_le] at hlt
    set ε := min ((M.surplus μ true t - M.surplus μ true kH.2) / 2)
      ((M.util M.θL kL - (M.θH * (1 + μ * t) - M.c t M.θL)) / 2)
    have hε1 : ε ≤ (M.surplus μ true t - M.surplus μ true kH.2) / 2 := min_le_left _ _
    have hε2 : ε ≤ (M.util M.θL kL - (M.θH * (1 + μ * t) - M.c t M.θL)) / 2 :=
      min_le_right _ _
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    refine ScrGame.IsEq.dev_true hI hl0 h hz hkL hkH (k' := (M.θH * (1 + μ * t) - ε, t)) ht
      ?_ ?_ ?_
    · rw [hUt, hUt, hwH]; rw [hSt, hSt] at hε1; simp only; linarith
    · rw [hUf, hUf]; simp only [util] at hε2 ⊢; linarith
    · rw [hPt]; simp only; linarith
  · have h2 : kL.2 = kH.2 := by rw [he]
    have hpos : 0 < 1 + μ * kL.2 := by nlinarith [mul_nonneg hμ hLv]
    rw [he, hwH, ← h2] at hwL
    nlinarith

/-- **Exercise 13.D.1** (MWG, p. 476), observable types (the analogue of Section 13.D's
Proposition 13.D.1): the game in which firms compete for type `θ_b` alone. -/
noncomputable def obsGame (M : SigModel) (μ : ℝ) (b : Bool) : ScrGame where
  U _ k := M.util (M.θ b) k
  P _ k := M.θ b * (1 + μ * k.2) - k.1
  ρ _ := 0
  key k := k.2
  lam := 1
  adm k := 0 ≤ k.2

theorem obsGame_inj (M : SigModel) (μ : ℝ) (b : Bool) : (M.obsGame μ b).Inj := by
  intro _ k k' hu hk
  simp only [obsGame, util] at hu hk
  exact Prod.ext (by rw [hk] at hu; linarith) hk

/-- **Exercise 13.D.1** (MWG, p. 476), observable types: in every SPNE of the game for type
`θ_b` she takes `(θ_b(1 + μt), t)` with `t` maximizing her surplus, and firms earn zero. -/
theorem exercise_13_D_1_observable (hM : M.Valid) {μ : ℝ} (b : Bool)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : (M.obsGame μ b).IsEq A₁ A₂) :
    ∃ k, (M.obsGame μ b).Chooses true (A₁ ∪ A₂) k ∧ 0 ≤ k.2 ∧ k.1 = M.θ b * (1 + μ * k.2) ∧
      (∀ t, 0 ≤ t → M.surplus μ b t ≤ M.surplus μ b k.2) ∧
      (M.obsGame μ b).profit A₁ A₂ = 0 ∧ (M.obsGame μ b).profit A₂ A₁ = 0 := by
  have hI := obsGame_inj M μ b
  have hθ := θ_pos hM b
  have hz : (M.obsGame μ b).profit A₁ A₂ = 0 ∧ (M.obsGame μ b).profit A₂ A₁ = 0 :=
    ScrGame.IsEq.zero hI zero_le_one le_rfl (fun δ k => (k.1 + δ, k.2)) (fun _ _ _ hk => hk)
      (fun δ _ k => by simp only [obsGame, util]; ring) (fun _ _ => rfl)
      (fun _ k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => by simp only [obsGame]; linarith⟩) h
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hU : ∀ k, (M.obsGame μ b).U true k = k.1 - M.c k.2 (M.θ b) := fun _ => rfl
  have hP : ∀ k, (M.obsGame μ b).P true k = M.θ b * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hS : ∀ t, M.surplus μ b t = M.θ b * (1 + μ * t) - M.c t (M.θ b) := fun _ => rfl
  have hprof : ∀ B other, (M.obsGame μ b).profit B other =
      (M.obsGame μ b).typeProfit true B other := fun B other => by
    simp [ScrGame.profit, obsGame]
  have dev : ∀ t ε, 0 ≤ t → 0 < ε → 0 ≤ M.surplus μ b t - ε →
      (∀ k ∈ A₁ ∪ A₂, (M.obsGame μ b).U true k < M.surplus μ b t - ε) → False := by
    intro t ε ht hε h0 hlt
    have hc := ScrGame.typeProfit_capture hI (b := true) (other := A₂)
      (Finset.mem_singleton_self (M.θ b * (1 + μ * t) - ε, t))
      (by change (0 : ℝ) ≤ _; rw [hU]; rw [hS] at h0; linarith)
      (fun k hk => by
        have := hlt k (Finset.mem_union_right _ hk)
        simp only [hU, hS] at this ⊢; linarith)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have := h.2.2.1 {(M.θ b * (1 + μ * t) - ε, t)}
      (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact ht)
    rw [hz.1, hprof, hc, hP] at this
    simp only at this
    linarith
  obtain ⟨k, hk⟩ : ∃ k, (M.obsGame μ b).Chooses true (A₁ ∪ A₂) k := by
    by_contra hno
    refine dev 0 (M.θ b / 2) le_rfl (by linarith) ?_ fun k hk => ?_
    · rw [hS, hM.c_zero]; linarith
    · rw [hS, hM.c_zero]
      by_contra hle
      exact hno (ScrGame.exists_chooses true ⟨k, hk, by change (0 : ℝ) ≤ _; linarith⟩)
  have hkv := hval k hk.1
  have heff : ∀ t, 0 ≤ t → M.surplus μ b t ≤ (M.obsGame μ b).U true k := by
    intro t ht
    by_contra hlt
    rw [not_le] at hlt
    have h0 : (0 : ℝ) ≤ (M.obsGame μ b).U true k := hk.2.1
    refine dev t ((M.surplus μ b t - (M.obsGame μ b).U true k) / 2) ht (by linarith) (by linarith)
      fun k' hk' => ?_
    have := hk.2.2.1 k' hk'
    linarith
  have htot := ScrGame.profit_add (G := (M.obsGame μ b)) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hk] at htot
  have hl : (M.obsGame μ b).lam = 1 := rfl
  rw [hl] at htot
  have hP0 : (M.obsGame μ b).P true k ≤ 0 := by
    have := heff k.2 hkv
    rw [hP]; rw [hU, hS] at this; linarith
  have hw : k.1 = M.θ b * (1 + μ * k.2) := by
    have hfalse : ∀ A B, (M.obsGame μ b).typeProfit false A B =
        (M.obsGame μ b).typeProfit true A B := fun _ _ => rfl
    rw [hfalse, hfalse, ScrGame.typeProfit_add hI hk] at htot
    rw [hP] at htot hP0
    linarith
  refine ⟨k, hk, hkv, hw, fun t ht => ?_, hz.1, hz.2⟩
  have := heff t ht
  rw [hU, hw] at this
  simp only [hS] at this ⊢; linarith

/-- **Exercise 13.D.1** (MWG, p. 476), observable types, existence: if `t*` maximizes type
`θ_b`'s surplus, both firms offering `(θ_b(1 + μt*), t*)` is an SPNE. -/
theorem exercise_13_D_1_observable_exists (hM : M.Valid) {μ : ℝ} (b : Bool)
    {ts : ℝ} (hts : 0 ≤ ts) (hmax : ∀ t, 0 ≤ t → M.surplus μ b t ≤ M.surplus μ b ts) :
    (M.obsGame μ b).IsEq {(M.θ b * (1 + μ * ts), ts)} {(M.θ b * (1 + μ * ts), ts)} := by
  have hI := obsGame_inj M μ b
  set ks : ℝ × ℝ := (M.θ b * (1 + μ * ts), ts)
  have hv : (M.obsGame μ b).Menu {ks} := fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hts
  have hprof : ∀ B other, (M.obsGame μ b).profit B other =
      (M.obsGame μ b).typeProfit true B other := fun B other => by
    simp [ScrGame.profit, obsGame]
  have hS0 : 0 ≤ M.surplus μ b ts := by
    have := hmax 0 le_rfl
    simp only [surplus, hM.c_zero] at this ⊢
    linarith [θ_pos hM b]
  have hUs : (M.obsGame μ b).U true ks = M.surplus μ b ts := by simp [obsGame, util, surplus, ks]
  have hzero : (M.obsGame μ b).profit {ks} {ks} = 0 := by
    have hch : (M.obsGame μ b).Chooses true ({ks} ∪ {ks}) ks := by
      rw [Finset.union_self]
      exact ScrGame.chooses_of_strict (Finset.mem_singleton_self _)
        (by change (0 : ℝ) ≤ _; rw [hUs]; exact hS0)
        (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    rw [hprof, ScrGame.typeProfit_of_chooses hI hch]
    simp [obsGame, ks]
  have hdev : ∀ B, (M.obsGame μ b).Menu B →
      (M.obsGame μ b).profit B {ks} ≤ (M.obsGame μ b).profit {ks} {ks} := by
    intro B hB
    rw [hzero, hprof]
    by_cases hex : ∃ k, (M.obsGame μ b).Chooses true (B ∪ {ks}) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk]
      have hge := hk.2.2.1 ks (by simp)
      have hk2 : 0 ≤ k.2 := by
        rcases Finset.mem_union.1 hk.1 with h' | h'
        · exact hB k h'
        · rw [Finset.mem_singleton.1 h']; exact hts
      have := hmax k.2 hk2
      have hPk : (M.obsGame μ b).P true k ≤ 0 := by
        rw [hUs] at hge
        simp only [obsGame, util, surplus] at hge this ⊢
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) hPk
    · rw [ScrGame.typeProfit_of_not hex]
  exact ⟨hv, hv, hdev, hdev⟩

/-- **Exercise 13.D.1** (MWG, p. 476), comparison with observable types. In every SPNE the low
type gets her full-information utility `max S_L = S_L(t_L)`; if `t*` maximizes the high type's
surplus, the high type gets at most `S_H(t*)`, exactly `S_H(t*)` when the low type strictly
dislikes the contract `(θ_H(1 + μt*), t*)`, and strictly less when the low type weakly prefers
every such full-information contract of the high type to her own. -/
theorem exercise_13_D_1_compare (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) {ts : ℝ} (hts : 0 ≤ ts)
    (hmax : ∀ t, 0 ≤ t → M.surplus μ true t ≤ M.surplus μ true ts) :
    ∃ kL kH, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
      (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH ∧
      M.util M.θL kL = M.surplus μ false kL.2 ∧
      (∀ t, 0 ≤ t → M.surplus μ false t ≤ M.util M.θL kL) ∧
      M.util M.θH kH ≤ M.surplus μ true ts ∧
      (M.θH * (1 + μ * ts) - M.c ts M.θL < M.util M.θL kL →
        M.util M.θH kH = M.surplus μ true ts) ∧
      ((∀ t, 0 ≤ t → M.surplus μ true t = M.surplus μ true ts →
        M.util M.θL kL < M.θH * (1 + μ * t) - M.c t M.θL) →
        M.util M.θH kH < M.surplus μ true ts) := by
  obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, hLH, hHopt, -, -, -⟩ :=
    exercise_13_D_1 hM hμ h
  have hUL : M.util M.θL kL = M.surplus μ false kL.2 := by
    simp only [util, surplus, θ_false, hwL]
  have hUH : M.util M.θH kH = M.surplus μ true kH.2 := by
    simp only [util, surplus, θ_true, hwH]
  refine ⟨kL, kH, hkL, hkH, hUL, fun t ht => hUL ▸ hLeff t ht, hUH ▸ hmax _ hHv,
    fun hlt => ?_, fun hall => ?_⟩
  · exact le_antisymm (hUH ▸ hmax _ hHv) (hUH ▸ hHopt ts hts hlt)
  · rcases lt_or_eq_of_le (hUH ▸ hmax _ hHv : M.util M.θH kH ≤ M.surplus μ true ts) with hl | he
    · exact hl
    · exfalso
      have := hall kH.2 hHv (hUH ▸ he)
      simp only [util] at hLH this
      rw [hwH] at hLH
      linarith

/-- **Exercise 13.D.1** (MWG, p. 476), an existence criterion. Let `t_L` maximize the low type's
surplus, and let the contracts `k_L = (θ_L(1 + μt_L), t_L)` and `k_H = (θ_H(1 + μt_H), t_H)`
self-select (the low type weakly prefers `k_L`, with the tie-breaking rule; the high type
strictly prefers `k_H`). If `t_H` is constrained optimal for the high type (every contract she
weakly prefers to `k_H` that the low type does not strictly prefer to `k_L` makes no profit on
her) and no contract that the high type weakly prefers and the low type strictly prefers is
profitable even when it attracts both types, then both firms offering `{k_L, k_H}` is an SPNE. -/
theorem prod_isEq (hM : M.Valid) {μ : ℝ} {tL tH : ℝ} (htL : 0 ≤ tL) (htH : 0 ≤ tH)
    (hLmax : ∀ t, 0 ≤ t → M.surplus μ false t ≤ M.surplus μ false tL)
    (hLH : M.θH * (1 + μ * tH) - M.c tH M.θL ≤ M.surplus μ false tL)
    (hLtie : M.θH * (1 + μ * tH) - M.c tH M.θL = M.surplus μ false tL → tL ≤ tH)
    (hHL : M.θL * (1 + μ * tL) - M.c tL M.θH < M.surplus μ true tH)
    (hcon : ∀ w t, 0 ≤ t → M.surplus μ true tH ≤ w - M.c t M.θH →
      w - M.c t M.θL ≤ M.surplus μ false tL → M.θH * (1 + μ * t) ≤ w)
    (hN : ∀ w t, 0 ≤ t → M.surplus μ true tH ≤ w - M.c t M.θH →
      M.surplus μ false tL < w - M.c t M.θL →
      (1 - M.lam) * (M.surplus μ false tL - (w - M.c t M.θL)) +
        M.lam * (M.θH * (1 + μ * t) - w) ≤ 0) :
    (M.prodGame μ).IsEq {(M.θL * (1 + μ * tL), tL), (M.θH * (1 + μ * tH), tH)}
      {(M.θL * (1 + μ * tL), tL), (M.θH * (1 + μ * tH), tH)} := by
  have hI := prodGame_inj M μ
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  set kL : ℝ × ℝ := (M.θL * (1 + μ * tL), tL) with hkLdef
  set kH : ℝ × ℝ := (M.θH * (1 + μ * tH), tH) with hkHdef
  set A : Finset (ℝ × ℝ) := {kL, kH} with hA
  have hUf : ∀ k, (M.prodGame μ).U false k = k.1 - M.c k.2 M.θL := fun _ => rfl
  have hUt : ∀ k, (M.prodGame μ).U true k = k.1 - M.c k.2 M.θH := fun _ => rfl
  have hPf : ∀ k, (M.prodGame μ).P false k = M.θL * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hPt : ∀ k, (M.prodGame μ).P true k = M.θH * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hSf : ∀ t, M.surplus μ false t = M.θL * (1 + μ * t) - M.c t M.θL := fun _ => rfl
  have hSt : ∀ t, M.surplus μ true t = M.θH * (1 + μ * t) - M.c t M.θH := fun _ => rfl
  have hρ : ∀ b, (M.prodGame μ).ρ b = 0 := fun _ => rfl
  have hSL0 : M.θL ≤ M.surplus μ false tL := by
    have := hLmax 0 le_rfl; rw [hSf, hM.c_zero] at this; linarith
  have hAv : (M.prodGame μ).Menu A := by
    intro k hk
    simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact htL
    · exact htH
  have hmemL : kL ∈ A := by simp [hA]
  have hmemH : kH ∈ A := by simp [hA]
  have hULL : (M.prodGame μ).U false kL = M.surplus μ false tL := by rw [hUf, hSf]
  have hUHH : (M.prodGame μ).U true kH = M.surplus μ true tH := by rw [hUt, hSt]
  have hULH : (M.prodGame μ).U false kH = M.θH * (1 + μ * tH) - M.c tH M.θL := by rw [hUf]
  have hUHL : (M.prodGame μ).U true kL = M.θL * (1 + μ * tL) - M.c tL M.θH := by rw [hUt]
  have hchL : (M.prodGame μ).Chooses false (A ∪ A) kL := by
    rw [Finset.union_self]
    refine ⟨hmemL, by rw [hρ, hULL]; linarith, fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact le_rfl
      · rw [hULH, hULL]; exact hLH
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact le_rfl
      · rw [hULH, hULL] at hu; exact hLtie hu
  have hchH : (M.prodGame μ).Chooses true (A ∪ A) kH := by
    rw [Finset.union_self]
    have hcL := hM.c_le htL
    refine ScrGame.chooses_of_strict hmemH ?_ fun k hk hne => ?_
    · rw [hρ, hUHH]; rw [hSf] at hSL0; linarith
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rw [hUHL, hUHH]; exact hHL
      · exact absurd rfl hne
  have hzero : (M.prodGame μ).profit A A = 0 := by
    unfold ScrGame.profit
    rw [ScrGame.typeProfit_of_chooses hI hchL, ScrGame.typeProfit_of_chooses hI hchH, hPf, hPt]
    simp [hkLdef, hkHdef]
  have hval : ∀ B, (M.prodGame μ).Menu B → ∀ k ∈ B ∪ A, 0 ≤ k.2 := fun B hB k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact hB k hk
    · exact hAv k hk
  have hdev : ∀ B, (M.prodGame μ).Menu B → (M.prodGame μ).profit B A ≤ 0 := by
    intro B hB
    -- the profit from the low type is never positive
    have hLle : ∀ k', (M.prodGame μ).Chooses false (B ∪ A) k' →
        (M.prodGame μ).P false k' ≤ M.surplus μ false tL - (M.prodGame μ).U false k' := by
      intro k' hk'
      have := hLmax k'.2 (hval B hB k' hk'.1)
      simp only [hPf, hUf, hSf] at this ⊢; linarith
    have hLnp : (M.prodGame μ).typeProfit false B A ≤ 0 := by
      by_cases hex : ∃ k', (M.prodGame μ).Chooses false (B ∪ A) k'
      · obtain ⟨k', hk'⟩ := hex
        rw [ScrGame.typeProfit_of_chooses hI hk']
        have h1 := hLle k' hk'
        have h2 := hk'.2.2.1 kL (Finset.mem_union_right _ hmemL)
        rw [hULL] at h2
        exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) (by linarith)
      · rw [ScrGame.typeProfit_of_not hex]
    unfold ScrGame.profit
    have hlam : (M.prodGame μ).lam = M.lam := rfl
    rw [hlam]
    by_cases hexH : ∃ k, (M.prodGame μ).Chooses true (B ∪ A) k
    · obtain ⟨k, hk⟩ := hexH
      rw [ScrGame.typeProfit_of_chooses hI hk]
      rcases le_or_gt ((M.prodGame μ).P true k) 0 with hP | hP
      · have := mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg B A k) hP
        nlinarith
      · have hkv := hval B hB k hk.1
        have hgeH := hk.2.2.1 kH (Finset.mem_union_right _ hmemH)
        rw [hUHH] at hgeH
        have hkA : k ∉ A := by
          intro hm
          simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · rw [hUHL] at hgeH; linarith
          · rw [hPt] at hP; simp [hkHdef] at hP
        have hkB : k ∈ B := by
          rcases Finset.mem_union.1 hk.1 with hm | hm
          · exact hm
          · exact absurd hm hkA
        have hsh : SigModel.share B A k = 1 := by simp [SigModel.share, hkB, hkA]
        rw [hUt] at hgeH
        have hLk : M.surplus μ false tL < k.1 - M.c k.2 M.θL := by
          by_contra hle
          rw [not_lt] at hle
          have := hcon k.1 k.2 hkv hgeH hle
          rw [hPt] at hP; linarith
        obtain ⟨k', hk'⟩ := ScrGame.exists_chooses (G := M.prodGame μ) false
          ⟨k, hk.1, by rw [hρ, hUf]; linarith⟩
        have hk'k := hk'.2.2.1 k hk.1
        have hk'A : k' ∉ A := by
          intro hm
          simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · rw [hULL, hUf] at hk'k; linarith
          · rw [hULH, hUf] at hk'k; linarith
        have hk'B : k' ∈ B := by
          rcases Finset.mem_union.1 hk'.1 with hm | hm
          · exact hm
          · exact absurd hm hk'A
        have hpL : (M.prodGame μ).typeProfit false B A = (M.prodGame μ).P false k' := by
          rw [ScrGame.typeProfit_of_chooses hI hk']
          simp [SigModel.share, hk'B, hk'A]
        have h1 := hLle k' hk'
        rw [hpL, hsh, one_mul]
        have hn := hN k.1 k.2 hkv hgeH hLk
        rw [hUf] at hk'k
        rw [hPt] at hP ⊢
        nlinarith
    · rw [ScrGame.typeProfit_of_not hexH]
      nlinarith
  refine ⟨hAv, hAv, fun B hB => ?_, fun B hB => ?_⟩ <;> rw [hzero] <;> exact hdev B hB

/-- **Exercise 13.D.1**, a model for the instances: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`,
`c(t, θ) = t²/θ`. -/
noncomputable def quadModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun t θ => t ^ 2 / θ

theorem quadModel_cL (t : ℝ) : quadModel.c t quadModel.θL = t ^ 2 := by
  simp [quadModel]

theorem quadModel_cH (t : ℝ) : quadModel.c t quadModel.θH = t ^ 2 / 2 := by
  simp [quadModel]

theorem quadModel_valid : quadModel.Valid where
  θL_pos := by norm_num [quadModel]
  lt := by norm_num [quadModel]
  lam_pos := by norm_num [quadModel]
  lam_lt := by norm_num [quadModel]
  r_nonneg := by norm_num [quadModel]
  r_lt := by norm_num [quadModel]
  c_zero := fun θ => by simp [quadModel]
  c_mono := fun b => by
    cases b
    · intro a ha b _ hab
      simp only [θ_false, quadModel_cL]
      have : (0 : ℝ) ≤ a := ha
      nlinarith
    · intro a ha b _ hab
      simp only [θ_true, quadModel_cH]
      have : (0 : ℝ) ≤ a := ha
      nlinarith
  c_cont := fun b => by
    cases b
    · simp only [θ_false, quadModel_cL]; exact (continuous_pow 2).continuousOn
    · simp only [θ_true, quadModel_cH]; exact ((continuous_pow 2).div_const 2).continuousOn
  sc := fun e e' he hlt => by
    rw [quadModel_cH, quadModel_cH, quadModel_cL, quadModel_cL]
    nlinarith

/-- **Exercise 13.D.1** (MWG, p. 476), an instance where screening costs nothing: in
`quadModel` with `μ = 4` both firms offering the full-information contracts `{(9, 2), (66, 8)}`
is an SPNE, and in every SPNE the low type takes `(9, 2)` and the high type `(66, 8)`; these
maximize the types' surpluses (`5` and `34`), i.e. they are the observable-types outcome. -/
theorem exercise_13_D_1_fullinfo :
    (quadModel.prodGame 4).IsEq {(9, 2), (66, 8)} {(9, 2), (66, 8)} ∧
      (∀ A₁ A₂, (quadModel.prodGame 4).IsEq A₁ A₂ →
        (quadModel.prodGame 4).Chooses false (A₁ ∪ A₂) (9, 2) ∧
          (quadModel.prodGame 4).Chooses true (A₁ ∪ A₂) (66, 8)) ∧
      (∀ t, 0 ≤ t → quadModel.surplus 4 false t ≤ quadModel.surplus 4 false 2) ∧
      (∀ t, 0 ≤ t → quadModel.surplus 4 true t ≤ quadModel.surplus 4 true 8) := by
  have hv := quadModel_valid
  have hSf : ∀ t, quadModel.surplus 4 false t = 1 + 4 * t - t ^ 2 := fun t => by
    simp only [surplus, θ_false, quadModel_cL]; simp only [quadModel]; ring
  have hSt : ∀ t, quadModel.surplus 4 true t = 2 + 8 * t - t ^ 2 / 2 := fun t => by
    simp only [surplus, θ_true, quadModel_cH]; simp only [quadModel]; ring
  have hLmax : ∀ t, 0 ≤ t → quadModel.surplus 4 false t ≤ quadModel.surplus 4 false 2 :=
    fun t _ => by rw [hSf, hSf]; nlinarith [sq_nonneg (t - 2)]
  have hHmax : ∀ t, 0 ≤ t → quadModel.surplus 4 true t ≤ quadModel.surplus 4 true 8 :=
    fun t _ => by rw [hSt, hSt]; nlinarith [sq_nonneg (t - 8)]
  have hcL := quadModel_cL
  have hcH := quadModel_cH
  have hθL : quadModel.θL = 1 := rfl
  have hθH : quadModel.θH = 2 := rfl
  have hlam : quadModel.lam = 1 / 2 := rfl
  refine ⟨?_, fun A₁ A₂ h => ?_, hLmax, hHmax⟩
  · have := prod_isEq hv (μ := 4) (tL := 2) (tH := 8) (by norm_num) (by norm_num)
      hLmax ?_ ?_ ?_ ?_ ?_
    · convert this using 2 <;> simp [hθL, hθH] <;> norm_num
    all_goals simp only [hSf, hSt, hcL, hcH]
    all_goals simp only [hθL, hθH, hlam]
    · norm_num
    · norm_num
    · norm_num
    · intro w t _ h1 _; nlinarith [sq_nonneg (t - 8)]
    · intro w t _ h1 h2; nlinarith [sq_nonneg (t - 8)]
  · obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, -, hHopt, -⟩ :=
      exercise_13_D_1 hv (μ := 4) (by norm_num) h
    have hx : kL.2 = 2 := by
      have := hLeff 2 (by norm_num)
      rw [hSf, hSf] at this
      nlinarith [sq_nonneg (kL.2 - 2)]
    have hkL' : kL = (9, 2) := by
      refine Prod.ext ?_ hx
      rw [hwL, hx, hθL]; norm_num
    have hULk : quadModel.util quadModel.θL kL = 5 := by
      rw [hkL']; simp only [util, hcL]; norm_num
    have hy : kH.2 = 8 := by
      have := hHopt 8 (by norm_num) (by rw [hULk, hcL, hθH]; norm_num)
      rw [hSt, hSt] at this
      nlinarith [sq_nonneg (kH.2 - 8)]
    have hkH' : kH = (66, 8) := by
      refine Prod.ext ?_ hy
      rw [hwH, hy, hθH]; norm_num
    exact ⟨hkL' ▸ hkL, hkH' ▸ hkH⟩

/-- **Exercise 13.D.1** (MWG, p. 476), an instance with distortion: in `linModel`
(`c(t, θ_L) = t`, `c(t, θ_H) = t/2`, `λ = 1/2`) with `μ = 1/8`, both firms offering
`{(1, 0), (7/3, 4/3)}` is an SPNE, and in every SPNE the low type takes `(1, 0)` and the high
type `(7/3, 4/3)`. With observable types the high type would choose `t = 0` and get `2`; here
she gets `5/3`. -/
theorem exercise_13_D_1_distorted :
    (linModel.prodGame (1 / 8)).IsEq {(1, 0), (7 / 3, 4 / 3)} {(1, 0), (7 / 3, 4 / 3)} ∧
      (∀ A₁ A₂, (linModel.prodGame (1 / 8)).IsEq A₁ A₂ →
        (linModel.prodGame (1 / 8)).Chooses false (A₁ ∪ A₂) (1, 0) ∧
          (linModel.prodGame (1 / 8)).Chooses true (A₁ ∪ A₂) (7 / 3, 4 / 3)) ∧
      (∀ t, 0 ≤ t → linModel.surplus (1 / 8) true t ≤ linModel.surplus (1 / 8) true 0) ∧
      linModel.util linModel.θH (7 / 3, 4 / 3) = 5 / 3 ∧
      linModel.surplus (1 / 8) true 0 = 2 := by
  have hv := linModel_valid
  have hcL := linModel_cL
  have hcH := linModel_cH
  have hθL : linModel.θL = 1 := rfl
  have hθH : linModel.θH = 2 := rfl
  have hlam : linModel.lam = 1 / 2 := rfl
  have hSf : ∀ t, linModel.surplus (1 / 8) false t = 1 - 7 * t / 8 := fun t => by
    simp only [surplus, θ_false, hcL]; rw [hθL]; ring
  have hSt : ∀ t, linModel.surplus (1 / 8) true t = 2 - t / 4 := fun t => by
    simp only [surplus, θ_true, hcH]; rw [hθH]; ring
  refine ⟨?_, fun A₁ A₂ h => ?_, fun t ht => by rw [hSt, hSt]; linarith, ?_, ?_⟩
  · have := prod_isEq hv (μ := 1 / 8) (tL := 0) (tH := 4 / 3) le_rfl
      (by norm_num) (fun t ht => by rw [hSf, hSf]; linarith) ?_ ?_ ?_ ?_ ?_
    · convert this using 2 <;> simp [hθL, hθH] <;> norm_num
    all_goals simp only [hSf, hSt, hcL, hcH]
    all_goals simp only [hθL, hθH, hlam]
    · norm_num
    · norm_num
    · norm_num
    · intro w t _ h1 h2; linarith
    · intro w t ht h1 h2
      rcases le_or_gt t (4 / 3) with h3 | h3 <;> linarith
  · obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, hLH, hHopt, -⟩ :=
      exercise_13_D_1 hv (μ := 1 / 8) (by norm_num) h
    have hx : kL.2 = 0 := by
      have := hLeff 0 le_rfl
      rw [hSf, hSf] at this
      linarith
    have hkL' : kL = (1, 0) := by
      refine Prod.ext ?_ hx
      rw [hwL, hx, hθL]; norm_num
    have hULk : linModel.util linModel.θL kL = 1 := by
      rw [hkL']; simp only [util, hcL]; norm_num
    have hy1 : 4 / 3 ≤ kH.2 := by
      rw [hULk] at hLH
      simp only [util, hcL] at hLH
      rw [hwH, hθH] at hLH
      linarith
    have hy2 : kH.2 ≤ 4 / 3 := by
      by_contra hlt
      rw [not_le] at hlt
      have := hHopt ((kH.2 + 4 / 3) / 2) (by linarith)
        (by rw [hULk, hcL, hθH]; linarith)
      rw [hSt, hSt] at this
      linarith
    have hkH' : kH = (7 / 3, 4 / 3) := by
      have hy : kH.2 = 4 / 3 := le_antisymm hy2 hy1
      refine Prod.ext ?_ hy
      rw [hwH, hy, hθH]; norm_num
    exact ⟨hkL' ▸ hkL, hkH' ▸ hkH⟩
  · simp only [util, hcH]; norm_num
  · rw [hSt]; norm_num

/-- The linear model of `linModel` with `λ = 9/10`. -/
noncomputable def linModel9 : SigModel := { linModel with lam := 9 / 10 }

theorem linModel9_valid : linModel9.Valid where
  θL_pos := linModel_valid.θL_pos
  lt := linModel_valid.lt
  lam_pos := by norm_num [linModel9]
  lam_lt := by norm_num [linModel9]
  r_nonneg := linModel_valid.r_nonneg
  r_lt := linModel_valid.r_lt
  c_zero := linModel_valid.c_zero
  c_mono := linModel_valid.c_mono
  c_cont := linModel_valid.c_cont
  sc := linModel_valid.sc

/-- **Exercise 13.D.1** (MWG, p. 476), nonexistence: with `λ = 9/10` (and `μ = 1/8`) the pooling
contract `(9/5, 0)` breaks every candidate equilibrium: no SPNE exists. -/
theorem exercise_13_D_1_nonexistence :
    ¬ ∃ A₁ A₂, (linModel9.prodGame (1 / 8)).IsEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  have hv := linModel9_valid
  have hcL : ∀ t, linModel9.c t linModel9.θL = t := linModel_cL
  have hcH : ∀ t, linModel9.c t linModel9.θH = t / 2 := linModel_cH
  have hθL : linModel9.θL = 1 := rfl
  have hθH : linModel9.θH = 2 := rfl
  have hlam : linModel9.lam = 9 / 10 := rfl
  obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, -, hLH, -, -, hz, -⟩ :=
    exercise_13_D_1 hv (μ := 1 / 8) (by norm_num) h
  have hUL : linModel9.util linModel9.θL kL ≤ 1 := by
    simp only [util, hcL]; rw [hwL, hθL]; linarith
  have hUH : linModel9.util linModel9.θH kH ≤ 5 / 3 := by
    have h1 := hLH.trans hUL
    simp only [util, hcL, hcH] at h1 ⊢
    rw [hwH, hθH] at h1 ⊢
    linarith
  refine ScrGame.IsEq.dev_both (prodGame_inj _ _) h hz (k' := (9 / 5, 0)) le_rfl
    (fun b => ?_) (fun b k hk => ?_) ?_
  · change (0 : ℝ) ≤ _
    cases b <;> simp [prodGame, util, hv.c_zero] <;> norm_num
  · cases b
    · have := hkL.2.2.1 k (Finset.mem_union_right _ hk)
      change k.1 - linModel9.c k.2 linModel9.θL ≤ kL.1 - linModel9.c kL.2 linModel9.θL at this
      change k.1 - linModel9.c k.2 linModel9.θL < (9 / 5 : ℝ) - linModel9.c 0 linModel9.θL
      rw [hv.c_zero]
      simp only [util] at hUL; linarith
    · have := hkH.2.2.1 k (Finset.mem_union_right _ hk)
      change k.1 - linModel9.c k.2 linModel9.θH ≤ kH.1 - linModel9.c kH.2 linModel9.θH at this
      change k.1 - linModel9.c k.2 linModel9.θH < (9 / 5 : ℝ) - linModel9.c 0 linModel9.θH
      rw [hv.c_zero]
      simp only [util] at hUH; linarith
  · simp only [prodGame, θ_false, θ_true, hθL, hθH, hlam]; norm_num

/-- **Exercise 13.D.1** (MWG, p. 476), observable types, an instance: in `quadModel` with
`μ = 4` the low type's full-information contract `(9, 2)` is an SPNE of her game. -/
theorem exercise_13_D_1_observable_instance :
    (quadModel.obsGame 4 false).IsEq {(9, 2)} {(9, 2)} := by
  have h := exercise_13_D_1_observable_exists quadModel_valid (μ := 4) false (ts := 2)
    (by norm_num) fun t _ => by
      simp only [surplus, θ_false, quadModel_cL]; simp only [quadModel]
      nlinarith [sq_nonneg (t - 2)]
  have e : (quadModel.θ false * (1 + 4 * 2), (2 : ℝ)) = (9, 2) := by
    simp only [θ_false, quadModel]; norm_num
  rwa [e] at h

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.D.2: screening in insurance markets (Rothschild-Stiglitz)

MWG, Exercise 13.D.2, p. 476.

**The general model (`RSModel`).** Two states (`1`: no loss / good output, `2`: loss / bad
output) and two types: the "safe" type `true` (probability `q_S` of state `1`, prior probability
`λ`) and the "risky" type `false` (`q_R < q_S`). The endowment (or output) is `(a₁, a₂)`,
`a₂ < a₁`. An expected-utility maximizer with strictly increasing, strictly concave Bernoulli
utility `u` is described by `h = u⁻¹`: a contract is given by the utility levels `(v₁, v₂)` it
yields in the two states, i.e. by the wealth levels `(h v₁, h v₂)`. Type `b` gets
`V_b = q_b v₁ + (1 - q_b) v₂` and her firm the expected profit
`Pr_b = q_b (a₁ - h v₁) + (1 - q_b)(a₂ - h v₂)`; she accepts a contract iff `V_b ≥ ρ_b`. The game
is the `ScrGame` `M.game` with tie-breaking key `v₁ - v₂` (an indifferent individual takes the
contract with more coverage).

* `rs_characterization`: in every SPNE the risky type is fully insured at her fair price
  (`(v*, v*)`, `h v* = q_R a₁ + (1 - q_R) a₂`); the safe type takes a contract `k_S` that is
  fair for her (`Pr_S = 0`), partial (`k_S.2 < k_S.1`) and on the risky type's indifference
  curve (`V_R(k_S) = v*`); both firms earn zero.
* `rs_point_unique`: there is at most one such `k_S`.
* `rs_isEq` (existence criterion), `rs_no_eq` (nonexistence via a pooling contract).
* `log_isEq`, `log_no_eq`: with `u = log` (`h = exp`, shifted by a constant `κ`),
  `q_S = 2/3`, `q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ`: the SPNE exists for `λ ≤ 9/19` and does
  not exist for `λ = 9/10`.

**The exercise.** Wealth `W`, loss `L`, loss probabilities `p_L < p_H`; a policy `(M, R)`
(premium, payment in case of loss).
* (a) `exercise_13_D_2a`: `(M, R) ↦ (W - M, W - L - M + R)` is a bijection from policies to
  wealth levels in the two states, under which expected utility and expected profit become
  functions of the wealth levels; `exercise_13_D_2a_log`: with `u = log`, positive wealth levels
  correspond bijectively to utility levels.
* (b) `insModel`; `exercise_13_D_2b`: the SPNE outcome (high risk: full insurance at her fair
  premium `p_H L`; low risk: partial insurance, fair for her, on the high-risk type's
  indifference curve); `exercise_13_D_2b_exists` (`W = 10`, `L = 8`, `p_L = 1/3`, `p_H = 1/2`,
  `u = log`, `λ = 1/10`) and `exercise_13_D_2b_nonexistence` (`λ = 9/10`): an equilibrium need not
  exist.

Departures: utility levels are used as coordinates, so `u` must map the wealth domain onto `ℝ`
(e.g. `log` on `(0, ∞)`); we assume `0 < p_L < p_H < 1` and `0 < L`; an indifferent individual
chooses the policy with more coverage.
-/

namespace MWG.AdverseSelection

open Set

/-- **Exercise 13.D.2** (MWG, p. 476). The two-type insurance (Rothschild-Stiglitz) screening
model in utility coordinates. -/
structure RSModel where
  qS : ℝ
  qR : ℝ
  a₁ : ℝ
  a₂ : ℝ
  h : ℝ → ℝ
  ρS : ℝ
  ρR : ℝ
  lam : ℝ

namespace RSModel

variable {M : RSModel}

/-- The probability of state `1` for type `b`. -/
def q (M : RSModel) (b : Bool) : ℝ := if b then M.qS else M.qR

/-- Expected utility of type `b` from the utility levels `k`. -/
def V (M : RSModel) (b : Bool) (k : ℝ × ℝ) : ℝ := M.q b * k.1 + (1 - M.q b) * k.2

/-- Expected profit on type `b`. -/
def Pr (M : RSModel) (b : Bool) (k : ℝ × ℝ) : ℝ :=
  M.q b * (M.a₁ - M.h k.1) + (1 - M.q b) * (M.a₂ - M.h k.2)

/-- Expected endowment `q_b a₁ + (1 - q_b) a₂` of type `b`. -/
def abar (M : RSModel) (b : Bool) : ℝ := M.q b * M.a₁ + (1 - M.q b) * M.a₂

/-- **Exercise 13.D.2** (MWG, p. 476). The screening game. -/
noncomputable def game (M : RSModel) : ScrGame where
  U := M.V
  P := M.Pr
  ρ b := if b then M.ρS else M.ρR
  key k := k.1 - k.2
  lam := M.lam
  adm _ := True

/-- The assumptions: `0 < q_R < q_S < 1`, `0 < λ < 1`, `a₂ < a₁`, and `h = u⁻¹` strictly
increasing, strictly convex and continuous (`u` strictly increasing and strictly concave). -/
structure Valid (M : RSModel) : Prop where
  qR_pos : 0 < M.qR
  q_lt : M.qR < M.qS
  qS_lt : M.qS < 1
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  a_lt : M.a₂ < M.a₁
  h_mono : StrictMono M.h
  h_conv : StrictConvexOn ℝ univ M.h
  h_cont : Continuous M.h

theorem q_true (M : RSModel) : M.q true = M.qS := rfl
theorem q_false (M : RSModel) : M.q false = M.qR := rfl

theorem Valid.q_pos (hM : M.Valid) (b : Bool) : 0 < M.q b := by
  cases b
  · exact hM.qR_pos
  · exact hM.qR_pos.trans hM.q_lt

theorem Valid.q_lt_one (hM : M.Valid) (b : Bool) : M.q b < 1 := by
  cases b
  · exact hM.q_lt.trans hM.qS_lt
  · exact hM.qS_lt

theorem game_inj (M : RSModel) : M.game.Inj := by
  intro b k k' hu hk
  simp only [game, V] at hu hk
  have h2 : k.2 = k'.2 := by
    have : M.q b * (k.1 - k.2) = M.q b * (k'.1 - k'.2) := by rw [hk]
    nlinarith
  exact Prod.ext (by linarith) h2

theorem V_diag (M : RSModel) (b : Bool) (v : ℝ) : M.V b (v, v) = v := by
  simp only [V]; ring

theorem Pr_diag (M : RSModel) (b : Bool) (v : ℝ) : M.Pr b (v, v) = M.abar b - M.h v := by
  simp only [Pr, abar]; ring

theorem abar_lt (hM : M.Valid) : M.abar false < M.abar true := by
  simp only [abar, q_true, q_false]
  nlinarith [mul_pos (sub_pos.2 hM.q_lt) (sub_pos.2 hM.a_lt)]

/-- Jensen's inequality: `h(V_b(k)) ≤ q_b h(k₁) + (1 - q_b) h(k₂)`, so
`Pr_b(k) ≤ a̅_b - h(V_b(k))`. -/
theorem Pr_le (hM : M.Valid) (b : Bool) (k : ℝ × ℝ) : M.Pr b k ≤ M.abar b - M.h (M.V b k) := by
  have := hM.h_conv.convexOn.2 (mem_univ k.1) (mem_univ k.2) (hM.q_pos b).le
    (sub_nonneg.2 (hM.q_lt_one b).le) (by ring)
  simp only [smul_eq_mul] at this
  simp only [Pr, abar, V]
  linarith

/-- Strict Jensen: `Pr_b(k) < a̅_b - h(V_b(k))` unless `k₁ = k₂`. -/
theorem Pr_lt (hM : M.Valid) (b : Bool) {k : ℝ × ℝ} (hk : k.1 ≠ k.2) :
    M.Pr b k < M.abar b - M.h (M.V b k) := by
  have := hM.h_conv.2 (mem_univ k.1) (mem_univ k.2) hk (hM.q_pos b)
    (sub_pos.2 (hM.q_lt_one b)) (by ring)
  simp only [smul_eq_mul] at this
  simp only [Pr, abar, V]
  linarith

theorem V_add (M : RSModel) (b : Bool) (k d : ℝ × ℝ) (τ : ℝ) :
    M.V b (k.1 + τ * d.1, k.2 + τ * d.2) = M.V b k + τ * (M.q b * d.1 + (1 - M.q b) * d.2) := by
  simp only [V]; ring

/-- Profits change continuously along a line. -/
theorem Pr_cont (hM : M.Valid) (b : Bool) (k d : ℝ × ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ τ₀, 0 < τ₀ ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → M.Pr b k - η < M.Pr b (k.1 + τ * d.1, k.2 + τ * d.2) := by
  have hc : Continuous fun τ : ℝ => M.Pr b (k.1 + τ * d.1, k.2 + τ * d.2) := by
    have := hM.h_cont
    simp only [Pr]
    fun_prop
  have hev := (hc.tendsto 0).eventually (lt_mem_nhds (a := M.Pr b k - η)
    (by simp only [zero_mul, add_zero, Prod.mk.eta]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun τ hτ hτle => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
  linarith

/-- **Lemma 13.D.1** for the insurance model: zero profits in every SPNE. -/
theorem game_zero (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.game.IsEq A₁ A₂) :
    M.game.profit A₁ A₂ = 0 ∧ M.game.profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (game_inj M) hM.lam_pos.le hM.lam_lt.le
    (fun δ k => (k.1 + δ, k.2 + δ)) (fun _ _ _ _ => trivial) (fun δ b k => ?_)
    (fun δ k => ?_) (fun b k η hη => ?_) h
  · simp only [game, V]; ring
  · simp only [game]; ring
  · obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM b k (1, 1) hη
    refine ⟨τ₀, hτ₀, fun δ hδ hδle => ?_⟩
    have := hτ δ hδ hδle
    simp only [mul_one] at this
    exact this

/-- From a contract `e` with `Pr_S(e) ≥ 0` that the risky type values below `v*`, there is a
contract the safe type strictly prefers, profitable on her, still valued below `v*` by the risky
type (move towards full insurance along the safe type's indifference curve, then sweeten). -/
theorem exists_improve (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {e : ℝ × ℝ}
    (he0 : 0 ≤ M.Pr true e) (heR : M.V false e < vs) :
    ∃ k', M.V true e < M.V true k' ∧ 0 < M.Pr true k' ∧ M.V false k' < vs := by
  have hab := abar_lt hM
  -- a contract with the same value for the safe type and a strictly positive profit
  obtain ⟨z, hzS, hzP, hzR⟩ : ∃ z, M.V true z = M.V true e ∧ 0 < M.Pr true z ∧
      M.V false z < vs := by
    by_cases hd : e.1 = e.2
    · refine ⟨e, rfl, ?_, heR⟩
      have he : e = (e.1, e.1) := Prod.ext rfl hd.symm
      rw [he, Pr_diag]
      rw [he, V_diag] at heR
      have := hM.h_mono heR
      linarith
    · set m := M.V true e
      set D := vs - M.V false e
      set A := |m - M.V false e|
      have hD : 0 < D := by simp only [D]; linarith
      have hA : 0 ≤ A := abs_nonneg _
      set τ := min (1 / 2) (D / (2 * (A + 1)))
      have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
      have hτ1 : τ ≤ 1 / 2 := min_le_left _ _
      have hτ2 : τ * (2 * (A + 1)) ≤ D :=
        (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
      refine ⟨((1 - τ) * e.1 + τ * m, (1 - τ) * e.2 + τ * m), ?_, ?_, ?_⟩
      · simp only [V, m]; ring
      · have c1 := hM.h_conv.convexOn.2 (mem_univ e.1) (mem_univ m) (by linarith : 0 ≤ 1 - τ)
          hτ0.le (by ring)
        have c2 := hM.h_conv.convexOn.2 (mem_univ e.2) (mem_univ m) (by linarith : 0 ≤ 1 - τ)
          hτ0.le (by ring)
        have j := Pr_lt hM true hd
        simp only [smul_eq_mul] at c1 c2
        have hq := hM.q_pos true
        have hq1 := hM.q_lt_one true
        simp only [Pr, abar] at j he0 ⊢
        have k1 := mul_le_mul_of_nonneg_left c1 hq.le
        have k2 := mul_le_mul_of_nonneg_left c2 (sub_nonneg.2 hq1.le)
        nlinarith [mul_lt_mul_of_pos_left j hτ0]
      · have hle : τ * (m - M.V false e) ≤ τ * A :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hτ0.le
        have : M.V false ((1 - τ) * e.1 + τ * m, (1 - τ) * e.2 + τ * m) =
            M.V false e + τ * (m - M.V false e) := by simp only [V]; ring
        rw [this]
        nlinarith
  -- sweeten it slightly
  obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM true z (1, 1) (half_pos hzP)
  set δ := min τ₀ ((vs - M.V false z) / 2)
  have hδ : 0 < δ := lt_min hτ₀ (by linarith)
  have hδ2 : δ ≤ (vs - M.V false z) / 2 := min_le_right _ _
  have hP := hτ δ hδ (min_le_left _ _)
  simp only [mul_one] at hP
  refine ⟨(z.1 + δ, z.2 + δ), ?_, by linarith, ?_⟩
  · have := V_add M true z (1, 1) δ
    simp only [mul_one] at this
    rw [this, hzS]; simp only [q_true]; linarith
  · have := V_add M false z (1, 1) δ
    simp only [mul_one] at this
    rw [this]; simp only [q_false]; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476), the general characterization. Suppose `h v* = a̅_R`,
the risky type's outside option is worse than `v*`, and the safe type's outside option is the
value of a contract `e` with `Pr_S(e) ≥ 0` and `V_R(e) < v*` (both hold for insurance and for
Exercise 13.D.3(c)). In every SPNE the risky type takes full insurance `(v*, v*)` at her fair
price, the safe type takes a contract `k_S` with `Pr_S(k_S) = 0`, `V_R(k_S) = v*` and
`k_S.2 < k_S.1` (partial insurance), and both firms earn zero. -/
theorem rs_characterization (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false)
    (hR : M.ρR < vs) (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < vs)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.game.IsEq A₁ A₂) :
    ∃ kS, M.game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧ M.game.Chooses true (A₁ ∪ A₂) kS ∧
      M.Pr true kS = 0 ∧ M.V false kS = vs ∧ kS.2 < kS.1 ∧
      M.game.profit A₁ A₂ = 0 ∧ M.game.profit A₂ A₁ = 0 := by
  have hI := game_inj M
  have hz := game_zero hM h
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hab := abar_lt hM
  have hU : ∀ b k, M.game.U b k = M.V b k := fun _ _ => rfl
  have hP : ∀ b k, M.game.P b k = M.Pr b k := fun _ _ => rfl
  have hρf : M.game.ρ false = M.ρR := rfl
  have hρt : M.game.ρ true = M.ρS := rfl
  -- full insurance slightly above the risky type's utility is profitable
  have devR : ∀ v, M.ρR ≤ v → v < vs → (∀ k ∈ A₁ ∪ A₂, M.V false k < v) → False := by
    intro v hv0 hvs hlt
    have hhv : M.h v < M.abar false := hv ▸ hM.h_mono hvs
    refine ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (v, v)) trivial
      (by rw [hρf, hU, V_diag]; exact hv0) (fun k hk => ?_) (by rw [hP, Pr_diag]; linarith)
      (by rw [hP, Pr_diag]; linarith)
    rw [hU, hU, V_diag]; exact hlt k (Finset.mem_union_right _ hk)
  obtain ⟨kR, hkR⟩ : ∃ kR, M.game.Chooses false (A₁ ∪ A₂) kR := by
    by_contra hno
    refine devR M.ρR le_rfl hR fun k hk => ?_
    by_contra hle
    exact hno (ScrGame.exists_chooses false ⟨k, hk, by rw [hρf, hU]; linarith⟩)
  have hRge : vs ≤ M.V false kR := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : M.ρR ≤ M.V false kR := hkR.2.1
    refine devR ((M.V false kR + vs) / 2) (by linarith) (by linarith) fun k hk => ?_
    have := hkR.2.2.1 k hk
    rw [hU, hU] at this
    linarith
  have hPR : M.Pr false kR ≤ 0 := by
    have := Pr_le hM false kR
    have := hM.h_mono.monotone hRge
    linarith
  -- the safe type works
  obtain ⟨kS, hkS⟩ : ∃ kS, M.game.Chooses true (A₁ ∪ A₂) kS := by
    by_contra hno
    obtain ⟨e, he1, he2, he3⟩ := hS
    obtain ⟨k', hk1, hk2, hk3⟩ := exists_improve hM hv he2 he3
    refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial (k' := k')
      (by rw [hρt, hU]; linarith) (fun k hk => ?_) (by rw [hU, hU]; linarith) hk2
    rw [hU, hU]
    by_contra hle
    exact hno (ScrGame.exists_chooses true ⟨k, hk, by rw [hρt, hU]; linarith⟩)
  -- no profit on the safe type
  have hPS : M.Pr true kS ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set qm := (M.qR + M.qS) / 2
    obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM true kS (1 - qm, -qm) (half_pos hpos)
    have hP' := hτ τ₀ hτ₀ le_rfl
    have hVt := V_add M true kS (1 - qm, -qm) τ₀
    have hVf := V_add M false kS (1 - qm, -qm) τ₀
    simp only [q_true, q_false] at hVt hVf
    have hq := hM.q_lt
    have e1 : M.qS * (1 - qm) + (1 - M.qS) * -qm = M.qS - qm := by ring
    have e2 : M.qR * (1 - qm) + (1 - M.qR) * -qm = M.qR - qm := by ring
    rw [e1] at hVt
    rw [e2] at hVf
    have h1 : 0 < τ₀ * (M.qS - qm) := mul_pos hτ₀ (by simp only [qm]; linarith)
    have h2 : τ₀ * (M.qR - qm) < 0 := mul_neg_of_pos_of_neg hτ₀ (by simp only [qm]; linarith)
    have hkSR := hkR.2.2.1 kS hkS.1
    refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial
      (k' := (kS.1 + τ₀ * (1 - qm), kS.2 + τ₀ * -qm)) ?_ (fun k hk => ?_) ?_
      (by change 0 < M.Pr true _; linarith)
    · have := hkS.2.1; rw [hρt, hU] at this; rw [hρt, hU, hVt]; linarith
    · have := hkS.2.2.1 k hk; rw [hU, hU] at this; rw [hU, hU, hVt]; linarith
    · rw [hU, hU] at hkSR; rw [hU, hU, hVf]; linarith
  -- both chosen contracts break even
  have htot := ScrGame.profit_add (G := M.game) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hkR, ScrGame.typeProfit_add hI hkS, hP, hP] at htot
  have hlam : M.game.lam = M.lam := rfl
  rw [hlam] at htot
  have hPR0 : M.Pr false kR = 0 := by nlinarith
  have hPS0 : M.Pr true kS = 0 := by nlinarith
  -- the risky type is fully insured at her fair price
  have hdiag : kR.1 = kR.2 := by
    by_contra hne
    have := Pr_lt hM false hne
    have := hM.h_mono.monotone hRge
    linarith
  have hkReq : kR = (vs, vs) := by
    have hk : kR = (kR.1, kR.1) := Prod.ext rfl hdiag.symm
    rw [hk, Pr_diag] at hPR0
    have : M.h kR.1 = M.h vs := by linarith
    rw [hk, hM.h_mono.injective this]
  rw [hkReq] at hkR
  have hVRS : M.V false kS ≤ vs := by
    have := hkR.2.2.1 kS hkS.1
    rw [hU, hU, V_diag] at this; exact this
  have hVSS : vs ≤ M.V true kS := by
    have := hkS.2.2.1 (vs, vs) hkR.1
    rw [hU, hU, V_diag] at this; exact this
  have hpart : kS.2 < kS.1 := by
    by_contra hle
    rw [not_lt] at hle
    have hd : M.V true kS - M.V false kS = (M.qS - M.qR) * (kS.1 - kS.2) := by
      simp only [V, q_true, q_false]; ring
    have hq := hM.q_lt
    have h1 : (M.qS - M.qR) * (kS.1 - kS.2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have h2 : (M.qS - M.qR) * (kS.1 - kS.2) = 0 := by linarith
    have h3 : kS.1 = kS.2 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · linarith
      · linarith
    have hk : kS = (kS.1, kS.1) := Prod.ext rfl h3.symm
    have hm : kS.1 = vs := by
      have := hVSS; rw [hk, V_diag] at this
      have := hVRS; rw [hk, V_diag] at this
      linarith
    rw [hk, Pr_diag, hm] at hPS0
    linarith
  refine ⟨kS, hkR, hkS, hPS0, le_antisymm hVRS ?_, hpart, hz.1, hz.2⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨k', hk1, hk2, hk3⟩ := exists_improve hM hv hPS0.ge hlt
  refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial (k' := k') ?_ (fun k hk => ?_)
    (by rw [hU, hU, V_diag]; exact hk3) hk2
  · have := hkS.2.1; rw [hρt, hU] at this; rw [hρt, hU]; linarith
  · have := hkS.2.2.1 k hk; rw [hU, hU] at this; rw [hU, hU]; linarith

/-- The safe type's equilibrium contract is unique: the risky type's indifference line through
`(v*, v*)` meets the safe type's zero-profit curve at most once with `k₂ < k₁`. -/
theorem rs_point_lt (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {k k' : ℝ × ℝ}
    (hk : M.Pr true k = 0 ∧ M.V false k = vs ∧ k.2 < k.1)
    (hk' : M.Pr true k' = 0 ∧ M.V false k' = vs ∧ k'.2 < k'.1)
    (hlt : k.1 - k.2 < k'.1 - k'.2) : False := by
  have hab := abar_lt hM
  set s := k.1 - k.2
  set s' := k'.1 - k'.2
  have hs : 0 < s := by simp only [s]; linarith [hk.2.2]
  have hqR := hM.qR_pos
  have hqR1 := hM.q_lt_one false
  rw [q_false] at hqR1
  have hk1 : k.1 = vs + (1 - M.qR) * s := by
    have := hk.2.1; simp only [V, q_false] at this; simp only [s]; linear_combination this
  have hk2 : k.2 = vs - M.qR * s := by
    have := hk.2.1; simp only [V, q_false] at this; simp only [s]; linear_combination this
  have hk1' : k'.1 = vs + (1 - M.qR) * s' := by
    have := hk'.2.1; simp only [V, q_false] at this; simp only [s']; linear_combination this
  have hk2' : k'.2 = vs - M.qR * s' := by
    have := hk'.2.1; simp only [V, q_false] at this; simp only [s']; linear_combination this
  set t := s / s'
  have hs' : 0 < s' := hs.trans hlt
  have ht0 : 0 < t := div_pos hs hs'
  have ht1 : t < 1 := (div_lt_one hs').2 hlt
  have hts : t * s' = s := by simp only [t]; field_simp
  have hne1 : vs ≠ k'.1 := by
    rw [hk1']; nlinarith [mul_pos (sub_pos.2 hqR1) hs']
  have c1 := hM.h_conv.2 (mem_univ vs) (mem_univ k'.1) hne1 (sub_pos.2 ht1) ht0 (by ring)
  have c2 := hM.h_conv.convexOn.2 (mem_univ vs) (mem_univ k'.2) (sub_pos.2 ht1).le ht0.le
    (by ring)
  simp only [smul_eq_mul] at c1 c2
  have e1 : (1 - t) * vs + t * k'.1 = k.1 := by rw [hk1', hk1, ← hts]; ring
  have e2 : (1 - t) * vs + t * k'.2 = k.2 := by rw [hk2', hk2, ← hts]; ring
  rw [e1] at c1
  rw [e2] at c2
  have hq := hM.q_pos true
  have hq1 := hM.q_lt_one true
  have h0 := hk.1
  have h0' := hk'.1
  simp only [Pr, abar, q_true, q_false] at h0 h0' hv hab
  rw [q_true] at hq hq1
  have k1 := mul_lt_mul_of_pos_left c1 hq
  have k2 := mul_le_mul_of_nonneg_left c2 (sub_nonneg.2 hq1.le)
  nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 hab)]

theorem rs_point_unique (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {k k' : ℝ × ℝ}
    (hk : M.Pr true k = 0 ∧ M.V false k = vs ∧ k.2 < k.1)
    (hk' : M.Pr true k' = 0 ∧ M.V false k' = vs ∧ k'.2 < k'.1) : k = k' := by
  rcases lt_trichotomy (k.1 - k.2) (k'.1 - k'.2) with hlt | heq | hgt
  · exact (rs_point_lt hM hv hk hk' hlt).elim
  · exact game_inj M false k k'
      (by change M.V false k = M.V false k'; rw [hk.2.1, hk'.2.1]) heq
  · exact (rs_point_lt hM hv hk' hk hgt).elim

/-- **Exercise 13.D.2(b)** (MWG, p. 476), an existence criterion. Let `k_S` be the safe type's
contract of `rs_characterization`. If every contract `k` that the safe type weakly prefers to
`k_S` either is unprofitable on her when the risky type does not strictly prefer it to full
insurance, or, when the risky type strictly prefers it, loses money once the risky type's best
response is taken into account (`λ Pr_S(k) + (1 - λ)(a̅_R - h(V_R(k))) ≤ 0`), then both firms
offering `{(v*, v*), k_S}` is an SPNE. -/
theorem rs_isEq (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {kS : ℝ × ℝ}
    (hP : M.Pr true kS = 0) (hVR : M.V false kS = vs) (hlt : kS.2 < kS.1) (hρR : M.ρR ≤ vs)
    (hρS : M.ρS ≤ M.V true kS)
    (hN : ∀ k, M.V true kS ≤ M.V true k → (M.V false k ≤ vs → M.Pr true k ≤ 0) ∧
      (vs < M.V false k → M.lam * M.Pr true k + (1 - M.lam) * (M.abar false - M.h (M.V false k))
        ≤ 0)) :
    M.game.IsEq {(vs, vs), kS} {(vs, vs), kS} := by
  have hI := game_inj M
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  set A : Finset (ℝ × ℝ) := {(vs, vs), kS} with hA
  have hU : ∀ b k, M.game.U b k = M.V b k := fun _ _ => rfl
  have hPd : ∀ b k, M.game.P b k = M.Pr b k := fun _ _ => rfl
  have hρf : M.game.ρ false = M.ρR := rfl
  have hρt : M.game.ρ true = M.ρS := rfl
  have hkey : ∀ k, M.game.key k = k.1 - k.2 := fun _ => rfl
  have hVSS : vs < M.V true kS := by
    have : M.V true kS - M.V false kS = (M.qS - M.qR) * (kS.1 - kS.2) := by
      simp only [V, q_true, q_false]; ring
    nlinarith [mul_pos (sub_pos.2 hM.q_lt) (sub_pos.2 hlt)]
  have hmemd : (vs, vs) ∈ A := by simp [hA]
  have hmemS : kS ∈ A := by simp [hA]
  have hmemA : ∀ k ∈ A, k = (vs, vs) ∨ k = kS := fun k hk => by
    simpa [hA] using hk
  have hchR : M.game.Chooses false (A ∪ A) (vs, vs) := by
    rw [Finset.union_self]
    refine ⟨hmemd, by rw [hρf, hU, V_diag]; exact hρR, fun k hk => ?_, fun k hk hu => ?_⟩
    · rw [hU, hU, V_diag]
      rcases hmemA k hk with rfl | rfl
      · rw [V_diag]
      · rw [hVR]
    · rw [hkey, hkey]
      rcases hmemA k hk with rfl | rfl
      · exact le_rfl
      · simp only; linarith
  have hchS : M.game.Chooses true (A ∪ A) kS := by
    rw [Finset.union_self]
    refine ScrGame.chooses_of_strict hmemS (by rw [hρt, hU]; exact hρS) fun k hk hne => ?_
    rcases hmemA k hk with rfl | rfl
    · rw [hU, hU, V_diag]; exact hVSS
    · exact absurd rfl hne
  have hzero : M.game.profit A A = 0 := by
    unfold ScrGame.profit
    rw [ScrGame.typeProfit_of_chooses hI hchR, ScrGame.typeProfit_of_chooses hI hchS, hPd, hPd,
      Pr_diag, hv, hP]
    ring
  -- the risky type never yields a profit
  have hYle : ∀ B k', M.game.Chooses false (B ∪ A) k' →
      M.Pr false k' ≤ M.abar false - M.h (M.V false k') ∧ vs ≤ M.V false k' := by
    intro B k' hk'
    have h1 := hk'.2.2.1 (vs, vs) (Finset.mem_union_right _ hmemd)
    rw [hU, hU, V_diag] at h1
    exact ⟨Pr_le hM false k', h1⟩
  have hY : ∀ B, M.game.typeProfit false B A ≤ 0 := by
    intro B
    by_cases hex : ∃ k', M.game.Chooses false (B ∪ A) k'
    · obtain ⟨k', hk'⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk', hPd]
      obtain ⟨h1, h2⟩ := hYle B k' hk'
      have := hM.h_mono.monotone h2
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) (by linarith)
    · rw [ScrGame.typeProfit_of_not hex]
  have hdev : ∀ B, M.game.Menu B → M.game.profit B A ≤ 0 := by
    intro B _
    have hYB := hY B
    unfold ScrGame.profit
    have hlam : M.game.lam = M.lam := rfl
    rw [hlam]
    by_cases hexS : ∃ k, M.game.Chooses true (B ∪ A) k
    · obtain ⟨k, hk⟩ := hexS
      rw [ScrGame.typeProfit_of_chooses hI hk, hPd]
      have hge := hk.2.2.1 kS (Finset.mem_union_right _ hmemS)
      rw [hU, hU] at hge
      rcases le_or_gt (M.Pr true k) 0 with hPk | hPk
      · have := mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg B A k) hPk
        nlinarith
      · have hkA : k ∉ A := by
          intro hm
          rcases hmemA k hm with rfl | rfl
          · rw [V_diag] at hge; linarith
          · linarith
        have hkB : k ∈ B := by
          rcases Finset.mem_union.1 hk.1 with hm | hm
          · exact hm
          · exact absurd hm hkA
        have hsh : SigModel.share B A k = 1 := by simp [SigModel.share, hkB, hkA]
        have hRk : vs < M.V false k := by
          by_contra hle
          rw [not_lt] at hle
          linarith [(hN k hge).1 hle]
        obtain ⟨k', hk'⟩ := ScrGame.exists_chooses (G := M.game) false
          ⟨k, hk.1, by rw [hρf, hU]; linarith⟩
        have hk'k := hk'.2.2.1 k hk.1
        rw [hU, hU] at hk'k
        have hk'A : k' ∉ A := by
          intro hm
          rcases hmemA k' hm with rfl | rfl
          · rw [V_diag] at hk'k; linarith
          · linarith
        have hk'B : k' ∈ B := by
          rcases Finset.mem_union.1 hk'.1 with hm | hm
          · exact hm
          · exact absurd hm hk'A
        have hpR : M.game.typeProfit false B A = M.Pr false k' := by
          rw [ScrGame.typeProfit_of_chooses hI hk', hPd]
          simp [SigModel.share, hk'B, hk'A]
        have h1 := (hYle B k' hk').1
        have h2 := hM.h_mono.monotone hk'k
        have h3 := (hN k hge).2 hRk
        rw [hpR, hsh, one_mul]
        nlinarith
    · rw [ScrGame.typeProfit_of_not hexS]
      nlinarith
  refine ⟨fun _ _ => trivial, fun _ _ => trivial, fun B hB => ?_, fun B hB => ?_⟩ <;>
    rw [hzero] <;> exact hdev B hB

/-- **Exercise 13.D.2(b)** (MWG, p. 476), nonexistence. If some contract `k'` gives both types
strictly more than their equilibrium contracts (`(v*, v*)` and the safe type's `k_S`) at a
positive expected profit, no SPNE exists. -/
theorem rs_no_eq (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) (hR : M.ρR < vs)
    (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < vs)
    {kS : ℝ × ℝ} (hkS : M.Pr true kS = 0 ∧ M.V false kS = vs ∧ kS.2 < kS.1) {k' : ℝ × ℝ}
    (hS' : M.V true kS < M.V true k') (hR' : vs < M.V false k')
    (hpos : 0 < (1 - M.lam) * M.Pr false k' + M.lam * M.Pr true k') :
    ¬ ∃ A₁ A₂, M.game.IsEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  obtain ⟨kS', hkR, hkS', hP0, hV0, hlt0, hz, -⟩ := rs_characterization hM hv hR hS h
  have he := rs_point_unique hM hv ⟨hP0, hV0, hlt0⟩ hkS
  rw [he] at hkS'
  refine ScrGame.IsEq.dev_both (game_inj M) h hz (k' := k') trivial (fun b => ?_)
    (fun b k hk => ?_) hpos
  · cases b
    · have := hkR.2.1; change M.ρR ≤ M.V false (vs, vs) at this
      rw [V_diag] at this; change M.ρR ≤ M.V false k'; linarith
    · have := hkS'.2.1; change M.ρS ≤ M.V true kS at this
      change M.ρS ≤ M.V true k'; linarith
  · cases b
    · have := hkR.2.2.1 k (Finset.mem_union_right _ hk)
      change M.V false k ≤ M.V false (vs, vs) at this
      rw [V_diag] at this; change M.V false k < M.V false k'; linarith
    · have := hkS'.2.2.1 k (Finset.mem_union_right _ hk)
      change M.V true k ≤ M.V true kS at this
      change M.V true k < M.V true k'; linarith

/-- The tangent line of `exp` at `log x₀`: `x₀ (1 + v - log x₀) ≤ exp v`. -/
theorem exp_ge_tangent {x0 : ℝ} (hx0 : 0 < x0) (v : ℝ) :
    x0 * (1 + (v - Real.log x0)) ≤ Real.exp v := by
  have h1 : Real.exp v = x0 * Real.exp (v - Real.log x0) := by
    rw [← Real.exp_log hx0, ← Real.exp_add, Real.exp_log hx0]; ring_nf
  rw [h1]
  have := Real.add_one_le_exp (v - Real.log x0)
  nlinarith

theorem log9_add_log4 : Real.log 9 + Real.log 4 = 2 * Real.log 6 := by
  rw [← Real.log_mul (by norm_num) (by norm_num), two_mul,
    ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log4_lt_log9 : Real.log 4 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)

/-- The model with `u = log` (`h = exp + κ`), `q_S = 2/3`, `q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ`
satisfies the assumptions. -/
theorem log_valid (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl0 : 0 < M.lam) (hl1 : M.lam < 1) : M.Valid where
  qR_pos := by rw [hqR]; norm_num
  q_lt := by rw [hqR, hqS]; norm_num
  qS_lt := by rw [hqS]; norm_num
  lam_pos := hl0
  lam_lt := hl1
  a_lt := by rw [ha1, ha2]; linarith
  h_mono := by rw [hh]; exact fun a b hab => by simp only; linarith [Real.exp_lt_exp.2 hab]
  h_conv := by rw [hh]; exact strictConvexOn_exp.add_const κ
  h_cont := by rw [hh]; fun_prop

/-- **Exercise 13.D.2(b)** (MWG, p. 476), an existence instance (`u = log`). With `q_S = 2/3`,
`q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ` and `λ ≤ 9/19`, both firms offering
`{(log 6, log 6), (log 9, log 4)}` (wealth `(6, 6) + κ` and `(9, 4) + κ`) is an SPNE, provided
the outside options are not better than the equilibrium contracts. -/
theorem log_isEq (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl0 : 0 < M.lam) (hl : M.lam ≤ 9 / 19) (hρR : M.ρR ≤ Real.log 6)
    (hρS : M.ρS ≤ M.V true (Real.log 9, Real.log 4)) :
    M.game.IsEq {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have hM := log_valid M hqS hqR ha1 ha2 hh hl0 (by linarith)
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have e6 : Real.exp (Real.log 6) = 6 := Real.exp_log (by norm_num)
  refine rs_isEq hM (vs := Real.log 6) ?_ ?_ ?_ log4_lt_log9 hρR hρS fun k hk => ⟨?_, ?_⟩
  · rw [hh]; simp only [abar, q_false, hqR, ha1, ha2, e6]; ring
  · simp only [Pr, hh, q_true, hqS, ha1, ha2, e9, e4]; ring
  · simp only [V, q_false, hqR]; linarith
  · intro hR
    simp only [V, q_true, q_false, hqS, hqR] at hk hR
    have t1 := exp_ge_tangent (x0 := 9) (by norm_num) k.1
    have t2 := exp_ge_tangent (x0 := 4) (by norm_num) k.2
    simp only [Pr, hh, q_true, hqS, ha1, ha2]
    nlinarith
  · intro hR
    simp only [V, q_true, q_false, hqS, hqR] at hk hR
    have t1 := exp_ge_tangent (x0 := 9) (by norm_num) k.1
    have t2 := exp_ge_tangent (x0 := 4) (by norm_num) k.2
    have t3 := exp_ge_tangent (x0 := 6) (by norm_num) (1 / 2 * k.1 + (1 - 1 / 2) * k.2)
    simp only [Pr, abar, V, hh, q_true, q_false, hqS, hqR, ha1, ha2]
    set d1 := k.1 - Real.log 9
    set d2 := k.2 - Real.log 4
    have hd : 0 ≤ 2 * d1 + d2 := by simp only [d1, d2]; linarith
    have hd' : 0 < d1 + d2 := by simp only [d1, d2]; linarith
    have hS : 2 / 3 * (10 + κ - (Real.exp k.1 + κ)) + (1 - 2 / 3) * (2 + κ - (Real.exp k.2 + κ))
        ≤ -6 * d1 - 4 / 3 * d2 := by simp only [d1, d2]; linarith
    have hRb : 1 / 2 * (10 + κ) + (1 - 1 / 2) * (2 + κ) -
        (Real.exp (1 / 2 * k.1 + (1 - 1 / 2) * k.2) + κ) ≤ -3 * (d1 + d2) := by
      simp only [d1, d2]; linarith
    have hl1 : 0 ≤ 1 - M.lam := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hS hl0.le, mul_le_mul_of_nonneg_left hRb hl1,
      mul_nonneg hl0.le hd, mul_nonneg (by linarith : (0 : ℝ) ≤ 9 / 19 - M.lam) hd'.le]

/-- **Exercise 13.D.2(b)** (MWG, p. 476), a nonexistence instance (`u = log`). With the data of
`log_isEq` and `λ = 9/10`, the pooling contract `(log 7, log 7)` (wealth `7 + κ` in both states)
attracts both types at a profit: no SPNE exists. -/
theorem log_no_eq (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl : M.lam = 9 / 10) (hR : M.ρR < Real.log 6)
    (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < Real.log 6) :
    ¬ ∃ A₁ A₂, M.game.IsEq A₁ A₂ := by
  have hM := log_valid M hqS hqR ha1 ha2 hh (by rw [hl]; norm_num) (by rw [hl]; norm_num)
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have e6 : Real.exp (Real.log 6) = 6 := Real.exp_log (by norm_num)
  have e7 : Real.exp (Real.log 7) = 7 := Real.exp_log (by norm_num)
  have h76 : Real.log 6 < Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
  have h7 : 2 * Real.log 9 + Real.log 4 < 3 * Real.log 7 := by
    have a : 2 * Real.log 9 + Real.log 4 = Real.log (9 ^ 2 * 4) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have b : 3 * Real.log 7 = Real.log (7 ^ 3) := by rw [Real.log_pow]; norm_num
    rw [a, b]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  refine rs_no_eq hM (vs := Real.log 6) ?_ hR hS (kS := (Real.log 9, Real.log 4)) ⟨?_, ?_,
    log4_lt_log9⟩ (k' := (Real.log 7, Real.log 7)) ?_ ?_ ?_
  · rw [hh]; simp only [abar, q_false, hqR, ha1, ha2, e6]; ring
  · simp only [Pr, hh, q_true, hqS, ha1, ha2, e9, e4]; ring
  · simp only [V, q_false, hqR]; linarith
  · simp only [V, q_true, hqS]; linarith
  · rw [V_diag]; exact h76
  · rw [Pr_diag, Pr_diag, hh, hl]
    simp only [abar, q_true, q_false, hqS, hqR, ha1, ha2, e7]
    linarith

/-- **Exercise 13.D.2(a)** (MWG, p. 476). A policy `(M, R)` (premium `M`, payment `R` in case of
loss) corresponds to the wealth levels `(W - M, W - L - M + R)` in the states "no loss" and
"loss". -/
def policyWealth (W L : ℝ) : ℝ × ℝ ≃ ℝ × ℝ where
  toFun p := (W - p.1, W - L - p.1 + p.2)
  invFun x := (W - x.1, x.2 - x.1 + L)
  left_inv p := by ext <;> simp only <;> ring
  right_inv x := by ext <;> simp only <;> ring

/-- **Exercise 13.D.2(a)** (MWG, p. 476). Policies and wealth levels correspond bijectively, and
the insured's expected utility and the insurer's expected profit `M - pR` are functions of the
wealth levels `x = (x₁, x₂)`: `(1 - p) u(x₁) + p u(x₂)` and `(1 - p)(W - x₁) + p(W - L - x₂)`. -/
theorem exercise_13_D_2a (W L p : ℝ) (u : ℝ → ℝ) (pol : ℝ × ℝ) :
    Function.Bijective (policyWealth W L) ∧
      (1 - p) * u (W - pol.1) + p * u (W - L - pol.1 + pol.2) =
        (1 - p) * u (policyWealth W L pol).1 + p * u (policyWealth W L pol).2 ∧
      pol.1 - p * pol.2 =
        (1 - p) * (W - (policyWealth W L pol).1) + p * (W - L - (policyWealth W L pol).2) := by
  refine ⟨(policyWealth W L).bijective, rfl, ?_⟩
  simp only [policyWealth, Equiv.coe_fn_mk]; ring

/-- **Exercise 13.D.2(a)** (MWG, p. 476), with `u = log`: positive wealth levels and utility
levels correspond bijectively (`h = exp` is the inverse of `u`). -/
theorem exercise_13_D_2a_log (x v : ℝ × ℝ) (hx1 : 0 < x.1) (hx2 : 0 < x.2) :
    (Real.exp (Real.log x.1), Real.exp (Real.log x.2)) = x ∧
      (Real.log (Real.exp v.1), Real.log (Real.exp v.2)) = v := by
  rw [Real.exp_log hx1, Real.exp_log hx2, Real.log_exp, Real.log_exp]
  exact ⟨rfl, rfl⟩

/-- **Exercise 13.D.2(b)** (MWG, p. 476). The insurance model: wealth `W`, loss `L`, loss
probabilities `p_L` (low risk, the safe type `true`) and `p_H` (high risk), `λ` the probability
of low risk, `h = u⁻¹`; `(e₁, e₂)` are the utility levels of the endowment (no insurance). -/
def insModel (W L pL pH lam : ℝ) (h : ℝ → ℝ) (e₁ e₂ : ℝ) : RSModel where
  qS := 1 - pL
  qR := 1 - pH
  a₁ := W
  a₂ := W - L
  h := h
  ρS := (1 - pL) * e₁ + pL * e₂
  ρR := (1 - pH) * e₁ + pH * e₂
  lam := lam

/-- In the insurance model the outside options satisfy the hypotheses of
`rs_characterization` (Jensen's inequality). -/
theorem ins_participation {W L pL pH lam : ℝ} {h : ℝ → ℝ} {e₁ e₂ vs : ℝ}
    (hM : (insModel W L pL pH lam h e₁ e₂).Valid) (he₁ : h e₁ = W) (he₂ : h e₂ = W - L)
    (hv : h vs = (insModel W L pL pH lam h e₁ e₂).abar false) :
    (insModel W L pL pH lam h e₁ e₂).ρR < vs ∧
      ∃ e : ℝ × ℝ, (insModel W L pL pH lam h e₁ e₂).V true e =
        (insModel W L pL pH lam h e₁ e₂).ρS ∧ 0 ≤ (insModel W L pL pH lam h e₁ e₂).Pr true e ∧
        (insModel W L pL pH lam h e₁ e₂).V false e < vs := by
  set N := insModel W L pL pH lam h e₁ e₂
  have hL : W - L < W := hM.a_lt
  have hne : e₁ ≠ e₂ := by
    intro he
    have : h e₁ = h e₂ := by rw [he]
    linarith
  have hPe : ∀ b, N.Pr b (e₁, e₂) = 0 := fun b => by
    simp only [N, Pr, insModel, he₁, he₂]; ring
  have hj := Pr_lt hM false (k := (e₁, e₂)) hne
  rw [hPe, ← hv] at hj
  have hv'' : N.h vs = N.abar false := hv
  have hlt : N.V false (e₁, e₂) < vs := hM.h_mono.lt_iff_lt.1 (by linarith)
  have hρR : N.ρR = N.V false (e₁, e₂) := by simp only [N, V, q_false, insModel]; ring
  refine ⟨hρR ▸ hlt, (e₁, e₂), ?_, (hPe true).ge, hlt⟩
  simp only [N, V, q_true, insModel]; ring

/-- **Exercise 13.D.2(b)** (MWG, p. 476). In every SPNE of the insurance game the high-risk type
buys full insurance at her fair premium (wealth `h v* = W - p_H L` in both states; the policy
`(p_H L, L)`), the low-risk type buys a policy that is fair for her, gives her strictly less
wealth in the loss state (partial insurance), and leaves the high-risk type indifferent
(`(1 - p_H) v₁ + p_H v₂ = v*`); both firms earn zero. -/
theorem exercise_13_D_2b {W L pL pH lam : ℝ} {h : ℝ → ℝ} {e₁ e₂ vs : ℝ}
    (hM : (insModel W L pL pH lam h e₁ e₂).Valid) (he₁ : h e₁ = W) (he₂ : h e₂ = W - L)
    (hv : h vs = W - pH * L) {A₁ A₂ : Finset (ℝ × ℝ)}
    (heq : (insModel W L pL pH lam h e₁ e₂).game.IsEq A₁ A₂) :
    ∃ kS, (insModel W L pL pH lam h e₁ e₂).game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧
      (insModel W L pL pH lam h e₁ e₂).game.Chooses true (A₁ ∪ A₂) kS ∧
      (policyWealth W L).symm (h vs, h vs) = (pH * L, L) ∧
      (1 - pL) * (W - h kS.1) + pL * (W - L - h kS.2) = 0 ∧
      (1 - pH) * kS.1 + pH * kS.2 = vs ∧ h kS.2 < h kS.1 ∧
      (insModel W L pL pH lam h e₁ e₂).game.profit A₁ A₂ = 0 ∧
      (insModel W L pL pH lam h e₁ e₂).game.profit A₂ A₁ = 0 := by
  have hv' : h vs = (insModel W L pL pH lam h e₁ e₂).abar false := by
    rw [hv]; simp only [abar, q_false, insModel]; ring
  obtain ⟨hR, hS⟩ := ins_participation hM he₁ he₂ hv'
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, hz1, hz2⟩ := rs_characterization hM hv' hR hS heq
  refine ⟨kS, hkR, hkS, ?_, ?_, ?_, hM.h_mono hlt, hz1, hz2⟩
  · simp only [policyWealth, Equiv.coe_fn_symm_mk, hv]; ext <;> simp only <;> ring
  · simp only [Pr, q_true, insModel] at hP; linarith
  · simp only [V, q_false, insModel] at hV; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476), existence: `W = 10`, `L = 8`, `p_L = 1/3`,
`p_H = 1/2`, `u = log`, `λ = 1/10`. Both firms offering the policies with wealth levels
`(6, 6)` (full insurance at premium `4`) and `(9, 4)` (premium `1`, coverage `3`) is an SPNE. -/
theorem exercise_13_D_2b_exists :
    (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.IsEq
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have h1 : Real.log 10 + Real.log 2 ≤ 2 * Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), two_mul,
      ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 : 2 * Real.log 10 + Real.log 2 ≤ 2 * Real.log 9 + Real.log 4 := by
    have a : 2 * Real.log 10 + Real.log 2 = Real.log (10 ^ 2 * 2) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have b : 2 * Real.log 9 + Real.log 4 = Real.log (9 ^ 2 * 4) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    rw [a, b]
    exact Real.log_le_log (by norm_num) (by norm_num)
  refine log_isEq _ (κ := 0) (by norm_num [insModel]) (by norm_num [insModel])
    (by norm_num [insModel]) (by norm_num [insModel]) (by funext v; simp [insModel])
    (by norm_num [insModel]) (by norm_num [insModel]) ?_ ?_
  · simp only [insModel]; linarith
  · simp only [insModel, V, q_true]; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476): an equilibrium need not exist. With the data of
`exercise_13_D_2b_exists` but `λ = 9/10` (mostly low risks), the pooling policy with wealth `7`
in both states attracts everybody at a profit, and no SPNE exists. -/
theorem exercise_13_D_2b_nonexistence :
    ¬ ∃ A₁ A₂, (insModel 10 8 (1 / 3) (1 / 2) (9 / 10) Real.exp (Real.log 10)
      (Real.log 2)).game.IsEq A₁ A₂ := by
  set N := insModel 10 8 (1 / 3) (1 / 2) (9 / 10) Real.exp (Real.log 10) (Real.log 2)
  have hN : N.Valid := log_valid N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel])
  have hv : Real.exp (Real.log 6) = N.abar false := by
    rw [Real.exp_log (by norm_num)]; simp only [N, abar, q_false, insModel]; norm_num
  obtain ⟨hR, hS⟩ := ins_participation (vs := Real.log 6) hN (Real.exp_log (by norm_num))
    (by rw [Real.exp_log (by norm_num)]; norm_num) hv
  exact log_no_eq N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) hR hS

/-- **Exercise 13.D.2(b)** (MWG, p. 476), the instance of `exercise_13_D_2b_exists`: in every
SPNE the high-risk type gets wealth `(6, 6)` and the low-risk type `(9, 4)`. -/
theorem exercise_13_D_2b_outcome {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10)
      (Real.log 2)).game.IsEq A₁ A₂) :
    (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.Chooses
        false (A₁ ∪ A₂) (Real.log 6, Real.log 6) ∧
      (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.Chooses
        true (A₁ ∪ A₂) (Real.log 9, Real.log 4) := by
  set N := insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)
  have hN : N.Valid := log_valid N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel])
  have hv : N.h (Real.log 6) = N.abar false := by
    simp only [N, insModel, abar, q_false]; rw [Real.exp_log (by norm_num)]; norm_num
  obtain ⟨hR, hS⟩ := ins_participation (vs := Real.log 6) hN (Real.exp_log (by norm_num))
    (by rw [Real.exp_log (by norm_num)]; norm_num) hv
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, -⟩ := rs_characterization hN hv hR hS h
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have he := rs_point_unique hN hv ⟨hP, hV, hlt⟩ (k' := (Real.log 9, Real.log 4))
    ⟨by simp only [N, insModel, Pr, q_true, e9, e4]; norm_num,
      by simp only [N, insModel, V, q_false]; linarith, log4_lt_log9⟩
  exact ⟨hkR, he ▸ hkS⟩

end RSModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.D.3: screening with observable output

MWG, Exercise 13.D.3, p. 476.

All workers perform the fixed task `T`; accepting employment has a type-independent monetary cost
`c > 0`; output is observable and contractible, so a contract is a wage schedule over output
levels, `k = (w_G, w_B)`: the wage after the good (or, in (a), the high type's) output and after
the bad (the low type's) output. A worker of type `b` obtains the good output with probability
`p_b`, and gets `p_b u(w_G - c) + (1 - p_b) u(w_B - c)` if she works, `u(0)` if she does not.

* (b) `rnGame` (risk neutral, `u(w) = w`); `exercise_13_D_3b`: in every SPNE both firms earn
  zero, a type whose expected output `ȳ_b` exceeds `c` works and gets exactly `ȳ_b - c` (she is
  paid her expected output), a type with `ȳ_b < c` does not work; `exercise_13_D_3b_exists`:
  both firms offering "pay the output" `(q_G, q_B)` is an SPNE. The full-information outcome
  obtains: output-contingent pay removes the adverse selection.
* (a) `exercise_13_D_3a`, `exercise_13_D_3a_exists`: deterministic output `θ(1 + μT)`, the case
  `p_H = 1`, `p_L = 0`: each type is paid her output `θ(1 + μT)` (if it exceeds `c`).
* (c) `labModel` (an `RSModel`: the high type is the "safe" type); `exercise_13_D_3c`: with
  strictly risk averse workers the low type receives the constant wage `p_L q_G + (1 - p_L) q_B`
  (full insurance at her expected output), the high type a wage schedule with `w_G > w_B` that
  breaks even on her and leaves the low type indifferent; instances with `u(x) = log(1 + x)`:
  `exercise_13_D_3c_exists` (`λ = 1/10`) and `exercise_13_D_3c_nonexistence` (`λ = 9/10`).

Departures: the cost enters as `u(w - c)` (a monetary cost); in (c) we assume `0 < p_L < p_H < 1`,
`q_B < q_G`, that the low type's expected output exceeds `c`, and that `u` maps onto `ℝ` from
its domain (as in Exercise 13.D.2); ties are broken in favour of the flatter wage schedule.
-/

namespace MWG.AdverseSelection

/-- The probability of the good output for type `b`. -/
def rnProb (pH pL : ℝ) (b : Bool) : ℝ := if b then pH else pL

/-- Expected output of type `b`. -/
def rnMean (pH pL qG qB : ℝ) (b : Bool) : ℝ := rnProb pH pL b * qG + (1 - rnProb pH pL b) * qB

/-- **Exercise 13.D.3(b)** (MWG, p. 476). The screening game with observable random output and
risk-neutral workers: contracts `(w_G, w_B)`, utility `E[w] - c`, profit `E[q - w]`. -/
noncomputable def rnGame (pH pL qG qB c lam : ℝ) : ScrGame where
  U b k := rnProb pH pL b * k.1 + (1 - rnProb pH pL b) * k.2 - c
  P b k := rnProb pH pL b * (qG - k.1) + (1 - rnProb pH pL b) * (qB - k.2)
  ρ _ := 0
  key k := k.1 - k.2
  lam := lam
  adm _ := True

namespace RnGame

variable {pH pL qG qB c lam : ℝ}

theorem inj (pH pL qG qB c lam : ℝ) : (rnGame pH pL qG qB c lam).Inj := by
  intro b k k' hu hk
  simp only [rnGame] at hu hk
  have h2 : k.2 = k'.2 := by
    have : rnProb pH pL b * (k.1 - k.2) = rnProb pH pL b * (k'.1 - k'.2) := by rw [hk]
    nlinarith
  exact Prod.ext (by linarith) h2

/-- Profit = expected output - cost - utility. -/
theorem P_eq (b : Bool) (k : ℝ × ℝ) :
    (rnGame pH pL qG qB c lam).P b k =
      rnMean pH pL qG qB b - c - (rnGame pH pL qG qB c lam).U b k := by
  simp only [rnGame, rnMean]; ring

theorem zero (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (rnGame pH pL qG qB c lam).IsEq A₁ A₂) :
    (rnGame pH pL qG qB c lam).profit A₁ A₂ = 0 ∧
      (rnGame pH pL qG qB c lam).profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (inj pH pL qG qB c lam) hl0 hl1 (fun δ k => (k.1 + δ, k.2 + δ))
    (fun _ _ _ _ => trivial) (fun δ b k => ?_) (fun δ k => ?_)
    (fun b k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => ?_⟩) h
  · simp only [rnGame]; ring
  · simp only [rnGame]; ring
  · simp only [rnGame]; ring_nf; linarith

end RnGame

/-- **Exercise 13.D.3(b)** (MWG, p. 476). With risk-neutral workers and observable output, in
every SPNE both firms earn zero, every type whose expected output exceeds `c` works and gets
utility `ȳ_b - c` (she is paid her expected output), and a type whose expected output is below
`c` does not work. -/
theorem exercise_13_D_3b {pH pL qG qB c lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : (rnGame pH pL qG qB c lam).IsEq A₁ A₂) :
    (rnGame pH pL qG qB c lam).profit A₁ A₂ = 0 ∧ (rnGame pH pL qG qB c lam).profit A₂ A₁ = 0 ∧
      (∀ b, c < rnMean pH pL qG qB b → ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k ∧
        (rnGame pH pL qG qB c lam).U b k = rnMean pH pL qG qB b - c) ∧
      ∀ b, rnMean pH pL qG qB b < c → ¬ ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k := by
  have hI := RnGame.inj pH pL qG qB c lam
  have hz := RnGame.zero hl0.le hl1.le h
  have hρ : ∀ b, (rnGame pH pL qG qB c lam).ρ b = 0 := fun _ => rfl
  -- "pay the output minus `ε`" attracts any type who gets less than `ȳ_b - c - ε`
  have dev : ∀ b ε, 0 < ε → 0 ≤ rnMean pH pL qG qB b - c - ε →
      (∀ k ∈ A₁ ∪ A₂, (rnGame pH pL qG qB c lam).U b k < rnMean pH pL qG qB b - c - ε) →
      False := by
    intro b ε hε h0 hlt
    have hU : ∀ b', (rnGame pH pL qG qB c lam).U b' (qG - ε, qB - ε) =
        rnMean pH pL qG qB b' - c - ε := fun b' => by simp only [rnGame, rnMean]; ring
    have hP : ∀ b', (rnGame pH pL qG qB c lam).P b' (qG - ε, qB - ε) = ε := fun b' => by
      simp only [rnGame]; ring
    cases b
    · exact ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (qG - ε, qB - ε)) trivial
        (by rw [hρ, hU]; exact h0)
        (fun k hk => by rw [hU]; exact hlt k (Finset.mem_union_right _ hk))
        (by rw [hP]; exact hε) (by rw [hP]; exact hε.le)
    · exact ScrGame.IsEq.dev_true_pos hI hl0 hl1.le h hz.1 (k' := (qG - ε, qB - ε)) trivial
        (by rw [hρ, hU]; exact h0)
        (fun k hk => by rw [hU]; exact hlt k (Finset.mem_union_right _ hk))
        (by rw [hP]; exact hε) (by rw [hP]; exact hε.le)
  have hA : ∀ b, c < rnMean pH pL qG qB b → ∃ k,
      (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k ∧
        rnMean pH pL qG qB b - c ≤ (rnGame pH pL qG qB c lam).U b k := by
    intro b hb
    obtain ⟨k, hk⟩ : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k := by
      by_contra hno
      refine dev b ((rnMean pH pL qG qB b - c) / 2) (by linarith) (by linarith) fun k hk => ?_
      by_contra hle
      exact hno (ScrGame.exists_chooses b ⟨k, hk, by rw [hρ]; linarith⟩)
    refine ⟨k, hk, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    refine dev b ((rnMean pH pL qG qB b - c - (rnGame pH pL qG qB c lam).U b k) / 2)
      (by linarith) (by linarith) fun k' hk' => ?_
    have := hk.2.2.1 k' hk'
    linarith
  have hB : ∀ b k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k →
      (rnGame pH pL qG qB c lam).P b k ≤ 0 := by
    intro b k hk
    rw [RnGame.P_eq]
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    rcases lt_or_ge c (rnMean pH pL qG qB b) with hb | hb
    · obtain ⟨k', hk', hge⟩ := hA b hb
      rw [ScrGame.chooses_unique hI hk hk']
      linarith
    · linarith
  -- each type's contribution to total profit is `≤ 0`, and the total is `0`
  have htot := ScrGame.profit_add (G := rnGame pH pL qG qB c lam) A₁ A₂
  rw [hz.1, hz.2] at htot
  have hlam : (rnGame pH pL qG qB c lam).lam = lam := rfl
  rw [hlam] at htot
  have hle : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b A₁ A₂ +
      (rnGame pH pL qG qB c lam).typeProfit b A₂ A₁ ≤ 0 := by
    intro b
    by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_add hI hk]; exact hB b k hk
    · rw [ScrGame.typeProfit_add_not hex]
  have hf := hle false
  have ht := hle true
  have hzero : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b A₁ A₂ +
      (rnGame pH pL qG qB c lam).typeProfit b A₂ A₁ = 0 := by
    intro b; cases b <;> nlinarith
  refine ⟨hz.1, hz.2, fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk, hge⟩ := hA b hb
    have := hzero b
    rw [ScrGame.typeProfit_add hI hk, RnGame.P_eq] at this
    exact ⟨k, hk, by linarith⟩
  · rintro ⟨k, hk⟩
    have := hzero b
    rw [ScrGame.typeProfit_add hI hk, RnGame.P_eq] at this
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    linarith

/-- **Exercise 13.D.3(b)** (MWG, p. 476), existence: both firms offering the contract that pays
the output, `(q_G, q_B)`, is an SPNE. -/
theorem exercise_13_D_3b_exists (pH pL qG qB c lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (rnGame pH pL qG qB c lam).IsEq {(qG, qB)} {(qG, qB)} := by
  have hI := RnGame.inj pH pL qG qB c lam
  have hP0 : ∀ b, (rnGame pH pL qG qB c lam).P b (qG, qB) = 0 := fun b => by
    simp only [rnGame]; ring
  have hle : ∀ b B, (rnGame pH pL qG qB c lam).typeProfit b B {(qG, qB)} ≤ 0 := by
    intro b B
    by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (B ∪ {(qG, qB)}) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk]
      have hge := hk.2.2.1 (qG, qB) (by simp)
      have hPk : (rnGame pH pL qG qB c lam).P b k ≤ 0 := by
        rw [RnGame.P_eq]
        have : (rnGame pH pL qG qB c lam).U b (qG, qB) = rnMean pH pL qG qB b - c := by
          simp only [rnGame, rnMean]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) hPk
    · rw [ScrGame.typeProfit_of_not hex]
  have hzero : (rnGame pH pL qG qB c lam).profit {(qG, qB)} {(qG, qB)} = 0 := by
    have : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b {(qG, qB)} {(qG, qB)} = 0 := by
      intro b
      by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b ({(qG, qB)} ∪ {(qG, qB)}) k
      · obtain ⟨k, hk⟩ := hex
        rw [ScrGame.typeProfit_of_chooses hI hk]
        have : k = (qG, qB) := by
          have := hk.1; rw [Finset.union_self] at this; exact Finset.mem_singleton.1 this
        rw [this, hP0, mul_zero]
      · exact ScrGame.typeProfit_of_not hex
    simp [ScrGame.profit, this]
  have hdev : ∀ B, (rnGame pH pL qG qB c lam).Menu B →
      (rnGame pH pL qG qB c lam).profit B {(qG, qB)} ≤
        (rnGame pH pL qG qB c lam).profit {(qG, qB)} {(qG, qB)} := by
    intro B _
    rw [hzero]
    unfold ScrGame.profit
    have hlam : (rnGame pH pL qG qB c lam).lam = lam := rfl
    rw [hlam]
    nlinarith [hle false B, hle true B]
  exact ⟨fun _ _ => trivial, fun _ _ => trivial, hdev, hdev⟩

/-- **Exercise 13.D.3(a)** (MWG, p. 476). Deterministic output: type `θ` produces `θ(1 + μT)` at
the fixed task `T`; a contract pays `w_H` after output `θ_H(1 + μT)` and `w_L` after
`θ_L(1 + μT)` (the case `p_H = 1`, `p_L = 0` of `rnGame`). In every SPNE firms earn zero and each
type whose output exceeds `c` works and is paid her output; a type whose output is below `c`
does not work. -/
theorem exercise_13_D_3a {M : SigModel} (hM : M.Valid) (μ T c : ℝ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).IsEq A₁ A₂) :
    (∀ b, c < M.θ b * (1 + μ * T) → ∃ k,
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).Chooses b (A₁ ∪ A₂) k ∧
        (if b then k.1 else k.2) = M.θ b * (1 + μ * T)) ∧
      (∀ b, M.θ b * (1 + μ * T) < c → ¬ ∃ k,
        (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).Chooses b (A₁ ∪ A₂) k) ∧
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).profit A₁ A₂ = 0 ∧
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).profit A₂ A₁ = 0 := by
  obtain ⟨hz1, hz2, hw, hn⟩ := exercise_13_D_3b hM.lam_pos hM.lam_lt h
  have hmean : ∀ b, rnMean 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) b =
      M.θ b * (1 + μ * T) := fun b => by
    cases b <;> simp [rnMean, rnProb, SigModel.θ]
  refine ⟨fun b hb => ?_, fun b hb => hn b (by rw [hmean]; exact hb), hz1, hz2⟩
  obtain ⟨k, hk, hu⟩ := hw b (by rw [hmean]; exact hb)
  refine ⟨k, hk, ?_⟩
  rw [hmean] at hu
  cases b <;> simp [rnGame, rnProb] at hu ⊢ <;> linarith

/-- **Exercise 13.D.3(a)** (MWG, p. 476), existence: paying each output level its value is an
SPNE. -/
theorem exercise_13_D_3a_exists {M : SigModel} (hM : M.Valid) (μ T c : ℝ) :
    (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).IsEq
      {(M.θH * (1 + μ * T), M.θL * (1 + μ * T))} {(M.θH * (1 + μ * T), M.θL * (1 + μ * T))} :=
  exercise_13_D_3b_exists _ _ _ _ _ _ hM.lam_pos.le hM.lam_lt.le

namespace RSModel

/-- **Exercise 13.D.3(c)** (MWG, p. 476). Risk-averse workers: the screening model in utility
coordinates `v_s = u(w_s - c)`, with the high type (`p_H`) as the safe type, endowment
`(q_G - c, q_B - c)`, and outside option `ρ₀ = u(0)`. -/
def labModel (pH pL qG qB c lam : ℝ) (h : ℝ → ℝ) (ρ0 : ℝ) : RSModel where
  qS := pH
  qR := pL
  a₁ := qG - c
  a₂ := qB - c
  h := h
  ρS := ρ0
  ρR := ρ0
  lam := lam

/-- In the labour model with `h ρ₀ = 0` (`ρ₀ = u(0)`) and `ȳ_L > c` the outside options satisfy
the hypotheses of `rs_characterization`. -/
theorem lab_participation {pH pL qG qB c lam : ℝ} {h : ℝ → ℝ} {ρ0 vs : ℝ}
    (hM : (labModel pH pL qG qB c lam h ρ0).Valid) (hρ0 : h ρ0 = 0)
    (hv : h vs = (labModel pH pL qG qB c lam h ρ0).abar false)
    (hpos : 0 < (labModel pH pL qG qB c lam h ρ0).abar false) :
    (labModel pH pL qG qB c lam h ρ0).ρR < vs ∧
      ∃ e : ℝ × ℝ, (labModel pH pL qG qB c lam h ρ0).V true e =
        (labModel pH pL qG qB c lam h ρ0).ρS ∧
        0 ≤ (labModel pH pL qG qB c lam h ρ0).Pr true e ∧
        (labModel pH pL qG qB c lam h ρ0).V false e < vs := by
  set N := labModel pH pL qG qB c lam h ρ0
  have hhρ : N.h ρ0 = 0 := hρ0
  have hhv : N.h vs = N.abar false := hv
  have hlt : ρ0 < vs := hM.h_mono.lt_iff_lt.1 (by rw [hhρ, hhv]; exact hpos)
  have hab := abar_lt hM
  refine ⟨hlt, (ρ0, ρ0), V_diag N true ρ0, ?_, by rw [V_diag]; exact hlt⟩
  rw [Pr_diag, hhρ]; linarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476). With strictly risk-averse workers, in every SPNE the
low-ability type receives the constant wage `h v* + c = p_L q_G + (1 - p_L) q_B` (her expected
output, full insurance), while the high-ability type receives a wage schedule `(w_G, w_B)`,
`w_G = h v₁ + c > w_B = h v₂ + c`, that breaks even on her and leaves the low-ability type
indifferent; both firms earn zero. -/
theorem exercise_13_D_3c {pH pL qG qB c lam : ℝ} {h : ℝ → ℝ} {ρ0 vs : ℝ}
    (hM : (labModel pH pL qG qB c lam h ρ0).Valid) (hρ0 : h ρ0 = 0)
    (hv : h vs + c = pL * qG + (1 - pL) * qB) (hpos : c < pL * qG + (1 - pL) * qB)
    {A₁ A₂ : Finset (ℝ × ℝ)} (heq : (labModel pH pL qG qB c lam h ρ0).game.IsEq A₁ A₂) :
    ∃ kS, (labModel pH pL qG qB c lam h ρ0).game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧
      (labModel pH pL qG qB c lam h ρ0).game.Chooses true (A₁ ∪ A₂) kS ∧
      pH * (qG - (h kS.1 + c)) + (1 - pH) * (qB - (h kS.2 + c)) = 0 ∧
      pL * kS.1 + (1 - pL) * kS.2 = vs ∧ h kS.2 + c < h kS.1 + c ∧
      (labModel pH pL qG qB c lam h ρ0).game.profit A₁ A₂ = 0 ∧
      (labModel pH pL qG qB c lam h ρ0).game.profit A₂ A₁ = 0 := by
  have hv' : h vs = (labModel pH pL qG qB c lam h ρ0).abar false := by
    simp only [abar, q_false, labModel]; linarith
  have hpos' : 0 < (labModel pH pL qG qB c lam h ρ0).abar false := by
    simp only [abar, q_false, labModel]; linarith
  obtain ⟨hR, hS⟩ := lab_participation hM hρ0 hv' hpos'
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, hz1, hz2⟩ := rs_characterization hM hv' hR hS heq
  refine ⟨kS, hkR, hkS, ?_, ?_, ?_, hz1, hz2⟩
  · simp only [Pr, q_true, labModel] at hP; linarith
  · simp only [V, q_false, labModel] at hV; linarith
  · have := hM.h_mono hlt
    change h kS.2 < h kS.1 at this
    linarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476), existence: `u(x) = log(1 + x)` (`h v = e^v - 1`),
`q_G = 10`, `q_B = 2`, `c = 1`, `p_H = 2/3`, `p_L = 1/2`, `λ = 1/10`: both firms offering the
constant wage `6` and the schedule `(10, 4)` (utility levels `(log 6, log 6)`, `(log 9, log 4)`)
is an SPNE. -/
theorem exercise_13_D_3c_exists :
    (labModel (2 / 3) (1 / 2) 10 2 1 (1 / 10) (fun v => Real.exp v - 1) 0).game.IsEq
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have l9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have l4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have l6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine log_isEq _ (κ := -1) (by norm_num [labModel]) (by norm_num [labModel])
    (by norm_num [labModel]) (by norm_num [labModel]) (by funext v; simp [labModel]; ring)
    (by norm_num [labModel]) (by norm_num [labModel]) ?_ ?_
  · simp only [labModel]; linarith
  · simp only [labModel, V, q_true]; nlinarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476): an equilibrium need not exist. With the data of
`exercise_13_D_3c_exists` but `λ = 9/10`, no SPNE exists. -/
theorem exercise_13_D_3c_nonexistence :
    ¬ ∃ A₁ A₂, (labModel (2 / 3) (1 / 2) 10 2 1 (9 / 10) (fun v => Real.exp v - 1) 0).game.IsEq
      A₁ A₂ := by
  set N := labModel (2 / 3) (1 / 2) 10 2 1 (9 / 10) (fun v => Real.exp v - 1) 0
  have hN : N.Valid := log_valid N (κ := -1) (by norm_num [N, labModel])
    (by norm_num [N, labModel]) (by norm_num [N, labModel]) (by norm_num [N, labModel])
    (by funext v; simp [N, labModel]; ring) (by norm_num [N, labModel]) (by norm_num [N, labModel])
  have hv : N.h (Real.log 6) = N.abar false := by
    simp only [N, labModel, abar, q_false]; rw [Real.exp_log (by norm_num)]; norm_num
  obtain ⟨hR, hS⟩ := lab_participation (vs := Real.log 6) hN (by simp) hv
    (by simp only [labModel, abar, q_false]; norm_num)
  exact log_no_eq N (κ := -1) (by norm_num [N, labModel]) (by norm_num [N, labModel])
    (by norm_num [N, labModel]) (by norm_num [N, labModel]) (by funext v; simp [N, labModel]; ring)
    (by norm_num [N, labModel]) hR hS

end RSModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.D.4: screening with free entry and single-contract firms

MWG, Exercise 13.D.4, p. 476 (the model of Section 13.D, pp. 460-466).

Infinitely many potential firms `i : ℕ`; each offers at most one contract (`s i = some k`) or
stays out (`s i = none`); finitely many are active. Workers choose from the set of offered
contracts with the book's rules (`ChoosesS`), and the firms offering a contract share equally the
workers who choose it. A firm's profit is `feProfit`; `IsFreeEntryEq` is the pure SPNE: no firm,
active or not, gains by changing its offer (in particular no entrant can make a profit:
`IsFreeEntryEq.no_entry`).

* `exercise_13_D_4`: in every free-entry equilibrium the low type takes `(θ_L, 0)` and the high
  type `(θ_H, t̂_H)` (as in Proposition 13.D.2); in particular there is no pooling.
* `fe_exists`: if no single contract that both types weakly prefer to these contracts has a wage
  below `E[θ]`, the profile in which firms `0, 1` offer `(θ_L, 0)` and firms `2, 3` offer
  `(θ_H, t̂_H)` is a free-entry equilibrium (each contract must be offered by at least two
  firms: a lone firm would lower its wage).
* `fe_no_eq_of_pooling`: a pooling contract that both types strictly prefer, with wage below
  `E[θ]`, rules out equilibrium (Figure 13.D.7(b)): `exercise_13_D_4_nonexistence`
  (`screenModel (3/4)`).
* The pair deviation of Figure 13.D.8 is not available to a single-contract entrant:
  `exercise_13_D_4_pair` shows that in `screenModel (2/5)`, where the two-firm game with finite
  menus has no SPNE (`nonexistence_pair_instance`), a free-entry equilibrium exists. Thus only
  the pooling form of nonexistence survives. `exercise_13_D_4_lin`: an equilibrium in `linModel`.
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- **Exercise 13.D.4** (MWG, p. 476). The set of contracts offered in the profile `s`. -/
def offered (s : ℕ → Option (ℝ × ℝ)) : Set (ℝ × ℝ) := {k | ∃ i, s i = some k}

/-- **Exercise 13.D.4** (MWG, p. 476). Type `θ` chooses `k` from the set `O` of offered
contracts (the rules of `Chooses`). -/
def ChoosesS (M : SigModel) (θ : ℝ) (O : Set (ℝ × ℝ)) (k : ℝ × ℝ) : Prop :=
  k ∈ O ∧ 0 ≤ M.util θ k ∧ (∀ k' ∈ O, M.util θ k' ≤ M.util θ k) ∧
    ∀ k' ∈ O, M.util θ k' = M.util θ k → k.2 ≤ k'.2

open Classical in
/-- The expected profit generated by contract `k` when `O` is offered (before sharing). -/
noncomputable def gross (M : SigModel) (O : Set (ℝ × ℝ)) (k : ℝ × ℝ) : ℝ :=
  (1 - M.lam) * (if M.ChoosesS M.θL O k then M.θL - k.1 else 0) +
    M.lam * (if M.ChoosesS M.θH O k then M.θH - k.1 else 0)

/-- **Exercise 13.D.4** (MWG, p. 476). Firm `i`'s profit: its contract's profit shared equally
among the firms offering it. -/
noncomputable def feProfit (M : SigModel) (s : ℕ → Option (ℝ × ℝ)) (i : ℕ) : ℝ :=
  match s i with
  | none => 0
  | some k => M.gross (offered s) k / ({j | s j = some k}.ncard : ℝ)

/-- **Exercise 13.D.4** (MWG, p. 476). A pure SPNE of the free-entry game: finitely many active
firms, contracts with `t ≥ 0`, and no firm gains by changing its offer. -/
def IsFreeEntryEq (M : SigModel) (s : ℕ → Option (ℝ × ℝ)) : Prop :=
  {i | s i ≠ none}.Finite ∧ (∀ i k, s i = some k → 0 ≤ k.2) ∧
    ∀ i (o : Option (ℝ × ℝ)), (∀ k, o = some k → 0 ≤ k.2) →
      M.feProfit (Function.update s i o) i ≤ M.feProfit s i

theorem choosesS_unique {θ : ℝ} {O : Set (ℝ × ℝ)} {k k' : ℝ × ℝ} (h : M.ChoosesS θ O k)
    (h' : M.ChoosesS θ O k') : k = k' := by
  have hu : M.util θ k = M.util θ k' := le_antisymm (h'.2.2.1 k h.1) (h.2.2.1 k' h'.1)
  have ht : k.2 = k'.2 := le_antisymm (h.2.2.2 k' h'.1 hu.symm) (h'.2.2.2 k h.1 hu)
  have hw : k.1 = k'.1 := by unfold util at hu; rw [ht] at hu; linarith
  exact Prod.ext hw ht

theorem exists_choosesS (θ : ℝ) {O : Set (ℝ × ℝ)} (hO : O.Finite)
    (h : ∃ k ∈ O, 0 ≤ M.util θ k) : ∃ k, M.ChoosesS θ O k := by
  obtain ⟨k0, hk0, hu0⟩ := h
  obtain ⟨k, hk⟩ := exists_chooses (M := M) θ (U := hO.toFinset)
    ⟨k0, (Set.Finite.mem_toFinset hO).2 hk0, hu0⟩
  refine ⟨k, (Set.Finite.mem_toFinset hO).1 hk.1, hk.2.1, fun k' hk' => hk.2.2.1 k'
    ((Set.Finite.mem_toFinset hO).2 hk'),
    fun k' hk' => hk.2.2.2 k' ((Set.Finite.mem_toFinset hO).2 hk')⟩

theorem choosesS_of_strict {θ : ℝ} {O : Set (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ O)
    (h0 : 0 ≤ M.util θ k) (hs : ∀ k' ∈ O, k' ≠ k → M.util θ k' < M.util θ k) :
    M.ChoosesS θ O k := by
  refine ⟨hk, h0, fun k' hk' => ?_, fun k' hk' he => ?_⟩
  · by_cases h : k' = k
    · rw [h]
    · exact (hs k' hk' h).le
  · by_cases h : k' = k
    · rw [h]
    · exact absurd he (hs k' hk' h).ne

theorem offered_finite {s : ℕ → Option (ℝ × ℝ)} (hf : {i | s i ≠ none}.Finite) :
    (offered s).Finite := by
  refine (hf.image fun i => (s i).getD 0).subset fun k ⟨i, hi⟩ => ⟨i, ?_, ?_⟩
  · simp [hi]
  · simp [hi]

theorem offered_update_none {s : ℕ → Option (ℝ × ℝ)} {i : ℕ} (hi : s i = none) (k' : ℝ × ℝ) :
    offered (Function.update s i (some k')) = insert k' (offered s) := by
  ext k
  simp only [offered, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji; rw [Function.update_self] at hj; exact Or.inl (Option.some.inj hj).symm
    · rw [Function.update_of_ne hji] at hj; exact Or.inr ⟨j, hj⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨i, Function.update_self _ _ _⟩
    · have hji : j ≠ i := fun h => by rw [h, hi] at hj; exact absurd hj (by simp)
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

/-- The number of firms offering `k` is positive when firm `i` offers it. -/
theorem ncard_pos_of {s : ℕ → Option (ℝ × ℝ)} (hf : {i | s i ≠ none}.Finite) {i : ℕ}
    {k : ℝ × ℝ} (hi : s i = some k) : (0 : ℝ) < ({j | s j = some k}.ncard : ℝ) := by
  have hfin : {j | s j = some k}.Finite :=
    hf.subset fun j hj => by simp only [Set.mem_ofPred_eq] at hj ⊢; rw [hj]; simp
  exact_mod_cast (Set.ncard_pos hfin).2 ⟨i, hi⟩

theorem update_finite {s : ℕ → Option (ℝ × ℝ)} (hf : {i | s i ≠ none}.Finite) (i : ℕ)
    (o : Option (ℝ × ℝ)) : {j | Function.update s i o j ≠ none}.Finite := by
  refine (hf.insert i).subset fun j hj => ?_
  by_cases hji : j = i
  · exact Or.inl hji
  · simp only [Set.mem_ofPred_eq] at hj
    rw [Function.update_of_ne hji] at hj
    exact Or.inr hj

/-- **Exercise 13.D.4** (MWG, p. 476): in an equilibrium no entrant can make a profit. -/
theorem IsFreeEntryEq.no_entry {s : ℕ → Option (ℝ × ℝ)} (h : M.IsFreeEntryEq s) {k' : ℝ × ℝ}
    (hk' : 0 ≤ k'.2) : M.gross (insert k' (offered s)) k' ≤ 0 := by
  obtain ⟨i, hi⟩ := h.1.exists_notMem
  have hin : s i = none := by simpa using hi
  have := h.2.2 i (some k') (fun k hk => by rw [Option.some.inj hk.symm]; exact hk')
  have hn := ncard_pos_of (update_finite h.1 i (some k'))
    (by simp : Function.update s i (some k') i = some k')
  simp only [feProfit, Function.update_self, offered_update_none hin, hin] at this
  by_contra hpos
  exact absurd this (not_le.2 (div_pos (not_le.1 hpos) hn))

/-- In an equilibrium an active firm's contract makes a nonnegative profit. -/
theorem IsFreeEntryEq.active_nonneg {s : ℕ → Option (ℝ × ℝ)} (h : M.IsFreeEntryEq s) {i : ℕ}
    {k : ℝ × ℝ} (hi : s i = some k) : 0 ≤ M.gross (offered s) k := by
  have := h.2.2 i none (fun _ hk => by simp at hk)
  have hn := ncard_pos_of h.1 hi
  simp only [feProfit, Function.update_self, hi] at this
  by_contra hneg
  exact absurd this (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hneg) hn))

/-- **Exercise 13.D.4** (MWG, p. 476). In every equilibrium of the free-entry game with
single-contract firms the low type takes `(θ_L, 0)` and the high type `(θ_H, t̂_H)`, where
`θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`: the outcome of Proposition 13.D.2 (no pooling). -/
theorem exercise_13_D_4 (hM : M.Valid) {s : ℕ → Option (ℝ × ℝ)} (h : M.IsFreeEntryEq s)
    {th : ℝ} (hth : 0 ≤ th) (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) :
    M.ChoosesS M.θL (offered s) (M.θL, 0) ∧ M.ChoosesS M.θH (offered s) (M.θH, th) := by
  have hO := offered_finite h.1
  have hval : ∀ k ∈ offered s, 0 ≤ k.2 := fun k ⟨i, hi⟩ => h.2.1 i k hi
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  rw [hM.c_zero, sub_zero] at hcth
  -- an entrant attracting a type strictly with a positive profit on her
  have entry_pos : ∀ k' : ℝ × ℝ, 0 ≤ k'.2 → 0 < M.gross (insert k' (offered s)) k' → False :=
    fun k' hk' hpos => absurd (h.no_entry hk') (not_le.2 hpos)
  have strict_choice : ∀ θ (k' : ℝ × ℝ), 0 ≤ M.util θ k' →
      (∀ k ∈ offered s, M.util θ k < M.util θ k') → M.ChoosesS θ (insert k' (offered s)) k' := by
    intro θ k' h0 hs
    refine choosesS_of_strict (Set.mem_insert _ _) h0 fun k hk hne => ?_
    rcases hk with rfl | hk
    · exact absurd rfl hne
    · exact hs k hk
  have not_choice : ∀ θ (k' k0 : ℝ × ℝ), k0 ∈ offered s → M.util θ k' < M.util θ k0 →
      ¬ M.ChoosesS θ (insert k' (offered s)) k' := fun θ k' k0 hk0 hlt hch =>
    absurd (hch.2.2.1 k0 (Set.mem_insert_of_mem _ hk0)) (not_le.2 hlt)
  -- the low type
  have devL : ∀ w, 0 ≤ w → w < M.θL → (∀ k ∈ offered s, M.util M.θL k < w) → False := by
    intro w hw0 hw hlt
    have hu : ∀ θ, M.util θ (w, 0) = w := fun θ => by simp [util, hM.c_zero]
    have hch := strict_choice M.θL (w, 0) (by rw [hu]; exact hw0)
      (fun k hk => by rw [hu]; exact hlt k hk)
    refine entry_pos (w, 0) le_rfl ?_
    unfold gross
    simp only [hch, ↓reduceIte]
    split_ifs <;> nlinarith
  obtain ⟨kL, hkL⟩ : ∃ kL, M.ChoosesS M.θL (offered s) kL := by
    by_contra hno
    refine devL (M.θL / 2) (by linarith) (by linarith) fun k hk => ?_
    by_contra hle
    exact hno (exists_choosesS M.θL hO ⟨k, hk, by linarith⟩)
  have hLv := hval kL hkL.1
  have hLge : M.θL ≤ M.util M.θL kL := by
    by_contra hlt
    rw [not_le] at hlt
    refine devL ((M.util M.θL kL + M.θL) / 2) (by linarith [hkL.2.1]) (by linarith)
      fun k hk => ?_
    have := hkL.2.2.1 k hk
    linarith
  -- the high type works
  obtain ⟨kH, hkH⟩ : ∃ kH, M.ChoosesS M.θH (offered s) kH := by
    refine exists_choosesS M.θH hO ⟨kL, hkL.1, ?_⟩
    have := hM.c_le hLv
    simp only [util] at hLge ⊢
    linarith
  have hHv := hval kH hkH.1
  -- no profit on the high type
  have hwH : M.θH ≤ kH.1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hHv (sub_pos.2 hlt)
    have hch := strict_choice M.θH k' (hkH.2.1.trans hH.le)
      (fun k hk => (hkH.2.2.1 k hk).trans_lt hH)
    have hno := not_choice M.θL k' kL hkL.1 (hL.trans_le (hkL.2.2.1 kH hkH.1))
    refine entry_pos k' hk'0 ?_
    unfold gross
    simp only [hch, hno, ↓reduceIte]
    nlinarith
  -- the active firms' contracts
  obtain ⟨iL, hiL⟩ := hkL.1
  obtain ⟨iH, hiH⟩ := hkH.1
  have hgL := h.active_nonneg hiL
  have hgH := h.active_nonneg hiH
  have hcL : 0 ≤ M.c kL.2 M.θL := by have := hM.c_nonneg false hLv; rwa [θ_false] at this
  have hne : kL ≠ kH := by
    intro he
    rw [← he] at hkH hwH
    unfold gross at hgL
    simp only [hkL, hkH, ↓reduceIte] at hgL
    simp only [util] at hLge
    nlinarith
  have hHnL : ¬ M.ChoosesS M.θH (offered s) kL := fun hc => hne (choosesS_unique hc hkH)
  have hLnH : ¬ M.ChoosesS M.θL (offered s) kH := fun hc => hne (choosesS_unique hkL hc)
  unfold gross at hgL hgH
  simp only [hkL, hHnL, hkH, hLnH, ↓reduceIte, mul_zero, add_zero, zero_add] at hgL hgH
  have hwL : kL.1 = M.θL := by
    simp only [util] at hLge
    nlinarith
  have htL : kL.2 = 0 := by
    by_contra hne0
    have hpos := hM.c_pos false (lt_of_le_of_ne hLv (Ne.symm hne0))
    simp only [θ_false] at hpos
    simp only [util] at hLge
    linarith
  have hwH' : kH.1 = M.θH := by nlinarith
  have hkL' : kL = (M.θL, 0) := Prod.ext hwL htL
  -- the high type's task level
  have hge : th ≤ kH.2 := by
    have := hkL.2.2.1 kH hkH.1
    simp only [util, hkL', hM.c_zero, sub_zero, hwH'] at this
    exact ((hM.c_mono false).le_iff_le hth hHv).1 (by simp only [θ_false]; linarith)
  have hkH' : kH = (M.θH, th) := by
    refine Prod.ext hwH' (le_antisymm ?_ hge)
    by_contra hlt
    rw [not_le] at hlt
    set t' := (th + kH.2) / 2
    have ht1 : th < t' := by simp only [t']; linarith
    have ht2 : t' < kH.2 := by simp only [t']; linarith
    have hcH := hM.c_mono true (hth.trans ht1.le) hHv ht2
    have hcL' := hM.c_mono false hth (hth.trans ht1.le) ht1
    simp only [θ_true, θ_false] at hcH hcL'
    set η := (M.c kH.2 M.θH - M.c t' M.θH) / 2
    have hη : 0 < η := by simp only [η]; linarith
    have hH' : M.util M.θH kH < M.util M.θH (M.θH - η, t') := by
      simp only [util, hwH', η]; linarith
    have hL' : M.util M.θL (M.θH - η, t') < M.util M.θL kL := by
      simp only [util, hkL', hM.c_zero]; linarith
    have hch := strict_choice M.θH (M.θH - η, t') (hkH.2.1.trans hH'.le)
      (fun k hk => (hkH.2.2.1 k hk).trans_lt hH')
    have hno := not_choice M.θL (M.θH - η, t') kL hkL.1 hL'
    refine entry_pos (M.θH - η, t') (hth.trans ht1.le) ?_
    unfold gross
    simp only [hch, hno, ↓reduceIte]
    nlinarith
  exact ⟨hkL' ▸ hkL, hkH' ▸ hkH⟩

/-- **Exercise 13.D.4** (MWG, p. 476), nonexistence: if a pooling contract `p` that both types
strictly prefer to `(θ_L, 0)` and `(θ_H, t̂_H)` has a wage below `E[θ]`, there is no
free-entry equilibrium. -/
theorem fe_no_eq_of_pooling (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) {p : ℝ × ℝ} (hp : 0 ≤ p.2)
    (hL : M.θL < M.util M.θL p) (hH : M.θH - M.c th M.θH < M.util M.θH p) (hw : p.1 < M.Eθ) :
    ¬ ∃ s, M.IsFreeEntryEq s := by
  rintro ⟨s, h⟩
  obtain ⟨hcL, hcH⟩ := exercise_13_D_4 hM h hth hcth
  have hθL := hM.θL_pos
  have hc : ∀ θ (k0 : ℝ × ℝ), M.ChoosesS θ (offered s) k0 → M.util θ k0 < M.util θ p →
      M.ChoosesS θ (insert p (offered s)) p := by
    intro θ k0 hk0 hlt
    refine choosesS_of_strict (Set.mem_insert _ _) (hk0.2.1.trans hlt.le) fun k hk hne => ?_
    rcases hk with rfl | hk
    · exact absurd rfl hne
    · exact (hk0.2.2.1 k hk).trans_lt hlt
  have h1 := hc M.θL _ hcL (by simp only [util, hM.c_zero, sub_zero]; exact hL)
  have h2 := hc M.θH _ hcH (by simp only [util]; exact hH)
  have := h.no_entry hp
  unfold gross at this
  simp only [h1, h2, ↓reduceIte] at this
  unfold Eθ at hw
  linarith

/-- **Exercise 13.D.4** (MWG, p. 476). The profile in which firms `0, 1` offer `(θ_L, 0)`,
firms `2, 3` offer `(θ_H, t̂_H)` and all other firms stay out. -/
def feProfile (M : SigModel) (th : ℝ) : ℕ → Option (ℝ × ℝ) :=
  fun i => if i < 2 then some (M.θL, 0) else if i < 4 then some (M.θH, th) else none

/-- **Exercise 13.D.4** (MWG, p. 476), existence: if every contract `(w, t)` that both types
weakly prefer to their Proposition 13.D.2 contracts has `w ≥ E[θ]` (no profitable pooling
entry), `feProfile` is a free-entry equilibrium. -/
theorem fe_exists (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL)
    (hNP : ∀ w t, 0 ≤ t → M.θH - M.c th M.θH ≤ w - M.c t M.θH → M.θL ≤ w - M.c t M.θL →
      M.Eθ ≤ w) :
    M.IsFreeEntryEq (M.feProfile th) := by
  rw [hM.c_zero, sub_zero] at hcth
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  set kL : ℝ × ℝ := (M.θL, 0)
  set kH : ℝ × ℝ := (M.θH, th)
  set s := M.feProfile th with hs
  have hthpos : 0 < th := by
    rcases eq_or_lt_of_le hth with h0 | h0
    · rw [← h0, hM.c_zero] at hcth; linarith
    · exact h0
  have hcHL := hM.c_lt_of_pos hthpos
  have hne : kL ≠ kH := fun he => by
    have := congrArg Prod.fst he; simp only [kL, kH] at this; linarith
  have huLL : M.util M.θL kL = M.θL := by simp [kL, util, hM.c_zero]
  have huLH : M.util M.θL kH = M.θL := by simp only [kH, util]; linarith
  have huHL : M.util M.θH kL = M.θL := by simp [kL, util, hM.c_zero]
  have huHH : M.util M.θH kH = M.θH - M.c th M.θH := rfl
  have hHgt : M.θL < M.θH - M.c th M.θH := by linarith
  have hsv : ∀ i, s i = none ∨ s i = some kL ∨ s i = some kH := by
    intro i
    simp only [hs, feProfile]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  -- the offered set after any change of firm `i`'s offer
  have hoff : ∀ i o, kL ∈ offered (Function.update s i o) ∧
      kH ∈ offered (Function.update s i o) ∧
      ∀ k ∈ offered (Function.update s i o), k = kL ∨ k = kH ∨ o = some k := by
    intro i o
    refine ⟨⟨if i = 0 then 1 else 0, ?_⟩, ⟨if i = 2 then 3 else 2, ?_⟩, fun k ⟨j, hj⟩ => ?_⟩
    · split_ifs with h0
      · rw [Function.update_of_ne (by omega)]; simp [hs, feProfile, kL]
      · rw [Function.update_of_ne (by omega)]; simp [hs, feProfile, kL]
    · split_ifs with h0
      · rw [Function.update_of_ne (by omega)]; simp [hs, feProfile, kH]
      · rw [Function.update_of_ne (by omega)]; simp [hs, feProfile, kH]
    · by_cases hji : j = i
      · subst hji; rw [Function.update_self] at hj; exact Or.inr (Or.inr hj)
      · rw [Function.update_of_ne hji] at hj
        rcases hsv j with h0 | h0 | h0 <;> rw [h0] at hj
        · exact absurd hj (by simp)
        · exact Or.inl (Option.some.inj hj).symm
        · exact Or.inr (Or.inl (Option.some.inj hj).symm)
  have hoff0 : ∀ k ∈ offered s, k = kL ∨ k = kH := by
    intro k ⟨j, hj⟩
    rcases hsv j with h0 | h0 | h0 <;> rw [h0] at hj
    · exact absurd hj (by simp)
    · exact Or.inl (Option.some.inj hj).symm
    · exact Or.inr (Option.some.inj hj).symm
  have hmemL : kL ∈ offered s := ⟨0, by simp [hs, feProfile, kL]⟩
  have hmemH : kH ∈ offered s := ⟨2, by simp [hs, feProfile, kH]⟩
  -- the equilibrium choices
  have hchL : M.ChoosesS M.θL (offered s) kL := by
    refine ⟨hmemL, by rw [huLL]; exact hθL.le, fun k hk => ?_, fun k hk _ => ?_⟩
    · rcases hoff0 k hk with rfl | rfl
      · exact le_rfl
      · rw [huLH, huLL]
    · rcases hoff0 k hk with rfl | rfl
      · exact le_rfl
      · exact hth
  have hchH : M.ChoosesS M.θH (offered s) kH := by
    refine choosesS_of_strict hmemH (by linarith) fun k hk hne' => ?_
    rcases hoff0 k hk with rfl | rfl
    · rw [huHL, huHH]; exact hHgt
    · exact absurd rfl hne'
  have hnHL : ¬ M.ChoosesS M.θH (offered s) kL := fun hc => hne (choosesS_unique hc hchH)
  have hnLH : ¬ M.ChoosesS M.θL (offered s) kH := fun hc => hne (choosesS_unique hchL hc)
  have hzero : ∀ i, M.feProfit s i = 0 := by
    intro i
    rcases hsv i with h0 | h0 | h0
    · simp [feProfit, h0]
    · simp only [feProfit, h0]
      unfold gross
      simp [hchL, hnHL, kL]
    · simp only [feProfit, h0]
      unfold gross
      simp [hchH, hnLH, kH]
  -- a deviation never makes a profit
  have hdev : ∀ i (k' : ℝ × ℝ), 0 ≤ k'.2 →
      M.gross (offered (Function.update s i (some k'))) k' ≤ 0 := by
    intro i k' hk'
    obtain ⟨hL', hH', hsub⟩ := hoff i (some k')
    set O := offered (Function.update s i (some k'))
    have hk'O : k' ∈ O := ⟨i, Function.update_self _ _ _⟩
    have hcL' : 0 ≤ M.c k'.2 M.θL := by have := hM.c_nonneg false hk'; rwa [θ_false] at this
    unfold gross
    split_ifs with hcL hcH hcH
    · -- both choose `k'`
      have hgeL := hcL.2.2.1 kL hL'
      have hgeH := hcH.2.2.1 kH hH'
      rw [huLL] at hgeL
      rw [huHH] at hgeH
      have := hNP k'.1 k'.2 hk' hgeH (by simp only [util] at hgeL; linarith)
      unfold Eθ at this
      nlinarith
    · have hgeL := hcL.2.2.1 kL hL'
      rw [huLL] at hgeL
      simp only [util] at hgeL
      nlinarith
    · -- only the high type chooses `k'`: then `w' ≥ θ_H`
      have hgeH := hcH.2.2.1 kH hH'
      rw [huHH] at hgeH
      simp only [util] at hgeH
      by_contra hpos
      rw [not_le, mul_zero, zero_add] at hpos
      have hw : k'.1 < M.θH := by nlinarith
      have hlt : k'.2 < th := by
        by_contra hle
        rw [not_lt] at hle
        have := (hM.c_mono true).le_iff_le hth hk'
        simp only [θ_true] at this
        linarith [this.2 hle]
      have hsc := hM.sc k'.2 th hk' hlt
      have hLk : M.θL < M.util M.θL k' := by simp only [util]; linarith
      refine hcL (choosesS_of_strict hk'O (by linarith) fun k hk hne' => ?_)
      rcases hsub k hk with rfl | rfl | hk
      · rw [huLL]; exact hLk
      · rw [huLH]; exact hLk
      · exact absurd (Option.some.inj hk).symm hne'
    · simp
  refine ⟨(Set.finite_Iio 4).subset fun i hi => ?_, fun i k hk => ?_, fun i o ho => ?_⟩
  · simp only [Set.mem_ofPred_eq, hs, feProfile] at hi
    simp only [Set.mem_Iio]
    by_contra h4
    exact hi (by split_ifs <;> first | omega | rfl)
  · rcases hsv i with h0 | h0 | h0 <;> rw [h0] at hk
    · exact absurd hk (by simp)
    · rw [← Option.some.inj hk]
    · rw [← Option.some.inj hk]; exact hth
  · rw [hzero]
    cases o with
    | none => simp [feProfit]
    | some k' =>
      simp only [feProfit, Function.update_self]
      exact div_nonpos_of_nonpos_of_nonneg (hdev i k' (ho k' rfl)) (Nat.cast_nonneg _)

/-- **Exercise 13.D.4** (MWG, p. 476), an instance: in `linModel` the profile `feProfile 1`
(contracts `(1, 0)` and `(2, 1)`) is a free-entry equilibrium. -/
theorem exercise_13_D_4_lin : linModel.IsFreeEntryEq (linModel.feProfile 1) := by
  refine fe_exists linModel_valid zero_le_one ?_ fun w t ht hH _ => ?_
  · rw [linModel_cL, linModel_valid.c_zero]; norm_num [linModel]
  · rw [linModel_cH, linModel_cH] at hH
    simp only [linModel, Eθ] at hH ⊢
    linarith

/-- **Exercise 13.D.4** (MWG, p. 476): the nonexistence of Figure 13.D.8 does not carry over. In
`screenModel (2/5)` the two-firm game with finite menus has no SPNE (a pair of contracts breaks
the separating outcome), but with single-contract firms `feProfile 1` is a free-entry
equilibrium. -/
theorem exercise_13_D_4_pair :
    (¬ ∃ A₁ A₂, (screenModel (2 / 5)).IsScreenEq A₁ A₂) ∧
      (screenModel (2 / 5)).IsFreeEntryEq ((screenModel (2 / 5)).feProfile 1) := by
  have hv := screenModel_valid (l := 2 / 5) (by norm_num) (by norm_num)
  refine ⟨nonexistence_pair_instance.2, fe_exists hv zero_le_one ?_ fun w t ht hH _ => ?_⟩
  · rw [screenModel_cL, hv.c_zero]; norm_num [screenModel, crossModel]
  · rw [screenModel_cH, screenModel_cH] at hH
    have : 0 ≤ t ^ 2 / (1 + t) := by positivity
    simp only [screenModel, crossModel, Eθ] at hH ⊢
    norm_num at hH ⊢
    linarith

/-- **Exercise 13.D.4** (MWG, p. 476): nonexistence survives in its pooling form. In
`screenModel (3/4)` the pooling contract `(8/5, 0)` rules out every free-entry equilibrium. -/
theorem exercise_13_D_4_nonexistence :
    ¬ ∃ s, (screenModel (3 / 4)).IsFreeEntryEq s := by
  have hv := screenModel_valid (l := 3 / 4) (by norm_num) (by norm_num)
  refine fe_no_eq_of_pooling hv (th := 1) zero_le_one ?_ (p := (8 / 5, 0)) le_rfl ?_ ?_ ?_
  all_goals simp [screenModel, crossModel, util, Eθ]
  all_goals norm_num

end SigModel

end MWG.AdverseSelection

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 13.AA.1: three types, several PBE satisfying the intuitive criterion

MWG, Exercise 13.AA.1, p. 476 (Appendix A, pp. 467-472).

The education signaling model of Section 13.C with three equally likely types (`Fin 3`) of
productivity `θ = (1, 2, 10)`, `r(θ) = 0`, and education cost `c(e, θ) = k_θ e` with
`k = (1, 1/2, 1/4)` (single crossing). It is the `SignalingGame` `aaGame` of Appendix A: the
worker chooses `e ≥ 0` (`NNReal`); two firms observe `e` and bid wages; the worker accepts the
highest bid if it is nonnegative (ties split); a firm's payoff is its share of `θ - w`. The firms'
response game after `e` with belief `μ` is the wage game of Section 13.B with expected
productivity `E_μ[θ]` (`aa_payoff`), so its Nash equilibria are both firms bidding `E_μ[θ]`
(`aa_nash_iff`).

* `aa_pbe1`: the separating (Riley) PBE: education `(0, 1, 17)`, wages `(1, 2, 10)`, payoffs
  `(1, 3/2, 23/4)`;
* `aa_pbe2`: a partially pooling PBE: types 1 and 2 choose `e = 0` (wage `3/2`), type 3
  chooses `17`; payoffs `(3/2, 3/2, 23/4)`;
* `aa_passes_ic`: both satisfy the intuitive criterion (13.AA.4);
* `exercise_13_AA_1`: the two PBE have different outcomes, so more than one PBE satisfies the
  intuitive criterion.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- Productivities `θ = (1, 2, 10)`. -/
def aaθ : Fin 3 → ℝ := ![1, 2, 10]

/-- Marginal education costs `k_θ = (1, 1/2, 1/4)`. -/
noncomputable def aaK : Fin 3 → ℝ := ![1, 1 / 2, 1 / 4]

/-- **Exercise 13.AA.1** (MWG, p. 476). The three-type education signaling game. -/
noncomputable def aaGame : SignalingGame (Fin 3) NNReal (Fin 2) (fun _ => ℝ) where
  u1 e w θ := max (max (w 0) (w 1)) 0 - aaK θ * e
  u j _ w θ := wageShare (w j) (w (1 - j)) (if 0 ≤ w j then aaθ θ - w j else 0)

/-- A two-type model used only for its home earnings `r = 0` in the Bertrand lemmas. -/
noncomputable def aaM0 : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun _ _ => 0

/-- Expected productivity under the belief `μ`. -/
noncomputable def aaMean (μ : Fin 3 → ℝ) : ℝ := ∑ θ, μ θ * aaθ θ

/-- The firms' response game after any education level is the wage game with expected
productivity `E_μ[θ]`. -/
theorem aa_payoff (a : NNReal) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (j : Fin 2) (w : Fin 2 → ℝ) :
    (aaGame.responseGame a μ).payoff j w =
      (wageGame (aaM0.offerProfit (aaMean μ))).payoff j w := by
  simp only [SignalingGame.responseGame, aaGame, wageGame, SigModel.offerProfit, aaM0, aaMean,
    wageShare, Fin.sum_univ_three] at hμ ⊢
  split_ifs
  all_goals first
    | ring1
    | linear_combination (-(w j)) * hμ
    | linear_combination (-(w j) / 2) * hμ

theorem aaMean_ge (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) : 1 ≤ aaMean μ := by
  obtain ⟨h0, h1, -⟩ := hμ
  simp only [aaMean, aaθ, Fin.sum_univ_three] at h1 ⊢
  simp
  nlinarith [h0 0, h0 1, h0 2]

theorem aaMean_le (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) : aaMean μ ≤ 10 := by
  obtain ⟨h0, h1, -⟩ := hμ
  simp only [aaMean, aaθ, Fin.sum_univ_three] at h1 ⊢
  simp
  nlinarith [h0 0, h0 1, h0 2]

theorem aa_belief_univ {T : Set (Fin 3)} {μ : Fin 3 → ℝ} (h : IsBeliefOn T μ) :
    IsBeliefOn Set.univ μ := ⟨h.1, h.2.1, fun _ _ => trivial⟩

/-- **Exercise 13.AA.1**. After education `a` with belief `μ`, the firms' Nash equilibria are both
bidding `E_μ[θ]` (Section 13.C, p. 452). -/
theorem aa_nash_iff (a : NNReal) (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (aaGame.responseGame a μ) w ↔ w 0 = aaMean μ ∧ w 1 = aaMean μ := by
  have hp := aaMean_ge μ hμ
  have heq : IsNashEquilibrium (aaGame.responseGame a μ) w ↔
      IsNashEquilibrium (wageGame (aaM0.offerProfit (aaMean μ))) w := by
    unfold IsNashEquilibrium
    simp only [aa_payoff a μ hμ.2.1]
  rw [heq, aaM0.bertrand_iff (by linarith) w]
  have hr : aaM0.r = 0 := rfl
  constructor
  · rintro ⟨h1, -, -⟩; exact h1 (by rw [hr]; linarith)
  · rintro ⟨h1, h2⟩
    refine ⟨fun _ => ⟨h1, h2⟩, fun h => ?_, fun h => ?_⟩ <;> rw [hr] at h <;> linarith

theorem aa_eqResponses (T : Set (Fin 3)) (a : NNReal) (w : Fin 2 → ℝ) :
    w ∈ aaGame.eqResponses T a ↔ ∃ μ, IsBeliefOn T μ ∧ w 0 = aaMean μ ∧ w 1 = aaMean μ := by
  constructor
  · rintro ⟨μ, hμ, hne⟩; exact ⟨μ, hμ, (aa_nash_iff a μ (aa_belief_univ hμ) w).1 hne⟩
  · rintro ⟨μ, hμ, hw⟩; exact ⟨μ, hμ, (aa_nash_iff a μ (aa_belief_univ hμ) w).2 hw⟩

theorem aa_u1 (a : NNReal) (m : ℝ) (hm : 0 ≤ m) (θ : Fin 3) :
    aaGame.u1 a (fun _ => m) θ = m - aaK θ * a := by
  simp [aaGame, hm]

theorem aaMean_pointMass (τ : Fin 3) : aaMean (pointMass τ) = aaθ τ := by
  simp [aaMean, pointMass]

/-- The wage bid `θ_τ` is an equilibrium response for beliefs concentrated on `T ∋ τ`. -/
theorem aa_resp_mem {T : Set (Fin 3)} {τ : Fin 3} (hτ : τ ∈ T) (a : NNReal) :
    (fun _ => aaθ τ) ∈ aaGame.eqResponses T a :=
  (aa_eqResponses T a _).2 ⟨pointMass τ, pointMass_belief τ T hτ, by rw [aaMean_pointMass],
    by rw [aaMean_pointMass]⟩

/-- Every equilibrium response gives type `θ` at most `10 - k_θ a`. -/
theorem aa_u1_le {T : Set (Fin 3)} {a : NNReal} {w : Fin 2 → ℝ} (hw : w ∈ aaGame.eqResponses T a)
    (θ : Fin 3) : aaGame.u1 a w θ ≤ 10 - aaK θ * a := by
  obtain ⟨μ, hμ, h0, h1⟩ := (aa_eqResponses T a w).1 hw
  have hge := aaMean_ge μ (aa_belief_univ hμ)
  have hle := aaMean_le μ (aa_belief_univ hμ)
  have : w = fun _ => aaMean μ := funext fun j => by fin_cases j <;> simp [h0, h1]
  rw [this, aa_u1 a _ (by linarith)]
  linarith

/-- **(13.AA.4)** for this game: a PBE with equilibrium payoffs `u* = (u₁, 3/2, 23/4)`,
`1 ≤ u₁ ≤ 3/2`, does not violate the intuitive criterion. For a deviation `e`, the beliefs
concentrated on the lowest type in `Θ**(e)` (or on type 1 if `Θ**(e)` is empty) produce a wage
that gives no type more than its equilibrium payoff. -/
theorem aa_passes_ic (uS : Fin 3 → ℝ) (h0 : 1 ≤ uS 0) (h0' : uS 0 ≤ 3 / 2) (h1 : uS 1 = 3 / 2)
    (h2 : uS 2 = 23 / 4) : ¬ aaGame.ViolatesIC uS := by
  rintro ⟨θ, a, hv⟩
  have ha : (0 : ℝ) ≤ a := a.2
  have hK : ∀ θ', 0 ≤ aaK θ' * a := fun θ' => by
    fin_cases θ' <;> simp [aaK]
  have hus : ∀ θ', 1 ≤ uS θ' := fun θ' => by
    fin_cases θ'
    · exact h0
    · simp [h1]; norm_num
    · simp [h2]; norm_num
  -- membership in `icTypes`
  have hic : ∀ τ, τ ∈ aaGame.typesNotEqDominated uS a → τ ∈ aaGame.icTypes uS a := by
    intro τ hτ
    have hne : (aaGame.typesNotEqDominated uS a).Nonempty := ⟨τ, hτ⟩
    simp only [icTypes, hne, ↓reduceIte]
    exact hτ
  have hmem10 : ∀ τ, uS τ ≤ 10 - aaK τ * a → τ ∈ aaGame.typesNotEqDominated uS a := by
    intro τ hle hdom
    have := hdom _ (aa_resp_mem (τ := 2) (Set.mem_univ _) a)
    rw [aa_u1 a _ (by simp [aaθ])] at this
    simp only [aaθ] at this
    simp at this
    linarith
  -- the deviation fails against the response `θ_τ`
  have key : ∀ τ, τ ∈ aaGame.icTypes uS a → aaθ τ - aaK θ * a ≤ uS θ → False := by
    intro τ hτ hle
    have := hv _ (aa_resp_mem hτ a)
    rw [aa_u1 a _ (by fin_cases τ <;> simp [aaθ])] at this
    linarith
  by_cases hd0 : uS 0 ≤ 10 - aaK 0 * a
  · -- type 1 is not equilibrium dominated: respond with the wage `1`
    refine key 0 (hic 0 (hmem10 0 hd0)) ?_
    have := hus θ
    have := hK θ
    simp only [aaθ]; simp; linarith
  · rw [not_le] at hd0
    have hk0 : aaK 0 * a = a := by simp [aaK]
    rw [hk0] at hd0
    by_cases ha17 : (a : ℝ) ≤ 17
    · -- type 2 is not equilibrium dominated: respond with the wage `2`
      refine key 1 (hic 1 (hmem10 1 (by rw [h1]; simp [aaK]; linarith))) ?_
      fin_cases θ <;> simp [aaθ, aaK, h1, h2] <;> linarith
    · -- no type is undominated: all beliefs are allowed; respond with the wage `1`
      rw [not_le] at ha17
      have hempty : aaGame.typesNotEqDominated uS a = ∅ := by
        ext τ
        simp only [typesNotEqDominated, EqDominated, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_not]
        intro w hw
        have := aa_u1_le hw τ
        fin_cases τ <;> simp [aaK, h1, h2] at this ⊢ <;> linarith
      have huniv : aaGame.icTypes uS a = Set.univ := by
        simp [icTypes, hempty]
      refine key 0 (by rw [huniv]; trivial) ?_
      have := hus θ
      have := hK θ
      simp only [aaθ]; simp; linarith

/-- The uniform prior. -/
noncomputable def aaPrior : Fin 3 → ℝ := fun _ => 1 / 3

/-- The pooled belief `(1/2, 1/2, 0)` on types 1 and 2. -/
noncomputable def aaPool : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

theorem aaPool_belief : IsBeliefOn Set.univ aaPool :=
  ⟨fun θ => by fin_cases θ <;> simp [aaPool], by simp [aaPool, Fin.sum_univ_three]; norm_num,
    fun _ _ => trivial⟩

/-- Education levels of the separating PBE. -/
noncomputable def aaE1 : Fin 3 → NNReal := ![0, 1, 17]

/-- Education levels of the partially pooling PBE. -/
noncomputable def aaE2 : Fin 3 → NNReal := ![0, 0, 17]

open Classical in
/-- Beliefs of the separating PBE: Bayes on the path, type 1 off the path. -/
noncomputable def aaBel1 (a : NNReal) : Fin 3 → ℝ :=
  if a = 1 then pointMass 1 else if a = 17 then pointMass 2 else pointMass 0

open Classical in
/-- Beliefs of the partially pooling PBE. -/
noncomputable def aaBel2 (a : NNReal) : Fin 3 → ℝ :=
  if a = 0 then aaPool else if a = 17 then pointMass 2 else pointMass 0

/-- The firms bid the expected productivity. -/
noncomputable def aaResp (μ : NNReal → Fin 3 → ℝ) (a : NNReal) : Fin 2 → ℝ :=
  fun _ => aaMean (μ a)

theorem aaBel1_belief (a : NNReal) : IsBeliefOn Set.univ (aaBel1 a) := by
  unfold aaBel1
  split_ifs <;> exact pointMass_belief _ _ trivial

theorem aaBel2_belief (a : NNReal) : IsBeliefOn Set.univ (aaBel2 a) := by
  unfold aaBel2
  split_ifs
  · exact aaPool_belief
  · exact pointMass_belief _ _ trivial
  · exact pointMass_belief _ _ trivial

theorem aaResp1 (a : NNReal) :
    aaResp aaBel1 a = fun _ => if a = 1 then 2 else if a = 17 then 10 else 1 := by
  funext j
  simp only [aaResp, aaBel1]
  split_ifs <;> rw [aaMean_pointMass] <;> simp [aaθ]

theorem aaResp2 (a : NNReal) :
    aaResp aaBel2 a = fun _ => if a = 0 then 3 / 2 else if a = 17 then 10 else 1 := by
  funext j
  simp only [aaResp, aaBel2]
  split_ifs
  · simp [aaMean, aaPool, aaθ, Fin.sum_univ_three]; norm_num
  · rw [aaMean_pointMass]; simp [aaθ]
  · rw [aaMean_pointMass]; simp [aaθ]

theorem aa_payoff1 : aaGame.eqPayoff aaE1 (aaResp aaBel1) = ![1, 3 / 2, 23 / 4] := by
  funext θ
  simp only [eqPayoff, aaResp1, aaGame]
  fin_cases θ <;> simp [aaE1, aaK] <;> norm_num

theorem aa_payoff2 : aaGame.eqPayoff aaE2 (aaResp aaBel2) = ![3 / 2, 3 / 2, 23 / 4] := by
  funext θ
  simp only [eqPayoff, aaResp2, aaGame]
  fin_cases θ <;> simp [aaE2, aaK] <;> norm_num

/-- **Exercise 13.AA.1** (MWG, p. 476). The separating PBE: education `(0, 1, 17)`. -/
theorem aa_pbe1 : aaGame.IsPBE aaPrior aaE1 (aaResp aaBel1) aaBel1 := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ⟨aaBel1_belief a,
    (aa_nash_iff a _ (aaBel1_belief a) _).2 ⟨rfl, rfl⟩⟩⟩
  · change _ ≤ aaGame.eqPayoff aaE1 (aaResp aaBel1) θ
    have ha := NNReal.coe_nonneg a
    rw [aa_payoff1, aaResp1, aa_u1 a _ (by split_ifs <;> norm_num)]
    split_ifs with h1 h2
    · subst h1; fin_cases θ <;> norm_num [aaK]
    · subst h2; fin_cases θ <;> norm_num [aaK]
    · fin_cases θ <;> norm_num [aaK] <;> linarith
  · obtain ⟨θ', rfl⟩ := ha
    simp only [Finset.sum_filter, Fin.sum_univ_three]
    fin_cases θ' <;> fin_cases θ <;> simp [aaBel1, aaE1, aaPrior, pointMass]

/-- **Exercise 13.AA.1** (MWG, p. 476). The partially pooling PBE: types 1 and 2 choose
`e = 0`, type 3 chooses `17`. -/
theorem aa_pbe2 : aaGame.IsPBE aaPrior aaE2 (aaResp aaBel2) aaBel2 := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ⟨aaBel2_belief a,
    (aa_nash_iff a _ (aaBel2_belief a) _).2 ⟨rfl, rfl⟩⟩⟩
  · change _ ≤ aaGame.eqPayoff aaE2 (aaResp aaBel2) θ
    have ha := NNReal.coe_nonneg a
    rw [aa_payoff2, aaResp2, aa_u1 a _ (by split_ifs <;> norm_num)]
    split_ifs with h1 h2
    · subst h1; fin_cases θ <;> norm_num [aaK]
    · subst h2; fin_cases θ <;> norm_num [aaK]
    · fin_cases θ <;> norm_num [aaK] <;> linarith
  · obtain ⟨θ', rfl⟩ := ha
    simp only [Finset.sum_filter, Fin.sum_univ_three]
    fin_cases θ' <;> fin_cases θ <;> simp [aaBel2, aaE2, aaPrior, aaPool, pointMass] <;> norm_num

/-- **Exercise 13.AA.1** (MWG, p. 476). In the three-type education signaling model with
`r(θ) = 0`, two PBE with different outcomes, the separating PBE (education `(0, 1, 17)`) and a
partially pooling PBE (education `(0, 0, 17)`), both satisfy the intuitive criterion: the
lowest type gets `1` in the first and `3/2` in the second. -/
theorem exercise_13_AA_1 :
    aaGame.IsPBE aaPrior aaE1 (aaResp aaBel1) aaBel1 ∧
      aaGame.IsPBE aaPrior aaE2 (aaResp aaBel2) aaBel2 ∧
      ¬ aaGame.ViolatesIC (aaGame.eqPayoff aaE1 (aaResp aaBel1)) ∧
      ¬ aaGame.ViolatesIC (aaGame.eqPayoff aaE2 (aaResp aaBel2)) ∧
      aaE1 ≠ aaE2 ∧
      aaGame.eqPayoff aaE1 (aaResp aaBel1) 0 ≠ aaGame.eqPayoff aaE2 (aaResp aaBel2) 0 := by
  refine ⟨aa_pbe1, aa_pbe2, ?_, ?_, fun h => ?_, ?_⟩
  · rw [aa_payoff1]; exact aa_passes_ic _ (by simp) (by simp; norm_num) (by simp) (by simp)
  · rw [aa_payoff2]
    exact aa_passes_ic _ (by simp; norm_num) (by simp) (by simp) (by simp)
  · have := congrFun h 1
    simp [aaE1, aaE2] at this
  · rw [aa_payoff1, aa_payoff2]; simp; norm_num

end MWG.AdverseSelection

set_option linter.style.longLine false
#print axioms MWG.AdverseSelection.acceptSet
#print axioms MWG.AdverseSelection.meanType
#print axioms MWG.AdverseSelection.condMean
#print axioms MWG.AdverseSelection.IsCompEq
#print axioms MWG.AdverseSelection.eqWages
#print axioms MWG.AdverseSelection.mem_eqWages_iff
#print axioms MWG.AdverseSelection.laborDemand
#print axioms MWG.AdverseSelection.laborDemand_unbounded
#print axioms MWG.AdverseSelection.laborDemand_profit
#print axioms MWG.AdverseSelection.firmProfit
#print axioms MWG.AdverseSelection.TypeDist
#print axioms MWG.AdverseSelection.TypeDist.mk
#print axioms MWG.AdverseSelection.TypeDist.nonneg
#print axioms MWG.AdverseSelection.TypeDist.lt
#print axioms MWG.AdverseSelection.TypeDist.prob
#print axioms MWG.AdverseSelection.TypeDist.supp
#print axioms MWG.AdverseSelection.HasPosDensity
#print axioms MWG.AdverseSelection.HasPosDensity.mk
#print axioms MWG.AdverseSelection.HasPosDensity.noAtom
#print axioms MWG.AdverseSelection.HasPosDensity.pos
#print axioms MWG.AdverseSelection.TypeDist.ae_mem
#print axioms MWG.AdverseSelection.TypeDist.integrable_id
#print axioms MWG.AdverseSelection.TypeDist.meanType_mem
#print axioms MWG.AdverseSelection.measurableSet_acceptSet
#print axioms MWG.AdverseSelection.firmProfit_eq_setIntegral
#print axioms MWG.AdverseSelection.firmProfit_eq
#print axioms MWG.AdverseSelection.mem_eqWages_iff_profit
#print axioms MWG.AdverseSelection.firmProfit_of_null
#print axioms MWG.AdverseSelection.continuous_firmProfit
#print axioms MWG.AdverseSelection.firmProfit_nonpos_of_gt
#print axioms MWG.AdverseSelection.setIntegral_pos_of_ae_pos
#print axioms MWG.AdverseSelection.firmProfit_neg_of_gt
#print axioms MWG.AdverseSelection.measure_acceptSet_inter
#print axioms MWG.AdverseSelection.condMean_of_superset
#print axioms MWG.AdverseSelection.firmProfit_neg_of_ae_lt
#print axioms MWG.AdverseSelection.acceptSet_inter_eq_empty
#print axioms MWG.AdverseSelection.acceptSet_inter_eq_singleton
#print axioms MWG.AdverseSelection.measure_acceptSet_pos
#print axioms MWG.AdverseSelection.not_mem_eqWages_of_lt
#print axioms MWG.AdverseSelection.mem_eqWages_rl_iff
#print axioms MWG.AdverseSelection.firmProfit_rl
#print axioms MWG.AdverseSelection.firmProfit_of_lt
#print axioms MWG.AdverseSelection.firmProfit_zero_nonneg
#print axioms MWG.AdverseSelection.RegularModel
#print axioms MWG.AdverseSelection.RegularModel.mk
#print axioms MWG.AdverseSelection.RegularModel.dist
#print axioms MWG.AdverseSelection.RegularModel.dens
#print axioms MWG.AdverseSelection.RegularModel.meas
#print axioms MWG.AdverseSelection.RegularModel.mono
#print axioms MWG.AdverseSelection.RegularModel.cont
#print axioms MWG.AdverseSelection.RegularModel.le
#print axioms MWG.AdverseSelection.RegularModel.continuous
#print axioms MWG.AdverseSelection.RegularModel.mem_eqWages_iff
#print axioms MWG.AdverseSelection.RegularModel.firmProfit_neg_of_gt_max
#print axioms MWG.AdverseSelection.RegularModel.firmProfit_pos_of_lt_θl
#print axioms MWG.AdverseSelection.RegularModel.exists_isGreatest_eqWages
#print axioms MWG.AdverseSelection.condMean_ge
#print axioms MWG.AdverseSelection.condMean_mono_of_sep
#print axioms MWG.AdverseSelection.condMean_lt_of_sep
#print axioms MWG.AdverseSelection.condMean_acceptSet_mono
#print axioms MWG.AdverseSelection.RegularModel.condMean_acceptSet_strictMono
#print axioms MWG.AdverseSelection.wageShare
#print axioms MWG.AdverseSelection.wageGame
#print axioms MWG.AdverseSelection.WageBestReply
#print axioms MWG.AdverseSelection.isNash_wageGame_iff
#print axioms MWG.AdverseSelection.wageShare_nonneg
#print axioms MWG.AdverseSelection.wageShare_of_gt
#print axioms MWG.AdverseSelection.wageShare_of_eq
#print axioms MWG.AdverseSelection.wageShare_of_lt
#print axioms MWG.AdverseSelection.WageBestReply.nonneg
#print axioms MWG.AdverseSelection.WageBestReply.profit_nonpos
#print axioms MWG.AdverseSelection.wageGame_unique
#print axioms MWG.AdverseSelection.wageGame_flat
#print axioms MWG.AdverseSelection.wageGame_flat_open
#print axioms MWG.AdverseSelection.worker_best
#print axioms MWG.AdverseSelection.proposition_13_B_1_i
#print axioms MWG.AdverseSelection.proposition_13_B_1_i_outcome
#print axioms MWG.AdverseSelection.proposition_13_B_1_ii
#print axioms MWG.AdverseSelection.proposition_13_B_1_ii_multiple
#print axioms MWG.AdverseSelection.proposition_13_B_1_ii_payoffs
#print axioms MWG.AdverseSelection.unifMeas
#print axioms MWG.AdverseSelection.unifMeas_apply
#print axioms MWG.AdverseSelection.unifMeas_isProb
#print axioms MWG.AdverseSelection.unifMeas_compl
#print axioms MWG.AdverseSelection.Iic_inter_Icc_of_le
#print axioms MWG.AdverseSelection.unifMeas_typeDist
#print axioms MWG.AdverseSelection.unifMeas_density
#print axioms MWG.AdverseSelection.unifMeas_Iic
#print axioms MWG.AdverseSelection.unifMeas_setIntegral_Iic
#print axioms MWG.AdverseSelection.unifMeas_mean
#print axioms MWG.AdverseSelection.akerlofR
#print axioms MWG.AdverseSelection.acceptSet_akerlofR
#print axioms MWG.AdverseSelection.akerlof_regular
#print axioms MWG.AdverseSelection.example_13_B_1
#print axioms MWG.AdverseSelection.example_13_B_1_zero
#print axioms MWG.AdverseSelection.example_13_B_1_high
#print axioms MWG.AdverseSelection.example_13_B_1_lt
#print axioms MWG.AdverseSelection.example_13_B_1_unravel
#print axioms MWG.AdverseSelection.example_13_B_1_akerlof
#print axioms MWG.AdverseSelection.example_13_B_1_spne
#print axioms MWG.AdverseSelection.example_13_B_1_lowα
#print axioms MWG.AdverseSelection.proposition_13_B_1_i_instance
#print axioms MWG.AdverseSelection.jumpR
#print axioms MWG.AdverseSelection.jumpR_inter_subset
#print axioms MWG.AdverseSelection.jumpR_null
#print axioms MWG.AdverseSelection.jumpR_meas
#print axioms MWG.AdverseSelection.jumpR_profit_neg
#print axioms MWG.AdverseSelection.counterexample_13_B_1_i
#print axioms MWG.AdverseSelection.typeMarketClears
#print axioms MWG.AdverseSelection.typeMarket_clears_iff
#print axioms MWG.AdverseSelection.fullInfo_eq
#print axioms MWG.AdverseSelection.aggSurplus
#print axioms MWG.AdverseSelection.optEmployment
#print axioms MWG.AdverseSelection.optEmployment_eq
#print axioms MWG.AdverseSelection.employment_le
#print axioms MWG.AdverseSelection.integrable_employment
#print axioms MWG.AdverseSelection.aggSurplus_le_opt
#print axioms MWG.AdverseSelection.aggSurplus_lt_opt
#print axioms MWG.AdverseSelection.condMean_const
#print axioms MWG.AdverseSelection.eqWages_const
#print axioms MWG.AdverseSelection.acceptSet_const
#print axioms MWG.AdverseSelection.const_inefficient
#print axioms MWG.AdverseSelection.atomMeas
#print axioms MWG.AdverseSelection.integral_atomMeas
#print axioms MWG.AdverseSelection.atomMeas_typeDist
#print axioms MWG.AdverseSelection.const_atom_counterexample
#print axioms MWG.AdverseSelection.pareto_ranked
#print axioms MWG.AdverseSelection.MonoModel
#print axioms MWG.AdverseSelection.MonoModel.mk
#print axioms MWG.AdverseSelection.MonoModel.dist
#print axioms MWG.AdverseSelection.MonoModel.dens
#print axioms MWG.AdverseSelection.MonoModel.meas
#print axioms MWG.AdverseSelection.MonoModel.mono
#print axioms MWG.AdverseSelection.MonoModel.cont
#print axioms MWG.AdverseSelection.RegularModel.toMono
#print axioms MWG.AdverseSelection.BudgetOK
#print axioms MWG.AdverseSelection.IsParetoImprovement
#print axioms MWG.AdverseSelection.IsConstrainedPO
#print axioms MWG.AdverseSelection.budget_wu_le
#print axioms MWG.AdverseSelection.footnote_15
#print axioms MWG.AdverseSelection.scheme_payoff
#print axioms MWG.AdverseSelection.MonoModel.firmProfit_neg_of_gt_max
#print axioms MWG.AdverseSelection.MonoModel.profit_add_lt
#print axioms MWG.AdverseSelection.firmProfit_of_full
#print axioms MWG.AdverseSelection.mean_mem_eqWages
#print axioms MWG.AdverseSelection.MonoModel.isConstrainedPO
#print axioms MWG.AdverseSelection.proposition_13_B_2
#print axioms MWG.AdverseSelection.exercise_13_B_10
#print axioms MWG.AdverseSelection.schemeWu
#print axioms MWG.AdverseSelection.schemeWe
#print axioms MWG.AdverseSelection.scheme_13_B_7_8
#print axioms MWG.AdverseSelection.scheme_13_B_11_12
#print axioms MWG.AdverseSelection.scheme_at_θstar
#print axioms MWG.AdverseSelection.highest_wage_implementable
#print axioms MWG.AdverseSelection.dominated_not_constrainedPO
#print axioms MWG.AdverseSelection.weightedWelfare
#print axioms MWG.AdverseSelection.weightedWelfare_const
#print axioms MWG.AdverseSelection.mandate_all
#print axioms MWG.AdverseSelection.MechIR
#print axioms MWG.AdverseSelection.MechBB
#print axioms MWG.AdverseSelection.MechIC
#print axioms MWG.AdverseSelection.MechBudget
#print axioms MWG.AdverseSelection.mechanism_17_of_14_15
#print axioms MWG.AdverseSelection.mechanism_exists_t
#print axioms MWG.AdverseSelection.mechanism_two_outcome
#print axioms MWG.AdverseSelection.mechanism_scheme
#print axioms MWG.AdverseSelection.SigModel
#print axioms MWG.AdverseSelection.SigModel.mk
#print axioms MWG.AdverseSelection.SigModel.θL
#print axioms MWG.AdverseSelection.SigModel.θH
#print axioms MWG.AdverseSelection.SigModel.lam
#print axioms MWG.AdverseSelection.SigModel.r
#print axioms MWG.AdverseSelection.SigModel.c
#print axioms MWG.AdverseSelection.SigModel.θ
#print axioms MWG.AdverseSelection.SigModel.Eθ
#print axioms MWG.AdverseSelection.SigModel.expProd
#print axioms MWG.AdverseSelection.SigModel.Valid
#print axioms MWG.AdverseSelection.SigModel.Valid.mk
#print axioms MWG.AdverseSelection.SigModel.Valid.θL_pos
#print axioms MWG.AdverseSelection.SigModel.Valid.lt
#print axioms MWG.AdverseSelection.SigModel.Valid.lam_pos
#print axioms MWG.AdverseSelection.SigModel.Valid.lam_lt
#print axioms MWG.AdverseSelection.SigModel.Valid.r_nonneg
#print axioms MWG.AdverseSelection.SigModel.Valid.r_lt
#print axioms MWG.AdverseSelection.SigModel.Valid.c_zero
#print axioms MWG.AdverseSelection.SigModel.Valid.c_mono
#print axioms MWG.AdverseSelection.SigModel.Valid.c_cont
#print axioms MWG.AdverseSelection.SigModel.Valid.sc
#print axioms MWG.AdverseSelection.SigModel.offerProfit
#print axioms MWG.AdverseSelection.SigModel.workerPay
#print axioms MWG.AdverseSelection.SigModel.BayesOnPath
#print axioms MWG.AdverseSelection.SigModel.IsPBE
#print axioms MWG.AdverseSelection.SigModel.Separating
#print axioms MWG.AdverseSelection.SigModel.Pooling
#print axioms MWG.AdverseSelection.SigModel.θ_true
#print axioms MWG.AdverseSelection.SigModel.θ_false
#print axioms MWG.AdverseSelection.SigModel.Valid.expProd_mem
#print axioms MWG.AdverseSelection.SigModel.expProd_one
#print axioms MWG.AdverseSelection.SigModel.expProd_zero
#print axioms MWG.AdverseSelection.SigModel.expProd_lam
#print axioms MWG.AdverseSelection.SigModel.Valid.Eθ_mem
#print axioms MWG.AdverseSelection.SigModel.Valid.c_lt_of_pos
#print axioms MWG.AdverseSelection.SigModel.Valid.c_le
#print axioms MWG.AdverseSelection.SigModel.Valid.c_pos
#print axioms MWG.AdverseSelection.SigModel.Valid.c_nonneg
#print axioms MWG.AdverseSelection.SigModel.offerProfit_rc
#print axioms MWG.AdverseSelection.SigModel.bertrand_iff
#print axioms MWG.AdverseSelection.SigModel.bertrand_wage
#print axioms MWG.AdverseSelection.SigModel.bertrandOffer
#print axioms MWG.AdverseSelection.SigModel.bertrandOffer_nash
#print axioms MWG.AdverseSelection.SigModel.bertrandOffer_max
#print axioms MWG.AdverseSelection.SigModel.redPay
#print axioms MWG.AdverseSelection.SigModel.IsPBERed
#print axioms MWG.AdverseSelection.SigModel.Valid.isPBERed_of_isPBE
#print axioms MWG.AdverseSelection.SigModel.Valid.isPBE_of_isPBERed
#print axioms MWG.AdverseSelection.SigModel.Valid.exists_isPBE_iff
#print axioms MWG.AdverseSelection.SigModel.Valid.wage_mem
#print axioms MWG.AdverseSelection.SigModel.lemma_13_C_1
#print axioms MWG.AdverseSelection.SigModel.lemma_13_C_1_r0
#print axioms MWG.AdverseSelection.SigModel.Valid.low_payoff
#print axioms MWG.AdverseSelection.SigModel.lemma_13_C_2
#print axioms MWG.AdverseSelection.SigModel.sepBelief
#print axioms MWG.AdverseSelection.SigModel.separating_sep
#print axioms MWG.AdverseSelection.SigModel.separating_sepBelief
#print axioms MWG.AdverseSelection.SigModel.separating_iff
#print axioms MWG.AdverseSelection.SigModel.separating_interval
#print axioms MWG.AdverseSelection.SigModel.poolBelief
#print axioms MWG.AdverseSelection.SigModel.pooling_iff
#print axioms MWG.AdverseSelection.SigModel.pooling_interval
#print axioms MWG.AdverseSelection.SigModel.separating_pareto_ranked
#print axioms MWG.AdverseSelection.SigModel.separating_payoffs
#print axioms MWG.AdverseSelection.SigModel.separating_vs_nosignal
#print axioms MWG.AdverseSelection.SigModel.high_type_worse_as_lam_to_one
#print axioms MWG.AdverseSelection.SigModel.pooling_dominated
#print axioms MWG.AdverseSelection.SigModel.low_never_above
#print axioms MWG.AdverseSelection.SigModel.refined_separating
#print axioms MWG.AdverseSelection.SigModel.pooling_eliminated
#print axioms MWG.AdverseSelection.SigModel.smalltype_pooling
#print axioms MWG.AdverseSelection.SigModel.smalltype_separating
#print axioms MWG.AdverseSelection.SigModel.smalltype_pareto
#print axioms MWG.AdverseSelection.SigModel.crossModel
#print axioms MWG.AdverseSelection.SigModel.crossModel_cL
#print axioms MWG.AdverseSelection.SigModel.crossModel_cH
#print axioms MWG.AdverseSelection.SigModel.crossModel_cH_lt
#print axioms MWG.AdverseSelection.SigModel.crossModel_valid
#print axioms MWG.AdverseSelection.SigModel.crossModel_separating
#print axioms MWG.AdverseSelection.SigModel.crossModel_pooling
#print axioms MWG.AdverseSelection.SigModel.crossWage
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_3
#print axioms MWG.AdverseSelection.SignalingGame
#print axioms MWG.AdverseSelection.SignalingGame.mk
#print axioms MWG.AdverseSelection.SignalingGame.u1
#print axioms MWG.AdverseSelection.SignalingGame.u
#print axioms MWG.AdverseSelection.SignalingGame.IsBeliefOn
#print axioms MWG.AdverseSelection.SignalingGame.responseGame
#print axioms MWG.AdverseSelection.SignalingGame.IsPBE
#print axioms MWG.AdverseSelection.SignalingGame.DominatedFor
#print axioms MWG.AdverseSelection.SignalingGame.typesUndominated
#print axioms MWG.AdverseSelection.SignalingGame.eqResponses
#print axioms MWG.AdverseSelection.SignalingGame.typesUndominatedStar
#print axioms MWG.AdverseSelection.SignalingGame.EqDominated
#print axioms MWG.AdverseSelection.SignalingGame.typesNotEqDominated
#print axioms MWG.AdverseSelection.SignalingGame.ReasonableBeliefs
#print axioms MWG.AdverseSelection.SignalingGame.eqPayoff
#print axioms MWG.AdverseSelection.SignalingGame.icTypes
#print axioms MWG.AdverseSelection.SignalingGame.ViolatesIC
#print axioms MWG.AdverseSelection.SignalingGame.IsPBE.mem_eqResponses
#print axioms MWG.AdverseSelection.SignalingGame.eqDominated_of_dominated
#print axioms MWG.AdverseSelection.SignalingGame.typesNotEqDominated_subset
#print axioms MWG.AdverseSelection.SignalingGame.passesIC_of_reasonable
#print axioms MWG.AdverseSelection.SignalingGame.two_types_singleton
#print axioms MWG.AdverseSelection.SignalingGame.two_types_reasonable
#print axioms MWG.AdverseSelection.exG
#print axioms MWG.AdverseSelection.exGame
#print axioms MWG.AdverseSelection.exPrior
#print axioms MWG.AdverseSelection.exGame_payoff
#print axioms MWG.AdverseSelection.exGame_nash_iff
#print axioms MWG.AdverseSelection.pointMass
#print axioms MWG.AdverseSelection.pointMass_belief
#print axioms MWG.AdverseSelection.pointMass_resp
#print axioms MWG.AdverseSelection.exGame_eqResponses
#print axioms MWG.AdverseSelection.example_13_AA_1_eqdom
#print axioms MWG.AdverseSelection.exResp
#print axioms MWG.AdverseSelection.exBelief
#print axioms MWG.AdverseSelection.exPrior_belief
#print axioms MWG.AdverseSelection.exGame_eqPayoff
#print axioms MWG.AdverseSelection.example_13_AA_1_pbe
#print axioms MWG.AdverseSelection.example_13_AA_1_ic
#print axioms MWG.AdverseSelection.example_13_AA_1_no_reasonable
#print axioms MWG.AdverseSelection.twoG
#print axioms MWG.AdverseSelection.twoGame
#print axioms MWG.AdverseSelection.twoGame_payoff
#print axioms MWG.AdverseSelection.twoGame_nash_iff
#print axioms MWG.AdverseSelection.boolPoint
#print axioms MWG.AdverseSelection.boolPoint_belief
#print axioms MWG.AdverseSelection.twoGame_one_mem
#print axioms MWG.AdverseSelection.twoResp
#print axioms MWG.AdverseSelection.twoBelief
#print axioms MWG.AdverseSelection.twoTypes_instance
#print axioms MWG.AdverseSelection.SigModel.education_Sstar
#print axioms MWG.AdverseSelection.SigModel.education_Theta_all
#print axioms MWG.AdverseSelection.SigModel.EqDomEd
#print axioms MWG.AdverseSelection.SigModel.notEqDomEd
#print axioms MWG.AdverseSelection.SigModel.AdmissibleOn
#print axioms MWG.AdverseSelection.SigModel.icSetEd
#print axioms MWG.AdverseSelection.SigModel.ViolatesICEd
#print axioms MWG.AdverseSelection.SigModel.eqPay
#print axioms MWG.AdverseSelection.SigModel.violates_of_high
#print axioms MWG.AdverseSelection.SigModel.education_IC_unique
#print axioms MWG.AdverseSelection.SigModel.education_IC_exists
#print axioms MWG.AdverseSelection.SigModel.education_IC_instance
#print axioms MWG.AdverseSelection.SigModel.util
#print axioms MWG.AdverseSelection.SigModel.ValidMenu
#print axioms MWG.AdverseSelection.SigModel.Chooses
#print axioms MWG.AdverseSelection.SigModel.share
#print axioms MWG.AdverseSelection.SigModel.typeProfit
#print axioms MWG.AdverseSelection.SigModel.screenProfit
#print axioms MWG.AdverseSelection.SigModel.IsScreenEq
#print axioms MWG.AdverseSelection.SigModel.chooses_unique
#print axioms MWG.AdverseSelection.SigModel.exists_chooses
#print axioms MWG.AdverseSelection.SigModel.typeProfit_of_chooses
#print axioms MWG.AdverseSelection.SigModel.typeProfit_of_not
#print axioms MWG.AdverseSelection.SigModel.share_add
#print axioms MWG.AdverseSelection.SigModel.share_nonneg
#print axioms MWG.AdverseSelection.SigModel.share_le_one
#print axioms MWG.AdverseSelection.SigModel.screenProfit_empty
#print axioms MWG.AdverseSelection.SigModel.chooses_of_strict
#print axioms MWG.AdverseSelection.SigModel.typeProfit_empty
#print axioms MWG.AdverseSelection.SigModel.typeProfit_capture
#print axioms MWG.AdverseSelection.SigModel.typeProfit_add
#print axioms MWG.AdverseSelection.SigModel.IsTypeEq
#print axioms MWG.AdverseSelection.SigModel.IsTypeEq.symm
#print axioms MWG.AdverseSelection.SigModel.proposition_13_D_1
#print axioms MWG.AdverseSelection.SigModel.proposition_13_D_1_exists
#print axioms MWG.AdverseSelection.SigModel.BothEmployed
#print axioms MWG.AdverseSelection.SigModel.IsScreenEq.symm
#print axioms MWG.AdverseSelection.SigModel.BothEmployed.symm
#print axioms MWG.AdverseSelection.SigModel.IsScreenEq.nonneg
#print axioms MWG.AdverseSelection.SigModel.screenProfit_add
#print axioms MWG.AdverseSelection.SigModel.chosen_valid
#print axioms MWG.AdverseSelection.SigModel.screenProfit_capture_high
#print axioms MWG.AdverseSelection.SigModel.screenProfit_capture_low_pos
#print axioms MWG.AdverseSelection.SigModel.IsScreenEq.exists_bothEmployed
#print axioms MWG.AdverseSelection.SigModel.zero_profits_of_employed
#print axioms MWG.AdverseSelection.SigModel.lemma_13_D_1
#print axioms MWG.AdverseSelection.SigModel.exists_high_dev
#print axioms MWG.AdverseSelection.SigModel.lemma_13_D_2
#print axioms MWG.AdverseSelection.SigModel.no_low_capture
#print axioms MWG.AdverseSelection.SigModel.lemma_13_D_3
#print axioms MWG.AdverseSelection.SigModel.lemma_13_D_4
#print axioms MWG.AdverseSelection.SigModel.lemma_13_D_5
#print axioms MWG.AdverseSelection.SigModel.proposition_13_D_2
#print axioms MWG.AdverseSelection.SigModel.no_eq_of_pair_deviation
#print axioms MWG.AdverseSelection.SigModel.no_eq_of_pooling_deviation
#print axioms MWG.AdverseSelection.SigModel.screenModel
#print axioms MWG.AdverseSelection.SigModel.screenModel_valid
#print axioms MWG.AdverseSelection.SigModel.nonexistence_pooling_instance
#print axioms MWG.AdverseSelection.SigModel.nonexistence_pair_instance
#print axioms MWG.AdverseSelection.SigModel.sepMenu
#print axioms MWG.AdverseSelection.SigModel.NoProfitableDeviation
#print axioms MWG.AdverseSelection.SigModel.isScreenEq_sepMenu
#print axioms MWG.AdverseSelection.SigModel.screening_low_worse
#print axioms MWG.AdverseSelection.SigModel.screening_inefficient
#print axioms MWG.AdverseSelection.SigModel.screening_high_better
#print axioms MWG.AdverseSelection.SigModel.ScreenFeasible
#print axioms MWG.AdverseSelection.SigModel.screening_no_strict_improvement
#print axioms MWG.AdverseSelection.SigModel.linModel
#print axioms MWG.AdverseSelection.SigModel.linModel_cL
#print axioms MWG.AdverseSelection.SigModel.linModel_cH
#print axioms MWG.AdverseSelection.SigModel.linModel_valid
#print axioms MWG.AdverseSelection.SigModel.footnote_25_counterexample
#print axioms MWG.AdverseSelection.SigModel.screenModel_cL
#print axioms MWG.AdverseSelection.SigModel.screenModel_cH
#print axioms MWG.AdverseSelection.SigModel.figure_13_D_7a
#print axioms MWG.AdverseSelection.SigModel.proposition_13_D_2_instance
#print axioms MWG.AdverseSelection.sum_pos_of_fibers
#print axioms MWG.AdverseSelection.exercise_13_B_4
#print axioms MWG.AdverseSelection.exercise_13_C_5a
#print axioms MWG.AdverseSelection.exercise_13_C_5b
#print axioms MWG.AdverseSelection.exercise_13_C_6a
#print axioms MWG.AdverseSelection.eqWagesB5
#print axioms MWG.AdverseSelection.exercise_13_B_5a
#print axioms MWG.AdverseSelection.exercise_13_B_5b
#print axioms MWG.AdverseSelection.exercise_13_B_5c
#print axioms MWG.AdverseSelection.exercise_13_B_5d
#print axioms MWG.AdverseSelection.proposition_13_B_2_instance
#print axioms MWG.AdverseSelection.IsPBEC4
#print axioms MWG.AdverseSelection.sepEduc
#print axioms MWG.AdverseSelection.sepWage
#print axioms MWG.AdverseSelection.sepEduc_sq
#print axioms MWG.AdverseSelection.sepWage_sepEduc
#print axioms MWG.AdverseSelection.sepEduc_injOn
#print axioms MWG.AdverseSelection.exercise_13_C_4_separating
#print axioms MWG.AdverseSelection.poolWage
#print axioms MWG.AdverseSelection.exercise_13_C_4_pooling
#print axioms MWG.AdverseSelection.exercise_13_C_4_not_unique
#print axioms MWG.AdverseSelection.eq_of_sq_bound
#print axioms MWG.AdverseSelection.exercise_13_C_4_unique_separating
#print axioms MWG.AdverseSelection.exercise_13_C_4_instance
#print axioms MWG.AdverseSelection.exB_ae_eq_of_inter
#print axioms MWG.AdverseSelection.exB_condMean_congr
#print axioms MWG.AdverseSelection.exB_condMean_empty
#print axioms MWG.AdverseSelection.exB_le_condMean
#print axioms MWG.AdverseSelection.exB_eq_zero_of_cross
#print axioms MWG.AdverseSelection.exB_lt_near
#print axioms MWG.AdverseSelection.exB_gt_near
#print axioms MWG.AdverseSelection.exB_integrable
#print axioms MWG.AdverseSelection.exercise_13_B_1_cutoff
#print axioms MWG.AdverseSelection.MonoModel.acceptSet_cutoff
#print axioms MWG.AdverseSelection.exercise_13_B_1
#print axioms MWG.AdverseSelection.exercise_13_B_1_full
#print axioms MWG.AdverseSelection.exercise_13_B_1_po
#print axioms MWG.AdverseSelection.exercise_13_B_1_nonmono
#print axioms MWG.AdverseSelection.exercise_13_B_2
#print axioms MWG.AdverseSelection.exB_unif_condMean_Iic
#print axioms MWG.AdverseSelection.exercise_13_B_2_instance
#print axioms MWG.AdverseSelection.AntiModel
#print axioms MWG.AdverseSelection.AntiModel.mk
#print axioms MWG.AdverseSelection.AntiModel.dist
#print axioms MWG.AdverseSelection.AntiModel.dens
#print axioms MWG.AdverseSelection.AntiModel.meas
#print axioms MWG.AdverseSelection.AntiModel.anti
#print axioms MWG.AdverseSelection.AntiModel.cont
#print axioms MWG.AdverseSelection.exercise_13_B_3a
#print axioms MWG.AdverseSelection.exercise_13_B_3b
#print axioms MWG.AdverseSelection.AntiModel.measure_acceptSet_pos
#print axioms MWG.AdverseSelection.exercise_13_B_3b_lt
#print axioms MWG.AdverseSelection.exercise_13_B_3c
#print axioms MWG.AdverseSelection.exercise_13_B_3b_instance
#print axioms MWG.AdverseSelection.exercise_13_B_3b_lt_instance
#print axioms MWG.AdverseSelection.exercise_13_B_3c_instance
#print axioms MWG.AdverseSelection.exercise_13_B_3c_counterexample
#print axioms MWG.AdverseSelection.ReducesEmployment
#print axioms MWG.AdverseSelection.IncreasesEmployment
#print axioms MWG.AdverseSelection.budgetOK_iff
#print axioms MWG.AdverseSelection.exB7_reduces_exists
#print axioms MWG.AdverseSelection.exB7_reduces_of
#print axioms MWG.AdverseSelection.exB7_increases_exists
#print axioms MWG.AdverseSelection.exB7_increases_of
#print axioms MWG.AdverseSelection.exB7_pay_emp
#print axioms MWG.AdverseSelection.exB7_pay_unemp
#print axioms MWG.AdverseSelection.exB7_profit_of_empty
#print axioms MWG.AdverseSelection.exercise_13_B_7_reduce
#print axioms MWG.AdverseSelection.MonoModel.levelNull
#print axioms MWG.AdverseSelection.exercise_13_B_7_increase
#print axioms MWG.AdverseSelection.exB7_profit_congr
#print axioms MWG.AdverseSelection.MonoModel.measureReal_acceptSet_lt_one
#print axioms MWG.AdverseSelection.exercise_13_B_7_proposition_13_B_2
#print axioms MWG.AdverseSelection.exercise_13_B_7_instance
#print axioms MWG.AdverseSelection.xNetRev
#print axioms MWG.AdverseSelection.XBudgetOK
#print axioms MWG.AdverseSelection.IsXParetoImprovement
#print axioms MWG.AdverseSelection.xNetRev_const
#print axioms MWG.AdverseSelection.xBudgetOK_const_iff
#print axioms MWG.AdverseSelection.exB8_integral_lt
#print axioms MWG.AdverseSelection.exercise_13_B_8_false
#print axioms MWG.AdverseSelection.exercise_13_B_8
#print axioms MWG.AdverseSelection.exercise_13_B_8_const_x
#print axioms MWG.AdverseSelection.exercise_13_B_8_instance
#print axioms MWG.AdverseSelection.twoPt
#print axioms MWG.AdverseSelection.integral_twoPt
#print axioms MWG.AdverseSelection.twoPt_typeDist
#print axioms MWG.AdverseSelection.meanType_twoPt
#print axioms MWG.AdverseSelection.firmProfit_twoPt
#print axioms MWG.AdverseSelection.exercise_13_B_9_exact
#print axioms MWG.AdverseSelection.exercise_13_B_9
#print axioms MWG.AdverseSelection.exercise_13_B_9_cpo_instance
#print axioms MWG.AdverseSelection.FirmDensity
#print axioms MWG.AdverseSelection.FirmDensity.mk
#print axioms MWG.AdverseSelection.FirmDensity.cont
#print axioms MWG.AdverseSelection.FirmDensity.pos
#print axioms MWG.AdverseSelection.FirmDensity.integrable
#print axioms MWG.AdverseSelection.FirmDensity.total
#print axioms MWG.AdverseSelection.wilHireSet
#print axioms MWG.AdverseSelection.wilDemand
#print axioms MWG.AdverseSelection.wilTail
#print axioms MWG.AdverseSelection.wil_hire_best
#print axioms MWG.AdverseSelection.wilHireSet_eq
#print axioms MWG.AdverseSelection.measurableSet_wilHireSet
#print axioms MWG.AdverseSelection.wilTail_split
#print axioms MWG.AdverseSelection.wilTail_lt
#print axioms MWG.AdverseSelection.wilTail_anti
#print axioms MWG.AdverseSelection.wilTail_nonneg
#print axioms MWG.AdverseSelection.wilTail_pos
#print axioms MWG.AdverseSelection.exercise_13_B_6a
#print axioms MWG.AdverseSelection.exercise_13_B_6b
#print axioms MWG.AdverseSelection.WilsonEconomy
#print axioms MWG.AdverseSelection.WilsonEconomy.mk
#print axioms MWG.AdverseSelection.WilsonEconomy.N
#print axioms MWG.AdverseSelection.WilsonEconomy.g
#print axioms MWG.AdverseSelection.WilsonEconomy.F
#print axioms MWG.AdverseSelection.WilsonEconomy.θl
#print axioms MWG.AdverseSelection.WilsonEconomy.θh
#print axioms MWG.AdverseSelection.WilsonEconomy.r
#print axioms MWG.AdverseSelection.WilsonEconomy.mu
#print axioms MWG.AdverseSelection.WilsonEconomy.zstar
#print axioms MWG.AdverseSelection.WilsonEconomy.supply
#print axioms MWG.AdverseSelection.WilsonEconomy.IsCE
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.mk
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.firms
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.N_pos
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.dist
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.θl_pos
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.meas
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.mono
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.r_nonneg
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.mu_pos
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.zstar_eq
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.zstar_pos
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.ce_ge
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.ce_nonneg
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.supply_mono
#print axioms MWG.AdverseSelection.WilsonEconomy.exercise_13_B_6c
#print axioms MWG.AdverseSelection.WilsonEconomy.offerPay
#print axioms MWG.AdverseSelection.WilsonEconomy.IsSPNE
#print axioms MWG.AdverseSelection.WilsonEconomy.Valid.deviation_of_mu_lt
#print axioms MWG.AdverseSelection.WilsonEconomy.exercise_13_B_6d_i
#print axioms MWG.AdverseSelection.WilsonEconomy.exercise_13_B_6d_ii_necessary
#print axioms MWG.AdverseSelection.WilsonEconomy.exercise_13_B_6d_ii_corrected
#print axioms MWG.AdverseSelection.WilsonEconomy.exercise_13_B_6d_ii_full_employment
#print axioms MWG.AdverseSelection.expDensity
#print axioms MWG.AdverseSelection.wilTail_exp
#print axioms MWG.AdverseSelection.stepR
#print axioms MWG.AdverseSelection.stepEconomy
#print axioms MWG.AdverseSelection.stepEconomy_valid
#print axioms MWG.AdverseSelection.stepR_accept_low
#print axioms MWG.AdverseSelection.stepR_accept_high
#print axioms MWG.AdverseSelection.stepEconomy_mu_low
#print axioms MWG.AdverseSelection.stepEconomy_mu_high
#print axioms MWG.AdverseSelection.stepEconomy_supply_low
#print axioms MWG.AdverseSelection.stepEconomy_supply_high
#print axioms MWG.AdverseSelection.stepEconomy_zstar_low
#print axioms MWG.AdverseSelection.stepEconomy_zstar_high
#print axioms MWG.AdverseSelection.exp_neg_log_two
#print axioms MWG.AdverseSelection.log_two_bounds
#print axioms MWG.AdverseSelection.exercise_13_B_6b_instance
#print axioms MWG.AdverseSelection.exercise_13_B_6_instance
#print axioms MWG.AdverseSelection.exercise_13_B_6d_ii_counterexample
#print axioms MWG.AdverseSelection.testNonTakers
#print axioms MWG.AdverseSelection.IsTestEq
#print axioms MWG.AdverseSelection.exercise_13_C_1
#print axioms MWG.AdverseSelection.exercise_13_C_1_instance
#print axioms MWG.AdverseSelection.SigModel.prodWage
#print axioms MWG.AdverseSelection.SigModel.prodPay
#print axioms MWG.AdverseSelection.SigModel.IsPBEProd
#print axioms MWG.AdverseSelection.SigModel.IsPBEProdRed
#print axioms MWG.AdverseSelection.SigModel.fullPay
#print axioms MWG.AdverseSelection.SigModel.IsFullInfoChoice
#print axioms MWG.AdverseSelection.SigModel.Valid.prodWage_nonneg
#print axioms MWG.AdverseSelection.SigModel.Valid.prodWage_ge
#print axioms MWG.AdverseSelection.SigModel.Valid.exists_isPBEProd_iff
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_separating
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_full_info
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_distorted
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_pooling
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_pooling_low
#print axioms MWG.AdverseSelection.SigModel.prodSigModel
#print axioms MWG.AdverseSelection.SigModel.prodSigModel_valid
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_instance
#print axioms MWG.AdverseSelection.SigModel.prodSigModel3
#print axioms MWG.AdverseSelection.SigModel.prodSigModel3_valid
#print axioms MWG.AdverseSelection.SigModel.exercise_13_C_2_full_info_instance
#print axioms MWG.AdverseSelection.LoanModel
#print axioms MWG.AdverseSelection.LoanModel.mk
#print axioms MWG.AdverseSelection.LoanModel.pG
#print axioms MWG.AdverseSelection.LoanModel.pB
#print axioms MWG.AdverseSelection.LoanModel.lam
#print axioms MWG.AdverseSelection.LoanModel.Pf
#print axioms MWG.AdverseSelection.LoanModel.r
#print axioms MWG.AdverseSelection.LoanModel.rho
#print axioms MWG.AdverseSelection.LoanModel.Valid
#print axioms MWG.AdverseSelection.LoanModel.Valid.mk
#print axioms MWG.AdverseSelection.LoanModel.Valid.pB_pos
#print axioms MWG.AdverseSelection.LoanModel.Valid.lt
#print axioms MWG.AdverseSelection.LoanModel.Valid.pG_le
#print axioms MWG.AdverseSelection.LoanModel.Valid.lam_pos
#print axioms MWG.AdverseSelection.LoanModel.Valid.lam_lt
#print axioms MWG.AdverseSelection.LoanModel.Valid.r_nonneg
#print axioms MWG.AdverseSelection.LoanModel.Valid.rho_gt
#print axioms MWG.AdverseSelection.LoanModel.Valid.good
#print axioms MWG.AdverseSelection.LoanModel.Valid.bad
#print axioms MWG.AdverseSelection.LoanModel.p
#print axioms MWG.AdverseSelection.LoanModel.pbar
#print axioms MWG.AdverseSelection.LoanModel.entPay
#print axioms MWG.AdverseSelection.LoanModel.repay
#print axioms MWG.AdverseSelection.LoanModel.gamePay
#print axioms MWG.AdverseSelection.LoanModel.IsLoanPBE
#print axioms MWG.AdverseSelection.LoanModel.xStar
#print axioms MWG.AdverseSelection.LoanModel.Valid.den_pos
#print axioms MWG.AdverseSelection.LoanModel.Valid.pbar_pos
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_bank_zero_profit
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_i
#print axioms MWG.AdverseSelection.LoanModel.Valid.bad_mimic_iff
#print axioms MWG.AdverseSelection.LoanModel.Valid.xStar_mem
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_ii_separating
#print axioms MWG.AdverseSelection.LoanModel.Valid.goodPay_xStar
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_ii_best
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_ii_statics
#print axioms MWG.AdverseSelection.LoanModel.poolPay
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_iii
#print axioms MWG.AdverseSelection.LoanModel.loanModel
#print axioms MWG.AdverseSelection.LoanModel.loanModel_valid
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_iii_instance
#print axioms MWG.AdverseSelection.LoanModel.exercise_13_C_6b_ii_statics_instance
#print axioms MWG.AdverseSelection.ScrGame
#print axioms MWG.AdverseSelection.ScrGame.mk
#print axioms MWG.AdverseSelection.ScrGame.U
#print axioms MWG.AdverseSelection.ScrGame.P
#print axioms MWG.AdverseSelection.ScrGame.ρ
#print axioms MWG.AdverseSelection.ScrGame.key
#print axioms MWG.AdverseSelection.ScrGame.lam
#print axioms MWG.AdverseSelection.ScrGame.adm
#print axioms MWG.AdverseSelection.ScrGame.Menu
#print axioms MWG.AdverseSelection.ScrGame.Chooses
#print axioms MWG.AdverseSelection.ScrGame.Inj
#print axioms MWG.AdverseSelection.ScrGame.typeProfit
#print axioms MWG.AdverseSelection.ScrGame.profit
#print axioms MWG.AdverseSelection.ScrGame.IsEq
#print axioms MWG.AdverseSelection.ScrGame.chooses_unique
#print axioms MWG.AdverseSelection.ScrGame.exists_chooses
#print axioms MWG.AdverseSelection.ScrGame.chooses_of_strict
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_of_chooses
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_of_not
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_add
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_add_not
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_empty
#print axioms MWG.AdverseSelection.ScrGame.profit_empty
#print axioms MWG.AdverseSelection.ScrGame.IsEq.symm
#print axioms MWG.AdverseSelection.ScrGame.menu_empty
#print axioms MWG.AdverseSelection.ScrGame.IsEq.nonneg
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_capture
#print axioms MWG.AdverseSelection.ScrGame.no_capture_of_other
#print axioms MWG.AdverseSelection.ScrGame.typeProfit_nonneg_of
#print axioms MWG.AdverseSelection.ScrGame.profit_add
#print axioms MWG.AdverseSelection.ScrGame.exists_gap
#print axioms MWG.AdverseSelection.ScrGame.dev_type
#print axioms MWG.AdverseSelection.ScrGame.IsEq.zero
#print axioms MWG.AdverseSelection.ScrGame.IsEq.dev_true
#print axioms MWG.AdverseSelection.ScrGame.IsEq.dev_true'
#print axioms MWG.AdverseSelection.ScrGame.IsEq.dev_false
#print axioms MWG.AdverseSelection.ScrGame.IsEq.dev_true_pos
#print axioms MWG.AdverseSelection.ScrGame.IsEq.dev_both
#print axioms MWG.AdverseSelection.SigModel.prodGame
#print axioms MWG.AdverseSelection.SigModel.surplus
#print axioms MWG.AdverseSelection.SigModel.prodGame_inj
#print axioms MWG.AdverseSelection.SigModel.prodGame_P
#print axioms MWG.AdverseSelection.SigModel.prodGame_zero
#print axioms MWG.AdverseSelection.SigModel.θ_pos
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1
#print axioms MWG.AdverseSelection.SigModel.obsGame
#print axioms MWG.AdverseSelection.SigModel.obsGame_inj
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_observable
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_observable_exists
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_compare
#print axioms MWG.AdverseSelection.SigModel.prod_isEq
#print axioms MWG.AdverseSelection.SigModel.quadModel
#print axioms MWG.AdverseSelection.SigModel.quadModel_cL
#print axioms MWG.AdverseSelection.SigModel.quadModel_cH
#print axioms MWG.AdverseSelection.SigModel.quadModel_valid
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_fullinfo
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_distorted
#print axioms MWG.AdverseSelection.SigModel.linModel9
#print axioms MWG.AdverseSelection.SigModel.linModel9_valid
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_nonexistence
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_1_observable_instance
#print axioms MWG.AdverseSelection.RSModel
#print axioms MWG.AdverseSelection.RSModel.mk
#print axioms MWG.AdverseSelection.RSModel.qS
#print axioms MWG.AdverseSelection.RSModel.qR
#print axioms MWG.AdverseSelection.RSModel.a₁
#print axioms MWG.AdverseSelection.RSModel.a₂
#print axioms MWG.AdverseSelection.RSModel.h
#print axioms MWG.AdverseSelection.RSModel.ρS
#print axioms MWG.AdverseSelection.RSModel.ρR
#print axioms MWG.AdverseSelection.RSModel.lam
#print axioms MWG.AdverseSelection.RSModel.q
#print axioms MWG.AdverseSelection.RSModel.V
#print axioms MWG.AdverseSelection.RSModel.Pr
#print axioms MWG.AdverseSelection.RSModel.abar
#print axioms MWG.AdverseSelection.RSModel.game
#print axioms MWG.AdverseSelection.RSModel.Valid
#print axioms MWG.AdverseSelection.RSModel.Valid.mk
#print axioms MWG.AdverseSelection.RSModel.Valid.qR_pos
#print axioms MWG.AdverseSelection.RSModel.Valid.q_lt
#print axioms MWG.AdverseSelection.RSModel.Valid.qS_lt
#print axioms MWG.AdverseSelection.RSModel.Valid.lam_pos
#print axioms MWG.AdverseSelection.RSModel.Valid.lam_lt
#print axioms MWG.AdverseSelection.RSModel.Valid.a_lt
#print axioms MWG.AdverseSelection.RSModel.Valid.h_mono
#print axioms MWG.AdverseSelection.RSModel.Valid.h_conv
#print axioms MWG.AdverseSelection.RSModel.Valid.h_cont
#print axioms MWG.AdverseSelection.RSModel.q_true
#print axioms MWG.AdverseSelection.RSModel.q_false
#print axioms MWG.AdverseSelection.RSModel.Valid.q_pos
#print axioms MWG.AdverseSelection.RSModel.Valid.q_lt_one
#print axioms MWG.AdverseSelection.RSModel.game_inj
#print axioms MWG.AdverseSelection.RSModel.V_diag
#print axioms MWG.AdverseSelection.RSModel.Pr_diag
#print axioms MWG.AdverseSelection.RSModel.abar_lt
#print axioms MWG.AdverseSelection.RSModel.Pr_le
#print axioms MWG.AdverseSelection.RSModel.Pr_lt
#print axioms MWG.AdverseSelection.RSModel.V_add
#print axioms MWG.AdverseSelection.RSModel.Pr_cont
#print axioms MWG.AdverseSelection.RSModel.game_zero
#print axioms MWG.AdverseSelection.RSModel.exists_improve
#print axioms MWG.AdverseSelection.RSModel.rs_characterization
#print axioms MWG.AdverseSelection.RSModel.rs_point_lt
#print axioms MWG.AdverseSelection.RSModel.rs_point_unique
#print axioms MWG.AdverseSelection.RSModel.rs_isEq
#print axioms MWG.AdverseSelection.RSModel.rs_no_eq
#print axioms MWG.AdverseSelection.RSModel.exp_ge_tangent
#print axioms MWG.AdverseSelection.RSModel.log9_add_log4
#print axioms MWG.AdverseSelection.RSModel.log4_lt_log9
#print axioms MWG.AdverseSelection.RSModel.log_valid
#print axioms MWG.AdverseSelection.RSModel.log_isEq
#print axioms MWG.AdverseSelection.RSModel.log_no_eq
#print axioms MWG.AdverseSelection.RSModel.policyWealth
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2a
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2a_log
#print axioms MWG.AdverseSelection.RSModel.insModel
#print axioms MWG.AdverseSelection.RSModel.ins_participation
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2b
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2b_exists
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2b_nonexistence
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_2b_outcome
#print axioms MWG.AdverseSelection.rnProb
#print axioms MWG.AdverseSelection.rnMean
#print axioms MWG.AdverseSelection.rnGame
#print axioms MWG.AdverseSelection.RnGame.inj
#print axioms MWG.AdverseSelection.RnGame.P_eq
#print axioms MWG.AdverseSelection.RnGame.zero
#print axioms MWG.AdverseSelection.exercise_13_D_3b
#print axioms MWG.AdverseSelection.exercise_13_D_3b_exists
#print axioms MWG.AdverseSelection.exercise_13_D_3a
#print axioms MWG.AdverseSelection.exercise_13_D_3a_exists
#print axioms MWG.AdverseSelection.RSModel.labModel
#print axioms MWG.AdverseSelection.RSModel.lab_participation
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_3c
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_3c_exists
#print axioms MWG.AdverseSelection.RSModel.exercise_13_D_3c_nonexistence
#print axioms MWG.AdverseSelection.SigModel.offered
#print axioms MWG.AdverseSelection.SigModel.ChoosesS
#print axioms MWG.AdverseSelection.SigModel.gross
#print axioms MWG.AdverseSelection.SigModel.feProfit
#print axioms MWG.AdverseSelection.SigModel.IsFreeEntryEq
#print axioms MWG.AdverseSelection.SigModel.choosesS_unique
#print axioms MWG.AdverseSelection.SigModel.exists_choosesS
#print axioms MWG.AdverseSelection.SigModel.choosesS_of_strict
#print axioms MWG.AdverseSelection.SigModel.offered_finite
#print axioms MWG.AdverseSelection.SigModel.offered_update_none
#print axioms MWG.AdverseSelection.SigModel.ncard_pos_of
#print axioms MWG.AdverseSelection.SigModel.update_finite
#print axioms MWG.AdverseSelection.SigModel.IsFreeEntryEq.no_entry
#print axioms MWG.AdverseSelection.SigModel.IsFreeEntryEq.active_nonneg
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_4
#print axioms MWG.AdverseSelection.SigModel.fe_no_eq_of_pooling
#print axioms MWG.AdverseSelection.SigModel.feProfile
#print axioms MWG.AdverseSelection.SigModel.fe_exists
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_4_lin
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_4_pair
#print axioms MWG.AdverseSelection.SigModel.exercise_13_D_4_nonexistence
#print axioms MWG.AdverseSelection.aaθ
#print axioms MWG.AdverseSelection.aaK
#print axioms MWG.AdverseSelection.aaGame
#print axioms MWG.AdverseSelection.aaM0
#print axioms MWG.AdverseSelection.aaMean
#print axioms MWG.AdverseSelection.aa_payoff
#print axioms MWG.AdverseSelection.aaMean_ge
#print axioms MWG.AdverseSelection.aaMean_le
#print axioms MWG.AdverseSelection.aa_belief_univ
#print axioms MWG.AdverseSelection.aa_nash_iff
#print axioms MWG.AdverseSelection.aa_eqResponses
#print axioms MWG.AdverseSelection.aa_u1
#print axioms MWG.AdverseSelection.aaMean_pointMass
#print axioms MWG.AdverseSelection.aa_resp_mem
#print axioms MWG.AdverseSelection.aa_u1_le
#print axioms MWG.AdverseSelection.aa_passes_ic
#print axioms MWG.AdverseSelection.aaPrior
#print axioms MWG.AdverseSelection.aaPool
#print axioms MWG.AdverseSelection.aaPool_belief
#print axioms MWG.AdverseSelection.aaE1
#print axioms MWG.AdverseSelection.aaE2
#print axioms MWG.AdverseSelection.aaBel1
#print axioms MWG.AdverseSelection.aaBel2
#print axioms MWG.AdverseSelection.aaResp
#print axioms MWG.AdverseSelection.aaBel1_belief
#print axioms MWG.AdverseSelection.aaBel2_belief
#print axioms MWG.AdverseSelection.aaResp1
#print axioms MWG.AdverseSelection.aaResp2
#print axioms MWG.AdverseSelection.aa_payoff1
#print axioms MWG.AdverseSelection.aa_payoff2
#print axioms MWG.AdverseSelection.aa_pbe1
#print axioms MWG.AdverseSelection.aa_pbe2
#print axioms MWG.AdverseSelection.exercise_13_AA_1
