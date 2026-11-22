/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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
