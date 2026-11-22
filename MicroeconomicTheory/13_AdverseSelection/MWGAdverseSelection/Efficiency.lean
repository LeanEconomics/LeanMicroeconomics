/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Regular
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac.Basic

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
