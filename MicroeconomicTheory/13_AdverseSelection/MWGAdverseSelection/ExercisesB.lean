/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Constrained
import MWGAdverseSelection.Efficiency
import MWGAdverseSelection.Uniform

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
