/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.StrassenFinite
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# A martingale coupling as a weak limit

Preparation for Proposition 6.D.2, (i) ⇒ (ii) (MWG, p. 199). For the grids of mesh
`x̄/(n+1)`, the finite martingale couplings of `StrassenFinite` all live on the compact square
`[-x̄, 2x̄]²`. By Prokhorov's theorem (Mathlib: probability measures giving zero mass outside a
fixed compact set form a compact set for the weak topology) the sequence has a cluster point
`π`. Expectations of bounded continuous functions are continuous in the weak topology, and
along the sequence the marginal expectations converge to those under `F` and `G` (uniform
continuity on the square), while the martingale expectations `∫ φ(x)(y - x)` vanish
identically. Hence `π` has marginals `F` and `G` and `∫ φ(x)(y - x) dπ = 0` for every bounded
continuous `φ`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BoundedContinuousFunction

/-- A cluster point of a sequence whose image under a continuous map converges is sent to the
limit. -/
theorem eq_of_mapClusterPt_of_tendsto {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {P : ℕ → X} {Q : X} (hQ : MapClusterPt Q atTop P) {Φ : X → Y}
    (hΦ : Continuous Φ) {c : Y} (hc : Tendsto (Φ ∘ P) atTop (𝓝 c)) : Φ Q = c := by
  have h1 : MapClusterPt (Φ Q) atTop (Φ ∘ P) := hQ.continuousAt_comp hΦ.continuousAt
  exact eq_of_nhds_neBot (h1.neBot.mono (inf_le_inf_left _ hc))

/-- The hat-weighted averages of `g` at points within `h` of the grid points converge to
`∫ g dF` as the mesh `x̄/(n+1)` goes to zero. -/
theorem tendsto_hat_average {μ : Measure ℝ} [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M)
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 M) {g : ℝ → ℝ} (hg : Continuous g) (y : ℕ → ℕ → ℝ)
    (hy : ∀ n j, |y n j - gridPt (M / (n + 1)) j| ≤ M / (n + 1)) :
    Tendsto (fun n : ℕ => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
      hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * g (y n j) ∂μ) atTop
      (𝓝 (∫ t, g t ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := (isCompact_Icc (a := -M) (b := 2 * M)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / 2) (by linarith)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * M / δ)
  refine ⟨n0, fun n hn => ?_⟩
  set h := M / (n + 1) with hh_def
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hh : 0 < h := div_pos hM hn1
  have hhM : h ≤ M := div_le_self hM.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hNh : ((n + 1 : ℕ) : ℝ) * h = M := by rw [hh_def]; push_cast; field_simp
  have h2h : 2 * h < δ := by
    have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hδ] at hn0
    rw [hh_def, ← mul_div_assoc, div_lt_iff₀ hn1]
    nlinarith
  have hae' : ∀ᵐ t ∂μ, t ∈ Ioc 0 (((n + 1 : ℕ) : ℝ) * h) := by rwa [hNh]
  have hint : Integrable (fun t => ∑ j ∈ Finset.range (n + 1 + 1),
      hatFn h (gridPt h j) t * g (y n j)) μ :=
    integrable_finsetSum _ fun j _ =>
      (integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)).mul_const _
  rw [Real.dist_eq, ← integral_sub hint (integrable_of_continuous_ae_Ioc hae hg)]
  have hbound : ∀ᵐ t ∂μ, ‖∑ j ∈ Finset.range (n + 1 + 1),
      hatFn h (gridPt h j) t * g (y n j) - g t‖ ≤ ε / 2 := by
    filter_upwards [hae'] with t ht
    rw [Real.norm_eq_abs]
    refine hatFn_sum_approx hh ht.1 ht.2 g (y n) fun j hj hp => ?_
    have hjN : (j : ℝ) ≤ n + 1 := by
      have := Finset.mem_range.mp hj
      exact_mod_cast Nat.lt_succ_iff.mp this
    have hx0 : 0 ≤ gridPt h j := by unfold gridPt; positivity
    have hxM : gridPt h j ≤ M := by
      rw [← hNh]; unfold gridPt; push_cast
      exact mul_le_mul_of_nonneg_right hjN hh.le
    have h1 := abs_sub_lt_of_hatFn_pos hh hp
    have h2 := hy n j
    rw [abs_lt] at h1
    rw [abs_le] at h2
    have hmemy : y n j ∈ Icc (-M) (2 * M) := ⟨by linarith, by linarith⟩
    have hmemt : t ∈ Icc (-M) (2 * M) := ⟨by linarith [ht.1], by linarith [ht.2, hNh]⟩
    have hd : dist (y n j) t < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδg _ hmemy _ hmemt hd
    rw [Real.dist_eq] at this
    exact this.le
  have := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  linarith

/-- The truncation `max(-c, min(z, c))`. -/
noncomputable def truncAt (c z : ℝ) : ℝ := max (-c) (min z c)

theorem continuous_truncAt (c : ℝ) : Continuous (truncAt c) := by
  unfold truncAt; fun_prop

theorem abs_truncAt_le {c : ℝ} (hc : 0 ≤ c) (z : ℝ) : |truncAt c z| ≤ c := by
  unfold truncAt
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem truncAt_eq {c z : ℝ} (h : |z| ≤ c) : truncAt c z = z := by
  unfold truncAt
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

/-- **Existence of a martingale coupling.** If `F` (`μ`) dominates `G` (`ν`) for every
nondecreasing concave utility on `ℝ`, with equal means, both concentrated on `(0, x̄]`, there
is a Borel probability measure `π` on `ℝ²` concentrated on `[-x̄, 2x̄]²` with marginals `F` and
`G` and `∫ φ(x)(y - x) dπ = 0` for every bounded continuous `φ`. -/
theorem exists_martingale_coupling {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 < M)
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioc 0 M) (hν : ∀ᵐ t ∂ν, t ∈ Ioc 0 M)
    (hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ)
    (hmean : ∫ t, t ∂μ = ∫ t, t ∂ν) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      (∀ᵐ p ∂π, p.1 ∈ Icc (-M) (2 * M) ∧ p.2 ∈ Icc (-M) (2 * M)) ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ φ : ℝ →ᵇ ℝ, ∫ p, φ p.1 * (p.2 - p.1) ∂π = 0 := by
  set K : Set (ℝ × ℝ) := Icc (-M) (2 * M) ×ˢ Icc (-M) (2 * M) with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hfin (n : ℕ) := exists_grid_martingale_coupling (μ := μ) (ν := ν)
    (h := M / (n + 1)) (div_pos hM (by positivity)) (N := n + 1)
    (by
      have : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
      rwa [this])
    (by
      have : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
      rwa [this])
    hdom hmean
  choose π hprob hsupp hfst hsnd hmart using hfin
  have hMn (n : ℕ) : M / (n + 1) ≤ M :=
    div_le_self hM.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hNh (n : ℕ) : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
  have hπK (n : ℕ) : ∀ᵐ p ∂(π n), p ∈ K := by
    filter_upwards [hsupp n] with p hp
    rw [hNh] at hp
    have := hMn n
    have h0 : 0 ≤ M / (n + 1) := div_nonneg hM.le (by positivity)
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  let P : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n => ⟨π n, hprob n⟩
  set S : Set (ProbabilityMeasure (ℝ × ℝ)) := {R | ∀ _ : ℕ, R Kᶜ ≤ (fun _ : ℕ => (0 : ℝ≥0)) 0}
  have hS : IsCompact S :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le (u := fun _ => 0)
      (K := fun _ => K) tendsto_const_nhds (fun _ => hKc) (Or.inr monotone_const)
  have hPS (n : ℕ) : P n ∈ S := by
    intro _
    rw [nonpos_iff_eq_zero, ProbabilityMeasure.null_iff_toMeasure_null]
    exact measure_eq_zero_iff_ae_notMem.mpr ((hπK n).mono fun p hp hn => hn hp)
  obtain ⟨Q, hQS, hQ⟩ := hS.exists_mapClusterPt (f := atTop) (u := P)
    (tendsto_principal.mpr (Eventually.of_forall hPS))
  have hQK : ∀ᵐ p ∂(Q : Measure (ℝ × ℝ)), p ∈ K := by
    have := hQS 0
    rw [nonpos_iff_eq_zero, ProbabilityMeasure.null_iff_toMeasure_null] at this
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with p hp
    exact not_not.mp hp
  -- passing a bounded continuous test function to the limit
  have hlim (F : ℝ × ℝ →ᵇ ℝ) (c : ℝ)
      (hc : Tendsto (fun n => ∫ p, F p ∂(π n)) atTop (𝓝 c)) :
      ∫ p, F p ∂(Q : Measure (ℝ × ℝ)) = c :=
    eq_of_mapClusterPt_of_tendsto hQ
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F) hc
  have hQprob : IsProbabilityMeasure (Q : Measure (ℝ × ℝ)) := inferInstance
  refine ⟨Q, hQprob, hQK.mono fun p hp => hp, ?_, ?_, fun φ => ?_⟩
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    refine hlim (f.compContinuous ⟨Prod.fst, continuous_fst⟩) _ ?_
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    have e : (fun n => ∫ p, f p.1 ∂(π n)) = fun n => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
        hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * f (gridCtr μ (M / (n + 1)) j) ∂μ :=
      funext fun n => by rw [hfst n f, sum_gridMass_mul (by rw [hNh]; exact hμ)]
    rw [e]
    exact tendsto_hat_average hM hμ f.continuous (fun n j => gridCtr μ (M / (n + 1)) j)
      fun n j => abs_gridCtr_sub_le (div_pos hM (by positivity)) (N := n + 1)
        (by rw [hNh]; exact hμ) j
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    refine hlim (f.compContinuous ⟨Prod.snd, continuous_snd⟩) _ ?_
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    have e : (fun n => ∫ p, f p.2 ∂(π n)) = fun n => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
        hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * f (gridPt (M / (n + 1)) j) ∂ν :=
      funext fun n => by rw [hsnd n f, sum_gridMass_mul (by rw [hNh]; exact hν)]
    rw [e]
    exact tendsto_hat_average hM hν f.continuous (fun n j => gridPt (M / (n + 1)) j)
      fun n j => by simp [div_nonneg hM.le (by positivity : (0 : ℝ) ≤ n + 1)]
  · -- the truncated martingale test function
    set c := 3 * M
    let G : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => φ p.1 * truncAt c (p.2 - p.1))
      ((φ.continuous.comp continuous_fst).mul ((continuous_truncAt c).comp
        (continuous_snd.sub continuous_fst))) (‖φ‖ * c) (fun p => by
          rw [norm_mul]
          exact mul_le_mul (φ.norm_coe_le_norm _) (by
            rw [Real.norm_eq_abs]; exact abs_truncAt_le (by linarith) _)
            (norm_nonneg _) (norm_nonneg _))
    have hGeq (R : Measure (ℝ × ℝ)) (hR : ∀ᵐ p ∂R, p ∈ K) :
        ∫ p, G p ∂R = ∫ p, φ p.1 * (p.2 - p.1) ∂R := by
      apply integral_congr_ae
      filter_upwards [hR] with p hp
      change φ p.1 * truncAt c (p.2 - p.1) = _
      rw [truncAt_eq]
      rw [abs_le]
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
      constructor <;> linarith
    rw [← hGeq _ hQK]
    refine hlim G 0 ?_
    simp_rw [hGeq _ (hπK _), hmart]
    exact tendsto_const_nhds

end MWG.ChoiceUnderUncertainty
