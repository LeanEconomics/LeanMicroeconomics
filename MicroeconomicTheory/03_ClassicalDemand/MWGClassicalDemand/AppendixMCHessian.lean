/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMJ

/-!
# Mathematical Appendix M.C: Hessian characterisations

MWG, Theorems M.C.2 and M.C.4, pp. 933-935. As footnote 4 requires, the domain `A` is open
(and convex). Instead of twice continuous differentiability we assume that `f` is
differentiable on `A` and that `∇f` is differentiable at every point `y ∈ A` with second
derivative `D2 y`; `z·D²f(y)z = D2 y z z` (`hessianMatrix_quad`).

* Theorem M.C.2: `f` is concave iff `D²f(y)` is negative semidefinite on `A`; negative
  definiteness on `A` gives strict concavity.
* Theorem M.C.4: quasiconcavity implies negative semidefiniteness of `D²f(y)` on
  `{z : ∇f(y)·z = 0}`; negative definiteness there gives strict quasiconcavity. The printed
  converse of the first part ("if and only if") is false: `x⁴` (`theorem_M_C_4_if_false`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N : ℕ}

/-- The derivative of `t ↦ ∇f(x + tz)·z` at any `s`, from the second derivative at `x + sz`. -/
theorem mc_line_second_deriv_at {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x z : Fin N → ℝ} {s : ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) D2 (x + s • z)) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • z) z) (D2 z z) s := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • z) z s := by
    simpa using ((hasDerivAt_id s).smul_const z).const_add x
  have hc := h2.comp_hasDerivAt s h1
  have := hc.clm_apply (hasDerivAt_const s z)
  simpa using this

/-- A positive second directional derivative at `x` puts `f` strictly above its tangent line
along `z`, just to the right of `0`. -/
theorem mc_eventually_gt_of_quad_pos {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {x z : Fin N → ℝ}
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (h2 : HasFDerivAt (fderiv ℝ f) D2 x)
    (hpos : 0 < D2 z z) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f x + t * fderiv ℝ f x z < f (x + t • z) := by
  have hψ := mj_line_second_deriv h2 z
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), fderiv ℝ f x z < fderiv ℝ f (x + t • z) z := by
    filter_upwards [hψ.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos),
      self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr ht0)).mp ht
    linarith
  obtain ⟨δ, hδ, hδset⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hright
  obtain ⟨ε, hε, hεset⟩ := Metric.eventually_nhds_iff.mp (mj_line_deriv_eventually hdiff z)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hε)] with t ht
  have htδ : t < δ := ht.2.trans_le (min_le_left _ _)
  have htε : t < ε := ht.2.trans_le (min_le_right _ _)
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivAt (fun s : ℝ => f (x + s • z) - s * fderiv ℝ f x z)
      (fderiv ℝ f (x + s • z) z - fderiv ℝ f x z) s := by
    intro s hs
    have hd := hεset (show dist s 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; linarith [hs.2])
    exact (hd.sub ((hasDerivAt_id s).mul_const (fderiv ℝ f x z))).congr_deriv (by simp)
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => f (x + s • z) - s * fderiv ℝ f x z)
    (fun s => fderiv ℝ f (x + s • z) z - fderiv ℝ f x z) ht.1
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => hder s ⟨hs.1.le, hs.2.le⟩)
  have hcpos : 0 < fderiv ℝ f (x + c • z) z - fderiv ℝ f x z := by
    exact sub_pos.mpr (hδset ⟨hc.1, hc.2.trans htδ⟩)
  rw [hcs, sub_zero, lt_div_iff₀ ht.1, zero_mul] at hcpos
  simp only [zero_smul, add_zero, zero_mul, sub_zero] at hcpos
  linarith

/-- **Theorem M.C.2** (MWG, p. 933). On an open convex set, `f` is concave if and only if
`D²f(y)` is negative semidefinite at every `y ∈ A`. -/
theorem theorem_M_C_2 {A : Set (Fin N → ℝ)} (hAo : IsOpen A) (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ y ∈ A, DifferentiableAt ℝ f y) (h2 : ∀ y ∈ A, HasFDerivAt (fderiv ℝ f) (D2 y) y) :
    ConcaveOn ℝ A f ↔ ∀ y ∈ A, NegSemidef (hessianMatrix (D2 y)) := by
  have hf' : ∀ y ∈ A, HasFDerivAt f (fderiv ℝ f y) y := fun y hy => (hf y hy).hasFDerivAt
  constructor
  · intro hc y hy z
    rw [hessianMatrix_quad]
    by_contra hpos
    push Not at hpos
    have hdiff : ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ f w :=
      Filter.mem_of_superset (hAo.mem_nhds hy) fun w hw => hf w hw
    have hev := mc_eventually_gt_of_quad_pos hdiff (h2 y hy) hpos
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • z ∈ A := by
      have hpath : Tendsto (fun t : ℝ => y + t • z) (𝓝 0) (𝓝 y) := by
        have : Continuous (fun t : ℝ => y + t • z) := by fun_prop
        simpa using this.tendsto 0
      exact (hpath.eventually (hAo.mem_nhds hy)).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ht, htA⟩ := (hev.and hmem).exists
    have := theorem_M_C_1_necessity hf' hc hy htA
    rw [map_smul, smul_eq_mul] at this
    linarith
  · intro hnsd
    apply theorem_M_C_1_sufficiency (f' := fun y => fderiv ℝ f y) hA
    intro x hx z hxz
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • z ∈ A := by
      intro t ht
      have : x + t • z = t • (x + z) + (1 - t) • x := by module
      rw [this]
      exact hA hxz hx ht.1 (by linarith [ht.2]) (by ring)
    have hψ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • z) z) (D2 (x + t • z) z z) t :=
      fun t ht => mc_line_second_deriv_at (h2 _ (hseg t ht))
    have hψle : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ f (x + t • z) z ≤ fderiv ℝ f x z := by
      intro t ht
      rcases ht.1.lt_or_eq with ht0 | ht0
      · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
          (fun s : ℝ => fderiv ℝ f (x + s • z) z) (fun s => D2 (x + s • z) z z) ht0
          (fun s hs => (hψ s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt.continuousWithinAt)
          (fun s hs => hψ s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
        have hneg : D2 (x + c • z) z z ≤ 0 := by
          have := hnsd _ (hseg c ⟨hc.1.le, hc.2.le.trans ht.2⟩) z
          rwa [hessianMatrix_quad] at this
        rw [hcs, div_nonpos_iff] at hneg
        simp only [zero_smul, add_zero, sub_zero] at hneg
        rcases hneg with h | h <;> linarith [h.1, h.2]
      · rw [← ht0, zero_smul, add_zero]
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
      (fun s : ℝ => f (x + s • z) - s * fderiv ℝ f x z)
      (fun s => fderiv ℝ f (x + s • z) z - fderiv ℝ f x z) one_pos
      (fun s hs => ((mc_line_hasDerivAt_at (hf' _ (hseg s hs))).sub
        ((hasDerivAt_id s).mul_const _)).continuousAt.continuousWithinAt)
      (fun s hs => ((mc_line_hasDerivAt_at (hf' _ (hseg s ⟨hs.1.le, hs.2.le⟩))).sub
          ((hasDerivAt_id s).mul_const (fderiv ℝ f x z))).congr_deriv (by simp))
    have := hψle c ⟨hc.1.le, hc.2.le⟩
    simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, div_one] at hcs
    linarith

/-- **Theorem M.C.2** (MWG, p. 933), strict part. If `D²f(y)` is negative definite at every
`y ∈ A`, then `f` is strictly concave on `A`. -/
theorem theorem_M_C_2_strict {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ y ∈ A, DifferentiableAt ℝ f y) (h2 : ∀ y ∈ A, HasFDerivAt (fderiv ℝ f) (D2 y) y)
    (hnd : ∀ y ∈ A, NegDef (hessianMatrix (D2 y))) : StrictConcaveOn ℝ A f := by
  have hf' : ∀ y ∈ A, HasFDerivAt f (fderiv ℝ f y) y := fun y hy => (hf y hy).hasFDerivAt
  apply theorem_M_C_1_strict (f' := fun y => fderiv ℝ f y) hA
  intro x hx z hz hxz
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • z ∈ A := by
    intro t ht
    have : x + t • z = t • (x + z) + (1 - t) • x := by module
    rw [this]
    exact hA hxz hx ht.1 (by linarith [ht.2]) (by ring)
  have hψ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • z) z) (D2 (x + t • z) z z) t :=
    fun t ht => mc_line_second_deriv_at (h2 _ (hseg t ht))
  have hψlt : ∀ t ∈ Set.Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • z) z < fderiv ℝ f x z := by
    intro t ht
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
      (fun s : ℝ => fderiv ℝ f (x + s • z) z) (fun s => D2 (x + s • z) z z) ht.1
      (fun s hs => (hψ s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => hψ s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    have hneg : D2 (x + c • z) z z < 0 := by
      have := hnd _ (hseg c ⟨hc.1.le, hc.2.le.trans ht.2⟩) z hz
      rwa [hessianMatrix_quad] at this
    rw [hcs, div_neg_iff] at hneg
    simp only [zero_smul, add_zero, sub_zero] at hneg
    rcases hneg with h | h
    · linarith [h.2, ht.1]
    · linarith [h.1]
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => f (x + s • z) - s * fderiv ℝ f x z)
    (fun s => fderiv ℝ f (x + s • z) z - fderiv ℝ f x z) one_pos
    (fun s hs => ((mc_line_hasDerivAt_at (hf' _ (hseg s hs))).sub
      ((hasDerivAt_id s).mul_const _)).continuousAt.continuousWithinAt)
    (fun s hs => ((mc_line_hasDerivAt_at (hf' _ (hseg s ⟨hs.1.le, hs.2.le⟩))).sub
        ((hasDerivAt_id s).mul_const (fderiv ℝ f x z))).congr_deriv (by simp))
  have := hψlt c ⟨hc.1, hc.2.le⟩
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, div_one] at hcs
  linarith

/-- The second derivative of `-f`. -/
theorem mc_neg_second_deriv {f : (Fin N → ℝ) → ℝ}
    {D2 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} {y : Fin N → ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) D2 y) : HasFDerivAt (fderiv ℝ (-f)) (-D2) y := by
  have : fderiv ℝ (-f) = -fderiv ℝ f := funext fun w => fderiv_neg
  rw [this]
  exact h2.neg

/-- **Theorem M.C.4** (MWG, p. 935), the direction that holds. If `f` is quasiconcave on the
open set `A`, then for every `y ∈ A`, `z·D²f(y)z ≤ 0` whenever `∇f(y)·z = 0`. -/
theorem theorem_M_C_4_necessity {A : Set (Fin N → ℝ)} (hAo : IsOpen A)
    {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ y ∈ A, DifferentiableAt ℝ f y) (h2 : ∀ y ∈ A, HasFDerivAt (fderiv ℝ f) (D2 y) y)
    (hq : QuasiconcaveOn ℝ A f) :
    ∀ y ∈ A, ∀ z, fderiv ℝ f y z = 0 → D2 y z z ≤ 0 := by
  intro y hy z hz
  by_contra hpos
  push Not at hpos
  have hdiff : ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ f w :=
    Filter.mem_of_superset (hAo.mem_nhds hy) fun w hw => hf w hw
  have hpos' : 0 < D2 y (-z) (-z) := by simpa using hpos
  have hz' : fderiv ℝ f y (-z) = 0 := by rw [map_neg, hz, neg_zero]
  have h1 := mc_eventually_gt_of_quad_pos hdiff (h2 y hy) hpos
  have h2' := mc_eventually_gt_of_quad_pos hdiff (h2 y hy) hpos'
  have hmem : ∀ v : Fin N → ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v ∈ A := by
    intro v
    have hpath : Tendsto (fun t : ℝ => y + t • v) (𝓝 0) (𝓝 y) := by
      have : Continuous (fun t : ℝ => y + t • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hpath.eventually (hAo.mem_nhds hy)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨⟨ha, hb⟩, hA1⟩, hA2⟩ := (((h1.and h2').and (hmem z)).and (hmem (-z))).exists
  rw [hz, mul_zero, add_zero] at ha
  rw [hz', mul_zero, add_zero] at hb
  have hmid := (quasiconcaveOn_iff_min_le.mp hq).2 hA1 hA2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • (y + t • z) + (1 / 2 : ℝ) • (y + t • -z) = y := by module
  rw [heq] at hmid
  rcases min_le_iff.mp hmid with h | h <;> linarith

/-- **Theorem M.C.4** (MWG, p. 935), strict part. If, at every `y ∈ A` (open and convex),
`z·D²f(y)z < 0` for all `z ≠ 0` with `∇f(y)·z = 0`, then `f` is strictly quasiconcave. -/
theorem theorem_M_C_4_strict {A : Set (Fin N → ℝ)} (hAo : IsOpen A) (hA : Convex ℝ A)
    {f : (Fin N → ℝ) → ℝ} {D2 : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ y ∈ A, DifferentiableAt ℝ f y) (h2 : ∀ y ∈ A, HasFDerivAt (fderiv ℝ f) (D2 y) y)
    (hnd : ∀ y ∈ A, ∀ z, z ≠ 0 → fderiv ℝ f y z = 0 → D2 y z z < 0) :
    StrictlyQuasiconcaveOn A f := by
  rw [strictlyQuasiconcaveOn_iff_min]
  refine ⟨hA, fun x hx x' hx' hne α h0 h1 => ?_⟩
  by_contra hle
  push Not at hle
  set d := x - x' with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  set φ : ℝ → ℝ := fun t => f (x' + t • d) with hφ
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x' + t • d ∈ A := by
    intro t ht
    have : x' + t • d = t • x + (1 - t) • x' := by rw [hd]; module
    rw [this]
    exact hA hx hx' ht.1 (by linarith [ht.2]) (by ring)
  have hφd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (fderiv ℝ f (x' + t • d) d) t :=
    fun t ht => mc_line_hasDerivAt_at (hf _ (hseg t ht)).hasFDerivAt
  have hcont : ContinuousOn φ (Set.Icc 0 1) :=
    fun t ht => (hφd t ht).continuousAt.continuousWithinAt
  have hφα : φ α = f (α • x + (1 - α) • x') := by
    simp only [hφ, hd]
    congr 1
    module
  have hφ0 : φ 0 = f x' := by simp [hφ]
  have hφ1 : φ 1 = f x := by simp [hφ, hd]
  obtain ⟨s0, hs0, hmin0⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont
  -- an interior minimizer of `φ` on `[0, 1]`
  obtain ⟨s, hs, hmin⟩ : ∃ s ∈ Set.Ioo (0 : ℝ) 1, IsMinOn φ (Set.Icc 0 1) s := by
    by_cases hs : s0 ∈ Set.Ioo (0 : ℝ) 1
    · exact ⟨s0, hs, hmin0⟩
    · refine ⟨α, ⟨h0, h1⟩, fun t ht => ?_⟩
      have hend : φ α ≤ φ s0 := by
        rcases hs0.1.lt_or_eq with h | h
        · have : s0 = 1 := by
            by_contra h'
            exact hs ⟨h, lt_of_le_of_ne hs0.2 h'⟩
          rw [this, hφα, hφ1]
          exact hle.trans (min_le_left _ _)
        · rw [← h, hφα, hφ0]
          exact hle.trans (min_le_right _ _)
      exact hend.trans (hmin0 ht)
  set y := x' + s • d with hy
  have hyA := hseg s ⟨hs.1.le, hs.2.le⟩
  have hloc : IsLocalMin φ s :=
    Filter.mem_of_superset (Icc_mem_nhds hs.1 hs.2) fun t ht => hmin ht
  have hgrad : fderiv ℝ f y d = 0 := hloc.hasDerivAt_eq_zero (hφd s ⟨hs.1.le, hs.2.le⟩)
  have hneg := hnd y hyA d hd0 hgrad
  have hdiff : ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ (-f) w :=
    Filter.mem_of_superset (hAo.mem_nhds hyA) fun w hw => (hf w hw).neg
  have hpos : 0 < (-D2 y) d d := by simpa using hneg
  have hev := mc_eventually_gt_of_quad_pos hdiff (mc_neg_second_deriv (h2 y hyA)) hpos
  have hfd : fderiv ℝ (-f) y d = 0 := by
    rw [show fderiv ℝ (-f) y = -fderiv ℝ f y from fderiv_neg]
    simp [hgrad]
  obtain ⟨t, ht, ht0, ht1⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - s by
    linarith [hs.2]))).exists
  rw [hfd, mul_zero, add_zero] at ht
  have hst : φ s ≤ φ (s + t) := hmin ⟨by linarith [hs.1], by linarith⟩
  have : y + t • d = x' + (s + t) • d := by rw [hy]; module
  simp only [Pi.neg_apply, neg_lt_neg_iff] at ht
  rw [this] at ht
  exact absurd hst (not_le.mpr ht)

/-- **Theorem M.C.4** (MWG, p. 935): the printed "if" direction is false. `f(x) = x⁴` on `ℝ`
satisfies `z f''(x) z ≤ 0` whenever `f'(x) z = 0` (only `z = 0` qualifies at `x ≠ 0`, and
`f''(0) = 0`), but it is not quasiconcave. -/
theorem theorem_M_C_4_if_false :
    (∀ x z : ℝ, deriv (fun x : ℝ => x ^ 4) x * z = 0 →
      z * deriv (deriv fun x : ℝ => x ^ 4) x * z ≤ 0) ∧
      ¬ QuasiconcaveOn ℝ Set.univ (fun x : ℝ => x ^ 4) := by
  have hd : deriv (fun x : ℝ => x ^ 4) = fun x => 4 * x ^ 3 := by
    ext x
    simp
  have hd2 : deriv (fun x : ℝ => 4 * x ^ 3) = fun x => 4 * (3 * x ^ 2) := by
    ext x
    simp
  refine ⟨fun x z h => ?_, fun h => ?_⟩
  · rw [hd] at h
    rw [hd, hd2]
    rcases mul_eq_zero.mp h with h | h
    · have hx : x = 0 := by
        have : x ^ 3 = 0 := by linarith
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      simp [hx]
    · simp [h]
  · have := (quasiconcaveOn_iff_min_le.mp h).2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ 1)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num at this

end MWG.ClassicalDemand
