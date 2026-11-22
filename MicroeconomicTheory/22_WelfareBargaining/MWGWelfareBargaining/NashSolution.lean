/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Bargaining
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.BigOperators.Field

/-!
# The Nash bargaining solution and Proposition 22.E.1

MWG, Example 22.E.3 (pp. 842-843), the small-type characterization (p. 843), Proposition 22.E.1
with its proof (pp. 843-844) and footnotes 27-28, and Exercise 22.E.3(a)-(b).

We treat the weighted (nonsymmetric) Nash solution, which maximizes `∑ αᵢ ln(uᵢ - u*ᵢ)` over
`{u ∈ U : u ≫ u*}`, for weights `α ≫ 0`; MWG's Nash solution is `α = 1` (`nash`). Existence
uses compactness of `{u ∈ U : u ≥ u*}` and continuity of `∏ (uᵢ - u*ᵢ)^{αᵢ}`; uniqueness uses
strict concavity of `ln` (midpoint inequality). The supporting-hyperplane step of the proof of
Proposition 22.E.1 ("`U ⊆ U'` because the concave function `∑ ln uᵢ` has gradient
`(1/ûᵢ)ᵢ` at `û`") is `nash_foc`, proved by differentiating along segments.

The Nash solution is independent of utility origins and units, Paretian (even strongly),
symmetric (for equal weights), individually rational and satisfies IIA; Proposition 22.E.1
shows that these properties characterize it, and footnote 28 (IR is implied) follows.
-/

namespace MWG.WelfareBargaining

open Set Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The weighted Nash objective `∑ αᵢ ln(uᵢ - dᵢ)`. -/
noncomputable def nashObj (α d u : ι → ℝ) : ℝ := ∑ i, α i * Real.log (u i - d i)

/-- `û` is the (weighted) Nash point of `P`: it lies in `U`, strictly above the threat point,
and maximizes the Nash objective there. -/
def IsNashPoint (α : ι → ℝ) (P : BargainingProblem ι) (û : ι → ℝ) : Prop :=
  û ∈ P.U ∧ (∀ i, P.d i < û i) ∧
    ∀ u ∈ P.U, (∀ i, P.d i < u i) → nashObj α P.d u ≤ nashObj α P.d û

/-- The strict concavity of `ln` at midpoints. -/
theorem log_midpoint {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.log a + Real.log b) / 2 ≤ Real.log ((a + b) / 2) ∧
      (a ≠ b → (Real.log a + Real.log b) / 2 < Real.log ((a + b) / 2)) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hm : 0 < ((a + b) / 2) ^ 2 := by positivity
  have key : Real.log a + Real.log b = Real.log (a * b) := (Real.log_mul ha.ne' hb.ne').symm
  have key2 : Real.log (((a + b) / 2) ^ 2) = 2 * Real.log ((a + b) / 2) := by
    rw [Real.log_pow]; norm_num
  constructor
  · have : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have := Real.log_le_log hab this
    rw [key2] at this
    linarith
  · intro hne
    have : a * b < ((a + b) / 2) ^ 2 := by
      have : 0 < (a - b) ^ 2 := by positivity
      nlinarith
    have := Real.log_lt_log hab this
    rw [key2] at this
    linarith

/-- Existence of the weighted Nash point (MWG, p. 842). -/
theorem exists_nashPoint [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (P : BargainingProblem ι) : ∃ û, IsNashPoint α P û := by
  set K := {u ∈ P.U | P.d ≤ u}
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded
    (P.closed.inter (isClosed_le continuous_const continuous_id)) P.isBounded
  set G : (ι → ℝ) → ℝ := fun u => ∏ i, (max (u i - P.d i) 0) ^ (α i)
  have hG : Continuous G := continuous_finsetProd _ fun i _ =>
    (Real.continuous_rpow_const (hα i).le).comp
      (((continuous_apply i).sub continuous_const).max continuous_const)
  obtain ⟨û, hûK, hmax⟩ := hKc.exists_isMaxOn ⟨P.d, P.d_mem, le_rfl⟩ hG.continuousOn
  obtain ⟨ε, hε, hp⟩ := P.exists_gt
  have hpK : (fun i => P.d i + ε) ∈ K := ⟨hp, fun i => by simp; linarith⟩
  have hGp : 0 < G (fun i => P.d i + ε) := Finset.prod_pos fun i _ => by
    simp only [add_sub_cancel_left, max_eq_left hε.le]
    exact Real.rpow_pos_of_pos hε _
  have hGû : 0 < G û := lt_of_lt_of_le hGp (hmax hpK)
  have hgt : ∀ i, P.d i < û i := by
    intro i
    by_contra h
    have hi : û i - P.d i ≤ 0 := by linarith [not_lt.1 h]
    have : G û = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by
      simp only [max_eq_right hi]
      exact Real.zero_rpow (hα i).ne')
    linarith
  have hlogG : ∀ u : ι → ℝ, (∀ i, P.d i < u i) → Real.log (G u) = nashObj α P.d u := by
    intro u hu
    simp only [G, nashObj]
    rw [Real.log_prod (fun i _ => by
      rw [max_eq_left (sub_pos.2 (hu i)).le]
      exact (Real.rpow_pos_of_pos (sub_pos.2 (hu i)) _).ne')]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [max_eq_left (sub_pos.2 (hu i)).le, Real.log_rpow (sub_pos.2 (hu i))]
  refine ⟨û, hûK.1, hgt, fun u hu hdu => ?_⟩
  rw [← hlogG u hdu, ← hlogG û hgt]
  have hGu : 0 < G u := Finset.prod_pos fun i _ => by
    rw [max_eq_left (sub_pos.2 (hdu i)).le]
    exact Real.rpow_pos_of_pos (sub_pos.2 (hdu i)) _
  exact Real.log_le_log hGu (hmax ⟨hu, fun i => (hdu i).le⟩)

/-- Uniqueness of the weighted Nash point (strict concavity of `ln`, MWG p. 842). -/
theorem nashPoint_unique {α : ι → ℝ} (hα : ∀ i, 0 < α i) {P : BargainingProblem ι}
    {û û' : ι → ℝ} (h : IsNashPoint α P û) (h' : IsNashPoint α P û') : û = û' := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, û j ≠ û' j := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  set m : ι → ℝ := (1 / 2 : ℝ) • û + (1 / 2 : ℝ) • û'
  have hm : m ∈ P.U := P.convex h.1 h'.1 (by norm_num) (by norm_num) (by norm_num)
  have hmi : ∀ i, m i - P.d i = ((û i - P.d i) + (û' i - P.d i)) / 2 := fun i => by
    simp only [m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hmd : ∀ i, P.d i < m i := fun i => by
    have := hmi i; have := h.2.1 i; have := h'.2.1 i; linarith
  have heq : nashObj α P.d û = nashObj α P.d û' :=
    le_antisymm (h'.2.2 _ h.1 h.2.1) (h.2.2 _ h'.1 h'.2.1)
  have hlt : (nashObj α P.d û + nashObj α P.d û') / 2 < nashObj α P.d m := by
    simp only [nashObj, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_lt_sum
    · intro i _
      have := (log_midpoint (sub_pos.2 (h.2.1 i)) (sub_pos.2 (h'.2.1 i))).1
      rw [hmi i]
      nlinarith [hα i]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      have := (log_midpoint (sub_pos.2 (h.2.1 j)) (sub_pos.2 (h'.2.1 j))).2
        (fun e => hj (by linarith))
      rw [hmi j]
      nlinarith [hα j]
  have := h.2.2 m hm hmd
  linarith

/-- **Example 22.E.3** (MWG, p. 842). The weighted Nash solution (any point if the weights are
not positive or there are no agents). -/
noncomputable def nashSol (α : ι → ℝ) (P : BargainingProblem ι) : ι → ℝ := by
  classical
  exact if h : ∃ û, IsNashPoint α P û then h.choose else P.d

/-- **Example 22.E.3** (MWG, p. 842). The Nash solution: the point of `U ∩ ℝ^I₊` (after
normalisation) maximizing `u₁ × ⋯ × u_I`, equivalently `∑ ln uᵢ`. -/
noncomputable def nash (P : BargainingProblem ι) : ι → ℝ := nashSol (fun _ => 1) P

theorem nashSol_spec [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) (P : BargainingProblem ι) :
    IsNashPoint α P (nashSol α P) := by
  unfold nashSol
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_nashPoint hα P) h

theorem nashSol_eq [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) {P : BargainingProblem ι}
    {û : ι → ℝ} (h : IsNashPoint α P û) : nashSol α P = û :=
  nashPoint_unique hα (nashSol_spec hα P) h

/-- **Proposition 22.E.1, proof** (MWG, p. 844). The supporting hyperplane at the Nash point:
for every `u ∈ U`, `∑ αᵢ (uᵢ - dᵢ)/(ûᵢ - dᵢ) ≤ ∑ αᵢ`, i.e. `U ⊆ U'` (footnote 27: the gradient
of the concave function `∑ αᵢ ln uᵢ` at `û` supports `U`). -/
theorem nash_foc {α : ι → ℝ} {P : BargainingProblem ι} {û : ι → ℝ}
    (h : IsNashPoint α P û) {u : ι → ℝ} (hu : u ∈ P.U) :
    ∑ i, α i * ((u i - P.d i) / (û i - P.d i)) ≤ ∑ i, α i := by
  have hpos : ∀ i, 0 < û i - P.d i := fun i => sub_pos.2 (h.2.1 i)
  set D := ∑ i, α i * ((u i - û i) / (û i - P.d i))
  have hsplit : ∑ i, α i * ((u i - P.d i) / (û i - P.d i)) = ∑ i, α i + D := by
    simp only [D, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [(hpos i).ne']
    ring
  rw [hsplit]
  suffices D ≤ 0 by linarith
  by_contra hD
  push Not at hD
  -- the objective along the segment from `û` towards `u`
  set φ : ℝ → ℝ := fun t => ∑ i, α i * Real.log (û i + t * (u i - û i) - P.d i)
  have hφ : HasDerivAt φ D 0 := by
    have := HasDerivAt.sum (u := Finset.univ) (x := (0 : ℝ))
      (A := fun i t => α i * Real.log (û i + t * (u i - û i) - P.d i))
      (A' := fun i => α i * ((u i - û i) / (û i - P.d i))) fun i _ => by
        have h1 : HasDerivAt (fun t : ℝ => û i + t * (u i - û i) - P.d i) (u i - û i) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u i - û i)).const_add (û i)
            |>.sub_const (P.d i)
        have h2 := h1.log (by simp only [zero_mul, add_zero, ne_eq]; exact (hpos i).ne')
        simp only [zero_mul, add_zero] at h2
        exact h2.const_mul (α i)
    convert this using 1
    funext t
    simp [φ]
  rw [hasDerivAt_iff_tendsto_slope] at hφ
  have hev1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope φ 0 t := hφ.eventually (lt_mem_nhds hD)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), (t < 1 ∧ ∀ i, P.d i < û i + t * (u i - û i)) := by
    refine (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).and ?_
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun t : ℝ => û i + t * (u i - û i) := by fun_prop
    exact hc.tendsto 0 |>.eventually
      (lt_mem_nhds (by simp only [zero_mul, add_zero]; exact h.2.1 i))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 0 < slope φ 0 t ∧ t < 1 ∧
      ∀ i, P.d i < û i + t * (u i - û i) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono _ (fun x hx => ne_of_gt hx) hev1,
      nhdsWithin_le_nhds hev2] with t ht h1 h2
    exact ⟨ht, h1, h2⟩
  obtain ⟨t, ht0, hslope, ht1, hd⟩ := hev.exists
  have hw : (fun i => û i + t * (u i - û i)) ∈ P.U := by
    have := P.convex h.1 hu (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    convert this using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hle := h.2.2 _ hw hd
  have hφ0 : φ 0 = nashObj α P.d û := by simp [φ, nashObj]
  have hφt : φ t = nashObj α P.d (fun i => û i + t * (u i - û i)) := rfl
  rw [slope_def_field, hφ0, hφt, sub_zero] at hslope
  have := (div_pos_iff_of_pos_right ht0).1 hslope
  linarith

theorem isNashPoint_translate {α : ι → ℝ} {P : BargainingProblem ι} {û : ι → ℝ}
    (h : IsNashPoint α P û) (a : ι → ℝ) : IsNashPoint α (P.translate a) (û + a) := by
  have hobj : ∀ v : ι → ℝ, nashObj α (P.d + a) v = nashObj α P.d (v - a) := fun v => by
    simp only [nashObj, Pi.add_apply, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  refine ⟨by simpa using h.1, fun i => by simpa using h.2.1 i, fun u hu hdu => ?_⟩
  simp only [BargainingProblem.translate_d] at hdu ⊢
  rw [hobj, hobj, add_sub_cancel_right]
  exact h.2.2 _ hu fun i => by have := hdu i; simp at this ⊢; linarith

theorem isNashPoint_scale {α : ι → ℝ} {P : BargainingProblem ι} {û : ι → ℝ}
    (h : IsNashPoint α P û) (β : ι → ℝ) (hβ : ∀ i, 0 < β i) :
    IsNashPoint α (P.scale β hβ) (fun i => β i * û i) := by
  have hobj : ∀ v : ι → ℝ, (∀ i, β i * P.d i < v i) → nashObj α (P.scale β hβ).d v =
      ∑ i, α i * Real.log (β i) + nashObj α P.d (fun i => v i / β i) := by
    intro v hvd
    simp only [nashObj, BargainingProblem.scale_d, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hv : v i / β i - P.d i ≠ 0 := by
      have := hvd i
      rw [sub_ne_zero]
      intro e
      rw [div_eq_iff (hβ i).ne'] at e
      linarith
    have e : v i - β i * P.d i = β i * (v i / β i - P.d i) := by
      field_simp [(hβ i).ne']
    rw [e, Real.log_mul (hβ i).ne' hv]
    ring
  refine ⟨P.mem_scale β hβ h.1, fun i => ?_, fun u hu hdu => ?_⟩
  · rw [BargainingProblem.scale_d]
    exact mul_lt_mul_of_pos_left (h.2.1 i) (hβ i)
  · rw [hobj _ hdu, hobj _ fun i => mul_lt_mul_of_pos_left (h.2.1 i) (hβ i)]
    have e : (fun i => β i * û i / β i) = û := funext fun i => by field_simp [(hβ i).ne']
    rw [e]
    have := h.2.2 _ hu fun i => by
      have := hdu i
      rw [BargainingProblem.scale_d] at this
      rw [lt_div_iff₀ (hβ i), mul_comm]; exact this
    linarith

theorem isNashPoint_of_subset {α : ι → ℝ} {P P' : BargainingProblem ι} {û : ι → ℝ}
    (h : IsNashPoint α P û) (hsub : P'.U ⊆ P.U) (hd : P'.d = P.d) (hû : û ∈ P'.U) :
    IsNashPoint α P' û :=
  ⟨hû, fun i => hd ▸ h.2.1 i, fun u hu hdu => hd ▸ h.2.2 u (hsub hu) (hd ▸ hdu)⟩

/-- At the Nash point no feasible vector is weakly better for all and different: the Nash
solution is (strongly) Pareto optimal (MWG, p. 842). -/
theorem nashPoint_strong_pareto {α : ι → ℝ} (hα : ∀ i, 0 < α i) {P : BargainingProblem ι}
    {û : ι → ℝ} (h : IsNashPoint α P û) {v : ι → ℝ} (hv : v ∈ P.U) (hle : ∀ i, û i ≤ v i) :
    v = û := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ û j := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  have hvd : ∀ i, P.d i < v i := fun i => lt_of_lt_of_le (h.2.1 i) (hle i)
  have hlt : nashObj α P.d û < nashObj α P.d v := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (sub_pos.2 (h.2.1 i))
        (by linarith [hle i])) (hα i).le
    · refine ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (Real.log_lt_log
        (sub_pos.2 (h.2.1 j)) ?_) (hα j)⟩
      have := lt_of_le_of_ne (hle j) (Ne.symm hj)
      linarith
  linarith [h.2.2 v hv hvd]

theorem nashSol_isBargainingSolution [Nonempty ι] {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) : IsBargainingSolution (nashSol α) :=
  fun P => (nashSol_spec hα P).1

theorem nashSol_IUO [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) : IUO (nashSol α) := fun P a =>
  nashSol_eq hα (isNashPoint_translate (nashSol_spec hα P) a)

theorem nashSol_IUU [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) : IUU (nashSol α) := fun P β hβ =>
  nashSol_eq hα (isNashPoint_scale (nashSol_spec hα P) β hβ)

theorem nashSol_pareto [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) : ParetoBS (nashSol α) := by
  rintro P ⟨v, hv, hlt⟩
  have := nashPoint_strong_pareto hα (nashSol_spec hα P) hv fun i => (hlt i).le
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hlt i).ne (congrFun this i).symm

theorem nashSol_IR [Nonempty ι] {α : ι → ℝ} (hα : ∀ i, 0 < α i) : IndivRational (nashSol α) :=
  fun P i => ((nashSol_spec hα P).2.1 i).le

theorem nashSol_IIA [Nonempty ι] {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) : IIA (nashSol α) := fun P _ hsub hd hmem =>
  nashSol_eq hα (isNashPoint_of_subset (nashSol_spec hα P) hsub hd hmem)

/-- With equal weights the Nash solution is symmetric. -/
theorem nashSol_symmetric [Nonempty ι] {c : ℝ} (hc : 0 < c)
    : SymmetricBS (nashSol fun _ : ι => c) := by
  classical
  intro P hsym hd i j
  have hspec := nashSol_spec (fun _ => hc) P
  set û := nashSol (fun _ : ι => c) P
  have hperm : ∀ σ : Equiv.Perm ι, IsNashPoint (fun _ => c) P (û ∘ σ) := by
    intro σ
    refine ⟨hsym σ _ hspec.1, fun k => ?_, fun u hu hdu => ?_⟩
    · have := hspec.2.1 (σ k)
      rwa [hd (σ k) k] at this
    · have e : nashObj (fun _ => c) P.d (û ∘ σ) = nashObj (fun _ => c) P.d û := by
        simp only [nashObj, Function.comp]
        rw [← Equiv.sum_comp σ (fun k => c * Real.log (û k - P.d k))]
        exact Finset.sum_congr rfl fun k _ => by rw [hd (σ k) k]
      rw [e]
      exact hspec.2.2 u hu hdu
  have := nashPoint_unique (fun _ => hc) (hperm (Equiv.swap i j)) hspec
  have := congrFun this i
  simpa [Equiv.swap_apply_left] using this.symm


/-- **Example 22.E.3** (MWG, pp. 842-843). The Nash solution is a bargaining solution that is
independent of utility origins and units, Paretian, symmetric, individually rational and
satisfies the independence of irrelevant alternatives. -/
theorem example_22_E_3 [Nonempty ι] :
    IsBargainingSolution (nash (ι := ι)) ∧ IUO (nash (ι := ι)) ∧ IUU (nash (ι := ι)) ∧
      ParetoBS (nash (ι := ι)) ∧ SymmetricBS (nash (ι := ι)) ∧
      IndivRational (nash (ι := ι)) ∧ IIA (nash (ι := ι)) :=
  ⟨nashSol_isBargainingSolution (fun _ => one_pos), nashSol_IUO (fun _ => one_pos),
    nashSol_IUU (fun _ => one_pos), nashSol_pareto (fun _ => one_pos),
    nashSol_symmetric one_pos, nashSol_IR (fun _ => one_pos), nashSol_IIA (fun _ => one_pos)⟩

/-- The symmetric problem `U'' = {u : ∑ uᵢ ≤ I}` of the proof of Proposition 22.E.1. -/
noncomputable def simplexProblem [Nonempty ι] : BargainingProblem ι :=
  halfSpace (fun _ => 1) (fun _ => one_pos) (Fintype.card ι) (Nat.cast_pos.2 Fintype.card_pos)

/-- **Proposition 22.E.1, proof** (MWG, p. 844). A symmetric, Paretian bargaining solution
assigns `(1, …, 1)` to `U'' = {u : ∑ uᵢ ≤ I}`. -/
theorem simplexProblem_value [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (hB : IsBargainingSolution f) (hP : ParetoBS f) (hS : SymmetricBS f) :
    f simplexProblem = fun _ => 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsym : ∀ i, f simplexProblem i = f simplexProblem i₀ := fun i =>
    hS _ (halfSpace_symmetric 1 one_pos _ _) (fun _ _ => rfl) i i₀
  set t := f simplexProblem i₀
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hmem := hB simplexProblem
  have hmem' : (Fintype.card ι : ℝ) * t ≤ Fintype.card ι := by
    have : ∑ i, (1 : ℝ) * f simplexProblem i ≤ Fintype.card ι := hmem
    simp only [one_mul, hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have ht1 : t ≤ 1 := by nlinarith
  have ht : t = 1 := by
    by_contra hne
    have hlt : t < 1 := lt_of_le_of_ne ht1 hne
    apply hP simplexProblem
    refine ⟨fun _ => (1 + t) / 2, ?_, fun i => by rw [hsym]; linarith⟩
    change ∑ i, (1 : ℝ) * ((1 + t) / 2) ≤ Fintype.card ι
    simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith
  funext i
  rw [hsym, ht]

/-- **Proposition 22.E.1** (MWG, p. 843). The Nash solution is the only bargaining solution that
is independent of utility origins and units, Paretian, symmetric and independent of irrelevant
alternatives. -/
theorem proposition_22_E_1 [Nonempty ι] (f : BargainingProblem ι → ι → ℝ) :
    (IsBargainingSolution f ∧ IUO f ∧ IUU f ∧ ParetoBS f ∧ SymmetricBS f ∧ IIA f) ↔
      f = nash := by
  constructor
  · rintro ⟨hB, hO, hU, hP, hS, hI⟩
    funext P
    rw [show nash P = nashSol (fun _ => 1) P from rfl, normalize_eq hO P,
      normalize_eq (nashSol_IUO (fun _ => one_pos)) P]
    congr 1
    -- the normalised problem `Q`, with threat point `0`
    set Q := P.normalize
    have hQd : Q.d = 0 := P.normalize_d
    have hspec : IsNashPoint (fun _ => 1) Q (nash Q) := nashSol_spec (fun _ => one_pos) Q
    set û := nash Q
    have hûpos : ∀ i, 0 < û i := fun i => by have := hspec.2.1 i; rwa [hQd] at this
    -- `U' = {u : ∑ uᵢ/ûᵢ ≤ I}` is the rescaling of `U''` by `û`
    set Q' := (simplexProblem (ι := ι)).scale û hûpos
    have hQ'd : Q'.d = Q.d := by
      rw [hQd]; funext i; simp [Q', BargainingProblem.scale_d, simplexProblem, halfSpace]
    have hsub : Q.U ⊆ Q'.U := by
      intro u hu
      have := nash_foc hspec hu
      simp only [hQd, Pi.zero_apply, sub_zero, one_mul, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at this
      change ∑ i, (1 : ℝ) * (u i / û i) ≤ Fintype.card ι
      simpa using this
    have hfQ' : f Q' = û := by
      rw [hU, simplexProblem_value hB hP hS]
      funext i; simp
    have := hI Q' Q hsub hQ'd.symm (by rw [hfQ']; exact hspec.1)
    rw [this, hfQ']
    rfl
  · rintro rfl
    exact ⟨nashSol_isBargainingSolution (fun _ => one_pos), nashSol_IUO (fun _ => one_pos),
      nashSol_IUU (fun _ => one_pos), nashSol_pareto (fun _ => one_pos),
      nashSol_symmetric one_pos, nashSol_IIA (fun _ => one_pos)⟩

/-- **Footnote 28** (MWG, p. 843). Individual rationality is implied by the other conditions of
Proposition 22.E.1. -/
theorem footnote_22_28 [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (h : IsBargainingSolution f ∧ IUO f ∧ IUU f ∧ ParetoBS f ∧ SymmetricBS f ∧ IIA f) :
    IndivRational f := by
  rw [(proposition_22_E_1 f).1 h]
  exact nashSol_IR (fun _ => one_pos)

/-- **Section 22.E, small type** (MWG, p. 843). If for some rescaling factors `η ≫ 0` the point
`û` is simultaneously utilitarian (it maximizes `∑ ηᵢ(uᵢ - u*ᵢ)` on `U`) and egalitarian
(`ηᵢ(ûᵢ - u*ᵢ)` is the same `γ > 0` for all `i`), then `û` is the Nash solution. -/
theorem nash_of_utilitarian_egalitarian [Nonempty ι] {P : BargainingProblem ι} {û η : ι → ℝ}
    {γ : ℝ} (hγ : 0 < γ) (hη : ∀ i, 0 < η i) (hû : û ∈ P.U)
    (hutil : ∀ u ∈ P.U, ∑ i, η i * (u i - P.d i) ≤ ∑ i, η i * (û i - P.d i))
    (hegal : ∀ i, η i * (û i - P.d i) = γ) : nash P = û := by
  have hpos : ∀ i, 0 < û i - P.d i := fun i => by
    have := hegal i
    by_contra h; push Not at h
    nlinarith [hη i]
  refine nashSol_eq (fun _ => one_pos) ⟨hû, fun i => sub_pos.1 (hpos i), fun u hu hdu => ?_⟩
  -- `ln x ≤ ln y + (x - y)/y`
  have hlog : ∀ i, Real.log (u i - P.d i) ≤
      Real.log (û i - P.d i) + (u i - P.d i) / (û i - P.d i) - 1 := by
    intro i
    have hx : 0 < u i - P.d i := sub_pos.2 (hdu i)
    have := Real.log_le_sub_one_of_pos (div_pos hx (hpos i))
    rw [Real.log_div hx.ne' (hpos i).ne'] at this
    linarith
  have hratio : ∀ i, (u i - P.d i) / (û i - P.d i) = η i * (u i - P.d i) / γ := by
    intro i
    rw [← hegal i]
    field_simp [(hpos i).ne', (hη i).ne']
  have hsum : ∑ i, (u i - P.d i) / (û i - P.d i) ≤ Fintype.card ι := by
    simp only [hratio, ← Finset.sum_div]
    rw [div_le_iff₀ hγ]
    have := hutil u hu
    simp only [hegal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    linarith
  simp only [nashObj, one_mul]
  calc ∑ i, Real.log (u i - P.d i)
      ≤ ∑ i, (Real.log (û i - P.d i) + (u i - P.d i) / (û i - P.d i) - 1) :=
        Finset.sum_le_sum fun i _ => hlog i
    _ = ∑ i, Real.log (û i - P.d i) + (∑ i, (u i - P.d i) / (û i - P.d i) -
        Fintype.card ι) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]
        ring
    _ ≤ ∑ i, Real.log (û i - P.d i) := by linarith

/-- **Exercise 22.E.3(b)** (MWG, p. 853). For the rescaling factors `ηᵢ = 1/(ûᵢ - u*ᵢ)` the Nash
solution `û` is simultaneously utilitarian and egalitarian. -/
theorem exercise_22_E_3b [Nonempty ι] (P : BargainingProblem ι) :
    ∃ η : ι → ℝ, (∀ i, 0 < η i) ∧
      (∀ u ∈ P.U, ∑ i, η i * (u i - P.d i) ≤ ∑ i, η i * (nash P i - P.d i)) ∧
      ∀ i, η i * (nash P i - P.d i) = 1 := by
  have hspec : IsNashPoint (fun _ => 1) P (nash P) := nashSol_spec (fun _ => one_pos) P
  have hpos : ∀ i, 0 < nash P i - P.d i := fun i => sub_pos.2 (hspec.2.1 i)
  have hone : ∀ i, 1 / (nash P i - P.d i) * (nash P i - P.d i) = 1 := fun i => by
    field_simp [(hpos i).ne']
  refine ⟨fun i => 1 / (nash P i - P.d i), fun i => one_div_pos.2 (hpos i), fun u hu => ?_, hone⟩
  have := nash_foc hspec hu
  simp only [hone, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this ⊢
  simpa only [one_div, inv_mul_eq_div] using this

/-- **Exercise 22.E.3(a)** (MWG, p. 853), first half (`I = 2`, threat point `0`). The line
`u₁/(2û₁) + u₂/(2û₂) = 1` through the Nash solution `û` supports `U`, and the midpoint of its
segment in the positive orthant, between `(2û₁, 0)` and `(0, 2û₂)`, is `û`. -/
theorem exercise_22_E_3a_tangent (P : BargainingProblem (Fin 2)) (hd : P.d = 0) :
    (∀ u ∈ P.U, u 0 / (2 * nash P 0) + u 1 / (2 * nash P 1) ≤ 1) ∧
      nash P 0 / (2 * nash P 0) + nash P 1 / (2 * nash P 1) = 1 ∧
      (fun i : Fin 2 => ((![2 * nash P 0, 0] : Fin 2 → ℝ) i + ![0, 2 * nash P 1] i) / 2) =
        nash P := by
  have hspec : IsNashPoint (fun _ => 1) P (nash P) := nashSol_spec (fun _ => one_pos) P
  have hpos : ∀ i, 0 < nash P i := fun i => by have := hspec.2.1 i; rwa [hd] at this
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · have := nash_foc hspec hu
    simp only [hd, Pi.zero_apply, sub_zero, one_mul, Fin.sum_univ_two] at this
    have e : u 0 / (2 * nash P 0) + u 1 / (2 * nash P 1) =
        (u 0 / nash P 0 + u 1 / nash P 1) / 2 := by
      field_simp [(hpos 0).ne', (hpos 1).ne']
    rw [e]; linarith
  · field_simp [(hpos 0).ne', (hpos 1).ne']; norm_num
  · funext i; fin_cases i <;> simp

/-- **Exercise 22.E.3(a)** (MWG, p. 853), second half (`I = 2`, threat point `0`). Conversely, a
boundary point `û ≫ 0` of `U` through which passes a supporting line `u₁/a + u₂/b = 1` whose
positive-orthant segment has midpoint `û = (a/2, b/2)` is the Nash solution. -/
theorem exercise_22_E_3a_converse (P : BargainingProblem (Fin 2)) (hd : P.d = 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hmem : ![a / 2, b / 2] ∈ P.U)
    (hsupp : ∀ u ∈ P.U, u 0 / a + u 1 / b ≤ 1) : nash P = ![a / 2, b / 2] := by
  refine nash_of_utilitarian_egalitarian (η := ![1 / a, 1 / b]) (γ := 1 / 2) (by norm_num)
    (fun i => by fin_cases i <;> simp [ha, hb]) hmem (fun u hu => ?_) (fun i => ?_)
  · simp only [hd, Pi.zero_apply, sub_zero, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have := hsupp u hu
    have e1 : 1 / a * u 0 + 1 / b * u 1 = u 0 / a + u 1 / b := by ring
    have e2 : 1 / a * (a / 2) + 1 / b * (b / 2) = 1 := by field_simp; norm_num
    rw [e1, e2]; exact this
  · rw [hd]
    fin_cases i
    · change 1 / a * (a / 2 - 0) = 1 / 2
      field_simp
      ring
    · change 1 / b * (b / 2 - 0) = 1 / 2
      field_simp
      ring

end MWG.WelfareBargaining
