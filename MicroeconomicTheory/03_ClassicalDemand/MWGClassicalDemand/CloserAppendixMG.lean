/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMG
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Minkowski's theorem: Theorem M.G.1 in its exact form

MWG, Mathematical Appendix, Section M.G, Theorem M.G.1, p. 947: if `B ⊆ ℝ^N` is convex and
compact, every `x ∈ B` is a convex combination of at most `N + 1` extreme points of `B`.

The earlier module `AppendixMG` proved Carathéodory's bound and the Krein-Milman closure form.
Here Minkowski's theorem `B = Co(ext B)` (no closure) is proved, by strong induction on the
dimension of the affine span of `B`, in any finite-dimensional real inner product space:

* a point `x ∈ B` that is not alone in `B` lies on a segment through `x` whose two endpoints
  cannot be extended inside `B` (`closerMG_endpoint`);
* at such an endpoint `z` there is a nonzero `f` in the direction space of `B` with `z`
  maximizing `⟪f, ·⟫` on `B` (`closerMG_support_of_endpoint`; nearest-point normals and a
  compactness limit);
* the exposed face `{w ∈ B : ⟪f, w⟫ = ⟪f, z⟫}` is an extreme subset of strictly smaller
  dimension (`closerMG_face_finrank_lt`), so the induction hypothesis applies to it.

The theorem is transferred to `ℝ^N = Fin N → ℝ` through `EuclideanSpace.equiv`, and combined
with Carathéodory's bound (`caratheodory_M_G_1`) gives `theorem_M_G_1`.
-/

namespace MWG.ClassicalDemand

open Filter Topology

/-- **Theorem M.G.1** (MWG, p. 947), supporting step. Let `B` be compact and convex in a
finite-dimensional inner product space, `z ∈ B`, and `d` a direction of the affine span of `B`
along which `z` cannot move inside `B`. Then some nonzero `f` in the direction space of `B`
has `z` as a maximizer of `⟪f, ·⟫` on `B`. -/
theorem closerMG_support_of_endpoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {B : Set E} (hc : IsCompact B)
    (hconv : Convex ℝ B) {z d : E} (hz : z ∈ B) (hd : d ∈ vectorSpan ℝ B)
    (hend : ∀ ε : ℝ, 0 < ε → z + ε • d ∉ B) :
    ∃ f ∈ vectorSpan ℝ B, f ≠ 0 ∧ ∀ w ∈ B, inner ℝ f w ≤ inner ℝ f z := by
  set V := vectorSpan ℝ B with hVdef
  have hne : B.Nonempty := ⟨z, hz⟩
  have proj : ∀ p : E, ∃ q ∈ B, ‖p - q‖ ≤ ‖p - z‖ ∧
      ∀ w ∈ B, inner ℝ (p - q) (w - q) ≤ 0 := by
    intro p
    obtain ⟨q, hq, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv p
    refine ⟨q, hq, ?_, (norm_eq_iInf_iff_real_inner_le_zero hconv hq).1 heq⟩
    rw [heq]
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : B)
  choose q hqB hqle hqin using proj
  set p : ℕ → E := fun n => z + (1 / ((n : ℝ) + 1)) • d with hpdef
  have hpB : ∀ n, p n ∉ B := fun n => hend _ (by positivity)
  have hpq : ∀ n, p n - q (p n) ≠ 0 := fun n h =>
    hpB n (by rw [sub_eq_zero.1 h]; exact hqB _)
  set u : ℕ → E := fun n => ‖p n - q (p n)‖⁻¹ • (p n - q (p n)) with hudef
  have huV : ∀ n, u n ∈ V := by
    intro n
    apply V.smul_mem
    have h1 : p n - z ∈ V := by
      have : p n - z = (1 / ((n : ℝ) + 1)) • d := by simp [hpdef]
      rw [this]
      exact V.smul_mem _ hd
    have h2 : z - q (p n) ∈ V := vsub_mem_vectorSpan ℝ hz (hqB _)
    have : p n - q (p n) = (p n - z) + (z - q (p n)) := by abel
    rw [this]
    exact V.add_mem h1 h2
  have hun : ∀ n, ‖u n‖ = 1 := by
    intro n
    simp only [hudef, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hpq n))
  have hK : IsCompact ((V : Set E) ∩ Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).inter_left V.closed_of_finiteDimensional
  obtain ⟨f, ⟨hfV, hf1⟩, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := u) (fun n => ⟨huV n, by simp [hun n]⟩)
  refine ⟨f, hfV, ?_, ?_⟩
  · intro h
    simp [h] at hf1
  · intro w hw
    have key : ∀ n : ℕ, inner ℝ (u n) (w - z) ≤ 2 * ‖d‖ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have h0 : inner ℝ (u n) (w - q (p n)) ≤ 0 := by
        simp only [hudef, real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hqin _ w hw)
      have h1 : inner ℝ (u n) (q (p n) - z) ≤ ‖q (p n) - z‖ := by
        calc _ ≤ ‖u n‖ * ‖q (p n) - z‖ := real_inner_le_norm _ _
          _ = _ := by rw [hun n, one_mul]
      have hpz : ‖p n - z‖ = ‖d‖ * (1 / ((n : ℝ) + 1)) := by
        have : p n - z = (1 / ((n : ℝ) + 1)) • d := by simp [hpdef]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_comm]
      have h2 : ‖q (p n) - z‖ ≤ 2 * ‖d‖ * (1 / ((n : ℝ) + 1)) := by
        calc ‖q (p n) - z‖ = ‖(p n - z) - (p n - q (p n))‖ := by congr 1; abel
          _ ≤ ‖p n - z‖ + ‖p n - q (p n)‖ := norm_sub_le _ _
          _ ≤ ‖p n - z‖ + ‖p n - z‖ := by linarith [hqle (p n)]
          _ = _ := by rw [hpz]; ring
      have : w - z = (w - q (p n)) + (q (p n) - z) := by abel
      rw [this, inner_add_right]
      linarith
    have hlim1 : Tendsto (fun n => inner ℝ (u (φ n)) (w - z)) atTop
        (𝓝 (inner ℝ f (w - z))) := hlim.inner tendsto_const_nhds
    have hlim2 : Tendsto (fun n => 2 * ‖d‖ * (1 / (((φ n : ℕ) : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_mul
        (2 * ‖d‖)
      simpa using this
    have : inner ℝ f (w - z) ≤ 0 :=
      le_of_tendsto_of_tendsto' hlim1 hlim2 (fun n => key (φ n))
    rw [inner_sub_right] at this
    linarith

/-- **Theorem M.G.1** (MWG, p. 947), endpoint step: along any direction `e`, a point `x` of a
compact `B` can be pushed to a last point `x + t e ∈ B` (`t ≥ 0`, maximal). -/
theorem closerMG_endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}
    (hc : IsCompact B) {x e : E} (hx : x ∈ B) (he : e ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ x + t • e ∈ B ∧ ∀ s : ℝ, x + s • e ∈ B → s ≤ t := by
  set T : Set ℝ := {t | x + t • e ∈ B} with hTdef
  have hTc : IsClosed T :=
    hc.isClosed.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded
  have hepos : 0 < ‖e‖ := norm_pos_iff.2 he
  have hTb : Bornology.IsBounded T := by
    refine (Metric.isBounded_Icc (-((R + ‖x‖) / ‖e‖)) ((R + ‖x‖) / ‖e‖)).subset ?_
    intro t ht
    have h1 : ‖x + t • e‖ ≤ R := by simpa using hR ht
    have h2 : |t| * ‖e‖ ≤ R + ‖x‖ := by
      have : ‖t • e‖ ≤ ‖x + t • e‖ + ‖x‖ := by
        calc ‖t • e‖ = ‖(x + t • e) - x‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      rw [norm_smul, Real.norm_eq_abs] at this
      linarith
    have h3 : |t| ≤ (R + ‖x‖) / ‖e‖ := by rw [le_div_iff₀ hepos]; exact h2
    exact abs_le.1 h3
  have hT : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc hTb
  have h0 : (0 : ℝ) ∈ T := by simp [hTdef, hx]
  obtain ⟨t, htT, htmax⟩ := hT.exists_isGreatest ⟨0, h0⟩
  exact ⟨t, htmax h0, htT, fun s hs => htmax hs⟩

/-- **Theorem M.G.1** (MWG, p. 947), face step: if `f` is nonzero and lies in the direction
space of `B`, the face `{w ∈ B : ⟪f, z⟫ ≤ ⟪f, w⟫}` has a strictly smaller direction space when
`z` maximizes `⟪f, ·⟫` on `B`. -/
theorem closerMG_face_finrank_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Set E} {z f : E} (hfV : f ∈ vectorSpan ℝ B) (hf0 : f ≠ 0)
    (hmax : ∀ w ∈ B, inner ℝ f w ≤ inner ℝ f z) :
    Module.finrank ℝ (vectorSpan ℝ (B ∩ {w | inner ℝ f z ≤ inner ℝ f w})) <
      Module.finrank ℝ (vectorSpan ℝ B) := by
  set F := B ∩ {w | inner ℝ f z ≤ inner ℝ f w}
  have hle : vectorSpan ℝ F ≤ vectorSpan ℝ B := vectorSpan_mono ℝ Set.inter_subset_left
  have hker : vectorSpan ℝ F ≤ LinearMap.ker (innerₛₗ ℝ f) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨w₁, hw₁, w₂, hw₂, rfl⟩
    have e₁ : inner ℝ f w₁ = inner ℝ f z := le_antisymm (hmax _ hw₁.1) hw₁.2
    have e₂ : inner ℝ f w₂ = inner ℝ f z := le_antisymm (hmax _ hw₂.1) hw₂.2
    simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply, vsub_eq_sub,
      inner_sub_right, e₁, e₂, sub_self]
  have hne : vectorSpan ℝ F ≠ vectorSpan ℝ B := by
    intro h
    have : f ∈ LinearMap.ker (innerₛₗ ℝ f) := hker (h ▸ hfV)
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, real_inner_self_eq_norm_sq] at this
    exact hf0 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)

/-- **Theorem M.G.1** (MWG, p. 947), Minkowski's theorem in a finite-dimensional real inner
product space, by induction on the dimension `k` of the affine span: a compact convex set is
contained in the convex hull of its extreme points. -/
theorem closerMG_minkowski_finrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) : ∀ B : Set E, Module.finrank ℝ (vectorSpan ℝ B) = k →
      IsCompact B → Convex ℝ B → B ⊆ convexHull ℝ (B.extremePoints ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro B hk hc hconv x hx
  by_cases hsing : ∀ y ∈ B, y = x
  · apply subset_convexHull
    rw [mem_extremePoints]
    exact ⟨hx, fun x₁ h₁ x₂ h₂ _ => ⟨hsing x₁ h₁, hsing x₂ h₂⟩⟩
  push Not at hsing
  obtain ⟨y, hy, hyx⟩ := hsing
  set V := vectorSpan ℝ B
  have face : ∀ z ∈ B, ∀ e ∈ V, (∀ ε : ℝ, 0 < ε → z + ε • e ∉ B) →
      z ∈ convexHull ℝ (B.extremePoints ℝ) := by
    intro z hz e he hend
    obtain ⟨f, hfV, hf0, hmax⟩ := closerMG_support_of_endpoint hc hconv hz he hend
    set F := B ∩ {w | inner ℝ f z ≤ inner ℝ f w} with hFdef
    have hlt := closerMG_face_finrank_lt hfV hf0 hmax
    have hFc : IsCompact F :=
      hc.inter_right (isClosed_le continuous_const (continuous_const.inner continuous_id))
    have hFconv : Convex ℝ F := by
      refine hconv.inter ?_
      intro w₁ h₁ w₂ h₂ a b ha hb hab
      simp only [Set.mem_ofPred_eq, inner_add_right, inner_smul_right] at h₁ h₂ ⊢
      have hsplit : inner ℝ f z = a * inner ℝ f z + b * inner ℝ f z := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]
    have hext : IsExtreme ℝ B F := by
      refine ⟨Set.inter_subset_left, ?_⟩
      rintro x₁ hx₁ x₂ hx₂ w hw ⟨a, b, ha, hb, hab, rfl⟩
      have h₁ := hmax x₁ hx₁
      have h₂ := hmax x₂ hx₂
      have hw' := hw.2
      simp only [Set.mem_ofPred_eq, inner_add_right, inner_smul_right] at hw'
      have hsplit : inner ℝ f z = a * inner ℝ f z + b * inner ℝ f z := by
        rw [← add_mul, hab, one_mul]
      refine Set.mem_inter hx₁ ?_
      change inner ℝ f z ≤ inner ℝ f x₁
      refine le_of_not_gt fun hcon => ?_
      nlinarith [mul_lt_mul_of_pos_left hcon ha, mul_le_mul_of_nonneg_left h₂ hb.le]
    have hzF : z ∈ F := Set.mem_inter hz (show inner ℝ f z ≤ inner ℝ f z from le_rfl)
    have := ih _ (hk ▸ hlt) F rfl hFc hFconv hzF
    exact convexHull_mono hext.extremePoints_subset_extremePoints this
  set d : E := x - y
  have hdV : d ∈ V := vsub_mem_vectorSpan ℝ hx hy
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hyx)
  obtain ⟨b, hb0, hbB, hbmax⟩ := closerMG_endpoint hc hx hd0
  obtain ⟨a, -, haB, hamax⟩ := closerMG_endpoint hc hx (neg_ne_zero.2 hd0)
  have ha1 : 1 ≤ a := hamax 1 (by simpa [d] using hy)
  have h₁ := face _ hbB d hdV (fun ε hε hmem => by
    have := hbmax (b + ε) (by rwa [add_smul, ← add_assoc])
    linarith)
  have h₂ := face _ haB (-d) (V.neg_mem hdV) (fun ε hε hmem => by
    have := hamax (a + ε) (by rwa [add_smul, ← add_assoc])
    linarith)
  have hab : 0 < a + b := by linarith
  have hx' : (a / (a + b)) • (x + b • d) + (b / (a + b)) • (x + a • -d) = x := by
    have hc1 : a / (a + b) + b / (a + b) = 1 := by
      rw [← add_div, div_self hab.ne']
    calc (a / (a + b)) • (x + b • d) + (b / (a + b)) • (x + a • -d)
        = (a / (a + b) + b / (a + b)) • x + (a / (a + b) * b - b / (a + b) * a) • d := by
          module
      _ = x := by rw [hc1, show a / (a + b) * b - b / (a + b) * a = 0 by ring]; simp
  rw [← hx']
  exact convex_convexHull ℝ _ h₁ h₂ (by positivity) (by positivity)
    (by rw [← add_div, div_self hab.ne'])

/-- **Theorem M.G.1** (MWG, p. 947), Minkowski's theorem in a finite-dimensional real inner
product space: a compact convex set is the convex hull of its extreme points. -/
theorem closerMG_minkowski {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Set E} (hc : IsCompact B) (hconv : Convex ℝ B) :
    convexHull ℝ (B.extremePoints ℝ) = B :=
  Set.Subset.antisymm (convexHull_min extremePoints_subset hconv)
    (closerMG_minkowski_finrank _ B rfl hc hconv)

/-- **Theorem M.G.1** (MWG, p. 947), Minkowski's theorem on `ℝ^N`: a compact convex
`B ⊆ ℝ^N` is the convex hull of its extreme points, `B = Co(ext B)` (no closure needed). -/
theorem theorem_M_G_1_minkowski {N : ℕ} {B : Set (Fin N → ℝ)} (hc : IsCompact B)
    (hconv : Convex ℝ B) : convexHull ℝ (B.extremePoints ℝ) = B := by
  set e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ) := EuclideanSpace.equiv (Fin N) ℝ
  set B' : Set (EuclideanSpace ℝ (Fin N)) := e.symm '' B with hB'
  have hc' : IsCompact B' := hc.image e.symm.continuous
  have hconv' : Convex ℝ B' := hconv.linear_image (e.symm.toLinearEquiv.toLinearMap)
  have hBB : e '' B' = B := by
    rw [hB', Set.image_image]
    simp
  have key := closerMG_minkowski hc' hconv'
  have : e '' convexHull ℝ (B'.extremePoints ℝ) = e '' B' := by rw [key]
  have h1 : e '' convexHull ℝ (B'.extremePoints ℝ) =
      convexHull ℝ (e '' B'.extremePoints ℝ) :=
    LinearMap.image_convexHull (e.toLinearEquiv.toLinearMap) _
  have h2 : e '' B'.extremePoints ℝ = (e '' B').extremePoints ℝ :=
    image_extremePoints e.toLinearEquiv B'
  calc convexHull ℝ (B.extremePoints ℝ) = convexHull ℝ ((e '' B').extremePoints ℝ) := by
        rw [hBB]
    _ = e '' convexHull ℝ (B'.extremePoints ℝ) := by rw [h1, h2]
    _ = B := by rw [this, hBB]

/-- **Theorem M.G.1** (MWG, p. 947), as printed: if `B ⊆ ℝ^N` is convex and compact, every
`x ∈ B` is a convex combination of at most `N + 1` extreme points of `B`. -/
theorem theorem_M_G_1 {N : ℕ} {B : Set (Fin N → ℝ)} (hc : IsCompact B) (hconv : Convex ℝ B)
    {x : Fin N → ℝ} (hx : x ∈ B) :
    ∃ t : Finset (Fin N → ℝ), ↑t ⊆ B.extremePoints ℝ ∧ t.card ≤ N + 1 ∧
      x ∈ convexHull ℝ (t : Set (Fin N → ℝ)) := by
  rw [← theorem_M_G_1_minkowski hc hconv] at hx
  exact caratheodory_M_G_1 hx

/-- **Theorem M.G.1** (MWG, p. 947), with explicit weights: `x = ∑ wᵢ yᵢ` with at most
`N + 1` extreme points `yᵢ` of `B`, `wᵢ ≥ 0`, `∑ wᵢ = 1`. -/
theorem theorem_M_G_1_weights {N : ℕ} {B : Set (Fin N → ℝ)} (hc : IsCompact B)
    (hconv : Convex ℝ B) {x : Fin N → ℝ} (hx : x ∈ B) :
    ∃ t : Finset (Fin N → ℝ), ↑t ⊆ B.extremePoints ℝ ∧ t.card ≤ N + 1 ∧
      ∃ w : (Fin N → ℝ) → ℝ, (∀ y ∈ t, 0 ≤ w y) ∧ ∑ y ∈ t, w y = 1 ∧
        ∑ y ∈ t, w y • y = x := by
  obtain ⟨t, ht, hcard, hxt⟩ := theorem_M_G_1 hc hconv hx
  rw [Finset.mem_convexHull'] at hxt
  obtain ⟨w, hw0, hw1, hwx⟩ := hxt
  exact ⟨t, ht, hcard, w, hw0, hw1, hwx⟩

end MWG.ClassicalDemand
