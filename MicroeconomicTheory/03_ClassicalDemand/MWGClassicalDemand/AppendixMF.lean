/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Mathematical Appendix M.F: continuous functions and compact sets

MWG, Section M.F, pp. 943-945. Vectors are `Fin N → ℝ` with the book's Euclidean distance
`euclidDist`; Mathlib's (sup-norm) topology on `Fin N → ℝ` is the same topology, and the bridges
below show that each definition agrees with Mathlib's notion.

* Definition M.F.1: convergence of sequences (`Filter.Tendsto`).
* Definition M.F.2: sequential continuity on a domain `X` is Mathlib's `ContinuousOn`.
* Definition M.F.3 and Theorem M.F.1(iii): a set is closed iff it contains the limits of its
  convergent sequences (in the ambient case `X = ℝ^N`).
* Definition M.F.4: bounded (Euclidean) and compact (bounded and closed) is Mathlib's
  `IsCompact`.
* Theorem M.F.2: continuous images of compact sets are compact; continuous functions attain a
  maximum on nonempty compact sets.
* Theorem M.F.3: sequential compactness, and compact discrete sets are finite.

Theorem M.F.1(i)-(ii) (unions and intersections of relatively open and closed sets) and the
relative interior, closure and boundary are Mathlib's subspace-topology facts and are only
listed.
-/

namespace MWG.ClassicalDemand

open Filter Topology

variable {N : ℕ}

/-- **Definition M.F.1** (MWG, p. 943). `xᵐ → x` iff for every `ε > 0` there is `M_ε` with
`‖xᵐ - x‖ < ε` (Euclidean) for all `m > M_ε`; this is Mathlib's convergence. -/
theorem definition_M_F_1 (xs : ℕ → Fin N → ℝ) (x : Fin N → ℝ) :
    Tendsto xs atTop (𝓝 x) ↔ ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m, M < m → euclidDist (xs m) x < ε := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    obtain ⟨M, hM⟩ := h (ε / (Real.sqrt N + 1)) (div_pos hε (by linarith))
    refine ⟨M, fun m hm => ?_⟩
    have h1 := euclidDist_le_sqrt_mul_dist (xs m) x
    have h2 := hM m hm.le
    have h3 : Real.sqrt N * dist (xs m) x ≤ Real.sqrt N * (ε / (Real.sqrt N + 1)) :=
      mul_le_mul_of_nonneg_left h2.le hs
    have h4 : Real.sqrt N * (ε / (Real.sqrt N + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    exact ⟨M + 1, fun m hm => (dist_le_euclidDist _ _).trans_lt (hM m (by omega))⟩

/-- **Definition M.F.2** (MWG, p. 943). `f` is continuous on `X` iff `f(xᵐ) → f(x)` for every
`x ∈ X` and every sequence `xᵐ → x` in `X`; this is Mathlib's `ContinuousOn`. -/
theorem definition_M_F_2 {K : ℕ} (X : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → Fin K → ℝ) :
    ContinuousOn f X ↔ ∀ x ∈ X, ∀ xs : ℕ → Fin N → ℝ, (∀ m, xs m ∈ X) →
      Tendsto xs atTop (𝓝 x) → Tendsto (fun m => f (xs m)) atTop (𝓝 (f x)) := by
  constructor
  · intro hf x hx xs hxs ht
    exact (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hxs⟩)
  · intro h x hx
    rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
    intro xs hxs
    obtain ⟨ht, hmem⟩ := tendsto_nhdsWithin_iff.mp hxs
    obtain ⟨M, hM⟩ := eventually_atTop.mp hmem
    have := h x hx (fun m => xs (m + M)) (fun m => hM _ (by omega))
      (ht.comp (tendsto_add_atTop_nat M))
    exact (tendsto_add_atTop_iff_nat M).mp this

/-- **Definition M.F.2** (MWG, p. 943). A function into `ℝ^K` is continuous iff each coordinate
function is. -/
theorem definition_M_F_2_coord {K : ℕ} (X : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → Fin K → ℝ) :
    ContinuousOn f X ↔ ∀ k, ContinuousOn (fun x => f x k) X := continuousOn_pi

/-- **Theorem M.F.1(iii)** (MWG, p. 944), with `X = ℝ^N`. A set is closed iff it contains the
limit of every convergent sequence of its points. -/
theorem theorem_M_F_1_iii (A : Set (Fin N → ℝ)) :
    IsClosed A ↔ ∀ (xs : ℕ → Fin N → ℝ) (x : Fin N → ℝ), (∀ m, xs m ∈ A) →
      Tendsto xs atTop (𝓝 x) → x ∈ A := by
  rw [← isSeqClosed_iff_isClosed]
  exact ⟨fun h xs x hxs ht => h hxs ht, fun h xs x hxs ht => h xs x hxs ht⟩

/-- **Definition M.F.4** (MWG, p. 945). `A` is bounded if `‖x‖ < r` (Euclidean) on `A`. -/
def EuclidBounded (A : Set (Fin N → ℝ)) : Prop := ∃ r : ℝ, ∀ x ∈ A, euclidDist x 0 < r

/-- **Definition M.F.4** (MWG, p. 945). Compactness (bounded and closed) is Mathlib's
`IsCompact`. -/
theorem definition_M_F_4 (A : Set (Fin N → ℝ)) :
    IsCompact A ↔ EuclidBounded A ∧ IsClosed A := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · rintro ⟨hc, hb⟩
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hb
    refine ⟨⟨Real.sqrt N * r + 1, fun x hx => ?_⟩, hc⟩
    have h1 := euclidDist_le_sqrt_mul_dist x 0
    have h2 : dist x 0 ≤ r := hr hx
    have := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (N : ℝ))
    linarith
  · rintro ⟨⟨r, hr⟩, hc⟩
    refine ⟨hc, (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨r, fun x hx => ?_⟩⟩
    exact (Metric.mem_closedBall.mpr ((dist_le_euclidDist x 0).trans (hr x hx).le))

/-- **Theorem M.F.2(i)** (MWG, p. 945). The image of a compact set under a continuous function
is compact. -/
theorem theorem_M_F_2_i {K : ℕ} {X A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → Fin K → ℝ}
    (hf : ContinuousOn f X) (hAX : A ⊆ X) (hA : IsCompact A) : IsCompact (f '' A) :=
  hA.image_of_continuousOn (hf.mono hAX)

/-- **Theorem M.F.2(ii)** (MWG, p. 945). A continuous real function on a nonempty compact set
has a maximizer. -/
theorem theorem_M_F_2_ii {X : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f X)
    (hX : IsCompact X) (hne : X.Nonempty) : ∃ x ∈ X, ∀ x' ∈ X, f x' ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := hX.exists_isMaxOn hne hf
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

/-- **Theorem M.F.3(i)** (MWG, p. 945). Every sequence in a compact set has a subsequence
converging to a point of the set. -/
theorem theorem_M_F_3_i {A : Set (Fin N → ℝ)} (hA : IsCompact A) {xs : ℕ → Fin N → ℝ}
    (hxs : ∀ m, xs m ∈ A) :
    ∃ x ∈ A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (xs ∘ φ) atTop (𝓝 x) :=
  hA.tendsto_subseq hxs

/-- **Theorem M.F.3(ii)** (MWG, p. 945). A compact set all of whose points are isolated
(in Euclidean distance) is finite. -/
theorem theorem_M_F_3_ii {A : Set (Fin N → ℝ)} (hA : IsCompact A)
    (hdisc : ∀ x ∈ A, ∃ ε > 0, ∀ x' ∈ A, euclidDist x' x < ε → x' = x) : A.Finite := by
  by_contra hinf
  obtain ⟨x, hxA, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hA le_rfl
  obtain ⟨ε, hε, hiso⟩ := hdisc x hxA
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hδ : 0 < ε / (Real.sqrt N + 1) := div_pos hε (by linarith)
  obtain ⟨y, ⟨hyU, hyA⟩, hyx⟩ :=
    accPt_iff_nhds.mp hacc (Metric.ball x (ε / (Real.sqrt N + 1))) (Metric.ball_mem_nhds x hδ)
  apply hyx
  apply hiso y hyA
  have h1 := euclidDist_le_sqrt_mul_dist y x
  have h2 : dist y x < ε / (Real.sqrt N + 1) := hyU
  have h3 : Real.sqrt N * dist y x ≤ Real.sqrt N * (ε / (Real.sqrt N + 1)) :=
    mul_le_mul_of_nonneg_left h2.le hs
  have h4 : Real.sqrt N * (ε / (Real.sqrt N + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

end MWG.ClassicalDemand
