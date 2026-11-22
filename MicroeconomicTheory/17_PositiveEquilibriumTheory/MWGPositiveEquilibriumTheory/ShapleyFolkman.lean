/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Shapley-Folkman theorem and the convexifying effect of replication
(MWG Section 17.I, pp. 627-629)

Section 17.I asserts (p. 628) that "for any `p ≫ 0` and whatever the number of commodities, as
`r → ∞` the per-replica excess demand `z_{ir}(p)` of type `i` converges as a set to the convex
hull of `zᵢ(p)`", where `z_{ir}(p) = (1/r)(zᵢ(p) + ⋯ + zᵢ(p))` (`r` terms). The book gives the
argument only for two demand points (the integers `a_r` with `|a_r/r - α| ≤ 1/r`). The general
statement is a consequence of the **Shapley-Folkman theorem** (Starr 1969, cited in footnote
72), proved here from Carathéodory's theorem (Mathlib's `eq_pos_convex_span_of_mem_convexHull`):

* `shapley_folkman`: in a real vector space of dimension `N`, if `xₖ ∈ conv Sₖ` for finitely many
  sets `Sₖ`, there are `yₖ ∈ conv Sₖ` with `∑ₖ yₖ = ∑ₖ xₖ` and `yₖ ∈ Sₖ` for all but at most
  `N` indices `k`. The proof lifts `Sₖ` to `Sₖ × {eₖ} ⊆ E × ℝ^K`, applies Carathéodory there, and
  counts with the affine dimension of the hyperplane `∑ₖ cₖ = 1` (`dim E + K - 1`).
* `perReplicaSet Z r = (1/r)(Z + ⋯ + Z)`; `perReplicaSet_subset_convexHull`;
  `convexHull_near_perReplica` (every point of `conv Z` is within `N·diam Z / r` of
  `perReplicaSet Z r`) and `tendsto_hausdorffDist_perReplica` (Hausdorff convergence to `conv Z`
  for bounded `Z`).
* The book's two-point argument (p. 628): `exists_nat_near` (`a_r`), `twoPoint_mem_perReplica`,
  `twoPoint_near`.
-/

namespace MWG.PositiveEquilibriumTheory

open Module Filter Topology

/-! ### The Shapley-Folkman theorem -/

open Classical in
/-- **The Shapley-Folkman theorem** (Starr 1969, MWG footnote 72, p. 628; the general fact
behind "this convexifying property is completely general", p. 628). Let `E` be a real vector
space of finite dimension `N` and `Sₖ ⊆ E` finitely many sets. If `xₖ ∈ conv Sₖ` for every `k`,
then there are `yₖ ∈ conv Sₖ` with `∑ₖ yₖ = ∑ₖ xₖ` such that `yₖ ∈ Sₖ` for all but at most `N`
indices. -/
theorem shapley_folkman {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {κ : Type*} [Fintype κ] (S : κ → Set E) (x : κ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (S k)) :
    ∃ y : κ → E, (∀ k, y k ∈ convexHull ℝ (S k)) ∧ ∑ k, y k = ∑ k, x k ∧
      (Finset.univ.filter fun k => y k ∉ S k).card ≤ finrank ℝ E := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨x, hx, rfl, by simp⟩
  set n : ℕ := Fintype.card κ with hn_def
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  set e : κ → κ → ℝ := fun k => Pi.single k 1 with he
  set T : Set (E × (κ → ℝ)) := ⋃ k, S k ×ˢ {e k} with hT
  have hlift : ∀ k, (x k, e k) ∈ convexHull ℝ T := by
    intro k
    have h1 : (x k, e k) ∈ convexHull ℝ (S k ×ˢ {e k}) := by
      rw [convexHull_prod, convexHull_singleton]
      exact ⟨hx k, Set.mem_singleton _⟩
    exact convexHull_mono (Set.subset_iUnion (fun k => S k ×ˢ {e k}) k) h1
  have hP : (∑ k, (n : ℝ)⁻¹ • (x k, e k)) ∈ convexHull ℝ T := by
    refine (convex_convexHull ℝ T).sum_mem (fun _ _ => inv_nonneg.2 hn.le) ?_ fun k _ => hlift k
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
    exact mul_inv_cancel₀ hn.ne'
  obtain ⟨ι, _, z, w, hzT, hai, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hP
  have hmem : ∀ j, ∃ k, (z j).1 ∈ S k ∧ (z j).2 = e k := by
    intro j
    have h := hzT ⟨j, rfl⟩
    rw [hT, Set.mem_iUnion] at h
    obtain ⟨k, hk1, hk2⟩ := h
    exact ⟨k, hk1, hk2⟩
  choose kk hkS hke using hmem
  -- second components: the weights of the points lifted from `Sₖ` add up to `1/n`
  have hsnd : ∑ j, w j • (z j).2 = ∑ k, (n : ℝ)⁻¹ • e k := by
    have := congrArg Prod.snd hwz
    simpa only [Prod.snd_sum, Prod.smul_snd] using this
  have hfib : ∀ k, ∑ j ∈ Finset.univ.filter (fun j => kk j = k), w j = (n : ℝ)⁻¹ := by
    intro k
    have h := congrFun hsnd k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, he, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h
    rw [← h, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hke j]
    by_cases hj : kk j = k
    · simp [hj, he]
    · simp [hj, Ne.symm hj, he]
  have hfst : ∑ j, w j • (z j).1 = (n : ℝ)⁻¹ • ∑ k, x k := by
    have := congrArg Prod.fst hwz
    simp only [Prod.fst_sum, Prod.smul_fst] at this
    rw [this, Finset.smul_sum]
  set J : κ → Finset ι := fun k => Finset.univ.filter (fun j => kk j = k) with hJ
  set y : κ → E := fun k => ∑ j ∈ J k, ((n : ℝ) * w j) • (z j).1 with hy
  -- each `J k` is nonempty, and `y k ∉ S k` forces `|J k| ≥ 2`
  have hJne : ∀ k, (J k).Nonempty := by
    intro k
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have h : ∑ j ∈ J k, w j = (n : ℝ)⁻¹ := hfib k
    simp only [h0, Finset.sum_empty] at h
    exact (inv_pos.2 hn).ne h
  have hbad : ∀ k, y k ∉ S k → 2 ≤ (J k).card := by
    intro k hk
    by_contra hlt
    push Not at hlt
    have h1 : (J k).card = 1 := by
      have := Finset.card_pos.2 (hJne k)
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h1
    have hjk : kk j = k := by
      have : j ∈ J k := by rw [hj]; exact Finset.mem_singleton_self j
      exact (Finset.mem_filter.1 this).2
    have hwj : w j = (n : ℝ)⁻¹ := by
      have h : ∑ j ∈ J k, w j = (n : ℝ)⁻¹ := hfib k
      simpa [hj] using h
    apply hk
    simp only [hy, hj, Finset.sum_singleton, hwj, mul_inv_cancel₀ hn.ne', one_smul]
    exact hjk ▸ hkS j
  -- the dimension count: `|ι| ≤ dim E + n`
  have hcard : Fintype.card ι ≤ finrank ℝ E + n := by
    let φ : (E × (κ → ℝ)) →ₗ[ℝ] ℝ :=
      (∑ k : κ, (LinearMap.proj k : (κ → ℝ) →ₗ[ℝ] ℝ)).comp (LinearMap.snd ℝ E (κ → ℝ))
    have hφz : ∀ j, φ (z j) = 1 := by
      intro j
      simp [φ, hke j, he, Pi.single_apply]
    have hspan : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker φ := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨j', rfl⟩, rfl⟩
      simp [vsub_eq_sub, hφz]
    have hι : 0 < Fintype.card ι := by
      rcases isEmpty_or_nonempty ι with h | h
      · simp at hw1
      · exact Fintype.card_pos
    obtain ⟨j₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 hι
    have hv := hai.finrank_vectorSpan (n := Fintype.card ι - 1) (by omega)
    have hmono := Submodule.finrank_mono hspan
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : 1 ≤ finrank ℝ (LinearMap.range φ) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Submodule.finrank_eq_zero] at h0
      have h := LinearMap.mem_range_self φ (z j₀)
      rw [h0, Submodule.mem_bot, hφz] at h
      exact one_ne_zero h
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at hrk
    omega
  refine ⟨y, fun k => ?_, ?_, ?_⟩
  · refine (convex_convexHull ℝ (S k)).sum_mem (fun j _ => mul_nonneg hn.le (hw0 j).le) ?_ ?_
    · rw [← Finset.mul_sum, hfib k, mul_inv_cancel₀ hn.ne']
    · intro j hj
      have : kk j = k := (Finset.mem_filter.1 hj).2
      exact subset_convexHull ℝ _ (this ▸ hkS j)
  · calc ∑ k, y k = ∑ j, ((n : ℝ) * w j) • (z j).1 :=
          Finset.sum_fiberwise Finset.univ kk fun j => ((n : ℝ) * w j) • (z j).1
      _ = (n : ℝ) • ∑ j, w j • (z j).1 := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]
      _ = ∑ k, x k := by rw [hfst, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  · have hge : ∀ k ∈ Finset.univ, 1 + (if y k ∉ S k then 1 else 0) ≤ (J k).card := by
      intro k _
      by_cases h : y k ∉ S k
      · simp only [h, not_false_eq_true, ↓reduceIte]
        exact hbad k h
      · simp only [h, ↓reduceIte, add_zero]
        exact Finset.card_pos.2 (hJne k)
    have hsum := Finset.sum_le_sum hge
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Finset.card_filter] at hsum
    have hfibcard : Fintype.card ι = ∑ k, (J k).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise fun j _ => Finset.mem_univ (kk j)
    omega

/-! ### Per-replica sets -/

/-- **Section 17.I** (MWG, p. 628). The per-replica average of `r` copies of a set:
`(1/r)(Z + ⋯ + Z) = {(1/r)(z₁ + ⋯ + z_r) : zₖ ∈ Z}` (the sum has `r` terms). -/
def perReplicaSet {E : Type*} [AddCommGroup E] [Module ℝ E] (Z : Set E) (r : ℕ) : Set E :=
  {y | ∃ z : Fin r → E, (∀ k, z k ∈ Z) ∧ y = (r : ℝ)⁻¹ • ∑ k, z k}

/-- **Section 17.I** (MWG, p. 628). For `r ≥ 1`, `(1/r)(Z + ⋯ + Z) ⊆ conv Z`. -/
theorem perReplicaSet_subset_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] (Z : Set E)
    {r : ℕ} (hr : 0 < r) : perReplicaSet Z r ⊆ convexHull ℝ Z := by
  rintro _ ⟨z, hz, rfl⟩
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ Z).sum_mem (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)) ?_
    fun k _ => subset_convexHull ℝ Z (hz k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hr'

/-- **Section 17.I** (MWG, p. 628), via the Shapley-Folkman theorem. In a finite-dimensional
normed space, every point of the convex hull of a bounded set `Z` lies within
`(dim E)·diam Z / r` of the per-replica set `(1/r)(Z + ⋯ + Z)`. -/
theorem convexHull_near_perReplica {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Z : Set E} (hZ : Bornology.IsBounded Z) {r : ℕ} (hr : 0 < r)
    {y : E} (hy : y ∈ convexHull ℝ Z) :
    ∃ y' ∈ perReplicaSet Z r, ‖y - y'‖ ≤ finrank ℝ E * Metric.diam Z / r := by
  classical
  obtain ⟨v, hv, hsum, hcard⟩ := shapley_folkman (fun _ : Fin r => Z) (fun _ => y) fun _ => hy
  have hZne : Z.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty] at hy
    exact hy
  obtain ⟨z0, hz0⟩ := hZne
  set z : Fin r → E := fun k => if v k ∈ Z then v k else z0 with hzdef
  have hz : ∀ k, z k ∈ Z := fun k => by
    by_cases h : v k ∈ Z
    · simp only [hzdef, h, ↓reduceIte]
    · simp only [hzdef, h, ↓reduceIte, hz0]
  refine ⟨(r : ℝ)⁻¹ • ∑ k, z k, ⟨z, hz, rfl⟩, ?_⟩
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have hy_eq : y = (r : ℝ)⁻¹ • ∑ k, v k := by
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, inv_mul_cancel₀ hr', one_smul]
  have hbd : Bornology.IsBounded (convexHull ℝ Z) := isBounded_convexHull.2 hZ
  have hterm : ∀ k, ‖v k - z k‖ ≤ if v k ∉ Z then Metric.diam Z else 0 := by
    intro k
    by_cases h : v k ∈ Z
    · simp [hzdef, h]
    · simp only [hzdef, h, ↓reduceIte, not_false_eq_true]
      rw [← dist_eq_norm, ← convexHull_diam]
      exact Metric.dist_le_diam_of_mem hbd (hv k) (subset_convexHull ℝ Z hz0)
  have hdiam : 0 ≤ Metric.diam Z := Metric.diam_nonneg
  have hcard' : ((Finset.univ.filter fun k => v k ∉ Z).card : ℝ) ≤ finrank ℝ E := by
    exact_mod_cast hcard
  calc ‖y - (r : ℝ)⁻¹ • ∑ k, z k‖ = (r : ℝ)⁻¹ * ‖∑ k, (v k - z k)‖ := by
        rw [hy_eq, ← smul_sub, norm_smul, ← Finset.sum_sub_distrib, Real.norm_eq_abs, abs_inv,
          Nat.abs_cast]
    _ ≤ (r : ℝ)⁻¹ * ∑ k, (if v k ∉ Z then Metric.diam Z else 0) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
    _ = (r : ℝ)⁻¹ * ((Finset.univ.filter fun k => v k ∉ Z).card * Metric.diam Z) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ)⁻¹ * (finrank ℝ E * Metric.diam Z) := by gcongr
    _ = finrank ℝ E * Metric.diam Z / r := by ring

/-- **Section 17.I** (MWG, p. 628). As `r → ∞`, the per-replica set `(1/r)(Z + ⋯ + Z)` of a
bounded set `Z` in a finite-dimensional normed space converges to `conv Z` in the Hausdorff
distance ("converges as a set to the convex hull"). -/
theorem tendsto_hausdorffDist_perReplica {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Z : Set E} (hZ : Bornology.IsBounded Z) :
    Tendsto (fun r : ℕ => Metric.hausdorffDist (perReplicaSet Z r) (convexHull ℝ Z)) atTop
      (𝓝 0) := by
  set C : ℝ := finrank ℝ E * Metric.diam Z with hC
  have hC0 : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) Metric.diam_nonneg
  have hle : ∀ᶠ r : ℕ in atTop,
      Metric.hausdorffDist (perReplicaSet Z r) (convexHull ℝ Z) ≤ C / r := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    refine Metric.hausdorffDist_le_of_mem_dist (div_nonneg hC0 (Nat.cast_nonneg _)) ?_ ?_
    · intro y hy
      refine ⟨y, perReplicaSet_subset_convexHull Z hr hy, ?_⟩
      rw [dist_self]
      exact div_nonneg hC0 (Nat.cast_nonneg _)
    · intro y hy
      obtain ⟨y', hy', hd⟩ := convexHull_near_perReplica hZ hr hy
      exact ⟨y', hy', by rw [dist_eq_norm]; exact hd⟩
  exact squeeze_zero' (Eventually.of_forall fun _ => Metric.hausdorffDist_nonneg) hle
    (tendsto_const_div_atTop_nhds_zero_nat C)

/-! ### The book's two-point argument (p. 628) -/

/-- A sum over `Fin r` of a two-valued expression: `∑ₖ (if k < a then u else v) =
a • u + (r - a) • v` for `a ≤ r`. -/
theorem sum_fin_ite_lt {M : Type*} [AddCommMonoid M] {r a : ℕ} (har : a ≤ r) (u v : M) :
    ∑ k : Fin r, (if (k : ℕ) < a then u else v) = a • u + (r - a) • v := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < a then u else v) r,
    ← Finset.sum_range_add_sum_Ico _ har]
  have h1 : ∑ k ∈ Finset.range a, (if k < a then u else v) = a • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u) fun k hk => by
      simp [Finset.mem_range.1 hk], Finset.sum_const,
      Finset.card_range]
  have h2 : ∑ k ∈ Finset.Ico a r, (if k < a then u else v) = (r - a) • v := by
    rw [Finset.sum_congr rfl (g := fun _ => v) fun k hk => by
      simp [not_lt.2 (Finset.mem_Ico.1 hk).1],
      Finset.sum_const, Nat.card_Ico]
  rw [h1, h2]

/-- **Section 17.I** (MWG, p. 628). For any `α ∈ [0, 1]` and integer `r ≥ 1` there is an integer
`a_r ∈ [0, r]` with `|a_r/r - α| ≤ 1/r`. -/
theorem exists_nat_near {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {r : ℕ} (hr : 0 < r) :
    ∃ a : ℕ, a ≤ r ∧ |(a : ℝ) / r - α| ≤ 1 / r := by
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have hαr : 0 ≤ α * r := mul_nonneg hα0 hrpos.le
  refine ⟨⌊α * r⌋₊, ?_, ?_⟩
  · have h1 : (⌊α * r⌋₊ : ℝ) ≤ r :=
      (Nat.floor_le hαr).trans (by nlinarith)
    exact_mod_cast h1
  · have h1 := Nat.floor_le hαr
    have h2 := Nat.lt_floor_add_one (α * r)
    have heq : (⌊α * r⌋₊ : ℝ) / r - α = (⌊α * r⌋₊ - α * r) / r := by field_simp
    rw [heq, abs_div, abs_of_pos hrpos]
    gcongr
    rw [abs_le]
    constructor <;> linarith

/-- **Section 17.I** (MWG, p. 628). Putting `a_r` consumers at `x₁` and `r - a_r` at `x'₁`
gives the per-replica consumption `(a_r/r)x₁ + (1 - a_r/r)x'₁ ∈ (1/r)({x₁, x'₁} + ⋯)`. -/
theorem twoPoint_mem_perReplica {E : Type*} [AddCommGroup E] [Module ℝ E] (x₁ x₁' : E) {r a : ℕ}
    (hr : 0 < r) (har : a ≤ r) :
    ((a : ℝ) / r) • x₁ + (1 - (a : ℝ) / r) • x₁' ∈ perReplicaSet {x₁, x₁'} r := by
  classical
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  refine ⟨fun k => if (k : ℕ) < a then x₁ else x₁', fun k => ?_, ?_⟩
  · by_cases h : (k : ℕ) < a
    · simp [h]
    · simp [h]
  · rw [sum_fin_ite_lt har, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ,
      Nat.cast_sub har, smul_add, smul_smul, smul_smul]
    congr 2
    · field_simp
    · field_simp

/-- **Section 17.I** (MWG, p. 628). The per-replica consumption of `twoPoint_mem_perReplica`
is within `‖x₁ - x'₁‖/r` of `αx₁ + (1 - α)x'₁`: "by taking `r` large enough, comes as close to
`αx₁ + (1 - α)x'₁` as we wish". -/
theorem twoPoint_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x₁ x₁' : E)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {r : ℕ} (hr : 0 < r) :
    ∃ y ∈ perReplicaSet {x₁, x₁'} r,
      ‖y - (α • x₁ + (1 - α) • x₁')‖ ≤ ‖x₁ - x₁'‖ / r := by
  obtain ⟨a, har, hnear⟩ := exists_nat_near hα0 hα1 hr
  refine ⟨_, twoPoint_mem_perReplica x₁ x₁' hr har, ?_⟩
  have heq : ((a : ℝ) / r) • x₁ + (1 - (a : ℝ) / r) • x₁' - (α • x₁ + (1 - α) • x₁') =
      ((a : ℝ) / r - α) • (x₁ - x₁') := by module
  rw [heq, norm_smul, Real.norm_eq_abs]
  calc |(a : ℝ) / r - α| * ‖x₁ - x₁'‖ ≤ 1 / r * ‖x₁ - x₁'‖ :=
        mul_le_mul_of_nonneg_right hnear (norm_nonneg _)
    _ = ‖x₁ - x₁'‖ / r := by ring

end MWG.PositiveEquilibriumTheory
