/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.DualitySupport
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Convex sets and separating hyperplanes

MWG, Mathematical Appendix, Section M.G, pp. 946-949, on `ℝ^N = Fin N → ℝ`.

* Definitions M.G.1-M.G.4 with bridges to Mathlib (`Convex`, `convexHull`, `Set.extremePoints`,
  `StrictConvex`), the hypograph of a concave function, intersections and unions.
* **Definition M.G.3** and **footnote 14** omit `y ≠ z` (resp. `x ≠ x'`): as printed no point is
  extreme and only open sets are strictly convex (`definition_M_G_3_printed_vacuous`,
  `footnote_M_G_14_printed_open`; correction B5). The corrected definitions are Mathlib's.
* **Theorem M.G.1**: Carathéodory's bound (`caratheodory_M_G_1`) and the Krein-Milman closure
  form (`theorem_M_G_1_closure`) are proved; the exact statement needs Minkowski's theorem
  (`B = Co(ext B)` without closure), which Mathlib lacks: OPEN.
* **Theorem M.G.2** (separating hyperplane): the point/closed-convex-set case for `N ≥ 1`
  (`theorem_M_G_2_i`), and disjoint convex sets for nonempty `A`, `B` (`theorem_M_G_2_ii`).
  The printed statements need these side conditions (`theorem_M_G_2_i_needs_dimension`,
  `theorem_M_G_2_ii_needs_nonempty`; correction B6).
* **Theorem M.G.3** (supporting hyperplane) for `N ≥ 1` (`theorem_M_G_3`).
-/

namespace MWG.ClassicalDemand

open Filter Topology

variable {N : ℕ}

/-- **Definition M.G.1** (MWG, p. 946). `A ⊆ ℝ^N` is convex iff `αx + (1-α)x' ∈ A` whenever
`x, x' ∈ A` and `α ∈ [0, 1]` (Mathlib's `Convex`). -/
theorem definition_M_G_1 (A : Set (Fin N → ℝ)) :
    Convex ℝ A ↔ ∀ x ∈ A, ∀ x' ∈ A, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → α • x + (1 - α) • x' ∈ A := by
  constructor
  · intro h x hx x' hx' α h0 h1
    exact h hx hx' h0 (by linarith) (by ring)
  · intro h x hx x' hx' a b ha hb hab
    have := h x hx x' hx' a ha (by linarith)
    rwa [show 1 - a = b by linarith] at this

/-- **Footnote 14** (MWG, p. 946), as printed: `αx + (1-α)x'` is interior for all `x, x' ∈ A`
and `α ∈ (0, 1)` (no requirement `x ≠ x'`). -/
def StrictlyConvexPrinted (A : Set (Fin N → ℝ)) : Prop :=
  ∀ x ∈ A, ∀ x' ∈ A, ∀ α : ℝ, 0 < α → α < 1 → α • x + (1 - α) • x' ∈ interior A

/-- **Footnote 14** (MWG, p. 946) as printed forces `A` to be open (take `x = x'`), so e.g. the
closed unit interval, which is strictly convex, fails it (correction B5). -/
theorem footnote_M_G_14_printed_open {A : Set (Fin N → ℝ)} (h : StrictlyConvexPrinted A) :
    IsOpen A := by
  have : A ⊆ interior A := by
    intro x hx
    have := h x hx x hx (1 / 2) (by norm_num) (by norm_num)
    rwa [← add_smul, show (1 / 2 : ℝ) + (1 - 1 / 2) = 1 by norm_num, one_smul] at this
  exact interior_eq_iff_isOpen.mp (Set.Subset.antisymm interior_subset this)

/-- **Footnote 14** (MWG, p. 946), corrected: Mathlib's `StrictConvex` is the printed condition
restricted to `x ≠ x'`. -/
theorem footnote_M_G_14 (A : Set (Fin N → ℝ)) :
    StrictConvex ℝ A ↔ ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ∀ α : ℝ, 0 < α → α < 1 →
      α • x + (1 - α) • x' ∈ interior A := by
  constructor
  · intro h x hx x' hx' hne α h0 h1
    exact h hx hx' hne h0 (by linarith) (by ring)
  · intro h x hx x' hx' hne a b ha hb hab
    have := h x hx x' hx' hne a ha (by linarith)
    rwa [show 1 - a = b by linarith] at this

/-- The closed unit interval `[-1, 1] ⊆ ℝ¹` is strictly convex but not strictly convex in the
printed sense of footnote 14. -/
theorem footnote_M_G_14_printed_counterexample :
    StrictConvex ℝ (Metric.closedBall (0 : Fin 1 → ℝ) 1) ∧
      ¬ StrictlyConvexPrinted (Metric.closedBall (0 : Fin 1 → ℝ) 1) := by
  constructor
  · intro x hx y hy hne a b ha hb hab
    rw [interior_closedBall _ one_ne_zero, Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff one_pos]
    rw [Metric.mem_closedBall, dist_zero_right] at hx hy
    have hx0 : |x 0| ≤ 1 := by
      have := norm_le_pi_norm x 0; rw [Real.norm_eq_abs] at this; linarith
    have hy0 : |y 0| ≤ 1 := by
      have := norm_le_pi_norm y 0; rw [Real.norm_eq_abs] at this; linarith
    have hxy : x 0 ≠ y 0 := by
      intro h; apply hne; funext i; rw [Subsingleton.elim i 0]; exact h
    intro i
    rw [Subsingleton.elim i 0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_lt]
    rw [abs_le] at hx0 hy0
    rcases lt_or_gt_of_ne hxy with h | h <;> constructor <;> nlinarith
  · intro h
    have hopen := footnote_M_G_14_printed_open h
    have hne : (Metric.closedBall (0 : Fin 1 → ℝ) 1) ≠ Set.univ := by
      intro h'
      have : (fun _ => 2 : Fin 1 → ℝ) ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 := h' ▸ Set.mem_univ _
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one] at this
      have := this 0
      norm_num at this
    exact hne (IsClopen.eq_univ ⟨Metric.isClosed_closedBall, hopen⟩ ⟨0, by simp⟩)

/-- **Section M.G** (MWG, p. 946). The hypograph `{(z, v) : v ≤ f(z), z ∈ A}` of a concave
function is convex. -/
theorem convex_hypograph_M_G {A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hf : ConcaveOn ℝ A f) : Convex ℝ {zv : (Fin N → ℝ) × ℝ | zv.1 ∈ A ∧ zv.2 ≤ f zv.1} :=
  hf.convex_hypograph

/-- **Section M.G** (MWG, p. 946). Any intersection of convex sets is convex. -/
theorem convex_sInter_M_G {S : Set (Set (Fin N → ℝ))} (h : ∀ A ∈ S, Convex ℝ A) :
    Convex ℝ (⋂₀ S) := convex_sInter h

/-- **Section M.G** (MWG, p. 946). A union of convex sets need not be convex: `{0} ∪ {1}` in
`ℝ¹`. -/
theorem union_not_convex_M_G :
    Convex ℝ ({0} : Set (Fin 1 → ℝ)) ∧ Convex ℝ ({1} : Set (Fin 1 → ℝ)) ∧
      ¬ Convex ℝ (({0} : Set (Fin 1 → ℝ)) ∪ {1}) := by
  refine ⟨convex_singleton 0, convex_singleton 1, fun h => ?_⟩
  have := h (Or.inl rfl) (Or.inr rfl) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rcases this with h1 | h1
  · have := congrFun h1 0; norm_num at this
  · have := congrFun h1 0; norm_num at this

/-- **Definition M.G.2** (MWG, p. 946). The convex hull is the intersection of all convex sets
containing `B`. -/
theorem definition_M_G_2 (B : Set (Fin N → ℝ)) :
    convexHull ℝ B = ⋂ (t : Set (Fin N → ℝ)) (_ : B ⊆ t) (_ : Convex ℝ t), t :=
  convexHull_eq_iInter ℝ B

/-- **Section M.G** (MWG, p. 946). The convex hull is the set of convex combinations
`∑ α_j x_j` of finitely many `x_j ∈ B` with `α_j ≥ 0`, `∑ α_j = 1`. -/
theorem convexHull_eq_combinations (B : Set (Fin N → ℝ)) (x : Fin N → ℝ) :
    x ∈ convexHull ℝ B ↔ ∃ (J : ℕ) (α : Fin J → ℝ) (y : Fin J → Fin N → ℝ),
      (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1 ∧ (∀ j, y j ∈ B) ∧ ∑ j, α j • y j = x := by
  rw [mem_convexHull_iff_exists_fintype]
  constructor
  · rintro ⟨ι, _, w, z, hw, hsum, hz, hx⟩
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, w ∘ e.symm, z ∘ e.symm, fun j => hw _, ?_, fun j => hz _, ?_⟩
    · rw [← hsum]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    · rw [← hx]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · rintro ⟨J, α, y, hα, hsum, hy, hx⟩
    exact ⟨Fin J, inferInstance, α, y, hα, hsum, hy, hx⟩

/-- **Definition M.G.3** (MWG, p. 946) as printed: `x ∈ B` cannot be written as
`αy + (1-α)z` with `y, z ∈ B`, `α ∈ (0, 1)`. -/
def ExtremePointPrinted (B : Set (Fin N → ℝ)) (x : Fin N → ℝ) : Prop :=
  x ∈ B ∧ ¬ ∃ y ∈ B, ∃ z ∈ B, ∃ α : ℝ, 0 < α ∧ α < 1 ∧ x = α • y + (1 - α) • z

/-- **Definition M.G.3** (MWG, p. 946) as printed is vacuous (correction B5): every `x ∈ B` is
`αx + (1-α)x`, so no set has an extreme point in the printed sense, contradicting Figure
M.G.3 and Theorem M.G.1. -/
theorem definition_M_G_3_printed_vacuous (B : Set (Fin N → ℝ)) (x : Fin N → ℝ) :
    ¬ ExtremePointPrinted B x := by
  rintro ⟨hx, h⟩
  exact h ⟨x, hx, x, hx, 1 / 2, by norm_num, by norm_num, by
    rw [← add_smul, show (1 / 2 : ℝ) + (1 - 1 / 2) = 1 by norm_num, one_smul]⟩

/-- **Definition M.G.3** (MWG, p. 946), corrected: `x` is an extreme point of `B` iff it is not
`αy + (1-α)z` for distinct `y, z ∈ B` and `α ∈ (0, 1)`; this is Mathlib's `extremePoints`. -/
theorem definition_M_G_3 (B : Set (Fin N → ℝ)) (x : Fin N → ℝ) :
    x ∈ B.extremePoints ℝ ↔ x ∈ B ∧ ∀ y ∈ B, ∀ z ∈ B, y ≠ z → ∀ α : ℝ, 0 < α → α < 1 →
      x ≠ α • y + (1 - α) • z := by
  rw [mem_extremePoints]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy z hz hyz α h0 h1 heq => hyz ?_⟩
    have hseg : x ∈ openSegment ℝ y z := ⟨α, 1 - α, h0, by linarith, by ring, heq.symm⟩
    obtain ⟨h1, h2⟩ := h y hy z hz hseg
    rw [h1, h2]
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy z hz hseg => ?_⟩
    by_cases hyz : y = z
    · subst hyz
      rw [openSegment_same, Set.mem_singleton_iff] at hseg
      exact ⟨hseg.symm, hseg.symm⟩
    · exfalso
      obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
      exact h y hy z hz hyz a ha (by linarith) (by rw [← heq, show 1 - a = b by linarith])

/-- **Theorem M.G.1** (MWG, p. 947), Carathéodory's part: every point of the convex hull of a
set `S ⊆ ℝ^N` is a convex combination of at most `N + 1` points of `S`. -/
theorem caratheodory_M_G_1 {S : Set (Fin N → ℝ)} {x : Fin N → ℝ} (hx : x ∈ convexHull ℝ S) :
    ∃ t : Finset (Fin N → ℝ), ↑t ⊆ S ∧ t.card ≤ N + 1 ∧ x ∈ convexHull ℝ (t : Set _) := by
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, hts, hai, hxt⟩ := hx
  refine ⟨t, hts, ?_, hxt⟩
  have h1 := hai.card_le_finrank_succ
  have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Fin N → ℝ))) ≤ N := by
    have := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → Fin N → ℝ)))
    simpa using this
  rw [Fintype.card_coe] at h1
  omega

/-- **Theorem M.G.1** (MWG, p. 947), the Krein-Milman form: a compact convex `B ⊆ ℝ^N` is the
closure of the convex hull of its extreme points. -/
theorem theorem_M_G_1_closure {B : Set (Fin N → ℝ)} (hc : IsCompact B) (hconv : Convex ℝ B) :
    closure (convexHull ℝ (B.extremePoints ℝ)) = B :=
  closure_convexHull_extremePoints hc hconv

/-- **Definition M.G.4** (MWG, p. 947). The half-space below the hyperplane `H_{p,c}`,
`{z : p·z ≤ c}`; the half-space above is `halfSpace p c` and the hyperplane `hyperplane p c`. -/
def halfSpaceBelow (p : Fin N → ℝ) (c : ℝ) : Set (Fin N → ℝ) := {z | p ⬝ᵥ z ≤ c}

/-- **Section M.G** (MWG, p. 947). Half-spaces below a hyperplane are convex. -/
theorem convex_halfSpaceBelow (p : Fin N → ℝ) (c : ℝ) : Convex ℝ (halfSpaceBelow p c) := by
  intro x hx y hy a b ha hb hab
  simp only [halfSpaceBelow, Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at *
  have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- A nonzero vector of `ℝ^N` for `N ≥ 1`. -/
theorem appendixMG_exists_ne_zero_vec (hN : 0 < N) : ∃ p : Fin N → ℝ, p ≠ 0 :=
  ⟨Pi.single ⟨0, hN⟩ 1, fun h => by simpa using congrFun h ⟨0, hN⟩⟩

/-- **Theorem M.G.2** (MWG, p. 948), first part (separating a point from a closed convex set),
for `N ≥ 1`: there are `p ≠ 0` and `c` with `p·x > c` and `p·y < c` for every `y ∈ B`. -/
theorem theorem_M_G_2_i (hN : 0 < N) {B : Set (Fin N → ℝ)} (hB : Convex ℝ B)
    (hcl : IsClosed B) {x : Fin N → ℝ} (hx : x ∉ B) :
    ∃ p : Fin N → ℝ, p ≠ 0 ∧ ∃ c : ℝ, c < p ⬝ᵥ x ∧ ∀ y ∈ B, p ⬝ᵥ y < c := by
  obtain ⟨f, u, hfB, hfx⟩ := geometric_hahn_banach_closed_point hB hcl hx
  obtain ⟨p, hp⟩ := duality_exists_dot_of_clm f
  rcases B.eq_empty_or_nonempty with hB0 | ⟨y0, hy0⟩
  · subst hB0
    obtain ⟨q, hq⟩ := appendixMG_exists_ne_zero_vec hN
    exact ⟨q, hq, q ⬝ᵥ x - 1, by linarith, fun y hy => absurd hy (Set.notMem_empty y)⟩
  refine ⟨p, ?_, u, by rw [← hp]; exact hfx, fun y hy => by rw [← hp]; exact hfB y hy⟩
  rintro rfl
  have h1 := hfB y0 hy0
  rw [hp, zero_dotProduct] at h1
  rw [hp, zero_dotProduct] at hfx
  linarith

/-- **Theorem M.G.2(i)** needs `N ≥ 1` (correction B6): in `ℝ⁰` the closed convex set `∅` and
the point `0 ∉ ∅` admit no `p ≠ 0`. -/
theorem theorem_M_G_2_i_needs_dimension :
    Convex ℝ (∅ : Set (Fin 0 → ℝ)) ∧ IsClosed (∅ : Set (Fin 0 → ℝ)) ∧
      (0 : Fin 0 → ℝ) ∉ (∅ : Set (Fin 0 → ℝ)) ∧ ∀ p : Fin 0 → ℝ, p = 0 :=
  ⟨convex_empty, isClosed_empty, Set.notMem_empty _, fun _ => funext fun i => i.elim0⟩

/-- **Theorem M.G.3 (supporting hyperplane theorem)** (MWG, p. 949), for `N ≥ 1`: if `B` is
convex and `x ∉ Int B`, there is `p ≠ 0` with `p·x ≥ p·y` for every `y ∈ B`. -/
theorem theorem_M_G_3 (hN : 0 < N) {B : Set (Fin N → ℝ)} (hB : Convex ℝ B) {x : Fin N → ℝ}
    (hx : x ∉ interior B) : ∃ p : Fin N → ℝ, p ≠ 0 ∧ ∀ y ∈ B, p ⬝ᵥ y ≤ p ⬝ᵥ x := by
  rcases B.eq_empty_or_nonempty with hB0 | ⟨y0, hy0⟩
  · obtain ⟨q, hq⟩ := appendixMG_exists_ne_zero_vec hN
    exact ⟨q, hq, fun y hy => by rw [hB0] at hy; exact absurd hy (Set.notMem_empty y)⟩
  by_cases hint : (interior B).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hB.interior isOpen_interior hx
    obtain ⟨p, hp⟩ := duality_exists_dot_of_clm f
    obtain ⟨a, ha⟩ := hint
    refine ⟨p, ?_, fun y hy => ?_⟩
    · rintro rfl
      have := hf a ha
      rw [hp, hp, zero_dotProduct, zero_dotProduct] at this
      exact lt_irrefl _ this
    · have hcl : y ∈ closure (interior B) := by
        rw [hB.closure_interior_eq_closure_of_nonempty_interior ⟨a, ha⟩]
        exact subset_closure hy
      have hsub : closure (interior B) ⊆ {z | p ⬝ᵥ z ≤ p ⬝ᵥ x} :=
        closure_minimal (fun z hz => by rw [Set.mem_ofPred_eq, ← hp, ← hp]; exact (hf z hz).le)
          (isClosed_le (by fun_prop) continuous_const)
      exact hsub hcl
  · have hspan : affineSpan ℝ B ≠ ⊤ := by
      intro h
      exact hint ((hB.interior_nonempty_iff_affineSpan_eq_top).mpr h)
    have hdir : (affineSpan ℝ B).direction < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨y0, subset_affineSpan ℝ B hy0⟩).mp h)
    obtain ⟨f, hf0, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hdir inferInstance
    obtain ⟨p, hp⟩ := duality_exists_dot_of_clm (LinearMap.toContinuousLinearMap f)
    have hp' : ∀ z, f z = p ⬝ᵥ z := fun z => hp z
    have hpne : p ≠ 0 := by
      rintro rfl
      exact hf0 (LinearMap.ext fun z => by rw [hp', zero_dotProduct, LinearMap.zero_apply])
    have hconst : ∀ y ∈ B, p ⬝ᵥ y = p ⬝ᵥ y0 := by
      intro y hy
      have hmem : y -ᵥ y0 ∈ (affineSpan ℝ B).direction := by
        rw [direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hy hy0
      have : f (y -ᵥ y0) = 0 := by
        have := Submodule.mem_map_of_mem (f := f) hmem
        rw [hmap, Submodule.mem_bot] at this
        exact this
      rw [hp', vsub_eq_sub, dotProduct_sub, sub_eq_zero] at this
      exact this
    by_cases hsign : p ⬝ᵥ y0 ≤ p ⬝ᵥ x
    · exact ⟨p, hpne, fun y hy => (hconst y hy).trans_le hsign⟩
    · refine ⟨-p, neg_ne_zero.mpr hpne, fun y hy => ?_⟩
      rw [neg_dotProduct, neg_dotProduct, neg_le_neg_iff, hconst y hy]
      exact (not_le.mp hsign).le

open scoped Pointwise in
/-- **Theorem M.G.2** (MWG, p. 948), second part, for nonempty disjoint convex `A, B ⊆ ℝ^N`
(`N ≥ 1`): there are `p ≠ 0` and `c` with `p·x ≥ c` on `A` and `p·y ≤ c` on `B`. -/
theorem theorem_M_G_2_ii (hN : 0 < N) {A B : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B) :
    ∃ p : Fin N → ℝ, p ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ p ⬝ᵥ x) ∧ ∀ y ∈ B, p ⬝ᵥ y ≤ c := by
  have hD : Convex ℝ (A - B) := hA.sub hB
  have h0 : (0 : Fin N → ℝ) ∉ interior (A - B) := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := interior_subset h
    exact Set.disjoint_left.mp hdisj ha (by rw [sub_eq_zero.mp hab]; exact hb)
  obtain ⟨p, hp, hsup⟩ := theorem_M_G_3 hN hD h0
  have hab : ∀ a ∈ A, ∀ b ∈ B, p ⬝ᵥ a ≤ p ⬝ᵥ b := by
    intro a ha b hb
    have := hsup (a - b) ⟨a, ha, b, hb, rfl⟩
    rw [dotProduct_zero, dotProduct_sub] at this
    linarith
  obtain ⟨b0, hb0⟩ := hBne
  refine ⟨-p, neg_ne_zero.mpr hp, sInf ((fun a => -p ⬝ᵥ a) '' A), fun x hx => ?_, fun y hy => ?_⟩
  · apply csInf_le
    · refine ⟨-p ⬝ᵥ b0, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      simp only [neg_dotProduct, neg_le_neg_iff]
      exact hab a ha b0 hb0
    · exact ⟨x, hx, rfl⟩
  · apply le_csInf (hAne.image _)
    rintro _ ⟨a, ha, rfl⟩
    simp only [neg_dotProduct, neg_le_neg_iff]
    exact hab a ha y hy

/-- **Theorem M.G.2(ii)** needs nonempty sets (correction B6): `∅` and `ℝ^N` are disjoint and
convex, but no `p ≠ 0` and `c` have `p·y ≤ c` on all of `ℝ^N`. -/
theorem theorem_M_G_2_ii_needs_nonempty :
    Convex ℝ (∅ : Set (Fin N → ℝ)) ∧ Convex ℝ (Set.univ : Set (Fin N → ℝ)) ∧
      Disjoint (∅ : Set (Fin N → ℝ)) Set.univ ∧
      ¬ ∃ p : Fin N → ℝ, p ≠ 0 ∧ ∃ c : ℝ, ∀ y : Fin N → ℝ, p ⬝ᵥ y ≤ c := by
  refine ⟨convex_empty, convex_univ, Set.empty_disjoint _, ?_⟩
  rintro ⟨p, hp, c, hc⟩
  have hpp : 0 < p ⬝ᵥ p := by
    have h0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
    have hne : p ⬝ᵥ p ≠ 0 := fun h => hp (dotProduct_self_eq_zero.mp h)
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  have := hc (((|c| + 1) / (p ⬝ᵥ p)) • p)
  rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hpp.ne'] at this
  have := le_abs_self c
  linarith

end MWG.ClassicalDemand
