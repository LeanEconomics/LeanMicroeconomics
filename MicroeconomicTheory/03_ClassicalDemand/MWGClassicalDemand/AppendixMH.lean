/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CorrespondenceMaximum
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Correspondences

MWG, Mathematical Appendix, Section M.H, pp. 949-952.

The book works with `A ⊆ ℝ^N` and `Y ⊆ ℝ^K`; everything here is stated for metric spaces
`α`, `β` (with `β` proper where Bolzano-Weierstrass is used), which `ℝ^N`, `ℝ^K` and the
figures' `ℝ` are instances of. A correspondence is `f : α → Set β`, studied on `A`.

* **Definitions M.H.1-M.H.4**: correspondence into `Y`, graph, closed graph (sequential), upper
  hemicontinuity (closed graph and bounded images of compact sets), lower hemicontinuity
  (sequential, with membership from some index on), continuity (both).
* The closed graph is closedness of the graph relative to `A × Y` (`hasClosedGraph_iff_closure`).
* Footnote 17 (images of compact sets are compact, `footnote_M_H_17`), footnote 18
  (`footnote_M_H_18`), the compact-range case (`uhc_iff_hasClosedGraph_of_isCompact`),
  **Theorem M.H.1** (`theorem_M_H_1`), lower hemicontinuity of functions
  (`lhc_singleton_iff`) and footnote 19 (open graph ⇒ lhc, `footnote_M_H_19`).
* Figures M.H.1-M.H.3 as concrete correspondences on `[0, 1]`.
* Bridges: closed graph is Kreps's `SequentialUpper` and MWG lhc is Kreps's `SequentialLower`
  on the subtype `A` (Kreps I, Appendix 4); MWG lhc is Mathlib's `LowerHemicontinuous` and
  MWG uhc implies Mathlib's (open-set) `UpperHemicontinuous` on `A`.
-/

namespace MWG.ClassicalDemand

open Filter Topology

variable {α β : Type*} [MetricSpace α] [MetricSpace β]

/-- **Definition M.H.1** (MWG, p. 949). A correspondence `f` from `A` into `Y`, `f : A → Y`:
`f(x) ⊆ Y` for every `x ∈ A` (`f(x)` may be empty). -/
def CorrMapsInto (A : Set α) (Y : Set β) (f : α → Set β) : Prop := ∀ x ∈ A, f x ⊆ Y

/-- **Section M.H** (MWG, p. 949). The graph `{(x, y) ∈ A × Y : y ∈ f(x)}`. -/
def corrGraph (A : Set α) (f : α → Set β) : Set (α × β) := {q | q.1 ∈ A ∧ q.2 ∈ f q.1}

/-- **Definition M.H.2** (MWG, p. 949). `f` has a closed graph if for sequences `xᵐ → x ∈ A`
and `yᵐ → y` with `xᵐ ∈ A` and `yᵐ ∈ f(xᵐ)` for every `m`, we have `y ∈ f(x)`. -/
def HasClosedGraph (A : Set α) (f : α → Set β) : Prop :=
  ∀ (xs : ℕ → α) (ys : ℕ → β) (x : α) (y : β), (∀ m, xs m ∈ A) → x ∈ A →
    (∀ m, ys m ∈ f (xs m)) → Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) → y ∈ f x

/-- **Section M.H** (MWG, p. 950). "The concept of a closed graph is simply our usual notion of
closedness (relative to `A × Y`)": for `f : A → Y` with `Y` closed, `f` has a closed graph iff
every point of `A × Y` in the closure of the graph lies in the graph. -/
theorem hasClosedGraph_iff_closure {A : Set α} {Y : Set β} {f : α → Set β} (hY : IsClosed Y)
    (hf : CorrMapsInto A Y f) :
    HasClosedGraph A f ↔ closure (corrGraph A f) ∩ A ×ˢ Y ⊆ corrGraph A f := by
  constructor
  · rintro h ⟨x, y⟩ ⟨hcl, hxA, -⟩
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
    exact ⟨hxA, h (fun n => (u n).1) (fun n => (u n).2) x y (fun n => (hu n).1) hxA
      (fun n => (hu n).2) ((continuous_fst.tendsto _).comp hlim)
      ((continuous_snd.tendsto _).comp hlim)⟩
  · intro h xs ys x y hxs hx hys hxl hyl
    have hmem : (x, y) ∈ closure (corrGraph A f) :=
      mem_closure_of_tendsto (hxl.prodMk_nhds hyl) (Eventually.of_forall fun n => ⟨hxs n, hys n⟩)
    have hyY : y ∈ Y := hY.mem_of_tendsto hyl (Eventually.of_forall fun n => hf _ (hxs n) (hys n))
    exact (h ⟨hmem, hx, hyY⟩).2

/-- A correspondence whose graph over `A` is cut out by a closed set has a closed graph. -/
theorem hasClosedGraph_of_isClosed {A : Set α} {f : α → Set β} {C : Set (α × β)}
    (hC : IsClosed C) (hfC : ∀ x ∈ A, ∀ y, y ∈ f x ↔ (x, y) ∈ C) : HasClosedGraph A f := by
  intro xs ys x y hxs hx hys hxl hyl
  exact (hfC x hx y).mpr (hC.mem_of_tendsto (hxl.prodMk_nhds hyl)
    (Eventually.of_forall fun n => (hfC _ (hxs n) _).mp (hys n)))

/-- **Definition M.H.3** (MWG, p. 950). `f` is upper hemicontinuous if it has a closed graph and
the image `f(B) = ⋃_{x ∈ B} f(x)` of every compact `B ⊆ A` is bounded. -/
def UpperHemicontinuousMWG (A : Set α) (f : α → Set β) : Prop :=
  HasClosedGraph A f ∧ ∀ B ⊆ A, IsCompact B → Bornology.IsBounded (⋃ x ∈ B, f x)

/-- **Footnote 17** (MWG, p. 950). The image of a compact set under an upper hemicontinuous
correspondence is compact (closed and bounded). -/
theorem footnote_M_H_17 [ProperSpace β] {A : Set α} {f : α → Set β}
    (h : UpperHemicontinuousMWG A f) {B : Set α} (hBA : B ⊆ A) (hB : IsCompact B) :
    IsCompact (⋃ x ∈ B, f x) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ (h.2 B hBA hB)
  apply IsSeqClosed.isClosed
  intro ys y hys hyl
  have hys' : ∀ n, ∃ x ∈ B, ys n ∈ f x := fun n => by simpa using hys n
  choose xs hxsB hxsf using hys'
  obtain ⟨x, hxB, φ, hφ, hxφ⟩ := hB.tendsto_subseq hxsB
  have := h.1 (xs ∘ φ) (ys ∘ φ) x y (fun n => hBA (hxsB _)) (hBA hxB) (fun n => hxsf _) hxφ
    (hyl.comp hφ.tendsto_atTop)
  exact Set.mem_biUnion hxB this

/-- **Footnote 18** (MWG, p. 950). A convergent sequence together with its limit forms a compact,
hence bounded, set. -/
theorem footnote_M_H_18 {xs : ℕ → α} {x : α} (hx : Tendsto xs atTop (𝓝 x)) :
    IsCompact (insert x (Set.range xs)) ∧ Bornology.IsBounded (insert x (Set.range xs)) :=
  ⟨hx.isCompact_insert_range, hx.isCompact_insert_range.isBounded⟩

/-- **Section M.H** (MWG, p. 950). "If the range space `Y` is compact, the upper hemicontinuity
property reduces to the closed graph condition." -/
theorem uhc_iff_hasClosedGraph_of_isCompact {A : Set α} {Y : Set β} {f : α → Set β}
    (hY : IsCompact Y) (hf : CorrMapsInto A Y f) :
    UpperHemicontinuousMWG A f ↔ HasClosedGraph A f :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hBA _ =>
    hY.isBounded.subset (Set.iUnion₂_subset fun x hx => hf x (hBA hx))⟩⟩

omit [MetricSpace α] [MetricSpace β] in
/-- The image of `B` under a function, written as a correspondence. -/
theorem appendixMH_biUnion_singleton_eq_image (g : α → β) (B : Set α) :
    (⋃ x ∈ B, ({g x} : Set β)) = g '' B := by
  ext y
  simp [eq_comm]

/-- Sequential continuity on `A`: a function is continuous on `A` if it maps every sequence of
`A` converging in `A` to a convergent sequence. -/
theorem appendixMH_continuousOn_of_seq {A : Set α} {g : α → β}
    (h : ∀ (xs : ℕ → α) (x : α), (∀ m, xs m ∈ A) → x ∈ A → Tendsto xs atTop (𝓝 x) →
      Tendsto (g ∘ xs) atTop (𝓝 (g x))) : ContinuousOn g A := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro u a hu
  exact h (fun n => (u n).1) a.1 (fun n => (u n).2) a.2
    ((continuous_subtype_val.tendsto a).comp hu)

/-- **Theorem M.H.1** (MWG, p. 950). A single-valued correspondence `x ↦ {g(x)}` on `A` is upper
hemicontinuous iff `g` is continuous on `A`. (The closed range set `Y` plays no role.) -/
theorem theorem_M_H_1 [ProperSpace β] {A : Set α} {g : α → β} :
    UpperHemicontinuousMWG A (fun x => {g x}) ↔ ContinuousOn g A := by
  constructor
  · intro h
    apply appendixMH_continuousOn_of_seq
    intro xs x hxs hx hxl
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hzl : Tendsto (xs ∘ ns) atTop (𝓝 x) := hxl.comp hns
    have hSA : insert x (Set.range (xs ∘ ns)) ⊆ A := by
      rintro z (rfl | ⟨n, rfl⟩)
      · exact hx
      · exact hxs _
    have hbd := h.2 _ hSA (footnote_M_H_18 hzl).1
    obtain ⟨y, -, φ, hφ, hyl⟩ := tendsto_subseq_of_bounded hbd (x := fun n => g (xs (ns n)))
      (fun n => Set.mem_biUnion (Set.mem_insert_of_mem _ ⟨n, rfl⟩) rfl)
    have hy : y = g x := h.1 (xs ∘ ns ∘ φ) _ x y (fun n => hxs _) hx (fun n => rfl)
      (hzl.comp hφ.tendsto_atTop) hyl
    exact ⟨φ, by rw [← hy]; exact hyl⟩
  · intro hg
    refine ⟨fun xs ys x y hxs hx hys hxl hyl => ?_, fun B hBA hB => ?_⟩
    · have hys' : ys = g ∘ xs := funext fun n => hys n
      have hcomp : Tendsto (g ∘ xs) atTop (𝓝 (g x)) :=
        (hg x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hxl, Eventually.of_forall hxs⟩)
      rw [hys'] at hyl
      exact tendsto_nhds_unique hyl hcomp
    · rw [appendixMH_biUnion_singleton_eq_image]
      exact (hB.image_of_continuousOn (hg.mono hBA)).isBounded

/-- **Definition M.H.4** (MWG, p. 951). `f` is lower hemicontinuous if for every sequence
`xᵐ → x ∈ A` with `xᵐ ∈ A` and every `y ∈ f(x)` there are `yᵐ → y` and `M` with `yᵐ ∈ f(xᵐ)`
for `m > M`. (The book assumes `Y` compact; the definition does not use it.) -/
def LowerHemicontinuousMWG (A : Set α) (f : α → Set β) : Prop :=
  ∀ (xs : ℕ → α) (x : α), (∀ m, xs m ∈ A) → x ∈ A → Tendsto xs atTop (𝓝 x) →
    ∀ y ∈ f x, ∃ ys : ℕ → β, Tendsto ys atTop (𝓝 y) ∧ ∃ M : ℕ, ∀ m, M < m → ys m ∈ f (xs m)

/-- **Section M.H** (MWG, p. 951). A correspondence is continuous if it is both upper and lower
hemicontinuous. -/
def ContinuousCorrMWG (A : Set α) (f : α → Set β) : Prop :=
  UpperHemicontinuousMWG A f ∧ LowerHemicontinuousMWG A f

/-- **Section M.H** (MWG, p. 951). "If `f` is a function, lower hemicontinuity as a
correspondence and continuity as a function coincide." -/
theorem lhc_singleton_iff {A : Set α} {g : α → β} :
    LowerHemicontinuousMWG A (fun x => {g x}) ↔ ContinuousOn g A := by
  constructor
  · intro h
    apply appendixMH_continuousOn_of_seq
    intro xs x hxs hx hxl
    obtain ⟨ys, hyl, M, hM⟩ := h xs x hxs hx hxl (g x) rfl
    refine hyl.congr' ?_
    filter_upwards [eventually_gt_atTop M] with m hm
    exact hM m hm
  · intro hg xs x hxs hx hxl y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨g ∘ xs, (hg x hx).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hxl, Eventually.of_forall hxs⟩), 0, fun m _ => rfl⟩

/-- **Footnote 19** (MWG, p. 951). A correspondence `f : A → Y` whose graph is open relative to
`A × Y` is lower hemicontinuous. -/
theorem footnote_M_H_19 {A : Set α} {Y : Set β} {f : α → Set β} (hf : CorrMapsInto A Y f)
    {U : Set (α × β)} (hU : IsOpen U) (hgraph : corrGraph A f = U ∩ A ×ˢ Y) :
    LowerHemicontinuousMWG A f := by
  intro xs x hxs hx hxl y hy
  have hxyU : (x, y) ∈ U := by
    have : (x, y) ∈ corrGraph A f := ⟨hx, hy⟩
    rw [hgraph] at this
    exact this.1
  have hev := (hxl.prodMk_nhds (tendsto_const_nhds (x := y))).eventually (hU.mem_nhds hxyU)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨fun _ => y, tendsto_const_nhds, M, fun m hm => ?_⟩
  have : (xs m, y) ∈ corrGraph A f := by
    rw [hgraph]
    exact ⟨hM m hm.le, hxs m, hf x hx hy⟩
  exact this.2

/-- Bridge to Kreps I, Appendix 4 (Definition A4.2a). The closed-graph condition on `A` is
Kreps's `SequentialUpper` for the correspondence restricted to the subtype `A`. -/
theorem hasClosedGraph_iff_sequentialUpper {A : Set α} {f : α → Set β} :
    HasClosedGraph A f ↔ Kreps.ConsumerDemand.SequentialUpper (fun a : A => f a) := by
  constructor
  · intro h p ys p₀ y hp hyl hys
    exact h (fun n => (p n).1) ys p₀.1 y (fun n => (p n).2) p₀.2 hys
      ((continuous_subtype_val.tendsto p₀).comp hp) hyl
  · intro h xs ys x y hxs hx hys hxl hyl
    exact h (fun n => ⟨xs n, hxs n⟩) ys ⟨x, hx⟩ y (tendsto_subtype_rng.mpr hxl) hyl hys

/-- Bridge to Kreps I, Appendix 4 (Definition A4.2b). MWG's lower hemicontinuity on `A` is
Kreps's `SequentialLower` for the correspondence restricted to the subtype `A`. -/
theorem lhc_iff_sequentialLower {A : Set α} {f : α → Set β} :
    LowerHemicontinuousMWG A f ↔ Kreps.ConsumerDemand.SequentialLower (fun a : A => f a) := by
  constructor
  · intro h p p₀ hp y hy
    obtain ⟨ys, hyl, M, hM⟩ := h (fun n => (p n).1) p₀.1 (fun n => (p n).2) p₀.2
      ((continuous_subtype_val.tendsto p₀).comp hp) y hy
    refine ⟨ys, ?_, hyl⟩
    filter_upwards [eventually_gt_atTop M] with m hm
    exact hM m hm
  · intro h xs x hxs hx hxl y hy
    obtain ⟨ys, hev, hyl⟩ := h (fun n => ⟨xs n, hxs n⟩) ⟨x, hx⟩ (tendsto_subtype_rng.mpr hxl) y hy
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    exact ⟨ys, hyl, M, fun m hm => hM m hm.le⟩

/-- Bridge to Mathlib. MWG's lower hemicontinuity on `A` is Mathlib's (open-set) lower
hemicontinuity of the correspondence restricted to the subtype `A`. -/
theorem lhc_iff_lowerHemicontinuous {A : Set α} {f : α → Set β} :
    LowerHemicontinuousMWG A f ↔ LowerHemicontinuous (fun a : A => f a) := by
  rw [lhc_iff_sequentialLower]
  constructor
  · intro h
    rw [lowerHemicontinuous_iff]
    intro a
    rw [lowerHemicontinuousAt_iff]
    rintro U hU ⟨y, hyf, hyU⟩
    by_contra hc
    rw [Filter.not_eventually] at hc
    obtain ⟨p, hp, hpU⟩ := exists_seq_forall_of_frequently hc
    obtain ⟨ys, hev, hyl⟩ := h p a hp y hyf
    obtain ⟨n, hn1, hn2⟩ := (hev.and (hyl.eventually (hU.mem_nhds hyU))).exists
    exact hpU n ⟨ys n, hn1, hn2⟩
  · intro h p p₀ hp y hy
    rw [lowerHemicontinuous_iff] at h
    exact (h p₀).exists_seq_tendsto hp hy

/-- Bridge to Mathlib. MWG's upper hemicontinuity on `A` implies Mathlib's (open-set) upper
hemicontinuity of the correspondence restricted to the subtype `A`: for every open `U ⊇ f(x)`,
`f(x') ⊆ U` for `x'` near `x`. -/
theorem upperHemicontinuous_of_uhc [ProperSpace β] {A : Set α} {f : α → Set β}
    (h : UpperHemicontinuousMWG A f) : UpperHemicontinuous (fun a : A => f a) := by
  rw [upperHemicontinuous_iff]
  intro a
  rw [upperHemicontinuousAt_iff_forall_isOpen]
  intro U hU hfU
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨p, hp, hpU⟩ := exists_seq_forall_of_frequently hc
  have hy : ∀ n, ∃ y ∈ f (p n), y ∉ U := fun n => Set.not_subset.mp (hpU n)
  choose ys hysf hysU using hy
  have hxl : Tendsto (fun n => (p n).1) atTop (𝓝 a.1) :=
    (continuous_subtype_val.tendsto a).comp hp
  have hSA : insert a.1 (Set.range fun n => (p n).1) ⊆ A := by
    rintro z (rfl | ⟨n, rfl⟩)
    · exact a.2
    · exact (p n).2
  have hbd := h.2 _ hSA (footnote_M_H_18 hxl).1
  obtain ⟨y, -, φ, hφ, hyl⟩ := tendsto_subseq_of_bounded hbd (x := ys)
    (fun n => Set.mem_biUnion (Set.mem_insert_of_mem _ ⟨n, rfl⟩) (hysf n))
  have hya : y ∈ f a := h.1 (fun n => (p (φ n)).1) (ys ∘ φ) a.1 y (fun n => (p _).2) a.2
    (fun n => hysf _) (hxl.comp hφ.tendsto_atTop) hyl
  exact hU.isClosed_compl.mem_of_tendsto hyl (Eventually.of_forall fun n => hysU _) (hfU hya)

/-! ### Figures M.H.1-M.H.3 (on `A = [0, 1]`) -/

/-- **Figure M.H.1(a)** (MWG, p. 950). A function on `[0, 1]`: `1` on `[0, 1/2]` and
`1/(2x - 1)` on `(1/2, 1]`. -/
noncomputable def figure_M_H_1a (x : ℝ) : Set ℝ := if x ≤ 1 / 2 then {1} else {1 / (2 * x - 1)}

/-- **Figure M.H.1(a)** (MWG, p. 950). The correspondence has a closed graph but is not upper
hemicontinuous: its image of the compact set `[0, 1]` is unbounded. -/
theorem figure_M_H_1a_spec :
    HasClosedGraph (Set.Icc (0 : ℝ) 1) figure_M_H_1a ∧
      ¬UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_1a := by
  constructor
  · apply hasClosedGraph_of_isClosed (C := {q : ℝ × ℝ | q.1 ≤ 1 / 2 ∧ q.2 = 1} ∪
      {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 * (2 * q.1 - 1) = 1})
    · apply IsClosed.union
      · exact (isClosed_le continuous_fst continuous_const).inter
          (isClosed_eq continuous_snd continuous_const)
      · exact (isClosed_le continuous_const continuous_snd).inter
          (isClosed_eq (continuous_snd.mul ((continuous_const.mul continuous_fst).sub
            continuous_const)) continuous_const)
    · intro x _ y
      simp only [figure_M_H_1a, Set.mem_union, Set.mem_ofPred_eq]
      split_ifs with hx
      · rw [Set.mem_singleton_iff]
        constructor
        · intro h
          exact Or.inl ⟨hx, h⟩
        · rintro (⟨-, h⟩ | ⟨hy, h⟩)
          · exact h
          · nlinarith
      · rw [Set.mem_singleton_iff]
        have hpos : 0 < 2 * x - 1 := by linarith [not_le.mp hx]
        constructor
        · intro h
          right
          rw [h]
          exact ⟨by positivity, by field_simp⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hx
          · field_simp
            linarith
  · rintro ⟨-, hbd⟩
    obtain ⟨C, hC⟩ := (hbd (Set.Icc 0 1) le_rfl isCompact_Icc).subset_closedBall 0
    set t : ℝ := 1 / 2 + 1 / (2 * (|C| + 1)) with ht
    have hC1 : 0 < |C| + 1 := by positivity
    have htmem : t ∈ Set.Icc (0 : ℝ) 1 := by
      have : 1 / (2 * (|C| + 1)) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by norm_num); linarith [abs_nonneg C]
      constructor <;> [positivity; linarith]
    have htgt : ¬t ≤ 1 / 2 := by
      rw [not_le, ht]
      have : 0 < 1 / (2 * (|C| + 1)) := by positivity
      linarith
    have hval : 1 / (2 * t - 1) = |C| + 1 := by
      rw [ht]
      field_simp
      ring
    have hmem : (|C| + 1 : ℝ) ∈ ⋃ x ∈ Set.Icc (0 : ℝ) 1, figure_M_H_1a x := by
      refine Set.mem_biUnion htmem ?_
      simp only [figure_M_H_1a, htgt, ↓reduceIte, Set.mem_singleton_iff]
      exact hval.symm
    have := hC hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hC1] at this
    linarith [le_abs_self C]

/-- **Figure M.H.1(b)** (MWG, p. 950). `1` on `[0, 1/2)`, the interval `[1, 2]` at `1/2`, and
`3 - 2x` on `(1/2, 1]`. -/
noncomputable def figure_M_H_1b (x : ℝ) : Set ℝ :=
  if x < 1 / 2 then {1} else if x = 1 / 2 then Set.Icc 1 2 else {3 - 2 * x}

/-- **Figure M.H.1(b)** (MWG, p. 950). With `Y = [0, 3]` the correspondence is upper
hemicontinuous. -/
theorem figure_M_H_1b_uhc : UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_1b := by
  have hinto : CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 3) figure_M_H_1b := by
    intro x hx y hy
    simp only [figure_M_H_1b] at hy
    split_ifs at hy with h1 h2
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      norm_num
    · exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [uhc_iff_hasClosedGraph_of_isCompact isCompact_Icc hinto]
  apply hasClosedGraph_of_isClosed (C := ({q : ℝ × ℝ | q.1 ≤ 1 / 2 ∧ q.2 = 1} ∪
    {q : ℝ × ℝ | q.1 = 1 / 2 ∧ 1 ≤ q.2 ∧ q.2 ≤ 2}) ∪ {q : ℝ × ℝ | 1 / 2 ≤ q.1 ∧ q.2 = 3 - 2 * q.1})
  · refine ((IsClosed.inter (isClosed_le continuous_fst continuous_const)
      (isClosed_eq continuous_snd continuous_const)).union
      ((isClosed_eq continuous_fst continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const)))).union
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_eq continuous_snd (continuous_const.sub (continuous_const.mul continuous_fst))))
  · intro x _ y
    simp only [figure_M_H_1b, Set.mem_union, Set.mem_ofPred_eq]
    split_ifs with h1 h2
    · rw [Set.mem_singleton_iff]
      constructor
      · intro h
        exact Or.inl (Or.inl ⟨h1.le, h⟩)
      · rintro ((⟨-, h⟩ | ⟨h, -⟩) | ⟨h, -⟩)
        · exact h
        · linarith
        · linarith
    · subst h2
      constructor
      · intro h
        exact Or.inl (Or.inr ⟨rfl, h.1, h.2⟩)
      · rintro ((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩)
        · rw [h]; norm_num
        · exact h
        · rw [h]; norm_num
    · rw [Set.mem_singleton_iff]
      have hx : 1 / 2 < x := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      constructor
      · intro h
        exact Or.inr ⟨hx.le, h⟩
      · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨-, h⟩)
        · linarith
        · linarith
        · exact h

/-- **Figure M.H.2(a)** (MWG, p. 951). `{2}` on `[0, 1/2]` and `[2, 3]` on `(1/2, 1]`. -/
noncomputable def figure_M_H_2a (x : ℝ) : Set ℝ := if x ≤ 1 / 2 then {2} else Set.Icc 2 3

/-- **Figure M.H.2(a)** (MWG, p. 951). A lower hemicontinuous correspondence that is not upper
hemicontinuous (it does not have a closed graph). -/
theorem figure_M_H_2a_spec :
    LowerHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_2a ∧
      ¬UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_2a := by
  constructor
  · intro xs x _ _ hxl y hy
    refine ⟨fun _ => y, tendsto_const_nhds, ?_⟩
    by_cases hx : x ≤ 1 / 2
    · simp only [figure_M_H_2a, hx, ↓reduceIte, Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨0, fun m _ => ?_⟩
      simp only [figure_M_H_2a]
      split_ifs
      · rfl
      · norm_num
    · simp only [figure_M_H_2a, hx, ↓reduceIte] at hy
      have hev := hxl.eventually (lt_mem_nhds (not_le.mp hx))
      obtain ⟨M, hM⟩ := eventually_atTop.mp hev
      refine ⟨M, fun m hm => ?_⟩
      simp only [figure_M_H_2a, not_le.mpr (hM m hm.le), ↓reduceIte]
      exact hy
  · rintro ⟨hcg, -⟩
    have hxs : ∀ m : ℕ, (1 / 2 : ℝ) + 1 / ((m : ℝ) + 2) ∈ Set.Icc (0 : ℝ) 1 := by
      intro m
      have h1 : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
        linarith [m.cast_nonneg' (α := ℝ)]
      constructor <;> [positivity; linarith]
    have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) + 1 / ((m : ℝ) + 2)) atTop (𝓝 (1 / 2)) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      have h2 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
        refine this.congr fun m => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        ring
      simpa using h2.const_add (1 / 2 : ℝ)
    have := hcg _ (fun _ => (3 : ℝ)) (1 / 2) 3 hxs (by norm_num) (fun m => ?_) hlim
      tendsto_const_nhds
    · simp only [figure_M_H_2a, le_refl, ↓reduceIte, Set.mem_singleton_iff] at this
      norm_num at this
    · have : ¬(1 / 2 : ℝ) + 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
        rw [not_le]
        have : 0 < 1 / ((m : ℝ) + 2) := by positivity
        linarith
      simp only [figure_M_H_2a, this, ↓reduceIte]
      norm_num

/-- **Figure M.H.2(b)** (MWG, p. 951). `{2}` on `[0, 1/2)` and `[2, 3]` on `[1/2, 1]`. -/
noncomputable def figure_M_H_2b (x : ℝ) : Set ℝ := if x < 1 / 2 then {2} else Set.Icc 2 3

/-- **Figure M.H.2(b)** (MWG, p. 951). An upper hemicontinuous correspondence that is not lower
hemicontinuous (take `xᵐ ↑ 1/2` and `3 ∈ f(1/2)`). -/
theorem figure_M_H_2b_spec :
    UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_2b ∧
      ¬LowerHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figure_M_H_2b := by
  constructor
  · have hinto : CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 3) figure_M_H_2b := by
      intro x _ y hy
      simp only [figure_M_H_2b] at hy
      split_ifs at hy
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        norm_num
      · exact ⟨by linarith [hy.1], hy.2⟩
    rw [uhc_iff_hasClosedGraph_of_isCompact isCompact_Icc hinto]
    apply hasClosedGraph_of_isClosed (C := {q : ℝ × ℝ | q.1 ≤ 1 / 2 ∧ q.2 = 2} ∪
      {q : ℝ × ℝ | 1 / 2 ≤ q.1 ∧ 2 ≤ q.2 ∧ q.2 ≤ 3})
    · exact ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_eq continuous_snd continuous_const)).union
        ((isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le continuous_snd continuous_const)))
    · intro x _ y
      simp only [figure_M_H_2b, Set.mem_union, Set.mem_ofPred_eq]
      split_ifs with h1
      · rw [Set.mem_singleton_iff]
        constructor
        · intro h
          exact Or.inl ⟨h1.le, h⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact h
          · linarith
      · constructor
        · intro h
          exact Or.inr ⟨not_lt.mp h1, h.1, h.2⟩
        · rintro (⟨-, h⟩ | ⟨-, h⟩)
          · rw [h]; norm_num
          · exact h
  · intro h
    have hxs : ∀ m : ℕ, (1 / 2 : ℝ) - 1 / ((m : ℝ) + 3) ∈ Set.Icc (0 : ℝ) 1 := by
      intro m
      have h1 : 1 / ((m : ℝ) + 3) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
        linarith [m.cast_nonneg' (α := ℝ)]
      have h2 : 0 < 1 / ((m : ℝ) + 3) := by positivity
      constructor <;> linarith
    have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) - 1 / ((m : ℝ) + 3)) atTop (𝓝 (1 / 2)) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
      have h2 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 3)) atTop (𝓝 0) := by
        refine this.congr fun m => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
        ring
      simpa using h2.const_sub (1 / 2 : ℝ)
    have h3 : (3 : ℝ) ∈ figure_M_H_2b (1 / 2) := by
      simp only [figure_M_H_2b, lt_irrefl, ↓reduceIte]
      norm_num
    obtain ⟨ys, hyl, M, hM⟩ := h _ (1 / 2) hxs (by norm_num) hlim 3 h3
    have hev : ys =ᶠ[atTop] fun _ => (2 : ℝ) := by
      filter_upwards [eventually_gt_atTop M] with m hm
      have := hM m hm
      have hlt : (1 / 2 : ℝ) - 1 / ((m : ℝ) + 3) < 1 / 2 := by
        have : 0 < 1 / ((m : ℝ) + 3) := by positivity
        linarith
      simp only [figure_M_H_2b, hlt, ↓reduceIte, Set.mem_singleton_iff] at this
      exact this
    have := tendsto_nhds_unique (hyl.congr' hev) tendsto_const_nhds
    norm_num at this

/-- **Figure M.H.3** (MWG, p. 952). The region between the lines `3x` and `3 - 3x` on `[0, 1]`:
`f(x) = [min(3x, 3 - 3x), max(3x, 3 - 3x)]`. -/
noncomputable def figure_M_H_3 (x : ℝ) : Set ℝ :=
  Set.Icc (min (3 * x) (3 - 3 * x)) (max (3 * x) (3 - 3 * x))

/-- **Figure M.H.3** (MWG, p. 952). With `Y = [0, 3]`, the correspondence is continuous (upper
and lower hemicontinuous). -/
theorem figure_M_H_3_continuous : ContinuousCorrMWG (Set.Icc (0 : ℝ) 1) figure_M_H_3 := by
  have hlo : Continuous fun x : ℝ => min (3 * x) (3 - 3 * x) := by fun_prop
  have hhi : Continuous fun x : ℝ => max (3 * x) (3 - 3 * x) := by fun_prop
  constructor
  · have hinto : CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 3) figure_M_H_3 := by
      intro x hx y hy
      obtain ⟨h1, h2⟩ := hy
      constructor
      · exact le_trans (le_min (by linarith [hx.1]) (by linarith [hx.2])) h1
      · exact le_trans h2 (max_le (by linarith [hx.2]) (by linarith [hx.1]))
    rw [uhc_iff_hasClosedGraph_of_isCompact isCompact_Icc hinto]
    apply hasClosedGraph_of_isClosed (C := {q : ℝ × ℝ | min (3 * q.1) (3 - 3 * q.1) ≤ q.2 ∧
      q.2 ≤ max (3 * q.1) (3 - 3 * q.1)})
    · exact (isClosed_le (hlo.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (hhi.comp continuous_fst))
    · intro x _ y
      rfl
  · intro xs x _ _ hxl y hy
    refine ⟨fun m => max (min (3 * xs m) (3 - 3 * xs m))
      (min y (max (3 * xs m) (3 - 3 * xs m))), ?_, 0, fun m _ => ?_⟩
    · have h1 := (hlo.tendsto x).comp hxl
      have h2 := (hhi.tendsto x).comp hxl
      have hlim : Tendsto (fun m => max (min (3 * xs m) (3 - 3 * xs m))
          (min y (max (3 * xs m) (3 - 3 * xs m)))) atTop
          (𝓝 (max (min (3 * x) (3 - 3 * x)) (min y (max (3 * x) (3 - 3 * x))))) :=
        h1.max ((tendsto_const_nhds (x := y)).min h2)
      have heq : max (min (3 * x) (3 - 3 * x)) (min y (max (3 * x) (3 - 3 * x))) = y := by
        rw [min_eq_left hy.2, max_eq_right hy.1]
      rw [heq] at hlim
      exact hlim
    · have hle : min (3 * xs m) (3 - 3 * xs m) ≤ max (3 * xs m) (3 - 3 * xs m) :=
        min_le_max
      exact ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩

end MWG.ClassicalDemand
