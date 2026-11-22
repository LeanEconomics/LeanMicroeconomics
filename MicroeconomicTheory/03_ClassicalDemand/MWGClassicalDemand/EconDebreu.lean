/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UtilityRepresentation
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Prod.Lex

/-!
# Proposition 3.C.1 on an arbitrary consumption set (Debreu's theorem)

MWG, Section 3.C, Proposition 3.C.1, p. 47: a continuous rational preference relation on a
consumption set `X ⊆ ℝ^L_+` has a continuous utility representation. The earlier modules prove
it for `X = ℝ^L_+` and every convex `X` (Kreps's Proposition 2.9 needs connectedness). Here it
is proved for every `X ⊆ ℝ^L`, connected or not (`proposition_3_C_1_general`), via Debreu's
theorem on any second-countable space (`econ_debreu_representation`).

The proof has two steps.
* A representation (not yet continuous): with a countable base `b₀, b₁, …`,
  `v(x) = ∑ {2⁻ⁿ : bₙ ⊆ {z : x ≻ z}}` represents `≿` (`econBaseUtility_represents`).
* Debreu's open-gap lemma, in the form needed (`econ_gap_lemma`): if all sets `{v < v z}` and
  `{v > v z}` are open, a strictly increasing transformation of `v` is continuous. Let `T` be
  the range of `v`, `J ⊆ T` the lower ends of its jumps (`a < b` in `T`, nothing of `T`
  between) and `Δ ⊇ J` a countable subset of `T` meeting every interval between two points of
  `T` that has a point of `T` inside. The countable order `P ⊆ ℝ ×ₗ ℚ` of the points `(a, 0)`,
  `a ∈ Δ`, plus a copy of `(0, 1) ∩ ℚ` after each jump and after the end markers `-1` and `3`,
  is dense without end points, hence (Cantor) order-isomorphic to `(0, 1) ∩ ℚ`. The
  transformed utility is `f(x) = sup {e(z) : z ∈ P, z.1 < v(x)}`.

No departure from the book.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

open Classical in
/-- The representation built from a sequence `b` of open sets: the sum of `2⁻ⁿ` over the `n`
with `bₙ` strictly below `x`. -/
noncomputable def econBaseUtility (b : ℕ → Set X) (r : X → X → Prop) (x : X) : ℝ :=
  ∑' n, if b n ⊆ StrictlyWorseThan r x then ((1 : ℝ) / 2) ^ n else 0

omit [TopologicalSpace X] in
open Classical in
/-- The terms of `econBaseUtility` are summable. -/
theorem econBaseUtility_summable (b : ℕ → Set X) (r : X → X → Prop) (x : X) :
    Summable fun n => if b n ⊆ StrictlyWorseThan r x then ((1 : ℝ) / 2) ^ n else 0 := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_geometric_two
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · positivity

omit [TopologicalSpace X] in
open Classical in
/-- `econBaseUtility` takes values in `[0, 2]`. -/
theorem econBaseUtility_bounds (b : ℕ → Set X) (r : X → X → Prop) (x : X) :
    0 ≤ econBaseUtility b r x ∧ econBaseUtility b r x ≤ 2 := by
  constructor
  · exact tsum_nonneg fun n => by split_ifs <;> positivity
  · rw [← tsum_geometric_two]
    refine (econBaseUtility_summable b r x).tsum_le_tsum (fun n => ?_) summable_geometric_two
    split_ifs
    · exact le_rfl
    · positivity

open Classical in
/-- `econBaseUtility` represents a rational `≿` with open strict contours, when `b` is a
base of the topology. -/
theorem econBaseUtility_represents {b : ℕ → Set X}
    (hb : ∀ U : Set X, IsOpen U → ∀ x ∈ U, ∃ n, x ∈ b n ∧ b n ⊆ U) (hr : Rational r)
    (ho : OpenStrictContours r) : Represents (econBaseUtility b r) r := by
  have hmono : ∀ x y, r x y → econBaseUtility b r y ≤ econBaseUtility b r x := by
    intro x y hxy
    refine (econBaseUtility_summable b r y).tsum_le_tsum (fun n => ?_)
      (econBaseUtility_summable b r x)
    by_cases hy : b n ⊆ StrictlyWorseThan r y
    · have hx : b n ⊆ StrictlyWorseThan r x := by
        intro z hz
        obtain ⟨hyz, hzy⟩ := hy hz
        exact ⟨hr.2 x y z hxy hyz, fun hzx => hzy (hr.2 z x y hzx hxy)⟩
      simp only [hy, hx, ↓reduceIte, le_refl]
    · simp only [hy, ↓reduceIte]
      split_ifs <;> positivity
  intro x y
  refine ⟨hmono x y, fun h => ?_⟩
  by_contra hxy
  have hyx : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
  obtain ⟨n, hxn, hn⟩ := hb _ (ho y).2 x hyx
  have hnx : ¬ b n ⊆ StrictlyWorseThan r x := fun hs => (hs hxn).2 (hs hxn).1
  have hlt : econBaseUtility b r x < econBaseUtility b r y := by
    refine Summable.tsum_lt_tsum_of_nonneg (i := n) (fun m => ?_) (fun m => ?_) ?_
      (econBaseUtility_summable b r y)
    · split_ifs <;> positivity
    · by_cases hx : b m ⊆ StrictlyWorseThan r x
      · have hy : b m ⊆ StrictlyWorseThan r y := by
          intro z hz
          obtain ⟨hxz, hzx⟩ := hx hz
          exact ⟨hr.2 y x z hyx.1 hxz, fun hzy => hyx.2 (hr.2 x z y hxz hzy)⟩
        simp only [hx, hy, ↓reduceIte, le_refl]
      · simp only [hx, ↓reduceIte]
        split_ifs <;> positivity
    · simp only [hnx, hn, ↓reduceIte]
      positivity
  exact absurd h (not_le.mpr hlt)

/-- A second-countable space has a base indexed by `ℕ`. -/
theorem econ_exists_nat_basis [SecondCountableTopology X] :
    ∃ b : ℕ → Set X, ∀ U : Set X, IsOpen U → ∀ x ∈ U, ∃ n, x ∈ b n ∧ b n ⊆ U := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨b, hb⟩ := (hBc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨b, fun U hU x hx => ?_⟩
  obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx hU
  have hV' : V ∈ insert ∅ B := Set.mem_insert_of_mem _ hV
  rw [hb] at hV'
  obtain ⟨n, rfl⟩ := hV'
  exact ⟨n, hxV, hVU⟩

/-- The lower ends of the jumps of `T ⊆ ℝ`: `a ∈ T` with some `b ∈ T`, `a < b`, and no point
of `T` strictly between. -/
def econJumps (T : Set ℝ) : Set ℝ :=
  {a | a ∈ T ∧ ∃ b ∈ T, a < b ∧ ∀ c ∈ T, ¬ (a < c ∧ c < b)}

/-- The countable "Debreu-dense" subset of `T`: the jump ends and one chosen point of `T` in
each rational interval meeting `T`. -/
def econDense (T : Set ℝ) : Set ℝ :=
  econJumps T ∪
    Set.range fun s : {qq : ℚ × ℚ // (T ∩ Set.Ioo (qq.1 : ℝ) qq.2).Nonempty} => s.2.some

/-- The jumps of any `T ⊆ ℝ` are countable. -/
theorem econJumps_countable (T : Set ℝ) : (econJumps T).Countable := by
  classical
  let nx : ℝ → ℝ := fun a => if h : a ∈ econJumps T then h.2.choose else a
  have hnx : ∀ a ∈ econJumps T, nx a ∈ T ∧ a < nx a ∧ ∀ c ∈ T, ¬ (a < c ∧ c < nx a) := by
    intro a ha
    simp only [nx, ha, ↓reduceDIte]
    exact ha.2.choose_spec
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun a => Set.Ioo a (nx a)) ?_
    (fun _ _ => isOpen_Ioo) (fun a ha => Set.nonempty_Ioo.mpr (hnx a ha).2.1)
  have key : ∀ a ∈ econJumps T, ∀ a' ∈ econJumps T, a < a' →
      Disjoint (Set.Ioo a (nx a)) (Set.Ioo a' (nx a')) := by
    intro a ha a' ha' hlt
    have hle : nx a ≤ a' := by
      by_contra h
      exact (hnx a ha).2.2 a' ha'.1 ⟨hlt, not_le.mp h⟩
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd (ht.2.trans_le hle) (not_lt.mpr ht'.1.le)
  intro a ha a' ha' hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a ha a' ha' h
  · exact (key a' ha' a ha h).symm

/-- `econDense T` is countable. -/
theorem econDense_countable (T : Set ℝ) : (econDense T).Countable :=
  (econJumps_countable T).union (Set.countable_range _)

/-- `econDense T ⊆ T`. -/
theorem econDense_subset (T : Set ℝ) : econDense T ⊆ T := by
  rintro a (ha | ⟨s, rfl⟩)
  · exact ha.1
  · exact s.2.some_mem.1

/-- Between two points of `T` that are not a jump, there is a point of `econDense T`. -/
theorem econDense_between {T : Set ℝ} {a b : ℝ} (ha : a ∈ T) (hb : b ∈ T) (hab : a < b)
    (hj : a ∉ econJumps T) : ∃ d ∈ econDense T, a < d ∧ d < b := by
  have : ∃ c ∈ T, a < c ∧ c < b := by
    by_contra hn
    simp only [not_exists, not_and, not_lt] at hn
    exact hj ⟨ha, b, hb, hab, fun c hc h => absurd h.2 (not_lt.mpr (hn c hc h.1))⟩
  obtain ⟨c, hcT, hac, hcb⟩ := this
  obtain ⟨q, haq, hqc⟩ := exists_rat_btwn hac
  obtain ⟨q', hcq, hqb⟩ := exists_rat_btwn hcb
  let s : {qq : ℚ × ℚ // (T ∩ Set.Ioo (qq.1 : ℝ) qq.2).Nonempty} :=
    ⟨(q, q'), ⟨c, hcT, hqc, hcq⟩⟩
  have hs := s.2.some_mem
  exact ⟨s.2.some, Or.inr ⟨s, rfl⟩, haq.trans hs.2.1, hs.2.2.trans hqb⟩

/-- The countable order used in the gap lemma: `(a, 0)` for `a ∈ econDense T`, and `(a, q)`,
`q ∈ (0, 1) ∩ ℚ`, for `a` a jump end or one of the end markers `-1`, `3`. -/
def econGapOrder (T : Set ℝ) : Set (Lex (ℝ × ℚ)) :=
  {z | ((ofLex z).1 ∈ econDense T ∧ (ofLex z).2 = 0) ∨
    (((ofLex z).1 ∈ econJumps T ∨ (ofLex z).1 = -1 ∨ (ofLex z).1 = 3) ∧
      0 < (ofLex z).2 ∧ (ofLex z).2 < 1)}

/-- The utility transformed through an order isomorphism `e` of `econGapOrder` onto
`(0, 1) ∩ ℚ`. -/
noncomputable def econGapUtility (v : X → ℝ) (e : econGapOrder (Set.range v) ≃o RationalUnit)
    (x : X) : ℝ :=
  sSup ((fun z => (((e z : RationalUnit) : ℚ) : ℝ)) '' {z | (ofLex z.1).1 < v x})

/-- **Debreu's open-gap lemma** (in the form used for Proposition 3.C.1). If `0 ≤ v ≤ 2` and
all the sets `{v < v z}`, `{v > v z}` are open, some `f` with the same order as `v`
(`v x ≤ v y ⟺ f x ≤ f y`) is continuous. -/
theorem econ_gap_lemma {v : X → ℝ} (hb : ∀ x, 0 ≤ v x ∧ v x ≤ 2)
    (hlt : ∀ z, IsOpen {x | v x < v z}) (hgt : ∀ z, IsOpen {x | v z < v x}) :
    ∃ f : X → ℝ, Continuous f ∧ ∀ x y, v x ≤ v y ↔ f x ≤ f y := by
  classical
  set T := Set.range v with hTdef
  set P := econGapOrder T with hPdef
  have hJΔ : econJumps T ⊆ econDense T := Set.subset_union_left
  have hΔT := econDense_subset T
  have hTb : ∀ a ∈ T, 0 ≤ a ∧ a ≤ 2 := by
    rintro _ ⟨x, rfl⟩
    exact hb x
  have hopen : ∀ c : ℝ, (c ∈ T ∨ c < 0 ∨ 2 < c) →
      IsOpen {x | v x < c} ∧ IsOpen {x | c < v x} := by
    rintro c (⟨z, rfl⟩ | hc | hc)
    · exact ⟨hlt z, hgt z⟩
    · have h1 : {x | v x < c} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => absurd (hb x).1 (not_le.mpr (hx.trans hc))
      have h2 : {x | c < v x} = Set.univ :=
        Set.eq_univ_of_forall fun x => hc.trans_le (hb x).1
      rw [h1, h2]
      exact ⟨isOpen_empty, isOpen_univ⟩
    · have h1 : {x | v x < c} = Set.univ :=
        Set.eq_univ_of_forall fun x => (hb x).2.trans_lt hc
      have h2 : {x | c < v x} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => absurd (hb x).2 (not_le.mpr (hc.trans hx))
      rw [h1, h2]
      exact ⟨isOpen_univ, isOpen_empty⟩
  have hfst : ∀ z ∈ P, (ofLex z).1 ∈ econDense T ∨ (ofLex z).1 = -1 ∨ (ofLex z).1 = 3 := by
    rintro z (h | h)
    · exact Or.inl h.1
    · rcases h.1 with h' | h' | h'
      · exact Or.inl (hJΔ h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hfstT : ∀ z ∈ P, (ofLex z).1 ∈ T ∨ (ofLex z).1 < 0 ∨ 2 < (ofLex z).1 := by
    intro z hz
    rcases hfst z hz with h | h | h
    · exact Or.inl (hΔT h)
    · exact Or.inr (Or.inl (by rw [h]; norm_num))
    · exact Or.inr (Or.inr (by rw [h]; norm_num))
  have hmk0 : ∀ a ∈ econDense T, toLex (a, (0 : ℚ)) ∈ P := fun a ha => Or.inl ⟨ha, rfl⟩
  have hmkq : ∀ a : ℝ, (a ∈ econJumps T ∨ a = -1 ∨ a = 3) → ∀ q : ℚ, 0 < q → q < 1 →
      toLex (a, q) ∈ P := fun a ha q h0 h1 => Or.inr ⟨ha, h0, h1⟩
  have hlex : ∀ z w : Lex (ℝ × ℚ), z < w ↔
      (ofLex z).1 < (ofLex w).1 ∨ (ofLex z).1 = (ofLex w).1 ∧ (ofLex z).2 < (ofLex w).2 :=
    fun z w => Prod.Lex.toLex_lt_toLex (x := ofLex z) (y := ofLex w)
  -- the order `P` is countable, dense and has no end points
  let : Countable P := by
    have hc : ((econDense T ∪ {-1, 3}) ×ˢ (Set.univ : Set ℚ)).Countable :=
      ((econDense_countable T).union (Set.toFinite _).countable).prod Set.countable_univ
    refine ((hc.image toLex).mono ?_).to_subtype
    intro z hz
    refine ⟨ofLex z, ⟨?_, Set.mem_univ _⟩, rfl⟩
    rcases hfst z hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  let : Nonempty P := ⟨⟨toLex (-1, 1 / 2), hmkq _ (Or.inr (Or.inl rfl)) _
    (by norm_num) (by norm_num)⟩⟩
  have hcopy : ∀ z ∈ P, (ofLex z).2 ≠ 0 →
      ((ofLex z).1 ∈ econJumps T ∨ (ofLex z).1 = -1 ∨ (ofLex z).1 = 3) ∧
        0 < (ofLex z).2 ∧ (ofLex z).2 < 1 := by
    rintro z (h | h) hne
    · exact absurd h.2 hne
    · exact h
  have hsnd : ∀ z ∈ P, 0 ≤ (ofLex z).2 ∧ (ofLex z).2 < 1 := by
    rintro z (h | h)
    · rw [h.2]
      norm_num
    · exact ⟨h.2.1.le, h.2.2⟩
  let : DenselyOrdered P := ⟨by
    rintro ⟨z, hz⟩ ⟨w, hw⟩ hzw
    change z < w at hzw
    rw [hlex] at hzw
    rcases hzw with hlt | ⟨heq, hlt⟩
    · by_cases hc : (ofLex z).1 ∈ econJumps T ∨ (ofLex z).1 = -1 ∨ (ofLex z).1 = 3
      · have hs := hsnd z hz
        refine ⟨⟨toLex ((ofLex z).1, ((ofLex z).2 + 1) / 2), hmkq _ hc _ (by linarith)
          (by linarith)⟩, ?_, ?_⟩
        · change z < toLex _
          rw [hlex]
          exact Or.inr ⟨rfl, by change (ofLex z).2 < ((ofLex z).2 + 1) / 2; linarith⟩
        · change toLex _ < w
          rw [hlex]
          exact Or.inl hlt
      · have hz0 : (ofLex z).2 = 0 := by
          by_contra h0
          exact hc (hcopy z hz h0).1
        have hzΔ : (ofLex z).1 ∈ econDense T := by
          rcases hfst z hz with h | h | h
          · exact h
          · exact absurd (Or.inr (Or.inl h)) hc
          · exact absurd (Or.inr (Or.inr h)) hc
        have hzJ : (ofLex z).1 ∉ econJumps T := fun h => hc (Or.inl h)
        rcases hfst w hw with hwΔ | hw1 | hw3
        · obtain ⟨d, hd, hzd, hdw⟩ := econDense_between (hΔT hzΔ) (hΔT hwΔ) hlt hzJ
          refine ⟨⟨toLex (d, 0), hmk0 d hd⟩, ?_, ?_⟩
          · change z < toLex _
            rw [hlex]
            exact Or.inl hzd
          · change toLex _ < w
            rw [hlex]
            exact Or.inl hdw
        · have := (hTb _ (hΔT hzΔ)).1
          rw [hw1] at hlt
          linarith
        · have hw0 : (ofLex w).2 ≠ 0 := by
            intro h0
            rcases hw with h | h
            · have := (hTb _ (hΔT h.1)).2
              rw [hw3] at this
              norm_num at this
            · rw [h0] at h
              exact lt_irrefl _ h.2.1
          have hws := (hcopy w hw hw0).2
          refine ⟨⟨toLex (3, (ofLex w).2 / 2), hmkq _ (Or.inr (Or.inr rfl)) _ (by linarith)
            (by linarith)⟩, ?_, ?_⟩
          · change z < toLex _
            rw [hlex]
            left
            change (ofLex z).1 < 3
            rw [← hw3]
            exact hlt
          · change toLex _ < w
            rw [hlex]
            right
            exact ⟨hw3.symm, by change (ofLex w).2 / 2 < (ofLex w).2; linarith⟩
    · have hw0 : (ofLex w).2 ≠ 0 := by
        have := (hsnd z hz).1
        intro h
        rw [h] at hlt
        linarith
      have hwc := hcopy w hw hw0
      have hzs := (hsnd z hz).1
      refine ⟨⟨toLex ((ofLex z).1, ((ofLex z).2 + (ofLex w).2) / 2), hmkq _ ?_ _
        (by linarith) (by linarith)⟩, ?_, ?_⟩
      · rw [heq]
        exact hwc.1
      · change z < toLex _
        rw [hlex]
        exact Or.inr ⟨rfl, by change (ofLex z).2 < ((ofLex z).2 + (ofLex w).2) / 2; linarith⟩
      · change toLex _ < w
        rw [hlex]
        exact Or.inr ⟨heq, by
          change ((ofLex z).2 + (ofLex w).2) / 2 < (ofLex w).2; linarith⟩⟩
  let : NoMinOrder P := ⟨by
    rintro ⟨z, hz⟩
    by_cases h0 : (ofLex z).2 = 0
    · refine ⟨⟨toLex (-1, 1 / 2), hmkq _ (Or.inr (Or.inl rfl)) _ (by norm_num)
        (by norm_num)⟩, ?_⟩
      change toLex _ < z
      rw [hlex]
      left
      change (-1 : ℝ) < (ofLex z).1
      rcases hz with h | h
      · linarith [(hTb _ (hΔT h.1)).1]
      · exact absurd h0 (ne_of_gt h.2.1)
    · have hc := hcopy z hz h0
      refine ⟨⟨toLex ((ofLex z).1, (ofLex z).2 / 2), hmkq _ hc.1 _ (by linarith)
        (by linarith)⟩, ?_⟩
      change toLex _ < z
      rw [hlex]
      exact Or.inr ⟨rfl, by change (ofLex z).2 / 2 < (ofLex z).2; linarith⟩⟩
  let : NoMaxOrder P := ⟨by
    rintro ⟨z, hz⟩
    have hs := hsnd z hz
    by_cases h3 : (ofLex z).1 = 3
    · refine ⟨⟨toLex (3, ((ofLex z).2 + 1) / 2), hmkq _ (Or.inr (Or.inr rfl)) _
        (by linarith) (by linarith)⟩, ?_⟩
      change z < toLex _
      rw [hlex]
      exact Or.inr ⟨h3, by change (ofLex z).2 < ((ofLex z).2 + 1) / 2; linarith⟩
    · refine ⟨⟨toLex (3, 1 / 2), hmkq _ (Or.inr (Or.inr rfl)) _ (by norm_num)
        (by norm_num)⟩, ?_⟩
      change z < toLex _
      rw [hlex]
      left
      change (ofLex z).1 < 3
      rcases hfst z hz with h | h | h
      · linarith [(hTb _ (hΔT h)).2]
      · rw [h]
        norm_num
      · exact absurd h h3⟩
  let : Nonempty RationalUnit := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
  obtain ⟨e⟩ := Order.iso_of_countable_dense P RationalUnit
  -- the transformed utility
  set ψ : P → ℝ := fun z => (((e z : RationalUnit) : ℚ) : ℝ) with hψdef
  have hψ : ∀ z, 0 < ψ z ∧ ψ z < 1 := by
    intro z
    have h := (e z).2
    change (0 : ℝ) < (((e z : RationalUnit) : ℚ) : ℝ) ∧ (((e z : RationalUnit) : ℚ) : ℝ) < 1
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hψmono : ∀ z w : P, z < w → ψ z < ψ w := by
    intro z w hzw
    have h := e.strictMono hzw
    change (((e z : RationalUnit) : ℚ) : ℝ) < (((e w : RationalUnit) : ℚ) : ℝ)
    exact_mod_cast h
  let f : X → ℝ := econGapUtility v e
  have hf : ∀ x, f x = sSup (ψ '' {z | (ofLex z.1).1 < v x}) := fun x => rfl
  let lo : P := ⟨toLex (-1, 1 / 2), hmkq _ (Or.inr (Or.inl rfl)) _ (by norm_num)
    (by norm_num)⟩
  have hlo : ∀ x, lo ∈ {z : P | (ofLex z.1).1 < v x} := by
    intro x
    change (-1 : ℝ) < v x
    linarith [(hb x).1]
  have hbdd : ∀ x, BddAbove (ψ '' {z : P | (ofLex z.1).1 < v x}) := by
    intro x
    refine ⟨1, ?_⟩
    rintro _ ⟨z, -, rfl⟩
    exact (hψ z).2.le
  have hne : ∀ x, (ψ '' {z : P | (ofLex z.1).1 < v x}).Nonempty :=
    fun x => ⟨ψ lo, lo, hlo x, rfl⟩
  have le_f : ∀ x, ∀ z : P, (ofLex z.1).1 < v x → ψ z ≤ f x := by
    intro x z hz
    rw [hf]
    exact le_csSup (hbdd x) ⟨z, hz, rfl⟩
  have f_le : ∀ x, ∀ z : P, v x ≤ (ofLex z.1).1 → f x ≤ ψ z := by
    intro x z hz
    rw [hf]
    refine csSup_le (hne x) ?_
    rintro _ ⟨w, hw, rfl⟩
    refine (hψmono w z ?_).le
    change w.1 < z.1
    rw [hlex]
    exact Or.inl (lt_of_lt_of_le hw hz)
  have f_le_one : ∀ x, f x ≤ 1 := by
    intro x
    rw [hf]
    refine csSup_le (hne x) ?_
    rintro _ ⟨z, -, rfl⟩
    exact (hψ z).2.le
  have f_pos : ∀ x, 0 < f x := fun x => (hψ lo).1.trans_le (le_f x lo (hlo x))
  have lt_f : ∀ x t, t < f x → ∃ z : P, (ofLex z.1).1 < v x ∧ t < ψ z := by
    intro x t ht
    rw [hf] at ht
    obtain ⟨_, ⟨z, hz, rfl⟩, h⟩ := (lt_csSup_iff (hbdd x) (hne x)).mp ht
    exact ⟨z, hz, h⟩
  -- strict monotonicity
  have hstep : ∀ d ∈ econDense T, ∀ c ∈ T, d < c →
      ∃ z : P, toLex (d, (0 : ℚ)) < z.1 ∧ (ofLex z.1).1 < c := by
    intro d hd c hc hdc
    by_cases hj : d ∈ econJumps T
    · refine ⟨⟨toLex (d, 1 / 2), hmkq _ (Or.inl hj) _ (by norm_num) (by norm_num)⟩, ?_, hdc⟩
      change toLex (d, (0 : ℚ)) < toLex (d, 1 / 2)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, by norm_num⟩
    · obtain ⟨d', hd', hdd', hd'c⟩ := econDense_between (hΔT hd) hc hdc hj
      refine ⟨⟨toLex (d', 0), hmk0 d' hd'⟩, ?_, hd'c⟩
      change toLex (d, (0 : ℚ)) < toLex (d', 0)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hdd'
  have hstrict : ∀ x y, v x < v y → f x < f y := by
    intro x y hxy
    obtain ⟨d, hd, hxd, hdy⟩ : ∃ d ∈ econDense T, v x ≤ d ∧ d < v y := by
      by_cases hj : v x ∈ econJumps T
      · exact ⟨v x, hJΔ hj, le_rfl, hxy⟩
      · obtain ⟨d, hd, h1, h2⟩ := econDense_between (T := T) ⟨x, rfl⟩ ⟨y, rfl⟩ hxy hj
        exact ⟨d, hd, h1.le, h2⟩
    obtain ⟨z, hz, hzy⟩ := hstep d hd (v y) ⟨y, rfl⟩ hdy
    let p₁ : P := ⟨toLex (d, 0), hmk0 d hd⟩
    calc f x ≤ ψ p₁ := f_le x p₁ hxd
      _ < ψ z := hψmono p₁ z hz
      _ ≤ f y := le_f y z hzy
  have hcongr : ∀ x y, v x = v y → f x = f y := by
    intro x y h
    rw [hf, hf, h]
  refine ⟨f, ?_, fun x y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · apply OrderTopology.continuous_iff.mpr
    intro a
    constructor
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change a < f x at hx
      obtain ⟨z, hz, haz⟩ := lt_f x a hx
      have hU := (hopen _ (hfstT z.1 z.2)).2
      apply Filter.mem_of_superset (hU.mem_nhds hz)
      intro x' hx'
      exact haz.trans_le (le_f x' z hx')
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change f x < a at hx
      by_cases ha : 1 < a
      · exact Filter.mem_of_superset Filter.univ_mem fun x' _ => (f_le_one x').trans_lt ha
      obtain ⟨q, hxq, hqa⟩ := exists_rat_btwn hx
      have hq0 : (0 : ℚ) < q := by exact_mod_cast (f_pos x).trans hxq
      have hq1 : q < (1 : ℚ) := by exact_mod_cast hqa.trans_le (not_lt.mp ha)
      set p : P := e.symm (⟨q, hq0, hq1⟩ : RationalUnit) with hpdef
      have hψp : ψ p = q := by simp [hψdef, hpdef]
      have hvx : v x ≤ (ofLex p.1).1 := by
        by_contra hcon
        have := le_f x p (not_le.mp hcon)
        rw [hψp] at this
        exact absurd hxq (not_lt.mpr this)
      by_cases hpJ : (ofLex p.1).1 ∈ econJumps T
      · obtain ⟨-, c, hcT, hpc, hnone⟩ := hpJ
        have hU := (hopen c (Or.inl hcT)).1
        apply Filter.mem_of_superset (hU.mem_nhds (lt_of_le_of_lt hvx hpc))
        intro x' hx'
        have hle : v x' ≤ (ofLex p.1).1 := by
          by_contra hcon
          exact hnone (v x') ⟨x', rfl⟩ ⟨not_le.mp hcon, hx'⟩
        exact (f_le x' p hle).trans_lt (hψp ▸ hqa)
      by_cases hp3 : (ofLex p.1).1 = 3
      · refine Filter.mem_of_superset Filter.univ_mem fun x' _ => ?_
        have hle : v x' ≤ (ofLex p.1).1 := by
          rw [hp3]
          linarith [(hb x').2]
        exact (f_le x' p hle).trans_lt (hψp ▸ hqa)
      have hp1 : (ofLex p.1).1 ≠ -1 := by
        intro h
        rw [h] at hvx
        linarith [(hb x).1]
      have hp0 : (ofLex p.1).2 = 0 := by
        by_contra h0
        rcases (hcopy p.1 p.2 h0).1 with h | h | h
        · exact hpJ h
        · exact hp1 h
        · exact hp3 h
      obtain ⟨q', hqq', hq'a⟩ := exists_rat_btwn hqa
      have hq'0 : (0 : ℚ) < q' := hq0.trans (by exact_mod_cast hqq')
      have hq'1 : q' < (1 : ℚ) := by exact_mod_cast hq'a.trans_le (not_lt.mp ha)
      set p₀ : P := e.symm (⟨q', hq'0, hq'1⟩ : RationalUnit) with hp₀def
      have hψp₀ : ψ p₀ = q' := by simp [hψdef, hp₀def]
      have hpp₀ : p < p₀ := by
        rw [hpdef, hp₀def]
        apply e.symm.strictMono
        change q < q'
        exact_mod_cast hqq'
      have hlt0 : (ofLex p.1).1 < (ofLex p₀.1).1 := by
        have h := hpp₀
        change p.1 < p₀.1 at h
        rw [hlex] at h
        rcases h with h | ⟨heq, h2⟩
        · exact h
        · exfalso
          have hne0 : (ofLex p₀.1).2 ≠ 0 := by
            rw [hp0] at h2
            exact ne_of_gt h2
          rcases (hcopy p₀.1 p₀.2 hne0).1 with h | h | h
          · exact hpJ (heq ▸ h)
          · exact hp1 (heq ▸ h)
          · exact hp3 (heq ▸ h)
      have hU := (hopen _ (hfstT p₀.1 p₀.2)).1
      apply Filter.mem_of_superset (hU.mem_nhds (lt_of_le_of_lt hvx hlt0))
      intro x' hx'
      exact (f_le x' p₀ (le_of_lt hx')).trans_lt (hψp₀ ▸ hq'a)
  · rcases h.lt_or_eq with h | h
    · exact (hstrict x y h).le
    · exact (hcongr x y h).le
  · by_contra hcon
    exact absurd h (not_le.mpr (hstrict y x (not_le.mp hcon)))

/-- **Debreu's theorem.** On a second-countable space, a continuous rational preference
relation has a continuous utility representation. -/
theorem econ_debreu_representation [SecondCountableTopology X] (hr : Rational r)
    (hc : ContinuousPreference r) : ∃ u : X → ℝ, Represents u r ∧ Continuous u := by
  have ho := continuousPreference_openStrictContours hc
  obtain ⟨b, hb⟩ := econ_exists_nat_basis (X := X)
  set v := econBaseUtility b r with hvdef
  have hv : Represents v r := econBaseUtility_represents hb hr ho
  have hlt : ∀ z, IsOpen {x | v x < v z} := by
    intro z
    have hset : {x | v x < v z} = StrictlyWorseThan r z := by
      ext x
      change v x < v z ↔ r z x ∧ ¬ r x z
      rw [hv z x, hv x z, not_le]
      exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩
    rw [hset]
    exact (ho z).2
  have hgt : ∀ z, IsOpen {x | v z < v x} := by
    intro z
    have hset : {x | v z < v x} = StrictlyBetterThan r z := by
      ext x
      change v z < v x ↔ r x z ∧ ¬ r z x
      rw [hv z x, hv x z, not_le]
      exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩
    rw [hset]
    exact (ho z).1
  obtain ⟨f, hfc, hfv⟩ := econ_gap_lemma (econBaseUtility_bounds b r) hlt hgt
  refine ⟨f, fun x y => ?_, hfc⟩
  rw [hv x y, hfv]

/-- **Proposition 3.C.1** (MWG, p. 47) at the book's generality: on any consumption set
`X ⊆ ℝ^L` (connected or not, in particular any `X ⊆ ℝ^L_+`) a continuous rational `≿` has a
utility representation continuous on `X`. -/
theorem proposition_3_C_1_general {L : ℕ} {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r) (hc : PrefContinuous X r) :
    ∃ u : (Fin L → ℝ) → ℝ, ContinuousOn u X ∧ RepresentsOn X u r := by
  classical
  have hr' := (rationalOn_iff_rational X r).mp hr
  have hc' := (prefContinuous_iff_continuousPreference hr).mp hc
  obtain ⟨v, hv, hvc⟩ := econ_debreu_representation hr' hc'
  refine ⟨fun x => if h : x ∈ X then v ⟨x, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hvc using 1
    funext x
    simp [x.2]
  · intro x hx y hy
    simp only [hx, hy, ↓reduceDIte]
    exact hv ⟨x, hx⟩ ⟨y, hy⟩

end MWG.ClassicalDemand
