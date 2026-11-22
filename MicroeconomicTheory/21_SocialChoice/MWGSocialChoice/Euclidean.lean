/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Aggregation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Euclidean preferences, medians and Condorcet winners

MWG, Section 21.D, pp. 805-806: Example 21.D.6 (Euclidean preferences), Figures 21.D.6-21.D.8
and footnotes 11-12.

Alternatives and ideal points live in a real inner product space `E` (MWG: `ℝⁿ`). The agent
with peak `x` ranks alternatives by distance to `x`. The peaks preferring `y` to `z` form
`A(y, z) = {x : ‖x - y‖ < ‖x - z‖}`, an open half-space bounded by the perpendicular bisector
of `[y, z]`. A continuum of agents is a probability measure `μ` on peaks (MWG: a density `g`).
`x*` is a *median* if every open half-space bounded by a hyperplane through `x*` has mass at
most `1/2`; with null hyperplanes (e.g. a density) this is the book's "each half-space has mass
`1/2`" (`isMedianPoint_iff_book`). We prove, for every probability measure, that `x*` is a
Condorcet winner iff it is a median (MWG's two arguments, made precise with continuity of
measure). Figure 21.D.8(a): the centre of a rectangle is a median of the uniform distribution
(proved for every centrally symmetric measure).

**Departure.** The book's median ("each half-space has mass `1/2`") presupposes that hyperplanes
are null; our definition works for all probability measures and agrees with it then.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 805). The Euclidean preference with peak `x`:
`y ≿ z` iff `‖y - x‖ ≤ ‖z - x‖` (utility `-‖y - x‖`). -/
def euclidPref (x : E) : E → E → Prop := fun y z => ‖y - x‖ ≤ ‖z - x‖

omit [InnerProductSpace ℝ E] in
/-- Euclidean preferences are rational and have `x` as their unique best alternative. -/
theorem euclidPref_spec (x : E) :
    Rational (euclidPref x) ∧ ∀ y, y ≠ x → Strict (euclidPref x) x y := by
  refine ⟨⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h1 h2⟩, fun y hy => ?_⟩
  have : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  simp only [Strict, euclidPref, sub_self, norm_zero]
  exact ⟨this.le, not_le.2 this⟩

omit [InnerProductSpace ℝ E] in
/-- **Example 21.D.6** (MWG, p. 805). Each peak identifies a unique Euclidean preference:
different peaks give different preferences. -/
theorem euclidPref_injective {x x' : E} (h : euclidPref x = euclidPref x') : x = x' := by
  by_contra hne
  have h1 := (euclidPref_spec x').2 x hne
  rw [← h] at h1
  have h2 := (euclidPref_spec x).2 x' (Ne.symm hne)
  exact strict_asymm h2 h1

/-- **Example 21.D.6** (MWG, p. 805). `A(y, z)`: the peaks of the agents preferring `y` to `z`. -/
def prefRegion (y z : E) : Set E := {x | ‖x - y‖ < ‖x - z‖}

omit [InnerProductSpace ℝ E] in
/-- An agent with peak `x` prefers `y` to `z` iff `x ∈ A(y, z)`. -/
theorem strict_euclidPref_iff (x y z : E) : Strict (euclidPref x) y z ↔ x ∈ prefRegion y z := by
  simp only [Strict, euclidPref, prefRegion, Set.mem_ofPred_eq, not_le, norm_sub_rev x]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Distance comparison through the inner product:
`‖x - y‖ < ‖x - z‖ ↔ ‖y - z‖² < 2⟪x - z, y - z⟫`. -/
theorem mem_prefRegion_iff (x y z : E) :
    x ∈ prefRegion y z ↔ ‖y - z‖ ^ 2 < 2 * ⟪x - z, y - z⟫ := by
  have e : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 - 2 * ⟪x - z, y - z⟫ + ‖y - z‖ ^ 2 := by
    rw [← norm_sub_sq_real]
    congr 1
    abel
  simp only [prefRegion, Set.mem_ofPred_eq]
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Example 21.D.6** (MWG, p. 805, Figure 21.D.6). `A(y, z)` is the open half-space
`{x : ⟪x, z - y⟫ < (‖z‖² - ‖y‖²)/2}`. -/
theorem prefRegion_eq_halfspace (y z : E) :
    prefRegion y z = {x | ⟪x, z - y⟫ < (‖z‖ ^ 2 - ‖y‖ ^ 2) / 2} := by
  ext x
  simp only [prefRegion, Set.mem_ofPred_eq]
  have ey : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have ez : ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, z⟫ + ‖z‖ ^ 2 := norm_sub_sq_real x z
  have ei : ⟪x, z - y⟫ = ⟪x, z⟫ - ⟪x, y⟫ := inner_sub_right x z y
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Example 21.D.6** (MWG, p. 805). The boundary of `A(y, z)` is the hyperplane perpendicular
to `[y, z]` through its midpoint: `‖x - y‖ = ‖x - z‖ ↔ ⟪x - (y + z)/2, z - y⟫ = 0`. -/
theorem bisector_iff (x y z : E) :
    ‖x - y‖ = ‖x - z‖ ↔ ⟪x - (1 / 2 : ℝ) • (y + z), z - y⟫ = 0 := by
  have ey : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have ez : ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, z⟫ + ‖z‖ ^ 2 := norm_sub_sq_real x z
  have ei : ⟪x - (1 / 2 : ℝ) • (y + z), z - y⟫ = ⟪x, z⟫ - ⟪x, y⟫ - (‖z‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_add_left,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real, real_inner_comm y z]
    ring
  rw [ei]
  have h1 := norm_nonneg (x - y)
  have h2 := norm_nonneg (x - z)
  constructor
  · intro h
    have : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 := by rw [h]
    linarith
  · intro h
    have : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 := by linarith
    nlinarith [sq_nonneg (‖x - y‖ - ‖x - z‖), sq_nonneg (‖x - y‖ + ‖x - z‖)]

variable [MeasurableSpace E] [BorelSpace E]

/-- The open half-space `{z : ⟪z - x, q⟫ > 0}` bounded by the hyperplane through `x` with
normal `q`. -/
def openHalfSpace (x q : E) : Set E := {z | 0 < ⟪z - x, q⟫}

/-- Open half-spaces are measurable. -/
theorem measurableSet_openHalfSpace (x q : E) : MeasurableSet (openHalfSpace x q) :=
  (isOpen_lt continuous_const ((continuous_id.sub continuous_const).inner
    continuous_const)).measurableSet

/-- **Example 21.D.6** (MWG, p. 805). `x` is a median of the distribution `μ` of peaks: every
open half-space bounded by a hyperplane through `x` has at most half of the mass. -/
def IsMedianPoint (μ : Measure E) (x : E) : Prop :=
  ∀ q : E, q ≠ 0 → 2 * μ (openHalfSpace x q) ≤ μ Set.univ

/-- **Example 21.D.6** (MWG, p. 805). `x` is a Condorcet winner for the distribution `μ`: no
alternative is preferred to `x` by more agents than prefer `x` to it. -/
def IsCondorcetWinnerMeasure (μ : Measure E) (x : E) : Prop :=
  ∀ y, μ (prefRegion y x) ≤ μ (prefRegion x y)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The two open half-spaces bounded by a hyperplane through `x` are disjoint. -/
theorem disjoint_openHalfSpace (x q : E) :
    Disjoint (openHalfSpace x q) (openHalfSpace x (-q)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [openHalfSpace, inner_neg_right, Set.mem_ofPred_eq] at hz hz'
  linarith

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `A(y, z)` and `A(z, y)` are disjoint. -/
theorem disjoint_prefRegion (y z : E) : Disjoint (prefRegion y z) (prefRegion z y) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  simp only [prefRegion, Set.mem_ofPred_eq] at h1 h2
  linarith

omit [BorelSpace E] in
/-- **Example 21.D.6** (MWG, p. 805), the book's median: when hyperplanes are null, `x` is a
median iff every hyperplane through `x` splits the mass into two halves (`2μ(H) = 1`). -/
theorem isMedianPoint_iff_book (μ : Measure E) [IsProbabilityMeasure μ] (x : E)
    (hnull : ∀ q : E, μ {z | ⟪z - x, q⟫ = 0} = 0) :
    IsMedianPoint μ x ↔ ∀ q : E, q ≠ 0 → 2 * μ (openHalfSpace x q) = 1 := by
  constructor
  · intro h q hq
    have h1 := h q hq
    have h2 := h (-q) (neg_ne_zero.2 hq)
    rw [measure_univ] at h1 h2
    have hcover : Set.univ ⊆ (openHalfSpace x q ∪ openHalfSpace x (-q)) ∪
        {z | ⟪z - x, q⟫ = 0} := by
      intro z _
      simp only [openHalfSpace, inner_neg_right, Set.mem_union, Set.mem_ofPred_eq]
      rcases lt_trichotomy 0 ⟪z - x, q⟫ with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm
      · exact Or.inl (Or.inr (by linarith))
    have hge : 1 ≤ μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := by
      calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
        _ ≤ μ ((openHalfSpace x q ∪ openHalfSpace x (-q)) ∪ {z | ⟪z - x, q⟫ = 0}) :=
          measure_mono hcover
        _ ≤ μ (openHalfSpace x q ∪ openHalfSpace x (-q)) + μ {z | ⟪z - x, q⟫ = 0} :=
          measure_union_le _ _
        _ = μ (openHalfSpace x q ∪ openHalfSpace x (-q)) := by rw [hnull q, add_zero]
        _ ≤ μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := measure_union_le _ _
    refine le_antisymm h1 ?_
    have h3 : 1 + 1 ≤ 2 * μ (openHalfSpace x q) + 1 := by
      calc (1 : ENNReal) + 1 = 2 * 1 := by norm_num
        _ ≤ 2 * (μ (openHalfSpace x q) + μ (openHalfSpace x (-q))) := by gcongr
        _ = 2 * μ (openHalfSpace x q) + 2 * μ (openHalfSpace x (-q)) := mul_add _ _ _
        _ ≤ 2 * μ (openHalfSpace x q) + 1 := by gcongr
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h3
  · intro h q hq
    rw [h q hq, measure_univ]

/-- **Example 21.D.6** (MWG, pp. 805-806). For any probability distribution of peaks, `x*` is a
Condorcet winner iff it is a median. (If `y ≠ x*`, `A(y, x*)` lies in an open half-space
through `x*` and `A(x*, y)` contains the complementary closed one; if `x*` is not a median,
moving slightly from `x*` in the direction `q` of a heavy half-space defeats `x*`, by continuity
of the measure: Figure 21.D.7.) -/
theorem example_21_D_6 (μ : Measure E) [IsProbabilityMeasure μ] (x : E) :
    IsMedianPoint μ x ↔ IsCondorcetWinnerMeasure μ x := by
  constructor
  · intro h y
    by_cases hyx : y = x
    · subst hyx
      have : prefRegion y y = ∅ := by
        ext z
        simp [prefRegion]
      rw [this]
    set q := y - x with hq
    have hq0 : q ≠ 0 := sub_ne_zero.2 hyx
    set H := openHalfSpace x q
    have hH := measurableSet_openHalfSpace x q
    have s1 : prefRegion y x ⊆ H := by
      intro z hz
      rw [mem_prefRegion_iff] at hz
      simp only [H, openHalfSpace, Set.mem_ofPred_eq]
      nlinarith [sq_nonneg ‖y - x‖]
    have s2 : Hᶜ ⊆ prefRegion x y := by
      intro z hz
      simp only [H, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hz
      rw [mem_prefRegion_iff]
      have e : ⟪z - y, x - y⟫ = -⟪z - x, q⟫ + ‖x - y‖ ^ 2 := by
        have h1 : z - y = (z - x) - q := by rw [hq]; abel
        have h2 : x - y = -q := by rw [hq]; abel
        rw [h1, h2, inner_neg_right, inner_sub_left, norm_neg, ← real_inner_self_eq_norm_sq]
        ring
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
      rw [e]
      nlinarith
    have h1 := h q hq0
    rw [← measure_add_measure_compl hH, two_mul] at h1
    have h2 : μ H ≤ μ Hᶜ := (ENNReal.add_le_add_iff_left (measure_ne_top μ H)).1 h1
    exact (measure_mono s1).trans (h2.trans (measure_mono s2))
  · intro h
    by_contra hm
    simp only [IsMedianPoint, not_forall, not_le] at hm
    obtain ⟨q, hq0, hq⟩ := hm
    rw [measure_univ] at hq
    have hp : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    let A : ℕ → Set E := fun n => prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x
    have hAmem : ∀ n z, z ∈ A n ↔ (1 / ((n : ℝ) + 1)) * ‖q‖ ^ 2 < 2 * ⟪z - x, q⟫ := by
      intro n z
      simp only [A]
      rw [mem_prefRegion_iff, add_sub_cancel_left, norm_smul, inner_smul_right,
        Real.norm_eq_abs, abs_of_pos (hp n), mul_pow]
      have hpn := hp n
      constructor
      · intro h'
        by_contra hc
        push Not at hc
        nlinarith [mul_le_mul_of_nonneg_left hc hpn.le]
      · intro h'
        nlinarith [mul_lt_mul_of_pos_left h' hpn]
    have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hmono : Monotone A := by
      intro n m hnm z hz
      rw [hAmem] at hz ⊢
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      nlinarith [sq_nonneg ‖q‖]
    have hunion : (⋃ n, A n) = openHalfSpace x q := by
      ext z
      simp only [Set.mem_iUnion, openHalfSpace, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩
        rw [hAmem] at hn
        nlinarith [hp n, sq_nonneg ‖q‖, mul_pos (hp n) (pow_pos hqpos 2)]
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos (mul_pos two_pos hz) (pow_pos hqpos 2))
        refine ⟨n, (hAmem n z).2 ?_⟩
        rw [lt_div_iff₀ (pow_pos hqpos 2)] at hn
        linarith
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at ht
    have ht2 := ENNReal.Tendsto.const_mul ht (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    obtain ⟨n, hn⟩ := (ht2.eventually (lt_mem_nhds hq)).exists
    have hcw := h (x + (1 / ((n : ℝ) + 1)) • q)
    have hmeas : MeasurableSet (prefRegion x (x + (1 / ((n : ℝ) + 1)) • q)) :=
      (isOpen_lt (continuous_id.sub continuous_const).norm
        (continuous_id.sub continuous_const).norm).measurableSet
    have hsum := measure_union (μ := μ) (disjoint_prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x)
      hmeas
    have hle : μ (prefRegion (x + (1 / ((n : ℝ) + 1)) • q) x ∪
        prefRegion x (x + (1 / ((n : ℝ) + 1)) • q)) ≤ 1 := prob_le_one
    rw [hsum] at hle
    have : 2 * μ (A n) ≤ 1 := by
      rw [two_mul]
      exact le_trans (add_le_add le_rfl hcw) hle
    exact absurd hn (not_lt.2 this)

end MWG.SocialChoice
