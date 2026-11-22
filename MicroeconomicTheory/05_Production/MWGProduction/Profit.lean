/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Basic
import MWGClassicalDemand.DualitySupport
import MWGClassicalDemand.RelationsBasic
import Mathlib.Data.EReal.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The profit maximization problem (MWG Section 5.C, pp. 135-139)

The profit function and supply correspondence of a production set `Y ⊆ ℝ^L`:

* `profitFn Y p = sup {p·y : y ∈ Y}` with values in `[-∞, +∞]` (footnote 5), its real version
  `profit Y p` (where `p·y` is bounded above on `Y`), and `supply Y p`, the set of
  profit-maximizing plans. The bridge `profit_eq_neg_supportFn` gives `π(p) = -μ_{-Y}(p)`
  (p. 137) in terms of Chapter 3's support function.
* The constant-returns example on p. 136, **Exercise 5.C.1**, the law of supply (5.C.3).
* **Proposition 5.C.1** (i)-(vii), with **Exercise 5.C.2** (= (ii)).

Departures (see `docs/corrections.md`): (iii) is false as printed with prices `p ≫ 0`
(`proposition_5_C_1_iii_counterexample`); it holds with all `p ≥ 0`
(`proposition_5_C_1_iii_nonneg`) and with `p ≫ 0` when profits are bounded at some `p₀ ≫ 0`
(`proposition_5_C_1_iii`). Hotelling's lemma (vi) needs convexity
(`proposition_5_C_1_vi_nonconvex_counterexample`); (vii) is proved for convex `Y`, with the
semidefiniteness and `Dy(p̄)p̄ = 0` parts for every `Y`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Section 5.C** (MWG, p. 136, footnote 5). The profit function
`π(p) = sup {p·y : y ∈ Y}`, with values in `[-∞, +∞]`. -/
noncomputable def profitFn (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : EReal :=
  ⨆ y ∈ Y, ((p ⬝ᵥ y : ℝ) : EReal)

/-- The real profit function `sup {p·y : y ∈ Y}`, meaningful where `p·y` is bounded above on a
nonempty `Y` (there it equals `profitFn`, `profitFn_eq_coe`). -/
noncomputable def profit (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : ℝ :=
  sSup ((fun y => p ⬝ᵥ y) '' Y)

/-- **Section 5.C** (MWG, p. 136). The supply correspondence `y(p) = {y ∈ Y : p·y = π(p)}`, the
set of profit-maximizing production plans. -/
def supply (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | y ∈ Y ∧ ∀ y' ∈ Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y}

/-- `p·y ≤ π(p)` for every `y ∈ Y`. -/
theorem le_profitFn {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hy : y ∈ Y) :
    ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p :=
  le_iSup₂ (f := fun y (_ : y ∈ Y) => ((p ⬝ᵥ y : ℝ) : EReal)) y hy

/-- An upper bound for profits bounds the profit function. -/
theorem profitFn_le {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ} {c : EReal}
    (h : ∀ y ∈ Y, ((p ⬝ᵥ y : ℝ) : EReal) ≤ c) : profitFn Y p ≤ c :=
  iSup₂_le h

/-- Where profits are bounded above on a nonempty `Y`, the two profit functions agree. -/
theorem profitFn_eq_coe {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) {p : Fin L → ℝ}
    (hb : BddAbove ((fun y => p ⬝ᵥ y) '' Y)) : profitFn Y p = (profit Y p : EReal) := by
  apply le_antisymm
  · exact profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (le_csSup hb ⟨y, hy, rfl⟩)
  · by_contra h
    rw [not_le] at h
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    have : profit Y p ≤ r := by
      apply csSup_le (hne.image _)
      rintro _ ⟨y, hy, rfl⟩
      exact (EReal.coe_le_coe_iff.mp ((le_profitFn hy).trans hr1.le))
    have := EReal.coe_lt_coe_iff.mp hr2
    linarith

/-- **Footnote 5** (MWG, p. 136). Where profits are unbounded, `π(p) = +∞`. -/
theorem profitFn_eq_top {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ}
    (hb : ¬ BddAbove ((fun y => p ⬝ᵥ y) '' Y)) : profitFn Y p = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  rw [not_bddAbove_iff] at hb
  obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := hb r
  exact (EReal.coe_lt_coe_iff.mpr hlt).trans_le (le_profitFn hy)

/-- `π(p) < +∞` exactly when profits are bounded above. -/
theorem profitFn_lt_top_iff {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ} :
    profitFn Y p < ⊤ ↔ BddAbove ((fun y => p ⬝ᵥ y) '' Y) := by
  constructor
  · intro h
    by_contra hb
    rw [profitFn_eq_top hb] at h
    exact lt_irrefl _ h
  · rintro ⟨m, hm⟩
    exact (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hm ⟨y, hy, rfl⟩)).trans_lt
      (EReal.coe_lt_top m)

/-- A profit-maximizing plan gives the value of the profit function. -/
theorem profit_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hy : y ∈ supply Y p) :
    profit Y p = p ⬝ᵥ y :=
  IsGreatest.csSup_eq ⟨⟨y, hy.1, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact hy.2 y' hy'⟩

/-- A profit-maximizing plan gives the value of the extended profit function. -/
theorem profitFn_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ}
    (hy : y ∈ supply Y p) : profitFn Y p = ((p ⬝ᵥ y : ℝ) : EReal) :=
  le_antisymm (profitFn_le fun y' hy' => EReal.coe_le_coe_iff.mpr (hy.2 y' hy'))
    (le_profitFn hy.1)

/-- `y ∈ y(p)` iff `y ∈ Y` and `p·y = π(p)`, the book's definition (p. 136). -/
theorem mem_supply_iff {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} :
    y ∈ supply Y p ↔ y ∈ Y ∧ ((p ⬝ᵥ y : ℝ) : EReal) = profitFn Y p := by
  constructor
  · intro hy
    exact ⟨hy.1, (profitFn_eq_of_mem_supply hy).symm⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    have := le_profitFn (p := p) hy'
    rw [← h] at this
    exact EReal.coe_le_coe_iff.mp this

open scoped Pointwise in
/-- **Section 5.C** (MWG, p. 137). `π(p) = -μ_{-Y}(p)`, where `μ_{-Y}` is Chapter 3's support
function (Definition 3.F.1) of `-Y`. -/
theorem profit_eq_neg_supportFn (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    profit Y p = -supportFn (-Y) p := by
  unfold profit supportFn
  have : (fun x => p ⬝ᵥ x) '' (-Y) = -((fun y => p ⬝ᵥ y) '' Y) := by
    ext t
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨-x, hx, by simp [dotProduct_neg]⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨-y, by rwa [neg_neg], by rw [dotProduct_neg, h, neg_neg]⟩
  rw [this, Real.sInf_neg, neg_neg]

open scoped Pointwise in
/-- **Section 5.C** (MWG, p. 137). The supply correspondence is `-` the set of minimizers of
`p·x` on `-Y`. -/
theorem supply_eq_neg_supportArgmin (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    supply Y p = -supportArgmin (-Y) p := by
  ext y
  simp only [supply, supportArgmin, Set.mem_neg, Set.mem_ofPred_eq, neg_neg]
  constructor
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, fun x hx => ?_⟩
    have := hmax (-x) hx
    simp only [dotProduct_neg] at this ⊢
    linarith
  · rintro ⟨hy, hmin⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    have := hmin (-y') (by rwa [neg_neg])
    simp only [dotProduct_neg] at this ⊢
    linarith

open scoped Pointwise in
/-- Boundedness of profits on `Y` is boundedness below of `p·x` on `-Y`. -/
theorem bddAbove_iff_bddBelow_neg (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    BddAbove ((fun y => p ⬝ᵥ y) '' Y) ↔ BddBelow ((fun x => p ⬝ᵥ x) '' (-Y)) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := hm ⟨-x, hx, rfl⟩
    simp only [dotProduct_neg] at this
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hm ⟨-y, by rwa [Set.mem_neg, neg_neg], rfl⟩
    simp only [dotProduct_neg] at this
    linarith

/-! ### The example on p. 136 and Exercise 5.C.1 -/

/-- The constant-returns technology of p. 136: one unit of good 2 per unit of good 1 used,
with free disposal: `{y ∈ ℝ² : y₁ ≤ 0, y₁ + y₂ ≤ 0}`. -/
def oneForOneTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 0 + y 1 ≤ 0}

/-- **Section 5.C** (MWG, p. 136). For the one-for-one constant-returns technology and `p ≫ 0`,
`π(p) = 0` if `p₂ ≤ p₁` and `π(p) = +∞` if `p₂ > p₁`. -/
theorem example_5_C_profit_oneForOne {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    (p 1 ≤ p 0 → profitFn oneForOneTech p = 0) ∧
      (p 0 < p 1 → profitFn oneForOneTech p = ⊤) := by
  constructor
  · intro h
    apply le_antisymm
    · apply profitFn_le
      rintro y ⟨h0, h1⟩
      rw [EReal.coe_nonpos]
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [hp 0, hp 1]
    · have := le_profitFn (Y := oneForOneTech) (p := p) (y := 0)
        ⟨le_rfl, by simp⟩
      simpa using this
  · intro h
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set t := (|r| + 1) / (p 1 - p 0) with ht
    have hpos : 0 < p 1 - p 0 := by linarith
    refine ⟨_, ⟨![-t, t], ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, neg_nonpos]
      exact div_nonneg (by positivity) hpos.le
    · simp
    · simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have : p 0 * -t + p 1 * t = |r| + 1 := by
        rw [ht]
        field_simp
        ring
      rw [this]
      linarith [le_abs_self r]

/-- **Exercise 5.C.1** (MWG, p. 136). With nondecreasing returns to scale, either `π(p) ≤ 0` or
`π(p) = +∞`. -/
theorem exercise_5_C_1 {Y : Set (Fin L → ℝ)} (h : NondecreasingReturns Y) (p : Fin L → ℝ) :
    profitFn Y p ≤ 0 ∨ profitFn Y p = ⊤ := by
  by_cases hpos : ∃ y ∈ Y, 0 < p ⬝ᵥ y
  · right
    obtain ⟨y, hy, hpy⟩ := hpos
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set α := max 1 ((|r| + 1) / (p ⬝ᵥ y)) with hα
    refine ⟨_, ⟨α • y, h y hy α (le_max_left _ _), rfl⟩, ?_⟩
    change r < p ⬝ᵥ (α • y)
    rw [dotProduct_smul, smul_eq_mul]
    have h1 : (|r| + 1) / (p ⬝ᵥ y) ≤ α := le_max_right _ _
    have h2 : |r| + 1 ≤ α * (p ⬝ᵥ y) := by
      rwa [div_le_iff₀ hpy] at h1
    linarith [le_abs_self r]
  · left
    push Not at hpos
    exact profitFn_le fun y hy => EReal.coe_nonpos.mpr (hpos y hy)

/-! ### Proposition 5.C.1 -/

/-- **Proposition 5.C.1(i)** (MWG, p. 138). The profit function is homogeneous of degree one:
`π(αp) = απ(p)` for `α > 0`. -/
theorem proposition_5_C_1_i (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 < α) :
    profitFn Y (α • p) = (α : EReal) * profitFn Y p := by
  have key : ∀ (β : ℝ), 0 < β → ∀ q : Fin L → ℝ,
      profitFn Y (β • q) ≤ (β : EReal) * profitFn Y q := by
    intro β hβ q
    apply profitFn_le
    intro y hy
    rw [smul_dotProduct, smul_eq_mul, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr hβ.le)
  apply le_antisymm (key α hα p)
  have h2 := key α⁻¹ (inv_pos.mpr hα) (α • p)
  rw [smul_smul, inv_mul_cancel₀ hα.ne', one_smul] at h2
  calc (α : EReal) * profitFn Y p ≤ (α : EReal) * ((α⁻¹ : ℝ) * profitFn Y (α • p)) :=
        mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.mpr hα.le)
    _ = profitFn Y (α • p) := by
        rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hα.ne', EReal.coe_one, one_mul]

/-- **Proposition 5.C.1(ii)** and **Exercise 5.C.2** (MWG, p. 138). The profit function is
convex: `π(αp + (1-α)p') ≤ απ(p) + (1-α)π(p')` for `α ∈ [0, 1]`, in `[-∞, +∞]`. -/
theorem proposition_5_C_1_ii (Y : Set (Fin L → ℝ)) (p p' : Fin L → ℝ) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    profitFn Y (α • p + (1 - α) • p') ≤
      (α : EReal) * profitFn Y p + ((1 - α : ℝ) : EReal) * profitFn Y p' := by
  apply profitFn_le
  intro y hy
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr h0))
    (mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr (by linarith)))

/-- **Exercise 5.C.2** (MWG, p. 138), the hint's argument for a maximizer `y ∈ y(αp + (1-α)p')`. -/
theorem exercise_5_C_2 (Y : Set (Fin L → ℝ)) (p p' : Fin L → ℝ) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    profitFn Y (α • p + (1 - α) • p') ≤
      (α : EReal) * profitFn Y p + ((1 - α : ℝ) : EReal) * profitFn Y p' :=
  proposition_5_C_1_ii Y p p' h0 h1

/-- **Proposition 5.C.1(ii)** (MWG, p. 138), real form: `π` is convex on the convex set of
prices at which profits are bounded, from the concavity of Chapter 3's support function. -/
theorem proposition_5_C_1_ii_real {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) :
    ConvexOn ℝ {p : Fin L → ℝ | BddAbove ((fun y => p ⬝ᵥ y) '' Y)} (profit Y) := by
  have hne' : (-Y).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨-y, by rwa [Set.mem_neg, neg_neg]⟩
  have hc := supportFn_concaveOn hne'
  have hdom : {p : Fin L → ℝ | BddAbove ((fun y => p ⬝ᵥ y) '' Y)} =
      {p : Fin L → ℝ | BddBelow ((fun x => p ⬝ᵥ x) '' (-Y))} := by
    ext p
    exact bddAbove_iff_bddBelow_neg Y p
  rw [hdom]
  have : profit Y = -supportFn (-Y) := funext fun p => profit_eq_neg_supportFn Y p
  rw [this]
  exact hc.neg

/-- A nonzero vector of `ℝ^L` with a negative coordinate is unbounded against free disposal:
if `Y` is nonempty with free disposal and `p·y ≤ c` on `Y`, then `p ≥ 0`. -/
theorem nonneg_of_bdd_freeDisposal {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty)
    (hfd : FreeDisposal Y) {p : Fin L → ℝ} {c : ℝ} (hc : ∀ y ∈ Y, p ⬝ᵥ y ≤ c) : 0 ≤ p := by
  intro l
  by_contra hl0
  have hl : p l < 0 := not_le.mp hl0
  have hpl : p l ≠ 0 := hl.ne
  obtain ⟨y, hy⟩ := hne
  set t := (|c| + |p ⬝ᵥ y| + 1) / (-p l) with ht
  have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have hmem : y - t • Pi.single l 1 ∈ Y := by
    apply hfd y hy
    exact sub_le_self y (smul_nonneg htpos (Pi.single_nonneg.mpr zero_le_one))
  have := hc _ hmem
  rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
  have h2 : t * p l = -(|c| + |p ⬝ᵥ y| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hpl, mul_one]
  rw [h2] at this
  linarith [le_abs_self c, neg_abs_le (p ⬝ᵥ y)]

/-- **Proposition 5.C.1(iii)**, corrected (MWG, p. 138). If `Y` is closed, convex and has free
disposal, then `Y = {y : p·y ≤ π(p) for all p ≥ 0}`. -/
theorem proposition_5_C_1_iii_nonneg {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    (hc : Convex ℝ Y) (hfd : FreeDisposal Y) :
    Y = {y | ∀ p : Fin L → ℝ, 0 ≤ p → ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p} := by
  ext x
  constructor
  · intro hx p _
    exact le_profitFn hx
  · intro hx
    by_contra hxY
    rcases Y.eq_empty_or_nonempty with hY | hne
    · have := hx 0 le_rfl
      rw [hY] at this
      simp [profitFn] at this
    obtain ⟨q, c, hqx, hqY⟩ := separation_section_3_F hcl hc hxY
    have hb : ∀ y ∈ Y, (-q) ⬝ᵥ y ≤ -c := by
      intro y hy
      rw [neg_dotProduct]
      linarith [hqY y hy]
    have hp0 := nonneg_of_bdd_freeDisposal hne hfd hb
    have h1 := (hx (-q) hp0).trans (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hb y hy))
    have h2 := EReal.coe_le_coe_iff.mp h1
    rw [neg_dotProduct] at h2
    linarith

/-- **Proposition 5.C.1(iii)** (MWG, p. 138) with prices `p ≫ 0`, under the extra hypothesis
that profits are bounded at some `p₀ ≫ 0` (or `Y = ∅`): if `Y` is closed, convex and has free
disposal, then `Y = {y : p·y ≤ π(p) for all p ≫ 0}`. -/
theorem proposition_5_C_1_iii {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    (hfd : FreeDisposal Y) {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀)
    (hb₀ : BddAbove ((fun y => p₀ ⬝ᵥ y) '' Y)) :
    Y = {y | ∀ p : Fin L → ℝ, StrictlyPositive p → ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p} := by
  ext x
  constructor
  · intro hx p _
    exact le_profitFn hx
  · intro hx
    by_contra hxY
    rcases Y.eq_empty_or_nonempty with hY | hne
    · have := hx p₀ hp₀
      rw [hY] at this
      simp [profitFn] at this
    obtain ⟨m, hm⟩ := hb₀
    obtain ⟨q, c, hqx, hqY⟩ := separation_section_3_F hcl hc hxY
    have hb : ∀ y ∈ Y, (-q) ⬝ᵥ y ≤ -c := by
      intro y hy
      rw [neg_dotProduct]
      linarith [hqY y hy]
    have hp0 := nonneg_of_bdd_freeDisposal hne hfd hb
    set δ := (-q) ⬝ᵥ x + c with hδ
    have hδpos : 0 < δ := by rw [hδ, neg_dotProduct]; linarith
    set A := |m - p₀ ⬝ᵥ x| with hA
    set ε := δ / (2 * (δ + A)) with hε
    have hδA : 0 < δ + A := by positivity
    have hεpos : 0 < ε := by positivity
    have hε1 : ε < 1 := by
      rw [hε, div_lt_one (by positivity)]
      have : 0 ≤ A := abs_nonneg _
      linarith
    set p := (1 - ε) • (-q) + ε • p₀ with hp
    have hppos : StrictlyPositive p := by
      intro l
      simp only [hp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hp0 l
      have := hp₀ l
      have : 0 ≤ (1 - ε) * (-q) l := mul_nonneg (by linarith) (hp0 l)
      nlinarith
    have hbound : ∀ y ∈ Y, p ⬝ᵥ y ≤ (1 - ε) * (-c) + ε * m := by
      intro y hy
      simp only [hp, add_dotProduct, smul_dotProduct, smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb y hy) (by linarith))
        (mul_le_mul_of_nonneg_left (hm ⟨y, hy, rfl⟩) hεpos.le)
    have h1 := (hx p hppos).trans
      (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hbound y hy))
    have h2 := EReal.coe_le_coe_iff.mp h1
    simp only [hp, add_dotProduct, smul_dotProduct, smul_eq_mul] at h2
    have hkey : ε * (δ + A) < δ := by
      have : ε * (δ + A) = δ / 2 := by
        rw [hε]
        field_simp
      linarith
    have hAge : m - p₀ ⬝ᵥ x ≤ A := le_abs_self _
    have : (1 - ε) * ((-q) ⬝ᵥ x) + ε * (p₀ ⬝ᵥ x) - ((1 - ε) * (-c) + ε * m) =
        (1 - ε) * δ - ε * (m - p₀ ⬝ᵥ x) := by
      rw [hδ]; ring
    nlinarith

/-- **Proposition 5.C.1(iii)** is false as printed (correction): `Y = {y ∈ ℝ² : y₂ ≤ 0}` is
nonempty, closed, convex and has free disposal, `π(p) = +∞` for every `p ≫ 0`, so
`{y : p·y ≤ π(p) for all p ≫ 0} = ℝ² ≠ Y`. -/
theorem proposition_5_C_1_iii_counterexample :
    let Y : Set (Fin 2 → ℝ) := {y | y 1 ≤ 0}
    Y.Nonempty ∧ IsClosed Y ∧ Convex ℝ Y ∧ FreeDisposal Y ∧
      (∀ p : Fin 2 → ℝ, StrictlyPositive p → profitFn Y p = ⊤) ∧
      ![0, 1] ∉ Y ∧
      ∀ p : Fin 2 → ℝ, StrictlyPositive p →
        ((p ⬝ᵥ ![0, 1] : ℝ) : EReal) ≤ profitFn Y p := by
  intro Y
  have htop : ∀ p : Fin 2 → ℝ, StrictlyPositive p → profitFn Y p = ⊤ := by
    intro p hp
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    refine ⟨_, ⟨![(|r| + 1) / p 0, 0], by simp [Y], rfl⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, add_zero]
    rw [mul_div_cancel₀ _ (hp 0).ne']
    linarith [le_abs_self r]
  refine ⟨⟨0, by simp [Y]⟩, isClosed_le (continuous_apply 1) continuous_const, ?_, ?_, htop,
    by simp [Y], fun p hp => by rw [htop p hp]; exact le_top⟩
  · intro y hy y' hy' a b ha hb _
    simp only [Y, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hy' ⊢
    nlinarith
  · intro y hy y' hy'
    exact (hy' 1).trans hy

/-- **Proposition 5.C.1(iv)** (MWG, p. 138). The supply correspondence is homogeneous of degree
zero: `y(αp) = y(p)` for `α > 0`. -/
theorem proposition_5_C_1_iv (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 < α) :
    supply Y (α • p) = supply Y p := by
  ext y
  simp only [supply, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun y' hy' => le_of_mul_le_mul_left (h y' hy') hα⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun y' hy' => mul_le_mul_of_nonneg_left (h y' hy') hα.le⟩

/-- **Proposition 5.C.1(v)** (MWG, p. 138), first part. If `Y` is convex, `y(p)` is convex. -/
theorem proposition_5_C_1_v_convex {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y) (p : Fin L → ℝ) :
    Convex ℝ (supply Y p) := by
  rintro y ⟨hy, hmax⟩ y' ⟨hy', hmax'⟩ a b ha hb hab
  refine ⟨hc hy hy' ha hb hab, fun z hz => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := hmax z hz
  have h2 := hmax' z hz
  calc p ⬝ᵥ z = a * p ⬝ᵥ z + b * p ⬝ᵥ z := by rw [← add_mul, hab, one_mul]
    _ ≤ a * p ⬝ᵥ y + b * p ⬝ᵥ y' :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **Proposition 5.C.1(v)** (MWG, p. 138), second part. If `Y` is strictly convex, `y(p)` has
at most one element (for `p ≠ 0`). -/
theorem proposition_5_C_1_v_strict {Y : Set (Fin L → ℝ)} (hsc : StrictConvex ℝ Y)
    {p : Fin L → ℝ} (hp : p ≠ 0) : (supply Y p).Subsingleton := by
  intro y hy y' hy'
  by_contra hne
  have hint := hsc hy.1 hy'.1 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  set m := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y'
  have hnhds : Y ∈ 𝓝 m := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => m + t • p := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : m + (ε / 2) • p ∈ Y := hball hmem
  have hle := hy.2 _ hin
  have hle' := hy'.2 y hy.1
  have hle'' := hy.2 y' hy'.1
  have hpp : 0 < p ⬝ᵥ p := by
    have h0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hp (dotProduct_self_eq_zero.mp h))
  simp only [m, dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
  nlinarith

/-- **Proposition 5.C.1(vi), Hotelling's lemma** (MWG, p. 138), for closed convex `Y`: if
`y(p̄) = {ȳ}`, then profits are finite near `p̄` and `π` is differentiable at `p̄` with
`∇π(p̄) = ȳ`. Proof: Proposition 3.F.1 (Chapter 3) applied to `-Y`. -/
theorem proposition_5_C_1_vi {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    {p y : Fin L → ℝ} (hy : supply Y p = {y}) :
    (∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' Y)) ∧
      HasFDerivAt (profit Y) (dualityDotCLM y) p := by
  have hmem : -y ∈ supportArgmin (-Y) p := by
    have : y ∈ supply Y p := by rw [hy]; rfl
    rw [supply_eq_neg_supportArgmin] at this
    exact this
  have huniq : ∀ x ∈ supportArgmin (-Y) p, x = -y := by
    intro x hx
    have : -x ∈ supply Y p := by
      rw [supply_eq_neg_supportArgmin, Set.mem_neg, neg_neg]
      exact hx
    rw [hy] at this
    rw [← neg_neg x, show -x = y from this]
  have hcl' : IsClosed (-Y) := hcl.neg
  have hc' : Convex ℝ (-Y) := hc.neg
  obtain ⟨hb, hd⟩ := duality_differentiable_of_unique hcl' hc' hmem huniq
  refine ⟨?_, ?_⟩
  · filter_upwards [hb] with q hq
    exact (bddAbove_iff_bddBelow_neg Y q).mpr hq
  · have : profit Y = fun q => -supportFn (-Y) q := funext fun q => profit_eq_neg_supportFn Y q
    rw [this]
    have h2 := hd.neg
    have heq : -dualityDotCLM (-y) = dualityDotCLM (L := L) y := by
      ext q
      simp [dualityDotCLM_apply]
    rwa [heq] at h2

/-- The nonconvex production set `ℝ²_- ∪ {y : y₁ + y₂ ≤ -1}` (closed, free disposal). -/
def hotellingCounterexampleSet : Set (Fin 2 → ℝ) :=
  {y | y ≤ 0} ∪ {y | y 0 + y 1 ≤ -1}

/-- **Proposition 5.C.1(vi)** needs convexity (correction): `Y = ℝ²_- ∪ {y : y₁ + y₂ ≤ -1}` is
nonempty, closed and has free disposal, `y(1, 1) = {0}`, but `π(1 + δ, 1) = +∞` for every
`δ > 0`, so `π` is not finite near `(1, 1)`, let alone differentiable. -/
theorem proposition_5_C_1_vi_nonconvex_counterexample :
    IsClosed hotellingCounterexampleSet ∧ FreeDisposal hotellingCounterexampleSet ∧
      supply hotellingCounterexampleSet ![1, 1] = {0} ∧
      ∀ δ : ℝ, 0 < δ → profitFn hotellingCounterexampleSet ![1 + δ, 1] = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (isClosed_le continuous_id continuous_const).union
      (isClosed_le (by fun_prop) continuous_const)
  · rintro y (hy | hy) y' hy'
    · exact Or.inl (hy'.trans hy)
    · right
      simp only [Set.mem_ofPred_eq] at hy ⊢
      linarith [hy' 0, hy' 1]
  · ext y
    simp only [supply, hotellingCounterexampleSet, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul]
    constructor
    · rintro ⟨hy, hmax⟩
      have h0 := hmax 0 (Or.inl le_rfl)
      simp only [Pi.zero_apply, add_zero] at h0
      rcases hy with hy | hy
      · funext i
        fin_cases i
        · have h0' : y 0 ≤ 0 := hy 0
          have h1' : y 1 ≤ 0 := hy 1
          simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
          linarith
        · have h0' : y 0 ≤ 0 := hy 0
          have h1' : y 1 ≤ 0 := hy 1
          simp only [Fin.mk_one, Fin.isValue, Pi.zero_apply]
          linarith
      · linarith
    · rintro rfl
      refine ⟨Or.inl le_rfl, fun y' hy' => ?_⟩
      simp only [Pi.zero_apply, add_zero]
      rcases hy' with hy' | hy'
      · have h0' : y' 0 ≤ 0 := hy' 0
        have h1' : y' 1 ≤ 0 := hy' 1
        linarith
      · linarith
  · intro δ hδ
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set t := (|r| + 2) / δ with ht
    refine ⟨_, ⟨![t, -1 - t], Or.inr (by simp), rfl⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : δ * t = |r| + 2 := by rw [ht]; field_simp
    nlinarith [le_abs_self r]

/-- **Section 5.C** (MWG, p. 138), the law of supply (5.C.3): `(p - p')·(y - y') ≥ 0` for
`y ∈ y(p)` and `y' ∈ y(p')`, by the revealed preference argument. -/
theorem law_of_supply {Y : Set (Fin L → ℝ)} {p p' y y' : Fin L → ℝ} (hy : y ∈ supply Y p)
    (hy' : y' ∈ supply Y p') : 0 ≤ (p - p') ⬝ᵥ (y - y') := by
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), semidefiniteness, for any `Y`: if `y(·)` is a
selection from the supply correspondence near `p̄` with derivative `Dy` at `p̄`, then
`Dy(p̄)` is positive semidefinite (the law of supply in differential form). -/
theorem proposition_5_C_1_vii_psd {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    PosSemidefMWG (jacobian D) := by
  intro z
  rw [jacobian_mulVec]
  set γ : ℝ → Fin L → ℝ := fun t => p + t • z with hγ
  have hγd : HasDerivAt γ z 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => ys (γ t)) (D z) 0 := by
    rw [← hγ0] at hD
    exact hD.comp_hasDerivAt 0 hγd
  have hg : HasDerivAt (fun t => ∑ l, z l * ys (γ t) l) (∑ l, z l * D z l) 0 :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hcomp l).const_mul (z l)
  rw [← neg_nonpos]
  apply hasDerivAt_nonpos_of_right_le hg.neg
  have hcont : Tendsto γ (𝓝[>] 0) (𝓝 p) := by
    rw [← hγ0]
    exact hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hcont.eventually hys, self_mem_nhdsWithin] with t ht htpos
  have hlaw := law_of_supply ht hys.self_of_nhds
  have hsub : γ t - p = t • z := by simp [γ]
  rw [hsub, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hlaw
  have : 0 ≤ z ⬝ᵥ ys (γ t) - z ⬝ᵥ ys p := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_pos_of_neg (show (0 : ℝ) < t from htpos) h
    linarith
  simp only [dotProduct] at this
  simp only [Pi.neg_apply, hγ0]
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), `Dy(p̄)p̄ = 0`, for any `Y`: if `y(q) = {ys q}` for
`q` near `p̄` and `ys` has derivative `Dy` at `p̄`, then `Dy(p̄)p̄ = 0` (from (iv)). -/
theorem proposition_5_C_1_vii_euler {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) : D p = 0 := by
  set γ : ℝ → Fin L → ℝ := fun t => p + t • p with hγ
  have hγd : HasDerivAt γ p 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => ys (γ t)) (D p) 0 := by
    have hD' := hD
    rw [← hγ0] at hD'
    exact hD'.comp_hasDerivAt 0 hγd
  have hcont : Tendsto γ (𝓝 0) (𝓝 p) := by
    rw [← hγ0]
    exact hγd.continuousAt.tendsto
  have hconst : (fun t => ys (γ t)) =ᶠ[𝓝 0] fun _ => ys p := by
    have : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := lt_mem_nhds (by norm_num)
    filter_upwards [this, hcont.eventually hys] with t ht hst
    have hpos : 0 < 1 + t := by linarith
    have hγt : γ t = (1 + t) • p := by simp [γ, add_smul]
    have h1 := hys.self_of_nhds
    rw [hγt, proposition_5_C_1_iv Y p hpos, h1] at hst
    rw [hγt]
    have : ys ((1 + t) • p) ∈ ({ys p} : Set (Fin L → ℝ)) := by rw [hst]; rfl
    exact this
  have h0 : HasDerivAt (fun t => ys (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (ys p)).congr_of_eventuallyEq hconst
  exact hcomp.unique h0

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), `Dy(p̄) = D²π(p̄)` and symmetry, for closed convex
`Y`: if `y(q) = {ys q}` for `q` near `p̄` and `ys` has derivative `Dy` at `p̄`, then `∇π = ys`
near `p̄`, the Hessian of `π` at `p̄` is the Jacobian of `ys`, and it is symmetric. -/
theorem proposition_5_C_1_vii {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    hessianMatrix (profit Y) p = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ PosSemidefMWG (jacobian D) ∧ D p = 0 := by
  have hgrad : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q := by
    filter_upwards [hys] with q hq
    exact (proposition_5_C_1_vi hcl hc hq).2
  refine ⟨?_, ?_, ?_, proposition_5_C_1_vii_euler hys hD⟩
  · have heq : (fun q => gradientVec (fderiv ℝ (profit Y) q)) =ᶠ[𝓝 p] ys := by
      filter_upwards [hgrad] with q hq
      rw [hq.fderiv, gradientVec_dualityDotCLM]
    rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]
  · have h1 : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotLin (ys q)) q := by
      filter_upwards [hgrad] with q hq
      rwa [dualityDotLin_apply]
    have h2 : HasFDerivAt (fun q => dualityDotLin (ys q)) (dualityDotLin.comp D) p :=
      dualityDotLin.hasFDerivAt.comp p hD
    intro i j
    have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
    simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
      dotProduct_single, mul_one] at this
    simpa [jacobian] using this
  · exact proposition_5_C_1_vii_psd (hys.mono fun q hq => by rw [hq]; rfl) hD

end MWG.Production
