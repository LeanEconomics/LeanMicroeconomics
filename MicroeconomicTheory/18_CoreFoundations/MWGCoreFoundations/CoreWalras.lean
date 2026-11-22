/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.Basic

/-!
# Walrasian allocations are in the core (MWG Section 18.B, pp. 653-655; Exercise 18.B.1)

* **Proposition 18.B.1** (`proposition_18_B_1`): every Walrasian equilibrium allocation has the
  core property, for any convex constant returns technology `Y` (this is **Exercise 18.B.1**;
  only the cone property of `Y` and no assumption on preferences is used). The book's exchange
  case `Y = -ℝ^L₊` is `proposition_18_B_1_exchange`.
* Pareto optimality for the economy of Section 18.B (`CoreEconomy.IsParetoOptimal`), with the
  bridge `isParetoOptimal_iff_toPriv` to Chapter 16's Definition 16.B.2.
* **Footnote 2** (`footnote_18_2`): with continuity and strong monotonicity a Pareto dominated
  feasible allocation is dominated by a feasible allocation that is strictly better for every
  consumer (a small transfer of one good), via the general lemma `exists_strict_all_of_weak`.
* p. 654: core allocations are Pareto optimal (`core_isParetoOptimal`; without footnote 2 only
  weak Pareto optimality holds, `core_not_strictly_dominated`) and individually rational.
* **Figure 18.B.1** (`figure_18_B_1`): with two consumers the core is the set of Pareto optimal
  and individually rational allocations (the contract curve).
* p. 655, the converse of Proposition 18.B.1 is false (`converse_18_B_1_false`): with
  `u = √x₁ + √x₂`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)`, the allocation `x₁ = (1/3, 1/3)`,
  `x₂ = (2/3, 2/3)` is in the core but is not Walrasian for any price vector.
* **Figure 18.B.2** (`figure_18_B_2`): in the 2-replica of that economy the same equal-treatment
  allocation is blocked by the two consumers of the less favoured type 1 together with one
  consumer of type 2 (type 2 gets `(1, 9/20)`, each type 1 gets `(1/2, 11/40)`), so the type
  allocation lies in `C₁` but not in `C₂` (the book's figure has the roles of the types
  interchanged). The book's bracketed identity `-2(x'₂ - ω₂) = x'₁ - ω₁` is
  `figure_18_B_2_identity`; footnote 4 (Bertrand competition) is verbal.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {ι : Type*} {L : ℕ}

/-- **Proposition 18.B.1** (MWG, p. 654), in the generality of Exercise 18.B.1: with a constant
returns technology, every Walrasian equilibrium allocation has the core property. -/
theorem proposition_18_B_1 [Fintype ι] (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y)
    {x : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) : x ∈ E.core := by
  obtain ⟨⟨y, hy, hsum, hmax⟩, hx⟩ := h
  have hp0 := profit_eq_zero_of_max hY hy hmax
  refine ⟨⟨fun i => (hx i).1.1, y, hy, hsum⟩, fun S ⟨hS, x', hx', y', hy', hsum'⟩ => ?_⟩
  have hgt : ∀ i ∈ S, p ⬝ᵥ E.ω i < p ⬝ᵥ x' i := by
    intro i hi
    by_contra hle
    push Not at hle
    exact (hx' i hi).2.2 ((hx i).2 _ ⟨(hx' i hi).1, hle⟩)
  have hlt := Finset.sum_lt_sum_of_nonempty hS hgt
  rw [← dotProduct_sum, ← dotProduct_sum, hsum', dotProduct_add] at hlt
  have := hmax y' hy'
  linarith

/-- **Exercise 18.B.1** (MWG, p. 684). Walrasian allocations are in the core for the model with a
constant returns technology of Section 18.B. -/
theorem exercise_18_B_1 [Fintype ι] (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y)
    {x : ι → Fin L → ℝ} (h : E.IsWalrasAlloc x) : x ∈ E.core :=
  proposition_18_B_1 E hY h.choose_spec

/-- **Proposition 18.B.1** (MWG, pp. 654-655), the exchange case proved in the book:
`Y = -ℝ^L₊`. -/
theorem proposition_18_B_1_exchange [Fintype ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) {x : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    x ∈ E.core :=
  proposition_18_B_1 E (hY ▸ isCRSTechnology_nonposOrthant) h

/-! ### Pareto optimality and individual rationality -/

/-- **Section 18.B** (MWG, p. 654; Definition 16.B.2). `x'` Pareto dominates `x`. -/
def CoreEconomy.ParetoDominates (E : CoreEconomy ι L) (x' x : ι → Fin L → ℝ) : Prop :=
  (∀ i, E.pref i (x' i) (x i)) ∧ ∃ i, Strict (E.pref i) (x' i) (x i)

/-- **Section 18.B** (MWG, p. 654; Definition 16.B.2). A feasible allocation is Pareto optimal if
no feasible allocation Pareto dominates it. -/
def CoreEconomy.IsParetoOptimal [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Prop :=
  E.IsFeasible x ∧ ¬ ∃ x', E.IsFeasible x' ∧ E.ParetoDominates x' x

/-- **Section 18.B** (MWG, p. 654). `x` is individually rational: no consumer can do strictly
better on her own, i.e. `xᵢ ≿ᵢ z` for every `z ≥ 0` in `Y + {ωᵢ}` (no one-consumer coalition
blocks). -/
def CoreEconomy.IsIndividuallyRational (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∀ i, ∀ z ∈ nonnegOrthant L, (∃ y ∈ E.Y, z = y + E.ω i) → E.pref i (x i) z

/-- Pareto optimality of Section 18.B is Chapter 16's Definition 16.B.2 for the private ownership
economy with one constant returns firm (any shares). -/
theorem isParetoOptimal_iff_toPriv [Fintype ι] (E : CoreEconomy ι L) (θ : ι → ℝ)
    (x : ι → Fin L → ℝ) :
    E.IsParetoOptimal x ↔ ∃ y, (E.toPriv θ).toEconomy.IsParetoOptimal ⟨x, fun _ => y⟩ := by
  have hfeas : ∀ (x' : ι → Fin L → ℝ) (y : Fin L → ℝ),
      (E.toPriv θ).toEconomy.IsFeasible ⟨x', fun _ => y⟩ ↔
        (∀ i, x' i ∈ nonnegOrthant L) ∧ y ∈ E.Y ∧ ∑ i, x' i = y + ∑ i, E.ω i := by
    intro x' y
    simp only [PrefEconomy.IsFeasible, PrefEconomy.IsAllocation, PrivPrefEconomy.toEconomy,
      CoreEconomy.toPriv, Finset.univ_unique, Finset.sum_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2 (), by rw [h3, add_comm]⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, fun _ => h2⟩, by rw [h3, add_comm]⟩
  constructor
  · rintro ⟨⟨hx, y, hy, hsum⟩, hpo⟩
    refine ⟨y, (hfeas x y).2 ⟨hx, hy, hsum⟩, ?_⟩
    rintro ⟨a', ha', hdom⟩
    obtain ⟨h1, h2, h3⟩ := (hfeas a'.x (a'.y ())).1 (by
      obtain ⟨⟨hx1, hy1⟩, hs1⟩ := ha'
      refine ⟨⟨hx1, fun _ => hy1 ()⟩, ?_⟩
      simpa [PrivPrefEconomy.toEconomy] using hs1)
    exact hpo ⟨a'.x, ⟨h1, _, h2, h3⟩, hdom⟩
  · rintro ⟨y, hfe, hpo⟩
    obtain ⟨hx, hy, hsum⟩ := (hfeas x y).1 hfe
    refine ⟨⟨hx, y, hy, hsum⟩, ?_⟩
    rintro ⟨x', ⟨hx', y', hy', hsum'⟩, hdom⟩
    exact hpo ⟨⟨x', fun _ => y'⟩, (hfeas x' y').2 ⟨hx', hy', hsum'⟩, hdom⟩

/-- A transfer lemma (footnotes 2 and 5 of MWG, pp. 654 and 656): if within the group `S` every
`x'ᵢ` is weakly preferred to `zᵢ` and `x'ₖ` is strictly preferred to `zₖ`, then, with rational,
continuous and strongly monotone preferences on `ℝ^L₊`, there are `x''ᵢ ≥ 0` with the same total
over `S`, every one strictly preferred to `zᵢ`: consumer `k` gives away a small amount `δ` of a
good she holds, shared equally among the members of `S`. -/
theorem exists_strict_all_of_weak
    {pref : ι → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant L) (pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (pref i)) (S : Finset ι)
    {x' z : ι → Fin L → ℝ} (hx' : ∀ i ∈ S, x' i ∈ nonnegOrthant L)
    (hz : ∀ i ∈ S, z i ∈ nonnegOrthant L) (hweak : ∀ i ∈ S, pref i (x' i) (z i)) {k : ι}
    (hk : k ∈ S) (hstrict : Strict (pref k) (x' k) (z k)) :
    ∃ x'' : ι → Fin L → ℝ, (∀ i ∈ S, x'' i ∈ nonnegOrthant L ∧ Strict (pref i) (x'' i) (z i)) ∧
      ∑ i ∈ S, x'' i = ∑ i ∈ S, x' i := by
  classical
  -- consumer `k` holds some good in positive quantity
  obtain ⟨m, hm0⟩ : ∃ m, 0 < x' k m := by
    by_contra hall
    push Not at hall
    have hx0 : x' k = 0 := funext fun m => le_antisymm (hall m) (hx' k hk m)
    by_cases hzk : z k = x' k
    · rw [hzk] at hstrict
      exact hstrict.2 hstrict.1
    · have hle : x' k ≤ z k := fun l => by rw [hx0]; exact hz k hk l
      exact hstrict.2 (hm k (x' k) (hx' k hk) (z k) (hz k hk) hle hzk).1
  obtain ⟨δ, hδ, hmem, hs⟩ :=
    exists_strict_sub_single (hr k) (hc k) (hx' k hk) (hz k hk) hstrict hm0
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨k, hk⟩
  set base : ι → Fin L → ℝ := fun i => x' i - if i = k then Pi.single m δ else 0 with hbase
  set x'' : ι → Fin L → ℝ := fun i => base i + Pi.single m (δ / S.card) with hx''
  have hbaseX : ∀ i ∈ S, base i ∈ nonnegOrthant L := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simpa [hbase] using hmem
    · simpa [hbase, hik] using hx' i hi
  have hbaseR : ∀ i ∈ S, pref i (base i) (z i) := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simpa [hbase] using hs.1
    · simpa [hbase, hik] using hweak i hi
  have hδc : 0 < δ / S.card := div_pos hδ hcard
  refine ⟨x'', fun i hi => ?_, ?_⟩
  · have hle : base i ≤ x'' i := fun l => by
      simp only [hx'', Pi.add_apply, le_add_iff_nonneg_right]
      by_cases hl : l = m
      · subst hl; simp [hδc.le]
      · simp [hl]
    have hne : x'' i ≠ base i := by
      intro h
      have := congrFun h m
      simp only [hx'', Pi.add_apply, Pi.single_eq_same, add_eq_left] at this
      exact hδc.ne' this
    have hX : x'' i ∈ nonnegOrthant L := fun l => le_trans (hbaseX i hi l) (hle l)
    have hst := hm i (base i) (hbaseX i hi) (x'' i) hX hle hne
    refine ⟨hX, ?_⟩
    exact strict_of_strict_of_pref (hr i).2 hX (hbaseX i hi) (hz i hi) hst (hbaseR i hi)
  · simp only [hx'', hbase, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' S k, hk, ↓reduceIte, Finset.sum_const]
    have hns : S.card • (Pi.single m (δ / S.card) : Fin L → ℝ) = Pi.single m δ := by
      funext l
      rw [Pi.smul_apply, nsmul_eq_mul]
      by_cases hl : l = m
      · subst hl
        rw [Pi.single_eq_same, Pi.single_eq_same]
        field_simp
      · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, mul_zero]
    rw [hns]
    abel

/-- **Footnote 2** (MWG, p. 654). With continuity and strong monotonicity of preferences, if a
feasible allocation `x'` Pareto dominates `x`, then some feasible allocation is strictly better
than `x` for every consumer. -/
theorem footnote_18_2 [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {x x' : ι → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (hfe : E.IsFeasible x') (hdom : E.ParetoDominates x' x) :
    ∃ x'', E.IsFeasible x'' ∧ ∀ i, Strict (E.pref i) (x'' i) (x i) := by
  classical
  obtain ⟨k, hk⟩ := hdom.2
  obtain ⟨x'', hx'', hsum⟩ := exists_strict_all_of_weak hr hc hm Finset.univ
    (fun i _ => hfe.1 i) (fun i _ => hx i) (fun i _ => hdom.1 i) (Finset.mem_univ k) hk
  obtain ⟨y, hy, hs⟩ := hfe.2
  exact ⟨x'', ⟨fun i => (hx'' i (Finset.mem_univ i)).1, y, hy, by rw [hsum, hs]⟩,
    fun i => (hx'' i (Finset.mem_univ i)).2⟩

/-- **Section 18.B** (MWG, p. 654). A core allocation is weakly Pareto optimal: the coalition of
the whole cannot make everyone strictly better off. -/
theorem core_not_strictly_dominated [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    {x : ι → Fin L → ℝ} (hx : x ∈ E.core) :
    ¬ ∃ x', E.IsFeasible x' ∧ ∀ i, Strict (E.pref i) (x' i) (x i) := by
  rintro ⟨x', ⟨hx', y, hy, hsum⟩, hs⟩
  exact hx.2 Finset.univ ⟨Finset.univ_nonempty, x', fun i _ => ⟨hx' i, hs i⟩, y, hy, hsum⟩

/-- **Section 18.B** (MWG, p. 654). All allocations in the core are Pareto optimal (with
footnote 2: continuous, strongly monotone preferences). -/
theorem core_isParetoOptimal [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : x ∈ E.core) : E.IsParetoOptimal x := by
  refine ⟨hx.1, ?_⟩
  rintro ⟨x', hfe, hdom⟩
  have : Nonempty ι := ⟨hdom.2.choose⟩
  obtain ⟨x'', hfe'', hs⟩ := footnote_18_2 E hr hc hm hx.1.1 hfe hdom
  exact core_not_strictly_dominated E hx ⟨x'', hfe'', hs⟩

/-- **Section 18.B** (MWG, p. 654). A core allocation is individually rational (no one-consumer
coalition blocks it; completeness of preferences is used). -/
theorem core_isIndividuallyRational [Fintype ι] (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : x ∈ E.core) : E.IsIndividuallyRational x := by
  classical
  intro i z hz ⟨y, hy, hzy⟩
  rcases (hr i).1 (x i) (hx.1.1 i) z hz with h | h
  · exact h
  · by_contra hn
    refine hx.2 {i} ⟨Finset.singleton_nonempty i, fun _ => z, ?_, y, hy, ?_⟩
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨hz, h, hn⟩
    · simp [hzy]

/-- In a pure exchange economy with rational, strongly monotone preferences and `ωᵢ ≥ 0`,
individual rationality is `xᵢ ≿ᵢ ωᵢ` for every `i`. -/
theorem isIndividuallyRational_iff_exchange (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {x : ι → Fin L → ℝ} (hx : ∀ i, x i ∈ nonnegOrthant L) :
    E.IsIndividuallyRational x ↔ ∀ i, E.pref i (x i) (E.ω i) := by
  constructor
  · intro h i
    exact h i (E.ω i) (hω i) ⟨0, hY ▸ fun _ => le_rfl, (zero_add _).symm⟩
  · intro h i z hz ⟨y, hy, hzy⟩
    rw [hY] at hy
    have hle : z ≤ E.ω i := fun l => by rw [hzy]; simp only [Pi.add_apply]; linarith [hy l]
    by_cases hzω : E.ω i = z
    · rw [← hzω]; exact h i
    · exact (hr i).2 _ (hx i) _ (hω i) _ hz (h i) (hm i z hz (E.ω i) (hω i) hle hzω).1

/-- **Figure 18.B.1** (MWG, p. 654). With two consumers (continuous, strongly monotone
preferences) the core consists exactly of the Pareto optimal and individually rational
allocations: the only coalitions are `{1}`, `{2}` and `{1, 2}`. -/
theorem figure_18_B_1 [Fintype ι] (hcard : Fintype.card ι = 2) (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (x : ι → Fin L → ℝ) :
    x ∈ E.core ↔ E.IsParetoOptimal x ∧ E.IsIndividuallyRational x := by
  classical
  refine ⟨fun h => ⟨core_isParetoOptimal E hr hc hm h, core_isIndividuallyRational E hr h⟩, ?_⟩
  rintro ⟨hpo, hir⟩
  refine ⟨hpo.1, fun S ⟨hS, x', hx', y, hy, hsum⟩ => ?_⟩
  have hle : S.card ≤ 2 := hcard ▸ Finset.card_le_univ S
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  rcases (show S.card = 1 ∨ S.card = 2 by omega) with h1 | h2
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have hi := hx' i (Finset.mem_singleton_self i)
    exact hi.2.2 (hir i (x' i) hi.1 ⟨y, hy, by simpa using hsum⟩)
  · have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [h2, hcard])
    subst hSu
    obtain ⟨k, -⟩ := hS
    exact hpo.2 ⟨x', ⟨fun i => (hx' i (Finset.mem_univ i)).1, y, hy, hsum⟩,
      fun i => (hx' i (Finset.mem_univ i)).2.1, k, (hx' k (Finset.mem_univ k)).2⟩

/-! ### The converse of Proposition 18.B.1 is false (p. 655) -/

/-- `√x₁ + √x₂` for two goods. -/
theorem sqrtU_two (x : Fin 2 → ℝ) : sqrtU x = Real.sqrt (x 0) + Real.sqrt (x 1) := by
  simp [sqrtU, Fin.sum_univ_two]

/-- `√a + √b` at the bundle `(a, b)`. -/
theorem sqrtU_vec (a b : ℝ) : sqrtU ![a, b] = Real.sqrt a + Real.sqrt b := by
  rw [sqrtU_two]
  rfl

/-- The tangent-line bound for `√`: `2c√a ≤ a + c²` for `a ≥ 0`. -/
theorem two_mul_sqrt_le (a c : ℝ) (ha : 0 ≤ a) : 2 * c * Real.sqrt a ≤ a + c ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - c), Real.sq_sqrt ha]

/-- In a pure exchange economy with utilities `√x₁ + √x₂`, an allocation on the diagonals,
`xᵢ = (tᵢ, tᵢ)` with `tᵢ > 0` and `∑ᵢ tᵢ` equal to the total endowment of each good, is Pareto
optimal (the tangent-line bound gives `x'ᵢ₁ + x'ᵢ₂ ≥ 2tᵢ` for any `x'ᵢ ≿ xᵢ`). -/
theorem sqrtEconomy_diag_isParetoOptimal [Fintype ι] {ω : ι → Fin 2 → ℝ} {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (h0 : ∑ i, ω i 0 = ∑ i, t i) (h1 : ∑ i, ω i 1 = ∑ i, t i) :
    (sqrtEconomy ω).IsParetoOptimal (fun i => ![t i, t i]) := by
  have hfe : (sqrtEconomy ω).IsFeasible (fun i => ![t i, t i]) := by
    refine ⟨fun i l => ?_, 0, fun _ => le_rfl, ?_⟩
    · fin_cases l <;> simp [(ht i).le]
    · funext l
      fin_cases l <;> simp [Finset.sum_apply, sqrtEconomy, h0, h1]
  refine ⟨hfe, ?_⟩
  rintro ⟨x', ⟨hx', y, hy, hsum⟩, hweak, k, hk⟩
  -- each consumer needs at least `2tᵢ` units in total, consumer `k` more
  have hbound : ∀ i, 2 * t i ≤ x' i 0 + x' i 1 := by
    intro i
    have hw : 2 * Real.sqrt (t i) ≤ sqrtU (x' i) := by
      have := hweak i
      change sqrtU ![t i, t i] ≤ sqrtU (x' i) at this
      rw [sqrtU_vec] at this
      linarith
    rw [sqrtU_two] at hw
    have a0 := two_mul_sqrt_le (x' i 0) (Real.sqrt (t i)) (hx' i 0)
    have a1 := two_mul_sqrt_le (x' i 1) (Real.sqrt (t i)) (hx' i 1)
    have hs := Real.sq_sqrt (ht i).le
    have hsp := Real.sqrt_pos.mpr (ht i)
    nlinarith
  have hstrict : 2 * t k < x' k 0 + x' k 1 := by
    have hw : 2 * Real.sqrt (t k) < sqrtU (x' k) := by
      have := hk.2
      change ¬ sqrtU (x' k) ≤ sqrtU ![t k, t k] at this
      rw [sqrtU_vec] at this
      linarith
    rw [sqrtU_two] at hw
    have a0 := two_mul_sqrt_le (x' k 0) (Real.sqrt (t k)) (hx' k 0)
    have a1 := two_mul_sqrt_le (x' k 1) (Real.sqrt (t k)) (hx' k 1)
    have hs := Real.sq_sqrt (ht k).le
    have hsp := Real.sqrt_pos.mpr (ht k)
    nlinarith
  have hlt : ∑ i, 2 * t i < ∑ i, (x' i 0 + x' i 1) :=
    Finset.sum_lt_sum (fun i _ => hbound i) ⟨k, Finset.mem_univ k, hstrict⟩
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply] at e0 e1
  have hy0 := hy 0
  have hy1 := hy 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hlt
  simp only [sqrtEconomy] at e0 e1
  linarith

/-- The endowments `ω₁ = (1, 0)`, `ω₂ = (0, 1)` of the example of p. 655. -/
def exampleEndow : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- The diagonal shares `t = (1/3, 2/3)`. -/
noncomputable def exampleShare : Fin 2 → ℝ := ![1 / 3, 2 / 3]

/-- The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)`. -/
noncomputable def exampleAlloc : Fin 2 → Fin 2 → ℝ := fun i => ![exampleShare i, exampleShare i]

/-- `2√(1/3) < 6/5`. -/
theorem two_sqrt_third_lt : 2 * Real.sqrt (1 / 3) < 6 / 5 := by
  have : Real.sqrt (1 / 3) < 3 / 5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- `2√(2/3) < 41/25`. -/
theorem two_sqrt_two_thirds_lt : 2 * Real.sqrt (2 / 3) < 41 / 25 := by
  have : Real.sqrt (2 / 3) < 41 / 50 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Individual rationality in the example of p. 655: `uₕ(ωₕ) = 1 ≤ uₕ(xₕ)`. -/
theorem exampleAlloc_ir (a : Fin 2) : sqrtU (exampleEndow a) ≤ sqrtU (exampleAlloc a) := by
  fin_cases a
  · change sqrtU ![1, 0] ≤ sqrtU ![1 / 3, 1 / 3]
    rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one, Real.sqrt_zero]
    have : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 3) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  · change sqrtU ![0, 1] ≤ sqrtU ![2 / 3, 2 / 3]
    rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one, Real.sqrt_zero]
    have : (1 : ℝ) / 2 ≤ Real.sqrt (2 / 3) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith

/-- **Section 18.B** (MWG, p. 655). The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` of the
economy with `u = √x₁ + √x₂`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)` is in the core. -/
theorem exampleAlloc_mem_core : exampleAlloc ∈ (sqrtEconomy exampleEndow).core := by
  have hst := sqrtEconomy_standing (ω := exampleEndow) (L := 2)
    (fun i l => by fin_cases i <;> fin_cases l <;> norm_num [exampleEndow])
  have hr := fun i => (hst.2 i).2.1
  have hc := fun i => (hst.2 i).2.2.1
  have hm := fun i => (hst.2 i).2.2.2.2
  have hx : ∀ i, exampleAlloc i ∈ nonnegOrthant 2 := fun i l => by
    fin_cases i <;> fin_cases l <;> norm_num [exampleAlloc, exampleShare]
  refine (figure_18_B_1 (by simp) _ hr hc hm _).2 ⟨?_, ?_⟩
  · exact sqrtEconomy_diag_isParetoOptimal (t := exampleShare)
      (fun i => by fin_cases i <;> norm_num [exampleShare])
      (by simp [exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
      (by simp [exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
  · refine (isIndividuallyRational_iff_exchange _ rfl hr hm (fun i l => (hst.2 i).1 l) hx).2 ?_
    intro i
    exact exampleAlloc_ir i

/-- **Section 18.B** (MWG, p. 655). The allocation `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` is not a
Walrasian equilibrium allocation for any price vector `p`: affordability of both bundles forces
`p₂ = 2p₁`; if `p₁ ≤ 0` the bundle `(1, 1)` is affordable for consumer 1, and if `p₁ > 0` the
bundle `(1/2, 1/4)` is, both better than `(1/3, 1/3)`. -/
theorem exampleAlloc_not_walras : ¬ (sqrtEconomy exampleEndow).IsWalrasAlloc exampleAlloc := by
  rintro ⟨p, -, hx⟩
  have b0 := (hx 0).1.2
  have b1 := (hx 1).1.2
  change p ⬝ᵥ ![1 / 3, 1 / 3] ≤ p ⬝ᵥ ![1, 0] at b0
  change p ⬝ᵥ ![2 / 3, 2 / 3] ≤ p ⬝ᵥ ![0, 1] at b1
  simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at b0 b1
  have hu : sqrtU (exampleAlloc 0) < 6 / 5 := by
    change sqrtU ![1 / 3, 1 / 3] < 6 / 5
    rw [sqrtU_vec]
    linarith [two_sqrt_third_lt]
  rcases le_or_gt (p 0) 0 with hp | hp
  · have hb : (![1, 1] : Fin 2 → ℝ) ∈
        budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy exampleEndow).ω 0) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      change p ⬝ᵥ ![1, 1] ≤ p ⬝ᵥ ![1, 0]
      simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have := (hx 0).2 _ hb
    change sqrtU ![1, 1] ≤ sqrtU (exampleAlloc 0) at this
    rw [sqrtU_vec, Real.sqrt_one] at this
    linarith
  · have hb : (![1 / 2, 1 / 4] : Fin 2 → ℝ) ∈
        budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy exampleEndow).ω 0) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      change p ⬝ᵥ ![1 / 2, 1 / 4] ≤ p ⬝ᵥ ![1, 0]
      simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have := (hx 0).2 _ hb
    change sqrtU ![1 / 2, 1 / 4] ≤ sqrtU (exampleAlloc 0) at this
    rw [sqrtU_vec] at this
    have h1 : (7 : ℝ) / 10 < Real.sqrt (1 / 2) := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h2 : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 4) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith

/-- **Section 18.B** (MWG, p. 655). The converse of Proposition 18.B.1 is false: a core allocation
need not be Walrasian. -/
theorem converse_18_B_1_false :
    exampleAlloc ∈ (sqrtEconomy exampleEndow).core ∧
      ¬ (sqrtEconomy exampleEndow).IsWalrasAlloc exampleAlloc :=
  ⟨exampleAlloc_mem_core, exampleAlloc_not_walras⟩

/-! ### Figure 18.B.2: blocking in the 2-replica -/

/-- The blocking coalition of the 2-replica: both consumers of type 1 and one of type 2. -/
def fig18B2Coalition : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0)}

/-- The blocking consumptions: `(1/2, 11/40)` for type 1 and `(1, 9/20)` for type 2. -/
noncomputable def fig18B2Bundle : Fin 2 × Fin 2 → Fin 2 → ℝ :=
  fun i => ![![1 / 2, 11 / 40], ![1, 9 / 20]] i.1

/-- **Figure 18.B.2** (MWG, p. 655). In the 2-replica of the economy of p. 655 (two consumers of
each type), the equal-treatment allocation induced by `x₁ = (1/3, 1/3)`, `x₂ = (2/3, 2/3)` is
blocked by the two consumers of type 1 together with one consumer of type 2: the former get
`(1/2, 11/40)` each, the latter `(1, 9/20)`. So the type allocation is in `C₁` but not in
`C₂`. (The book's figure has the roles of the types interchanged.) -/
theorem figure_18_B_2 :
    ((sqrtEconomy exampleEndow).replica 2).Blocks fig18B2Coalition (typeAlloc exampleAlloc 2) ∧
      exampleAlloc ∈ (sqrtEconomy exampleEndow).CN 1 ∧
      exampleAlloc ∉ (sqrtEconomy exampleEndow).CN 2 := by
  have hblock : ((sqrtEconomy exampleEndow).replica 2).Blocks fig18B2Coalition
      (typeAlloc exampleAlloc 2) := by
    refine ⟨⟨(0, 0), by simp [fig18B2Coalition]⟩, fig18B2Bundle, fun i hi => ?_, 0,
      fun _ => le_rfl, ?_⟩
    · have h1 : (7 : ℝ) / 10 < Real.sqrt (1 / 2) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h2 : (13 : ℝ) / 25 < Real.sqrt (11 / 40) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h3 : (67 : ℝ) / 100 < Real.sqrt (9 / 20) := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h4 := two_sqrt_third_lt
      have h5 := two_sqrt_two_thirds_lt
      simp only [fig18B2Coalition, Finset.mem_insert, Finset.mem_singleton] at hi
      have k1 : sqrtU ![1 / 3, 1 / 3] < sqrtU ![1 / 2, 11 / 40] := by
        rw [sqrtU_vec, sqrtU_vec]; linarith
      have k2 : sqrtU ![2 / 3, 2 / 3] < sqrtU ![1, 9 / 20] := by
        rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]; linarith
      rcases hi with rfl | rfl | rfl
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![1 / 3, 1 / 3] ≤ sqrtU ![1 / 2, 11 / 40] ∧
          ¬ sqrtU ![1 / 2, 11 / 40] ≤ sqrtU ![1 / 3, 1 / 3]
        exact ⟨k1.le, not_le.mpr k1⟩
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![1 / 3, 1 / 3] ≤ sqrtU ![1 / 2, 11 / 40] ∧
          ¬ sqrtU ![1 / 2, 11 / 40] ≤ sqrtU ![1 / 3, 1 / 3]
        exact ⟨k1.le, not_le.mpr k1⟩
      · refine ⟨fun l => by fin_cases l <;> norm_num [fig18B2Bundle], ?_⟩
        change sqrtU ![2 / 3, 2 / 3] ≤ sqrtU ![1, 9 / 20] ∧
          ¬ sqrtU ![1, 9 / 20] ≤ sqrtU ![2 / 3, 2 / 3]
        exact ⟨k2.le, not_le.mpr k2⟩
    · funext l
      fin_cases l <;>
        simp [fig18B2Coalition, fig18B2Bundle, CoreEconomy.replica, sqrtEconomy,
          exampleEndow] <;> norm_num
  refine ⟨hblock, ⟨exampleAlloc_mem_core.1, ?_⟩, fun h => h.2.2 _ hblock⟩
  -- `C₁`: the replica with one consumer of each type is a two-consumer economy
  have hst := sqrtEconomy_standing (ω := fun i : Fin 2 × Fin 1 => exampleEndow i.1) (L := 2)
    (fun i l => by fin_cases l <;> fin_cases i <;> norm_num [exampleEndow])
  have hr := fun i => (hst.2 i).2.1
  have hc := fun i => (hst.2 i).2.2.1
  have hm := fun i => (hst.2 i).2.2.2.2
  have hx : ∀ i, typeAlloc exampleAlloc 1 i ∈ nonnegOrthant 2 := fun i l => by
    obtain ⟨a, b⟩ := i
    fin_cases a <;> fin_cases l <;> norm_num [typeAlloc, exampleAlloc, exampleShare]
  refine (figure_18_B_1 (by simp) _ hr hc hm _).2 ⟨?_, ?_⟩
  · exact sqrtEconomy_diag_isParetoOptimal (ι := Fin 2 × Fin 1)
      (ω := fun i => exampleEndow i.1) (t := fun i => exampleShare i.1)
      (fun i => by obtain ⟨a, b⟩ := i; fin_cases a <;> norm_num [exampleShare])
      (by simp [Fintype.sum_prod_type, exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
      (by simp [Fintype.sum_prod_type, exampleEndow, exampleShare, Fin.sum_univ_two]; norm_num)
  · refine (isIndividuallyRational_iff_exchange _ rfl hr hm (fun i l => (hst.2 i).1 l) hx).2 ?_
    intro i
    exact exampleAlloc_ir i.1

/-- **Figure 18.B.2** (MWG, p. 655), the bracketed identity: for a coalition of one consumer of
type 1 (consuming `x'₁`) and two of type 2 (each consuming `x'₂`) in a pure exchange economy, the
coalition's consumptions exactly exhaust its endowments iff `-2(x'₂ - ω₂) = x'₁ - ω₁`. -/
theorem figure_18_B_2_identity (x₁ x₂ ω₁ ω₂ : Fin L → ℝ) :
    x₁ + (2 : ℝ) • x₂ = ω₁ + (2 : ℝ) • ω₂ ↔ -(2 : ℝ) • (x₂ - ω₂) = x₁ - ω₁ := by
  constructor
  · intro h
    linear_combination (norm := module) (-1 : ℝ) • h
  · intro h
    linear_combination (norm := module) (-1 : ℝ) • h

/-- **Figure 18.B.2** (MWG, p. 655): the blocking consumptions of `figure_18_B_2` satisfy the
identity, with the roles of the types interchanged: `-2(x'₁ - ω₁) = x'₂ - ω₂`. -/
theorem figure_18_B_2_identity_instance :
    -(2 : ℝ) • (fig18B2Bundle (0, 0) - exampleEndow 0) = fig18B2Bundle (1, 0) - exampleEndow 1 := by
  funext l
  fin_cases l <;> simp [fig18B2Bundle, exampleEndow] <;> norm_num

end MWG.CoreFoundations
