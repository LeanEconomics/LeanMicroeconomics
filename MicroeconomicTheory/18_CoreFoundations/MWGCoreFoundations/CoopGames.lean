/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.CoreWalras
import MWGWelfareBargaining.Shapley

/-!
# Cooperative games: characteristic form and the core (MWG Appendix A, pp. 673-679)

Players are `Fin n` (`I = {1, ..., I}`), coalitions are nonempty `S : Finset (Fin n)`, and an
outcome is `u : Fin n → ℝ`.

**Representation of `ℝ^S`.** A subset `U^S ⊆ ℝ^S` is represented by the cylinder
`{u ∈ ℝ^I : u^S ∈ U^S}`, a set of outcomes whose membership depends only on the coordinates in
`S`. Definition 18.AA.1 is stated on such sets (`IsUtilityPossibilitySet`); the bridge
`isUtilityPossibilitySet_iff` proves that this is exactly the preimage, under the projection
`u ↦ u^S` (`projS`, with values in `S → ℝ`), of a nonempty, closed, comprehensive subset of
`S → ℝ`. With this representation the pair `(u^S, u^T)` of Definition 18.AA.3 is the outcome
that agrees with `u` on `S` and with `u'` elsewhere.

* Definitions 18.AA.1-18.AA.2: utility possibility sets, games in characteristic form
  (`NTUGame`, `IsCharacteristicForm`).
* **Example 18.AA.1** (`econGame`): comprehensive, nonempty, convex (`example_18_AA_1_convex`)
  and superadditive (`example_18_AA_1_superadditive`). **Correction**: `V(S)` need not be closed
  when `Y` is not closed (`example_18_AA_1_not_closed`: `L = 2`, one consumer,
  `Y = {y : y₁ < 0, y₂ < -y₁} ∪ {0}`, `ω = (1, 0)`, `u(x) = x₂`, `V = (-∞, 1)`); it is closed when
  `Y` is closed and contained in `-ℝ^L₊` (`example_18_AA_1_closed`; closed cones with no free
  production in `Closer18AA`).
* **Example 18.AA.2** (`votingGame`): a game in characteristic form, superadditive; with the
  values of Figure 18.AA.4, `V(I)` is not convex (`example_18_AA_2_not_convex`).
* Definition 18.AA.3 (superadditivity); TU games (Definition 18.AA.4, `tuSet` on Chapter 22's
  `Game`): utility possibility sets, superadditive iff `v` is (`tuSet_superadditive_iff`);
  **Example 18.AA.3** (`tuMajority`, the worths are the maximal total utilities).
* Definitions 18.AA.5-18.AA.6 (`ntuBlocks`, `ntuCore`), the TU specialisations
  (`tu_blocks_iff`, `ntuCore_tuSet`), **Exercise 18.AA.2**, **Example 18.AA.4** (both majority
  games have empty cores), **Example 18.AA.5** (the core of an economy and of its game),
  **Example 18.AA.6** and **Exercise 18.AA.3** (production games), **footnote 28**.

The Bondareva-Shapley theorem (Exercise 18.AA.1) is in `MWGCoreFoundations.Balanced`.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {n : ℕ}

/-! ### Outcomes, utility possibility sets, games in characteristic form -/

/-- **Appendix A** (MWG, p. 674). The projection `u^S = (uᵢ)_{i∈S} ∈ ℝ^S` of an outcome. -/
def projS (S : Finset (Fin n)) (u : Fin n → ℝ) : S → ℝ := fun i => u i

/-- **Definition 18.AA.1** (MWG, p. 674). A utility possibility set for the coalition `S`
(represented as a set of outcomes depending only on the coordinates in `S`): nonempty, closed
and comprehensive (`u ∈ U` and `u'^S ≤ u^S` imply `u' ∈ U`). -/
def IsUtilityPossibilitySet (S : Finset (Fin n)) (U : Set (Fin n → ℝ)) : Prop :=
  U.Nonempty ∧ IsClosed U ∧ ∀ u ∈ U, ∀ u' : Fin n → ℝ, (∀ i ∈ S, u' i ≤ u i) → u' ∈ U

/-- **Appendix A** (MWG, p. 674). The extension of `w ∈ ℝ^S` by zero outside `S`. -/
noncomputable def extS (S : Finset (Fin n)) (w : S → ℝ) : Fin n → ℝ := fun i => by
  classical
  exact if h : i ∈ S then w ⟨i, h⟩ else 0

/-- **Appendix A** (MWG, p. 674). `(ext_S w)^S = w`. -/
theorem projS_extS (S : Finset (Fin n)) (w : S → ℝ) : projS S (extS S w) = w := by
  funext i
  simp [projS, extS, i.2]

/-- **Appendix A** (MWG, p. 674). The projection `u ↦ u^S` is continuous. -/
theorem continuous_projS (S : Finset (Fin n)) : Continuous (projS S) :=
  continuous_pi fun i => continuous_apply (i : Fin n)

/-- **Appendix A** (MWG, p. 674). The extension by zero is continuous. -/
theorem continuous_extS (S : Finset (Fin n)) : Continuous (extS S) := by
  classical
  refine continuous_pi fun i => ?_
  by_cases h : i ∈ S
  · have : (fun w : S → ℝ => extS S w i) = fun w => w ⟨i, h⟩ := by
      funext w; simp [extS, h]
    rw [this]; exact continuous_apply _
  · have : (fun w : S → ℝ => extS S w i) = fun _ => 0 := by
      funext w; simp [extS, h]
    rw [this]; exact continuous_const

/-- **Definition 18.AA.1** (MWG, p. 674), bridge to `ℝ^S`: a set of outcomes is a utility
possibility set for `S` in our representation iff it is the preimage under `u ↦ u^S` of a
nonempty, closed, comprehensive subset of `ℝ^S = (S → ℝ)`. -/
theorem isUtilityPossibilitySet_iff (S : Finset (Fin n)) (U : Set (Fin n → ℝ)) :
    IsUtilityPossibilitySet S U ↔ ∃ W : Set (S → ℝ), W.Nonempty ∧ IsClosed W ∧
      (∀ w ∈ W, ∀ w' : S → ℝ, w' ≤ w → w' ∈ W) ∧ U = projS S ⁻¹' W := by
  constructor
  · rintro ⟨⟨u, hu⟩, hcl, hcomp⟩
    have hW : projS S '' U = extS S ⁻¹' U := by
      ext w
      constructor
      · rintro ⟨u', hu', rfl⟩
        refine hcomp u' hu' _ fun i hi => ?_
        simp [extS, projS, hi]
      · intro hw
        exact ⟨extS S w, hw, projS_extS S w⟩
    refine ⟨projS S '' U, ⟨projS S u, u, hu, rfl⟩, ?_, ?_, ?_⟩
    · rw [hW]; exact hcl.preimage (continuous_extS S)
    · rintro w ⟨u', hu', rfl⟩ w' hw'
      refine ⟨extS S w', hcomp u' hu' _ fun i hi => ?_, projS_extS S w'⟩
      have := hw' ⟨i, hi⟩
      simpa [extS, projS, hi] using this
    · ext u'
      constructor
      · intro h; exact ⟨u', h, rfl⟩
      · rintro ⟨u'', hu'', he⟩
        refine hcomp u'' hu'' u' fun i hi => ?_
        have := congrFun he ⟨i, hi⟩
        simp only [projS] at this
        rw [this]
  · rintro ⟨W, ⟨w, hw⟩, hcl, hcomp, rfl⟩
    refine ⟨⟨extS S w, by simp [projS_extS, hw]⟩, hcl.preimage (continuous_projS S), ?_⟩
    intro u hu u' hle
    exact hcomp _ hu _ fun i => hle i i.2

/-- **Definition 18.AA.2** (MWG, p. 675). A game in characteristic form `(I, V)`: a rule `V`
assigning to every coalition a set of payoffs (represented as in Definition 18.AA.1). -/
abbrev NTUGame (n : ℕ) := Finset (Fin n) → Set (Fin n → ℝ)

/-- **Definition 18.AA.2** (MWG, p. 675). `V(S)` is a utility possibility set for `S` for every
coalition `S`. -/
def IsCharacteristicForm (V : NTUGame n) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → IsUtilityPossibilitySet S (V S)

/-- **Definition 18.AA.3** (MWG, p. 676). Superadditivity: for disjoint coalitions `S, T`,
`u^S ∈ V(S)` and `u'^T ∈ V(T)` imply `(u^S, u'^T) ∈ V(S ∪ T)`. -/
def IsSuperadditive (V : NTUGame n) : Prop :=
  ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty → Disjoint S T → ∀ u u' : Fin n → ℝ,
    u ∈ V S → u' ∈ V T → (fun i => if i ∈ S then u i else u' i) ∈ V (S ∪ T)

/-! ### Example 18.AA.1: economies -/

variable {L : ℕ}

/-- **Example 18.AA.1** (MWG, p. 675). The game of an economy with utilities `uᵢ`, endowments
`ωᵢ` and the public technology `Y`: `V(S) = {(uᵢ(xᵢ))_{i∈S} : ∑_S xᵢ = ∑_S ωᵢ + y, y ∈ Y} - ℝ^S₊`
with `xᵢ ∈ ℝ^L₊`. -/
def econGame (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ) (Y : Set (Fin L → ℝ)) :
    NTUGame n := fun S =>
  {w | ∃ x : Fin n → Fin L → ℝ, (∀ i ∈ S, x i ∈ nonnegOrthant L) ∧
    (∃ y ∈ Y, ∑ i ∈ S, x i = ∑ i ∈ S, ω i + y) ∧ ∀ i ∈ S, w i ≤ u i (x i)}

/-- **Example 18.AA.1** (MWG, p. 675). `V(S)` is comprehensive. -/
theorem econGame_comprehensive (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ)
    (Y : Set (Fin L → ℝ)) (S : Finset (Fin n)) {w w' : Fin n → ℝ}
    (hw : w ∈ econGame u ω Y S) (hle : ∀ i ∈ S, w' i ≤ w i) : w' ∈ econGame u ω Y S := by
  obtain ⟨x, hx, hy, hu⟩ := hw
  exact ⟨x, hx, hy, fun i hi => (hle i hi).trans (hu i hi)⟩

/-- **Example 18.AA.1** (MWG, p. 675). `V(S)` is nonempty when `0 ∈ Y` and `ωᵢ ≥ 0`. -/
theorem econGame_nonempty (u : Fin n → (Fin L → ℝ) → ℝ) {ω : Fin n → Fin L → ℝ}
    {Y : Set (Fin L → ℝ)} (h0 : (0 : Fin L → ℝ) ∈ Y) (hω : ∀ i, ω i ∈ nonnegOrthant L)
    (S : Finset (Fin n)) : (econGame u ω Y S).Nonempty :=
  ⟨fun i => u i (ω i), ω, fun i _ => hω i, ⟨0, h0, by simp⟩, fun _ _ => le_rfl⟩

/-- **Example 18.AA.1** (MWG, p. 675; Exercise 16.E.2). With concave utilities on `ℝ^L₊` and a
convex technology, every `V(S)` is convex. -/
theorem example_18_AA_1_convex {u : Fin n → (Fin L → ℝ) → ℝ} (ω : Fin n → Fin L → ℝ)
    {Y : Set (Fin L → ℝ)} (hY : Convex ℝ Y) (hu : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (u i))
    (S : Finset (Fin n)) : Convex ℝ (econGame u ω Y S) := by
  rintro w₁ ⟨x₁, hx₁, ⟨y₁, hy₁, hs₁⟩, hu₁⟩ w₂ ⟨x₂, hx₂, ⟨y₂, hy₂, hs₂⟩, hu₂⟩ a b ha hb hab
  have hxS : ∀ i ∈ S, a • x₁ i + b • x₂ i ∈ nonnegOrthant L := fun i hi =>
    (hu i).1 (hx₁ i hi) (hx₂ i hi) ha hb hab
  refine ⟨a • x₁ + b • x₂, fun i hi => hxS i hi, ⟨a • y₁ + b • y₂, hY hy₁ hy₂ ha hb hab, ?_⟩,
    fun i hi => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, hs₁, hs₂]
    calc a • (∑ i ∈ S, ω i + y₁) + b • (∑ i ∈ S, ω i + y₂)
        = (a + b) • ∑ i ∈ S, ω i + (a • y₁ + b • y₂) := by module
      _ = ∑ i ∈ S, ω i + (a • y₁ + b • y₂) := by rw [hab, one_smul]
  · have hc := (hu i).2 (hx₁ i hi) (hx₂ i hi) ha hb hab
    simp only [smul_eq_mul] at hc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hu₁ i hi, hu₂ i hi]

/-- **Example 18.AA.1** (MWG, pp. 675-676). With a convex constant returns technology the game
of an economy is superadditive (the claim of p. 676). -/
theorem example_18_AA_1_superadditive (u : Fin n → (Fin L → ℝ) → ℝ) (ω : Fin n → Fin L → ℝ)
    {Y : Set (Fin L → ℝ)} (hY : IsCRSTechnology Y) : IsSuperadditive (econGame u ω Y) := by
  classical
  intro S T _ _ hST w w' ⟨x, hx, ⟨y, hy, hs⟩, hu⟩ ⟨x', hx', ⟨y', hy', hs'⟩, hu'⟩
  have hyy : y + y' ∈ Y := by
    have h := hY.1 hy hy' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have h2 := hY.2.2 _ h 2 (by norm_num)
    have e : (2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') = y + y' := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    rwa [e] at h2
  have hT : ∀ i ∈ T, i ∉ S := fun i hi hiS => Finset.disjoint_left.1 hST hiS hi
  refine ⟨fun i => if i ∈ S then x i else x' i, fun i hi => ?_, ⟨y + y', hyy, ?_⟩,
    fun i hi => ?_⟩
  · rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using hx i h
    · simpa [hT i h] using hx' i h
  · have e1 : ∑ i ∈ S, (if i ∈ S then x i else x' i) = ∑ i ∈ S, x i :=
      Finset.sum_congr rfl fun i hi => by simp [hi]
    have e2 : ∑ i ∈ T, (if i ∈ S then x i else x' i) = ∑ i ∈ T, x' i :=
      Finset.sum_congr rfl fun i hi => by simp [hT i hi]
    rw [Finset.sum_union hST, Finset.sum_union hST, e1, e2, hs, hs']
    abel
  · rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using hu i h
    · simpa [hT i h] using hu' i h

/-- **Example 18.AA.1** (MWG, p. 675), correction. The technology `{y : y₁ < 0, y₂ < -y₁} ∪ {0}` of
the correction to Example 18.AA.1. -/
def openConeTech : Set (Fin 2 → ℝ) := {y | y 0 < 0 ∧ y 1 < -y 0} ∪ {0}

/-- **Example 18.AA.1** (MWG, p. 675), correction. The technology `openConeTech` is a convex
constant returns technology (a convex cone). -/
theorem openConeTech_isCRS : IsCRSTechnology openConeTech := by
  refine ⟨?_, Or.inr rfl, ?_⟩
  · rintro a ha b hb s t hs ht hst
    simp only [openConeTech, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with ⟨ha0, ha1⟩ | rfl <;> rcases hb with ⟨hb0, hb1⟩ | rfl
    · left
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_lt_of_le hs with h | hs'
      · subst h
        have ht1 : t = 1 := by linarith
        subst ht1; constructor <;> linarith
      · have h1 := mul_pos hs' (neg_pos.2 ha0)
        have h2 := mul_pos hs' (by linarith : (0 : ℝ) < -(a 1 + a 0))
        have h3 := mul_nonneg ht (neg_pos.2 hb0).le
        have h4 := mul_nonneg ht (by linarith : (0 : ℝ) ≤ -(b 1 + b 0))
        constructor <;> nlinarith
    · rcases eq_or_lt_of_le hs with h | hs'
      · subst h; right; simp
      · left
        simp only [smul_zero, add_zero, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_pos hs' (neg_pos.2 ha0)
        have h2 := mul_pos hs' (by linarith : (0 : ℝ) < -(a 1 + a 0))
        constructor <;> nlinarith
    · rcases eq_or_lt_of_le ht with h | ht'
      · subst h; right; simp
      · left
        simp only [smul_zero, zero_add, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_pos ht' (neg_pos.2 hb0)
        have h2 := mul_pos ht' (by linarith : (0 : ℝ) < -(b 1 + b 0))
        constructor <;> nlinarith
    · right; simp
  · intro y hy t ht
    simp only [openConeTech, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hy ⊢
    rcases hy with ⟨h0, h1⟩ | rfl
    · rcases eq_or_lt_of_le ht with h | ht'
      · subst h; right; simp
      · left
        simp only [Pi.smul_apply, smul_eq_mul]
        have h2 := mul_pos ht' (by linarith : (0 : ℝ) < -(y 1 + y 0))
        constructor <;> nlinarith
    · right; simp

/-- **Example 18.AA.1** (MWG, p. 675), correction: `V(S)` need not be closed. With `L = 2`, one
consumer with `ω = (1, 0)` and the continuous, increasing, concave utility `u(x) = x₂`, and the
convex constant returns technology `openConeTech`, `V(I) = {w : w₁ < 1}`, which is not closed. -/
theorem example_18_AA_1_not_closed :
    econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech Finset.univ =
      {w | w 0 < 1} ∧
    ¬ IsClosed (econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech
      Finset.univ) := by
  have hV : econGame (n := 1) (fun _ x => x 1) (fun _ => ![1, 0]) openConeTech Finset.univ =
      {w | w 0 < 1} := by
    ext w
    simp only [econGame, Finset.mem_univ, true_implies, Fin.sum_univ_one, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, ⟨y, hy, hs⟩, hu⟩
      have h0 := congrFun hs 0
      have h1 := congrFun hs 1
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hx0 := hx 0 0
      have hw := hu 0
      rcases hy with ⟨hy0, hy1⟩ | hy
      · linarith
      · rw [Set.mem_singleton_iff] at hy; subst hy
        simp only [Pi.zero_apply] at h1; linarith
    · intro hw
      refine ⟨fun _ => ![0, max (w 0) 0], fun _ l => ?_, ⟨![-1, max (w 0) 0], Or.inl ⟨?_, ?_⟩,
        ?_⟩, fun _ => ?_⟩
      · fin_cases l <;> simp
      · simp
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [max_lt_iff]; constructor <;> norm_num [hw]
      · funext l; fin_cases l <;> simp
      · rename_i j; fin_cases j; simp
  refine ⟨hV, fun hcl => ?_⟩
  rw [hV] at hcl
  have hc : IsClosed (Set.Iio (1 : ℝ)) := by
    have : Set.Iio (1 : ℝ) = (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' {w | w 0 < 1} := by
      ext t; simp
    rw [this]; exact hcl.preimage (continuous_pi fun _ => continuous_id)
  have := hc.closure_eq
  rw [closure_Iio] at this
  have h1 : (1 : ℝ) ∈ Set.Iic (1 : ℝ) := Set.mem_Iic.2 le_rfl
  rw [this] at h1
  exact lt_irrefl _ (Set.mem_Iio.1 h1)

open Filter Topology in
/-- **Example 18.AA.1** (MWG, p. 675), corrected closedness: if the technology `Y` is closed and
contained in `-ℝ^L₊` (e.g. pure exchange, `Y = -ℝ^L₊`) and the utilities are continuous on
`ℝ^L₊`, then every `V(S)` is closed (the feasible consumptions lie in a compact box). -/
theorem example_18_AA_1_closed {u : Fin n → (Fin L → ℝ) → ℝ} {ω : Fin n → Fin L → ℝ}
    {Y : Set (Fin L → ℝ)} (hYc : IsClosed Y) (hYneg : Y ⊆ nonposOrthant L)
    (hu : ∀ i, ContinuousOn (u i) (nonnegOrthant L)) (S : Finset (Fin n)) :
    IsClosed (econGame u ω Y S) := by
  classical
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨ws, hws, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose x hx hy hux using hws
  choose y hyY hsum using hy
  set M : Fin n → Fin L → ℝ := fun _ => ∑ j ∈ S, ω j with hM
  set xt : ℕ → Fin n → Fin L → ℝ := fun k i => if i ∈ S then x k i else 0 with hxt
  have hxtS : ∀ k, ∀ i ∈ S, xt k i = x k i := fun k i hi => by simp [hxt, hi]
  have hbox : ∀ k, xt k ∈ Set.Icc (0 : Fin n → Fin L → ℝ) M := by
    intro k
    refine ⟨fun i l => ?_, fun i l => ?_⟩
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]; exact hx k i hi l
      · simp [hxt, hi]
    · by_cases hi : i ∈ S
      · rw [hxtS k i hi]
        have h1 : x k i l ≤ ∑ j ∈ S, x k j l :=
          Finset.single_le_sum (f := fun j => x k j l) (fun j hj => hx k j hj l) hi
        have h2 := congrFun (hsum k) l
        simp only [Finset.sum_apply, Pi.add_apply] at h2
        have h3 := hYneg (hyY k) l
        simp only [hM, Finset.sum_apply]
        linarith
      · simp only [hxt, hi, ↓reduceIte, hM, Pi.zero_apply, Finset.sum_apply]
        have h2 := congrFun (hsum k) l
        have h3 := hYneg (hyY k) l
        have h4 : 0 ≤ ∑ j ∈ S, x k j l := Finset.sum_nonneg fun j hj => hx k j hj l
        simp only [Finset.sum_apply, Pi.add_apply] at h2
        linarith
  obtain ⟨xb, hxb, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hbox
  have hcoord : ∀ i, Tendsto (fun k => xt (φ k) i) atTop (𝓝 (xb i)) :=
    fun i => tendsto_pi_nhds.1 hconv i
  have hxbnn : ∀ i, xb i ∈ nonnegOrthant L := fun i l => hxb.1 i l
  refine ⟨xb, fun i _ => hxbnn i, ⟨∑ i ∈ S, xb i - ∑ i ∈ S, ω i, ?_, by abel⟩, fun i hi => ?_⟩
  · refine hYc.mem_of_tendsto (f := fun k => y (φ k)) (b := atTop) ?_
      (Eventually.of_forall fun k => hyY _)
    have hy' : (fun k => y (φ k)) = fun k => ∑ i ∈ S, xt (φ k) i - ∑ i ∈ S, ω i := by
      funext k
      rw [Finset.sum_congr rfl fun i hi => hxtS (φ k) i hi, hsum (φ k)]
      abel
    rw [hy']
    exact (tendsto_finsetSum S fun i _ => hcoord i).sub tendsto_const_nhds
  · have hwl : Tendsto (fun k => ws (φ k) i) atTop (𝓝 (w i)) :=
      (tendsto_pi_nhds.1 hlim i).comp hφ.tendsto_atTop
    have hul : Tendsto (fun k => u i (xt (φ k) i)) atTop (𝓝 (u i (xb i))) :=
      ((hu i) (xb i) (hxbnn i)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hcoord i, Eventually.of_forall fun k l =>
          (hbox (φ k)).1 i l⟩)
    refine le_of_tendsto_of_tendsto hwl hul (Eventually.of_forall fun k => ?_)
    simp only [hxtS (φ k) i hi]
    exact hux (φ k) i hi

/-! ### Example 18.AA.2: majority voting -/

/-- **Example 18.AA.2** (MWG, p. 675). Majority voting among three players over the alternatives
`A` with payoffs `uᵢ(a)`: a coalition of at least two players can select any alternative,
`V(S) = {(uᵢ(a))_{i∈S} : a ∈ A} - ℝ^S₊`, and a single player can only withdraw, `V({i}) = -ℝ₊`. -/
def votingGame {A : Type*} (u : A → Fin 3 → ℝ) : NTUGame 3 := fun S =>
  if 2 ≤ S.card then {w | ∃ a, ∀ i ∈ S, w i ≤ u a i} else {w | ∀ i ∈ S, w i ≤ 0}

/-- **Example 18.AA.2** (MWG, p. 675). With finitely many alternatives (and at least one), the
majority voting game is a game in characteristic form. -/
theorem votingGame_isCharacteristicForm {A : Type*} [Finite A] [Nonempty A]
    (u : A → Fin 3 → ℝ) : IsCharacteristicForm (votingGame u) := by
  intro S _
  unfold votingGame
  split_ifs with h
  · refine ⟨⟨u (Classical.arbitrary A), Classical.arbitrary A, fun _ _ => le_rfl⟩, ?_, ?_⟩
    · have : {w : Fin 3 → ℝ | ∃ a, ∀ i ∈ S, w i ≤ u a i} =
          ⋃ a, ⋂ i ∈ S, {w | w i ≤ u a i} := by
        ext w; simp
      rw [this]
      exact isClosed_iUnion_of_finite fun a => isClosed_biInter fun i _ =>
        isClosed_le (continuous_apply i) continuous_const
    · rintro w ⟨a, ha⟩ w' hw'
      exact ⟨a, fun i hi => (hw' i hi).trans (ha i hi)⟩
  · refine ⟨⟨0, fun _ _ => le_rfl⟩, ?_, ?_⟩
    · have : {w : Fin 3 → ℝ | ∀ i ∈ S, w i ≤ 0} = ⋂ i ∈ S, {w | w i ≤ 0} := by
        ext w; simp
      rw [this]
      exact isClosed_biInter fun i _ => isClosed_le (continuous_apply i) continuous_const
    · intro w hw w' hw' i hi
      exact (hw' i hi).trans (hw i hi)

/-- **Definition 18.AA.3** (MWG, p. 676). The majority voting game of Example 18.AA.2 is
superadditive (nonnegative payoffs `uᵢ(a) ≥ 0`, at least one alternative). -/
theorem votingGame_superadditive {A : Type*} [Nonempty A] {u : A → Fin 3 → ℝ}
    (hu : ∀ a i, 0 ≤ u a i) : IsSuperadditive (votingGame u) := by
  classical
  intro S T hS hT hST w w' hw hw'
  have hcard : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  have hle : (S ∪ T).card ≤ 3 := by simpa using Finset.card_le_univ (S ∪ T)
  have hS1 := hS.card_pos
  have hT1 := hT.card_pos
  have hU : 2 ≤ (S ∪ T).card := by omega
  have hTS : ∀ i ∈ T, i ∉ S := fun i hi hiS => Finset.disjoint_left.1 hST hiS hi
  simp only [votingGame, hU, ↓reduceIte] at hw hw' ⊢
  by_cases h2S : 2 ≤ S.card
  · have h1T : ¬ 2 ≤ T.card := by omega
    simp only [h2S, h1T, ↓reduceIte] at hw hw'
    obtain ⟨a, ha⟩ := hw
    refine ⟨a, fun i hi => ?_⟩
    rcases Finset.mem_union.1 hi with h | h
    · simpa [h] using ha i h
    · simpa [hTS i h] using (hw' i h).trans (hu a i)
  · simp only [h2S, ↓reduceIte] at hw
    by_cases h2T : 2 ≤ T.card
    · simp only [h2T, ↓reduceIte] at hw'
      obtain ⟨a, ha⟩ := hw'
      refine ⟨a, fun i hi => ?_⟩
      rcases Finset.mem_union.1 hi with h | h
      · simpa [h] using (hw i h).trans (hu a i)
      · simpa [hTS i h] using ha i h
    · simp only [h2T, ↓reduceIte] at hw'
      refine ⟨Classical.arbitrary A, fun i hi => ?_⟩
      rcases Finset.mem_union.1 hi with h | h
      · simpa [h] using (hw i h).trans (hu _ i)
      · simpa [hTS i h] using (hw' i h).trans (hu _ i)

/-- **Figure 18.AA.4** (MWG, pp. 675-676). The payoffs of the three alternatives:
`u(a₁) = (2, 1, 0)`, `u(a₂) = (1, 0, 2)`, `u(a₃) = (0, 2, 1)`. -/
def votingPayoffs : Fin 3 → Fin 3 → ℝ := ![![2, 1, 0], ![1, 0, 2], ![0, 2, 1]]

/-- **Example 18.AA.2** (MWG, p. 676). With the values of Figure 18.AA.4, `V(I)` is not convex:
the midpoint of `u(a₁)` and `u(a₃)` is not dominated by any `u(a)`. -/
theorem example_18_AA_2_not_convex : ¬ Convex ℝ (votingGame votingPayoffs Finset.univ) := by
  intro hc
  have h1 : votingPayoffs 0 ∈ votingGame votingPayoffs Finset.univ := by
    simp only [votingGame, Finset.card_univ, Fintype.card_fin]
    exact ⟨0, fun _ _ => le_rfl⟩
  have h3 : votingPayoffs 2 ∈ votingGame votingPayoffs Finset.univ := by
    simp only [votingGame, Finset.card_univ, Fintype.card_fin]
    exact ⟨2, fun _ _ => le_rfl⟩
  have hm := hc h1 h3 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [votingGame, Finset.card_univ, Fintype.card_fin] at hm
  obtain ⟨a, ha⟩ := hm
  have e0 := ha 0 (Finset.mem_univ _)
  have e1 := ha 1 (Finset.mem_univ _)
  have e2 := ha 2 (Finset.mem_univ _)
  fin_cases a <;> simp [votingPayoffs] at e0 e1 e2 <;> linarith

/-! ### Transferable utility games -/

/-- **Definition 18.AA.4** (MWG, p. 676). The utility possibility set of a TU game with
characteristic function `v` (Chapter 22's `Game`): `V(S) = {u^S : ∑_{i∈S} uᵢ ≤ v(S)}`. -/
def tuSet (v : WelfareBargaining.Game n) : NTUGame n := fun S => {w | ∑ i ∈ S, w i ≤ v S}

/-- **Definition 18.AA.4** (MWG, p. 676). The sets of a TU game are utility possibility sets: the
TU game is a game in characteristic form. -/
theorem tuSet_isCharacteristicForm (v : WelfareBargaining.Game n) :
    IsCharacteristicForm (tuSet v) := by
  intro S hS
  refine ⟨⟨fun _ => v S / S.card, ?_⟩, ?_, ?_⟩
  · have : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
    simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ this]
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  · intro w hw w' hle
    exact (Finset.sum_le_sum hle).trans hw

/-- **Definitions 18.AA.3-18.AA.4** (MWG, p. 676). A TU game is superadditive in the sense of
Definition 18.AA.3 iff `v(S) + v(T) ≤ v(S ∪ T)` for disjoint coalitions `S, T`. -/
theorem tuSet_superadditive_iff (v : WelfareBargaining.Game n) :
    IsSuperadditive (tuSet v) ↔ ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty →
      Disjoint S T → v S + v T ≤ v (S ∪ T) := by
  classical
  have hTS : ∀ {S T : Finset (Fin n)}, Disjoint S T → ∀ i ∈ T, i ∉ S :=
    fun hST i hi hiS => Finset.disjoint_left.1 hST hiS hi
  have hsplit : ∀ {S T : Finset (Fin n)}, Disjoint S T → ∀ u u' : Fin n → ℝ,
      ∑ i ∈ S ∪ T, (if i ∈ S then u i else u' i) = ∑ i ∈ S, u i + ∑ i ∈ T, u' i := by
    intro S T hST u u'
    rw [Finset.sum_union hST]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by simp [hi]
    · exact Finset.sum_congr rfl fun i hi => by simp [hTS hST i hi]
  constructor
  · intro h S T hS hT hST
    have hcS : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
    have hcT : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
    have hu : (fun _ => v S / S.card) ∈ tuSet v S := by
      simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hcS]
    have hu' : (fun _ => v T / T.card) ∈ tuSet v T := by
      simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hcT]
    have := h S T hS hT hST _ _ hu hu'
    simp only [tuSet, Set.mem_ofPred_eq] at this
    rw [hsplit hST] at this
    simp only [Finset.sum_const, nsmul_eq_mul] at this
    rwa [mul_div_cancel₀ _ hcS, mul_div_cancel₀ _ hcT] at this
  · intro h S T hS hT hST u u' hu hu'
    simp only [tuSet, Set.mem_ofPred_eq] at hu hu' ⊢
    rw [hsplit hST]
    linarith [h S T hS hT hST]

/-- **Example 18.AA.3** (MWG, p. 677). TU majority voting: `v(I) = 3`, `v(S) = 3` for pairs and
`v({i}) = 0`. -/
def tuMajority : WelfareBargaining.Game 3 := fun S => if 2 ≤ S.card then 3 else 0

/-- **Example 18.AA.3** (MWG, pp. 676-677). With the values of Figure 18.AA.4 and freely
transferable utility, the worth of every coalition with at least two members is the maximal
total utility `max_a ∑_{i∈S} uᵢ(a)` it can obtain, and `v({i}) = 0`. -/
theorem example_18_AA_3 :
    (∀ S : Finset (Fin 3), 2 ≤ S.card →
      IsGreatest (Set.range fun a => ∑ i ∈ S, votingPayoffs a i) (tuMajority S)) ∧
    ∀ i : Fin 3, tuMajority {i} = 0 := by
  refine ⟨fun S hS => ?_, fun i => by simp [tuMajority]⟩
  have hcases : S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = Finset.univ := by
    revert S; decide
  have hv : tuMajority S = 3 := by simp [tuMajority, hS]
  rw [hv]
  rcases hcases with rfl | rfl | rfl | rfl
  · refine ⟨⟨0, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨1, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨2, by simp [votingPayoffs]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs] <;> norm_num
  · refine ⟨⟨0, by simp [votingPayoffs, Fin.sum_univ_three]; norm_num⟩, ?_⟩
    rintro _ ⟨a, rfl⟩; fin_cases a <;> simp [votingPayoffs, Fin.sum_univ_three] <;> norm_num

/-! ### Blocking and the core -/

/-- **Definition 18.AA.5** (MWG, p. 678). The outcome `u` is blocked (improved upon) by the
coalition `S` if some `u' ∈ V(S)` has `uᵢ < u'ᵢ` for all `i ∈ S`. -/
def ntuBlocks (V : NTUGame n) (S : Finset (Fin n)) (u : Fin n → ℝ) : Prop :=
  S.Nonempty ∧ ∃ u' ∈ V S, ∀ i ∈ S, u i < u' i

/-- **Definition 18.AA.6** (MWG, p. 678). The core: the outcomes feasible for the grand
coalition (`u ∈ V(I)`) that no coalition blocks. -/
def ntuCore (V : NTUGame n) : Set (Fin n → ℝ) :=
  {u | u ∈ V Finset.univ ∧ ∀ S, ¬ ntuBlocks V S u}

/-- **Appendix A** (MWG, p. 678). The core of a TU game:
`∑_{i∈S} uᵢ ≥ v(S)` for every coalition `S` and `∑_{i∈I} uᵢ ≤ v(I)`. -/
def tuCore (v : WelfareBargaining.Game n) : Set (Fin n → ℝ) :=
  {u | (∀ S : Finset (Fin n), S.Nonempty → v S ≤ ∑ i ∈ S, u i) ∧ ∑ i, u i ≤ v Finset.univ}

/-- **Definition 18.AA.5** (MWG, p. 678), TU case: `u` is blocked by `S` iff
`∑_{i∈S} uᵢ < v(S)`. -/
theorem tu_blocks_iff (v : WelfareBargaining.Game n) (S : Finset (Fin n)) (u : Fin n → ℝ) :
    ntuBlocks (tuSet v) S u ↔ S.Nonempty ∧ ∑ i ∈ S, u i < v S := by
  constructor
  · rintro ⟨hS, u', hu', hlt⟩
    exact ⟨hS, (Finset.sum_lt_sum_of_nonempty hS hlt).trans_le hu'⟩
  · rintro ⟨hS, hlt⟩
    have hc : (0 : ℝ) < S.card := Nat.cast_pos.2 hS.card_pos
    set δ := (v S - ∑ i ∈ S, u i) / S.card with hδ
    have hδpos : 0 < δ := div_pos (by linarith) hc
    refine ⟨hS, fun i => u i + δ, ?_, fun i _ => by linarith⟩
    simp only [tuSet, Set.mem_ofPred_eq, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, hδ]
    rw [mul_div_cancel₀ _ hc.ne']
    linarith

/-- **Definition 18.AA.6** (MWG, p. 678), TU case: the core of the TU game is the set of
`u` with `∑_{i∈S} uᵢ ≥ v(S)` for all `S` and `∑_{i∈I} uᵢ ≤ v(I)`. -/
theorem ntuCore_tuSet (v : WelfareBargaining.Game n) : ntuCore (tuSet v) = tuCore v := by
  ext u
  simp only [ntuCore, tuCore, Set.mem_ofPred_eq, tu_blocks_iff, tuSet, not_and, not_lt]
  exact ⟨fun h => ⟨fun S hS => h.2 S hS, h.1⟩, fun h => ⟨h.2, fun S hS => h.1 S hS⟩⟩

/-- **Exercise 18.AA.2** (MWG, p. 678). A TU game with a nonempty core satisfies
`v(S) + v(T) ≤ v(I)` for every partition of `I` into two coalitions `S, T`. -/
theorem exercise_18_AA_2 {v : WelfareBargaining.Game n} (hcore : (tuCore v).Nonempty)
    {S T : Finset (Fin n)} (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T)
    (hU : S ∪ T = Finset.univ) : v S + v T ≤ v Finset.univ := by
  obtain ⟨u, hu, htot⟩ := hcore
  have h := Finset.sum_union hST (f := u)
  rw [hU] at h
  linarith [hu S hS, hu T hT]

/-- **Example 18.AA.4** (MWG, p. 678). The TU majority voting game has an empty core: if
`u₁ + u₂ + u₃ ≤ 3` then some pair gets less than `3`. -/
theorem example_18_AA_4_tu : tuCore tuMajority = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hS, htot⟩
  have h01 := hS {0, 1} (by simp)
  have h02 := hS {0, 2} (by simp)
  have h12 := hS {1, 2} (by simp)
  simp [tuMajority, Fin.sum_univ_three] at h01 h02 h12 htot
  linarith

/-- **Example 18.AA.4** (MWG, p. 678). The majority voting game of Figure 18.AA.4 has an empty
core: `(2, 1, 0)`, `(1, 0, 2)`, `(0, 2, 1)` (and everything below them) are blocked by `{2, 3}`
using `a₃`, `{1, 2}` using `a₁` and `{1, 3}` using `a₂` (the Condorcet paradox). -/
theorem example_18_AA_4_ntu : ntuCore (votingGame votingPayoffs) = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hu, hnb⟩
  simp only [votingGame, Finset.card_univ, Fintype.card_fin] at hu
  obtain ⟨a, ha⟩ := hu
  have e0 := ha 0 (Finset.mem_univ _)
  have e1 := ha 1 (Finset.mem_univ _)
  have e2 := ha 2 (Finset.mem_univ _)
  fin_cases a
  · apply hnb {1, 2}
    refine ⟨by simp, votingPayoffs 2, ?_, ?_⟩
    · have hc : 2 ≤ ({1, 2} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨2, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith
  · apply hnb {0, 1}
    refine ⟨by simp, votingPayoffs 0, ?_, ?_⟩
    · have hc : 2 ≤ ({0, 1} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨0, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith
  · apply hnb {0, 2}
    refine ⟨by simp, votingPayoffs 1, ?_, ?_⟩
    · have hc : 2 ≤ ({0, 2} : Finset (Fin 3)).card := by decide
      simp only [votingGame, hc, ↓reduceIte]
      exact ⟨1, fun _ _ => le_rfl⟩
    · simp [votingPayoffs] at e0 e1 e2 ⊢; constructor <;> linarith

/-! ### Example 18.AA.5: economies again -/

/-- **Example 18.AA.5** (MWG, pp. 678-679). For an economy of Section 18.B whose preferences are
represented by utilities `Uᵢ`, a feasible allocation `x` has the core property iff its utility
vector `(Uᵢ(xᵢ))ᵢ` is in the core of the game of Example 18.AA.1: the two notions of the core
coincide. -/
theorem example_18_AA_5 (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) (x : Fin n → Fin L → ℝ) :
    x ∈ E.core ↔ E.IsFeasible x ∧ (fun i => U i (x i)) ∈ ntuCore (econGame U E.ω E.Y) := by
  constructor
  · rintro ⟨hfeas, hnb⟩
    obtain ⟨hx0, y, hy, hsum⟩ := hfeas
    refine ⟨⟨hx0, y, hy, hsum⟩, ⟨x, fun i _ => hx0 i, ⟨y, hy, by rw [hsum, add_comm]⟩,
      fun _ _ => le_rfl⟩, ?_⟩
    rintro S ⟨hS, w, ⟨x', hx', ⟨y', hy', hs'⟩, hu'⟩, hlt⟩
    refine hnb S ⟨hS, x', fun i hi => ⟨hx' i hi, ?_⟩, y', hy', by rw [hs', add_comm]⟩
    rw [hpref i]
    have h := (hlt i hi).trans_le (hu' i hi)
    exact ⟨h.le, not_le.2 h⟩
  · rintro ⟨hfeas, _, hnb⟩
    refine ⟨hfeas, fun S ⟨hS, x', hx', y', hy', hs'⟩ => hnb S ⟨hS, fun i => U i (x' i),
      ⟨x', fun i hi => (hx' i hi).1, ⟨y', hy', by rw [hs', add_comm]⟩, fun _ _ => le_rfl⟩,
      fun i hi => ?_⟩⟩
    have h := (hx' i hi).2
    rw [hpref i] at h
    exact not_le.1 h.2

/-- **Example 18.AA.5** (MWG, p. 678). Conversely, every core outcome of the game of the economy
is dominated by the utility vector of an allocation with the core property. -/
theorem example_18_AA_5_game_core (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) {w : Fin n → ℝ}
    (hw : w ∈ ntuCore (econGame U E.ω E.Y)) : ∃ x ∈ E.core, ∀ i, w i ≤ U i (x i) := by
  obtain ⟨⟨x, hx0, ⟨y, hy, hsum⟩, hux⟩, hnb⟩ := hw
  refine ⟨x, ?_, fun i => hux i (Finset.mem_univ i)⟩
  refine ⟨⟨fun i => hx0 i (Finset.mem_univ i), y, hy, by rw [hsum, add_comm]⟩, ?_⟩
  rintro S ⟨hS, x', hx', y', hy', hs'⟩
  refine hnb S ⟨hS, fun i => U i (x' i), ⟨x', fun i hi => (hx' i hi).1,
    ⟨y', hy', by rw [hs', add_comm]⟩, fun _ _ => le_rfl⟩, fun i hi => ?_⟩
  have h := (hx' i hi).2
  rw [hpref i] at h
  exact (hux i (Finset.mem_univ i)).trans_lt (not_le.1 h.2)

/-- **Example 18.AA.5** (MWG, p. 679). If a Walrasian equilibrium exists then the core of the
game of the economy is nonempty (Proposition 18.B.1, for a convex constant returns
technology). -/
theorem example_18_AA_5_walras (E : CoreEconomy (Fin n) L) (U : Fin n → (Fin L → ℝ) → ℝ)
    (hpref : ∀ i, E.pref i = utilityPref (U i)) (hY : IsCRSTechnology E.Y)
    {x : Fin n → Fin L → ℝ} {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    (ntuCore (econGame U E.ω E.Y)).Nonempty :=
  ⟨_, ((example_18_AA_5 E U hpref x).1 (proposition_18_B_1 E hY h)).2⟩

/-! ### Example 18.AA.6: single-input production games -/

/-- **Example 18.AA.6** (MWG, p. 679). The TU game of a one-input technology `f`:
`v(S) = f(∑_{i∈S} ωᵢ)`. -/
def prodGame (f : ℝ → ℝ) (ω : Fin n → ℝ) : WelfareBargaining.Game n :=
  fun S => f (∑ i ∈ S, ω i)

/-- **Example 18.AA.6** (MWG, p. 679). The proportional distribution of output:
`u_h = ω_h / (∑_{i∈I} ωᵢ) · f(∑_{i∈I} ωᵢ)`. -/
noncomputable def propAlloc (f : ℝ → ℝ) (ω : Fin n → ℝ) : Fin n → ℝ :=
  fun h => ω h / (∑ i, ω i) * f (∑ i, ω i)

/-- **Example 18.AA.6** (MWG, p. 679). `∑_{h∈S} u_h = (∑_{h∈S} ω_h)/(∑_{i∈I} ωᵢ) · f(∑_{i∈I} ωᵢ)`.
-/
theorem propAlloc_sum (f : ℝ → ℝ) (ω : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ h ∈ S, propAlloc f ω h = (∑ h ∈ S, ω h) / (∑ i, ω i) * f (∑ i, ω i) := by
  simp only [propAlloc, ← Finset.sum_mul, ← Finset.sum_div]

/-- **Example 18.AA.6** (MWG, p. 679). If `f(0) = 0` and the average product `f(z)/z` is
nondecreasing on `z > 0`, the proportional allocation is in the core (`ωᵢ ≥ 0`). -/
theorem example_18_AA_6 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hf0 : f 0 = 0) (hω : ∀ i, 0 ≤ ω i)
    (hmono : MonotoneOn (fun z => f z / z) (Set.Ioi 0)) :
    propAlloc f ω ∈ tuCore (prodGame f ω) := by
  have hZ : 0 ≤ ∑ i, ω i := Finset.sum_nonneg fun i _ => hω i
  refine ⟨fun S _ => ?_, ?_⟩
  · rw [propAlloc_sum]
    simp only [prodGame]
    have hzS : 0 ≤ ∑ i ∈ S, ω i := Finset.sum_nonneg fun i _ => hω i
    have hle : ∑ i ∈ S, ω i ≤ ∑ i, ω i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hω i
    rcases eq_or_lt_of_le hzS with h | h
    · rw [← h, hf0]; simp
    · have hZpos : 0 < ∑ i, ω i := h.trans_le hle
      have hm := hmono h hZpos hle
      simp only at hm
      rw [div_le_div_iff₀ h hZpos] at hm
      rw [div_mul_eq_mul_div, le_div_iff₀ hZpos]
      linarith
  · rw [propAlloc_sum]
    simp only [prodGame]
    rcases eq_or_lt_of_le hZ with h | h
    · rw [← h, hf0]; simp
    · rw [div_self h.ne', one_mul]

/-- **Example 18.AA.6** (MWG, p. 679), bracketed claim: if `f` is convex on `ℝ₊` with
`f(0) = 0` then the average product `f(z)/z` is nondecreasing on `z > 0`. -/
theorem example_18_AA_6_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0) :
    MonotoneOn (fun z => f z / z) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hm := hf.slope_mono (x := 0) h0 (by simpa using ha') (by simpa using hb') hab
  simpa [slope_def_field, hf0] using hm

/-- **Exercise 18.AA.3** (MWG, p. 685). If the average product is constant (`f(z)/z = c` for
`z > 0`, `f(0) = 0`) then the proportional allocation is the only allocation in the core. -/
theorem exercise_18_AA_3 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hf0 : f 0 = 0) (hω : ∀ i, 0 ≤ ω i)
    {c : ℝ} (hc : ∀ z, 0 < z → f z / z = c) : tuCore (prodGame f ω) = {propAlloc f ω} := by
  have hlin : ∀ z, 0 ≤ z → f z = c * z := by
    intro z hz
    rcases eq_or_lt_of_le hz with h | h
    · rw [← h, hf0, mul_zero]
    · have := hc z h; field_simp at this; linarith
  have hZ : 0 ≤ ∑ i, ω i := Finset.sum_nonneg fun i _ => hω i
  have hprop : ∀ h, propAlloc f ω h = c * ω h := by
    intro h
    simp only [propAlloc]
    rcases eq_or_lt_of_le hZ with hz | hz
    · have h0 : ω h = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hω i).1 hz.symm h
        (Finset.mem_univ h)
      rw [h0]; simp
    · rw [hlin _ hZ]; field_simp
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hS, htot⟩
    have hi : ∀ h, c * ω h ≤ u h := by
      intro h
      have := hS {h} (Finset.singleton_nonempty h)
      simpa [prodGame, hlin _ (hω h)] using this
    have htot' : ∑ h, (u h - c * ω h) ≤ 0 := by
      simp only [prodGame, hlin _ hZ] at htot
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => sub_nonneg.2 (hi h)).1
      (le_antisymm htot' (Finset.sum_nonneg fun h _ => sub_nonneg.2 (hi h)))
    funext h
    rw [hprop h]
    linarith [hzero h (Finset.mem_univ h)]
  · rintro rfl
    refine example_18_AA_6 hf0 hω fun a ha b hb _ => ?_
    simp only
    rw [hc a ha, hc b hb]

/-- **Footnote 28** (MWG, p. 679). With strictly decreasing returns (`f(z)/z` strictly decreasing
on `z > 0`) and positive endowments, `v(S) + v(T) > v(I)` for every partition of `I` into two
coalitions `S, T`. -/
theorem footnote_18_28 {f : ℝ → ℝ} {ω : Fin n → ℝ} (hω : ∀ i, 0 < ω i)
    (hanti : StrictAntiOn (fun z => f z / z) (Set.Ioi 0)) {S T : Finset (Fin n)}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T) (hU : S ∪ T = Finset.univ) :
    prodGame f ω Finset.univ < prodGame f ω S + prodGame f ω T := by
  simp only [prodGame]
  have hzS : 0 < ∑ i ∈ S, ω i := Finset.sum_pos (fun i _ => hω i) hS
  have hzT : 0 < ∑ i ∈ T, ω i := Finset.sum_pos (fun i _ => hω i) hT
  have hZ : ∑ i, ω i = ∑ i ∈ S, ω i + ∑ i ∈ T, ω i := by
    rw [← Finset.sum_union hST, hU]
  have hZpos : 0 < ∑ i, ω i := by rw [hZ]; linarith
  have h1 := hanti (show (0 : ℝ) < ∑ i ∈ S, ω i from hzS) (show (0 : ℝ) < ∑ i, ω i from hZpos)
    (by rw [hZ]; linarith)
  have h2 := hanti (show (0 : ℝ) < ∑ i ∈ T, ω i from hzT) (show (0 : ℝ) < ∑ i, ω i from hZpos)
    (by rw [hZ]; linarith)
  simp only at h1 h2
  rw [div_lt_div_iff₀ hZpos hzS] at h1
  rw [div_lt_div_iff₀ hZpos hzT] at h2
  have key : f (∑ i, ω i) * (∑ i, ω i) <
      (f (∑ i ∈ S, ω i) + f (∑ i ∈ T, ω i)) * (∑ i, ω i) := by
    have e : f (∑ i, ω i) * (∑ i, ω i) =
        f (∑ i, ω i) * (∑ i ∈ S, ω i) + f (∑ i, ω i) * (∑ i ∈ T, ω i) := by rw [hZ]; ring
    rw [e]; nlinarith
  exact lt_of_mul_lt_mul_right key hZpos.le

/-- **Footnote 28** (MWG, p. 679). Hence, with at least two players, the core is empty
(Exercise 18.AA.2). -/
theorem footnote_18_28_core_empty {f : ℝ → ℝ} {ω : Fin n → ℝ} (hn : 2 ≤ n)
    (hω : ∀ i, 0 < ω i) (hanti : StrictAntiOn (fun z => f z / z) (Set.Ioi 0)) :
    tuCore (prodGame f ω) = ∅ := by
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  have hab : b ≠ a := by simp [a, b, Fin.ext_iff]
  have hT : (Finset.univ.erase a).Nonempty := ⟨b, Finset.mem_erase.2 ⟨hab, Finset.mem_univ b⟩⟩
  have hST : Disjoint {a} (Finset.univ.erase a) := by simp
  have hU : {a} ∪ Finset.univ.erase a = Finset.univ := by
    rw [Finset.singleton_union, Finset.insert_erase (Finset.mem_univ a)]
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  have h1 := exercise_18_AA_2 ⟨u, hu⟩ (Finset.singleton_nonempty a) hT hST hU
  have h2 := footnote_18_28 hω hanti (Finset.singleton_nonempty a) hT hST hU
  linarith

end MWG.CoreFoundations
