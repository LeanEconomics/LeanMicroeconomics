/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bimatrix

/-!
# The examples of Section 8.B

MWG, Section 8.B, pp. 236-242. Rows and columns are numbered from `0` in the order printed.

* Figure 8.B.1, the Prisoner's Dilemma: "confess" is strictly dominant for both prisoners,
  `(confess, confess)` is a Nash equilibrium, and both prisoners prefer `(don't, don't)`.
* **Example 8.B.1** (Figure 8.B.2): no strictly dominant strategy; `D` is strictly dominated by
  `M` and by `U`.
* **Example 8.B.2** (Figure 8.B.3): `U` and `M` are weakly dominated by `D`. The small type of
  p. 240: iterated deletion of *weakly* dominated strategies depends on the order of deletion
  (`figure_8_B_3_order_dependence`).
* **Example 8.B.3** (Figure 8.B.4, the DA's Brother): neither of prisoner 1's strategies is
  dominated, but iterated strict dominance leaves only `(confess, confess)`.
* Figure 8.B.5 (pp. 241-242): no pure strategy dominates `M`, but `½U + ½D` does; with `M`
  paying `6` against both columns, neither `U` nor `D` is strictly dominated while `½U + ½D` is
  strictly dominated by `M`.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-! ### Figure 8.B.1: the Prisoner's Dilemma (row/column `0` = don't confess, `1` = confess) -/

/-- Prisoner 1's payoffs in Figure 8.B.1. -/
def pdU₁ : Fin 2 → Fin 2 → ℝ := ![![-2, -10], ![-1, -5]]

/-- Prisoner 2's payoffs in Figure 8.B.1. -/
def pdU₂ : Fin 2 → Fin 2 → ℝ := ![![-2, -1], ![-10, -5]]

/-- **Figure 8.B.1** (MWG, pp. 236-237). In the Prisoner's Dilemma "confess" is a strictly dominant
strategy for each prisoner. -/
theorem figure_8_B_1_confess_dominant :
    StrictlyDominant (bimatrix pdU₁ pdU₂) 0 (1 : Fin 2) ∧
      StrictlyDominant (bimatrix pdU₁ pdU₂) 1 (1 : Fin 2) := by
  refine ⟨(bimatrix_strictlyDominant_zero_iff _ _ _).2 ?_,
    (bimatrix_strictlyDominant_one_iff _ _ _).2 ?_⟩
  · intro a ha b
    fin_cases a
    · fin_cases b <;> norm_num [pdU₁]
    · exact absurd rfl ha
  · intro b hb a
    fin_cases b
    · fin_cases a <;> norm_num [pdU₂]
    · exact absurd rfl hb

/-- **Figure 8.B.1** (MWG, p. 237). `(confess, confess)` is a Nash equilibrium, yet both prisoners
prefer `(don't confess, don't confess)`; moving away from it, a prisoner gains one year and costs
his partner eight. -/
theorem figure_8_B_1_dilemma :
    IsNashEquilibrium (bimatrix pdU₁ pdU₂) (pp (1 : Fin 2) (1 : Fin 2)) ∧
      pdU₁ 1 1 < pdU₁ 0 0 ∧ pdU₂ 1 1 < pdU₂ 0 0 ∧
      pdU₁ 1 0 - pdU₁ 0 0 = 1 ∧ pdU₂ 1 0 - pdU₂ 0 0 = -8 := by
  refine ⟨(bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => ?_, fun b => ?_⟩, ?_⟩
  · fin_cases a <;> norm_num [pdU₁]
  · fin_cases b <;> norm_num [pdU₂]
  · norm_num [pdU₁, pdU₂]

/-! ### Example 8.B.1 (Figure 8.B.2) -/

/-- Player 1's payoffs in Figure 8.B.2 (rows `U, M, D`, columns `L, R`). -/
def fig8B2U₁ : Fin 3 → Fin 2 → ℝ := ![![1, -1], ![-1, 1], ![-2, -3]]

/-- Player 2's payoffs in Figure 8.B.2. -/
def fig8B2U₂ : Fin 3 → Fin 2 → ℝ := ![![-1, 1], ![1, -1], ![5, 2]]

/-- **Example 8.B.1** (MWG, p. 237). In the game of Figure 8.B.2 there is no strictly dominant
strategy, and `D` is strictly dominated by `M` (and also by `U`). -/
theorem example_8_B_1 :
    (¬ ∃ a : Fin 3, StrictlyDominant (bimatrix fig8B2U₁ fig8B2U₂) 0 a) ∧
      (¬ ∃ b : Fin 2, StrictlyDominant (bimatrix fig8B2U₁ fig8B2U₂) 1 b) ∧
      StrictlyDominates (bimatrix fig8B2U₁ fig8B2U₂) 0 (1 : Fin 3) (2 : Fin 3) ∧
      StrictlyDominates (bimatrix fig8B2U₁ fig8B2U₂) 0 (0 : Fin 3) (2 : Fin 3) := by
  refine ⟨?_, ?_, (bimatrix_strictlyDominates_zero_iff _ _ _ _).2 fun b => ?_,
    (bimatrix_strictlyDominates_zero_iff _ _ _ _).2 fun b => ?_⟩
  · rintro ⟨a, ha⟩
    have h := (bimatrix_strictlyDominant_zero_iff _ _ a).1 ha
    fin_cases a
    · have := h 1 (by decide) 1; norm_num [fig8B2U₁] at this
    · have := h 0 (by decide) 0; norm_num [fig8B2U₁] at this
    · have := h 0 (by decide) 0; norm_num [fig8B2U₁] at this
  · rintro ⟨b, hb⟩
    have h := (bimatrix_strictlyDominant_one_iff _ _ b).1 hb
    fin_cases b
    · have := h 1 (by decide) 0; norm_num [fig8B2U₂] at this
    · have := h 0 (by decide) 1; norm_num [fig8B2U₂] at this
  · fin_cases b <;> norm_num [fig8B2U₁]
  · fin_cases b <;> norm_num [fig8B2U₁]

/-! ### Example 8.B.2 (Figure 8.B.3) and order dependence of weak deletion -/

/-- Player 1's payoffs in Figure 8.B.3 (rows `U, M, D`, columns `L, R`). -/
def fig8B3U₁ : Fin 3 → Fin 2 → ℝ := ![![5, 4], ![6, 3], ![6, 4]]

/-- Player 2's payoffs in Figure 8.B.3. -/
def fig8B3U₂ : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![4, 4]]

/-- **Example 8.B.2** (MWG, p. 238). In Figure 8.B.3 player 1's strategies `U` and `M` are both
weakly dominated by `D`. -/
theorem example_8_B_2 :
    WeaklyDominates (bimatrix fig8B3U₁ fig8B3U₂) 0 (2 : Fin 3) (0 : Fin 3) ∧
      WeaklyDominates (bimatrix fig8B3U₁ fig8B3U₂) 0 (2 : Fin 3) (1 : Fin 3) := by
  refine ⟨(bimatrix_weaklyDominates_zero_iff _ _ _ _).2 ⟨fun b => ?_, 0, by norm_num [fig8B3U₁]⟩,
    (bimatrix_weaklyDominates_zero_iff _ _ _ _).2 ⟨fun b => ?_, 1, by norm_num [fig8B3U₁]⟩⟩
  · fin_cases b <;> norm_num [fig8B3U₁]
  · fin_cases b <;> norm_num [fig8B3U₁]

/-- Within remaining sets `A` (rows) and `B` (columns), `a` is weakly dominated by a remaining
row. -/
def RowWeaklyDominatedIn {m n : ℕ} (u : Fin m → Fin n → ℝ) (A : Set (Fin m)) (B : Set (Fin n))
    (a : Fin m) : Prop :=
  ∃ a' ∈ A, (∀ b ∈ B, u a b ≤ u a' b) ∧ ∃ b ∈ B, u a b < u a' b

/-- Within remaining sets, the column `b` is weakly dominated by a remaining column. -/
def ColWeaklyDominatedIn {m n : ℕ} (u : Fin m → Fin n → ℝ) (A : Set (Fin m)) (B : Set (Fin n))
    (b : Fin n) : Prop :=
  ∃ b' ∈ B, (∀ a ∈ A, u a b ≤ u a b') ∧ ∃ a ∈ A, u a b < u a b'

/-- **Section 8.B** (MWG, p. 240, small type). One step of iterated deletion of weakly dominated
strategies in a two-player table: everything removed is weakly dominated in the remaining
game. -/
def WDStep2 {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (P Q : Set (Fin m) × Set (Fin n)) : Prop :=
  Q.1 ⊆ P.1 ∧ Q.2 ⊆ P.2 ∧ (∀ a ∈ P.1, a ∉ Q.1 → RowWeaklyDominatedIn u₁ P.1 P.2 a) ∧
    ∀ b ∈ P.2, b ∉ Q.2 → ColWeaklyDominatedIn u₂ P.1 P.2 b

/-- No remaining strategy is weakly dominated in the remaining game. -/
def WDTerminal2 {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (P : Set (Fin m) × Set (Fin n)) : Prop :=
  (∀ a ∈ P.1, ¬ RowWeaklyDominatedIn u₁ P.1 P.2 a) ∧
    ∀ b ∈ P.2, ¬ ColWeaklyDominatedIn u₂ P.1 P.2 b

/-- A singleton game has no weakly dominated strategies. -/
theorem wdTerminal2_singleton {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (a : Fin m) (b : Fin n) :
    WDTerminal2 u₁ u₂ ({a}, {b}) := by
  constructor
  · rintro x hx ⟨a', ha', -, b', -, hlt⟩
    simp only [Set.mem_singleton_iff] at hx ha'
    subst hx ha'
    exact lt_irrefl _ hlt
  · rintro y hy ⟨b', hb', -, a', -, hlt⟩
    simp only [Set.mem_singleton_iff] at hy hb'
    subst hy hb'
    exact lt_irrefl _ hlt

/-- **Section 8.B** (MWG, p. 240, small type). In Figure 8.B.3 iterated deletion of weakly dominated
strategies depends on the order of deletion: deleting `U`, then `L`, then `M` leaves `(D, R)`;
deleting `M`, then `R`, then `U` leaves `(D, L)`. Both are complete deletion processes. -/
theorem figure_8_B_3_order_dependence :
    let u₁ := fig8B3U₁
    let u₂ := fig8B3U₂
    Relation.ReflTransGen (WDStep2 u₁ u₂) (Set.univ, Set.univ) ({2}, {1}) ∧
      WDTerminal2 u₁ u₂ ({2}, {1}) ∧
      Relation.ReflTransGen (WDStep2 u₁ u₂) (Set.univ, Set.univ) ({2}, {0}) ∧
      WDTerminal2 u₁ u₂ ({2}, {0}) ∧ (({2}, {1}) : Set (Fin 3) × Set (Fin 2)) ≠ ({2}, {0}) := by
  intro u₁ u₂
  refine ⟨?_, wdTerminal2_singleton _ _ _ _, ?_, wdTerminal2_singleton _ _ _ _, ?_⟩
  · -- delete `U`, then `L`, then `M`
    refine Relation.ReflTransGen.head (b := ({1, 2}, Set.univ)) ?_ ?_
    · refine ⟨Set.subset_univ _, le_rfl, fun a _ ha => ⟨2, Set.mem_univ _, ?_⟩,
        fun b _ hb => absurd (Set.mem_univ b) hb⟩
      have : a = 0 := by fin_cases a <;> simp_all
      subst this
      exact ⟨fun b _ => by fin_cases b <;> norm_num [u₁, fig8B3U₁],
        0, Set.mem_univ _, by norm_num [u₁, fig8B3U₁]⟩
    refine Relation.ReflTransGen.head (b := ({1, 2}, {1})) ?_ ?_
    · refine ⟨le_rfl, Set.subset_univ _, fun a ha ha' => absurd ha ha', fun b _ hb => ?_⟩
      have : b = 0 := by fin_cases b <;> simp_all
      subst this
      refine ⟨1, Set.mem_univ _, fun a ha => ?_, 1, by simp, by norm_num [u₂, fig8B3U₂]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> norm_num [u₂, fig8B3U₂]
    refine Relation.ReflTransGen.single ⟨by simp, le_rfl, fun a ha ha' => ?_,
      fun b hb hb' => absurd hb hb'⟩
    have : a = 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
      tauto
    subst this
    refine ⟨2, by simp, fun b hb => ?_, 1, rfl, by norm_num [u₁, fig8B3U₁]⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    norm_num [u₁, fig8B3U₁]
  · -- delete `M`, then `R`, then `U`
    refine Relation.ReflTransGen.head (b := ({0, 2}, Set.univ)) ?_ ?_
    · refine ⟨Set.subset_univ _, le_rfl, fun a _ ha => ⟨2, Set.mem_univ _, ?_⟩,
        fun b _ hb => absurd (Set.mem_univ b) hb⟩
      have : a = 1 := by fin_cases a <;> simp_all
      subst this
      exact ⟨fun b _ => by fin_cases b <;> norm_num [u₁, fig8B3U₁],
        1, Set.mem_univ _, by norm_num [u₁, fig8B3U₁]⟩
    refine Relation.ReflTransGen.head (b := ({0, 2}, {0})) ?_ ?_
    · refine ⟨le_rfl, Set.subset_univ _, fun a ha ha' => absurd ha ha', fun b _ hb => ?_⟩
      have : b = 1 := by fin_cases b <;> simp_all
      subst this
      refine ⟨0, Set.mem_univ _, fun a ha => ?_, 0, by simp, by norm_num [u₂, fig8B3U₂]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> norm_num [u₂, fig8B3U₂]
    refine Relation.ReflTransGen.single ⟨by simp, le_rfl, fun a ha ha' => ?_,
      fun b hb hb' => absurd hb hb'⟩
    have : a = 0 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
      tauto
    subst this
    refine ⟨2, by simp, fun b hb => ?_, 0, rfl, by norm_num [u₁, fig8B3U₁]⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    norm_num [u₁, fig8B3U₁]
  · intro h
    have := congrArg Prod.snd h
    simp only [Set.singleton_eq_singleton_iff] at this
    exact absurd this (by decide)

/-! ### Example 8.B.3 (Figure 8.B.4): the DA's Brother -/

/-- Prisoner 1's payoffs in the DA's Brother (Figure 8.B.4). -/
def daU₁ : Fin 2 → Fin 2 → ℝ := ![![0, -10], ![-1, -5]]

/-- Prisoner 2's payoffs in the DA's Brother. -/
def daU₂ : Fin 2 → Fin 2 → ℝ := ![![-2, -1], ![-10, -5]]

/-- **Example 8.B.3** (MWG, pp. 238-239). In the DA's Brother neither of prisoner 1's strategies is
weakly (let alone strictly) dominated, while "don't confess" is strictly dominated for
prisoner 2. -/
theorem example_8_B_3_dominance :
    (∀ a : Fin 2, ¬ WeaklyDominated (bimatrix daU₁ daU₂) 0 a) ∧
      (∀ a : Fin 2, ¬ StrictlyDominated (bimatrix daU₁ daU₂) 0 a) ∧
      StrictlyDominates (bimatrix daU₁ daU₂) 1 (1 : Fin 2) (0 : Fin 2) := by
  have hw : ∀ a : Fin 2, ¬ WeaklyDominated (bimatrix daU₁ daU₂) 0 a := by
    rintro a ⟨a', ha'⟩
    have h := (bimatrix_weaklyDominates_zero_iff _ _ a' a).1 ha'
    fin_cases a <;> fin_cases a'
    · obtain ⟨b, hb⟩ := h.2; exact lt_irrefl _ hb
    · have := h.1 0
      simp [daU₁] at this
      linarith
    · have := h.1 1
      simp [daU₁] at this
      linarith
    · obtain ⟨b, hb⟩ := h.2; exact lt_irrefl _ hb
  refine ⟨hw, fun a ⟨a', ha'⟩ => hw a ⟨a', ha'.weaklyDominates (pp 0 0)⟩,
    (bimatrix_strictlyDominates_one_iff _ _ _ _).2 fun a => ?_⟩
  fin_cases a <;> norm_num [daU₂]

/-- **Example 8.B.3** (MWG, p. 239). Iterated deletion of strictly dominated strategies in the DA's
Brother: delete prisoner 2's "don't confess", then prisoner 1's "don't confess"; the unique
prediction `(confess, confess)` is the end of every complete process (Exercise 8.B.4) and a
Nash equilibrium. -/
theorem example_8_B_3 :
    Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _) (ps {1} {1}) ∧
      SDTerminal (bimatrix daU₁ daU₂) (ps {1} {1}) ∧
      (∀ T, Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _) T →
        SDTerminal (bimatrix daU₁ daU₂) T → T = ps {1} {1}) ∧
      IsNashEquilibrium (bimatrix daU₁ daU₂) (pp (1 : Fin 2) (1 : Fin 2)) := by
  have hchain : Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _)
      (ps {1} {1}) := by
    rw [fullSets_eq_ps]
    refine Relation.ReflTransGen.head (b := ps Set.univ {1}) ?_ ?_
    · refine (bimatrix_sdStep_iff _ _ _ _ _ _).2 ⟨⟨le_rfl, Set.subset_univ _⟩,
        fun a _ ha => absurd (Set.mem_univ a) ha, fun b _ hb => ⟨1, Set.mem_univ _, ?_⟩⟩
      have : b = 0 := by fin_cases b <;> simp_all
      subst this
      intro a _
      fin_cases a <;> norm_num [daU₂]
    · refine Relation.ReflTransGen.single ((bimatrix_sdStep_iff _ _ _ _ _ _).2
        ⟨⟨Set.subset_univ _, le_rfl⟩, fun a _ ha => ⟨1, Set.mem_univ _, ?_⟩,
          fun b hb hb' => absurd hb hb'⟩)
      have : a = 0 := by fin_cases a <;> simp_all
      subst this
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      norm_num [daU₁]
  have hterm : SDTerminal (bimatrix daU₁ daU₂) (ps {1} {1}) := by
    refine (bimatrix_sdTerminal_iff _ _ _ _).2 ⟨fun a ha ⟨a', ha', h⟩ => ?_,
      fun b hb ⟨b', hb', h⟩ => ?_⟩
    · rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      exact lt_irrefl _ (h 1 rfl)
    · rw [Set.mem_singleton_iff] at hb hb'
      subst hb hb'
      exact lt_irrefl _ (h 1 rfl)
  have hne : ∀ i, Nonempty (S2 2 2 i) := fun i => by fin_cases i <;> exact ⟨(0 : Fin 2)⟩
  refine ⟨hchain, hterm, fun T hT hTt => exercise_8_B_4 hT hTt hchain hterm, ?_⟩
  refine exercise_8_D_2 hchain fun i => ?_
  fin_cases i <;> rfl

/-! ### Figure 8.B.5: domination by a randomized strategy -/

/-- Player 1's payoffs in Figure 8.B.5(a) (rows `U, M, D`, columns `L, R`). -/
def fig8B5U₁ : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![4, 4], ![0, 10]]

/-- Player 2's payoffs in Figure 8.B.5(a). -/
def fig8B5U₂ : Fin 3 → Fin 2 → ℝ := ![![1, 4], ![2, 3], ![5, 2]]

/-- The randomized strategy `½U + ½D`. -/
noncomputable def halfUD : Fin 3 → ℝ := ![1 / 2, 0, 1 / 2]

theorem isMixedStrategy_halfUD : IsMixedStrategy halfUD := by
  refine ⟨fun a => by fin_cases a <;> norm_num [halfUD], ?_⟩
  simp [halfUD, Fin.sum_univ_three]
  norm_num

/-- **Figure 8.B.5** (MWG, p. 241). None of `U`, `M`, `D` is strictly dominated by another pure
strategy, but `½U + ½D` (expected payoff `5` against both columns) strictly dominates `M`, so `M`
is strictly dominated in `[I, {Δ(S_i)}, {u_i(·)}]` (Proposition 8.B.1). -/
theorem figure_8_B_5 :
    (∀ a a' : Fin 3, ¬ StrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 a' a) ∧
      MixedStrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 halfUD (pureMixed (1 : Fin 3)) ∧
      MixedStrictlyDominated (bimatrix fig8B5U₁ fig8B5U₂) 0 (pureMixed (1 : Fin 3)) := by
  have hdom : MixedStrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 halfUD
      (pureMixed (1 : Fin 3)) := by
    refine (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁ fig8B5U₂ halfUD
      (pureMixed (1 : Fin 3))).2 fun b => ?_
    fin_cases b <;> simp [Fin.sum_univ_three, halfUD, pureMixed, fig8B5U₁] <;> norm_num
  refine ⟨fun a a' h => ?_, hdom, ⟨halfUD, isMixedStrategy_halfUD, hdom⟩⟩
  have h' := (bimatrix_strictlyDominates_zero_iff _ _ a' a).1 h
  have h0 := h' 0
  have h1 := h' 1
  fin_cases a <;> fin_cases a' <;> simp [fig8B5U₁] at h0 h1 <;> linarith

/-- Player 1's payoffs when `M` pays `6` against both columns (p. 242). -/
def fig8B5U₁' : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![6, 6], ![0, 10]]

/-- **Section 8.B** (MWG, p. 242). If `M` pays `6` against either column, neither `U` nor `D` is
strictly dominated (even by a mixed strategy), but `½U + ½D` is strictly dominated by `M`. -/
theorem figure_8_B_5_variant :
    ¬ MixedStrictlyDominated (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (0 : Fin 3)) ∧
      ¬ MixedStrictlyDominated (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (2 : Fin 3)) ∧
      MixedStrictlyDominates (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (1 : Fin 3)) halfUD := by
  refine ⟨fun ⟨(τ : Fin 3 → ℝ), hτ, h⟩ => ?_, fun ⟨(τ : Fin 3 → ℝ), hτ, h⟩ => ?_,
    (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ (pureMixed (1 : Fin 3))
      halfUD).2 fun b => ?_⟩
  · have h0 := (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ τ
      (pureMixed (0 : Fin 3))).1 h 0
    have hs : ∑ a : Fin 3, τ a = 1 := hτ.2
    simp only [Fin.sum_univ_three] at h0 hs
    simp [pureMixed, fig8B5U₁'] at h0
    nlinarith [hτ.1 (0 : Fin 3), hτ.1 (1 : Fin 3), hτ.1 (2 : Fin 3)]
  · have h1 := (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ τ
      (pureMixed (2 : Fin 3))).1 h 1
    have hs : ∑ a : Fin 3, τ a = 1 := hτ.2
    simp only [Fin.sum_univ_three] at h1 hs
    simp [pureMixed, fig8B5U₁'] at h1
    nlinarith [hτ.1 (0 : Fin 3), hτ.1 (1 : Fin 3), hτ.1 (2 : Fin 3)]
  · fin_cases b <;> simp [Fin.sum_univ_three, halfUD, pureMixed, fig8B5U₁'] <;> norm_num

end MWG.SimultaneousMoveGames
