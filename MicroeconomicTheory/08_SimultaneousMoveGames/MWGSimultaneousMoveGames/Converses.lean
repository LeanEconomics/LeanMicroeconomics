/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.ExercisesCF
import MWGSimultaneousMoveGames.TwoPlayerConverse

/-!
# Instances of the two-player converses (pp. 245 and 259)

MWG, Section 8.C, p. 245, and Section 8.F, p. 259.

* **p. 245, Definition 8.C.2 read literally** (correction 9). In the two-player game
  `ratGap` (rows `a, b, c`, columns `L, R, M`) nothing is strictly dominated, so every strategy
  survives iterated strict dominance, yet row `a` is not rationalizable in the sense of
  Definition 8.C.2 (`Rationalizable`): `a` is a best response only to `½L + ½R`, which is
  strictly dominated by `M` and is removed in the first round. With the probabilistic
  conjectures of footnote 1 (`RationalizableConv`) `a` is rationalizable, as
  `rationalizableConv_iff_two` says (`rationalizable_two_counterexample`).
* **p. 259**: in Figure 8.F.1, `(U, L)` is a Nash equilibrium in which neither strategy is
  weakly dominated, so it is trembling-hand perfect (`figure_8_F_1_UL_isTHP`, an instance of
  `isTHP_of_not_weaklyDominated_two`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- If every pure strategy of every player is a best response to some mixed profile, no
strategy is strictly dominated: the full game is a complete deletion process. -/
theorem msdTerminal_full_of_bestResponse {I : Type*} {S : I → Type*} [Fintype I]
    [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {N : NormalForm I S}
    (h : ∀ i (a : S i), ∃ σ, IsMixedProfile σ ∧ IsBestResponse N i (pureMixed a) σ) :
    MSDTerminal N (fullSets S) := by
  rintro i a - ⟨τ', hτ', -, hdom⟩
  obtain ⟨σ, hσ, hbr⟩ := h i a
  have hd : MixedStrictlyDominated N i (pureMixed a) :=
    (proposition_8_B_1 N i a).2 ⟨τ', hτ', fun s => hdom s fun _ _ => Set.mem_univ _⟩
  exact neverBestResponse_of_mixedStrictlyDominated N i hd σ hσ hbr

/-! ### Rationalizability, p. 245 -/

/-- Player 1's payoffs in `ratGap`: rows `a, b, c`, columns `L, R, M`. -/
def ratGapU₁ : Fin 3 → Fin 3 → ℝ := ![![2, 2, -1], ![4, 0, 0], ![0, 4, 0]]

/-- Player 2's payoffs in `ratGap`. -/
def ratGapU₂ : Fin 3 → Fin 3 → ℝ := ![![0, 0, 1], ![3, 0, 2], ![0, 3, 2]]

/-- The two-player game separating Definition 8.C.2 from iterated strict dominance. -/
def ratGap : NormalForm (Fin 2) (S2 3 3) := bimatrix ratGapU₁ ratGapU₂

/-- The mixed strategy `½L + ½R` of player 2. -/
noncomputable def halfLR : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

theorem isMixedStrategy_halfLR : IsMixedStrategy halfLR :=
  ⟨fun b => by fin_cases b <;> norm_num [halfLR], by norm_num [halfLR, Fin.sum_univ_three]⟩

/-- In `ratGap` every pure strategy is a best response to some mixed strategy: `a` to
`½L + ½R`, `b` to `L`, `c` to `R`, `L` to `b`, `R` to `c`, `M` to `a`. -/
theorem ratGap_bestResponse (i : Fin 2) (a : S2 3 3 i) :
    ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap i (pureMixed a) σ := by
  fin_cases i
  · change Fin 3 at a
    have key : ∀ y : Fin 3 → ℝ, IsMixedStrategy y →
        (∀ a', ∑ b, y b * ratGapU₁ a' b ≤ ∑ b, y b * ratGapU₁ a b) →
        ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap 0 (pureMixed a) σ :=
      fun y hy h => ⟨mp (pureMixed 0) y, isMixedProfile_mp (isMixedStrategy_pureMixed _) hy,
        bimatrix_isBestResponse_row _ _ _ a h⟩
    fin_cases a
    · exact key halfLR isMixedStrategy_halfLR fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, halfLR, ratGapU₁]
    · exact key (pureMixed 0) (isMixedStrategy_pureMixed _) fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₁]
    · exact key (pureMixed 1) (isMixedStrategy_pureMixed _) fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₁]
  · change Fin 3 at a
    have key : ∀ x : Fin 3 → ℝ, IsMixedStrategy x →
        (∀ b', ∑ c, x c * ratGapU₂ c b' ≤ ∑ c, x c * ratGapU₂ c a) →
        ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap 1 (pureMixed a) σ :=
      fun x hx h => ⟨mp x (pureMixed 0), isMixedProfile_mp hx (isMixedStrategy_pureMixed _),
        bimatrix_isBestResponse_col _ _ _ a h⟩
    fin_cases a
    · exact key (pureMixed 1) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]
    · exact key (pureMixed 2) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]
    · exact key (pureMixed 0) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]

/-- **Section 8.C, p. 245: Definition 8.C.2 read literally** (correction 9). In the two-player
game `ratGap` no strategy is strictly dominated (the full game is a complete process of iterated
strict dominance), but row `a` is not rationalizable under Definition 8.C.2; it is rationalizable
with the probabilistic conjectures of footnote 1. -/
theorem rationalizable_two_counterexample :
    MSDTerminal ratGap (fullSets (S2 3 3)) ∧ ¬ Rationalizable ratGap 0 (pureMixed (0 : Fin 3)) ∧
      RationalizableConv ratGap 0 (pureMixed (0 : Fin 3)) := by
  have hterm : MSDTerminal ratGap (fullSets (S2 3 3)) :=
    msdTerminal_full_of_bestResponse ratGap_bestResponse
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k; fin_cases k <;> simp
  refine ⟨hterm, fun h => ?_, (rationalizableConv_iff_two ratGap h01 htwo
    Relation.ReflTransGen.refl hterm 0 (0 : Fin 3)).2 (Set.mem_univ _)⟩
  obtain ⟨-, σ, hσ, hσT, hbr⟩ := h 2
  obtain ⟨σ', hσ', -, hbr'⟩ := (hσT 1 h01.symm).2
  -- `a` is a best response only to `½L + ½R`
  set y : Fin 3 → ℝ := σ 1 with hy
  have hrow : ∀ a : Fin 3, ratGap.mixedPayoff (update σ 0 (pureMixed a)) 0 =
      ∑ b : Fin 3, y b * ratGapU₁ a b := fun a => bimatrix_mixedPayoff_row _ _ σ a
  have hb : ∑ b : Fin 3, y b * ratGapU₁ 1 b ≤ ∑ b : Fin 3, y b * ratGapU₁ 0 b := by
    rw [← hrow, ← hrow]; exact hbr.2 _ (isMixedStrategy_pureMixed _)
  have hc : ∑ b : Fin 3, y b * ratGapU₁ 2 b ≤ ∑ b : Fin 3, y b * ratGapU₁ 0 b := by
    rw [← hrow, ← hrow]; exact hbr.2 _ (isMixedStrategy_pureMixed _)
  simp only [Fin.sum_univ_three, ratGapU₁] at hb hc
  norm_num at hb hc
  have hy0 : ∀ b : Fin 3, 0 ≤ y b := (hσ 1).1
  have hy1 : ∑ b : Fin 3, y b = 1 := (hσ 1).2
  have hys : y 0 + y 1 + y 2 = 1 := by simpa [Fin.sum_univ_three] using hy1
  have hy2 : y 2 = 0 := by linarith [hy0 0, hy0 1, hy0 2]
  have hy01 : y 0 = 1 / 2 ∧ y 1 = 1 / 2 := by constructor <;> linarith
  -- `½L + ½R` is strictly dominated by `M`, so it is never a best response
  have hdom := (bimatrix_mixedStrictlyDominates_one_iff ratGapU₁ ratGapU₂
    (pureMixed (2 : Fin 3)) y).2 (fun a => by
      fin_cases a <;>
        simp [Fin.sum_univ_three, ratGapU₂, pureMixed, hy2, hy01.1, hy01.2] <;> norm_num)
  exact neverBestResponse_of_mixedStrictlyDominated ratGap 1
    ⟨_, isMixedStrategy_pureMixed (2 : Fin 3), hdom⟩ σ' hσ' hbr'

/-! ### Trembling-hand perfection, p. 259 -/

/-- **Section 8.F** (MWG, p. 259, small type), an instance of the two-player converse of
Proposition 8.F.2. In Figure 8.F.1, `(U, L)` is a Nash equilibrium in which neither `U` nor `L`
is weakly dominated (by any mixed strategy), so it is trembling-hand perfect. -/
theorem figure_8_F_1_UL_isTHP :
    IsTHP (bimatrix fig8F1U₁ fig8F1U₂) (pureProfile (pp (0 : Fin 2) (0 : Fin 2))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k; fin_cases k <;> simp
  have hNE : IsNashEquilibrium (bimatrix fig8F1U₁ fig8F1U₂) (pp (0 : Fin 2) (0 : Fin 2)) :=
    (bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => by fin_cases a <;> norm_num [fig8F1U₁],
      fun b => by fin_cases b <;> norm_num [fig8F1U₂]⟩
  refine isTHP_of_not_weaklyDominated_two _ h01 htwo ((corollary_8_D_1 _ _).1 hNE) fun k => ?_
  rintro ⟨τ', hτ', hdom⟩
  obtain ⟨hle, s, hlt⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom
  have e1 := hle (pp (0 : Fin 2) (0 : Fin 2))
  rcases htwo k with rfl | rfl
  · set x : Fin 2 → ℝ := τ' with hx
    have h0 : ∀ a : Fin 2, 0 ≤ x a := hτ'.1
    have h2 : ∑ a : Fin 2, x a = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 2 2 i,
        (bimatrix fig8F1U₁ fig8F1U₂).mixedPayoff
          (update (pureProfile s') 0 (pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 0)) 0 =
        fig8F1U₁ 0 (s' 1) := fun s' => by
      rw [show pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 0 =
        pureMixed (pp (0 : Fin 2) (0 : Fin 2) 0) from rfl, mixedPayoff_pureProfile_update]
      simp
    rw [hL, bimatrix_mixed_vs_pure_zero] at e1 hlt
    simp only [Fin.sum_univ_two, pp_one] at e1 hlt h2
    norm_num [fig8F1U₁] at e1
    have hx1 : x 1 = 0 := by linarith [h0 0, h0 1]
    have hx0 : x 0 = 1 := by linarith
    rw [← hx, hx0, hx1] at hlt
    simp at hlt
  · set x : Fin 2 → ℝ := τ' with hx
    have h0 : ∀ a : Fin 2, 0 ≤ x a := hτ'.1
    have h2 : ∑ a : Fin 2, x a = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 2 2 i,
        (bimatrix fig8F1U₁ fig8F1U₂).mixedPayoff
          (update (pureProfile s') 1 (pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 1)) 1 =
        fig8F1U₂ (s' 0) 0 := fun s' => by
      rw [show pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 1 =
        pureMixed (pp (0 : Fin 2) (0 : Fin 2) 1) from rfl, mixedPayoff_pureProfile_update]
      simp
    rw [hL, bimatrix_mixed_vs_pure_one] at e1 hlt
    simp only [Fin.sum_univ_two, pp_zero] at e1 hlt h2
    norm_num [fig8F1U₂] at e1
    have hx1 : x 1 = 0 := by linarith [h0 0, h0 1]
    have hx0 : x 0 = 1 := by linarith
    rw [← hx, hx0, hx1] at hlt
    simp at hlt

end MWG.SimultaneousMoveGames
