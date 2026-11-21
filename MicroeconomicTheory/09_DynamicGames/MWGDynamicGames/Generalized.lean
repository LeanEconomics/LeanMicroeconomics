/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Zermelo

/-!
# The generalized backward induction procedure

MWG, Section 9.B, pp. 277-278: Proposition 9.B.3.

Fix a subgame `S` of `Γ_E` with initial node `x₀` and a profile `σ^S` that is an SPNE in `S`
(`IsSPNEIn`). The reduced game `Γ̂_E` replaces `S` by a terminal node with the payoffs
`cont(σ^S, x₀)`. A profile `F` of `Γ̂_E` (its moves outside `S`) is evaluated through the
spliced profile `splice σ^S F` (moves of `σ^S` at the information sets of `S`, of `F`
elsewhere), whose continuation payoff at `x₀` is the reduced game's terminal payoff
(`cont_splice_root`). `IsSPNEReduced` is subgame perfection in `Γ̂_E`: no player gains by
changing her moves outside `S`, in any subgame of `Γ_E` not lying strictly inside `S` (these
are the subgames of `Γ̂_E`).

* `proposition_9_B_3_i`: in any SPNE `σ` of `Γ_E` whose play in `S` is `σ^S`, the moves outside
  `S` form an SPNE of `Γ̂_E`.
* `proposition_9_B_3_ii`: if `F` is an SPNE of `Γ̂_E`, the profile playing `σ^S` in `S` and `F`
  elsewhere is an SPNE of `Γ_E`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- The information set `k` belongs to the subgame starting at `x₀`. -/
def InSub (x₀ : List A) (k : H) : Prop := ∃ y, G.IsDecision y ∧ x₀ <:+ y ∧ G.info y = k

open Classical in
/-- The profile playing `σS` at the information sets of the subgame at `x₀` and `F`
elsewhere. -/
noncomputable def splice (x₀ : List A) (σS F : I → H → A → ℝ) : I → H → A → ℝ :=
  fun i k => if InSub G x₀ k then σS i k else F i k

/-- `σS` is a subgame perfect Nash equilibrium of the subgame starting at `x₀`. -/
def IsSPNEIn (x₀ : List A) (σS : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G σS ∧ ∀ y, IsSubgameRoot G y → x₀ <:+ y → InducesNashAt G σS y

omit [DecidableEq H] in
/-- An SPNE of `Γ_E` is an SPNE of every subgame. -/
theorem isSPNEIn_of_isSPNE {σ : I → H → A → ℝ} (h : IsSPNE G σ) (x₀ : List A) :
    IsSPNEIn G x₀ σ :=
  ⟨h.1, fun y hy _ => h.2 y hy⟩

/-- **Proposition 9.B.3, the reduced game** (MWG, p. 277). `F` is a subgame perfect Nash
equilibrium of the reduced game `Γ̂_E` in which the subgame at `x₀` is replaced by the payoffs
of `σS`: in every subgame not lying strictly inside the subgame at `x₀`, no player gains by
changing her moves outside it. -/
def IsSPNEReduced (x₀ : List A) (σS F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G (splice G x₀ σS F) ∧ ∀ y, IsSubgameRoot G y → ¬ x₀ <:+ y →
    ∀ i g, G.IsBehaviorStrategy i g →
      cont G (G.assemble (splice G x₀ σS (Function.update F i g))) y i ≤
        cont G (G.assemble (splice G x₀ σS F)) y i

omit [Fintype A] [DecidableEq A] [DecidableEq I] [DecidableEq H] in
theorem inSub_of_suffix {x₀ y : List A} (hy : G.IsDecision y) (h : x₀ <:+ y) :
    InSub G x₀ (G.info y) := ⟨y, hy, h, rfl⟩

open Classical in
omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of a spliced profile. -/
theorem assemble_splice (x₀ : List A) (σS F : I → H → A → ℝ) (k : H) :
    G.assemble (splice G x₀ σS F) k =
      if InSub G x₀ k then G.assemble σS k else G.assemble F k := by
  classical
  cases hk : G.player k with
  | none => simp only [G.assemble_of_none _ hk, ite_self]
  | some j => simp only [G.assemble_of_some _ hk, splice]

omit [DecidableEq I] [DecidableEq H] in
/-- In the reduced game the subgame's root is a terminal node with the payoffs of `σS`. -/
theorem cont_splice_root (x₀ : List A) (σS F : I → H → A → ℝ) (i : I) :
    cont G (G.assemble (splice G x₀ σS F)) x₀ i = cont G (G.assemble σS) x₀ i :=
  cont_congr G (fun y hy hxy => by
    simp only [assemble_splice, inSub_of_suffix G hy hxy, ↓reduceIte]) i

open Classical in
omit [DecidableEq I] [DecidableEq H] in
/-- Below a subgame root, the information sets of nodes after an entry node of the subgame lie
in it; the entry nodes of the subgame from a node not inside it are at most its root. -/
theorem entryNodes_inSub {x₀ : List A} (hx₀ : IsSubgameRoot G x₀) {y : List A}
    (hy : ¬ x₀ <:+ y) {x : List A} (hx : x ∈ entryNodes G (InSub G x₀) y) : x = x₀ := by
  classical
  rw [mem_entryNodes] at hx
  obtain ⟨hxd, hyx, ⟨w, hw, hxw, hwk⟩, hmin⟩ := hx
  have hx₀x : x₀ <:+ x := hx₀.2.2 w hw hxw x hxd hwk.symm
  by_contra hne
  have hyx₀ : y <:+ x₀ := by
    rcases le_total y.length x₀.length with hl | hl
    · exact List.suffix_of_suffix_length_le hyx hx₀x hl
    · exact absurd (List.suffix_of_suffix_length_le hx₀x hyx hl) hy
  exact hmin x₀ hx₀.1 hyx₀ hx₀x (Ne.symm hne) ⟨x₀, hx₀.1, List.suffix_refl _, rfl⟩

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The deviation of player `i` to `g` within the spliced profile. -/
theorem assemble_update_splice (x₀ : List A) (σS F : I → H → A → ℝ) (i : I)
    (g : H → A → ℝ) (k : H) (hk : ¬ InSub G x₀ k) :
    G.assemble (Function.update (splice G x₀ σS F) i g) k =
      G.assemble (splice G x₀ σS (Function.update F i g)) k := by
  classical
  rw [assemble_splice]
  simp only [hk, ↓reduceIte]
  cases hp : G.player k with
  | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
  | some j =>
    rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj, splice, hk]

omit [DecidableEq H] in
/-- **Proposition 9.B.3(ii)** (MWG, p. 277). If `σS` is an SPNE in the subgame `S` starting at
`x₀` and `F` is an SPNE of the reduced game, then the profile playing `σS` in `S` and `F`
elsewhere is an SPNE of `Γ_E`. -/
theorem proposition_9_B_3_ii {x₀ : List A} (hx₀ : IsSubgameRoot G x₀)
    {σS F : I → H → A → ℝ} (hS : IsSPNEIn G x₀ σS) (hF : IsSPNEReduced G x₀ σS F) :
    IsSPNE G (splice G x₀ σS F) := by
  classical
  refine ⟨hF.1, fun y hy i g hg => ?_⟩
  by_cases hxy : x₀ <:+ y
  · -- inside the subgame the spliced profile is `σS`
    have h1 : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) y i =
        cont G (G.assemble (Function.update σS i g)) y i := by
      refine cont_congr G (fun w hw hyw => ?_) i
      have hin := inSub_of_suffix G hw (hxy.trans hyw)
      cases hp : G.player (G.info w) with
      | none => simp only [G.assemble_of_none _ hp]
      | some j =>
        rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, splice, hin]
    have h2 : cont G (G.assemble (splice G x₀ σS F)) y i = cont G (G.assemble σS) y i :=
      cont_congr G (fun w hw hyw => by
        simp only [assemble_splice, inSub_of_suffix G hw (hxy.trans hyw), ↓reduceIte]) i
    rw [h1, h2]
    exact hS.2 y hy hxy i g hg
  · -- outside: first replace the deviation inside `S` by `σS`, then use the reduced game
    have hoff : ∀ k, ¬ InSub G x₀ k →
        G.assemble (Function.update (splice G x₀ σS F) i g) k =
          G.assemble (splice G x₀ σS (Function.update F i g)) k :=
      fun k hk => assemble_update_splice G x₀ σS F i g k hk
    have hdec := cont_sub_eq_sum_entry G (InSub G x₀) hoff hy.1.1 i
    have hroot : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) x₀ i ≤
        cont G (G.assemble (splice G x₀ σS (Function.update F i g))) x₀ i := by
      rw [cont_splice_root]
      have h1 : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) x₀ i =
          cont G (G.assemble (Function.update σS i g)) x₀ i := by
        refine cont_congr G (fun w hw hyw => ?_) i
        have hin := inSub_of_suffix G hw hyw
        cases hp : G.player (G.info w) with
        | none => simp only [G.assemble_of_none _ hp]
        | some j =>
          rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj, splice, hin]
      rw [h1]
      exact hS.2 x₀ hx₀ (List.suffix_refl _) i g hg
    have hle : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) y i ≤
        cont G (G.assemble (splice G x₀ σS (Function.update F i g))) y i := by
      rw [← sub_nonpos, hdec]
      refine Finset.sum_nonpos fun x hx => ?_
      obtain rfl := entryNodes_inSub G hx₀ hxy hx
      exact mul_nonpos_of_nonneg_of_nonpos (reachFrom_nonneg G
        (assemble_nonneg G (isBehaviorProfile_update G hF.1 hg)) _ _) (sub_nonpos.2 hroot)
    exact hle.trans (hF.2 y hy hxy i g hg)

omit [DecidableEq H] in
/-- **Proposition 9.B.3(i)** (MWG, p. 277). In any SPNE `σ` of `Γ_E` whose play in the subgame
`S` at `x₀` is that of `σS`, the players' moves outside `S` form an SPNE of the reduced game. -/
theorem proposition_9_B_3_i {x₀ : List A} {σS σ : I → H → A → ℝ} (hσ : IsSPNE G σ)
    (hagree : ∀ k, InSub G x₀ k → G.assemble σ k = G.assemble σS k) :
    IsSPNEReduced G x₀ σS σ := by
  classical
  have hsp : G.assemble (splice G x₀ σS σ) = G.assemble σ := by
    funext k
    rw [assemble_splice]
    split_ifs with h
    · exact (hagree k h).symm
    · rfl
  refine ⟨?_, fun y hy _ i g hg => ?_⟩
  · intro j k hk
    have h := hσ.1 j k hk
    have e1 := congrFun hsp k
    rw [G.assemble_of_some _ hk, G.assemble_of_some _ hk] at e1
    rw [e1]
    exact h
  · -- the reduced-game deviation is a deviation of `Γ_E` keeping `σS`'s moves inside `S`
    set g' : H → A → ℝ := fun k => if InSub G x₀ k then σ i k else g k
    have hg' : G.IsBehaviorStrategy i g' := fun k hk => by
      simp only [g']
      split_ifs
      · exact hσ.1 i k hk
      · exact hg k hk
    have heq : G.assemble (splice G x₀ σS (Function.update σ i g)) =
        G.assemble (Function.update σ i g') := by
      funext k
      rw [assemble_splice]
      cases hp : G.player k with
      | none =>
        simp only [G.assemble_of_none _ hp]
        split_ifs <;> rfl
      | some j =>
        have e2 : G.assemble (Function.update σ i g') k = Function.update σ i g' j k :=
          G.assemble_of_some _ hp
        have e3 : G.assemble (Function.update σ i g) k = Function.update σ i g j k :=
          G.assemble_of_some _ hp
        rw [e2, e3]
        split_ifs with h
        · rw [← hagree k h, G.assemble_of_some _ hp]
          by_cases hj : j = i
          · subst hj; simp [g', h]
          · simp [Function.update_of_ne hj]
        · by_cases hj : j = i
          · subst hj; simp [g', h]
          · simp [Function.update_of_ne hj]
    rw [heq, hsp]
    exact hσ.2 y hy i g' hg'

end MWG.DynamicGames
