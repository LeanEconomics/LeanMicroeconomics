/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Sequential
import MWGDynamicGames.EntryTwo
import MWGSimultaneousMoveGames.TwoPlayerConverse
import MWGSimultaneousMoveGames.Bimatrix

/-!
# Extensive form trembling-hand perfection in examples

MWG, Appendix B, Figures 9.BB.1 and 9.BB.2 (pp. 299-301).

* `isEFTHP_eq_zero_of_worse`: in an extensive form trembling-hand perfect equilibrium, an agent
  never plays an action `a` that does worse than another action `b` against every totally mixed
  profile (in the agent normal form `a` is then never a best response in any perturbed game).
* `figure_9_BB_2`: in the entry game of Figure 9.BB.2, (out, fight) with beliefs on In₁ is a
  sequential equilibrium, but it is not extensive form trembling-hand perfect: in every EFTHP
  the incumbent accommodates for sure (fighting is worse against every totally mixed
  profile, since it is never better at In₁ and worse at In₂).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] in
/-- **Appendix B** (MWG, p. 300). In an extensive form trembling-hand perfect equilibrium of a
game without absent-mindedness, the agent at information set `k` puts probability zero on an
action `a` that is worse for its owner than another action `b` against every totally mixed
profile. -/
theorem isEFTHP_eq_zero_of_worse [Fintype H] (hNA : G.NoAbsentMindedness) {F : I → H → A → ℝ}
    (hF : IsEFTHP G F) {k : H} {i : I} (hk : G.player k = some i) {a b : A}
    (ha : a ∈ G.avail k) (hb : b ∈ G.avail k)
    (hworse : ∀ Fp, IsTotallyMixedB G Fp →
      ∑ x ∈ G.infoSet k, G.reach (G.assemble Fp) x *
        (cont G (G.assemble Fp) (a :: x) i - cont G (G.assemble Fp) (b :: x) i) < 0) :
    G.assemble F k a = 0 := by
  obtain ⟨-, σ, ⟨-, ε, σs, hε, hε0, hσs, hlim⟩, hFσ⟩ := hF
  have hne : G.player k ≠ none := by rw [hk]; simp
  set ag : Agent G := ⟨k, hne⟩
  have hown : owner G ag = i := by
    have := player_owner G ag
    rw [hk] at this
    exact (Option.some.inj this).symm
  set sa := agentPure G ag ⟨a, ha⟩
  set sb := agentPure G ag ⟨b, hb⟩
  have hmix : ∀ n ag', IsMixedStrategy (σs n ag') := fun n ag' =>
    isMixedStrategy_of_mem_perturbedSet (hε n) ((hσs n).1 ag')
  have heq : ∀ n, σs n ag sa = ε n ag sa := by
    intro n
    refine perturbedNash_eq_of_not_best (hσs n) ag (b := sb) ?_
    have hmixU : ∀ s, ∀ ag', IsMixedStrategy (Function.update (σs n) ag (pureMixed s) ag') := by
      intro s ag'
      by_cases h : ag' = ag
      · subst h
        rw [Function.update_self]
        exact isMixedStrategy_pureMixed s
      · rw [Function.update_of_ne h]
        exact hmix n ag'
    rw [agentNF_mixedPayoff G hNA (hmixU sa), agentNF_mixedPayoff G hNA (hmixU sb),
      assemble_agentProfile_update G _ ag ha, assemble_agentProfile_update G _ ag hb, hown]
    have hdiff := cont_update_dirac_sub G hNA (G.assemble (agentProfile G (σs n))) k ha hb i
    have hTM : IsTotallyMixedB G (agentProfile G (σs n)) := by
      refine ⟨isBehaviorProfile_agentProfile G (hmix n), fun j k' hk' c hc => ?_⟩
      have hne' : G.player k' ≠ none := by rw [hk']; simp
      have := assemble_agentProfile_apply G (σs n) ⟨k', hne'⟩ c
      rw [G.assemble_of_some _ hk'] at this
      rw [this]
      simp only [hc, ↓reduceDIte]
      exact lt_of_lt_of_le ((hε n).1 _ _).1 (((hσs n).1 _).1 _)
    have := hworse _ hTM
    rw [← hdiff] at this
    linarith
  have h1 : Tendsto (fun n => σs n ag sa) atTop (𝓝 (σ ag sa)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim ag) sa
  have h2 : Tendsto (fun n => σs n ag sa) atTop (𝓝 0) := by
    simp only [heq]
    exact hε0 ag sa
  have hσ0 : σ ag sa = 0 := tendsto_nhds_unique h1 h2
  rw [hFσ k hne, assemble_agentProfile_apply G σ ag a]
  split_ifs with h
  · exact hσ0
  · exact absurd ha h

/-- **Figure 9.BB.2** (MWG, p. 301): payoffs after entry `(−1, 0)`, `(3, 0)` (In₁) and
`(−1, −1)`, `(2, 1)` (In₂). -/
abbrev fig9BB2 : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]

theorem entryTwo_noAbsentMindedness (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    (entryTwo o t).NoAbsentMindedness := by
  have : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness; decide
  exact this

/-- In the entry game with two entry strategies, E staying out and I choosing `0`,
with beliefs putting probability one on In₁, is a consistent assessment: E trembles to In₁ with
probability `ε` and to In₂ with probability `ε²`, I trembles with probability `ε`. -/
theorem entryTwo_consistent_leftBelief_zero (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsConsistent (entryTwo o t) (pureMoves ![0, 0]) leftBelief := by
  have hr := entryTwo_reach o t
  have hI := entryTwo_infoSet o t
  -- trembles: E plays In₁ with probability `ε`, In₂ with `ε²`; I deviates with `ε`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
    simp only [hε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2]
    else ![1 - ε n, ε n, 0] with hFs
  have hTM : ∀ n, IsTotallyMixedB (entryTwo o t) (Fs n) := by
    intro n
    have e0 := hε0 n
    have e1 := hε1 n
    have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  have hlimε : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [hε, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 0])) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using hlimε.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, pureMoves, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using hsq
    · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simp [hFs, pureMoves, dirac]
  refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  have hmem := (mem_decisionNodes _).2 hx
  rw [hdn] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hasm : ∀ n, (entryTwo o t).assemble (Fs n) 0 = Fs n 0 0 := fun n => entryTwo_assemble _ _ _ 0
  have hprob : ∀ n, probInfo (entryTwo o t) ((entryTwo o t).assemble (Fs n)) 1 = ε n + ε n ^ 2 := by
    intro n
    rw [(hr _).2.2, hasm]
    simp [hFs]
  rcases hmem with rfl | rfl | rfl
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [] = 1 := by
      intro n
      unfold bayesBelief probInfo
      rw [show (entryTwo o t).info [] = 0 from rfl, hI.1]
      simp
    simp only [this, leftBelief]
    exact tendsto_const_nhds
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [1] =
        1 / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [1] = 1 from rfl, hprob, (hr _).1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    simp only [this, leftBelief]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
    simpa using this
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [2] =
        ε n / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [2] = 1 from rfl, hprob, (hr _).2.1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte]
      simp
      field_simp
    simp only [this, leftBelief]
    have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
      hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
    simpa using h

/-- In the entry game with two entry strategies, E staying out and I choosing `1`,
with beliefs putting probability one on In₁, is a consistent assessment: E trembles to In₁ with
probability `ε` and to In₂ with probability `ε²`, I trembles with probability `ε`. -/
theorem entryTwo_consistent_leftBelief_one (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsConsistent (entryTwo o t) (pureMoves ![0, 1]) leftBelief := by
  have hr := entryTwo_reach o t
  have hI := entryTwo_infoSet o t
  -- trembles: E plays In₁ with probability `ε`, In₂ with `ε²`; I deviates with `ε`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
    simp only [hε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2]
    else ![ε n, 1 - ε n, 0] with hFs
  have hTM : ∀ n, IsTotallyMixedB (entryTwo o t) (Fs n) := by
    intro n
    have e0 := hε0 n
    have e1 := hε1 n
    have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  have hlimε : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [hε, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1])) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using hlimε.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, pureMoves, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
    · simp [hFs, pureMoves, dirac]
  refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  have hmem := (mem_decisionNodes _).2 hx
  rw [hdn] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hasm : ∀ n, (entryTwo o t).assemble (Fs n) 0 = Fs n 0 0 := fun n => entryTwo_assemble _ _ _ 0
  have hprob : ∀ n, probInfo (entryTwo o t) ((entryTwo o t).assemble (Fs n)) 1 = ε n + ε n ^ 2 := by
    intro n
    rw [(hr _).2.2, hasm]
    simp [hFs]
  rcases hmem with rfl | rfl | rfl
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [] = 1 := by
      intro n
      unfold bayesBelief probInfo
      rw [show (entryTwo o t).info [] = 0 from rfl, hI.1]
      simp
    simp only [this, leftBelief]
    exact tendsto_const_nhds
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [1] =
        1 / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [1] = 1 from rfl, hprob, (hr _).1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    simp only [this, leftBelief]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
    simpa using this
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [2] =
        ε n / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [2] = 1 from rfl, hprob, (hr _).2.1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte]
      simp
      field_simp
    simp only [this, leftBelief]
    have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
      hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
    simpa using h

/-- **Figure 9.BB.2** (MWG, pp. 300-301). (out, fight if entry occurs) with beliefs putting
probability one on In₁ is a sequential equilibrium; but it is not extensive form
trembling-hand perfect: in every EFTHP the incumbent accommodates for sure. -/
theorem figure_9_BB_2 :
    IsSequentialEq fig9BB2 (pureMoves ![0, 0]) leftBelief ∧
    ∀ F, IsEFTHP fig9BB2 F → fig9BB2.assemble F 1 0 = 0 := by
  have hc := entryTwo_cont ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hr := entryTwo_reach ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hI := entryTwo_infoSet ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hB : IsBehaviorProfile fig9BB2 (pureMoves (I := Fin 2) ![0, 0]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [entryTwo]
  constructor
  · have hW : IsWeakPBE fig9BB2 (pureMoves ![0, 0]) leftBelief := by
      refine entryTwo_weakPBE_of _ _ hB (by simp [leftBelief]) (by simp [leftBelief])
        (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
      · norm_num [leftBelief, pureMoves, dirac]
      · norm_num [leftBelief, pureMoves, dirac]
      · intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
      · intro h
        simp [pureMoves, dirac] at h
    exact ⟨hB, hW.2.1, hW.2.2.1, entryTwo_consistent_leftBelief_zero _ _⟩
  · intro F hF
    refine isEFTHP_eq_zero_of_worse _ (entryTwo_noAbsentMindedness _ _) hF rfl
      (b := 1) (by simp [entryTwo]) (by simp [entryTwo]) fun Fp hTM => ?_
    have hpos : 0 < Fp 0 0 2 := hTM.2 0 0 rfl 2 (by simp [entryTwo])
    rw [hI.2, Finset.sum_insert (by decide), Finset.sum_singleton, (hr _).1, (hr _).2.1,
      entryTwo_assemble]
    simp [cont_unfold, entryTwo, entryTwoPay]
    linarith

/-- Payoffs `(u₁, u₂)` of Figure 9.BB.1: `R` gives `(2, 2)`; after `NR`, `(L, ℓ)` gives `(4, 1)`,
`(L, r)` gives `(1, 0)`, `(M, ℓ)` gives `(0, 0)` and `(M, r)` gives `(0, 1)`. -/
def bb1Pay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [1] then 2 else if z = [0, 0, 0] then ![4, 1] i else if z = [1, 0, 0] then ![1, 0] i
  else if z = [1, 1, 0] then ![0, 1] i else 0

/-- **Figure 9.BB.1** (MWG, p. 300; van Damme 1983). Player 1 (`0`) chooses `NR` (`0`) or `R`
(`1`) at information set `0`; after `NR` she chooses `L` (`0`) or `M` (`1`) at information set
`1`; player 2 (`1`), not observing that choice, chooses `ℓ` (`0`) or `r` (`1`) at information
set `2 = {[0, 0], [1, 0]}`. -/
def bb1Game : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 0, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bb1Pay

theorem bb1Game_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    bb1Game.assemble F 0 = F 0 0 ∧ bb1Game.assemble F 1 = F 0 1 ∧
      bb1Game.assemble F 2 = F 1 2 :=
  ⟨bb1Game.assemble_of_some _ rfl, bb1Game.assemble_of_some _ rfl,
    bb1Game.assemble_of_some _ rfl⟩

/-- Continuation payoffs in the game of Figure 9.BB.1. -/
theorem bb1Game_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont bb1Game f [0] i = f 1 0 * (f 2 0 * ![4, 1] i + f 2 1 * ![1, 0] i) +
      f 1 1 * (f 2 1 * ![0, 1] i) ∧
    cont bb1Game f [] i = f 0 0 * (f 1 0 * (f 2 0 * ![4, 1] i + f 2 1 * ![1, 0] i) +
      f 1 1 * (f 2 1 * ![0, 1] i)) + f 0 1 * 2 := by
  constructor <;> simp [cont_unfold, bb1Game, bb1Pay, Fin.sum_univ_two]

theorem bb1Game_decisionNodes : bb1Game.decisionNodes = {[], [0], [0, 0], [1, 0]} := by decide

/-- The subgames of Figure 9.BB.1 start at the initial node and at player 1's second decision
node. -/
theorem bb1Game_subgames (x : List (Fin 2)) : IsSubgameRoot bb1Game x ↔ x = [] ∨ x = [0] := by
  have hD : ∀ y, bb1Game.IsDecision y ↔ y = [] ∨ y = [0] ∨ y = [0, 0] ∨ y = [1, 0] := by
    intro y
    rw [← mem_decisionNodes, bb1Game_decisionNodes]
    simp
  constructor
  · intro hx
    rcases (hD x).1 hx.1 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hx.2.1 [1, 0] ((hD _).2 (by simp)) rfl) (by decide)
    · exact absurd (hx.2.1 [0, 0] ((hD _).2 (by simp)) rfl) (by decide)
  · rintro (rfl | rfl)
    · refine ⟨(hD _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd he (by decide)
    · refine ⟨(hD _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
          first | rfl | exact absurd he (by decide)
      · rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
          rcases (hD y').1 hy' with rfl | rfl | rfl | rfl <;>
          first | decide | exact absurd hxy (by decide) | exact absurd he (by decide)

theorem bb1Game_perfectRecall : bb1Game.PerfectRecall := by
  refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
  unfold ExtensiveForm.RecallFor
  fin_cases i <;> decide

/-- Playing `a` at information set `k` and following `F i` elsewhere. -/
theorem bb1Game_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bb1Game F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    bb1Game.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bb1Game]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- **Figure 9.BB.1** (MWG, p. 299). `((NR, L), ℓ)` is the unique subgame perfect Nash
equilibrium: it is an SPNE, and every SPNE (in behaviour strategies) plays `NR`, `L` and `ℓ` for
sure. -/
theorem figure_9_BB_1_spne :
    IsSPNE bb1Game (pureMoves ![0, 0, 0]) ∧ ∀ F, IsSPNE bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := by
  have hc := bb1Game_cont
  have hB : IsBehaviorProfile bb1Game (pureMoves (I := Fin 2) ![0, 0, 0]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hbeh : ∀ {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} {k : Fin 3},
      bb1Game.IsBehaviorStrategy i g → bb1Game.player k = some i →
      (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 := fun hg hk =>
    ⟨(hg _ hk).1, by simpa [bb1Game, Fin.sum_univ_two] using (hg _ hk).2.2⟩
  constructor
  · refine ⟨hB, fun x hx i g hg => ?_⟩
    have hA := bb1Game_assemble (Function.update (pureMoves ![0, 0, 0]) i g)
    have hA' := bb1Game_assemble (pureMoves ![0, 0, 0])
    have hi2 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases (bb1Game_subgames x).1 hx with rfl | rfl <;> rcases hi2 with rfl | rfl
    · obtain ⟨g0, g0s⟩ := hbeh hg (k := 0) rfl
      obtain ⟨g1, g1s⟩ := hbeh hg (k := 1) rfl
      rw [(hc _ _).2, (hc _ _).2, hA.1, hA.2.1, hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g0 0, g0 1, g1 0, g1 1, mul_nonneg (g0 0) (g1 1)]
    · obtain ⟨g2, g2s⟩ := hbeh hg (k := 2) rfl
      rw [(hc _ _).2, (hc _ _).2, hA.1, hA.2.1, hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g2 0, g2 1]
    · obtain ⟨g1, g1s⟩ := hbeh hg (k := 1) rfl
      rw [(hc _ _).1, (hc _ _).1, hA.2.1, hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g1 0, g1 1]
    · obtain ⟨g2, g2s⟩ := hbeh hg (k := 2) rfl
      rw [(hc _ _).1, (hc _ _).1, hA.2.1, hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g2 0, g2 1]
  · intro F hF
    have hA := bb1Game_assemble F
    obtain ⟨p0, p0s⟩ := hbeh (hF.1 0) (k := 0) rfl
    obtain ⟨p1, p1s⟩ := hbeh (hF.1 0) (k := 1) rfl
    obtain ⟨q, qs⟩ := hbeh (hF.1 1) (k := 2) rfl
    have hsub : IsSubgameRoot bb1Game [0] := (bb1Game_subgames _).2 (Or.inr rfl)
    have hroot : IsSubgameRoot bb1Game [] := (bb1Game_subgames _).2 (Or.inl rfl)
    -- player 1 plays `L` in the subgame
    have hL := hF.2 [0] hsub 0 _ (bb1Game_beh_update hF.1 0 1 0)
    have hAL := bb1Game_assemble (Function.update F 0 (Function.update (F 0) 1 (dirac 0)))
    rw [(hc _ _).1, (hc _ _).1, hAL.2.1, hAL.2.2, hA.2.1, hA.2.2] at hL
    simp [dirac] at hL
    have hpL : F 0 1 0 = 1 := by nlinarith [q 0, q 1, p1 0, p1 1]
    have hpM : F 0 1 1 = 0 := by linarith
    -- player 2 plays `ℓ`
    have hl := hF.2 [0] hsub 1 _ (bb1Game_beh_update hF.1 1 2 0)
    have hAl := bb1Game_assemble (Function.update F 1 (Function.update (F 1) 2 (dirac 0)))
    rw [(hc _ _).1, (hc _ _).1, hAl.2.1, hAl.2.2, hA.2.1, hA.2.2] at hl
    simp [dirac, hpL, hpM] at hl
    have hq : F 1 2 0 = 1 := by linarith [q 1]
    have hq' : F 1 2 1 = 0 := by linarith
    -- player 1 plays `NR`
    have hN := hF.2 [] hroot 0 _ (bb1Game_beh_update hF.1 0 0 0)
    have hAN := bb1Game_assemble (Function.update F 0 (Function.update (F 0) 0 (dirac 0)))
    rw [(hc _ _).2, (hc _ _).2, hAN.1, hAN.2.1, hAN.2.2, hA.1, hA.2.1, hA.2.2] at hN
    simp [dirac, hpL, hpM, hq, hq'] at hN
    have hNR : F 0 0 0 = 1 := by linarith [p0 1]
    have hNR' : F 0 0 1 = 0 := by linarith
    have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    intro k
    rcases hk3 k with rfl | rfl | rfl <;> funext a <;> fin_cases a <;>
      simp [hA, pureMoves, dirac, bb1Game_assemble, hNR, hNR', hpL, hpM, hq, hq']

/-- **Figure 9.BB.1** (MWG, p. 300). The unique extensive form trembling-hand perfect Nash
equilibrium is `((NR, L), ℓ)`: an EFTHP exists (`exists_isEFTHP`), and every EFTHP is subgame
perfect (`isSPNE_of_isEFTHP`), hence plays `NR`, `L` and `ℓ`. -/
theorem figure_9_BB_1_efthp :
    (∃ F, IsEFTHP bb1Game F ∧ ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k) ∧
    ∀ F, IsEFTHP bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := by
  have hN : NatureFullSupport bb1Game := fun k hk => absurd hk (by fin_cases k <;> simp [bb1Game])
  have huniq : ∀ F, IsEFTHP bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := fun F hF =>
    figure_9_BB_1_spne.2 F (isSPNE_of_isEFTHP _ bb1Game_perfectRecall hN hF)
  obtain ⟨F, hF⟩ := exists_isEFTHP bb1Game
  exact ⟨⟨F, hF, huniq F hF⟩, huniq⟩

/-- Player 1's payoffs in the normal form of Figure 9.BB.1; player 1's strategies are
`(NR, L)`, `(NR, M)`, `(R, L)`, `(R, M)` (`0, 1, 2, 3`) and player 2's are `ℓ`, `r` (`0, 1`). -/
def bb1U₁ (a : Fin 4) (b : Fin 2) : ℝ :=
  if a = 0 then (if b = 0 then 4 else 1) else if a = 1 then 0 else 2

/-- Player 2's payoffs in the normal form of Figure 9.BB.1. -/
def bb1U₂ (a : Fin 4) (b : Fin 2) : ℝ :=
  if a = 0 then (if b = 0 then 1 else 0) else if a = 1 then (if b = 0 then 0 else 1) else 2

/-- The normal form strategy of player 1 choosing `c₀` at the start and `c₁` after `NR`. -/
def bb1Row (c₀ c₁ : Fin 2) : Fin 4 :=
  if c₀ = 0 then (if c₁ = 0 then 0 else 1) else (if c₁ = 0 then 2 else 3)

/-- **Figure 9.BB.1** (MWG, p. 299). The normal form: the expected payoff of the pure profile
choosing `c k` at each information set is the bimatrix entry of player 1's strategy
`(c 0, c 1)` and player 2's `c 2`. -/
theorem bb1_normalForm (c : Fin 3 → Fin 2) (i : Fin 2) :
    cont bb1Game (bb1Game.assemble (pureMoves c)) [] i =
      (bimatrix bb1U₁ bb1U₂).payoff i (pp (bb1Row (c 0) (c 1)) (c 2)) := by
  have hA := bb1Game_assemble (pureMoves (I := Fin 2) c)
  rw [(bb1Game_cont _ _).2, hA.1, hA.2.1, hA.2.2]
  have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  simp only [pureMoves, dirac, bimatrix, pp_zero, pp_one, bb1Row, bb1U₁, bb1U₂]
  rcases h2 (c 0) with h0 | h0 <;> rcases h2 (c 1) with h1 | h1 <;>
    rcases h2 (c 2) with h3 | h3 <;> rcases h2 i with rfl | rfl <;>
    simp [h0, h1, h3]

/-- In the normal form of Figure 9.BB.1, a mixed strategy of player 1 giving at least `2`
against both `ℓ` and `r` puts no weight on `(NR, L)` and `(NR, M)`. -/
theorem bb1_row_two {x : Fin 4 → ℝ} (h0 : ∀ a, 0 ≤ x a) (h1 : ∑ a, x a = 1)
    (hr : 2 ≤ ∑ a, x a * bb1U₁ a 1) : x 0 = 0 ∧ x 1 = 0 := by
  simp only [Fin.sum_univ_four, bb1U₁] at h1 hr
  norm_num at hr
  constructor <;> linarith [h0 0, h0 1, h0 2, h0 3]

/-- **Figure 9.BB.1** (MWG, p. 299). The strategy profiles `((R, L), r)` and `((R, M), r)` are
normal form trembling-hand perfect Nash equilibria (of the normal form `bb1_normalForm`), though
not subgame perfect: each is a Nash equilibrium in which no player uses a weakly dominated
strategy (Chapter 8's two-player converse of Proposition 8.F.2). -/
theorem figure_9_BB_1_normalTHP (a : Fin 4) (ha : a = 2 ∨ a = 3) :
    IsTHP (bimatrix bb1U₁ bb1U₂) (pureProfile (pp a (1 : Fin 2))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  have hU : ∀ b, bb1U₁ a b = 2 ∧ bb1U₂ a b = 2 := by
    intro b; rcases ha with rfl | rfl <;> simp [bb1U₁, bb1U₂]
  have hNE : IsNashEquilibrium (bimatrix bb1U₁ bb1U₂) (pp a (1 : Fin 2)) :=
    (bimatrix_isNash_iff _ _ _ _).2 ⟨fun a' => by
      rw [(hU 1).1]; fin_cases a' <;> norm_num [bb1U₁], fun b' => by
      rw [(hU 1).2, (hU b').2]⟩
  refine isTHP_of_not_weaklyDominated_two _ h01 htwo ((corollary_8_D_1 _ _).1 hNE) fun k => ?_
  rintro ⟨τ', hτ', hdom⟩
  obtain ⟨hle, s, hlt⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom
  have hU1 : ∀ b : S2 4 2 1, bb1U₁ a b = 2 := fun b => (hU b).1
  rcases htwo k with rfl | rfl
  · set x : Fin 4 → ℝ := τ' with hx
    have h0 : ∀ b : Fin 4, 0 ≤ x b := hτ'.1
    have h2 : ∑ b : Fin 4, x b = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 4 2 i,
        (bimatrix bb1U₁ bb1U₂).mixedPayoff
          (Function.update (pureProfile s') 0 (pureProfile (pp a (1 : Fin 2)) 0)) 0 =
        bb1U₁ a (s' 1) := fun s' => by
      rw [show pureProfile (pp a (1 : Fin 2)) 0 = pureMixed (pp a (1 : Fin 2) 0) from rfl,
        mixedPayoff_pureProfile_update]
      simp [bimatrix, Function.update]
    have e1 : 2 ≤ ∑ b, x b * bb1U₁ b 1 := by
      have := hle (pp 0 1)
      rwa [hL, bimatrix_mixed_vs_pure_zero, hU1] at this
    obtain ⟨hx0, hx1⟩ := bb1_row_two h0 h2 e1
    rw [hL, bimatrix_mixed_vs_pure_zero, hU1] at hlt
    simp only [Fin.sum_univ_four, Fin.sum_univ_four] at hlt h2
    rw [← hx, hx0, hx1] at hlt
    have hb : ∀ b : S2 4 2 1, bb1U₁ 2 b = 2 ∧ bb1U₁ 3 b = 2 := fun b => by simp [bb1U₁]
    rw [(hb _).1, (hb _).2] at hlt
    linarith
  · set y : Fin 2 → ℝ := τ' with hy
    have h0 : ∀ b : Fin 2, 0 ≤ y b := hτ'.1
    have h2 : ∑ b : Fin 2, y b = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 4 2 i,
        (bimatrix bb1U₁ bb1U₂).mixedPayoff
          (Function.update (pureProfile s') 1 (pureProfile (pp a (1 : Fin 2)) 1)) 1 =
        bb1U₂ (s' 0) 1 := fun s' => by
      rw [show pureProfile (pp a (1 : Fin 2)) 1 = pureMixed (pp a (1 : Fin 2) 1) from rfl,
        mixedPayoff_pureProfile_update]
      simp [bimatrix, Function.update]
    have e1 : bb1U₂ 1 1 ≤ ∑ b, y b * bb1U₂ 1 b := by
      have := hle (pp 1 0)
      rwa [hL, bimatrix_mixed_vs_pure_one] at this
    simp only [Fin.sum_univ_two, bb1U₂] at e1 h2
    norm_num at e1
    have hy1 : y 1 = 1 := by linarith [h0 0]
    have hy0 : y 0 = 0 := by linarith
    rw [hL, bimatrix_mixed_vs_pure_one] at hlt
    simp only [Fin.sum_univ_two] at hlt
    rw [← hy, hy0, hy1] at hlt
    simp at hlt

end MWG.DynamicGames
