/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Trembling
import MWGDynamicGames.Further

/-!
# Forward induction: equilibrium domination and sequential equilibria

MWG, Section 9.D, footnote 15 and Figure 9.D.2 (pp. 292-294).

* `footnote_15_D_1a`, `footnote_15_D_1b`: the weak PBE of Figures 9.D.1(a) and 9.D.1(b) are
  sequential equilibria (E trembles to the dominated entry strategy with probability `ε` and to
  the other with `ε²`).
* `fig9D2`, `figure_9_D_2`: in the Niche Choice variant of Figure 9.D.2 (the incumbent also
  moves after "out"), E staying out, I playing `R` after "out" and the large niche after entry,
  with I believing E chose the small niche, is a weak PBE and a sequential equilibrium; "small
  niche" is no longer strictly dominated by "out" (against `L` after "out" and the large niche
  after entry it gives `−1 > −10`), but it is **equilibrium dominated**: whatever I does after
  entry it gives at most `−1 < 0`, E's equilibrium payoff.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(a) (E out, I fights, belief on
In₁) is a sequential equilibrium. -/
theorem footnote_15_D_1a : IsSequentialEq fig9D1a (pureMoves ![0, 0]) leftBelief :=
  ⟨figure_9_D_1a.1.1, figure_9_D_1a.1.2.1, figure_9_D_1a.1.2.2.1,
    entryTwo_consistent_leftBelief_zero _ _⟩

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(b) (E out, I targets the large
niche, belief on the small niche) is a sequential equilibrium. -/
theorem footnote_15_D_1b : IsSequentialEq fig9D1b (pureMoves ![0, 1]) leftBelief :=
  ⟨figure_9_D_1b.1.1, figure_9_D_1b.1.2.1, figure_9_D_1b.1.2.2.1,
    entryTwo_consistent_leftBelief_one _ _⟩

/-- Payoffs `(u_E, u_I)` of Figure 9.D.2. -/
def fig9D2Pay (i : Fin 2) (z : List (Fin 3)) : ℝ :=
  if z = [0, 0] then ![-10, -10] i else if z = [1, 0] then ![0, 2] i
  else if z = [0, 1] then ![-6, -6] i else if z = [1, 1] then ![-1, 1] i
  else if z = [0, 2] then ![1, -1] i else if z = [1, 2] then ![-3, -3] i else 0

/-- **Figure 9.D.2** (MWG, p. 294). E chooses Out (`0`), Small niche (`1`) or Large niche (`2`);
after Out, I chooses `L` (`0`) or `R` (`1`) (information set `1`); after entry I, not observing
the niche, chooses Small (`0`) or Large (`1`) (information set `2 = {[1], [2]}`). -/
def fig9D2 : ExtensiveForm (Fin 2) (Fin 3) (Fin 3) where
  nodes := {[], [0], [1], [2], [0, 0], [1, 0], [0, 1], [1, 1], [0, 2], [1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := fig9D2Pay

theorem fig9D2_assemble (F : Fin 2 → Fin 3 → Fin 3 → ℝ) :
    fig9D2.assemble F 0 = F 0 0 ∧ fig9D2.assemble F 1 = F 1 1 ∧ fig9D2.assemble F 2 = F 1 2 :=
  ⟨fig9D2.assemble_of_some _ rfl, fig9D2.assemble_of_some _ rfl, fig9D2.assemble_of_some _ rfl⟩

theorem fig9D2_cont (f : Fin 3 → Fin 3 → ℝ) (i : Fin 2) :
    cont fig9D2 f [0] i = f 1 0 * ![-10, -10] i + f 1 1 * ![0, 2] i ∧
    cont fig9D2 f [1] i = f 2 0 * ![-6, -6] i + f 2 1 * ![-1, 1] i ∧
    cont fig9D2 f [2] i = f 2 0 * ![1, -1] i + f 2 1 * ![-3, -3] i ∧
    cont fig9D2 f [] i = f 0 0 * (f 1 0 * ![-10, -10] i + f 1 1 * ![0, 2] i) +
      f 0 1 * (f 2 0 * ![-6, -6] i + f 2 1 * ![-1, 1] i) +
      f 0 2 * (f 2 0 * ![1, -1] i + f 2 1 * ![-3, -3] i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, fig9D2, fig9D2Pay, Fin.sum_univ_three]

theorem fig9D2_infoSet : fig9D2.infoSet 0 = {[]} ∧ fig9D2.infoSet 1 = {[0]} ∧
    fig9D2.infoSet 2 = {[1], [2]} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem fig9D2_reach (f : Fin 3 → Fin 3 → ℝ) :
    fig9D2.reach f [0] = f 0 0 ∧ fig9D2.reach f [1] = f 0 1 ∧ fig9D2.reach f [2] = f 0 2 ∧
    probInfo fig9D2 f 0 = 1 ∧ probInfo fig9D2 f 1 = f 0 0 ∧
    probInfo fig9D2 f 2 = f 0 1 + f 0 2 := by
  obtain ⟨h0, h1, h2⟩ := fig9D2_infoSet
  refine ⟨by simp [fig9D2], by simp [fig9D2], by simp [fig9D2], ?_, ?_, ?_⟩ <;> unfold probInfo
  · rw [h0]; simp
  · rw [h1]; simp [fig9D2]
  · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [fig9D2]

theorem fig9D2_condPayoff (f : Fin 3 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 2) :
    condPayoff fig9D2 f μ 0 i = μ [] * cont fig9D2 f [] i ∧
    condPayoff fig9D2 f μ 1 i = μ [0] * cont fig9D2 f [0] i ∧
    condPayoff fig9D2 f μ 2 i = μ [1] * cont fig9D2 f [1] i + μ [2] * cont fig9D2 f [2] i := by
  obtain ⟨h0, h1, h2⟩ := fig9D2_infoSet
  unfold condPayoff
  rw [h0, h1, h2]
  refine ⟨by simp, by simp, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **Figure 9.D.2** (MWG, pp. 293-294). E staying out, I playing `R` after "out" and the large
niche after entry, with I believing E chose the small niche, is a weak perfect Bayesian
equilibrium and a sequential equilibrium. "Small niche" is not strictly dominated by "out"
(if I plays `L` after "out" and the large niche after entry, "small niche" gives `−1` and
"out" gives `−10`), but it is equilibrium dominated: whatever I does after entry, "small
niche" gives E at most `−1 < 0`, E's equilibrium payoff. -/
theorem figure_9_D_2 :
    IsWeakPBE fig9D2 (pureMoves ![0, 1, 1]) leftBelief ∧
    IsSequentialEq fig9D2 (pureMoves ![0, 1, 1]) leftBelief ∧
    cont fig9D2 (fig9D2.assemble (pureMoves ![0, 0, 1])) [0] 0 <
      cont fig9D2 (fig9D2.assemble (pureMoves ![0, 0, 1])) [1] 0 ∧
    cont fig9D2 (fig9D2.assemble (pureMoves ![0, 1, 1])) [] 0 = 0 ∧
    ∀ f : Fin 3 → Fin 3 → ℝ, (∀ a, 0 ≤ f 2 a) → f 2 0 + f 2 1 = 1 →
      cont fig9D2 f [1] 0 ≤ -1 := by
  obtain ⟨hI0, hI1, hI2⟩ := fig9D2_infoSet
  have hc := fig9D2_cont
  have hcp := fig9D2_condPayoff
  have hr := fig9D2_reach
  have hB : IsBehaviorProfile fig9D2 (pureMoves (I := Fin 2) ![0, 1, 1]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [fig9D2]
  have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hW : IsWeakPBE fig9D2 (pureMoves ![0, 1, 1]) leftBelief := by
    have hA := fig9D2_assemble (pureMoves ![0, 1, 1])
    refine ⟨hB, ⟨fun x _ => ?_, fun k => ?_⟩, fun k i hi g hg => ?_, fun k hk x hx => ?_⟩
    · unfold leftBelief; split_ifs <;> norm_num
    · rcases hk3 k with rfl | rfl | rfl
      · simp [hI0, leftBelief]
      · simp [hI1, leftBelief]
      · rw [hI2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [leftBelief]
    · have hA' := fig9D2_assemble (Function.update (pureMoves ![0, 1, 1]) i g)
      rcases hk3 k with rfl | rfl | rfl
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 0 rfl).1
        have h1 := (hg 0 rfl).2.2
        simp only [fig9D2, Fin.sum_univ_three, ↓reduceIte] at h1
        rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2, (hc _ _).2.2.2, hA.1, hA.2.1,
          hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 1 rfl).1
        have h1 := (hg 1 rfl).2.2
        simp [fig9D2] at h1
        rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).1, (hc _ _).1, hA.2.1, hA'.2.1]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 2 rfl).1
        have h1 := (hg 2 rfl).2.2
        simp [fig9D2] at h1
        rw [(hcp _ _ _).2.2, (hcp _ _ _).2.2, (hc _ _).2.1, (hc _ _).2.1, (hc _ _).2.2.1,
          (hc _ _).2.2.1, hA.2.2, hA'.2.2]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1]
    · rcases hk3 k with rfl | rfl | rfl
      · rw [hI0, Finset.mem_singleton] at hx
        subst hx
        rw [(hr _).2.2.2.1]
        simp [leftBelief]
      · rw [hI1, Finset.mem_singleton] at hx
        subst hx
        rw [(hr _).2.2.2.2.1, (hr _).1]
        simp [hA.1, pureMoves, dirac, leftBelief]
      · rw [(hr _).2.2.2.2.2, hA.1] at hk
        simp [pureMoves, dirac] at hk
  refine ⟨hW, ⟨hB, hW.2.1, hW.2.2.1, ?_⟩, ?_, ?_, fun f hf0 hf1 => ?_⟩
  · -- trembles: E plays Small with probability `ε` and Large with `ε²`; I deviates with `ε`
    set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
    have hε0 : ∀ n, 0 < ε n := fun n => by positivity
    have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
      simp only [hε]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    set Fs : ℕ → Fin 2 → Fin 3 → Fin 3 → ℝ := fun n _ k =>
      if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
    have hTM : ∀ n, IsTotallyMixedB fig9D2 (Fs n) := by
      intro n
      have e0 := hε0 n
      have e1 := hε1 n
      have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
      refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
      · rcases hk3 k with rfl | rfl | rfl
        · refine ⟨fun a => ?_, fun a ha => absurd (by simp [fig9D2]) ha, ?_⟩
          · fin_cases a <;> simp [hFs] <;> nlinarith
          · simp [hFs, fig9D2, Fin.sum_univ_three]
            ring
        all_goals
          refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
          · fin_cases a <;> simp [hFs] <;> linarith
          · have : a = 2 := by
              fin_cases a <;> simp [fig9D2] at ha ⊢
            subst this
            simp [hFs]
          · simp [hFs, fig9D2]
      · rcases hk3 k with rfl | rfl | rfl
        · fin_cases a <;> simp [hFs] <;> nlinarith
        all_goals fin_cases a <;> simp [hFs, fig9D2] at ha ⊢ <;> linarith
    have hlimε : Tendsto ε atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp only [hε, Nat.cast_add, Nat.cast_one]
      ring
    have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1, 1])) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
      have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
        simpa using hlimε.pow 2
      rcases hk3 k with rfl | rfl | rfl
      · fin_cases a
        · simpa [hFs, pureMoves, dirac] using
            ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
        · simpa [hFs, pureMoves, dirac] using hlimε
        · simpa [hFs, pureMoves, dirac] using hsq
      all_goals
        fin_cases a
        · simpa [hFs, pureMoves, dirac] using hlimε
        · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
        · simp [hFs, pureMoves, dirac]
    refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
    have hmem := (mem_decisionNodes _).2 hx
    rw [show fig9D2.decisionNodes = {[], [0], [1], [2]} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hasm : ∀ n, fig9D2.assemble (Fs n) 0 = Fs n 0 0 := fun n => (fig9D2_assemble _).1
    have hprob : ∀ n, probInfo fig9D2 (fig9D2.assemble (Fs n)) 2 = ε n + ε n ^ 2 := by
      intro n
      rw [(hr _).2.2.2.2.2, hasm]
      simp [hFs]
    rcases hmem with rfl | rfl | rfl | rfl
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [] = 1 := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [] = 0 from rfl, (hr _).2.2.2.1]
        simp
      simp only [this, leftBelief]
      exact tendsto_const_nhds
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [0] = 1 := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [0] = 1 from rfl, (hr _).2.2.2.2.1, (hr _).1, hasm]
        have : Fs n 0 0 0 ≠ 0 := by
          have := hε1 n
          have := hε0 n
          simp only [hFs, ↓reduceIte, Matrix.cons_val_zero]
          nlinarith
        field_simp
      simp only [this, leftBelief]
      exact tendsto_const_nhds
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [1] = 1 / (1 + ε n) := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [1] = 2 from rfl, hprob, (hr _).2.1, hasm]
        have := hε0 n
        simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        field_simp
      simp only [this, leftBelief]
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
      simpa using this
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [2] = ε n / (1 + ε n) := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [2] = 2 from rfl, hprob, (hr _).2.2.1, hasm]
        have := hε0 n
        simp only [hFs, ↓reduceIte]
        simp
        field_simp
      simp only [this, leftBelief]
      have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
        hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
      simpa using h
  · have hA := fig9D2_assemble (pureMoves ![0, 0, 1])
    rw [(hc _ _).1, (hc _ _).2.1, hA.2.1, hA.2.2]
    norm_num [pureMoves, dirac]
  · have hA := fig9D2_assemble (pureMoves ![0, 1, 1])
    rw [(hc _ _).2.2.2, hA.1, hA.2.1, hA.2.2]
    norm_num [pureMoves, dirac]
  · rw [(hc _ _).2.1]
    simp
    nlinarith [hf0 0, hf0 1]

end MWG.DynamicGames
