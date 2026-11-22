/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.ForwardInduction

/-!
# Footnote 15: the forward induction examples are extensive form trembling-hand perfect

MWG, Section 9.D, footnote 15 (p. 292), with Appendix B (pp. 299-300).

* `isEFTHP_pureMoves_of`: a sufficient condition for extensive form trembling-hand perfection
  of a pure profile `c` (in a game without absent-mindedness): a sequence of totally mixed
  behaviour profiles converging to `c` against which, at every personal information set, the
  sure move `c k` is a best reply of the agent there. (The agent normal form profiles built from
  the sequence are totally mixed, converge to `c`, and `c` is a best response to each, so
  Proposition 8.F.1 applies; the limit is a Nash equilibrium of the agent normal form by
  continuity.)
* `footnote_15_D_1a_EFTHP`, `footnote_15_D_1b_EFTHP`, `footnote_15_D_2_EFTHP`: the weak PBE of
  Figures 9.D.1(a), 9.D.1(b) and 9.D.2 are extensive form trembling-hand perfect. Trembles: E
  plays the entry strategy that I's beliefs favour with probability `ε`, the other with `ε²`;
  each agent of I plays its other action with probability `ε`, where `ε = 1/(n + 5)`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] in
/-- **Appendix B** (MWG, pp. 299-300). A sufficient condition for extensive form trembling-hand
perfection. In a game without absent-mindedness, the sure choice `c` is an extensive form
trembling-hand perfect Nash equilibrium if there are totally mixed behaviour profiles `Fsⁿ`
whose moves converge to those of `c` and against which, for every `n` and every personal
information set `k` of player `i`, playing `c k` for sure at `k` is at least as good for `i` as
playing any other available action `b` for sure at `k`. -/
theorem isEFTHP_pureMoves_of [Fintype H] (hNA : G.NoAbsentMindedness) {c : H → A}
    (hc : ∀ k, c k ∈ G.avail k) (Fs : ℕ → I → H → A → ℝ)
    (hTM : ∀ n, IsTotallyMixedB G (Fs n))
    (hlim : ∀ i k, G.player k = some i → ∀ a,
      Tendsto (fun n => Fs n i k a) atTop (𝓝 (dirac (c k) a)))
    (hbest : ∀ n i k, G.player k = some i → ∀ b ∈ G.avail k,
      cont G (Function.update (G.assemble (Fs n)) k (dirac b)) [] i ≤
        cont G (Function.update (G.assemble (Fs n)) k (dirac (c k))) [] i) :
    IsEFTHP G (pureMoves (I := I) c) := by
  set ρ : ℕ → (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ :=
    fun n ag s => Fs n (owner G ag) ag.1 ((agentEquiv G ag).symm s).1 with hρ
  set σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ :=
    fun ag => pureMixed (agentPure G ag ⟨c ag.1, hc ag.1⟩) with hσ
  have hown : ∀ ag : Agent G, G.player ag.1 = some (owner G ag) := player_owner G
  -- the agent profiles assemble to the given behaviour profiles
  have hA : ∀ n, G.assemble (agentProfile G (ρ n)) = G.assemble (Fs n) := by
    intro n
    funext k a
    cases hk : G.player k with
    | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
    | some i =>
      have hne : G.player k ≠ none := by rw [hk]; simp
      have hi : owner G ⟨k, hne⟩ = i := by
        have := hown ⟨k, hne⟩
        rw [hk] at this
        exact (Option.some.inj this).symm
      have h1 := assemble_agentProfile_apply G (ρ n) ⟨k, hne⟩ a
      rw [h1, G.assemble_of_some _ hk]
      split_ifs with ha
      · simp only [hρ, hi]
        rfl
      · exact (((hTM n).1 i k hk).2.1 a ha).symm
  -- the agent profiles are totally mixed
  have hρpos : ∀ n ag s, 0 < ρ n ag s := fun n ag s =>
    (hTM n).2 _ _ (hown ag) _ ((agentEquiv G ag).symm s).2
  have hρsum : ∀ n ag, ∑ s, ρ n ag s = 1 := by
    intro n ag
    have h1 := ((hTM n).1 (owner G ag) ag.1 (hown ag)).2.2
    rw [← Finset.sum_coe_sort] at h1
    rw [← h1, ← Equiv.sum_comp (agentEquiv G ag)]
    rfl
  have hρmix : ∀ n ag, IsMixedStrategy (ρ n ag) := fun n ag =>
    ⟨fun s => (hρpos n ag s).le, hρsum n ag⟩
  -- the value of `σ` at the pure strategy of an action
  have hσval : ∀ ag (a : {a // a ∈ G.avail ag.1}),
      σ ag (agentEquiv G ag a) = dirac (c ag.1) a.1 := by
    intro ag a
    by_cases h : a.1 = c ag.1
    · have : a = ⟨c ag.1, hc ag.1⟩ := Subtype.ext h
      subst this
      change pureMixed _ (agentPure G ag _) = _
      simp [pureMixed, dirac]
    · have hne : agentEquiv G ag a ≠ agentPure G ag ⟨c ag.1, hc ag.1⟩ := fun he =>
        h (congrArg Subtype.val ((agentEquiv G ag).injective he))
      simp only [hσ, pureMixed, dirac, hne, h, ↓reduceIte]
  have hρlim : Tendsto ρ atTop (𝓝 σ) := by
    refine tendsto_pi_nhds.2 fun ag => tendsto_pi_nhds.2 fun s => ?_
    obtain ⟨a, rfl⟩ := (agentEquiv G ag).surjective s
    rw [hσval]
    exact hlim _ _ (hown ag) a.1
  -- `c` is a best reply of every agent against every `ρ n`
  have hpay : ∀ n ag (b : (agentForm G).PureStrategy ag),
      (agentNF G).mixedPayoff (Function.update (ρ n) ag (pureMixed b)) ag ≤
        (agentNF G).mixedPayoff (Function.update (ρ n) ag (σ ag)) ag := by
    intro n ag b
    obtain ⟨⟨b, hb⟩, rfl⟩ := (agentEquiv G ag).surjective b
    have hmixU : ∀ s, ∀ ag', IsMixedStrategy (Function.update (ρ n) ag (pureMixed s) ag') := by
      intro s ag'
      by_cases h : ag' = ag
      · subst h
        rw [Function.update_self]
        exact isMixedStrategy_pureMixed s
      · rw [Function.update_of_ne h]
        exact hρmix n ag'
    have e1 : agentEquiv G ag ⟨b, hb⟩ = agentPure G ag ⟨b, hb⟩ := rfl
    rw [e1, hσ, agentNF_mixedPayoff G hNA (hmixU _), agentNF_mixedPayoff G hNA (hmixU _),
      assemble_agentProfile_update G _ ag hb, assemble_agentProfile_update G _ ag (hc ag.1),
      hA n]
    exact hbest n _ _ (hown ag) b hb
  have hsupp : ∀ ag (a : (agentForm G).PureStrategy ag), 0 < σ ag a →
      pureMixed a = σ ag := by
    intro ag a ha
    simp only [hσ, pureMixed] at ha ⊢
    split_ifs at ha with h
    · rw [h]
    · exact absurd ha (lt_irrefl 0)
  have hbr : ∀ n ag, IsBestResponse (agentNF G) ag (σ ag) (ρ n) := by
    intro n ag
    refine (isBestResponse_iff_support _ ag (isMixedStrategy_pureMixed _) _).2
      fun a ha b => ?_
    rw [hsupp ag a ha]
    exact hpay n ag b
  -- the limit `σ` is a Nash equilibrium of the agent normal form
  have hσmix : IsMixedProfile σ := fun ag => isMixedStrategy_pureMixed _
  have hNash : IsMixedNash (agentNF G) σ := by
    refine (isMixedNash_iff_bestResponse _ σ).2 ⟨hσmix, fun ag => ?_⟩
    refine (isBestResponse_iff_support _ ag (hσmix ag) _).2 fun a ha b => ?_
    rw [hsupp ag a ha]
    exact le_of_tendsto_of_tendsto'
      (tendsto_mixedPayoff_update _ ag hρlim tendsto_const_nhds)
      (tendsto_mixedPayoff_update _ ag hρlim tendsto_const_nhds) fun n => hpay n ag b
  have hTHP : IsTHP (agentNF G) σ :=
    (proposition_8_F_1 _ hNash).2 ⟨ρ, fun n ag => ⟨hρmix n ag, hρpos n ag⟩, hρlim, hbr⟩
  refine ⟨isBehaviorProfile_pureMoves hc, σ, hTHP, fun k hk => ?_⟩
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hk
  funext a
  rw [G.assemble_of_some _ hi]
  have h1 := assemble_agentProfile_apply G σ ⟨k, hk⟩ a
  rw [h1]
  split_ifs with ha
  · exact (hσval ⟨k, hk⟩ ⟨a, ha⟩).symm
  · have : a ≠ c k := fun h => ha (h ▸ hc k)
    simp [pureMoves, dirac, this]

/-- The trembles `ε n = 1/(n + 5)`. -/
noncomputable def fwdTremble (n : ℕ) : ℝ := 1 / ((n : ℝ) + 5)

theorem fwdTremble_pos (n : ℕ) : 0 < fwdTremble n := by
  unfold fwdTremble
  positivity

theorem fwdTremble_le (n : ℕ) : fwdTremble n ≤ 1 / 5 := by
  unfold fwdTremble
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem tendsto_fwdTremble : Tendsto fwdTremble atTop (𝓝 0) := by
  refine squeeze_zero (fun n => (fwdTremble_pos n).le) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold fwdTremble
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(a) (E out, I fights after
entry) is extensive form trembling-hand perfect. E trembles to In₁ with probability `ε` and to
In₂ with probability `ε²`, I accommodates with probability `ε`: fighting is then a best reply
of I (it is better at In₁, which is twice as likely as In₂ up to `ε ≤ 1/2`), and Out is a best
reply of E (In₁ gives `−3 + 4ε` and In₂ gives `−2 + 5ε`, both `≤ 0` for `ε ≤ 1/5`). -/
theorem footnote_15_D_1a_EFTHP : IsEFTHP fig9D1a (pureMoves ![0, 0]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![1 - ε n, ε n, 0] with hFs
  have hc := entryTwo_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  refine isEFTHP_pureMoves_of _ (entryTwo_noAbsentMindedness _ _)
    (fun k => by fin_cases k <;> simp [entryTwo]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
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
  · intro i k hk a
    obtain rfl : k = i := Option.some.inj hk
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    obtain rfl : k = i := Option.some.inj hk
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      fin_cases b <;> simp [entryTwo_assemble, hFs, dirac] <;> nlinarith
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [entryTwo] at hb ⊢
      rcases this with rfl | rfl
      · simp
      · simp [entryTwo_assemble, hFs, dirac]
        nlinarith

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(b) (E out, I targets the large
niche) is extensive form trembling-hand perfect. E trembles to the small niche with probability
`ε` and to the large niche with probability `ε²`, I targets the small niche with probability
`ε`: the large niche is then a best reply of I (`7ε − 2ε² ≥ 0`), and Out is a best reply of E
(the small niche gives `−1 − 5ε` and the large niche `−3 + 4ε`). -/
theorem footnote_15_D_1b_EFTHP : IsEFTHP fig9D1b (pureMoves ![0, 1]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
  have hc := entryTwo_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  refine isEFTHP_pureMoves_of _ (entryTwo_noAbsentMindedness _ _)
    (fun k => by fin_cases k <;> simp [entryTwo]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
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
  · intro i k hk a
    obtain rfl : k = i := Option.some.inj hk
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    obtain rfl : k = i := Option.some.inj hk
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      fin_cases b <;> simp [entryTwo_assemble, hFs, dirac] <;> nlinarith
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [entryTwo] at hb ⊢
      rcases this with rfl | rfl
      · simp [entryTwo_assemble, hFs, dirac]
        nlinarith
      · simp

/-- **Footnote 15** (MWG, p. 292), for **Figure 9.D.2** (p. 294). The weak PBE of Figure 9.D.2
(E out, I plays `R` after "out" and the large niche after entry) is extensive form
trembling-hand perfect. E trembles to the small niche with probability `ε` and to the large
niche with probability `ε²`; each agent of I plays its other action with probability `ε`. Out
gives E `−10ε`, the small niche `−1 − 5ε` and the large niche `−3 + 4ε`, so Out is a best reply
for `ε ≤ 1/5`. -/
theorem footnote_15_D_2_EFTHP : IsEFTHP fig9D2 (pureMoves ![0, 1, 1]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 3 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
  have hc := fig9D2_cont
  have hNA : fig9D2.NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness
    decide
  refine isEFTHP_pureMoves_of _ hNA
    (fun k => by fin_cases k <;> simp [fig9D2]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · fin_cases k
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
    · fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      all_goals fin_cases a <;> simp [hFs, fig9D2] at ha ⊢ <;> linarith
  · intro i k hk a
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · obtain rfl : i = 0 := (Option.some.inj (hk : some 0 = some i)).symm
      rw [(hc _ _).2.2.2, (hc _ _).2.2.2]
      fin_cases b <;> simp [fig9D2_assemble, hFs, dirac] <;> nlinarith
    all_goals
      obtain rfl : i = 1 := (Option.some.inj (hk : some 1 = some i)).symm
      rw [(hc _ _).2.2.2, (hc _ _).2.2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [fig9D2] at hb ⊢
      rcases this with rfl | rfl
      · simp [fig9D2_assemble, hFs, dirac]
        nlinarith
      · simp

end MWG.DynamicGames
