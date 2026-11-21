/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.AgentForm
import MWGDynamicGames.OneShot
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

/-!
# Extensive form trembling-hand perfection implies sequential equilibrium; existence

MWG, Appendix B of Chapter 9, p. 300: "every extensive form trembling-hand perfect Nash
equilibrium is a sequential equilibrium". Since every finite game has an extensive form
trembling-hand perfect equilibrium (Selten), sequential equilibria exist, and with
Proposition 9.C.2 so do subgame perfect Nash equilibria (Exercise 9.B.8).

* `isSequentialEq_of_isEFTHP`: in a game with perfect recall in which nature's moves have full
  support, the strategies of an extensive form trembling-hand perfect equilibrium, with beliefs
  that are a limit of the Bayes beliefs along (a subsequence of) its trembling sequence, form a
  sequential equilibrium. In the perturbed agent games each agent's equilibrium move is optimal
  given the Bayes beliefs (`agent_best_iff`); in the limit no move at a single information set
  is profitable, and the one-shot deviation principle for consistent assessments
  (`oneShot_consistent`) gives sequential rationality.
* `exists_isSequentialEq` (existence of sequential equilibrium, Kreps and Wilson 1982),
  `isSPNE_of_isEFTHP` (every EFTHP is subgame perfect, p. 300) and `exercise_9_B_8` (every
  finite game, here with perfect recall and full-support moves of nature, has a mixed strategy
  SPNE).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] [DecidableEq H] in
/-- Continuation payoffs depend continuously on the profile. -/
theorem tendsto_cont {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (x : List A) (i : I) :
    Tendsto (fun n => cont G (G.assemble (Fs n)) x i) atTop
      (𝓝 (cont G (G.assemble F) x i)) := by
  unfold cont
  exact tendsto_finsetSum _ fun z _ => (tendsto_reachFrom G h x z).mul tendsto_const_nhds

omit [DecidableEq I] in
/-- Without absent-mindedness, the entry nodes of the single information set `k` are its
nodes. -/
theorem entryNodes_single (hNA : G.NoAbsentMindedness) (k : H) :
    entryNodes G (fun k' => k' = k) [] = G.infoSet k := by
  ext x
  rw [mem_entryNodes, mem_infoSet]
  constructor
  · rintro ⟨hx, -, hk, -⟩
    exact ⟨hx, hk⟩
  · rintro ⟨hx, hk⟩
    refine ⟨hx, List.nil_suffix, hk, fun w hw _ hwx hne hwk => hne ?_⟩
    exact eq_of_absentMinded G hNA hw hx (by rw [hwk, hk]) hwx

omit [DecidableEq I] in
/-- Without absent-mindedness, replacing the move at `H(x)` by a sure move `c` makes the
continuation from `x` that from `c :: x`. -/
theorem cont_update_dirac (hNA : G.NoAbsentMindedness) (f : H → A → ℝ) {x : List A}
    (hx : G.IsDecision x) {c : A} (hc : c ∈ G.avail (G.info x)) (i : I) :
    cont G (Function.update f (G.info x) (dirac c)) x i = cont G f (c :: x) i := by
  rw [cont_decision _ _ hx, Function.update_self]
  simp only [dirac, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (G.avail (G.info x))]
  simp only [hc, ↓reduceIte]
  refine cont_congr G (fun y hy hcy => ?_) i
  have hne : G.info y ≠ G.info x := fun he => by
    have := eq_of_absentMinded G hNA hx hy he.symm ((List.suffix_cons c x).trans hcy)
    subst this
    have := hcy.length_le
    simp at this
  rw [Function.update_of_ne hne]

omit [DecidableEq I] in
/-- **Agent best responses and beliefs.** With sure moves `a, b` at information set `k`, the
payoff difference of the mover is `∑_{x ∈ k} P(x) (cont(a :: x) − cont(b :: x))`. -/
theorem cont_update_dirac_sub (hNA : G.NoAbsentMindedness) (f : H → A → ℝ) (k : H) {a b : A}
    (ha : a ∈ G.avail k) (hb : b ∈ G.avail k) (i : I) :
    cont G (Function.update f k (dirac a)) [] i - cont G (Function.update f k (dirac b)) [] i =
      ∑ x ∈ G.infoSet k, G.reach f x * (cont G f (a :: x) i - cont G f (b :: x) i) := by
  have hoff : ∀ c, ∀ k', ¬ (fun k'' => k'' = k) k' →
      f k' = Function.update f k (dirac c) k' := fun c k' hk' => by
    rw [Function.update_of_ne hk']
  have h1 := cont_sub_eq_sum_entry G (fun k' => k' = k) (hoff a) G.nil_mem i
  have h2 := cont_sub_eq_sum_entry G (fun k' => k' = k) (hoff b) G.nil_mem i
  rw [entryNodes_single G hNA] at h1 h2
  have hc : ∀ c ∈ G.avail k, ∀ x ∈ G.infoSet k,
      cont G (Function.update f k (dirac c)) x i = cont G f (c :: x) i := by
    intro c hc x hx
    obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
    rw [← hxk]
    exact cont_update_dirac G hNA f hxd (by rw [hxk]; exact hc) i
  rw [Finset.sum_congr rfl fun x hx => by rw [hc a ha x hx, reachFrom_nil]] at h1
  rw [Finset.sum_congr rfl fun x hx => by rw [hc b hb x hx, reachFrom_nil]] at h2
  have : cont G (Function.update f k (dirac a)) [] i -
      cont G (Function.update f k (dirac b)) [] i =
      (cont G f [] i - cont G (Function.update f k (dirac b)) [] i) -
        (cont G f [] i - cont G (Function.update f k (dirac a)) [] i) := by ring
  rw [this, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [Fintype A] [DecidableEq I] in
/-- The agent profile with agent `ag` switched to the sure move `c`. -/
theorem assemble_agentProfile_update [Fintype H]
    (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) (ag : Agent G) {c : A}
    (hc : c ∈ G.avail ag.1) :
    G.assemble (agentProfile G (Function.update σ ag (pureMixed (agentPure G ag ⟨c, hc⟩)))) =
      Function.update (G.assemble (agentProfile G σ)) ag.1 (dirac c) := by
  funext k a
  by_cases hk : k = ag.1
  · subst hk
    rw [Function.update_self, assemble_agentProfile_apply, dirac]
    simp only [Function.update_self, pureMixed]
    by_cases ha : a ∈ G.avail ag.1
    · simp only [ha, ↓reduceDIte]
      by_cases hac : a = c
      · subst hac
        simp
      · have hne : agentPure G ag ⟨a, ha⟩ ≠ agentPure G ag ⟨c, hc⟩ := fun h =>
          hac (congrArg Subtype.val ((agentEquiv G ag).injective h))
        simp [hne, hac]
    · have hac : a ≠ c := fun h => ha (h ▸ hc)
      simp [ha, hac]
  · rw [Function.update_of_ne hk]
    cases hp : G.player k with
    | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
    | some j =>
      have hne : G.player k ≠ none := by rw [hp]; simp
      have hag : (⟨k, hne⟩ : Agent G) ≠ ag := fun h => hk (congrArg Subtype.val h)
      rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
      simp [agentProfile, hne, agentBeh, Function.update_of_ne hag]

/-- **Appendix 9.B** (MWG, p. 300). In a game with perfect recall in which nature's moves have
full support, every extensive form trembling-hand perfect Nash equilibrium is (the strategy
profile of) a sequential equilibrium. -/
theorem isSequentialEq_of_isEFTHP [Fintype H] (hPR : G.PerfectRecall)
    (hN : NatureFullSupport G) {F : I → H → A → ℝ} (hF : IsEFTHP G F) :
    ∃ μ, IsSequentialEq G F μ := by
  obtain ⟨hFb, σ, ⟨-, ε, σs, hε, hε0, hσs, hlim⟩, hFσ⟩ := hF
  have hmix : ∀ n ag, IsMixedStrategy (σs n ag) := fun n ag =>
    isMixedStrategy_of_mem_perturbedSet (hε n) ((hσs n).1 ag)
  -- the trembling sequence as behaviour profiles of `Γ_E`
  let Fs : ℕ → I → H → A → ℝ := fun n i k a =>
    if G.player k = some i then agentProfile G (σs n) i k a else F i k a
  have hasm : ∀ n, G.assemble (Fs n) = G.assemble (agentProfile G (σs n)) := by
    intro n
    funext k
    cases hp : G.player k with
    | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
    | some j =>
      rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
      funext a
      simp [Fs, hp]
  have hTM : ∀ n, IsTotallyMixedB G (Fs n) := by
    intro n
    have hb := isBehaviorProfile_agentProfile G (hmix n)
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · have := hb i k hk
      simp only [Fs, hk, ite_true]
      exact this
    · simp only [Fs, hk, ite_true]
      have hne : G.player k ≠ none := by rw [hk]; simp
      have := assemble_agentProfile_apply G (σs n) ⟨k, hne⟩ a
      rw [G.assemble_of_some _ hk] at this
      rw [this]
      simp only [ha, ↓reduceDIte]
      exact lt_of_lt_of_le ((hε n).1 _ _).1 (((hσs n).1 _).1 _)
  have hFsF : Tendsto Fs atTop (𝓝 F) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    by_cases hk : G.player k = some i
    · simp only [Fs, hk, ite_true]
      have hne : G.player k ≠ none := by rw [hk]; simp
      have h2 : F i k a = G.assemble (agentProfile G σ) k a := by
        have := congrFun (hFσ k hne) a
        rw [G.assemble_of_some _ hk] at this
        exact this
      have h1 : G.assemble (agentProfile G σ) k a = if ha : a ∈ G.avail k then
          σ ⟨k, hne⟩ (agentPure G ⟨k, hne⟩ ⟨a, ha⟩) else 0 :=
        assemble_agentProfile_apply G σ ⟨k, hne⟩ a
      rw [h2, h1]
      have happ : ∀ n, agentProfile G (σs n) i k a =
          if ha : a ∈ G.avail k then σs n ⟨k, hne⟩ (agentPure G ⟨k, hne⟩ ⟨a, ha⟩) else 0 := by
        intro n
        have := assemble_agentProfile_apply G (σs n) ⟨k, hne⟩ a
        rw [G.assemble_of_some _ hk] at this
        exact this
      simp only [happ]
      split_ifs with ha
      · exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim _) _
      · exact tendsto_const_nhds
    · simp only [Fs, hk, ite_false]
      exact tendsto_const_nhds
  -- a convergent subsequence of the Bayes beliefs
  set D := G.decisionNodes
  set v : ℕ → D → ℝ := fun n x => bayesBelief G (G.assemble (Fs n)) x.1
  set K : Set (D → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hP : ∀ n k, 0 < probInfo G (G.assemble (Fs n)) k := fun n k =>
    probInfo_pos G hN (hTM n) k
  have hvK : ∀ n, v n ∈ K := by
    intro n x _
    have hx := (mem_decisionNodes G).1 x.2
    have hxk : x.1 ∈ G.infoSet (G.info x.1) := (mem_infoSet G).2 ⟨hx, rfl⟩
    have hf := assemble_nonneg G (hTM n).1
    exact ⟨div_nonneg (G.reach_nonneg hf _) (hP n _).le,
      (div_le_one (hP n _)).2 (reach_le_probInfo G hf hxk)⟩
  obtain ⟨μv, hμK, φ, hφ, hμlim⟩ := hK.tendsto_subseq hvK
  let μ : List A → ℝ := fun x => if hx : x ∈ D then μv ⟨x, hx⟩ else 0
  have hbel : ∀ x, G.IsDecision x → Tendsto (fun n => bayesBelief G (G.assemble (Fs (φ n))) x)
      atTop (𝓝 (μ x)) := by
    intro x hx
    have hxD : x ∈ D := (mem_decisionNodes G).2 hx
    simp only [μ, hxD, ↓reduceDIte]
    exact tendsto_pi_nhds.1 hμlim ⟨x, hxD⟩
  have hcons : IsConsistent G F μ :=
    ⟨Fs ∘ φ, fun n => hTM (φ n), hFsF.comp hφ.tendsto_atTop, hbel⟩
  have hμ : IsBeliefSystem G μ := by
    refine ⟨fun x hx => ?_, fun k => ?_⟩
    · have hxD : x ∈ D := (mem_decisionNodes G).2 hx
      simp only [μ, hxD, ↓reduceDIte]
      exact hμK ⟨x, hxD⟩ (Set.mem_univ _)
    · refine tendsto_nhds_unique (tendsto_finsetSum _ fun x hx =>
        hbel x ((mem_infoSet G).1 hx).1) ?_
      simp only [sum_bayesBelief G (hP _ k)]
      exact tendsto_const_nhds
  -- no move at a single information set is profitable in the limit
  have hone : ∀ i k, G.player k = some i → ∀ b ∈ G.avail k,
      ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i ≤
        condPayoff G (G.assemble F) μ k i := by
    intro i k hk b hb
    have hne : G.player k ≠ none := by rw [hk]; simp
    set ag : Agent G := ⟨k, hne⟩
    have hown : owner G ag = i := by
      have := player_owner G ag
      rw [hk] at this
      exact (Option.some.inj this).symm
    set Q : (H → A → ℝ) → (List A → ℝ) → A → ℝ := fun f m c =>
      ∑ x ∈ G.infoSet k, m x * cont G f (c :: x) i
    have hQlim : ∀ c, Tendsto (fun n => Q (G.assemble (Fs (φ n)))
        (bayesBelief G (G.assemble (Fs (φ n)))) c) atTop (𝓝 (Q (G.assemble F) μ c)) := by
      intro c
      exact tendsto_finsetSum _ fun x hx => (hbel x ((mem_infoSet G).1 hx).1).mul
        (tendsto_cont G (hFsF.comp hφ.tendsto_atTop) _ i)
    -- every move played with positive probability is a best move in the limit
    have hbest : ∀ a ∈ G.avail k, 0 < G.assemble F k a →
        Q (G.assemble F) μ b ≤ Q (G.assemble F) μ a := by
      intro a ha hpos
      set sa := agentPure G ag ⟨a, ha⟩
      set sb := agentPure G ag ⟨b, hb⟩
      have hσa : 0 < σ ag sa := by
        have h2 := congrFun (hFσ k hne) a
        have h1 := assemble_agentProfile_apply G σ ag a
        have ha' : a ∈ G.avail ag.1 := ha
        simp only [ha', ↓reduceDIte] at h1
        exact lt_of_lt_of_eq hpos (h2.trans h1)
      have hev : ∀ᶠ n in atTop, ε (φ n) ag sa < σs (φ n) ag sa := by
        have h1 : Tendsto (fun n => σs (φ n) ag sa - ε (φ n) ag sa) atTop
            (𝓝 (σ ag sa - 0)) :=
          ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim ag) sa).comp hφ.tendsto_atTop).sub
            ((hε0 ag sa).comp hφ.tendsto_atTop)
        rw [sub_zero] at h1
        filter_upwards [h1.eventually (lt_mem_nhds hσa)] with n hn
        linarith
      refine le_of_tendsto_of_tendsto (hQlim b) (hQlim a) ?_
      filter_upwards [hev] with n hn
      set fn := G.assemble (Fs (φ n))
      have hnb : (agentNF G).mixedPayoff (Function.update (σs (φ n)) ag (pureMixed sb)) ag ≤
          (agentNF G).mixedPayoff (Function.update (σs (φ n)) ag (pureMixed sa)) ag := by
        by_contra hlt
        push Not at hlt
        have := perturbedNash_eq_of_not_best (hσs (φ n)) ag hlt
        linarith
      have hmixU : ∀ s, ∀ ag', IsMixedStrategy
          (Function.update (σs (φ n)) ag (pureMixed s) ag') := by
        intro s ag'
        by_cases h : ag' = ag
        · subst h
          rw [Function.update_self]
          exact isMixedStrategy_pureMixed s
        · rw [Function.update_of_ne h]
          exact hmix _ ag'
      rw [agentNF_mixedPayoff G hPR.1 (hmixU sb), agentNF_mixedPayoff G hPR.1 (hmixU sa),
        assemble_agentProfile_update G _ ag hb, assemble_agentProfile_update G _ ag ha,
        hown, ← hasm] at hnb
      have hdiff := cont_update_dirac_sub G hPR.1 fn k ha hb i
      have hsum : 0 ≤ ∑ x ∈ G.infoSet k, G.reach fn x * (cont G fn (a :: x) i -
          cont G fn (b :: x) i) := by
        rw [← hdiff]
        exact sub_nonneg.2 hnb
      have hPk := hP (φ n) k
      have : Q fn (bayesBelief G fn) a - Q fn (bayesBelief G fn) b =
          (∑ x ∈ G.infoSet k, G.reach fn x * (cont G fn (a :: x) i - cont G fn (b :: x) i)) /
            probInfo G fn k := by
        simp only [Q]
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [bayesBelief, ((mem_infoSet G).1 hx).2]
        ring
      have := div_nonneg hsum hPk.le
      linarith
    -- the expected payoff at `k` is the average of the `Q`-values
    have hV : condPayoff G (G.assemble F) μ k i =
        ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ a := by
      have h1 : ∀ x ∈ G.infoSet k, μ x * cont G (G.assemble F) x i =
          ∑ a ∈ G.avail k, G.assemble F k a * (μ x * cont G (G.assemble F) (a :: x) i) := by
        intro x hx
        rw [cont_decision G _ ((mem_infoSet G).1 hx).1, ((mem_infoSet G).1 hx).2,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      unfold condPayoff
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => by simp only [Q]; rw [Finset.mul_sum]
    rw [hV]
    have hsum1 := assemble_sum G hFb k
    calc ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i
        = ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ b := by
          rw [← Finset.sum_mul, hsum1, one_mul]
      _ ≤ ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ a := by
          refine Finset.sum_le_sum fun a ha => ?_
          rcases (assemble_nonneg G hFb k a).lt_or_eq with hpos | hz
          · exact mul_le_mul_of_nonneg_left (hbest a ha hpos) hpos.le
          · rw [← hz, zero_mul, zero_mul]
  refine ⟨μ, hFb, hμ, fun k i hk g hg => ?_, hcons⟩
  exact oneShot_consistent G hPR hN hcons (hone i) hg hk

/-- **Existence of sequential equilibrium** (Kreps and Wilson 1982; MWG, pp. 290 and 300). Every
finite game with perfect recall in which nature's moves have full support has a sequential
equilibrium. -/
theorem exists_isSequentialEq [Finite H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G) :
    ∃ F μ, IsSequentialEq G F μ := by
  have := Fintype.ofFinite H
  obtain ⟨F, hF⟩ := exists_isEFTHP G
  obtain ⟨μ, hμ⟩ := isSequentialEq_of_isEFTHP G hPR hN hF
  exact ⟨F, μ, hμ⟩

/-- **Appendix 9.B** (MWG, p. 300). Every extensive form trembling-hand perfect Nash equilibrium
is subgame perfect (perfect recall, nature with full support). -/
theorem isSPNE_of_isEFTHP [Fintype H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} (hF : IsEFTHP G F) : IsSPNE G F := by
  obtain ⟨μ, hμ⟩ := isSequentialEq_of_isEFTHP G hPR hN hF
  exact proposition_9_C_2 G hPR hμ

omit [DecidableEq H] in
/-- **Exercise 9.B.8** (MWG, p. 302). Every finite game `Γ_E` (here: with perfect recall and
moves of nature with full support) has a mixed (behaviour) strategy subgame perfect Nash
equilibrium. -/
theorem exercise_9_B_8 [Finite H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G) :
    ∃ F, IsSPNE G F := by
  classical
  obtain ⟨F, μ, hμ⟩ := exists_isSequentialEq G hPR hN
  exact ⟨F, proposition_9_C_2 G hPR hμ⟩

end MWG.DynamicGames
