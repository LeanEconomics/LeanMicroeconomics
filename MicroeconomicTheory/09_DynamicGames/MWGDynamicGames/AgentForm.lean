/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Beliefs
import MWGSimultaneousMoveGames.TremblingHand

/-!
# The agent normal form and extensive form trembling-hand perfection

MWG, Appendix B of Chapter 9, pp. 299-300.

* `Agent G`: the personal information sets of `Γ_E`; `agentForm G` is the extensive form in
  which each information set is controlled by a separate agent maximising the payoff of the
  player who owns it (Selten's agent form). Its normal form `agentNF G` is the **agent normal
  form** (MWG, p. 299).
* `agentProfile G σ`: the behaviour profile of `Γ_E` given by a mixed profile `σ` of the agent
  normal form (an agent's pure strategies are the actions at its information set,
  `agentEquiv`). `agentNF_mixedPayoff`: without absent-mindedness, agent `H`'s payoff in the
  agent normal form at `σ` is the expected payoff of its owner in `Γ_E` under
  `agentProfile G σ` (via Kuhn's construction of Chapter 7).
* `IsEFTHP` is **Definition 9.BB.1**; `exists_isEFTHP`: every finite game has an extensive form
  trembling-hand perfect Nash equilibrium (Selten 1975; Chapter 8's Exercise 8.F.3 applied to
  the agent normal form).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- An agent: a personal (non-nature) information set. -/
abbrev Agent := {k : H // G.player k ≠ none}

/-- The player who owns an agent. -/
def owner (ag : Agent G) : I := (G.player ag.1).get (Option.isSome_iff_ne_none.2 ag.2)

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem player_owner (ag : Agent G) : G.player ag.1 = some (owner G ag) := by
  simp [owner]

/-- **Appendix 9.B** (MWG, p. 299). Selten's agent form: the same tree, information sets and
moves of nature, with a separate agent at every personal information set, whose payoff is
that of the player owning the information set. -/
def agentForm : ExtensiveForm (Agent G) A H where
  nodes := G.nodes
  nil_mem := G.nil_mem
  tail_mem := G.tail_mem
  info := G.info
  avail := G.avail
  avail_spec := G.avail_spec
  info_surj := G.info_surj
  player k := if h : G.player k = none then none else some ⟨k, h⟩
  natureProb := G.natureProb
  nature_nonneg := fun k hk => G.nature_nonneg k (by by_contra h; simp [h] at hk)
  nature_zero := fun k hk => G.nature_zero k (by by_contra h; simp [h] at hk)
  nature_sum := fun k hk => G.nature_sum k (by by_contra h; simp [h] at hk)
  payoff ag z := G.payoff (owner G ag) z

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem agentForm_player_none {k : H} : (agentForm G).player k = none ↔ G.player k = none := by
  simp only [agentForm]
  split_ifs with h <;> simp [h]

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem agentForm_player_some {k : H} {ag : Agent G} :
    (agentForm G).player k = some ag ↔ k = ag.1 := by
  simp only [agentForm]
  split_ifs with h
  · simp only [false_iff]
    rintro rfl
    exact ag.2 h
  · constructor
    · intro he
      simp only [Option.some.injEq] at he
      rw [← he]
    · rintro rfl
      rfl

/-- **Appendix 9.B** (MWG, p. 299). The agent normal form of `Γ_E`. -/
def agentNF [Fintype H] : NormalForm (Agent G) (agentForm G).PureStrategy :=
  (agentForm G).toNormalForm

/-- The pure strategy of an agent playing action `a` at its information set. -/
def agentPure (ag : Agent G) (a : {a // a ∈ G.avail ag.1}) : (agentForm G).PureStrategy ag :=
  fun k => ⟨a.1, by
    have : k.1 = ag.1 := (agentForm_player_some G).1 k.2
    change a.1 ∈ G.avail k.1
    rw [this]
    exact a.2⟩

/-- The agent's own information set as one of its information sets in the agent form. -/
def agentSelf (ag : Agent G) : (agentForm G).InfoSetOf ag :=
  ⟨ag.1, (agentForm_player_some G).2 rfl⟩

/-- An agent's pure strategies are its actions. -/
def agentEquiv (ag : Agent G) : {a // a ∈ G.avail ag.1} ≃ (agentForm G).PureStrategy ag where
  toFun := agentPure G ag
  invFun s := ⟨(s (agentSelf G ag)).1, (s (agentSelf G ag)).2⟩
  left_inv a := rfl
  right_inv s := by
    funext k
    have hk : k = agentSelf G ag := Subtype.ext ((agentForm_player_some G).1 k.2)
    subst hk
    rfl

/-- The move probabilities of agent `ag` given its mixed strategy `σ ag`. -/
def agentBeh (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) (ag : Agent G) :
    H → A → ℝ :=
  fun _ a => if ha : a ∈ G.avail ag.1 then σ ag (agentPure G ag ⟨a, ha⟩) else 0

/-- The behaviour profile of `Γ_E` given by a mixed profile of the agent normal form. -/
def agentProfile (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) : I → H → A → ℝ :=
  fun _ k a => if h : G.player k = none then 0 else agentBeh G σ ⟨k, h⟩ k a

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem assemble_agentProfile (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) :
    G.assemble (agentProfile G σ) = (agentForm G).assemble (agentBeh G σ) := by
  funext k
  cases hk : G.player k with
  | none =>
    rw [G.assemble_of_none _ hk, (agentForm G).assemble_of_none _
      ((agentForm_player_none G).2 hk)]
    rfl
  | some i =>
    have hne : G.player k ≠ none := by rw [hk]; simp
    rw [G.assemble_of_some _ hk, (agentForm G).assemble_of_some _
      ((agentForm_player_some G (ag := ⟨k, hne⟩)).2 rfl)]
    funext a
    simp [agentProfile, hne]

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of `agentProfile G σ` at agent `ag`'s information set. -/
theorem assemble_agentProfile_apply (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ)
    (ag : Agent G) (a : A) :
    G.assemble (agentProfile G σ) ag.1 a =
      if ha : a ∈ G.avail ag.1 then σ ag (agentPure G ag ⟨a, ha⟩) else 0 := by
  rw [assemble_agentProfile, (agentForm G).assemble_of_some _
    ((agentForm_player_some G (ag := ag)).2 rfl)]
  rfl

omit [Fintype A] [DecidableEq I] in
/-- A mixed profile of the agent normal form gives a behaviour profile of `Γ_E`. -/
theorem isBehaviorProfile_agentProfile [Fintype H]
    {σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ}
    (hσ : ∀ ag, IsMixedStrategy (σ ag)) : IsBehaviorProfile G (agentProfile G σ) := by
  intro i k hk
  have hne : G.player k ≠ none := by rw [hk]; simp
  set ag : Agent G := ⟨k, hne⟩
  have happ := assemble_agentProfile_apply G σ ag
  rw [G.assemble_of_some _ hk] at happ
  refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
  · rw [happ]
    split_ifs
    · exact (hσ ag).1 _
    · exact le_rfl
  · rw [happ]
    split_ifs with h
    · exact absurd h ha
    · rfl
  · rw [Finset.sum_congr rfl fun a _ => happ a, ← Finset.sum_coe_sort]
    simp only [Finset.coe_mem, ↓reduceDIte]
    have := Equiv.sum_comp (agentEquiv G ag) (σ ag)
    rw [← (hσ ag).2, ← this]
    rfl

omit [Fintype A] [DecidableEq A] [DecidableEq I] [DecidableEq H] in
/-- The agent form has no absent-mindedness when `Γ_E` has none. -/
theorem agentForm_noAbsentMindedness (hNA : G.NoAbsentMindedness) :
    (agentForm G).NoAbsentMindedness := hNA

omit [DecidableEq A] [Fintype A] [DecidableEq H] [DecidableEq I] in
/-- Reach probabilities in the agent form are those of `Γ_E`. -/
theorem reach_agentForm (f : H → A → ℝ) (z : List A) : (agentForm G).reach f z = G.reach f z := by
  induction z with
  | nil => rfl
  | cons a z ih => rw [reach_cons, reach_cons, ih]; rfl

omit [DecidableEq I] in
/-- **Appendix 9.B** (MWG, p. 299). Agent `ag`'s payoff in the agent normal form at the mixed
profile `σ` is the expected payoff of its owner in `Γ_E` under the behaviour profile given by
`σ`. -/
theorem agentNF_mixedPayoff [Fintype H] (hNA : G.NoAbsentMindedness)
    {σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ}
    (hσ : ∀ ag, IsMixedStrategy (σ ag)) (ag : Agent G) :
    (agentNF G).mixedPayoff σ ag = cont G (G.assemble (agentProfile G σ)) [] (owner G ag) := by
  have hmix : ∀ ag', σ ag' = (agentForm G).mixedOfBehavior (i := ag') (agentBeh G σ ag') := by
    intro ag'
    funext s
    unfold mixedOfBehavior
    rw [Fintype.prod_eq_single (agentSelf G ag') fun k hk =>
      absurd (Subtype.ext ((agentForm_player_some G).1 k.2) : k = agentSelf G ag') hk]
    have : s = agentPure G ag' ⟨(s (agentSelf G ag')).1, (s (agentSelf G ag')).2⟩ :=
      ((agentEquiv G ag').right_inv s).symm
    simp only [agentBeh]
    split_ifs with hm
    · conv_lhs => rw [this]
    · exact absurd (s (agentSelf G ag')).2 hm
  have hbeh : ∀ ag', (agentForm G).IsBehaviorStrategy ag' (agentBeh G σ ag') := by
    intro ag' k hk
    have hk' : k = ag'.1 := (agentForm_player_some G).1 hk
    subst hk'
    have h := isBehaviorProfile_agentProfile G hσ (owner G ag') ag'.1 (player_owner G ag')
    have happ := assemble_agentProfile_apply G σ ag'
    rw [G.assemble_of_some _ (player_owner G ag')] at happ
    refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
    · have := h.1 a
      rw [happ] at this
      exact this
    · have := h.2.1 a ha
      rw [happ] at this
      exact this
    · have := h.2.2
      rw [Finset.sum_congr rfl fun a _ => happ a] at this
      exact this
  rw [agentNF, mixedPayoff_toNormalForm, cont_nil]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzn : z ∈ G.nodes := ((mem_terminals G).1 hz).1
  rw [mixedOutcome_factor]
  have hw : ∀ ag', (agentForm G).mixedWeight (σ ag') z =
      (agentForm G).weight (some ag') (agentBeh G σ ag') z := by
    intro ag'
    rw [hmix ag']
    exact (agentForm G).mixedWeight_mixedOfBehavior (agentForm_noAbsentMindedness G hNA)
      (hbeh ag') z hzn
  simp_rw [hw]
  rw [← (agentForm G).reach_assemble_factor, ← assemble_agentProfile, reach_agentForm]
  rfl

/-- **Definition 9.BB.1** (MWG, p. 299). A behaviour profile of `Γ_E` is an extensive form
trembling-hand perfect Nash equilibrium if it is (the behaviour profile of) a normal form
trembling-hand perfect Nash equilibrium of the agent normal form. -/
def IsEFTHP [Fintype H] (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∃ σ, IsTHP (agentNF G) σ ∧
    ∀ k, G.player k ≠ none → G.assemble F k = G.assemble (agentProfile G σ) k

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Every agent has a pure strategy. -/
theorem agent_nonempty (ag : Agent G) : Nonempty ((agentForm G).PureStrategy ag) := by
  obtain ⟨a, ha⟩ := G.avail_nonempty ag.1
  exact ⟨agentPure G ag ⟨a, ha⟩⟩

omit [DecidableEq I] in
/-- **Appendix 9.B** (MWG, p. 299; Selten 1975). Every finite game in extensive form has an
extensive form trembling-hand perfect Nash equilibrium. -/
theorem exists_isEFTHP [Fintype H] : ∃ F, IsEFTHP G F := by
  have := agent_nonempty G
  obtain ⟨σ, hσ⟩ := exercise_8_F_3 (agentNF G)
  have hmix : ∀ ag, IsMixedStrategy (σ ag) := fun ag => hσ.1.1 ag
  exact ⟨agentProfile G σ, isBehaviorProfile_agentProfile G hmix, σ, hσ, fun _ _ => rfl⟩

end MWG.DynamicGames
