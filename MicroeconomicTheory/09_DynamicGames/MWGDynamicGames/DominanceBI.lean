/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Zermelo
import MWGDynamicGames.Generalized
import MWGDynamicGames.Entry

/-!
# Iterated weak dominance and backward induction

MWG, Exercise 9.D.1 (p. 305): in a finite game of perfect information with no moves of nature
in which no player has the same payoffs at two terminal nodes (the condition of
Proposition 9.B.2 for a unique SPNE), there is an order of iterated removal of weakly dominated
strategies after which every surviving strategy profile has the SPNE outcome.

* `IsWDominatedIn`, `WDDeletionStep`: iterated deletion of weakly dominated strategies
  (Definition 8.B.3 within the remaining strategy sets; several strategies of several players
  may be removed at once), for any normal form game.
* `OnPath G f x w`: the moves `f` lead from node `x` to node `w`. `cont_onPath`, `cont_agree`:
  for pure moves, continuation payoffs are determined by the moves along the realised path.
* `biSets G s n`: the strategies of each player that follow the backward-induction profile `s`
  at every own decision node of length at least `n` that they do not exclude by their own
  earlier moves. `biSets_step`: going from `biSets (n + 1)` to `biSets n` removes only weakly
  dominated strategies: a strategy deviating at a node `y` of length `n` that it does not
  exclude is weakly dominated by the strategy that follows `s` in the subgame at `y` (strictly
  worse against rivals that lead to `y`; `towards`).
* `exercise_9_D_1`: the deletion order "deepest nodes first" ends in `biSets 0`, where every
  surviving profile follows the SPNE path and gives the SPNE payoffs; `exercise_9_D_1_instance`
  (the entry game of Example 9.B.1).

MWG notes that any order of deletion gives the result (Moulin, 1981); that stronger claim is
not formalized.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames

/-- **Definition 8.B.3 within remaining sets** (MWG, pp. 238-240). Within the remaining strategy
sets `T`, the strategy `s` of player `i` is weakly dominated by a remaining strategy `s'`: at
least as good against every remaining profile of the rivals and strictly better against
one. -/
def IsWDominatedIn {J : Type*} {S : J → Type*} [DecidableEq J] (N : NormalForm J S)
    (T : (i : J) → Set (S i)) (i : J) (s : S i) : Prop :=
  ∃ s' ∈ T i, (∀ r : (j : J) → S j, (∀ j, j ≠ i → r j ∈ T j) →
      N.payoff i (Function.update r i s) ≤ N.payoff i (Function.update r i s')) ∧
    ∃ r : (j : J) → S j, (∀ j, j ≠ i → r j ∈ T j) ∧
      N.payoff i (Function.update r i s) < N.payoff i (Function.update r i s')

/-- **Section 8.B** (MWG, p. 240). One step of iterated deletion of weakly dominated strategies:
`T'` keeps a subset of each `T_i`, and every removed strategy is weakly dominated in the game
restricted to `T`. -/
def WDDeletionStep {J : Type*} {S : J → Type*} [DecidableEq J] (N : NormalForm J S)
    (T T' : (i : J) → Set (S i)) : Prop :=
  (∀ i, T' i ⊆ T i) ∧ ∀ i, ∀ s ∈ T i, s ∉ T' i → IsWDominatedIn N T i s

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]

/-- The moves `f` lead from node `x` to node `w`: every move on the path from `x` to `w` has
probability one. -/
def OnPath (f : H → A → ℝ) (x w : List A) : Prop :=
  ∀ b v, x <:+ v → b :: v <:+ w → f (G.info v) b = 1

/-- Pure moves: probabilities `0` or `1`, zero off the available actions, summing to one. -/
def IsPureMoves (f : H → A → ℝ) : Prop :=
  (∀ k a, f k a = 0 ∨ f k a = 1) ∧ (∀ k a, a ∉ G.avail k → f k a = 0) ∧
    ∀ k, ∑ a ∈ G.avail k, f k a = 1

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem onPath_self (f : H → A → ℝ) (x : List A) : OnPath G f x x := by
  intro b v hxv hbv
  have h1 := hxv.length_le
  have h2 := hbv.length_le
  simp only [List.length_cons] at h2
  omega

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.mono {f : H → A → ℝ} {x w w' : List A} (h : OnPath G f x w') (hw : w <:+ w') :
    OnPath G f x w :=
  fun b v hxv hbv => h b v hxv (hbv.trans hw)

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.cons {f : H → A → ℝ} {x w : List A} (h : OnPath G f x w) (hxw : x <:+ w)
    {a : A} (ha : f (G.info w) a = 1) : OnPath G f x (a :: w) := by
  intro b v hxv hbv
  rcases List.suffix_cons_iff.1 hbv with he | he
  · obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ha
  · exact h b v hxv he

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.trans {f : H → A → ℝ} {x w : List A} (h1 : OnPath G f [] x) (hxw : x <:+ w)
    (h2 : OnPath G f x w) : OnPath G f [] w := by
  intro b v _ hbv
  rcases List.suffix_or_suffix_of_suffix hxw hbv with h | h
  · rcases List.suffix_cons_iff.1 h with he | he
    · exact h1 b v List.nil_suffix (he ▸ List.suffix_refl x)
    · exact h2 b v he hbv
  · exact h1 b v List.nil_suffix h

omit [DecidableEq I] in
/-- With pure moves, the continuation payoff at a decision node is that of the successor
chosen there. -/
theorem cont_step {f : H → A → ℝ} (hf : IsPureMoves G f) {y : List A} (hy : G.IsDecision y)
    {a : A} (ha : f (G.info y) a = 1) (i : I) : cont G f y i = cont G f (a :: y) i := by
  have haav : a ∈ G.avail (G.info y) := by
    by_contra h
    rw [hf.2.1 _ a h] at ha
    norm_num at ha
  have hzero : ∀ b ∈ G.avail (G.info y), b ≠ a → f (G.info y) b = 0 := by
    intro b hb hba
    have hs := hf.2.2 (G.info y)
    rw [← Finset.add_sum_erase _ _ haav, ha] at hs
    have hnn : ∀ c ∈ (G.avail (G.info y)).erase a, 0 ≤ f (G.info y) c := fun c _ => by
      rcases hf.1 (G.info y) c with h | h <;> simp [h]
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by linarith) b
      (Finset.mem_erase.2 ⟨hba, hb⟩)
  rw [cont_decision G f hy, Finset.sum_eq_single_of_mem a haav fun b hb hba => by
    rw [hzero b hb hba, zero_mul], ha, one_mul]

omit [DecidableEq I] in
/-- With pure moves, the continuation payoff from `x` equals that from any node `y` on the
path from `x`. -/
theorem cont_onPath {f : H → A → ℝ} (hf : IsPureMoves G f) {x y : List A} (hxy : x <:+ y)
    (hy : y ∈ G.nodes) (hp : OnPath G f x y) (i : I) : cont G f x i = cont G f y i := by
  induction y with
  | nil =>
    rw [List.eq_nil_of_suffix_nil hxy]
  | cons a y ih =>
    rcases List.suffix_cons_iff.1 hxy with he | he
    · rw [he]
    · rw [ih he (G.mem_of_cons_mem hy) (hp.mono G (List.suffix_cons a y)),
        cont_step G hf (G.isDecision_of_cons_mem hy) (hp a y he (List.suffix_refl _))]

omit [DecidableEq I] in
/-- With pure moves `f`, the continuation payoff from `y` does not change if the moves change
only off the path that `f` takes from `y`. -/
theorem cont_agree {f g : H → A → ℝ} (hf : IsPureMoves G f) {y : List A} (hy : y ∈ G.nodes)
    (h : ∀ w, G.IsDecision w → y <:+ w → OnPath G f y w → f (G.info w) = g (G.info w))
    (i : I) : cont G f y i = cont G g y i := by
  suffices key : ∀ n, ∀ y ∈ G.nodes, G.nodes.sup List.length - y.length ≤ n →
      (∀ w, G.IsDecision w → y <:+ w → OnPath G f y w → f (G.info w) = g (G.info w)) →
      cont G f y i = cont G g y i from key _ y hy le_rfl h
  intro n
  induction n with
  | zero =>
    intro y hy hn _
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  | succ n ih =>
    intro y hy hn h
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hfy := h y hdec (List.suffix_refl y) (onPath_self G f y)
      rw [cont_decision _ _ hdec, cont_decision _ g hdec, ← hfy]
      refine Finset.sum_congr rfl fun a ha => ?_
      rcases hf.1 (G.info y) a with h0 | h1
      · rw [h0, zero_mul, zero_mul]
      · rw [h1]
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        refine congrArg _ (ih (a :: y) hmem (by simp only [List.length_cons]; omega)
          fun w hw haw hp => h w hw ((List.suffix_cons a y).trans haw) ?_)
        intro b v hyv hbv
        by_cases hvy : v = y
        · subst hvy
          have := suffix_unique hbv haw (by simp)
          rw [(List.cons.inj this).1]
          exact h1
        · obtain ⟨c, hc⟩ := exists_cons_suffix hyv (Ne.symm hvy)
          have hca : c :: y = a :: y := suffix_unique (hc.trans ((List.suffix_cons b v).trans
            hbv)) haw (by simp)
          rw [hca] at hc
          exact hp b v hc hbv
    · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]

omit [Fintype A] in
/-- Without moves of nature the moves of a pure profile are pure. -/
theorem isPureMoves_pureProfile (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) : IsPureMoves G (G.pureProfile s) := by
  refine ⟨fun k a => ?_, fun k a ha => ?_, fun k => G.sum_pureProfile s k⟩
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
    rw [G.pureProfile_apply s hj]
    split_ifs <;> simp
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
    rw [G.pureProfile_apply s hj]
    have : (s j ⟨k, hj⟩).1 ≠ a := fun he => ha (he ▸ (s j ⟨k, hj⟩).2)
    simp [this]

/-- Player `j`'s strategy `σ` does not exclude node `y` by its own moves: at each of `j`'s
decision nodes on the path to `y`, `σ` takes the action leading towards `y`. -/
def Permits (j : I) (σ : G.PureStrategy j) (y : List A) : Prop :=
  ∀ b v (hv : G.player (G.info v) = some j), b :: v <:+ y → (σ ⟨G.info v, hv⟩).1 = b

/-- The strategies of player `j` that follow the backward-induction profile `s` at every own
decision node of length at least `n` that they do not exclude by their own moves. -/
def biSets (s : (i : I) → G.PureStrategy i) (n : ℕ) (j : I) : Set (G.PureStrategy j) :=
  {σ | ∀ y (hy : G.player (G.info y) = some j), G.IsDecision y → n ≤ y.length →
    Permits G j σ y → σ ⟨G.info y, hy⟩ = s j ⟨G.info y, hy⟩}

omit [Fintype A] in
theorem pureProfile_eq_one_iff (s : (i : I) → G.PureStrategy i) {k : H} {j : I}
    (hk : G.player k = some j) (a : A) : G.pureProfile s k a = 1 ↔ (s j ⟨k, hk⟩).1 = a := by
  rw [G.pureProfile_apply s hk]
  split_ifs with h <;> simp [h]

omit [Fintype A] in
theorem permits_of_onPath (s : (i : I) → G.PureStrategy i) {w : List A}
    (h : OnPath G (G.pureProfile s) [] w) (j : I) : Permits G j (s j) w :=
  fun b v hv hbv => (pureProfile_eq_one_iff G s hv b).1 (h b v List.nil_suffix hbv)

omit [Fintype A] in
/-- If every component of `t` lies in `biSets s m`, at decision nodes of length at least `m` on
the path of `t`, `t` makes the moves of `s`. -/
theorem biSets_agree (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    {m : ℕ} (ht : ∀ k, t k ∈ biSets G s m k) {w : List A} (hw : G.IsDecision w)
    (hl : m ≤ w.length) (hp : OnPath G (G.pureProfile t) [] w) :
    G.pureProfile t (G.info w) = G.pureProfile s (G.info w) := by
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info w))
  have he := ht j w hj hw hl (permits_of_onPath G t hp j)
  funext a
  rw [G.pureProfile_apply t hj, G.pureProfile_apply s hj, he]

/-- From a node of length at least `m` on the path of `t` (all of whose components lie in
`biSets s m`), the continuation payoffs of `t` are those of `s`. -/
theorem cont_biSets (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    {m : ℕ} (ht : ∀ k, t k ∈ biSets G s m k) {x : List A} (hx : x ∈ G.nodes)
    (hl : m ≤ x.length) (hp : OnPath G (G.pureProfile t) [] x) (i : I) :
    cont G (G.pureProfile t) x i = cont G (G.pureProfile s) x i :=
  cont_agree G (isPureMoves_pureProfile G hN t) hx (fun _ hw hxw hpw =>
    biSets_agree G hN s t ht hw (hl.trans hxw.length_le) (hp.trans G hxw hpw)) i

omit [Fintype A] in
/-- Every surviving profile at stage `0` follows the path of `s`. -/
theorem onPath_biSets_iff (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    (ht : ∀ k, t k ∈ biSets G s 0 k) {w : List A} (hw : w ∈ G.nodes) :
    OnPath G (G.pureProfile t) [] w ↔ OnPath G (G.pureProfile s) [] w := by
  induction w with
  | nil => exact ⟨fun _ => onPath_self G _ [], fun _ => onPath_self G _ []⟩
  | cons a w ih =>
    have hw' := G.mem_of_cons_mem hw
    have hdec := G.isDecision_of_cons_mem hw
    constructor
    · intro h
      have h1 := (ih hw').1 (h.mono G (List.suffix_cons a w))
      refine h1.cons G List.nil_suffix ?_
      rw [← biSets_agree G hN s t ht hdec (Nat.zero_le _) (h.mono G (List.suffix_cons a w))]
      exact h a w List.nil_suffix (List.suffix_refl _)
    · intro h
      have h1 := (ih hw').2 (h.mono G (List.suffix_cons a w))
      refine h1.cons G List.nil_suffix ?_
      rw [biSets_agree G hN s t ht hdec (Nat.zero_le _) h1]
      exact h a w List.nil_suffix (List.suffix_refl _)

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- Under perfect information the information sets of the subgame at `y` are those of the
decision nodes following `y`. -/
theorem inSub_iff_of_pi (hPI : G.PerfectInformation) {y v : List A} (hv : G.IsDecision v) :
    InSub G y (G.info v) ↔ y <:+ v := by
  constructor
  · rintro ⟨w, hw, hyw, he⟩
    rw [← hPI w hw.1 v hv.1 hw.2 hv.2 he]
    exact hyw
  · exact fun h => inSub_of_suffix G hv h

open Classical in
/-- The strategy of player `k` that takes the actions leading to node `y` at the nodes on the
path to `y`, and follows `s` elsewhere. -/
noncomputable def towards (s : (i : I) → G.PureStrategy i) {y : List A} (hy : y ∈ G.nodes)
    (k : I) : G.PureStrategy k := fun h =>
  if hex : ∃ b v, b :: v <:+ y ∧ G.info v = h.1 then
    ⟨hex.choose, by
      obtain ⟨v, hv, he⟩ := hex.choose_spec
      have hm := G.mem_avail_of_cons_mem (G.mem_of_suffix hv hy)
      rwa [he] at hm⟩
  else s k h

omit [DecidableEq A] [DecidableEq I] in
theorem towards_on_path (hPI : G.PerfectInformation) (s : (i : I) → G.PureStrategy i)
    {y : List A} (hy : y ∈ G.nodes) {b : A} {v : List A} (hbv : b :: v <:+ y) {k : I}
    (hk : G.player (G.info v) = some k) : (towards G s hy k ⟨G.info v, hk⟩).1 = b := by
  have hex : ∃ b' v', b' :: v' <:+ y ∧ G.info v' = G.info v := ⟨b, v, hbv, rfl⟩
  simp only [towards, hex, ↓reduceDIte]
  obtain ⟨v', hv', he⟩ := hex.choose_spec
  have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hy)
  have hvd' : G.IsDecision v' := G.isDecision_of_cons_mem (G.mem_of_suffix hv' hy)
  have hvv : v' = v := hPI v' hvd'.1 v hvd.1 hvd'.2 hvd.2 he
  subst hvv
  exact (List.cons.inj (suffix_unique hv' hbv (by simp))).1

omit [DecidableEq A] [DecidableEq I] in
theorem towards_mem (hPI : G.PerfectInformation) (s : (i : I) → G.PureStrategy i)
    {y : List A} (hy : y ∈ G.nodes) {n : ℕ} (hyl : y.length = n) (k : I) :
    towards G s hy k ∈ biSets G s (n + 1) k := by
  intro y' hy' hdec hl _
  have hex : ¬ ∃ b v, b :: v <:+ y ∧ G.info v = G.info y' := by
    rintro ⟨b, v, hbv, he⟩
    have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hy)
    have := hPI v hvd.1 y' hdec.1 hvd.2 hdec.2 he
    subst this
    have := hbv.length_le
    simp only [List.length_cons] at this
    omega
  simp only [towards, hex, ↓reduceDIte]

/-- **Backward induction is strict without ties** (MWG, p. 276). With no moves of nature and no
ties, the mover at a decision node strictly prefers the backward-induction move to any other
move, given the continuation play. -/
theorem bi_strict (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {s : (i : I) → G.PureStrategy i} (hs : IsBackwardInduction G s) {x : List A}
    (hx : G.IsDecision x) {j : I} (hj : G.player (G.info x) = some j) {a : A}
    (ha : a ∈ G.avail (G.info x)) (hne : a ≠ (s j ⟨G.info x, hj⟩).1) :
    cont G (G.pureProfile s) (a :: x) j <
      cont G (G.pureProfile s) ((s j ⟨G.info x, hj⟩).1 :: x) j := by
  set a' := (s j ⟨G.info x, hj⟩).1
  have hB := isBehaviorProfile_pureB G s
  obtain ⟨z, hz, haz, hcz⟩ :=
    (oneShotOptimal_unique G hN hinj hB hB hs hs (G.cons_mem_of_mem_avail hx ha)).1
  obtain ⟨z', hz', haz', hcz'⟩ := (oneShotOptimal_unique G hN hinj hB hB hs hs
    (G.cons_mem_of_mem_avail hx (s j ⟨G.info x, hj⟩).2)).1
  have hstep : cont G (G.pureProfile s) x j = cont G (G.pureProfile s) (a' :: x) j :=
    cont_step G (isPureMoves_pureProfile G hN s) hx
      ((pureProfile_eq_one_iff G s hj a').2 rfl) j
  have hle : cont G (G.pureProfile s) (a :: x) j ≤ cont G (G.pureProfile s) (a' :: x) j := by
    rw [← hstep]
    exact hs x hx j hj a ha
  refine lt_of_le_of_ne hle fun he => hne ?_
  rw [← assemble_pureB] at he
  rw [(hcz j).1, (hcz' j).1] at he
  have hzz := hinj j z hz z' hz' he
  subst hzz
  exact (List.cons.inj (suffix_unique haz haz' (by simp))).1

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem biSets_mono (s : (i : I) → G.PureStrategy i) (n : ℕ) (j : I) :
    biSets G s n j ⊆ biSets G s (n + 1) j :=
  fun _ hσ y hy hd hl hp => hσ y hy hd (by omega) hp

/-- **Exercise 9.D.1, one deletion step** (MWG, p. 305). Going from `biSets s (n + 1)` to
`biSets s n` removes only strategies that are weakly dominated in the game restricted to
`biSets s (n + 1)`: a strategy of player `j` deviating from `s` at a node `y` of length `n` that
it does not exclude is weakly dominated by the strategy that follows `s` in the subgame at
`y`. -/
theorem biSets_step (hPI : G.PerfectInformation) (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {s : (i : I) → G.PureStrategy i} (hs : IsBackwardInduction G s) (n : ℕ) :
    WDDeletionStep G.toNormalForm (biSets G s (n + 1)) (biSets G s n) := by
  classical
  refine ⟨biSets_mono G s n, fun j σ hσ hσn => ?_⟩
  -- the node where `σ` deviates
  obtain ⟨y, hy, hdec, hnl, hperm, hdev⟩ : ∃ y, ∃ hy : G.player (G.info y) = some j,
      G.IsDecision y ∧ n ≤ y.length ∧ Permits G j σ y ∧
        σ ⟨G.info y, hy⟩ ≠ s j ⟨G.info y, hy⟩ := by
    by_contra hno
    push Not at hno
    exact hσn fun y hy hd hl hp => hno y hy hd hl hp
  have hyl : y.length = n := by
    by_contra hne
    exact hdev (hσ y hy hdec (by omega) hperm)
  set a := (σ ⟨G.info y, hy⟩).1 with ha_def
  set a' := (s j ⟨G.info y, hy⟩).1 with ha'_def
  have hne : a ≠ a' := fun he => hdev (Subtype.ext he)
  -- the dominating strategy: follow `s` in the subgame at `y`
  set σ' : G.PureStrategy j := fun k => if InSub G y k.1 then s j k else σ k with hσ'_def
  have hσ'y : σ' ⟨G.info y, hy⟩ = s j ⟨G.info y, hy⟩ := by
    simp [hσ'_def, inSub_of_suffix G hdec (List.suffix_refl y)]
  have hσ'mem : σ' ∈ biSets G s (n + 1) j := by
    intro y' hy' hd' hl' hp'
    by_cases hin : InSub G y (G.info y')
    · simp [hσ'_def, hin]
    · have hσ'e : σ' ⟨G.info y', hy'⟩ = σ ⟨G.info y', hy'⟩ := by simp [hσ'_def, hin]
      rw [hσ'e]
      refine hσ y' hy' hd' hl' fun b v hv hbv => ?_
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hd'.1)
      have hnin : ¬ InSub G y (G.info v) := by
        rw [inSub_iff_of_pi G hPI hvd]
        intro hyv
        exact hin ((inSub_iff_of_pi G hPI hd').2
          (hyv.trans ((List.suffix_cons b v).trans hbv)))
      have := hp' b v hv hbv
      simp only [hσ'_def, hnin, ↓reduceIte] at this
      exact this
  -- the payoffs, as continuation payoffs
  have hpay : ∀ t : (i : I) → G.PureStrategy i,
      G.toNormalForm.payoff j t = cont G (G.pureProfile t) [] j :=
    fun t => toNormalForm_payoff_eq_cont G t j
  have hP := fun t => isPureMoves_pureProfile G hN t
  -- the two profiles differ only in the subgame at `y`
  have hdiff : ∀ r : (i : I) → G.PureStrategy i, ∀ v, G.IsDecision v →
      ¬ InSub G y (G.info v) → G.pureProfile (Function.update r j σ) (G.info v) =
        G.pureProfile (Function.update r j σ') (G.info v) := by
    intro r v hv hnin
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (hN (G.info v))
    funext b
    rw [G.pureProfile_apply _ hk, G.pureProfile_apply _ hk]
    by_cases hkj : k = j
    · subst hkj
      simp [hσ'_def, hnin]
    · simp [Function.update_of_ne hkj]
  -- the comparison when the rivals lead to `y`
  have hcomp : ∀ r : (i : I) → G.PureStrategy i, (∀ k, k ≠ j → r k ∈ biSets G s (n + 1) k) →
      OnPath G (G.pureProfile (Function.update r j σ)) [] y →
      cont G (G.pureProfile (Function.update r j σ)) [] j =
          cont G (G.pureProfile s) (a :: y) j ∧
        cont G (G.pureProfile (Function.update r j σ')) [] j =
          cont G (G.pureProfile s) (a' :: y) j := by
    intro r hr hpath
    have hmem : ∀ τ ∈ biSets G s (n + 1) j, ∀ k,
        Function.update r j τ k ∈ biSets G s (n + 1) k := by
      intro τ hτ k
      by_cases hkj : k = j
      · subst hkj
        simpa using hτ
      · simpa [Function.update_of_ne hkj] using hr k hkj
    have hpath' : OnPath G (G.pureProfile (Function.update r j σ')) [] y := by
      intro b v _ hbv
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hdec.1)
      have hnin : ¬ InSub G y (G.info v) := by
        rw [inSub_iff_of_pi G hPI hvd]
        intro hyv
        have h1 := hyv.length_le
        have h2 := hbv.length_le
        simp only [List.length_cons] at h2
        omega
      rw [← hdiff r v hvd hnin]
      exact hpath b v List.nil_suffix hbv
    have hplay : G.pureProfile (Function.update r j σ) (G.info y) a = 1 :=
      (pureProfile_eq_one_iff G _ hy a).2 (by simp [ha_def])
    have hplay' : G.pureProfile (Function.update r j σ') (G.info y) a' = 1 :=
      (pureProfile_eq_one_iff G _ hy a').2 (by simp [ha'_def, hσ'y])
    have hay : a :: y ∈ G.nodes := G.cons_mem_of_mem_avail hdec (σ ⟨G.info y, hy⟩).2
    have hay' : a' :: y ∈ G.nodes := G.cons_mem_of_mem_avail hdec (s j ⟨G.info y, hy⟩).2
    constructor
    · rw [cont_onPath G (hP _) List.nil_suffix hdec.1 hpath, cont_step G (hP _) hdec hplay]
      exact cont_biSets G hN s _ (hmem σ hσ) hay (by simp [hyl])
        (hpath.cons G List.nil_suffix hplay) j
    · rw [cont_onPath G (hP _) List.nil_suffix hdec.1 hpath', cont_step G (hP _) hdec hplay']
      exact cont_biSets G hN s _ (hmem σ' hσ'mem) hay' (by simp [hyl])
        (hpath'.cons G List.nil_suffix hplay') j
  have hbi : cont G (G.pureProfile s) (a :: y) j < cont G (G.pureProfile s) (a' :: y) j :=
    bi_strict G hN hinj hs hdec hy (σ ⟨G.info y, hy⟩).2 hne
  refine ⟨σ', hσ'mem, fun r hr => ?_, ?_⟩
  · rw [hpay, hpay]
    by_cases hpath : OnPath G (G.pureProfile (Function.update r j σ)) [] y
    · obtain ⟨h1, h2⟩ := hcomp r hr hpath
      rw [h1, h2]
      exact hbi.le
    · refine (cont_agree G (hP _) G.nil_mem (fun w hw _ hpw => ?_) j).le
      refine hdiff r w hw fun hin => hpath ?_
      exact hpw.mono G ((inSub_iff_of_pi G hPI hw).1 hin)
  · refine ⟨towards G s hdec.1, fun k _ => towards_mem G hPI s hdec.1 hyl k, ?_⟩
    have hpath : OnPath G (G.pureProfile (Function.update (towards G s hdec.1) j σ)) [] y := by
      intro b v _ hbv
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hdec.1)
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (hN (G.info v))
      refine (pureProfile_eq_one_iff G _ hk b).2 ?_
      by_cases hkj : k = j
      · subst hkj
        simpa using hperm b v hk hbv
      · simpa [Function.update_of_ne hkj] using towards_on_path G hPI s hdec.1 hbv hk
    obtain ⟨h1, h2⟩ := hcomp _ (fun k _ => towards_mem G hPI s hdec.1 hyl k) hpath
    rw [hpay, hpay, h1, h2]
    exact hbi

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem biSets_top (s : (i : I) → G.PureStrategy i) (j : I) :
    biSets G s (G.nodes.sup List.length + 1) j = Set.univ := by
  ext σ
  simp only [Set.mem_univ, iff_true]
  intro y _ hd hl _
  have := G.length_le_sup hd.1
  omega

/-- **Exercise 9.D.1** (MWG, p. 305). In a finite game of perfect information with no moves of
nature in which no player has the same payoffs at two terminal nodes (the condition of
Proposition 9.B.2 for a unique SPNE), there is a pure SPNE `s` and an order of iterated removal
of weakly dominated strategies (in the normal form) such that `s` survives and every surviving
strategy profile follows the same path as `s` and gives every player the same payoff. The
order removes, deepest decision nodes first, the strategies that deviate from backward induction
at a node they do not exclude by their own moves. -/
theorem exercise_9_D_1 (hPI : G.PerfectInformation) (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') :
    ∃ s : (i : I) → G.PureStrategy i, IsSPNE G (pureB G s) ∧
      ∃ T : (i : I) → Set (G.PureStrategy i),
        Relation.ReflTransGen (WDDeletionStep G.toNormalForm) (fullSets G.PureStrategy) T ∧
        (∀ i, s i ∈ T i) ∧ ∀ t : (i : I) → G.PureStrategy i, (∀ i, t i ∈ T i) →
          (∀ w ∈ G.nodes, OnPath G (G.pureProfile t) [] w ↔ OnPath G (G.pureProfile s) [] w) ∧
          ∀ i, G.toNormalForm.payoff i t = G.toNormalForm.payoff i s := by
  obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
  refine ⟨s, isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs, biSets G s 0, ?_,
    fun i y hy _ _ _ => rfl, fun t ht => ⟨fun w hw => onPath_biSets_iff G hN s t ht hw,
      fun i => ?_⟩⟩
  · set M := G.nodes.sup List.length + 1
    have key : ∀ k ≤ M, Relation.ReflTransGen (WDDeletionStep G.toNormalForm)
        (fullSets G.PureStrategy) (biSets G s (M - k)) := by
      intro k
      induction k with
      | zero =>
        intro _
        have : biSets G s (M - 0) = fullSets G.PureStrategy := by
          funext j
          exact biSets_top G s j
        rw [this]
      | succ k ih =>
        intro hk
        have he : M - k = M - (k + 1) + 1 := by omega
        refine (ih (by omega)).tail ?_
        rw [he]
        exact biSets_step G hPI hN hinj hs _
    simpa using key M le_rfl
  · rw [toNormalForm_payoff_eq_cont, toNormalForm_payoff_eq_cont]
    exact cont_biSets G hN s t ht G.nil_mem le_rfl (onPath_self G _ []) i

/-- **Exercise 9.D.1, an instance** (MWG, pp. 268 and 305). The entry game of Example 9.B.1
satisfies the hypotheses of Exercise 9.D.1 (perfect information, no moves of nature, no player
with equal payoffs at two terminal nodes), so iterated deletion of weakly dominated strategies
in a suitable order leaves only profiles with the SPNE outcome. -/
theorem exercise_9_D_1_instance :
    entryGame.PerfectInformation ∧ (∀ k, entryGame.player k ≠ none) ∧
    (∀ i, ∀ z ∈ entryGame.terminals, ∀ z' ∈ entryGame.terminals,
      entryGame.payoff i z = entryGame.payoff i z' → z = z') ∧
    ∃ s : (i : Fin 2) → entryGame.PureStrategy i, IsSPNE entryGame (pureB entryGame s) ∧
      ∃ T : (i : Fin 2) → Set (entryGame.PureStrategy i),
        Relation.ReflTransGen (WDDeletionStep entryGame.toNormalForm)
          (fullSets entryGame.PureStrategy) T ∧
        (∀ i, s i ∈ T i) ∧ ∀ t : (i : Fin 2) → entryGame.PureStrategy i, (∀ i, t i ∈ T i) →
          (∀ w ∈ entryGame.nodes, OnPath entryGame (entryGame.pureProfile t) [] w ↔
            OnPath entryGame (entryGame.pureProfile s) [] w) ∧
          ∀ i, entryGame.toNormalForm.payoff i t = entryGame.toNormalForm.payoff i s := by
  have hPI := example_9_B_1_perfectInformation
  have hN : ∀ k, entryGame.player k ≠ none := fun k => by simp [entryGame_player]
  have hinj : ∀ i, ∀ z ∈ entryGame.terminals, ∀ z' ∈ entryGame.terminals,
      entryGame.payoff i z = entryGame.payoff i z' → z = z' := by
    intro i z hz z' hz' he
    rw [entryGame_terminals] at hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;>
      first | rfl | (fin_cases i <;> norm_num [entryGame_payoff, entryPay] at he)
  exact ⟨hPI, hN, hinj, exercise_9_D_1 entryGame hPI hN hinj⟩

end MWG.DynamicGames
