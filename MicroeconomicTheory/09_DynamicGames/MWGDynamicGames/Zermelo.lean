/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Basic
import Mathlib.Tactic.FinCases

/-!
# Backward induction and Zermelo's theorem

MWG, Section 9.B, pp. 270-276: backward induction in finite games of perfect information,
Proposition 9.B.1 (Zermelo's theorem) and Proposition 9.B.2.

* `OneShotOptimalAt G F x`: at decision node `x` the mover's continuation payoff is at least
  that of every immediate successor, i.e. her move at `x` is optimal given the continuation
  play (the backward-induction requirement).
* `oneShot_deviation_principle` (the **one-shot deviation principle** for finite trees): if
  the moves are one-shot optimal at every decision node, then no player can gain from any
  change of her behaviour strategy, from any node on. In a game of perfect information the
  converse holds (`oneShotOptimal_of_isSPNE`), so SPNE = backward induction
  (`isSPNE_iff_oneShotOptimal`).
* `exists_backwardInduction`: in a finite game of perfect information a pure profile derived
  by backward induction exists (the procedure is well defined).
* `proposition_9_B_1` (Zermelo): a pure Nash equilibrium derived by backward induction exists;
  every such profile is a Nash equilibrium of `Γ_E` and of its normal form; with no moves of
  nature and no player having equal payoffs at two terminal nodes it is unique.
* `proposition_9_B_2`: a pure SPNE exists; with the same proviso it is unique (as a behaviour
  profile).
* Correction: with moves of nature the uniqueness clause fails (`natureTie`,
  `zermelo_uniqueness_fails_with_nature`): ties arise between lotteries over terminal nodes.
* `exercise_9_B_4`: in a finite two-player zero-sum game of perfect information all subgame
  perfect Nash equilibria have the same payoffs.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- **Section 9.B** (MWG, p. 270). The move at decision node `x` is optimal for its mover given
the continuation play: no immediate successor gives the mover a higher continuation payoff. -/
def OneShotOptimalAt (F : I → H → A → ℝ) (x : List A) : Prop :=
  ∀ j, G.player (G.info x) = some j → ∀ a ∈ G.avail (G.info x),
    cont G (G.assemble F) (a :: x) j ≤ cont G (G.assemble F) x j

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of nature. -/
theorem assemble_update_of_none (F : I → H → A → ℝ) (i : I) (g : H → A → ℝ) {k : H}
    (hk : G.player k = none) : G.assemble (Function.update F i g) k = G.assemble F k := by
  rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of a player `j ≠ i`. -/
theorem assemble_update_of_ne (F : I → H → A → ℝ) {i j : I} (g : H → A → ℝ) {k : H}
    (hk : G.player k = some j) (hji : j ≠ i) :
    G.assemble (Function.update F i g) k = G.assemble F k := by
  rw [G.assemble_of_some _ hk, G.assemble_of_some _ hk, Function.update_of_ne hji]

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of player `i`. -/
theorem assemble_update_self (F : I → H → A → ℝ) {i : I} (g : H → A → ℝ) {k : H}
    (hk : G.player k = some i) : G.assemble (Function.update F i g) k = g k := by
  rw [G.assemble_of_some _ hk, Function.update_self]

omit [DecidableEq H] in
/-- **One-shot deviation principle** (finite trees; MWG, proof of Proposition 9.B.1,
pp. 272-273). If a behaviour profile's moves are one-shot optimal at every decision node, then
from every node no player gains by switching to any other behaviour strategy. -/
theorem oneShot_deviation_principle {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F)
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x) {x : List A} (hx : x ∈ G.nodes)
    (i : I) {g : H → A → ℝ} (hg : G.IsBehaviorStrategy i g) :
    cont G (G.assemble (Function.update F i g)) x i ≤ cont G (G.assemble F) x i := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      cont G (G.assemble (Function.update F i g)) x i ≤ cont G (G.assemble F) x i from
    h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hchild : ∀ a ∈ G.avail (G.info y),
          cont G (G.assemble (Function.update F i g)) (a :: y) i ≤
            cont G (G.assemble F) (a :: y) i := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
      rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F) hdec]
      cases hk : G.player (G.info y) with
      | none =>
        rw [assemble_update_of_none G F i g hk]
        exact Finset.sum_le_sum fun a ha =>
          mul_le_mul_of_nonneg_left (hchild a ha) (assemble_nonneg G hF _ _)
      | some j =>
        by_cases hji : j = i
        · subst hji
          rw [assemble_update_self G F g hk]
          have hsum : ∑ a ∈ G.avail (G.info y), G.assemble F (G.info y) a *
              cont G (G.assemble F) (a :: y) j = cont G (G.assemble F) y j := by
            rw [cont_decision _ _ hdec]
          calc ∑ a ∈ G.avail (G.info y), g (G.info y) a *
                cont G (G.assemble (Function.update F j g)) (a :: y) j
              ≤ ∑ a ∈ G.avail (G.info y), g (G.info y) a * cont G (G.assemble F) y j :=
                Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
                  ((hchild a ha).trans (hopt y hdec j hk a ha)) ((hg _ hk).1 a)
            _ = cont G (G.assemble F) y j := by rw [← Finset.sum_mul, (hg _ hk).2.2, one_mul]
            _ = _ := hsum.symm
        · rw [assemble_update_of_ne G F g hk hji]
          exact Finset.sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left (hchild a ha) (assemble_nonneg G hF _ _)
    · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]

omit [DecidableEq H] in
/-- **One-shot deviation principle, consequence.** A behaviour profile whose moves are one-shot
optimal at every decision node is a subgame perfect Nash equilibrium (in every game). -/
theorem isSPNE_of_oneShotOptimal {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F)
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x) : IsSPNE G F :=
  ⟨hF, fun _ hx i _ hg => oneShot_deviation_principle G hF hopt hx.1.1 i hg⟩

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 275; Exercise 9.B.1). In a game of perfect information every
decision node initiates a subgame. -/
theorem isSubgameRoot_of_perfectInformation (hPI : G.PerfectInformation) {x : List A}
    (hx : G.IsDecision x) : IsSubgameRoot G x := by
  refine ⟨hx, fun y hy he => hPI y hy.1 x hx.1 hy.2 hx.2 he, fun y hy hxy y' hy' he => ?_⟩
  rw [hPI y' hy'.1 y hy.1 hy'.2 hy.2 he]
  exact hxy

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- In a game of perfect information, the information set of a decision node does not recur
after it. -/
theorem info_ne_of_perfectInformation (hPI : G.PerfectInformation) {x y : List A}
    (hx : G.IsDecision x) (hy : G.IsDecision y) {a : A} (hxy : a :: x <:+ y) :
    G.info y ≠ G.info x := by
  intro he
  have := hPI y hy.1 x hx.1 hy.2 hx.2 he
  subst this
  have := hxy.length_le
  simp at this

/-- The move function putting probability one on `a`. -/
def dirac (a : A) : A → ℝ := fun b => if b = a then 1 else 0

omit [DecidableEq I] in
/-- With the move at `x` replaced by a sure move `a`, the continuation from `x` is the
continuation from `a :: x` (perfect information). -/
theorem cont_dirac_update (hPI : G.PerfectInformation) (f : H → A → ℝ) {x : List A}
    (hx : G.IsDecision x) {a : A} (ha : a ∈ G.avail (G.info x)) (i : I) :
    cont G (Function.update f (G.info x) (dirac a)) x i = cont G f (a :: x) i := by
  rw [cont_decision _ _ hx, Function.update_self]
  simp only [dirac, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (G.avail (G.info x))]
  simp only [ha, ↓reduceIte]
  refine cont_congr G (fun y hy hay => ?_) i
  rw [Function.update_of_ne (info_ne_of_perfectInformation G hPI hx hy hay)]

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 275). In a game of perfect information an SPNE is one-shot
optimal at every decision node: each decision node starts a subgame, and a sure move is a
behaviour deviation. -/
theorem oneShotOptimal_of_isSPNE (hPI : G.PerfectInformation) {F : I → H → A → ℝ}
    (h : IsSPNE G F) {x : List A} (hx : G.IsDecision x) : OneShotOptimalAt G F x := by
  classical
  intro j hj a ha
  set g : H → A → ℝ := Function.update (F j) (G.info x) (dirac a) with hg_def
  have hg : G.IsBehaviorStrategy j g := by
    intro k hk
    by_cases hkx : k = G.info x
    · subst hkx
      simp only [hg_def, Function.update_self]
      refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
      · have hba : b ≠ a := fun h => hb (h ▸ ha)
        simp [dirac, hba]
      · simp only [dirac]
        rw [Finset.sum_ite_eq' (G.avail (G.info x))]
        simp [ha]
    · simp only [hg_def, Function.update_of_ne hkx]
      exact h.1 j k hk
  have hdev := h.2 x (isSubgameRoot_of_perfectInformation G hPI hx) j g hg
  have heq : G.assemble (Function.update F j g) =
      Function.update (G.assemble F) (G.info x) (dirac a) := by
    funext k
    by_cases hkx : k = G.info x
    · subst hkx
      rw [assemble_update_self G F g hj, Function.update_self, hg_def, Function.update_self]
    · rw [Function.update_of_ne hkx]
      cases hk : G.player k with
      | none => rw [assemble_update_of_none G F j g hk]
      | some l =>
        by_cases hlj : l = j
        · subst hlj
          rw [assemble_update_self G F g hk, hg_def, Function.update_of_ne hkx,
            G.assemble_of_some _ hk]
        · rw [assemble_update_of_ne G F g hk hlj]
  rw [heq, cont_dirac_update G hPI _ hx ha] at hdev
  exact hdev

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, pp. 275-276). In a finite game of perfect information the subgame
perfect Nash equilibria are exactly the behaviour profiles whose moves are optimal at every
decision node given the continuation play (backward induction). -/
theorem isSPNE_iff_oneShotOptimal (hPI : G.PerfectInformation) {F : I → H → A → ℝ}
    (hF : IsBehaviorProfile G F) :
    IsSPNE G F ↔ ∀ x, G.IsDecision x → OneShotOptimalAt G F x := by
  classical
  exact
    ⟨fun h _ hx => oneShotOptimal_of_isSPNE G hPI h hx, isSPNE_of_oneShotOptimal G hF⟩

/-- **Section 9.B** (MWG, p. 270). A pure strategy profile derived through backward induction:
its moves are optimal at every decision node given the continuation play. -/
def IsBackwardInduction (s : (i : I) → G.PureStrategy i) : Prop :=
  ∀ x, G.IsDecision x → OneShotOptimalAt G (pureB G s) x

/-- The pure strategy profile in which every player plays `c k` at each of her information
sets. -/
def pureOfChoice (c : H → A) (hc : ∀ k, c k ∈ G.avail k) : (i : I) → G.PureStrategy i :=
  fun i => G.pureOfFun i c fun k _ => hc k

omit [DecidableEq H] in
/-- At a player's decision node the continuation payoff of a pure profile is that of the
chosen successor. -/
theorem cont_pureOfChoice (c : H → A) (hc : ∀ k, c k ∈ G.avail k) {x : List A}
    (hx : G.IsDecision x) {j : I} (hj : G.player (G.info x) = some j) (i : I) :
    cont G (G.assemble (pureB G (pureOfChoice G c hc))) x i =
      cont G (G.assemble (pureB G (pureOfChoice G c hc))) (c (G.info x) :: x) i := by
  rw [cont_decision _ _ hx, assemble_pureB, Finset.sum_eq_single (c (G.info x))]
  · simp [G.pureProfile_apply _ hj, pureOfChoice]
  · intro b _ hb
    simp [G.pureProfile_apply _ hj, pureOfChoice, Ne.symm hb]
  · intro h
    exact absurd (hc _) h

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, pp. 270-272). In a finite game of perfect information the backward
induction procedure is well defined: there is a pure strategy profile whose moves are optimal
at every decision node given the continuation play. -/
theorem exists_backwardInduction (hPI : G.PerfectInformation) :
    ∃ s : (i : I) → G.PureStrategy i, IsBackwardInduction G s := by
  classical
  set D := G.nodes.sup List.length
  -- downward induction on the length of the decision nodes
  suffices h : ∀ n, ∃ c : H → A, ∃ hc : ∀ k, c k ∈ G.avail k, ∀ x, G.IsDecision x →
      D ≤ x.length + n → OneShotOptimalAt G (pureB G (pureOfChoice G c hc)) x by
    obtain ⟨c, hc, h⟩ := h D
    exact ⟨pureOfChoice G c hc, fun x hx => h x hx (by omega)⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun k => (G.avail_nonempty k).choose, fun k => (G.avail_nonempty k).choose_spec,
      fun x hx hl => ?_⟩
    obtain ⟨b, hb⟩ := hx.2
    have := G.length_le_sup hb
    simp only [List.length_cons] at this
    omega
  | succ n ih =>
    obtain ⟨c, hc, hopt⟩ := ih
    set F := pureB G (pureOfChoice G c hc)
    -- the new choice at the information sets of decision nodes of length `D - (n+1)`
    let best : H → A := fun k =>
      match G.player k with
      | none => c k
      | some j =>
        if (G.rep k).length + (n + 1) = D then
          ((G.avail k).exists_max_image (fun a => cont G (G.assemble F) (a :: G.rep k) j)
            (G.avail_nonempty k)).choose
        else c k
    have hbest : ∀ k, best k ∈ G.avail k := by
      intro k
      simp only [best]
      split
      · exact hc k
      · split_ifs
        · exact (Exists.choose_spec ((G.avail k).exists_max_image _ (G.avail_nonempty k))).1
        · exact hc k
    refine ⟨best, hbest, ?_⟩
    set F' := pureB G (pureOfChoice G best hbest)
    -- nodes of length at least `D - n` see no change
    have hrep : ∀ y, G.IsDecision y → G.rep (G.info y) = y := fun y hy =>
      hPI _ (G.rep_isDecision _).1 y hy.1 (G.rep_isDecision _).2 hy.2 (G.info_rep _)
    have hsame : ∀ y, G.IsDecision y → D ≤ y.length + n →
        G.assemble F' (G.info y) = G.assemble F (G.info y) := by
      intro y hy hl
      cases hk : G.player (G.info y) with
      | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
      | some j =>
        have hbk : best (G.info y) = c (G.info y) := by
          have hne : ¬ (y.length + (n + 1) = D) := by omega
          simp only [best, hk, hrep y hy, hne, ite_false]
        funext a
        simp only [F', F, assemble_pureB, G.pureProfile_apply _ hk, pureOfChoice,
          pureOfFun_apply, hbk]
        split_ifs with h1 <;> simp [h1]
    have hcont : ∀ y, y ∈ G.nodes → D ≤ y.length + n → ∀ i,
        cont G (G.assemble F') y i = cont G (G.assemble F) y i := by
      intro y _ hl i
      exact cont_congr G (fun w hw hyw => hsame w hw (by have := hyw.length_le; omega)) i
    intro x hx hl
    by_cases hlx : D ≤ x.length + n
    · intro j hj a ha
      have hax : a :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx ha
      rw [hcont x hx.1 hlx, hcont (a :: x) hax (by simp; omega)]
      exact hopt x hx hlx j hj a ha
    · have hxl : x.length + (n + 1) = D := by omega
      intro j hj a ha
      have hk : best (G.info x) = ((G.avail (G.info x)).exists_max_image
          (fun a => cont G (G.assemble F) (a :: G.rep (G.info x)) j)
          (G.avail_nonempty _)).choose := by
        simp only [best, hj, hrep x hx, hxl, ite_true]
      have hmax := (Exists.choose_spec ((G.avail (G.info x)).exists_max_image
          (fun a => cont G (G.assemble F) (a :: G.rep (G.info x)) j) (G.avail_nonempty _)))
      rw [← hk, hrep x hx] at hmax
      have hax : a :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx ha
      have hbx : best (G.info x) :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx (hbest _)
      rw [cont_pureOfChoice G best hbest hx hj, hcont _ hbx (by simp; omega),
        hcont _ hax (by simp; omega)]
      exact hmax.2 a ha

omit [DecidableEq I] [DecidableEq H] in
/-- Uniqueness core: with no moves of nature and no player having equal payoffs at two
terminal nodes, two profiles that are one-shot optimal everywhere have the same moves at every
information set after `x`, and both lead from `x` to the same terminal node. -/
theorem oneShotOptimal_unique (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {F F' : I → H → A → ℝ} (hF : IsBehaviorProfile G F) (hF' : IsBehaviorProfile G F')
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x)
    (hopt' : ∀ x, G.IsDecision x → OneShotOptimalAt G F' x) {x : List A} (hx : x ∈ G.nodes) :
    (∃ z ∈ G.terminals, x <:+ z ∧ ∀ i, cont G (G.assemble F) x i = G.payoff i z ∧
        cont G (G.assemble F') x i = G.payoff i z) ∧
      ∀ y, G.IsDecision y → x <:+ y → G.assemble F (G.info y) = G.assemble F' (G.info y) := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      (∃ z ∈ G.terminals, x <:+ z ∧ ∀ i, cont G (G.assemble F) x i = G.payoff i z ∧
        cont G (G.assemble F') x i = G.payoff i z) ∧
      ∀ y, G.IsDecision y → x <:+ y → G.assemble F (G.info y) = G.assemble F' (G.info y) from
    h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    refine ⟨⟨y, (mem_terminals G).2 hterm, List.suffix_refl _, fun i =>
      ⟨cont_terminal _ _ hterm i, cont_terminal _ _ hterm i⟩⟩, fun w hw hyw => ?_⟩
    have := G.eq_of_terminal_suffix hterm hw.1 hyw
    subst this
    exact absurd ⟨hw, hterm⟩ (G.isDecision_or_isTerminal hy).2
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · set k := G.info y with hkdef
      have hchild : ∀ a ∈ G.avail (G.info y),
          (∃ z ∈ G.terminals, a :: y <:+ z ∧ ∀ i, cont G (G.assemble F) (a :: y) i =
            G.payoff i z ∧ cont G (G.assemble F') (a :: y) i = G.payoff i z) ∧
          ∀ w, G.IsDecision w → a :: y <:+ w →
            G.assemble F (G.info w) = G.assemble F' (G.info w) := fun a ha => by
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
      have hex : ∀ a (ha : a ∈ G.avail (G.info y)), ∃ z, z ∈ G.terminals ∧ a :: y <:+ z ∧
          ∀ i, cont G (G.assemble F) (a :: y) i = G.payoff i z ∧
            cont G (G.assemble F') (a :: y) i = G.payoff i z := fun a ha => by
        obtain ⟨z, hz, h1, h2⟩ := (hchild a ha).1
        exact ⟨z, hz, h1, h2⟩
      choose zf hzf hyz hval using hex
      have hagree := fun a ha => (hchild a ha).2
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info y))
      -- the mover's values at the successors are distinct
      have hdist : ∀ a (ha : a ∈ G.avail k) b (hb : b ∈ G.avail k), a ≠ b →
          G.payoff j (zf a ha) ≠ G.payoff j (zf b hb) := by
        intro a ha b hb hab he
        have := hinj j _ (hzf a ha) _ (hzf b hb) he
        have h1 := hyz a ha
        rw [this] at h1
        exact hab (by simpa using suffix_unique h1 (hyz b hb) (by simp))
      obtain ⟨a₀, ha₀, hmax⟩ := (G.avail k).exists_max_image
        (fun a => if h : a ∈ G.avail k then G.payoff j (zf a h) else 0) (G.avail_nonempty k)
      simp only [ha₀, ↓reduceDIte] at hmax
      -- any one-shot optimal behaviour puts all mass on `a₀`
      have hdirac : ∀ (P : I → H → A → ℝ), IsBehaviorProfile G P →
          OneShotOptimalAt G P y →
          (∀ a (ha : a ∈ G.avail k), cont G (G.assemble P) (a :: y) j = G.payoff j (zf a ha)) →
          G.assemble P k = dirac a₀ := by
        intro P hP hoP hPv
        have hsum := cont_decision G (G.assemble P) hdec j
        have hge := hoP j hj a₀ ha₀
        rw [hPv a₀ ha₀] at hge
        have hzero : ∀ a ∈ G.avail k, G.assemble P k a *
            (G.payoff j (zf a₀ ha₀) - cont G (G.assemble P) (a :: y) j) = 0 := by
          have hnn : ∀ a ∈ G.avail k, 0 ≤ G.assemble P k a *
              (G.payoff j (zf a₀ ha₀) - cont G (G.assemble P) (a :: y) j) := by
            intro a ha
            refine mul_nonneg (assemble_nonneg G hP _ _) ?_
            rw [hPv a ha]
            have := hmax a ha
            simp only [ha, ↓reduceDIte] at this
            linarith
          refine (Finset.sum_eq_zero_iff_of_nonneg hnn).1 ?_
          refine le_antisymm ?_ (Finset.sum_nonneg hnn)
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hP, one_mul, ← hsum]
          linarith
        have hoff : ∀ a ∈ G.avail k, a ≠ a₀ → G.assemble P k a = 0 := by
          intro a ha hne
          have := hzero a ha
          rw [hPv a ha] at this
          have hlt : G.payoff j (zf a ha) < G.payoff j (zf a₀ ha₀) := by
            have h1 := hmax a ha
            simp only [ha, ↓reduceDIte] at h1
            exact lt_of_le_of_ne h1 (hdist a ha a₀ ha₀ hne)
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        have hon : G.assemble P k a₀ = 1 := by
          have := assemble_sum G hP k
          rw [← Finset.add_sum_erase _ _ ha₀, Finset.sum_eq_zero fun a ha =>
            hoff a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha), add_zero] at this
          exact this
        funext a
        simp only [dirac]
        split_ifs with h
        · subst h
          exact hon
        · by_cases ha : a ∈ G.avail k
          · exact hoff a ha h
          · rw [G.assemble_of_some _ hj]
            exact (hP j k hj).2.1 a ha
      have hFd := hdirac F hF (hopt y hdec) fun a ha => (hval a ha j).1
      have hF'd := hdirac F' hF' (hopt' y hdec) fun a ha => (hval a ha j).2
      refine ⟨⟨zf a₀ ha₀, hzf a₀ ha₀, (List.suffix_cons a₀ y).trans (hyz a₀ ha₀), fun i => ?_⟩,
        fun w hw hyw => ?_⟩
      · rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F') hdec, hFd, hF'd]
        simp only [dirac, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' (G.avail k), Finset.sum_ite_eq' (G.avail k)]
        simp only [ha₀, ↓reduceIte]
        exact hval a₀ ha₀ i
      · by_cases hwy : w = y
        · subst hwy
          rw [hFd, hF'd]
        · obtain ⟨b, hb⟩ := exists_cons_suffix hyw (Ne.symm hwy)
          have hbav : b ∈ G.avail k := G.mem_avail_of_cons_mem (G.mem_of_suffix hb hw.1)
          exact hagree b hbav w hw hb
    · refine ⟨⟨y, (mem_terminals G).2 hterm, List.suffix_refl _, fun i =>
        ⟨cont_terminal _ _ hterm i, cont_terminal _ _ hterm i⟩⟩, fun w hw hyw => ?_⟩
      have := G.eq_of_terminal_suffix hterm hw.1 hyw
      subst this
      exact absurd ⟨hw, hterm⟩ (G.isDecision_or_isTerminal hy).2

omit [Fintype A] [DecidableEq H] in
/-- Moves that agree at every information set give equal pure strategy profiles. -/
theorem pure_eq_of_assemble_eq {s s' : (i : I) → G.PureStrategy i}
    (h : ∀ k, G.assemble (pureB G s) k = G.assemble (pureB G s') k) : s = s' := by
  funext i
  funext k
  have := congrFun (h k.1) (s i k).1
  rw [assemble_pureB, assemble_pureB, G.pureProfile_apply _ k.2,
    G.pureProfile_apply _ k.2] at this
  simp only [ite_true] at this
  split_ifs at this with he
  · exact Subtype.ext he.symm
  · norm_num at this

omit [DecidableEq H] in
/-- **Proposition 9.B.1 (Zermelo's theorem)** (MWG, p. 272). Every finite game of perfect
information has a pure strategy profile derived through backward induction, and every such
profile is a Nash equilibrium of `Γ_E` (in behaviour strategies, hence also of its normal
form). Moreover, if there are no moves of nature and no player has the same payoffs at two
terminal nodes, there is a unique profile derived in this manner. -/
theorem proposition_9_B_1 (hPI : G.PerfectInformation) :
    (∃ s : (i : I) → G.PureStrategy i, IsBackwardInduction G s) ∧
    (∀ s, IsBackwardInduction G s → IsNashB G (pureB G s) ∧
      MWG.SimultaneousMoveGames.IsNashEquilibrium G.toNormalForm s) ∧
    ((∀ k, G.player k ≠ none) →
      (∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') →
      ∃! s : (i : I) → G.PureStrategy i, IsBackwardInduction G s) := by
  classical
  have hNA := G.noAbsentMindedness_of_perfectInformation hPI
  refine ⟨exists_backwardInduction G hPI, fun s hs => ?_, fun hN hinj => ?_⟩
  · have hN : IsNashB G (pureB G s) :=
      isNashB_of_isSPNE G hNA (isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs)
    exact ⟨hN, hN.isNashEquilibrium_pure⟩
  · obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
    refine ⟨s, hs, fun s' hs' => pure_eq_of_assemble_eq G fun k => ?_⟩
    obtain ⟨x, hx, hb, rfl⟩ := G.info_surj k
    exact ((oneShotOptimal_unique G hN hinj (isBehaviorProfile_pureB G s')
      (isBehaviorProfile_pureB G s) hs' hs G.nil_mem).2 x ⟨hx, hb⟩ List.nil_suffix)

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 273). Every finite game of perfect information has a pure strategy
Nash equilibrium. -/
theorem exists_pure_nash_of_perfectInformation
    (hPI : G.PerfectInformation) :
    ∃ s : (i : I) → G.PureStrategy i,
      MWG.SimultaneousMoveGames.IsNashEquilibrium G.toNormalForm s := by
  classical
  obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
  exact ⟨s, ((proposition_9_B_1 G hPI).2.1 s hs).2⟩

omit [DecidableEq H] in
/-- **Proposition 9.B.2** (MWG, p. 276). Every finite game of perfect information has a pure
strategy subgame perfect Nash equilibrium. Moreover, if there are no moves of nature and no
player has the same payoffs at any two terminal nodes, the SPNE is unique: any two SPNE (in
behaviour strategies) prescribe the same moves at every information set. -/
theorem proposition_9_B_2 (hPI : G.PerfectInformation) :
    (∃ s : (i : I) → G.PureStrategy i, IsSPNE G (pureB G s)) ∧
    ((∀ k, G.player k ≠ none) →
      (∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') →
      ∀ F F', IsSPNE G F → IsSPNE G F' → ∀ k, G.assemble F k = G.assemble F' k) := by
  classical
  refine ⟨?_, fun hN hinj F F' hF hF' k => ?_⟩
  · obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
    exact ⟨s, isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs⟩
  · obtain ⟨x, hx, hb, rfl⟩ := G.info_surj k
    exact (oneShotOptimal_unique G hN hinj hF.1 hF'.1
      (fun y hy => oneShotOptimal_of_isSPNE G hPI hF hy)
      (fun y hy => oneShotOptimal_of_isSPNE G hPI hF' hy) G.nil_mem).2 x ⟨hx, hb⟩
      List.nil_suffix

omit [DecidableEq H] in
/-- In a two-player zero-sum game the second player's continuation payoff is the negative of
the first's. -/
theorem cont_zeroSum {G : ExtensiveForm (Fin 2) A H} (hzs : ∀ z, G.payoff 1 z = -G.payoff 0 z)
    (f : H → A → ℝ) (x : List A) : cont G f x 1 = -cont G f x 0 := by
  unfold cont
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hzs]
  ring

omit [DecidableEq H] in
/-- **Exercise 9.B.4** (MWG, p. 302). In a finite two-player zero-sum game of perfect
information, all subgame perfect Nash equilibria give the same payoffs (from every node). -/
theorem exercise_9_B_4 {G : ExtensiveForm (Fin 2) A H} (hPI : G.PerfectInformation)
    (hzs : ∀ z, G.payoff 1 z = -G.payoff 0 z) {F F' : Fin 2 → H → A → ℝ}
    (hF : IsSPNE G F) (hF' : IsSPNE G F') {x : List A} (hx : x ∈ G.nodes) (i : Fin 2) :
    cont G (G.assemble F) x i = cont G (G.assemble F') x i := by
  classical
  have key : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      cont G (G.assemble F) x 0 = cont G (G.assemble F') x 0 := by
    intro n
    induction n with
    | zero =>
      intro y hy hn
      have hterm : G.IsTerminal y := by
        refine ⟨hy, fun b hb => ?_⟩
        have := G.length_le_sup hb
        simp only [List.length_cons] at this
        omega
      rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
    | succ n ih =>
      intro y hy hn
      rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
      · have hchild : ∀ a ∈ G.avail (G.info y),
            cont G (G.assemble F) (a :: y) 0 = cont G (G.assemble F') (a :: y) 0 := by
          intro a ha
          have hmem := G.cons_mem_of_mem_avail hdec ha
          have hl := G.length_le_sup hmem
          simp only [List.length_cons] at hl
          exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
        -- the mover's continuation payoff is the maximum over the successors
        have hmaxval : ∀ (P : Fin 2 → H → A → ℝ), IsSPNE G P → ∀ j,
            G.player (G.info y) = some j →
            (∀ a ∈ G.avail (G.info y), cont G (G.assemble P) (a :: y) j ≤
              cont G (G.assemble P) y j) ∧
            ∃ a ∈ G.avail (G.info y), cont G (G.assemble P) y j ≤
              cont G (G.assemble P) (a :: y) j := by
          intro P hP j hj
          refine ⟨oneShotOptimal_of_isSPNE G hPI hP hdec j hj, ?_⟩
          by_contra hno
          push Not at hno
          have := cont_decision G (G.assemble P) hdec j
          have hlt : ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
              cont G (G.assemble P) (a :: y) j ≤
              ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
                cont G (G.assemble P) y j :=
            Finset.sum_le_sum fun a ha =>
              mul_le_mul_of_nonneg_left (hno a ha).le (assemble_nonneg G hP.1 _ _)
          rw [← Finset.sum_mul, assemble_sum G hP.1, one_mul, ← this] at hlt
          obtain ⟨a, ha⟩ := G.avail_nonempty (G.info y)
          have h1 := hno a ha
          have hsum0 : ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
              (cont G (G.assemble P) y j - cont G (G.assemble P) (a :: y) j) = 0 := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hP.1, one_mul, ← this,
              sub_self]
          have hnn : ∀ b ∈ G.avail (G.info y), 0 ≤ G.assemble P (G.info y) b *
              (cont G (G.assemble P) y j - cont G (G.assemble P) (b :: y) j) :=
            fun b hb => mul_nonneg (assemble_nonneg G hP.1 _ _) (by linarith [hno b hb])
          have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0
          have hall : ∀ b ∈ G.avail (G.info y), G.assemble P (G.info y) b = 0 := by
            intro b hb
            rcases mul_eq_zero.1 (hz b hb) with h | h
            · exact h
            · linarith [hno b hb]
          have := assemble_sum G hP.1 (G.info y)
          rw [Finset.sum_eq_zero hall] at this
          norm_num at this
        cases hk : G.player (G.info y) with
        | none =>
          rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F') hdec,
            G.assemble_of_none _ hk, G.assemble_of_none _ hk]
          exact Finset.sum_congr rfl fun a ha => by rw [hchild a ha]
        | some j =>
          obtain ⟨h1, a, ha, h2⟩ := hmaxval F hF j hk
          obtain ⟨h1', a', ha', h2'⟩ := hmaxval F' hF' j hk
          have hj' : ∀ P : Fin 2 → H → A → ℝ, ∀ y',
              cont G (G.assemble P) y' j = if j = 0 then cont G (G.assemble P) y' 0
                else -cont G (G.assemble P) y' 0 := by
            intro P y'
            fin_cases j
            · simp
            · simp [cont_zeroSum hzs]
          simp only [hj'] at h1 h2 h1' h2'
          split_ifs at h1 h2 h1' h2' with hj0
          · have e1 := h1 a' ha'
            have e2 := h1' a ha
            rw [hchild a' ha'] at e1
            rw [← hchild a ha] at e2
            linarith
          · have e1 := h1 a' ha'
            have e2 := h1' a ha
            rw [hchild a' ha'] at e1
            rw [← hchild a ha] at e2
            linarith
      · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  have h0 := key _ x hx le_rfl
  fin_cases i
  · exact h0
  · simp only [Fin.mk_one, Fin.isValue]
    rw [cont_zeroSum hzs, cont_zeroSum hzs, h0]

end MWG.DynamicGames
