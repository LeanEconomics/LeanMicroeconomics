/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.DominanceBI
import MWGDynamicGames.EntryCoordination

/-!
# Strict backward induction

Tools for solving concrete finite games of perfect information by backward induction
(MWG, Section 9.B, pp. 270-276), used for Exercise 9.B.14.

* `cont_dirac_play`: with sure moves `c` (no moves of nature), the continuation payoff from a
  node is the payoff at the terminal node reached by following `c`, computed by iterating one
  step of play.
* `isSPNE_of_weak_bi`: sure moves that are optimal at every decision node given the continuation
  play form an SPNE.
* `eq_dirac_of_strict_bi`: if at every decision node after `x₀` the mover strictly prefers the
  move `c` to every other move (given the continuation play of `c`), every SPNE (in behaviour
  strategies) plays `c` at every decision node after `x₀`. Unlike Proposition 9.B.2 this needs no
  assumption on ties at terminal nodes, only strictness along the backward-induction solution.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]

omit [Fintype A] [DecidableEq I] in
theorem isPureMoves_dirac {c : H → A} (hc : ∀ k, c k ∈ G.avail k) :
    IsPureMoves G (fun k => dirac (c k)) := by
  refine ⟨fun k a => ?_, fun k a ha => ?_, fun k => ?_⟩
  · change dirac (c k) a = 0 ∨ dirac (c k) a = 1
    unfold dirac
    split_ifs <;> simp
  · have : a ≠ c k := fun he => ha (he ▸ hc k)
    simp [dirac, this]
  · simp only [dirac]
    rw [Finset.sum_ite_eq' (G.avail k)]
    simp [hc k]

/-- One step of play with sure moves `c`: at a decision node the move `c` is taken, a terminal
node is left unchanged. -/
def bstep (c : H → A) (l : List A) : List A :=
  if ∃ b, b :: l ∈ G.nodes then c (G.info l) :: l else l

omit [DecidableEq I] in
/-- With sure moves `c`, the continuation payoff from node `x` is the payoff at the terminal node
reached from `x` by following `c`: iterate `bstep` at least as often as the length of the
longest node. -/
theorem cont_dirac_play {c : H → A} (hc : ∀ k, c k ∈ G.avail k) {n : ℕ}
    (hn : ∀ y ∈ G.nodes, y.length ≤ n) {x : List A} (hx : x ∈ G.nodes) (i : I) :
    cont G (fun k => dirac (c k)) x i = G.payoff i ((bstep G c)^[n] x) := by
  suffices key : ∀ m, ∀ x ∈ G.nodes, n ≤ x.length + m →
      cont G (fun k => dirac (c k)) x i = G.payoff i ((bstep G c)^[m] x) from
    key n x hx (by omega)
  intro m
  induction m with
  | zero =>
    intro y hy hl
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := hn _ hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm]
    rfl
  | succ m ih =>
    intro y hy hl
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hb : bstep G c y = c (G.info y) :: y := by
        simp only [bstep, hdec.2, ↓reduceIte]
      rw [Function.iterate_succ_apply, hb,
        cont_step G (isPureMoves_dirac G hc) hdec (by simp [dirac] : dirac (c (G.info y))
          (c (G.info y)) = 1)]
      exact ih _ (G.cons_mem_of_mem_avail hdec (hc _)) (by simp only [List.length_cons]; omega)
    · have hb : bstep G c y = y := by
        have : ¬ ∃ b, b :: y ∈ G.nodes := fun ⟨b, hb⟩ => hterm.2 b hb
        simp only [bstep, this, ↓reduceIte]
      rw [Function.iterate_fixed hb, cont_terminal _ _ hterm]

/-- **Backward induction** (MWG, pp. 270-276). Sure moves `c` (no moves of nature) such that at
every decision node the mover's continuation payoff after `c` is at least that after any other
move form a subgame perfect Nash equilibrium. -/
theorem isSPNE_of_weak_bi (hN : ∀ k, G.player k ≠ none) {c : H → A}
    (hc : ∀ k, c k ∈ G.avail k)
    (hweak : ∀ x, G.IsDecision x → ∀ j, G.player (G.info x) = some j → ∀ a ∈ G.avail (G.info x),
      cont G (fun k => dirac (c k)) (a :: x) j ≤
        cont G (fun k => dirac (c k)) (c (G.info x) :: x) j) :
    IsSPNE G (pureMoves (I := I) c) := by
  refine isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureMoves hc) fun x hx j hj a ha => ?_
  rw [assemble_pureMoves hN, cont_step G (isPureMoves_dirac G hc) hx
    (by simp [dirac] : dirac (c (G.info x)) (c (G.info x)) = 1)]
  exact hweak x hx j hj a ha

/-- **Strict backward induction** (MWG, p. 276). Suppose that at every decision node `x` after
`x₀` the mover strictly prefers `c (H(x))` to every other move, given the continuation play of
`c`. Then every subgame perfect Nash equilibrium of a game of perfect information without moves
of nature plays `c` at every decision node after `x₀`. -/
theorem eq_dirac_of_strict_bi (hPI : G.PerfectInformation)
    (hN : ∀ k, G.player k ≠ none) {c : H → A} (hc : ∀ k, c k ∈ G.avail k) {x₀ : List A}
    (hstrict : ∀ x, G.IsDecision x → x₀ <:+ x → ∀ j, G.player (G.info x) = some j →
      ∀ a ∈ G.avail (G.info x), a ≠ c (G.info x) →
        cont G (fun k => dirac (c k)) (a :: x) j <
          cont G (fun k => dirac (c k)) (c (G.info x) :: x) j)
    {F : I → H → A → ℝ} (hF : IsSPNE G F) :
    ∀ x, G.IsDecision x → x₀ <:+ x → G.assemble F (G.info x) = dirac (c (G.info x)) := by
  set P : H → A → ℝ := fun k => dirac (c k)
  suffices key : ∀ n, ∀ y ∈ G.nodes, x₀ <:+ y → G.nodes.sup List.length - y.length ≤ n →
      ∀ x, G.IsDecision x → y <:+ x → G.assemble F (G.info x) = P (G.info x) by
    intro x hx hx₀
    exact key _ x hx.1 hx₀ le_rfl x hx (List.suffix_refl x)
  intro n
  induction n with
  | zero =>
    intro y hy _ hn x hx hyx
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    have := G.eq_of_terminal_suffix hterm hx.1 hyx
    subst this
    exact absurd ⟨hx, hterm⟩ (G.isDecision_or_isTerminal hy).2
  | succ n ih =>
    intro y hy hy₀ hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hchild : ∀ a ∈ G.avail (G.info y), ∀ x, G.IsDecision x → a :: y <:+ x →
          G.assemble F (G.info x) = P (G.info x) := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (hy₀.trans (List.suffix_cons a y))
          (by simp only [List.length_cons]; omega)
      have hcont : ∀ a ∈ G.avail (G.info y), ∀ i,
          cont G (G.assemble F) (a :: y) i = cont G P (a :: y) i :=
        fun a ha i => cont_congr G (fun w hw haw => hchild a ha w hw haw) i
      have hy' : G.assemble F (G.info y) = P (G.info y) := by
        obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info y))
        set a₀ := c (G.info y)
        have ha₀ : a₀ ∈ G.avail (G.info y) := hc _
        have hopt := oneShotOptimal_of_isSPNE G hPI hF hdec j hj
        have hsum := cont_decision G (G.assemble F) hdec j
        have hge := hopt a₀ ha₀
        have hnn : ∀ a ∈ G.avail (G.info y), 0 ≤ G.assemble F (G.info y) a *
            (cont G P (a₀ :: y) j - cont G P (a :: y) j) := by
          intro a ha
          refine mul_nonneg (assemble_nonneg G hF.1 _ _) ?_
          by_cases hae : a = a₀
          · rw [hae, sub_self]
          · linarith [hstrict y hdec hy₀ j hj a ha hae]
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by
          refine le_antisymm ?_ (Finset.sum_nonneg hnn)
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hF.1, one_mul]
          have : ∑ a ∈ G.avail (G.info y), G.assemble F (G.info y) a * cont G P (a :: y) j =
              cont G (G.assemble F) y j := by
            rw [hsum]
            exact Finset.sum_congr rfl fun a ha => by rw [hcont a ha j]
          rw [this, ← hcont a₀ ha₀ j]
          linarith)
        have hoff : ∀ a ∈ G.avail (G.info y), a ≠ a₀ → G.assemble F (G.info y) a = 0 := by
          intro a ha hne
          rcases mul_eq_zero.1 (hzero a ha) with h | h
          · exact h
          · linarith [hstrict y hdec hy₀ j hj a ha hne]
        have hon : G.assemble F (G.info y) a₀ = 1 := by
          have := assemble_sum G hF.1 (G.info y)
          rw [← Finset.add_sum_erase _ _ ha₀, Finset.sum_eq_zero fun a ha =>
            hoff a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha), add_zero] at this
          exact this
        funext a
        simp only [P, dirac]
        split_ifs with h
        · rw [h]
          exact hon
        · by_cases ha : a ∈ G.avail (G.info y)
          · exact hoff a ha h
          · rw [G.assemble_of_some _ hj]
            exact (hF.1 j _ hj).2.1 a ha
      intro x hx hyx
      by_cases hxy : x = y
      · rw [hxy]
        exact hy'
      · obtain ⟨b, hb⟩ := exists_cons_suffix hyx (Ne.symm hxy)
        exact hchild b (G.mem_avail_of_cons_mem (G.mem_of_suffix hb hx.1)) x hx hb
    · intro x hx hyx
      have := G.eq_of_terminal_suffix hterm hx.1 hyx
      subst this
      exact absurd ⟨hx, hterm⟩ (G.isDecision_or_isTerminal hy).2

end MWG.DynamicGames
